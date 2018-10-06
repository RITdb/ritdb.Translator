package ritdb;

import java.io.File;
import java.io.IOException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import ritdb.stdf4j.Header;
import ritdb.stdf4j.Record;
import ritdb.stdf4j.RecordData;
import ritdb.stdf4j.RecordVisitor;
import ritdb.stdf4j.STDFReader;
import rtalk.util.RtalkLoggerInterface;

/**Given an stdf file, and an SQL connection to a database, 
 * this populates the database with the contents of the STDF file.
 * 
 * Note: For STDF this uses the stdf4j library (com.tragicphantom.stdf) Ver: 0.0.2: 
 *       http://code.google.com/p/stdf4j/
 */
public class RiStdfToWideTables implements RecordVisitor {
  
  private Connection _sqlConnection=null;     //database connection
  private Statement _sqlStatement=null;       //reusable statement for communicating with the database
  private int _recordCnt=0;                   //keeps track of the number of records processed
  private HashSet _recordTypes=new HashSet(); //keeps track of record types that have been seen (PTR, MIR, etc.)
  //private NamesCounter _recordCntr = new NamesCounter(); //used to keep track of each type of stdf record
  private HashMap _prepStatements=new HashMap(); //collection of prepared statements associated with a given record type so don't have to create them each time
  
  private ArrayList _fieldNames=new ArrayList(); //names of the fields found in a single record. Is global just for reuse
  private ArrayList _fieldValues=new ArrayList(); //values for the fields found in a single record. Is global just for reuse
  private RtalkLoggerInterface _logger;
  public volatile boolean _stop = false;
  private File _srcFile;
  
  /**Constr. Given an STDF file and a connection to a database*/
  public RiStdfToWideTables(File file, Connection sqlConnection, RtalkLoggerInterface logger) throws IOException, ParseException, SQLException {
    _sqlConnection = sqlConnection;
    _logger = logger;
    _srcFile = file;
  }
  
  public void start() throws IOException, ParseException, SQLException{
    _sqlStatement=_sqlConnection.createStatement(); //reusable statement for communicating with the database
    try { _sqlStatement.executeUpdate("PRAGMA synchronous = OFF;"); } //generates an error in postgres but speeds things up in sqlite by allowing the database to perform ops without verifyng the disk writes went through
    catch(Exception e) { 
      //Emit.out("Warning: 'PRAGMA synchronous' not supported. The error was: [" + e + "]"); 
    }
    _sqlConnection.setAutoCommit(false);
    STDFReader reader=new STDFReader(_srcFile, _logger); //note: accepts File, InputStream or filename
    reader.parse(this); //as it parses, the reader calls handleRecord (below) for each entry
    _sqlConnection.commit(); //commit all those changes
    _sqlConnection.setAutoCommit(true);
    try { _sqlStatement.executeUpdate("PRAGMA synchronous = ON;"); } //restore setting allowing the database to verify writes to the file system
    catch(Exception e) {}
  }
  
  

  /**This is called for each record found, as the stdf file is read.
   * note: Required for interface RecordVisitor*/
  public void handleRecord(Record record) {
    try { 
      RecordData recordData=record.getData(); //throws ParseException
      String recordType=recordData.getType(); //type of record (Mir, Ptr etc.)
      //int recordNdx = recordCntr.add(recordType); //keep track of how many times this record type was seen

      ++_recordCnt; //keep track of how many STDF records are processed
      if((_recordCnt % 10000) == 0) {
        _logger.log(".");
        _sqlConnection.commit(); //commit once in a while
        if(_stop){
          throw new RuntimeException("stopping");
        }
        //Also consider doing an ANALYZE once in a while to speed things up
        //System.out.println("" + _recordCnt + "STDF records");
      }
      //System.out.println("Record "+_recordCnt+", type="+recordType+", "+recordData.size()+" entries"); //debug

      //Determine whether this record type has been seen yet:
      boolean creatingTable=false; //normally don't have to create the database table
      if(!_recordTypes.contains(recordType)) {
        _recordTypes.add(recordType); //keeps track of how many times this recordType has been seen (PIR, MIR, etc)
        _fieldNames.clear(); //clear this before each use. Note: this is global just to keep from creating a new ArrayList each time
        creatingTable=true; //go ahead and do the table create
      }

      //HashMap<String, Object> fieldsMap = recordData.getFields(); //jdk5
      HashMap fieldsMap=recordData.getFields(); //jdk4

      //Iterator<String> iterFieldNames = fieldsMap.keySet().iterator(); //jdk 5
      Iterator iterFieldNames=fieldsMap.keySet().iterator(); //jdk 4

      //Get field names and values for this record type:
      _fieldValues.clear(); //clear this before each use. Note: this is global just to keep from creating a new ArrayList for each record found
      while(iterFieldNames.hasNext()) {
        String fieldName = (String)iterFieldNames.next();
        Object fieldValue = fieldsMap.get(fieldName);
        //System.out.print("    "+key+" = "+( (fieldValue==null) ? "[NO ENTRY]" : fieldValue.toString())); //debug
        if(creatingTable) //if going to create the table then need to use the field names
          _fieldNames.add(fieldName);
        _fieldValues.add(fieldValue);
      }

      //Create database table if needed:
      String tableName = recordType; //converts stdf name to database column name, i.e. "HBR" to "HARDWARE_BIN"
      if(creatingTable) { //create sql table and prepared statement
        if(tableName==null) {
          tableName=recordType;
          System.out.println("Warning: Unrecognized STDF Record type: ["+recordType+"]"); //debug
        }
        
        StringBuffer sb=new StringBuffer("create table if not exists " + tableName + " (");
        int cnt = _fieldNames.size();
        for(int i=0; i < cnt; i++) {
          if(i > 0) sb.append(','); //skip the first comma
          String fieldName=(String)_fieldNames.get(i);
          sb.append(fieldName).append(" TEXT"); //note: the data type is useful for Postgres. Not so much needed for sqlite
        }
        sb.append(");"); //finish it off
        //System.out.println(sb.toString());
        if(cnt != 0) _sqlStatement.executeUpdate(sb.toString()); //create table
      }

      //Get or create the prepared SQL statement:
      int cnt = _fieldValues.size(); //was using fieldNames here but seems like fields is safer (should be equivalent unless things go horribly awry)
      PreparedStatement prep=(PreparedStatement)_prepStatements.get(recordType);
      if(prep == null && cnt > 0) { //create a prepared sql statement that has the necessary fields for this stdf record type
        StringBuffer sb=new StringBuffer("insert into " + tableName + " values (");

        if(cnt > 0) sb.append("?"); //first one
        for(int i=1; i < cnt; i++)
          sb.append(",?");
        sb.append(");"); //finish it off
          prep=_sqlConnection.prepareStatement(sb.toString()); //prepared statement: "insert into table..."
        _prepStatements.put(recordType, prep); //save for next time
      }

      //Populate the data and send it to the database:
      for(int i=0; i < cnt; i++) {
        Object fieldValue = _fieldValues.get(i);
        if(fieldValue == null) fieldValue="";
        else if(fieldValue instanceof byte[]) //if it's a byte array, convert it to a comma separated string 
          fieldValue = stringIt((byte[])fieldValue);
        else if(fieldValue instanceof Object[])  //if it's an Object array, convert it to a comma separated string
          fieldValue = toCsv((Object[])fieldValue);
        prep.setString(i+1, fieldValue.toString());
      }
      if(prep != null){
        prep.addBatch();
        try { prep.executeBatch(); }
        catch(Exception e) {
          String emsg = "Error in "+getClass().getName()+".handleRecord(): ["+e+"] executing SQL command: ["+clean(prep.toString().getBytes(), 0, -1, -1)+"]"; 
          _logger.log(emsg);
          _logger.log(emsg);
        }
      }
    } 
    catch(ParseException e) {
      String emsg = "Error in "+getClass().getName()+".handleRecord(): "+e; 
      _logger.log(emsg);
      e.printStackTrace();
      //System.exit(1); //debug
    }
    catch(SQLException e) {
      String emsg = "Error in "+getClass().getName()+".handleRecord(): "+e;
      _logger.log(emsg);
      e.printStackTrace();
      //System.exit(1); //debug
    }
  }
  
  /**Number of records found*/
  public int getRecordCount() { return _recordCnt; }

  /**note: Required for interface RecordVisitor*/
  public void afterFile() {}

  /**note: Required for interface RecordVisitor*/
  public void beforeFile() {}

  /**Conversion utility. 
   * Returns the given Object array as a comma separated string of values.
   * Does not return null.*/
  private String toCsv(Object[] a) {
    if(a==null) return "";
    int len = a.length;
    switch(len) {
      case 0: return "";
      case 1: return a[0]==null ? "" : a[0].toString();
      default:
        StringBuffer sb = new StringBuffer();
        for(int i=0; i<len; i++) {
          if(i>0) sb.append(", ");
          sb.append(a[i]==null ? "" : a[i].toString());
        }
        return sb.toString();
    }
  }
  
  /**Converts an array of bytes into a nice comma separated string of (decimal) numbers*/
  public static String stringIt(byte[] ba) {
    if(ba == null || ba.length == 0) return "";
    StringBuffer sb=new StringBuffer();
    int length=ba.length;
    for(int i=0; i < length; i++) {
      sb.append("" + (ba[i] & 0xff));
      if(i != length - 1) sb.append(",");
    }
    return sb.toString();
  }
  
  /**Returns an ASCII viewable representation of the given byte array section.
  'buf' may be quite large but offset/len define the region to be printed.
  If len is -1 then its value is the full length of the buffer.
  If 'maxCnt' > 0 then is used as an upper limit on number of chars returned.
  Note: Non-ASCII bytes display as ~n where n is a hex value
  Note: Changed on 9/16/08: Used to display as decimal instead of hex
  */
 public static String clean(byte[] buf, int offset, int len, int maxCnt) {
   /* *** * /
   StringBuffer sb = new StringBuffer(new String(buf, 0, cnt));
   for(int i=0; i<cnt; i++)
     if(buf[i] < ' ' || buf[i] > '~') sb.setCharAt(i, '.');
   /* *** */
   if(buf == null) return "";
   int max=buf.length - offset;
   if(len < 0 || len > max) len=max;
   if(maxCnt > 0 && len > maxCnt) len=maxCnt; //Truncate
   StringBuffer sb=new StringBuffer();
   int stopAt=offset + len;
   for(int i=offset; i < stopAt; i++) {
     int b=buf[i];
     if(b < ' ' || b > '~') {
       sb.append("~");
       int val=b & 0xff;
       if(val <= 15) sb.append('0');
       sb.append(Integer.toHexString(val));
     }
     else sb.append((char)b);
   }
   return sb.toString();
 }

@Override
public void handleUnknownRecord(Header header, byte[] bytes) {
	// TODO Auto-generated method stub
	
}

public void stopConvert(){
  _stop = true;
}
  

}
