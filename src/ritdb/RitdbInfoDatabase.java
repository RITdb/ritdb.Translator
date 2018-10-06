package ritdb;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.Iterator;
import java.util.TimeZone;
import org.sqlite.SQLiteJDBCLoader;
import rtalk.portal.NodeIdentifier;
import rtalk.util.GuruUtilities;
import rtalk.util.RtalkLoggerInterface;

/**
 * Helper class to handle the infomation database
 * @author markroos
 *
 */
public class RitdbInfoDatabase {
  
  private Connection _logDbConnection =null;
  private PreparedStatement _logDbStatement = null;
  private NodeIdentifier _nodeId;
  private long entityID = 0; // local runID is 1 first non run is 2
  private long sequence = 0; // holder for sequence override in secs
  private String _homeDirectory;
  private RtalkLoggerInterface _logger;
  
  public RitdbInfoDatabase(HashMap<String,String> args, RtalkLoggerInterface logger){
    _logger = logger;
    _nodeId = new NodeIdentifier(args);
    _homeDirectory = args.get("home");

  }
  
  public long nextEid(){
    if(entityID == 0) entityID = getLastEntityId();
    return ++entityID;
  }
  
  /**Create the "info log" database. Optionally clears out previously data.*/
  public void initializeLogDatabase(boolean clearPrevious, boolean verbose) {
    String jdbcClassName = "org.sqlite.JDBC";
    try { Class.forName(jdbcClassName); } //ensure the sqlite JDBC class is available (throws ClassNotFoundException)
    catch (ClassNotFoundException e) { _logger.log("Error: unable to load the JDBC class ("+jdbcClassName+")"); }
    Class c = null;
    _logger.log(System.getProperty("os.name"));
    _logger.log("sqlite ver "+ SQLiteJDBCLoader.getMajorVersion()+ "."+SQLiteJDBCLoader.getMinorVersion());
    String loadInfoDbaseName = "loadInfo.sqlite";
    String connectTo = "jdbc:sqlite:"+_homeDirectory + File.separator +loadInfoDbaseName;
    System.out.println("info database path = " + connectTo);
    _logger.log("'Info log' connection via: '"+connectTo+"' (driver="+jdbcClassName+")");

    try { if(_logDbConnection!=null) _logDbConnection.close(); } catch(Exception e1) {} //just in case is open

    try { _logDbConnection = DriverManager.getConnection(connectTo); } //open connection to 'info log' database
    catch(Exception e) {
      _logger.log("Error: unable to connect to '"+loadInfoDbaseName+"' database because: "+e.getMessage()); 
      return;} // failed so just return
    
    try {
      if(clearPrevious){//remove existing table
        _logDbConnection.createStatement().executeUpdate("drop table if exists main");
      }
        _logDbConnection.createStatement().executeUpdate(
          "create table if not exists " + "main" + " ("+
          "sequence INTEGER PRIMARY KEY,"+
          "entityID INTEGER,"+
          "indexID INTEGER,"+
          "name TEXT collate nocase,"+
          "value TEXT collate nocase,"+
          "value2 NONE);"
          );
    }
    catch (SQLException e) {
      System.out.print(" Unable to init 'info log' database main table because: "+e);
      _logger.log("Error creating 'info log' narrow table: "+e);
    }   

    try { _logDbStatement=_logDbConnection.prepareStatement("insert into main values (?,?,?,?,?,?);"); }
    catch (SQLException e) {
      _logger.log("Error creating loadInfo prepared statement: "+e);
    }
    if(verbose) {
      if(clearPrevious) _logger.log("Cleared 'info log' table");
      else _logger.log("Connected to 'info log' table");
    }
  }
  
  /**Closes up the "info log" database*/
  public void closeLogDbConnection() {
    try {
      if(_logDbStatement!=null)
        _logDbStatement.close();
    }
    catch(Exception e) {}
    try { 
      if(_logDbConnection!=null) 
        _logDbConnection.close(); 
    } 
    catch(Exception e1) {} //just in case is open
    _logDbStatement=null;
    _logDbConnection=null;
    
  }
  
  
  /**Returns the highest entity id found in the 'info log' database*/
  private int getLastEntityId() {
    if(_logDbConnection==null) //open info database if is currently closed
      initializeLogDatabase(false, false);
    
    ResultSet results = null;
    try {
      results=_logDbConnection.createStatement().executeQuery("SELECT MAX(entityID) FROM main" );
      results.next();
      return results.getInt(1);
    }
    catch (Exception e) {
      _logger.log("Error fetching last entity ID: "+e.getMessage());
      return 0;
    }
  }
  
  /**Returns the highest sequency found in the 'info log' database*/
  private int getLastSequence() {
    if(_logDbConnection==null) //open info database if is currently closed
      initializeLogDatabase(false, false);
    
    ResultSet results = null;
    try {
      results=_logDbConnection.createStatement().executeQuery("SELECT MAX(sequence) FROM main" );
      results.next();
      return results.getInt(1);
    }
    catch (SQLException e) {
      _logger.log("Error fetching last sequence: "+e);
      return 0;
    }
  }
  
  public boolean insertMetadata(HashMap<String,String> map){
    if(_logDbConnection==null) {//open info database if is currently closed
      entityID = getLastEntityId();
    }
    sequence = getSequence();
    Iterator<String> iter=map.keySet().iterator();
    String key;
    String val;
    String objHash = "";
    // seq,eid,iid,name,value,value2
    ++entityID;
    try {
      PreparedStatement narrowPrepStatement=_logDbConnection.prepareStatement("insert into main values (?,?,?,?,?,?);");
      while (iter.hasNext()) {
        key=(String)iter.next(); //guru key name
        val=(String)map.get(key); //value for key
        if(key.equalsIgnoreCase("ri.sys.ObjHash")) objHash = val;
        if (key != null && val != null) {
          narrowPrepStatement.setLong(1, ++sequence);
          narrowPrepStatement.setLong(2, entityID); //cid
          narrowPrepStatement.setString(4, key); //gkey
          narrowPrepStatement.setString(5, val); //gval
          narrowPrepStatement.addBatch();
          narrowPrepStatement.executeBatch();
        }
      }
    }
      catch (SQLException e) {
        _logger.log("Error in "+getClass().getName()+".insertMetadata(...) performing insert: "+e);
    }
    
    return true;
  }
  
  
  public long getSequence(){
    long lastSeq = getLastSequence();
      Calendar cal = Calendar.getInstance(TimeZone.getTimeZone("GMT"));
      Calendar epoch = Calendar.getInstance(TimeZone.getTimeZone("GMT"));
      epoch.set(Calendar.YEAR, 1990);
      epoch.set(Calendar.MONTH, 0);
      epoch.set(Calendar.DAY_OF_MONTH, 1);
      epoch.set(Calendar.HOUR_OF_DAY, 0);
      epoch.set(Calendar.MINUTE, 0);
      epoch.set(Calendar.SECOND, 0);
      Long timeSeq = (Long) ((cal.getTimeInMillis() - epoch.getTimeInMillis()) / 1000L) * 1000000L;
      if(timeSeq > lastSeq){
        return timeSeq;
      }else{
      return lastSeq + 1L;
      }
    }  
  
  public  String newCID() {
    long time = NodeIdentifier.guruTimeMillis();
    long lastSequence = (time % 1000 ) / 10; // 10 ms steps
    String timeString = GuruUtilities.asString(GuruUtilities.convertBase36(((time / 1000) * 1296) + lastSequence));
    return _nodeId.cellID + timeString;
  }
  
  /**Utility function to return the number of rows in a database.
   * note: expects an already open SQL Connection to database.
   * */
  public int getDbRowCount(Connection sqlConnection, File dbFile) {
    
    int totalRecordCnt=0;
    try {
      if(sqlConnection==null || sqlConnection.isClosed() || dbFile==null) return 0;
      
      DatabaseMetaData md = sqlConnection.getMetaData(); //get info on database tables
      ResultSet rs = md.getTables(dbFile.getName(), null, null, new String[]{"TABLE"});
      ArrayList<String> tableNames = new ArrayList<String>(); //list of tables in the database
      while(rs.next())
        tableNames.add(rs.getString(3)); //table name is index #3
      rs.close();

      //Get info on database records:
      totalRecordCnt=0; //total number of records in all the tables
      for(String tableName : tableNames) {
        int recordCount=0;
        ResultSet results = sqlConnection.createStatement().executeQuery("SELECT COUNT(*) FROM "+tableName);
        if(results.next())
          recordCount = results.getInt(1);
        //Emit.out("Table "+tableName+" has "+recordCount+" records"); //debug
        totalRecordCnt += recordCount;
        results.close();
      }
      
    }
    catch(Exception e) {
      System.out.println("Unable to get number of database rows from '"+dbFile.getAbsolutePath()+"' because: "+e.getMessage());
      return 0;
    }
    return totalRecordCnt;
  }
  
  /**
  * Insert the attribute set into guru
  * @param guruKeys
  * @param ps
  * @throws SQLException
  */
public void insertAttributes(HashMap<String, String> guruKeys) throws SQLException {
      long sequence = getSequence();
      guruKeys.put("arrivalTime", Long.toString(sequence / 1000000));
      Iterator<String> iter=guruKeys.keySet().iterator();
      String key;
      String val;
      Long index = null;
      String val2 = null;

      while (iter.hasNext()) {
          key=(String)iter.next(); //guru key name
          val=(String)guruKeys.get(key); //value for key
          if (key != null && val != null) {
            index = 0L;
              if(    (key.equalsIgnoreCase("ri.sys.Cid")) 
                || (key.equalsIgnoreCase("attrPath"))
                || (key.equalsIgnoreCase("Cid"))
                || (key.equalsIgnoreCase("RevisionOf"))
                || (key.equalsIgnoreCase("Creator"))
                || (key.equalsIgnoreCase("Sequence"))){
                }
              if(key.equalsIgnoreCase("ri.sys.ExpireOn")){
                Long expire = 0L;
          if(val.length() > 8){ 
                  expire = Long.valueOf(val);
                }else{
          expire = convertBase36(val.substring(0, 6));
                }
            index = expire;
              }
              // determine value2 by leading case or included periods
              String first = key.substring(0, 1);
              if(first.equals(first.toUpperCase())){
                val2 = "identity";
              }else{
                if(key.contains(".")){
                  val2 = "object";
                }else{
                  val2 = "info";
                }
              }
              // if the key is Title or ObjClass value2 is the permission
              if(    (key.equalsIgnoreCase("ObjClass")) 
                  || (key.equalsIgnoreCase("Title"))){
              val2 = guruKeys.get("Permission");       
                  }
            try {
              if (key != null && val != null) {
                _logDbStatement.setLong(1, ++sequence);
                _logDbStatement.setLong(2, nextEid()); 
                _logDbStatement.setLong(3, index); //reverse cid       
                _logDbStatement.setString(4, key); //gkey
                _logDbStatement.setString(5, val); //gval
                _logDbStatement.setString(6, val2); //type of row
                _logDbStatement.addBatch();
                _logDbStatement.executeBatch();
              }
            }
            catch (SQLException e) {
              System.out.println("Error in performing GuruKeys table insert: "+e);
            }
          }
      }
    }
private static Long convertBase36(String string) {
  //helper method to convert bytes to long
byte[] time = null;
  try {
  time = string.getBytes("ISO-8859-1");
} catch (UnsupportedEncodingException e) {
  e.printStackTrace();
}
  long result = 0L;
  int index = 0;
  int next;
  int size = time.length;
  for (int i = 0; i < size; i++) {
    result = result * 36;
    next = (int) time[index];
    if (next >= 65) {
      result = result + next - 55;
    } else {
      result = result + next - 48;
    }
    index = index + 1;
  }
  return (Long) result;
}
}
