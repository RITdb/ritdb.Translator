package ritdb;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.util.HashMap;
import java.util.function.Supplier;

import rtalk.util.RtalkConsoleLogger;
import rtalk.util.RtalkLoggerInterface;

public class TranslateWide implements RtalkLoggerInterface{
	  private File  _outDir;
	  private File  _srcDir;
	  private File  _ext;
	  private RitdbInfoDatabase _infoDb;
	  
	  /**Constr
	   * args[] are destDir, srcDir, extension
	   * 
	   * */
	  public TranslateWide(HashMap<String,String> args,RtalkLoggerInterface logger) {
	    if (!args.containsKey("home")) {  // make sure there is a home dir
	      args.put("home", System.getProperty("user.dir"));
	    }
	    _infoDb = new RitdbInfoDatabase(args, this);
	    // check the output directory
	    _outDir = new File(args.get("dst"));
	    _srcDir = new File(args.get("src"));
	    _ext = new File(args.get("ext"));
	    if(!(_outDir.exists())){
	      log(_outDir+" does not exist");
	      return;
	    }
	    if(!(_outDir.isDirectory())){
	    	log(_outDir+" is not a directory");
	      return;
	    }
	    // got this far so set up the database 
	    // create s list of files, expands directories if present
	    // expects a file or a directory followed by a filter
	    File[] list = _srcDir.listFiles(); //note: filter==null matches on all files
	    int len = (list==null) ? 0 : list.length;
	    if(len==0) return;
	    for(int i=0; i<len; i++) {
	    	if(list[i].isDirectory()){
	  	      File[] list2 = list[i].listFiles( new FilenameFilter(){
	  		      public boolean accept( File dir, String name ) { 
	  		        return name.toLowerCase().endsWith("."+_ext);
	  		      }
	  		      });
	  		      int len2 = (list2==null) ? 0 : list2.length;
	  		      if(len2==0) return;
	  		      for(int j=0; j<len2; j++) {
	  		    	translate(list2[j]);
	  		      }
	  		}else{
	    		if(list[i].getName().toLowerCase().endsWith("."+_ext)){
	    			translate(list[i]);
	    		}
	    	}
	        //File[] files = tmpFile.listFiles((FilenameFilter) new WildcardFilter("?e*.t?t"));

	        //for( int j= 0; j < files.length; j++){
	         // translate(files[j]);
	        //}
	    }
	    _infoDb.closeLogDbConnection(); //close up the 'info log' database (note: auto-reopens when needed)
	  }
	  
	  private void translate(File file){
		long t0 = System.currentTimeMillis();
	    String filename = file.getName();
	    String dbName; //get or create name of database to be used for this file
	    dbName = filename;
	    int p = dbName.lastIndexOf(".");
	    if(p>=0) dbName = dbName.substring(0, p);
	    dbName+=".sqlite";
	    File dbFile = new File(_outDir, dbName); //create 'File' object from complete pathname
	    if(dbFile.exists()){
	    	log(file.getAbsolutePath() + " output file exists");
	      return;}
	    log(filename+" ==> "+dbFile.getAbsolutePath());
	    HashMap<String,String> guruKeys = new HashMap<String,String>();
	    guruKeys.put("stdfFileName", filename);
	    long fileSize=file.length(); //size of stdf  file on disk
	    guruKeys.put("stdfFileSize", Long.toString(fileSize));
	    guruKeys.put("objPath", dbFile.getAbsolutePath());
	    //System.out.println("create db");
	    Connection sqlConnection = null; //connection to database
	    try {
	      sqlConnection = doConnectToSqlite(dbFile.getAbsolutePath());
	      if(sqlConnection==null)  
	        throw new Exception("No connection available to database '"+dbFile.getAbsolutePath()+"'");
	      //System.out.println("start translate");
	      long t3 = System.currentTimeMillis();
        RiStdfToWideTables sc = new RiStdfToWideTables(file, sqlConnection, this);
        sc.start();
	      long t4 = System.currentTimeMillis();
	      log("  ("+ ((t4-t3)/1000.0) +" sec)\n");
	      guruKeys.put("stdfRecords", Integer.toString(sc.getRecordCount()));
	      guruKeys.put("databaseSize", Long.toString(dbFile.length()));
	      //guruKeys.put("databaseRecordCount", Integer.toString(getDbRowCount(sqlConnection, dbFile)));
	      guruKeys.put("conversionTime", Double.toString((t4-t3)/1000.0));
	      _infoDb.insertAttributes(guruKeys);
	    }
	    catch(SQLException e) {
	      System.out.println("Unable to connect to database '"+dbFile.getAbsolutePath()+"' because: "+e);
	    }
	    catch(IOException e) {
	      String msg = "File Error with ["+file.getAbsolutePath()+"]: "+e;
	      System.out.println(msg);
	    }
	    catch(Exception e) {
	      String msg = "Error uploading STDF file "+file.getName()+": "+e; 
	      System.out.println(msg);
	      e.printStackTrace();
	    }
	    finally { //ensure dbase connection gets closed each time
	      try { if(sqlConnection!=null) sqlConnection.close(); }
	      catch(Exception e) { System.out.println("Error closing database '"+dbName+"': "+e); }
	  }
	long t5 = System.currentTimeMillis();

	}
	 
	  
	  /**Utility function to connect to an SQLite database
	   * Throws ClassCastException if the JDBC driver class is not available
	   * Throws SQLException if fails in establishing a connection to the specified database
	   * */
	  public static Connection doConnectToSqlite(String dbName) throws SQLException, ClassNotFoundException {
	    dbName = (dbName==null) ? "" : dbName.trim();

	    String jdbcClassName = "org.sqlite.JDBC";
	    Class.forName(jdbcClassName); //ensure the sqlite JDBC class is available (throws ClassNotFoundException) 
	    String connectTo = "jdbc:sqlite:"+dbName;
	    //System.out.println("Connect using: '"+connectTo+"' (driver="+jdbcClassName+")");
	    return DriverManager.getConnection(connectTo); //throws SQLException
	  }
	  
	
	protected static HashMap<String, String> parseArgs(String[] args){
	  HashMap<String, String> startupArgs = new HashMap<String, String>();
	  //Read through the command line parameters:
	  int len=args.length;
	  String[] pair = null;
	  for(int i=0; i < len; i++) {
	    int pos=args[i].indexOf('=');
	    if(pos < 0) {
	      startupArgs.put(args[i], "true");
	    }
	    else {
	      pair = args[i].split("=");
	      startupArgs.put(pair[0], pair[1]);
	    }
	  }
	  return startupArgs;
	}

	  public static void main(String[] args){
	    // args can be flags or key=value
	    /*flags
	     * duplicatePtrData
	     * duplicateTestNames
	     * skipEmptyTests
	     * addStateToNames
	     */
	    /*key       value
	     * src        "/Users/markroos/stdf/loadersrc/"
	     * dst        "/Users/markroos/stdf/loadertest/"
	     * ext        extention for dst   stdf
	     */
	    HashMap<String,String> newArgs = parseArgs(args);
	    new TranslateWide(newArgs, new RtalkConsoleLogger()); //run the upload(s) from a separate thread in case it takes awhile

	  }

    @Override
    public void log(String message) {
      // TODO Auto-generated method stub
      System.out.println(message);
    }

    @Override
    public void logError(String message) {
      // TODO Auto-generated method stub
      
    }

    @Override
    public void logDebug(String message) {
      // TODO Auto-generated method stub
      
    }

    @Override
    public void logVerbose(String message) {
      // TODO Auto-generated method stub
      
    }

    @Override
    public void logError(Exception e) {
      // TODO Auto-generated method stub
      
    }

    @Override
    public void logVerbose(Supplier msg) {
      // TODO Auto-generated method stub
      
    }


}
