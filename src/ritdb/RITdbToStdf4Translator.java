package ritdb;

import java.io.IOException;
import java.io.OutputStream;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;
import java.util.TimeZone;

import ritdb.stdf4j.Record;
import ritdb.stdf4j.RecordData;
import ritdb.stdf4j.RecordDescriptor;
import ritdb.stdf4j.RecordType;
import ritdb.stdf4j.STDFWriter;
import ritdb.stdf4j.v4.Types;
import rtalk.util.RtalkLoggerInterface;


public class RITdbToStdf4Translator {
	  private Connection _sqlConnection;  //connection to database
	  private static Map<String, RecordDescriptor> stdfTypes =   //map of STDF4 types 
	      createTypeMap(Types.getRecordDescriptors());
	  private ArrayList<Record> records=new ArrayList<Record>();
	  private Statement sqlStatement = null;
	  // we need to collect some stuff to use later
	  private Object[] mrrValues = new Object[(stdfTypes.get("MRR")).size()];;
	  private Object[] wrrValues = null;
	  private Object[] sdrValues = new Object[(stdfTypes.get("SDR")).size()];
	  Long lotEndTime ;
	  private Hashtable<Integer,Integer> testNumbers = new Hashtable<Integer,Integer>();
	  private Hashtable<Integer,String> testNames = new Hashtable<Integer,String>();
	  private Hashtable<Integer,Integer> siteNames = new Hashtable<Integer,Integer>();// eid to name
	  private Hashtable<Integer,String> hardNames = new Hashtable<Integer,String>();// eid to name
	  private Hashtable<Integer,String> softNames = new Hashtable<Integer,String>();// eid to name
	  private RtalkLoggerInterface _logger;
	  private OutputStream _saveStream;
	  private String _mainTable = "narrow";
	  private boolean duplicateTestName = false;
	  private boolean skipEmptyTests = true;
	  private boolean addStateToName = false;
	  private boolean duplicatePtrData = false;
	  private int siteCount = 0;
	  private String ritdbVer = "ALPHA_P004";
	    
	  /**Constr
	 * @throws IOException 
	 * @throws SQLException */
	  public RITdbToStdf4Translator(Connection source, OutputStream saveFile, RtalkLoggerInterface logger, Map<String,String> args) throws IOException, SQLException {
	    _sqlConnection = source;
		  _logger = logger;
	    _saveStream=saveFile;
	    _mainTable = getDbTableNames(source).get(0);
	    _logger.log("main table = " + _mainTable);
        if(args.containsKey("repeatLimits") && args.get("repeatLimits").equalsIgnoreCase("true"))duplicatePtrData = true;
        if(args.containsKey("repeatTestNames") && args.get("repeatTestNames").equalsIgnoreCase("true"))duplicateTestName = true;
        if(args.containsKey("includeEmptyTests") && args.get("includeEmptyTests").equalsIgnoreCase("true"))skipEmptyTests = false;
	    records=new ArrayList<Record>();
      sqlStatement = _sqlConnection.createStatement();
		  generate();
	      STDFWriter writer=new STDFWriter(_saveStream, _logger);
	      writer.write(records);
	      writer.close();
	      sqlStatement.close();
	  	}
	  /**
	   * applies indexes to table
	   * @param db
	   * @param tableName
	   * @throws SQLException
	   */
	  private void indexTable() throws SQLException{
      Statement tmpSm = _sqlConnection.createStatement();
      tmpSm.executeUpdate("create index if not exists val on "+_mainTable+" (entityID DESC, name DESC);");
      tmpSm.executeUpdate("create index if not exists entity on "+_mainTable+" (name DESC, value DESC);");
      tmpSm.execute("analyze");
      tmpSm.close();
	  }
	  /**
	   * drops indexes and minimizes the table
	   * @param db
	   * @param tableName
	   * @throws SQLException
	   */
	   private  void cleanTable() throws SQLException{
	      Statement tmpSm = _sqlConnection.createStatement();
	      tmpSm.executeUpdate("drop index if exists val;");
	      tmpSm.executeUpdate("drop index if exists entity;");
	      tmpSm.execute("vacuun");
	      tmpSm.close();
	    }
	  
	  public void generate() throws SQLException {
	      ritdbVer = getRitdbVersion();
	      _logger.log("ritdb version = " + ritdbVer);
	      records.add(createRecord("FAR", 2, 4));

	      //First need to generate the bin_eid maps as they are needed throughout

	      initBinMaps();
	      generateMir();
	      generateWcr();
	      if( ritdbVer.equals("ALPHA_P004")){
	         generateSdrOld(); // needs to be early to init siteEid => site
	      }else{
	         generateSdr(); // needs to be early to init siteEid => site      
	      }

	      generateWir(); // only supports one wafer
	      generatePtr();
	      generateWrr(); 
	      generateTsr();
	      generateHbr();
	      generateSbr();
	      generatePcr();
	      generateMrr(); 
	      //cleanTable();
	  
	      // ... the other records
	  }
	  
	  	private  long convertTimeToUnix(String time){
	      DateFormat dfm = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss");  

	      long unixtime = 0;
	      dfm.setTimeZone(TimeZone.getTimeZone("GMT"));//Specify your timezone 
	      try
	      {
	          unixtime = dfm.parse(time).getTime();  
	          unixtime=unixtime/1000;
	      } 
	      catch (Exception e) 
	      {
	          e.printStackTrace();
	      }
	      return unixtime;
	      }

	  
	  /**Utility method to create the STDF4 types map*/
	  private static Map<String, RecordDescriptor> createTypeMap(Map<RecordType, RecordDescriptor> spec) {
	    Map<String, RecordDescriptor> types=new HashMap<String, RecordDescriptor>();
	    for(RecordDescriptor desc : spec.values())
	      types.put(desc.getType().toUpperCase(), desc);
	    return types;
	  }

	  /**Utility method to create an STDF4 record*/
	  private Record createRecord(String type, Object... values) {
	    RecordDescriptor desc=stdfTypes.get(type);
	    //Assert.assertEquals(desc.size(), values.length);
	    Object[] fields=new Object[desc.size()];
	    for(int i=0; i < values.length && i < desc.size(); i++)
	      fields[i]=values[i];
	    return new Record(desc, new RecordData(desc, fields));
	  }
	  /**Utility method to create an default STDF4 record*/
	  private Object[] createDefaultRecord(RecordDescriptor desc, Object... values) {
	    Object[] fields=new Object[desc.size()];
	    for(int i=0; i < values.length && i < desc.size(); i++)
	      fields[i]=values[i];
	    return fields;
	  }

	  /**gets entity type eid.  Only for single instances
	 * @throws SQLException 
	   * 
	   */
	  private String getId(String entityType) throws SQLException{
      ResultSet results = sqlStatement.executeQuery("select entityID from "+ _mainTable+" where name='ENTITY_TYPE' and value='"+entityType+"';");
      String entityID = null;
      if(results.next()) entityID = Long.toString(results.getLong(1));
	    results.close();
	    return entityID;
	  }
	  
	   /**gets entity type eid for an keyValue  Only for single instances
	   * @throws SQLException 
	     * 
	     */
	    private String getAttrId(String name, String value) throws SQLException{
	      ResultSet results = sqlStatement.executeQuery("select entityID from "+ _mainTable+" where name='"+name+"' and value='"+value+"';");
	      String entityID = null;
	      if(results.next()) entityID = Long.toString(results.getLong(1));
	      results.close();
	      return entityID;
	    }
	  
	   /**gets ritdb version
	   * @throws SQLException 
	     * 
	     */
	    private String getRitdbVersion() throws SQLException{
	      ResultSet results = sqlStatement.executeQuery("select value from "+ _mainTable+" where name='RITDB_VERSION';");
	      String ver = null;
	      if(results.next()) ver = results.getString(1);
	      results.close();
	      if(ver == null) return "ALPHA_P004";
	      return ver;
	    }
	  
	  private void initBinMaps() throws SQLException{
	    // these come from the BIN entities and map eid to bin_number
      ResultSet bins = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='BIN';");
      while(bins.next()){
        int bineid = bins.getInt(1);
        ResultSet results = _sqlConnection.createStatement().executeQuery("select name, value from "+ _mainTable+" where entityID="+(bins.getString(1))+";");
        String  bnum = null;
        String btype = null;
        while(results.next()){
        String attrName = results.getString(1);
        if( attrName.equals("BIN_NUMBER")) bnum = results.getString(2);
        if( attrName.equals("BIN_TYPE")) btype = results.getString(2);
      }
        results.close();
      if(btype.equals("HARDBIN")){
        hardNames.put(bineid, bnum);        
      }else{
        softNames.put(bineid, bnum);        
      }
      }
      bins.close();
	  }
	  
	  private void generateMir() throws SQLException{
			// need to look in four places, runID, equip, prod, file
	    // this version duplicates the run part to support old style ritdbs
		// set up the MRR defaults
		RecordDescriptor mrrDesc=stdfTypes.get("MRR");
    mrrValues[0] = 0;
    mrrValues[1] = " ";
	    //First get the MIR information
	    RecordDescriptor desc=stdfTypes.get("MIR");
	    Object[] fieldValues = createDefaultRecord(desc, 
	        0, 0, 1, " ", " ", " ", 65535, 
	        " ", "lotid", "", "", "", "", "", "", "", "", "", "", "", "", "", "", 
	        "", "", "", "", "", "", "", "", "", "", "", "", "", "", "");
	    ResultSet results;
	    // from runId
	    String runID = getId("RUN_INFO");
	    if(runID != null){
  	    results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID='"+runID+"';");
  	    while(results.next()){
  	      String attrName = results.getString(1);
  	      Object attrValue = results.getObject(2);
  	      if( attrName.equals("TESTER_ID"))fieldValues[desc.getIndex("NODE_NAM")] = attrValue;
          if( attrName.equals("CELL_ID"))fieldValues[desc.getIndex("NODE_NAM")] = attrValue;  
  	      if( attrName.equals("LOT_ID"))fieldValues[desc.getIndex("LOT_ID")] = attrValue.toString();
  	      if( attrName.equals("STATION_NUMBER"))fieldValues[desc.getIndex("STAT_NUM")] = attrValue;
  	      if( attrName.equals("TESTER_MODE_CODE"))fieldValues[desc.getIndex("MODE_COD")] = attrValue;
  	      if( attrName.equals("RETEST_CODE"))fieldValues[desc.getIndex("RTST_COD")] = attrValue;
  	      if( attrName.equals("DATA_PROTECTION_CODE"))fieldValues[desc.getIndex("PROT_COD")] = attrValue;
  	      if( attrName.equals("TESTER_CMD_CODE"))fieldValues[desc.getIndex("CMOD_COD")] = attrValue;   
  	      if( attrName.equals("TESTER_TYPE"))fieldValues[desc.getIndex("TSTR_TYP")] = attrValue;
  	      if( attrName.equals("PRODUCT_ID"))fieldValues[desc.getIndex("PART_TYP")] = attrValue;
  	      if( attrName.equals("JOB_NAME"))fieldValues[desc.getIndex("JOB_NAM")] = attrValue;    
  	      if( attrName.equals("JOB_VERSION"))fieldValues[desc.getIndex("JOB_REV")] = attrValue.toString();
  	      if( attrName.equals("STEP_NAME"))fieldValues[desc.getIndex("SBLOT_ID")] = attrValue.toString();
  	      if( attrName.equals("OPERATOR_ID"))fieldValues[desc.getIndex("OPER_NAM")] = attrValue;    
  	      if( attrName.equals("TESTER_EXEC_SW_TYPE"))fieldValues[desc.getIndex("EXEC_TYP")] = attrValue;
  	      if( attrName.equals("TESTER_EXEC_SW_VER"))fieldValues[desc.getIndex("EXEC_VER")] = attrValue;
  	      if( attrName.equals("TEST_PASS_NAME"))fieldValues[desc.getIndex("TEST_COD")] = attrValue.toString();
  	      if( attrName.equals("TEST_TEMPERATURE"))fieldValues[desc.getIndex("TST_TEMP")] = attrValue;
  	      if( attrName.equals("USER_TXT"))fieldValues[desc.getIndex("USER_TXT")] = attrValue;
  	      if( attrName.equals("AUXILIARY_FILE"))fieldValues[desc.getIndex("AUX_FILE")] = attrValue;    
  	      if( attrName.equals("PACKAGE_TYPE"))fieldValues[desc.getIndex("PKG_TYP")] = attrValue;
  	      if( attrName.equals("PRODUCT_FAMILY_ID"))fieldValues[desc.getIndex("FAMLY_ID")] = attrValue;
  	      if( attrName.equals("DATE_CODE"))fieldValues[desc.getIndex("DATE_COD")] = attrValue;
  	      if( attrName.equals("TEST_FACILITY_ID"))fieldValues[desc.getIndex("FACIL_ID")] = attrValue;
  	      if( attrName.equals("TEST_FLOOR_ID"))fieldValues[desc.getIndex("FLOOR_ID")] = attrValue;  
  	      if( attrName.equals("FAB_PROCESS_ID"))fieldValues[desc.getIndex("PROC_ID")] = attrValue;
  	      if( attrName.equals("TEST_SPECIFICATION_NAME"))fieldValues[desc.getIndex("SPEC_NAM")] = attrValue;
  	      if( attrName.equals("TEST_SPECIFICATION_VERSION"))fieldValues[desc.getIndex("SPEC_VER")] = attrValue;
  	      if( attrName.equals("FLOW_ID"))fieldValues[desc.getIndex("FLOW_ID")] = attrValue;
  	      if( attrName.equals("TEST_SETUP"))fieldValues[desc.getIndex("SETUP_ID")] = attrValue;
  	      if( attrName.equals("DESIGN_REV"))fieldValues[desc.getIndex("DSGN_REV")] = attrValue;
  	      if( attrName.equals("ENGINEERING_LOT_ID"))fieldValues[desc.getIndex("ENG_ID")] = attrValue;
  	      if( attrName.equals("ROM_CODE"))fieldValues[desc.getIndex("ROM_COD")] = attrValue;
  	      if( attrName.equals("TESTER_SERIAL_ID"))fieldValues[desc.getIndex("SERL_NUM")] = attrValue;
  	      if( attrName.equals("SUPERVISOR_ID"))fieldValues[desc.getIndex("SUPR_NAM")] = attrValue;
  	      if( attrName.equals("USER_COMMENT")){
              if(results.getInt(3) == 1){
                mrrValues[mrrDesc.getIndex("USR_DESC")] = attrValue;
              }
              if(results.getInt(3) == 2){
                mrrValues[mrrDesc.getIndex("EXC_DESC")] = attrValue;
             }
              if(results.getInt(3) == 3){
                fieldValues[desc.getIndex("USER_TXT")] = attrValue;
             }
  	      }
          if( attrName.equals("COMMENT")){
            if(results.getInt(3) == 1){
              mrrValues[mrrDesc.getIndex("USR_DESC")] = attrValue;
            }
            if(results.getInt(3) == 2){
              mrrValues[mrrDesc.getIndex("EXC_DESC")] = attrValue;
           }
            if(results.getInt(3) == 3){
              fieldValues[desc.getIndex("USER_TXT")] = attrValue;
           }
          }
  	      if( attrName.equals("RUN_START_DTTM"))fieldValues[desc.getIndex("START_T")] = (Long) convertTimeToUnix((String)attrValue);
  	      if( attrName.equals("JOB_SETUP_DTTM"))fieldValues[desc.getIndex("SETUP_T")] = (Long) convertTimeToUnix((String)attrValue);
  	      //MRR information for use later
  	      if( attrName.equals("RUN_END_DTTM"))mrrValues[mrrDesc.getIndex("FINISH_T")] = (Long) convertTimeToUnix((String)attrValue);
  	      if( attrName.equals("LOT_DISPOSITION_CODE"))mrrValues[mrrDesc.getIndex("DISP_COD")] = attrValue;
  	      if( attrName.equals("USER_LOT_DESCRIPTION"))mrrValues[mrrDesc.getIndex("USR_DESC")] = attrValue;
  	      if( attrName.equals("EXEC_LOT_DESCRIPTION"))mrrValues[mrrDesc.getIndex("EXC_DESC")] = attrValue;
  	    }
  	    results.close();
	    }else{
	      System.out.println("missing RUN_INFO");
	    }
	     // from equip
      RecordDescriptor sdrDesc=stdfTypes.get("SDR");
      String ccID = getId("CELL_CONFIGURATION");
      if(ccID == null){
         ccID = getAttrId("CELL_INVENTORY_CLASS","TESTER" );
      }
      if(ccID != null){
        results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID='"+ccID+"';");
        while(results.next()){
          String attrName = results.getString(1);
          Object attrValue = results.getObject(2);
          if( attrName.equals("TESTER_ID"))fieldValues[desc.getIndex("NODE_NAM")] = attrValue;
          if( attrName.equals("CELL_INVENTORY_ID"))fieldValues[desc.getIndex("NODE_NAM")] = attrValue;
          if( attrName.equals("TESTER_SERIAL_ID"))fieldValues[desc.getIndex("SERL_NUM")] = attrValue;
          if( attrName.equals("CELL_INVENTORY_SERIAL_ID"))fieldValues[desc.getIndex("SERL_NUM")] = attrValue;
          if( attrName.equals("SETUP_ID"))fieldValues[desc.getIndex("SETUP_ID")] = attrValue;
          if( attrName.equals("TESTER_CMD_CODE"))fieldValues[desc.getIndex("CMOD_COD")] = attrValue;   
          if( attrName.equals("TESTER_TYPE"))fieldValues[desc.getIndex("TSTR_TYP")] = attrValue;
          if( attrName.equals("CELL_INVENTORY_TYPE"))fieldValues[desc.getIndex("TSTR_TYP")] = attrValue;
          if( attrName.equals("TESTER_EXEC_SW_TYPE"))fieldValues[desc.getIndex("EXEC_TYP")] = attrValue;
          if( attrName.equals("TESTER_EXEC_SW_VER"))fieldValues[desc.getIndex("EXEC_VER")] = attrValue;
          if( attrName.equals("TESTER_MODE_CODE"))fieldValues[desc.getIndex("MODE_COD")] = attrValue;
          if( attrName.equals("CELL_INVENTORY_MODE_CODE"))fieldValues[desc.getIndex("MODE_COD")] = attrValue;
            //values from sdr that are in equip info < 007
          if( attrName.equals("HANDLER_TYPE"))sdrValues[sdrDesc.getIndex("HAND_TYP")] = attrValue;
          if( attrName.equals("HANDLER_ID"))sdrValues[sdrDesc.getIndex("HAND_ID")] = attrValue;
          if( attrName.equals("LASER_TYPE"))sdrValues[sdrDesc.getIndex("LASR_TYP")] = attrValue;
          if( attrName.equals("LASER_ID"))sdrValues[sdrDesc.getIndex("LASR_ID")] = attrValue;
        }
        results.close();
      }
      // from prod
      String prodID = getId("PRODUCT_CELL_CONFIGURATION");
      if(prodID == null){
        prodID = getId("PROGRAM_TEST_CONFIGURATION");
     }
      if(prodID != null){
       results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID='"+prodID+"';");
       while(results.next()){
         String attrName = results.getString(1);
         Object attrValue = results.getObject(2);
         if( attrName.equals("JOB_SETUP_DTTM"))fieldValues[desc.getIndex("SETUP_T")] = (Long) convertTimeToUnix((String)attrValue);
         if( attrName.equals("TEST_SPECIFICATION_NAME"))fieldValues[desc.getIndex("SPEC_NAM")] = attrValue;
         if( attrName.equals("TEST_SPECIFICATION_VERSION"))fieldValues[desc.getIndex("SPEC_VER")] = attrValue;
         if( attrName.equals("TEST_TEMPERATURE"))fieldValues[desc.getIndex("TST_TEMP")] = attrValue;
         if( attrName.equals("AUXILIARY_FILE"))fieldValues[desc.getIndex("AUX_FILE")] = attrValue;
         if( attrName.equals("DESIGN_REV"))fieldValues[desc.getIndex("DSGN_REV")] = attrValue;
         if( attrName.equals("ROM_CODE"))fieldValues[desc.getIndex("ROM_COD")] = attrValue;
         if( attrName.equals("DATE_CODE"))fieldValues[desc.getIndex("DATE_COD")] = attrValue;
         if( attrName.equals("DATA_PROTECTION_CODE"))fieldValues[desc.getIndex("PROT_COD")] = attrValue;
         if( attrName.equals("SITE_COUNT")) siteCount = (Integer)attrValue;
         if( attrName.equals("JOB_NAME"))fieldValues[desc.getIndex("JOB_NAM")] = attrValue;
         if( attrName.equals("JOB_VERSION"))fieldValues[desc.getIndex("JOB_REV")] = attrValue;
         if( attrName.equals("PACKAGE_TYPE"))fieldValues[desc.getIndex("PKG_TYP")] = attrValue;
         if( attrName.equals("PRODUCT_ID"))fieldValues[desc.getIndex("PART_TYP")] = attrValue;
         if( attrName.equals("FAB_PROCESS_ID"))fieldValues[desc.getIndex("PROC_ID")] = attrValue;
         if( attrName.equals("PRODUCT_FAMILY_ID"))fieldValues[desc.getIndex("FAMLY_ID")] = attrValue;
         if( attrName.equals("SETUP_ID"))fieldValues[desc.getIndex("SETUP_ID")] = attrValue;
         if( attrName.equals("JOB_SETUP_DTTM"))fieldValues[desc.getIndex("SETUP_T")] = (Long) convertTimeToUnix((String)attrValue);
       }
       results.close();
      }
     RecordData data = new RecordData(desc, fieldValues);
     Record record = new Record(desc,data );
     records.add(record);
	  }
	  
	  
	  private void generateSdr() throws SQLException{
	    // version 007 and after
	    RecordDescriptor sdrDesc=stdfTypes.get("SDR");
		  sdrValues[sdrDesc.getIndex("HEAD_NUM")] = 1;
		  sdrValues[sdrDesc.getIndex("SITE_GRP")] = 1;
		  sdrValues[sdrDesc.getIndex("SITE_CNT")] = siteCount;
		  // get the hardware
      ResultSet hinfo = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='CELL_INVENTORY';");
      while(hinfo.next()){
        String hwClass = null;
        String hwType = null;
        String hwId = null;
        ResultSet results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(hinfo.getString(1))+";");
          while(results.next()){
            String attrName = results.getString(1);
            Object attrValue = results.getObject(2);   
            if( attrName.equals("CELL_INVENTORY_CLASS")) hwClass = (String)attrValue;
            if( attrName.equals("CELL_INVENTORY_TYPE")) hwType = (String)attrValue;
            if( attrName.equals("CELL_INVENTORY_ID")) hwId = (String)attrValue;
          }
        results.close();
        if(hwClass.equals("LOADBOARD")){
          sdrValues[sdrDesc.getIndex("LOAD_TYP")] = hwType;
          sdrValues[sdrDesc.getIndex("LOAD_ID")] = hwId;
        }
        if(hwClass.equals("DIB")){
          sdrValues[sdrDesc.getIndex("DIB_TYP")] = hwType;
          sdrValues[sdrDesc.getIndex("DIB_ID")] = hwId;
        }
      }
		  // get the set of site_info and iterate over them, should only be one group
      Object[] sites = new Object[(int)(siteCount)];
      // for each site info get the values    
		  ResultSet sinfo = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SITE_INFO';");
		  int siteIndex = 0;
		  while(sinfo.next()){
	        ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(sinfo.getString(1))+";");
	        while(results.next()){
	          String attrName = results.getString(1);
	          Object attrValue = results.getObject(2);   
	          if( attrName.equals("SITE_GROUP"))sdrValues[sdrDesc.getIndex("SITE_GRP")] = attrValue;
	          if( attrName.equals("SITE_ID")){
	        	  sites[siteIndex++] = ((Integer) attrValue).longValue();
	        	  siteNames.put(sinfo.getInt(1), ((Integer) attrValue));
	          }
	        }
	        results.close();
		    }
      sdrValues[sdrDesc.getIndex("SITE_CNT")] = new Long(siteCount);
      sdrValues[sdrDesc.getIndex("SITE_NUM")] = sites;  // array of Long
      RecordData data = new RecordData(sdrDesc, sdrValues);
      Record record = new Record(sdrDesc,data );
      records.add(record);
      sinfo.close();
    }
	  
	  private void generateSdrOld() throws SQLException{
	    // legacy conversion
      RecordDescriptor sdrDesc=stdfTypes.get("SDR");
      sdrValues[sdrDesc.getIndex("HEAD_NUM")] = 1;
      sdrValues[sdrDesc.getIndex("SITE_GRP")] = 1;
      sdrValues[sdrDesc.getIndex("SITE_CNT")] = siteCount;
      // get the hardware
      ResultSet hinfo = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='HARDWARE';");
      while(hinfo.next()){
        String hwClass = null;
        String hwType = null;
        String hwId = null;
        ResultSet results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(hinfo.getString(1))+";");
          while(results.next()){
            String attrName = results.getString(1);
            Object attrValue = results.getObject(2);   
            if( attrName.equals("HW_CLASS")) hwClass = (String)attrValue;
            if( attrName.equals("HW_TYPE")) hwType = (String)attrValue;
            if( attrName.equals("HW_ID")) hwId = (String)attrValue;
          }
        results.close();
        if(hwClass.equals("LOADBOARD")){
          sdrValues[sdrDesc.getIndex("LOAD_TYP")] = hwType;
          sdrValues[sdrDesc.getIndex("LOAD_ID")] = hwId;
        }
        if(hwClass.equals("DIB")){
          sdrValues[sdrDesc.getIndex("DIB_TYP")] = hwType;
          sdrValues[sdrDesc.getIndex("DIB_ID")] = hwId;
        }
      }
      // get the set of site_info and iterate over them, should only be one group
      Object[] sites = new Object[(int)(siteCount)];
      // for each site info get the values    
      ResultSet sinfo = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SITE_INFO';");
      int siteIndex = 0;
      while(sinfo.next()){
          ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(sinfo.getString(1))+";");
          while(results.next()){
            String attrName = results.getString(1);
            Object attrValue = results.getObject(2);   
            if( attrName.equals("SITE_GROUP_NUMBER"))sdrValues[sdrDesc.getIndex("SITE_GRP")] = attrValue;
            if( attrName.equals("SITE_ID")){
              sites[siteIndex++] = ((Integer) attrValue).longValue();
              siteNames.put(sinfo.getInt(1), ((Integer) attrValue));
            }
          }
          results.close();
        }
      sdrValues[sdrDesc.getIndex("SITE_CNT")] = new Long(siteCount);
      sdrValues[sdrDesc.getIndex("SITE_NUM")] = sites;  // array of Long
      RecordData data = new RecordData(sdrDesc, sdrValues);
      Record record = new Record(sdrDesc,data );
      records.add(record);
      sinfo.close();
    }
	  
	  private void generateTsr() throws SQLException{
		    // get the set of TSRs and iterate over them
		  RecordDescriptor desc=stdfTypes.get("TSR");
		  ResultSet tsrs = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='RESULT_SUMMARY';");
		  while(tsrs.next()){
				Object[] fieldValues =  new Object[(desc).size()];
	        	fieldValues[desc.getIndex("TEST_TIM")] =  0.0;
	        	fieldValues[desc.getIndex("TEST_TYP")] =  "P";
	        	fieldValues[desc.getIndex("ALRM_CNT")] =  4294967295L;
            fieldValues[desc.getIndex("FAIL_CNT")] =  4294967295L;
            fieldValues[desc.getIndex("EXEC_CNT")] =  4294967295L;
	        	fieldValues[desc.getIndex("SITE_NUM")] =  0;
            fieldValues[desc.getIndex("TEST_MIN")] =  0.0D;
            fieldValues[desc.getIndex("TEST_MAX")] =  0.0D;
            fieldValues[desc.getIndex("TST_SUMS")] =  0.0D;
            fieldValues[desc.getIndex("TST_SQRS")] =  0.0D;
	        	fieldValues[desc.getIndex("HEAD_NUM")] =  255;  //default to all sites
            int options = 255;
			  	// for each tsr get the values
	        	ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(tsrs.getString(1))+";");
		        while(results.next()){
		          String attrName = results.getString(1);
		          Object attrValue = results.getObject(2); 
		          if( attrName.equals("SUMMARY_TYPE")){
		        	  if(attrValue.equals("SITE")){
		        		  fieldValues[desc.getIndex("HEAD_NUM")] = 1;
		        	  }
		          }
		          if( attrName.equals("SITE_ID")){
		        	  fieldValues[desc.getIndex("SITE_NUM")] = attrValue;
		          }
		          if( attrName.equals("SITE_INFO_EID")){
		            fieldValues[desc.getIndex("SITE_NUM")] = siteNames.get((Integer) attrValue);
		          }
		          if( attrName.equals("TEST_TYPE"))fieldValues[desc.getIndex("TEST_TYP")] = attrValue;
		          if( attrName.equals("TEST_ID"))fieldValues[desc.getIndex("TEST_NUM")] = attrValue;
		          if( attrName.equals("TEST_EXECUTION_COUNT"))fieldValues[desc.getIndex("EXEC_CNT")] = attrValue;
		          if( attrName.equals("TEST_FAIL_COUNT"))fieldValues[desc.getIndex("FAIL_CNT")] = attrValue;
		          if( attrName.equals("TEST_ALARM_COUNT"))fieldValues[desc.getIndex("ALRM_CNT")] = attrValue;
		          if( attrName.equals("RESULT_NAME"))fieldValues[desc.getIndex("TEST_NAM")] = attrValue;
		          if( attrName.equals("TEST_SEQUENCER_NAME"))fieldValues[desc.getIndex("SEQ_NAME")] = attrValue;
		          if( attrName.equals("TEST_LABEL"))fieldValues[desc.getIndex("TEST_LBL")] = attrValue;
		          if( attrName.equals("AVERAGE_TEST_TIME")){
		        	  fieldValues[desc.getIndex("TEST_TIM")] = attrValue;
		        	  options = options & 0xfb;
		          }
		          if( attrName.equals("MINIMUM_TEST_VALUE")){
		          	  fieldValues[desc.getIndex("TEST_MIN")] = results.getDouble(2);
		        	  options = options & 0xfe;
		          }
		          if( attrName.equals("MAXIMUM_TEST_VALUE")){
			          fieldValues[desc.getIndex("TEST_MAX")] = results.getDouble(2);
		        	  options = options & 0xfd;
		          }
		          if( attrName.equals("SUM_TEST_VALUES")){
			          fieldValues[desc.getIndex("TST_SUMS")] = results.getDouble(2);
		        	  options = options & 0xef;
		          }
		          if( attrName.equals("SUMOFSQUARES_TEST_VALUES")){
			          fieldValues[desc.getIndex("TST_SQRS")] = results.getDouble(2);
		        	  options = options & 0xdf;
		          }
		        }
		        results.close();
	        	fieldValues[desc.getIndex("OPT_FLAG")] =  options;
		        RecordData data = new RecordData(desc, fieldValues);
		        Record record = new Record(desc,data );
		        records.add(record);
		  	}
	        tsrs.close();
		    }
	  
	  private void generateHbr() throws SQLException{
		    // get the set of hbrs and iterate over them
		  RecordDescriptor desc=stdfTypes.get("HBR");
		  ResultSet hbrs = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='HARDBIN';");
		  while(hbrs.next()){
			  	boolean site = false;
			  	// for each hbr  get the values
				Object[] fieldValues =  new Object[(desc).size()];
				fieldValues[desc.getIndex("SITE_NUM")] = 1;
        fieldValues[desc.getIndex("HBIN_CNT")] = 0;
        ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(hbrs.getString(1))+";");
        while(results.next()){
          String attrName = results.getString(1);
          Object attrValue = results.getObject(2);   
          if( attrName.equals("SITE_ID")){
        	  site = true;
        	  fieldValues[desc.getIndex("SITE_NUM")] = attrValue;
          }
          if( attrName.equals("SITE_INFO_EID")){
            site = true;
            fieldValues[desc.getIndex("SITE_NUM")] = siteNames.get((Integer) attrValue);
          }
          if( attrName.equals("BIN_NUMBER"))fieldValues[desc.getIndex("HBIN_NUM")] = attrValue;
          if( attrName.equals("BIN_COUNT"))fieldValues[desc.getIndex("HBIN_CNT")] = attrValue;
          if( attrName.equals("BIN_PF"))fieldValues[desc.getIndex("HBIN_PF")] = attrValue;
          if( attrName.equals("BIN_NAME"))fieldValues[desc.getIndex("HBIN_NAM")] = attrValue;

        }
        if(site){
        	fieldValues[desc.getIndex("HEAD_NUM")] = 1;
        }else{
        	fieldValues[desc.getIndex("HEAD_NUM")] = 255;
        }
        results.close();
        RecordData data = new RecordData(desc, fieldValues);
        Record record = new Record(desc,data );
        records.add(record);
		    }
	      hbrs.close();
		    }
	  
	  private void generateSbr() throws SQLException{
		    // get the set of sbrs and iterate over them
		  RecordDescriptor desc=stdfTypes.get("SBR");
		  // ge eids of all softbins
		  ResultSet sbrs = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SOFTBIN';");
		  while(sbrs.next()){
			  	// for each sbr get the BIN entity
				Object[] fieldValues =  new Object[(desc).size()];
        fieldValues[desc.getIndex("SITE_NUM")] = 1;
        fieldValues[desc.getIndex("SBIN_CNT")] = 0;
        ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(sbrs.getString(1))+";");
        while(results.next()){
          String attrName = results.getString(1);
          Object attrValue = results.getObject(2);   
          if( attrName.equals("BIN_NUMBER"))fieldValues[desc.getIndex("SBIN_NUM")] = attrValue;
          if( attrName.equals("BIN_PF"))fieldValues[desc.getIndex("SBIN_PF")] = attrValue;
          if( attrName.equals("BIN_NAME"))fieldValues[desc.getIndex("SBIN_NAM")] = attrValue;
        }
        results.close();
        // now we get the bin summary  bin_eid and type = bin summary
        ResultSet sums = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where name = 'BIN_EID' and value ="+(sbrs.getString(1))+";");
        while(sums.next()){
          Object[] sumFields = Arrays.copyOf(fieldValues, fieldValues.length);
          results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(sums.getString(1))+";");
          boolean valid = false;
          while(results.next()){
            String attrName = results.getString(1);
            Object attrValue = results.getObject(2);
            if( attrName.equals("SUMMARY_TYPE")){
              valid  = true;
              if(((String) attrValue).equals("SITE")){
                sumFields[desc.getIndex("HEAD_NUM")] = 1;
              }else{
                sumFields[desc.getIndex("HEAD_NUM")] = 255;
              }
            }
          if( attrName.equals("SITE_INFO_EID")){
            sumFields[desc.getIndex("SITE_NUM")] = siteNames.get((Integer) attrValue);
          }
          if( attrName.equals("BIN_COUNT"))sumFields[desc.getIndex("SBIN_CNT")] = attrValue;
          }
          results.close();
          if(valid){
            RecordData data = new RecordData(desc, sumFields);
            Record record = new Record(desc,data );
            records.add(record);
          }
		    }
        sums.close();
		  }
	    sbrs.close();
    }
	  
	  private void generatePcr() throws SQLException{
		    // get the set of pcrs and iterate over them
		  RecordDescriptor desc=stdfTypes.get("PCR");
		  ResultSet pcrs  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='RUN_SUMMARY';");
		  while(pcrs.next()){
			  	// for each sbr  get the values
			  	Object[] fieldValues =  new Object[(desc).size()];
			  	fieldValues[desc.getIndex("RTST_CNT")] =  4294967295L;
          fieldValues[desc.getIndex("ABRT_CNT")] =  4294967295L;
      		fieldValues[desc.getIndex("SITE_NUM")] =  0;
      		fieldValues[desc.getIndex("HEAD_NUM")] =  255;  //default to all sites
	        ResultSet results = sqlStatement.executeQuery("select name, value from "+ _mainTable+" where entityID="+(pcrs.getString(1))+";");
	        while(results.next()){
	          String attrName = results.getString(1);
	          Object attrValue = results.getObject(2);
	          if( attrName.equals("SUMMARY_TYPE")){
	        	  if(attrValue.equals("SITE")){
	        		  fieldValues[desc.getIndex("HEAD_NUM")] = 1;
	        	  }
	          }
	          if( attrName.equals("PART_COUNT"))fieldValues[desc.getIndex("PART_CNT")] = attrValue;
	          if( attrName.equals("RETEST_PART_COUNT"))fieldValues[desc.getIndex("RTST_CNT")] = attrValue;
	          if( attrName.equals("ABORT_PART_COUNT"))fieldValues[desc.getIndex("ABRT_CNT")] = attrValue;
	          if( attrName.equals("GOOD_PART_COUNT")){
	        	  fieldValues[desc.getIndex("GOOD_CNT")] = attrValue;
	        	  fieldValues[desc.getIndex("FUNC_CNT")] = attrValue;
	          }
	          if( attrName.equals("SITE_ID")){
	        	  fieldValues[desc.getIndex("SITE_NUM")] = attrValue;
	          }
	          if( attrName.equals("SITE_INFO_EID")){
	            fieldValues[desc.getIndex("SITE_NUM")] = siteNames.get((Integer) attrValue);
	          }
	        }
	        results.close();
	        RecordData data = new RecordData(desc, fieldValues);
	        Record record = new Record(desc,data );
	        records.add(record);
		    }
		  pcrs.close();
		    }
	  
	  private void generatePtr() throws SQLException{
		    // get the test events and create pir, ptr and prr as needed
		  RecordDescriptor pirDesc=stdfTypes.get("PIR");
		  RecordDescriptor prrDesc=stdfTypes.get("PRR");
		  RecordDescriptor ptrDesc=stdfTypes.get("PTR");
		  String limitNameString = null;
		  String limitSet = null;
		   // get the name for the limit file which is in the test program entity
      // get the entityID
      String prodID = getId("PRODUCT_CELL_CONFIGURATION");
      if(prodID == null){
        prodID = getId("PROGRAM_TEST_CONFIGURATION");
     }
		  ResultSet limitName  = null;
		  limitName  = _sqlConnection.createStatement().executeQuery("select value from "+ _mainTable+" where name='TEST_SPECIFICATION_NAME' AND entityId = "+ prodID.toString()  + ";");
		  if(limitName.next()){
			  limitNameString = limitName.getString(1);		  
		  }
		  limitName.close();
		  // get the eid for the limit file
		  if(limitNameString != null){
	      ResultSet limitEid  = null;
	      if( ritdbVer.equals("ALPHA_P004")){
	        limitEid  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where name='LIMITS_NAME' and value='"+limitNameString+"';");
	      }else{
          limitEid  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where name='LIMIT_SET_NAME' and value='"+limitNameString+"';");
          }
	      if(limitEid.next()) limitSet = limitEid.getString(1);
    		limitEid.close();
			  }
		  // now get the eids for all of the test events
	     ResultSet events  = null;
       if( ritdbVer.equals("ALPHA_P004")){
         events  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='TEST_EVENT';");
       }else{
         events  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='PART_RESULT_EVENT';"); 
       }
		  while(events.next()){
			  	// build the PIR and PRR fields
			  Object[] pirValues =  new Object[(pirDesc).size()];
			  Object[] prrValues =  new Object[(prrDesc).size()];
			  pirValues[pirDesc.getIndex("HEAD_NUM")] = 1;
			  prrValues[prrDesc.getIndex("HEAD_NUM")] = 1;
			  prrValues[prrDesc.getIndex("X_COORD")] = -32768;
			  prrValues[prrDesc.getIndex("Y_COORD")] = -32768;
			  prrValues[prrDesc.getIndex("PART_FIX")] = new byte[0];
			  prrValues[prrDesc.getIndex("HARD_BIN")] = 0;
			  prrValues[prrDesc.getIndex("SOFT_BIN")] = 32767;  // default value
			  Long site = 1L;
	    	  int flags = 0;
		      ResultSet pir = _sqlConnection.createStatement().executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(events.getString(1))+";");
		      while(pir.next()){
		          String attrName = pir.getString(1);
		          Object attrValue = pir.getObject(2); 
		          if( attrName.equals("SITE_ID")){
		        	  site = pir.getLong(2);
		        	  pirValues[pirDesc.getIndex("SITE_NUM")] = site;
		        	  prrValues[prrDesc.getIndex("SITE_NUM")] = site;
		          }
		          if( attrName.equals("SITE_INFO_EID")){
		            site = new Long(siteNames.get((Integer) attrValue));
                pirValues[pirDesc.getIndex("SITE_NUM")] = site;
                prrValues[prrDesc.getIndex("SITE_NUM")] = site;
		          }
		          if( attrName.equals("NUM_TESTS"))prrValues[prrDesc.getIndex("NUM_TEST")] = attrValue;
		          if( attrName.equals("BIN_EID")){
                int index = pir.getInt(3);
  		          if( ritdbVer.equals("ALPHA_P004")){
    		            if(index == 0){
    		               prrValues[prrDesc.getIndex("HARD_BIN")] = Long.parseLong(hardNames.get((Integer)attrValue));	              
    		            }else{
    		              prrValues[prrDesc.getIndex("SOFT_BIN")] = Long.parseLong(softNames.get((Integer)attrValue));
    		            }
  		          }else{
                  if(index == 1){
                    prrValues[prrDesc.getIndex("HARD_BIN")] = Long.parseLong(hardNames.get((Integer)attrValue));               
                 }else{
                   prrValues[prrDesc.getIndex("SOFT_BIN")] = Long.parseLong(softNames.get((Integer)attrValue));
                 }
             }
		          }
		          if( attrName.equals("X"))prrValues[prrDesc.getIndex("X_COORD")] = attrValue;
		          if( attrName.equals("Y"))prrValues[prrDesc.getIndex("Y_COORD")] = attrValue;
		          if( attrName.equals("UNIT_TEST_TIME")){
		        	  Long time = (long)((pir.getDouble(2)) * 1000.0);  // time in ms from seconds
		        	  prrValues[prrDesc.getIndex("TEST_T")] = time;
		          }
		          if( attrName.equals("PART_ID"))prrValues[prrDesc.getIndex("PART_ID")] = pir.getString(2);
		          if( attrName.equals("PART_TEXT"))prrValues[prrDesc.getIndex("PART_TXT")] = attrValue;
		          if( attrName.equals("RETEST_CODE")) flags = flags | 0x1  ;
		          if( attrName.equals("PF")){
		        	  if(((String) attrValue).equals("PASS")) flags = flags | 0x0;
		        	  if(((String) attrValue).equals("FAIL")) flags = flags | 0x8;
		        	  if(((String) attrValue).equals("TESTED")) flags = flags | 0x10;
		        	  if(((String) attrValue).equals("ABORT")) flags = flags | 0x4;
		           prrValues[prrDesc.getIndex("PART_FLG")] = flags;  
		          }
		      }
		      pir.close();
			  	// write the PIR
		      RecordData data = new RecordData(pirDesc, pirValues);
		      Record record = new Record(pirDesc,data );
		      records.add(record);
		      Object[] ptrValues =  null;
			  	// for each event  get the PTR values
		        ResultSet results = sqlStatement.executeQuery("select indexID, value, value2 from "+ _mainTable+" where name='R' and entityID="+(events.getString(1))+";");
		        while(results.next()){
		      	  // if this is the first time or if we need to duplicate it get the full info for the testInfo
	  	          if((!testNumbers.containsKey(results.getInt(1))) || duplicatePtrData){ 
	  		      	  ptrValues =  new Object[(ptrDesc).size()];
                  ptrValues[ptrDesc.getIndex("PARM_FLG")] = -64;
                  // these are set to values, if not used the opt_flag declares them to be invalid
	  	 	          ptrValues[ptrDesc.getIndex("RES_SCAL")] = 0;
	  	 	          ptrValues[ptrDesc.getIndex("LLM_SCAL")] = 0;
	  	 	          ptrValues[ptrDesc.getIndex("HLM_SCAL")] = 0;
  	  	          ptrValues[ptrDesc.getIndex("HI_LIMIT")] = 0.0;
  	  	          ptrValues[ptrDesc.getIndex("LO_LIMIT")] = 0.0;
  	  	          ptrValues[ptrDesc.getIndex("LO_SPEC")] = 0.0;
  	  	          ptrValues[ptrDesc.getIndex("HI_SPEC")] = 0.0;

	  	        	int optFlag = 255;
			        ResultSet testInfo = _sqlConnection.createStatement().executeQuery("select name, value  from "+ _mainTable+" where entityID="+(results.getString(1))+";");
			        while(testInfo.next()){
			        	String attrName = testInfo.getString(1);
			        	Object attrValue = testInfo.getObject(2);
				        if( attrName.equals("RESULT_NUMBER")){
				        	ptrValues[ptrDesc.getIndex("TEST_NUM")] = attrValue;
				        	testNumbers.put(results.getInt(1), testInfo.getInt(2));
				        }
				        if( attrName.equals("RESULT_NAME")){
				        	ptrValues[ptrDesc.getIndex("TEST_TXT")] = attrValue;
				        	testNames.put(results.getInt(1), testInfo.getString(2));
				        }
				        if( attrName.equals("ALARM_ID"))ptrValues[ptrDesc.getIndex("ALARM_ID")] = attrValue;
				        if( attrName.equals("R_SCALE")){
				        	int scale = ((int) Math.round(Math.log10(testInfo.getDouble(2))));
				        	optFlag = optFlag & 0xfe;
				        	ptrValues[ptrDesc.getIndex("RES_SCAL")] = scale;
					        ptrValues[ptrDesc.getIndex("LLM_SCAL")] = scale;
					        ptrValues[ptrDesc.getIndex("HLM_SCAL")] = scale;
				        }
				        if( attrName.equals("UNITS"))ptrValues[ptrDesc.getIndex("UNITS")] = attrValue;
                if( attrName.equals("RESULT_SCALE")){
                  int scale = ((int) Math.round(Math.log10(testInfo.getDouble(2))));
                  optFlag = optFlag & 0xfe;
                  ptrValues[ptrDesc.getIndex("RES_SCAL")] = scale;
                  ptrValues[ptrDesc.getIndex("LLM_SCAL")] = scale;
                  ptrValues[ptrDesc.getIndex("HLM_SCAL")] = scale;
                }
                if( attrName.equals("RESULT_UNITS"))ptrValues[ptrDesc.getIndex("UNITS")] = attrValue;
				        ptrValues[ptrDesc.getIndex("OPT_FLAG")] = optFlag;
			        }
			        testInfo.close();
			        // LIMITS
			        if(limitSet != null){
			        	ResultSet limits = _sqlConnection.createStatement().executeQuery("select name, value from "+ _mainTable+" where entityID="+limitSet+" and indexID="+(results.getString(1))+";");
				        while(limits.next()){
				        	String attrName = limits.getString(1);
					        if( attrName.equals("UL")){
					        	optFlag = optFlag & 0x5f;
					        	ptrValues[ptrDesc.getIndex("HI_LIMIT")] = limits.getDouble(2);
					        }
					        if( attrName.equals("LL")){
					        	optFlag = optFlag & 0xaf;
					        	ptrValues[ptrDesc.getIndex("LO_LIMIT")] = limits.getDouble(2);
					        }
					        if( attrName.equals("USL")){
					        	optFlag = optFlag & 0xf7;
					        	ptrValues[ptrDesc.getIndex("HI_SPEC")] = limits.getDouble(2);
					        }
					        if( attrName.equals("LSL")){
					        	optFlag = optFlag & 0xfb;
					        	ptrValues[ptrDesc.getIndex("LO_SPEC")] = limits.getDouble(2);
					        }
				        }
				        limits.close();
				    }
			        ptrValues[ptrDesc.getIndex("OPT_FLAG")] = optFlag;
	  	          }else{
	  	        	ptrValues =  new Object[8];  // don't write the optional data
			        ptrValues[ptrDesc.getIndex("TEST_NUM")] = testNumbers.get(results.getInt(1));
			        if(duplicateTestName){
			        	ptrValues[ptrDesc.getIndex("TEST_TXT")] = testNames.get(results.getInt(1));
			        }
	  	          }
			    // now insert the data and the flag
		        ptrValues[ptrDesc.getIndex("SITE_NUM")] = site;
		        ptrValues[ptrDesc.getIndex("HEAD_NUM")] = 1;
		  	    ptrValues[ptrDesc.getIndex("RESULT")] = 0.0;  
		        ptrValues[ptrDesc.getIndex("RESULT")] = results.getDouble(2);
		        flags = 0;
		        if(results.getString(3).equals("P")) flags = 0;		//pass
		        if(results.getString(3).equals("F")) flags = 128;	//fail
		        if(results.getString(3).equals("T")) flags = 0;	// tested no limits so passed
		        if(results.getString(3).equals("X")) flags = 0x10;	// skipped no data
		        if(results.getString(3) == null) flags = 64;
		        ptrValues[ptrDesc.getIndex("TEST_FLG")] = flags;
		        ptrValues[ptrDesc.getIndex("PARM_FLG")] = -64;
		        if(!(results.getString(3).equals("X") && skipEmptyTests)){
			        data = new RecordData(ptrDesc, ptrValues);
			        record = new Record(ptrDesc,data );
			        records.add(record); 
		        }
		        }
			    results.close();       
			  	// write the PRR
		        data = new RecordData(prrDesc, prrValues);
		        record = new Record(prrDesc,data );
		        records.add(record);
		  }
		  events.close();
	  }
	  
	  private void generateMrr() throws SQLException{
		    // These have been updated through out
	    RecordDescriptor desc=stdfTypes.get("MRR");
      RecordData data = new RecordData(desc, mrrValues);
      Record record = new Record(desc,data );
      records.add(record);
	  }
	  
	  /**Genrates the WIR, only supports one wafer per stdf file
	   * generates a WIR
	   * @throws SQLException
	   */
	  private void generateWir() throws SQLException{
		  Object[] fieldValues =  null;
		  RecordDescriptor desc=stdfTypes.get("WIR");
		  ResultSet wirs  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SUBSTRATE_EVENT';");
      if(!wirs.next()){
        wirs.close();
        return;
      }
		  String wirEid = wirs.getString(1);
		  wirs.close();
			fieldValues =  new Object[(desc).size()];
      fieldValues[desc.getIndex("SITE_GRP")] = 255;
      fieldValues[desc.getIndex("HEAD_NUM")] = 1;
      ResultSet results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(wirEid)+";");
      while(results.next()){
	      	String attrName = results.getString(1);
	      	Object attrValue = results.getObject(2);
	        if( attrName.equals("SUBSTRATE_START_DTTM"))fieldValues[desc.getIndex("START_T")] = (Long) convertTimeToUnix((String)attrValue);
          if( attrName.equals("SUBSTRATE_ID")){
            fieldValues[desc.getIndex("WAFER_ID")] = attrValue;
          }
      }
      results.close();
      RecordData data = new RecordData(desc, fieldValues);
      Record record = new Record(desc,data );
      records.add(record);
		  } 
	  
	  private void generateWrr() throws SQLException{
      // get the wrr info now as well
     RecordDescriptor wrrDesc=stdfTypes.get("WRR");
     wrrValues =  new Object[(wrrDesc).size()];
     wrrValues[wrrDesc.getIndex("SITE_GRP")] = 255;
     wrrValues[wrrDesc.getIndex("HEAD_NUM")] = 1;
     wrrValues[wrrDesc.getIndex("RTST_CNT")] = 4294967295L;
     wrrValues[wrrDesc.getIndex("ABRT_CNT")] = 4294967295L;
     wrrValues[wrrDesc.getIndex("FUNC_CNT")] = 4294967295L;
     ResultSet wrrs  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SUBSTRATE_EVENT';");
     if(!wrrs.next()){
       wrrs.close();
       return;
     }
     String wrrEid = wrrs.getString(1);
     wrrs.close();
     ResultSet results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(wrrEid)+";");
     while(results.next()){
         String attrName = results.getString(1);
         Object attrValue = results.getObject(2);
         if( attrName.equals("SUBSTRATE_STOP_DTTM"))wrrValues[wrrDesc.getIndex("FINISH_T")] = (Long) convertTimeToUnix((String)attrValue);
         if( attrName.equals("WAFER_FRAME_ID"))wrrValues[wrrDesc.getIndex("FRAME_ID")] = attrValue;
         if( attrName.equals("WAFER_MASK_ID"))wrrValues[wrrDesc.getIndex("MASK_ID")] = attrValue;
         if( attrName.equals("SUBSTRATE_USER_DESC"))wrrValues[wrrDesc.getIndex("USR_DESC")] = attrValue;
         if( attrName.equals("SUBSTRATE_EXEC_DESC"))wrrValues[wrrDesc.getIndex("EXC_DESC")] = attrValue;
         if( attrName.equals("SUBSTRATE_ID")){
           wrrValues[wrrDesc.getIndex("WAFER_ID")] = attrValue;
         }
         if( attrName.equals("PART_COUNT"))wrrValues[wrrDesc.getIndex("PART_CNT")] = attrValue;
         if( attrName.equals("RETEST_PART_COUNT"))wrrValues[wrrDesc.getIndex("RTST_CNT")] = attrValue;
         if( attrName.equals("ABORT_PART_COUNT"))wrrValues[wrrDesc.getIndex("ABRT_CNT")] = attrValue;
         if( attrName.equals("GOOD_PART_COUNT")){
             wrrValues[wrrDesc.getIndex("GOOD_CNT")] = attrValue;
             wrrValues[wrrDesc.getIndex("FUNC_CNT")] = attrValue;
         }
       } 
      results.close();
      results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where value='WAFER_SUMMARY';");
      while(results.next()){
          String attrName = results.getString(1);
          Object attrValue = results.getObject(2);
          if( attrName.equals("PART_COUNT"))wrrValues[wrrDesc.getIndex("PART_CNT")] = attrValue;
          if( attrName.equals("RETEST_PART_COUNT"))wrrValues[wrrDesc.getIndex("RTST_CNT")] = attrValue;
          if( attrName.equals("ABORT_PART_COUNT"))wrrValues[wrrDesc.getIndex("ABRT_CNT")] = attrValue;
          if( attrName.equals("GOOD_PART_COUNT")){
              wrrValues[wrrDesc.getIndex("GOOD_CNT")] = attrValue;
              wrrValues[wrrDesc.getIndex("FUNC_CNT")] = attrValue;
          }
        } 
       results.close();
		  records.add(new Record(wrrDesc,(new RecordData(wrrDesc, wrrValues))));
	  }
	  
	  private void generateWcr() throws SQLException{
		  Object[] fieldValues =  null;
		  RecordDescriptor desc=stdfTypes.get("WCR");
		  ResultSet wcrs  = _sqlConnection.createStatement().executeQuery("select entityID from "+ _mainTable+" where value='SUBSTRATE_INFO';");
		  if(!wcrs.next()){
		    wcrs.close();
		    return;
		  }
      String wcrEid = wcrs.getString(1);
      wcrs.close();
			fieldValues =  new Object[(desc).size()];
			fieldValues[desc.getIndex("WF_UNITS")] = 0L;
			fieldValues[desc.getIndex("DIE_HT")] = 0.0;
	     fieldValues[desc.getIndex("DIE_WID")] = 0.0;
      fieldValues[desc.getIndex("WAFR_SIZ")] = 0.0;
      fieldValues[desc.getIndex("CENTER_X")] = 0;
      fieldValues[desc.getIndex("CENTER_Y")] = 0;
      fieldValues[desc.getIndex("WF_FLAT")] = " ";
      ResultSet results = sqlStatement.executeQuery("select name, value, indexID from "+ _mainTable+" where entityID="+(wcrEid)+";");
        while(results.next()){
          String attrName = results.getString(1);
          Object attrValue = results.getObject(2);
		      if( attrName.equals("WAFER_SIZE"))fieldValues[desc.getIndex("WAFR_SIZ")] = attrValue;
		      //if( attrName.equals("DIE_HEIGHT"))fieldValues[desc.getIndex("DIE_HT")] = attrValue;
		      //if( attrName.equals("DIE_WIDTH"))fieldValues[desc.getIndex("DIE_WID")] = attrValue;
		      if( attrName.equals("CENTER_X"))fieldValues[desc.getIndex("CENTER_X")] = attrValue;
		      if( attrName.equals("CENTER_Y"))fieldValues[desc.getIndex("CENTER_Y")] = attrValue;
          if( attrName.equals("SUBSTRATE_ORIENTATION")){
            if((Long)attrValue == 0L)fieldValues[desc.getIndex("WF_FLAT")] = "D";
            if((Long)attrValue == 90L)fieldValues[desc.getIndex("WF_FLAT")] = "L";
            if((Long)attrValue == 180L)fieldValues[desc.getIndex("WF_FLAT")] = "U";
            if((Long)attrValue == 270L)fieldValues[desc.getIndex("WF_FLAT")] = "R";
          }
          if( attrName.equals("AXIS_DIRECTION")){
            if(attrValue.equals("UpLeft")){
              fieldValues[desc.getIndex("POS_Y")] = "U";
              fieldValues[desc.getIndex("POS_X")] = "L";
            }
            if(attrValue.equals("DownLeft")){
              fieldValues[desc.getIndex("POS_Y")] = "D";
              fieldValues[desc.getIndex("POS_X")] = "L";
            }
            if(attrValue.equals("UpRight")){
              fieldValues[desc.getIndex("POS_Y")] = "U";
              fieldValues[desc.getIndex("POS_X")] = "R";
            }
            if(attrValue.equals("DownRight")){
              fieldValues[desc.getIndex("POS_Y")] = "D";
              fieldValues[desc.getIndex("POS_X")] = "R";
            }

          } 
		      if( attrName.equals("SUBSTRATE_UNITS")){
		    	  if(attrValue.equals("NONE"))fieldValues[desc.getIndex("WF_UNITS")] = 0L;
		    	  if(attrValue.equals("in"))fieldValues[desc.getIndex("WF_UNITS")] = 1L;
		    	  if(attrValue.equals("cm"))fieldValues[desc.getIndex("WF_UNITS")] = 2L;
		    	  if(attrValue.equals("mm"))fieldValues[desc.getIndex("WF_UNITS")] = 3L;
		    	  if(attrValue.equals("mil"))fieldValues[desc.getIndex("WF_UNITS")] = 4L;
		      }	
        }
      results.close();
		  records.add(new Record(desc,(new RecordData(desc, fieldValues))));
	  }
	  
	  /**Utility function to return the tables names in a  database.
	   * note: expects an already open SQL Connection to database.
	   * */
	  public ArrayList<String> getDbTableNames(Connection sqlConnection) {
	      ArrayList<String> tableNames = new ArrayList<String>(); //list of tables in the database
	    try {
	      DatabaseMetaData md = sqlConnection.getMetaData(); //get info on database tables
	      ResultSet rs = md.getTables(null, null, null, new String[]{"TABLE"});
	      while(rs.next())
	        tableNames.add(rs.getString(3)); //table name is index #3
	      rs.close();
	    }
	    catch(Exception e) {
	    }
	    return tableNames;
	  }
	  

}
