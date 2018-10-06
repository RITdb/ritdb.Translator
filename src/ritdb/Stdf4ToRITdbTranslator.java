package ritdb;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.security.MessageDigest;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.TimeZone;
import java.util.UUID;

import ritdb.stdf4j.Header;
import ritdb.stdf4j.Record;
import ritdb.stdf4j.RecordData;
import ritdb.stdf4j.RecordVisitor;
import ritdb.stdf4j.STDFReader;
import rtalk.sm.SmCborBuffer;
import rtalk.util.GuruUtilities;
import rtalk.util.RtalkLoggerInterface;

public class Stdf4ToRITdbTranslator implements RecordVisitor {
	public static int _gmtOffsetMin = -480; // offset in minutes to use for gmt
											// time
	private String fileName = null;
	public int recordCnt = 0;
	private long sequence = 0; // holder for sequence override in secs
	private long realSequence = 0; // actual value for seq column gmt seconds *
									// 100000 + fraction
	private int entityID = 1; // local runID is 1 first non run is 2
	private int eventGroup = 0; // set of events from a single touchdown
	private int eventCount = 0; // total events
	private boolean inGroup = false; // true if between pirs and prrs, used to
										// bump eventGrpoup
	private Connection _sqlConnection = null; // database connection
	private Statement _sqlStatement = null; // reusable statement for
											// communicating with the database
	private PreparedStatement _stringInsert = null;
	private String waferIDvalue = null; // value of ID for the current wafer
	private int[] currentTE = new int[1025]; // entity ID per site for current
											// test event, between PIR/PRR
	// now a map from the test number in stdf to the entityID of the test
	private Hashtable<Integer, Integer> testMap = new Hashtable<Integer, Integer>();
	private int testOrder = 0;  // order of the test
	// if test indexing is via the name and not the number then we need a name
	// to entity map
	private Hashtable<String, Integer> testNameMap = new Hashtable<String, Integer>();
	// a map from site number to site info eid
	 private Hashtable<Integer, Integer> siteInfoEid = new Hashtable<Integer, Integer>();
	// and to support the textTxt field changing from ptr to ptr we need to keep
	// the last value per entityID
	private Hashtable<Integer, HashMap<Integer,String>> testTextMap = new Hashtable<Integer, HashMap<Integer,String>>();
	// and a map from test entityID to a some siteFlags if a PTR has been
	// processed
	// site flags keep info on which sites have been processed for test text
	private Hashtable<Integer, HashSet<Integer>> testUpdate = new Hashtable<Integer, HashSet<Integer>>();
	// and a map from test entityID to a true if a TSR has been processed
	private Hashtable<Integer, Boolean> testName = new Hashtable<Integer, Boolean>();
	 // and a map from test entityID to the result_scale
  private Hashtable<Integer, Double> testScaling = new Hashtable<Integer, Double>();
  private Hashtable<Integer, String> testUnits = new Hashtable<Integer, String>();
	// current limit file entityID.
	private int currentLimits = 0;
	private boolean _includeSummaries = false;
	private boolean _testByNumber = true; // if false uses the testTxt field as name else use TSR field
	private boolean _cleanProp = false; // if true removes or modifies proprietary info
	// the unique entity ID for specific entities
	private int runID = 0; // entity ID for the run
	private int waferID = 0; // entity ID for the current wafer
	private int pinlistID = 0; // entity ID for the current pinlist
	private int fileID = 0; // entity ID for the files
	private int prodID = 0; // entity ID for the product info
	private int partID = 0; // entity ID for the part info
	private int substrateID = 0; // entity ID for the substrate info
	private int cellInventoryID = 0; // entity ID for the cell inventory
	private int pinCondID = 0; // entity ID for the Result_cond_info for pins
	private int shmooCondID = 0; // entity ID for the Result_cond_info for shmoo
	private HashMap<Integer, Integer> pmrIndex = new HashMap<Integer, Integer>();
	private int dtrID = 0;
	private int bpsID = 0;
	private int epsID = 0;
	// map frmp hard bin number  to eid
  private Hashtable<String, Integer> hardBinInfoEid = new Hashtable<String, Integer>();
  private HashSet<String> hardBinUpdated = new HashSet<String>();
  // map from soft bin number to eid and if updated
  private Hashtable<String, Integer> softBinInfoEid = new Hashtable<String, Integer>();
  // to prevent dups in ETS testers
  private HashSet<Integer> softBinUpdated = new HashSet<Integer>(); // head* 65536 + site * 256 + binNum
  private HashSet<Long> softBinInfoUpdated = new HashSet<Long>();
	private HashMap<String, String> _guruKeys = null; // all keys
	private RtalkLoggerInterface _logger;
	private STDFReader reader;
	private String _mainTable = "ritdb1";
	 // for continuation records set to eid. PSR, STR, CDR only
	private SmCborBuffer[] _contBuffers = null; // record dep order
	private int    _continuationEid = 0;  // entity EID being continued
	private long    _continuationEid2 = 0;  // second entity EID being continued
	private int    _contTotal = 0; // counter
	private long _indexTimeRef = 0L;
	public boolean _stop = false;
	private File _srcFile;
	private boolean _indexRequired;
	private String _runUUID;
	
	// @Override
	public void afterFile() {
	}

	// @Override
	public void beforeFile() {
	}

	/**
	 * constructor
	 * 
	 */
	public Stdf4ToRITdbTranslator(File file, String runUUID, Connection sqlConnection, HashMap<String,String> flags,
			boolean indexRequired, boolean includeSummary,int gmtTimeMinutes, HashMap<String, String> guruKeys, RtalkLoggerInterface logger)
			throws SQLException, FileNotFoundException, IOException, ParseException {
		fileName = file.getName();
		_srcFile = file;
		_logger = logger;
		_sqlConnection = sqlConnection;
		_gmtOffsetMin = gmtTimeMinutes;
		_guruKeys = guruKeys;
		_includeSummaries = includeSummary;
		_indexRequired = indexRequired;
		_runUUID = runUUID;
		addToMetadata("Obsoleted", "false");
		addToMetadata("ObjClass", "RitdbLog");
		addToMetadata("ObjFormat", "ritdb");
		addToMetadata("ObjFormatVer", "8.0");
    addToMetadata("ritdb.file.RitdbVersion", "ALPHA_P008");
    addToMetadata("ritdb.file.Usecase", "datalog");
		if (flags.containsKey("testByName")) _testByNumber = false;
    if (flags.containsKey("obfuscate")) _cleanProp = true;
    if (flags.containsKey("includesSummaries")) _includeSummaries = true;
	}
	
	public void start() throws SQLException, FileNotFoundException, IOException, ParseException{
		
		_sqlStatement = _sqlConnection.createStatement(); // reusable statement
															// for communicating
															// with the database
		try {
			_sqlStatement.executeUpdate("PRAGMA synchronous = OFF;");
			_sqlStatement.executeUpdate("PRAGMA journal_mode = OFF;");
		} // generates an error in postgres but speeds things up in sqlite by
			// allowing the database to perform ops without verifyng the disk
			// writes went through
		catch (Exception e) {
			// Emit.out("Warning: 'PRAGMA synchronous' not supported. The error
			// was: [" + e + "]");
		}
		createTable(_mainTable);
		_sqlConnection.setAutoCommit(false);
		runID = entityID; // run_info  RUN_INFO
	  fileID = ++entityID; // entity ID for the files  FILE_INFO
	  prodID = ++entityID; // entity ID for the product info PROGRAM_TEST_CONFIGURATION
	  partID = ++entityID; // entity ID for the PART_INFO
    pinCondID = ++entityID; // result_cond_info for pin
    shmooCondID = ++entityID; // result_cond_info for shmoo
		UUID uuid = UUID.randomUUID();
		// create global entities and insert global attributes
		insertObject(sequence, runID, 0, "ENTITY_TYPE", "RUN_INFO");
    insertObject(sequence, runID, 0, "SEQUENCE_REFERENCE", "1990-01-01T00:00:00");
    insertObject(sequence, fileID, 0, "ENTITY_TYPE", "FILE_INFO");
    insertObject(sequence, partID, 0, "ENTITY_TYPE", "PART_INFO");
    insertObject(sequence, prodID, 0, "ENTITY_TYPE", "PROGRAM_TEST_CONFIGURATION");
    
    insertObject(sequence, fileID, 0, "RITDB_GENERATOR", "Stdf4ToRITdbTranslator");
    insertObject(sequence, fileID, 0, "RITDB_GENERATOR_VERSION", "67");
    insertObject(sequence, fileID, 0, "RITDB_VERSION", "ALPHA_P008");
    insertObject(sequence, fileID, 0, "IS_TRANSLATED", "Y");
    insertObject(sequence, runID, 0, "RUN_UUID", _runUUID);
    insertObject(sequence, runID, 0, "RUN_GROUP_UUID", uuid.toString());
    
		insertObject(sequence, fileID, 0, "SOURCE_FILE", nameHash(fileName));
    insertObject(sequence, fileID, 0, "FILE_UUID", UUID.randomUUID().toString());
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss");
    insertObject(sequence, fileID, 0, "SOURCE_FILE_DATE", sdf.format(_srcFile.lastModified()));
    insertObject(sequence, fileID, 0, "SOURCE_FILE_TYPE", "STDFV4");
		addToMetadata("Title", fileName);
		
		// create a result cond entry for pins
    insertObject(sequence, pinCondID, 0, "ENTITY_TYPE", "RESULT_COND_INFO");
    insertObject(sequence, pinCondID, 0, "CONDITION_RESOURCE", "DEVICE");
    insertObject(sequence, pinCondID, 0, "CONDITION_DATA_TYPE", "EID");
    insertObject(sequence, pinCondID, 0, "CONDITION_NAME", "PIN");
    insertObject(sequence, pinCondID, 0, "CONDITION_ID", "PIN"); //must be unique across entities
    insertObject(sequence, pinCondID, 0, "CONDITION_LABEL", "PIN");
    insertObject(sequence, pinCondID, 0, "CONDITION_DESC", "PIN");
    
    // create a result cond entry for shmoo
    insertObject(sequence, shmooCondID, 0, "ENTITY_TYPE", "RESULT_COND_INFO");
    insertObject(sequence, shmooCondID, 0, "CONDITION_RESOURCE", "SHMOO");
    insertObject(sequence, shmooCondID, 0, "CONDITION_DATA_TYPE", "FLOAT");
    insertObject(sequence, shmooCondID, 0, "CONDITION_NAME", "SHMOO");
    insertObject(sequence, shmooCondID, 0, "CONDITION_ID", "SHMOO");
    insertObject(sequence, shmooCondID, 0, "CONDITION_LABEL", "SHMOO");
    insertObject(sequence, shmooCondID, 0, "CONDITION_DESC", "SHMOO");
    
		reader = new STDFReader(_srcFile, _logger); // note: accepts File,
												// InputStream or filename
		reader.parse(this); // as it parses, the reader calls handleRecord
							          // (below) for each entry
		_sqlConnection.commit(); // commit all those changes
		_sqlConnection.setAutoCommit(true);

		try {
		  _stringInsert.executeBatch();
			_sqlStatement.executeUpdate("PRAGMA synchronous = ON;");
		} // restore setting allowing the database to verify writes to the file
			// system
		catch (Exception e) {
		}
		if(_indexRequired){
		  _logger.log("start indexing");
      try {
        _sqlStatement.executeUpdate("create index if not exists val on "+_mainTable+" (entityID DESC, name DESC);");
        _sqlStatement.executeUpdate("create index if not exists entity on "+_mainTable+" (name DESC, value DESC);");
        _sqlStatement.execute("analyze");
      } // restore setting allowing the database to verify writes to the file
        // system
      catch (Exception e) {
      }
    }
    _logger.log("start vacuum");
		try {
			_sqlStatement.executeUpdate("VACUUM");
			_sqlStatement.close();
		} // restore setting allowing the database to verify writes to the file
			// system
		catch (Exception e) {
		}
    _logger.log("ritdb closed");
    _guruKeys.put("databaseRecordCount", Long.toString(recordCnt));
	}
	
	public void stopConvert(){
	  _stop = true;
	}

	/**
	 * Create the single table table is sequence int,entity int,index int, name
	 * string, value string | int | float index is nullable, sequence is unique
	 */
	private void createTable(String tName) {
		// Create database table if needed:
		String tableName = tName;
		try {
			_sqlStatement.executeUpdate("create table if not exists " + tableName + " ("
					+ "sequence INTEGER PRIMARY KEY," + "entityID INTEGER," + "indexID INTEGER," + "name TEXT," +
					// "value TEXT,"+ //for postgres
					"value NONE," + "value2 TEXT);");
		} catch (SQLException e) {
			e.printStackTrace();
		}
		// now create the necessary prepared statements for each type
		// create a prepared sql statement that has the necessary fields for
		// this stdf record type
		try {
			_stringInsert = _sqlConnection.prepareStatement("insert into " + tableName + " values (?,?,?,?,?,?);");
		} catch (SQLException e) {
			e.printStackTrace();
		} // prepared statement: "insert into table..."
	}

	private void dropDataTable() {
		// drops the data
		try {
			Statement sqlStatement = _sqlConnection.createStatement();
			DatabaseMetaData dbmd = _sqlConnection.getMetaData();
			ResultSet rs = dbmd.getTables(_sqlConnection.getCatalog(), null, null, new String[] { "TABLE" });
			ArrayList<String> list = new ArrayList<String>();
			while (rs.next())
				list.add(rs.getString(3)); // table name is index #3
			rs.close();
			Iterator<String> iter = list.iterator();
			while (iter.hasNext()) {
				String tablename = iter.next().toString();
				sqlStatement.executeUpdate("drop table " + tablename);
				_logger.log("Dropped table " + tablename);
			}
			sqlStatement.executeUpdate("VACUUM");
		} catch (Exception e) {
			System.out.println("Error dropping tables: " + e);
		}
	}

	/**
	 * two possible insert types, no updates only inserts
	 * returns true if an insert occurred
	 * 
	 */
	private boolean insertObject(long seq, long eid, long index, String name, Object val) {
		// Get or create the prepared SQL statement:
		// Populate the data and send it to the database:
		// object can be string, long, double
		if (val == null) {
			return false;
		}
		// check if empty string and don't insert it
		if (val.getClass() == String.class) {
			String tString = (String) val;
			if (tString.trim().isEmpty()) {
				return false;
			}
		}
		++realSequence;
		PreparedStatement prep = _stringInsert;
		try {
			prep.setLong(1, realSequence);
			prep.setLong(2, eid);
			prep.setLong(3, index);
			prep.setString(4, name);
			prep.setNull(6, java.sql.Types.CHAR);

			/* For sqlite: */
			Class clazz = val.getClass();
			if (clazz == String.class)
				prep.setString(5, (String) val);
			else if (clazz == Long.class)
				prep.setLong(5, (Long) val);
			else if (clazz == Integer.class)
				prep.setInt(5, (Integer) val);
			else if (clazz == Double.class)
				prep.setDouble(5, (Double) val);
			else if (clazz == Float.class)
				prep.setFloat(5, (Float) val);
			else if (val instanceof byte[])
				prep.setBytes(5, (byte[]) val);
			/*
			 * For postgres:* / prep.setString(5, val==null ? null :
			 * val.toString()); prep.setString(6, null); /*
			 */
			prep.addBatch();
			//prep.executeBatch();
		} catch (Exception e) {
			String emsg = "Error in " + getClass().getName() + ".insertObject(): " + e;
			System.out.println(emsg);
			e.printStackTrace();
		}
		return true;
	}
	
	

	 /**
   * two possible insert types, no updates only inserts
   * returns true if an insert occurred
   * 
   */
	private boolean insertObject(long seq, long eid, long index, String name, Object val, String val2) {
		// Get or create the prepared SQL statement:
		// Populate the data and send it to the database:
		// object can be string, long, double
		PreparedStatement prep = _stringInsert;
		// sequence in seconds
		++realSequence;
		try {
			prep.setLong(1, realSequence);
			prep.setLong(2, eid);
			prep.setLong(3, index);
			prep.setString(4, name);
			prep.setString(6, val2);

			/* For sqlite: */
			if (val != null) {
				Class clazz = val.getClass();
				if (clazz == String.class)
					prep.setString(5, (String) val);
				else if (clazz == Long.class)
					prep.setLong(5, (Long) val);
				else if (clazz == Integer.class)
					prep.setInt(5, (Integer) val);
				else if (clazz == Double.class)
					prep.setDouble(5, (Double) val);
				else if (clazz == Float.class)
					prep.setFloat(5, (Float) val);
				// if(clazz == byte[]) prep.setBytes(5, (byte[])val);}
			}else{
			  prep.setNull(5, java.sql.Types.CHAR);
			  System.out.println("null value set for eid " +eid);
			}
			/*
			 * For postgres * / prep.setString(5, val==null ? null :
			 * val.toString()); /*
			 */

			prep.addBatch();
			//prep.executeBatch();
		} catch (Exception e) {
			String emsg = "Error in " + getClass().getName() + ".insertObject(): " + e;
			System.out.println(emsg);
			e.printStackTrace();
		}
		return true;
	}
	
	private String scaleCharFromInt(int val){
	  if(val == 2) return "%";
	  if(val == -3) return "K";
	  if(val == -6) return "M";
	  if(val == -9) return "G";
	  if(val == -12) return "T";
	  if(val == 3) return "m";
	  if(val == 6) return "u";
	  if(val == 9) return "n";
	  if(val == 12) return "p";
	  if(val == 15) return "f";
	  return " ";
	}

	private int getTestEntityFor(int testNumber, String testText) {
		// depending on mode this handles the various uses of testTest/testName
		//  if _testByNumber is true then we use this to see if the testText
		// has changed
		// since the last PTR, if it has then we save it again as part of the
		// result
		// if _testByNumber is false then we use testText as the unique test
		// identifier
		// and use it to look up the entity ID
		int testEntityId;
		if (_testByNumber == true) {
			if (testMap.containsKey(testNumber)) {
				testEntityId = testMap.get(testNumber);
			} else {
				entityID++;
				testMap.put(testNumber, entityID);
				testScaling.put(entityID, 1.0D);
        testUnits.put(entityID, " ");
				insertObject(sequence, entityID, 0, "ENTITY_TYPE", "RESULT_INFO");
				insertObject(sequence, entityID, 0, "RESULT_NUMBER", testNumber); 
				// put testNumber as result_number and result_id
				insertObject(sequence, entityID, 0, "RESULT_ID", testNumber);
				// add test_order for use by viewers
				insertObject(sequence, entityID, 0, "TEST_ORDER", ++testOrder); 
				testEntityId = entityID;
			}
			return testEntityId;
		} else {
			if (testNameMap.containsKey(testText)) {
				return testNameMap.get(testText);
			} else {
				entityID++;
				testNameMap.put(testText, entityID);
        testScaling.put(entityID, 1.0D); // default scaling
        testUnits.put(entityID, " ");
				insertObject(sequence, entityID, 0, "ENTITY_TYPE", "RESULT_INFO");
				insertObject(sequence, entityID, 0, "RESULT_NUMBER", testNumber); 
				insertObject(sequence, entityID, 0, "RESULT_NAME", nameHash(testText)); 
				insertObject(sequence, entityID, 0, "RESULT_ID", nameHash(testText)); 
				insertObject(sequence, entityID, 0, "TEST_ORDER", ++testOrder);
				return entityID;
			}
		}
	}

	private void updateTextText(int testEntity, int site, String testText) {
		// now update the testText
		if (_testByNumber == false)
			return; // no test text if used for unique ID
		if (testText == null)
			return;
		if (site < 0)
			return; // could be TSR so skip only for PTR,MPR and FTR
		// first update the text if this is the first time through
		if (testUpdate.containsKey(testEntity)) {
			if (testUpdate.get(testEntity).isEmpty()) testTextMap.put(testEntity, new HashMap<Integer,String>()); 
			if (!testUpdate.get(testEntity).contains(site)) { 
			    // check to see if there is text
				insertObject(sequence, testEntity, siteInfoEid.get(site), "RESULT_SITE_TEXT", testText);
				testUpdate.get(testEntity).add(site);
				(testTextMap.get(testEntity)).put(site, testText); 
				// per site test text
			}
		}
		if (!testText.isEmpty()) {// handle changing text
			if (!((testTextMap.get(testEntity)).get(site)).equalsIgnoreCase(testText)) {
				int te = currentTE[site]; // per site test event
				insertObject(sequence, te, testEntity, "RESULT_SITE_TEXT", testText);
			}
		}
	}

	private String convertUnixTimeStamp(long timeSecs) {
		// for stdf the timeSecs is the local offset from 1/1/1970
		if (timeSecs == 0) {
			return null;
		}
		// create a calendar object and set the time
		SimpleDateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss");
		df.setTimeZone(TimeZone.getTimeZone("UTC"));
		Calendar cal = Calendar.getInstance(TimeZone.getTimeZone("UTC"));
		cal.setTimeInMillis(timeSecs * 1000);
		return df.format(cal.getTime());
	}

	private String convertUnixTimeStampGMT(long timeSecs) {
		if (timeSecs == 0) {
			return null;
		}
		if (timeSecs * 1000000L > realSequence) {
			realSequence = timeSecs * 1000000L;
		}
		// create a calendar object and set the time
		Calendar cal = Calendar.getInstance(TimeZone.getTimeZone("UTC"));
		cal.setTimeInMillis(((_gmtOffsetMin * 60) + timeSecs) * 1000);
		SimpleDateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss");
		df.setTimeZone(TimeZone.getTimeZone("UTC"));
		return df.format(cal.getTime());
	}

	private void addToMetadata(String name, Object value) {
		if (value != null)
			_guruKeys.put(name, value.toString());
		// code for
		// if(_metadataDef.containsKey(name))
		// _guruKeys.put(_metadataDef.get(name), value);
	}

	public void handleUnknownRecord(Header header, byte[] bytes) {
		_logger.log("WARNING: Skipping unknown record type: " + header.getType() + ", " + header.getSubType() + " size "
				+ header.getLength());
		try {
			_sqlConnection.commit();
		} catch (SQLException e) {
			e.printStackTrace();
		} // commit all those changes up to here
	}

	// @Override
	public void handleRecord(Record record) {
		try {
			++recordCnt; // keep track of how many STDF records are processed
			if ((recordCnt % 10000) == 0) {
			  try {
          _stringInsert.executeBatch();
        }
        catch (SQLException e) {
          e.printStackTrace();
        }
				_logger.log("record processed " + recordCnt);
				if(_stop){
				  try {
            _sqlConnection.commit();
          }
          catch (SQLException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
				  throw new RuntimeException("stopping");
				}
			}
			RecordData recordData = record.getData(); // throws ParseException
			String recordType = recordData.getType(); // type of record (Mir,
														// Ptr etc.)
			HashMap<String, Object> fields = recordData.getFields();
			// System.out.println("parsing "+ recordType);
			if (recordType.equals("Mir")) {
				this.insertMir(fields);
			}
			if (recordType.equals("Far")) {
				this.insertFar(fields);
			}
			if (recordType.equals("Mrr")) {
				this.insertMrr(fields);
			}
			if (recordType.equals("Tsr")) {
				this.insertTsr(fields);
			}
			if (recordType.equals("Pir")) {
				this.insertPir(fields);
			}
			if (recordType.equals("Prr")) {
				this.insertPrr(fields);
			}
			if (recordType.equals("Ptr")) {
				this.insertPtr(fields);
			}
			if (recordType.equals("Pcr")) {
				this.insertPcr(fields);
			}
			if (recordType.equals("Hbr")) {
				this.insertHbr(fields);
			}
			if (recordType.equals("Sbr")) {
				this.insertSbr(fields);
			}
			if (recordType.equals("Sdr")) {
				this.insertSdr(fields);
			}
			if (recordType.equals("Dtr")) {
				this.insertDtr(fields);
			}
			if (recordType.equals("Rdr")) {
				this.insertRdr(fields);
			}
			if (recordType.equals("Wir")) {
				this.insertWir(fields);
			}
			if (recordType.equals("Wcr")) {
				this.insertWcr(fields);
			}
			if (recordType.equals("Wrr")) {
				this.insertWrr(fields);
			}
			if (recordType.equals("Pgr")) {
				this.insertPgr(fields);
			}
			if (recordType.equals("Pmr")) {
				this.insertPmr(fields);
			}
			if (recordType.equals("Ftr")) {
				this.insertFtr(fields);
			}
			if (recordType.equals("Plr")) {
				this.insertPlr(fields);
			}
			if (recordType.equals("Mpr")) {
				this.insertMpr(fields);
			}
			if (recordType.equals("Gdr")) {
				this.insertGdr(fields);
			}
			if (recordType.equals("Bps")) {
				this.insertBps(fields);
			}
			if (recordType.equals("Eps")) {
				this.insertEps(fields);
			}
			if (recordType.equals("Atr")) {
				this.insertAtr(fields);
			}
			if (recordType.equals("Vur")) {
				this.insertVur(fields);
			}
			if (recordType.equals("Psr")) {
				this.insertPsr(fields);
			}
			if (recordType.equals("Nmr")) {
				this.insertNmr(fields);
			}
			if (recordType.equals("Cnr")) {
				this.insertCnr(fields);
			}
			if (recordType.equals("Ssr")) {
				this.insertSsr(fields);
			}
			if (recordType.equals("Cdr")) {
				this.insertCdr(fields);
			}
			if (recordType.equals("Str")) {
				this.insertStr(fields);
			}
		} catch (ParseException e) {
			String emsg = "Error in " + getClass().getName() + ".handleRecord(): " + e;
			_logger.log(emsg);
			System.out.print(emsg);
			// System.exit(1); //debug

		}
	}

	private void insertFar(HashMap<String, Object> fields) {
		// insertObject(sequence, runID, 0, "CPU_TYPE", fields.get("CPU_TYPE"));
		// insertObject(sequence, runID, 0, "FILE_STDF_VER",
		// fields.get("STDF_VER"));

	}

	/**
	 * Handles MIR Record mapping
	 * 
	 */
	private void insertMir(HashMap<String, Object> fields) {
	  // start time
		long starttime = (Long) fields.get("START_T");
		if (starttime != 0) {
			insertObject(starttime, runID, 0, "RUN_START_DTTM_UTC", convertUnixTimeStampGMT(starttime));
			addToMetadata("ri.test.RUN_START_DTTM_UTC", convertUnixTimeStampGMT(starttime).toString());
			insertObject(starttime, runID, 0, "RUN_START_DTTM", convertUnixTimeStamp(starttime));
			addToMetadata("CreationDate", convertUnixTimeStamp(starttime).toString());
			addToMetadata("ri.test.RUN_START_DTTM", convertUnixTimeStamp(starttime).toString());
		}
		// run
    insertObject(sequence, runID, 0, "RITDB_SOURCE_ID", nameHash(fields.get("NODE_NAM")));
    insertObject(sequence, runID, 0, "STATION_NUMBER", fields.get("STAT_NUM"));
    insertObject(sequence, runID, 0, "CELL_ID", nameHash(fields.get("NODE_NAM")));
    insertObject(sequence, runID, 0, "CELL_NAME", nameHash(fields.get("NODE_NAM")));
    insertObject(sequence, runID, 0, "TEST_FACILITY_ID", nameHash(fields.get("FACIL_ID")));
    addToMetadata("ri.test.TEST_FACILITY_ID", nameHash(fields.get("FACIL_ID")));
    insertObject(sequence, runID, 0, "TEST_FLOOR_ID", nameHash(fields.get("FLOOR_ID")));
    insertObject(sequence, runID, 0, "LOT_ID", nameHash(fields.get("LOT_ID")));
    addToMetadata("ri.test.LOT_ID", nameHash(fields.get("LOT_ID")));
    insertObject(sequence, runID, 0, "STEP_NAME", fields.get("SBLOT_ID"));
    addToMetadata("ri.test.STEP_NAME", fields.get("SBLOT_ID"));
    insertObject(sequence, runID, 0, "PRODUCT_ID", nameHash(fields.get("PART_TYP")));
    insertObject(sequence, partID, 0, "PRODUCT_ID", nameHash(fields.get("PART_TYP")));
    insertObject(sequence, partID, 0, "PART_TYPE", nameHash(fields.get("PART_TYP")));
    addToMetadata("ri.test.PRODUCT_ID", nameHash(fields.get("PART_TYP")));

    insertObject(sequence, runID, 0, "JOB_NAME", nameHash(fields.get("JOB_NAM")));
    addToMetadata("ri.test.JOB_NAME", nameHash(fields.get("JOB_NAM")));
    insertObject(sequence, runID, 0, "JOB_VERSION", fields.get("JOB_REV"));
    insertObject(sequence, runID, 0, "FLOW_ID", fields.get("FLOW_ID"));
    insertObject(sequence, runID, 0, "ENGINEERING_LOT_ID", fields.get("ENG_ID"));
    insertObject(sequence, runID, 0, "TEST_PASS_NAME", fields.get("TEST_COD"));
    insertObject(sequence, runID, 0, "RETEST_CODE", fields.get("RTST_COD"));
    insertObject(sequence, runID, 3, "COMMENT", nameHash(fields.get("USER_TXT")));
    // cell inventory
    entityID++;
    cellInventoryID = entityID;
    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "CELL");
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("TSTR_TYP"));
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", nameHash(fields.get("NODE_NAM")));
    // tester inventory
    entityID++;
    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "TESTER");
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("TSTR_TYP"));
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_SERIAL_ID", fields.get("SERL_NUM")); 
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_MODE_CODE", fields.get("MODE_COD"));
    insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", nameHash(fields.get("NODE_NAM")));
    insertObject(sequence, entityID, 1, "CELL_SW_CLASS", "TESTER_EXEC");
    insertObject(sequence, entityID, 1, "CELL_SW_TYPE", fields.get("EXEC_TYP"));
    insertObject(sequence, entityID, 1, "CELL_SW_VER", fields.get("EXEC_VER"));

    addToMetadata("ri.test.TESTER_ID", fields.get("NODE_NAM"));

    //insertObject(sequence, equipID, 0, "TESTER_CMD_CODE", fields.get("CMOD_COD"));
    // product and job
    insertObject(sequence, prodID, 0, "PACKAGE_TYPE", fields.get("PKG_TYP"));
    insertObject(sequence, prodID, 0, "PRODUCT_ID", nameHash(fields.get("PART_TYP")));
    insertObject(sequence, prodID, 0, "FAB_PROCESS_ID", fields.get("PROC_ID"));
    insertObject(sequence, prodID, 0, "PRODUCT_FAMILY_ID", nameHash(fields.get("FAMLY_ID")));
    insertObject(sequence, prodID, 0, "TEST_SETUP", fields.get("SETUP_ID"));
    long time = (Long) fields.get("SETUP_T");
    if (time != 0) {
      insertObject(time, prodID, 0, "JOB_SETUP_DTTM_UTC", convertUnixTimeStampGMT(time));
      insertObject(time, prodID, 0, "JOB_SETUP_DTTM", convertUnixTimeStamp(time));
      insertObject(time, prodID, 0, "PGM_LOAD_MARKER", nameHash(fields.get("NODE_NAM")) + convertUnixTimeStamp(time));
      insertObject(time, prodID, 0, "LOT_START_MARKER", nameHash(fields.get("NODE_NAM")) + convertUnixTimeStamp(time));
    }else{
      insertObject(time, prodID, 0, "PGM_LOAD_MARKER", nameHash(fields.get("NODE_NAM")) + convertUnixTimeStamp(starttime));
      insertObject(time, prodID, 0, "LOT_START_MARKER", nameHash(fields.get("NODE_NAM")) + convertUnixTimeStamp(starttime));
    }
    insertObject(sequence, prodID, 0, "TEST_SPECIFICATION_NAME", nameHash(fields.get("SPEC_NAM"))); 
    insertObject(sequence, prodID, 0, "TEST_SPECIFICATION_VERSION", fields.get("SPEC_VER"));
    insertObject(sequence, prodID, 0, "TEST_TEMPERATURE", fields.get("TST_TEMP"));
    insertObject(sequence, prodID, 0, "AUXILIARY_FILE", fields.get("AUX_FILE"));
		insertObject(sequence, prodID, 0, "DESIGN_REV", fields.get("DSGN_REV"));
		insertObject(sequence, prodID, 0, "ROM_CODE", fields.get("ROM_COD"));
    insertObject(sequence, prodID, 0, "DATA_PROTECTION_CODE", fields.get("PROT_COD"));
    insertObject(sequence, prodID, 0, "DATE_CODE", fields.get("DATE_COD"));
    // misc
    //insertObject(sequence, runID, 0, "OPERATOR_ID", fields.get("OPER_NAM"));
    long tmp = (Long) fields.get("BURN_TIM");
    if (tmp != 65535L) {
      insertObject(sequence, runID, 0, "BURNIN_TIME", fields.get("BURN_TIM"));
    }
    // set up limits entity
    entityID++;
    currentLimits = entityID;
    insertObject(sequence, currentLimits, 0, "ENTITY_TYPE", "RESULT_LIMIT_SET");
    insertObject(sequence, currentLimits, 0, "LIMIT_SET_NAME", nameHash(fields.get("SPEC_NAM"))); 
    insertObject(sequence, currentLimits, 0, "LIMIT_SET_TYPE", "PROD");
    // create the worksheet script
    entityID++;
    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "SCRIPT");
    insertObject(sequence, entityID, 0, "NAME", "worksheet");
    insertObject(sequence, entityID, 0, "DESCRIPTION", "default view");
    insertObject(sequence, entityID, 0, "SCRIPT", generateScript((String) fields.get("SPEC_NAM")) );
    // default csv export
    entityID++;
    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "SCRIPT");
    insertObject(sequence, entityID, 0, "NAME", "csv");
    insertObject(sequence, entityID, 0, "DESCRIPTION", "default csv view");
    insertObject(sequence, entityID, 0, "SCRIPT", generateCsvScript((String) fields.get("SPEC_NAM")) );
	}

	/**
	 * Handles MRR Record mapping
	 * 
	 */
	private void insertMrr(HashMap<String, Object> fields) {
		long time = (Long) fields.get("FINISH_T");
		if (time != 0L) {
			insertObject(time, runID, 0, "RUN_END_DTTM", convertUnixTimeStamp(time));
			addToMetadata("ri.test.RUN_END_DTTM_UTC", convertUnixTimeStampGMT(time).toString());
			insertObject(time, runID, 0, "RUN_END_DTTM_UTC", convertUnixTimeStampGMT(time));
			addToMetadata("ri.test.RUN_END_DTTM", convertUnixTimeStampGMT(time).toString());
		}
		insertObject(sequence, runID, 0, "LOT_DISPOSITION_CODE", fields.get("DISP_COD"));
		insertObject(sequence, runID, 1, "COMMENT", fields.get("USR_DESC"));
		insertObject(sequence, runID, 2, "COMMENT", fields.get("EXC_DESC"));
	}
	
	/**
	 * handles the WIR
	 * @param fields
	 */
	 private void insertWir(HashMap<String, Object> fields) {
	    if (waferID == 0) {
	      entityID++; // get the next entity ID
	      waferID = entityID;
	      insertObject(sequence, waferID, 0, "ENTITY_TYPE", "SUBSTRATE_EVENT");
	      insertObject(sequence, runID, 0, "USECASE", "datalog.wafer");
	       insertObject(sequence, waferID, 0, "SUBSTRATE_INFO_EID", substrateID);
	    }
	    eventGroup = 0;
	    waferIDvalue = (String) fields.get("SUBSTRATE_ID"); // insert at WRR

	    Long time = (Long) fields.get("START_T");
	    insertObject(time, waferID, 0, "SUBSTRATE_START_DTTM", convertUnixTimeStamp(time));
	    insertObject(time, waferID, 0, "SUBSTRATE_START_DTTM_UTC", convertUnixTimeStampGMT(time));
	  }

	/**
	 * Handles WRR Record mapping
	 * 
	 */
	private void insertWrr(HashMap<String, Object> fields) {
		long time = (Long) fields.get("FINISH_T");
		insertObject(time, waferID, 0, "SUBSTRATE_STOP_DTTM", convertUnixTimeStamp(time));
		insertObject(time, waferID, 0, "SUBSTRATE_STOP_DTTM_UTC", convertUnixTimeStampGMT(time));
    insertObject(time, waferID, 0, "SUBSTRATE_STATUS", "finished");
		insertObject(sequence, waferID, 0, "CARRIER_ID", fields.get("FRAME_ID"));
		if (fields.get("WAFER_ID") != null)
			waferIDvalue = (String) fields.get("WAFER_ID");
		insertObject(sequence, waferID, 0, "SUBSTRATE_ID", nameHash(waferIDvalue));
		insertObject(sequence, waferID, 0, "WAFER_MASK_ID", fields.get("MASK_ID"));
		insertObject(sequence, waferID, 0, "SUBSTRATE_USER_DESC", nameHash(fields.get("USR_DESC")));
		insertObject(sequence, waferID, 0, "SUBSTRATE_EXEC_DESC", nameHash(fields.get("EXC_DESC")));
		
		// now add the WAFER_SUMMARY stuff
		if(_includeSummaries){
      entityID++;
      insertObject(sequence, entityID, 0, "ENTITY_TYPE", "EVENT");
      insertObject(sequence, entityID, 0, "EVENT_TYPE", "WAFER_SUMMARY");
      insertObject(sequence, entityID, 0, "SUBSTRATE_ID", nameHash(waferIDvalue));
      insertObject(sequence, entityID, 0, "SUBSTRATE_INFO_EID", substrateID);
  		insertObject(sequence, entityID, 0, "TOUCHDOWN_COUNT", eventGroup);
  		Long tmp = (Long) fields.get("PART_CNT");
  		if (tmp != null)
  			if (tmp != 4294967295L)
  				insertObject(sequence, entityID, 0, "PART_COUNT", fields.get("PART_CNT"));
  		tmp = (Long) fields.get("RTST_CNT");
  		if (tmp != null)
  			if (tmp != 4294967295L)
  				insertObject(sequence, entityID, 0, "RETEST_PART_COUNT", fields.get("RTST_CNT"));
  		tmp = (Long) fields.get("ABRT_CNT");
  		if (tmp != null)
  			if (tmp != 4294967295L)
  				insertObject(sequence, entityID, 0, "ABORT_PART_COUNT", fields.get("ABRT_CNT"));
  		tmp = (Long) fields.get("GOOD_CNT");
  		if (tmp != null)
  			if (tmp != 4294967295L)
  				insertObject(sequence, entityID, 0, "GOOD_PART_COUNT", fields.get("GOOD_CNT"));
  		tmp = (Long) fields.get("FUNC_CNT");
  		// if( tmp != null) if( tmp != 4294967295L)insertObject(sequence,
  		// entityID, 0, "FUNCTIONAL_PART_COUNT", fields.get("FUNC_CNT"));
		}
		waferID = 0; // reset for next wafer
	}

	/**
	 * Handles WCR Record mapping
	 * 
	 */
	private void insertWcr(HashMap<String, Object> fields) {
		entityID++;
		substrateID = entityID;
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "SUBSTRATE_INFO");  
    insertObject(sequence, entityID, 0, "SUBSTRATE_INFO_ID", "1");
    insertObject(sequence, entityID, 0, "SUBSTRATE_TYPE", "wafer");
    insertObject(sequence, entityID, 0, "SUBSTRATE_SIDE", "TopSide");
    insertObject(sequence, entityID, 0, "ORIGIN_LOCATION", "center");
		insertObject(sequence, entityID, 0, "WAFER_SIZE", fields.get("WAFR_SIZ"));
    insertObject(sequence, partID, 0, "WAFER_SIZE", fields.get("WAFR_SIZ"));
		insertObject(sequence, partID, 0, "PART_SIZE_Y", fields.get("DIE_HT"));
		insertObject(sequence, partID, 0, "PART_SIZE_X", fields.get("DIE_WID"));
		Long units = (Long) fields.get("WF_UNITS");
		if (units.equals(0L)){
			insertObject(sequence, entityID, 0, "SUBSTRATE_UNITS", "NONE");
      insertObject(sequence, partID, 0, "PART_UNITS", "NONE");
		}
		if (units.equals(1L)){
			insertObject(sequence, entityID, 0, "SUBSTRATE_UNITS", "in");
      insertObject(sequence, partID, 0, "PART_UNITS", "in");
		}
		if (units.equals(2L)){
			insertObject(sequence, entityID, 0, "SUBSTRATE_UNITS", "cm");
      insertObject(sequence, partID, 0, "PART_UNITS", "cm");
		}
		if (units.equals(3L)){
			insertObject(sequence, entityID, 0, "SUBSTRATE_UNITS", "mm");
      insertObject(sequence, partID, 0, "PART_UNITS", "mm");
		}
		if (units.equals(4L)){
			insertObject(sequence, entityID, 0, "SUBSTRATE_UNITS", "mil");
      insertObject(sequence, partID, 0, "PART_UNITS", "mil");
		}
		String flat = (String)fields.get("WF_FLAT");
		if(flat.equalsIgnoreCase("Down")){
      insertObject(sequence, entityID, 0, "SUBSTRATE_ORIENTATION", 0);		  
		}
    if(flat.equalsIgnoreCase("Up")){
      insertObject(sequence, entityID, 0, "SUBSTRATE_ORIENTATION", 180);     
    }
    if(flat.equalsIgnoreCase("Right")){
      insertObject(sequence, entityID, 0, "SUBSTRATE_ORIENTATION", 270);     
    }
    if(flat.equalsIgnoreCase("Left")){
      insertObject(sequence, entityID, 0, "SUBSTRATE_ORIENTATION", 90);     
    }
		insertObject(sequence, entityID, 0, "REFERENCE_DEVICE_X", fields.get("CENTER_X"));
		insertObject(sequence, entityID, 0, "REFERENCE_DEVICE_Y", fields.get("CENTER_Y"));
		String posX = (String) fields.get("POS_X"); // L R space
    String posY = (String) fields.get("POS_Y");  // U D space
    if( posX != null && posY != null && posX.equals("L") && posY.equals("U")){
      insertObject(sequence, entityID, 0, "AXIS_DIRECTION", "UpLeft");      
    }
    if( posX != null && posY != null && posX.equals("L") && posY.equals("D")){
      insertObject(sequence, entityID, 0, "AXIS_DIRECTION", "DownLeft");      
    }
    if( posX != null && posY != null && posX.equals("R") && posY.equals("U")){
      insertObject(sequence, entityID, 0, "AXIS_DIRECTION", "UpRight");      
    }
    if( posX != null && posY != null && posX.equals("R") && posY.equals("D")){
      insertObject(sequence, entityID, 0, "AXIS_DIRECTION", "DownRight");      
    }
	}

	// now lets go for the test synopsis record
	private void insertTsr(HashMap<String, Object> fields) {
		// first get the test number as this is the reference
		Integer tmp = ((Long) fields.get("TEST_NUM")).intValue();
		Integer testNumber = getTestEntityFor(tmp, (String) fields.get("TEST_NAM"));
    String tName = ((String) fields.get("TEST_NAM"));
    if (_testByNumber && !testName.containsKey(testNumber)) {
      insertObject(sequence, testNumber, 0, "RESULT_NAME", nameHash(tName));
      testName.put(testNumber, true);
    }
    insertObject(sequence, testNumber, 0, "TEST_SEQUENCER_NAME", fields.get("SEQ_NAME"));
    if(_includeSummaries){
  		entityID++; // get the next entity ID and do the test synopsis
      insertObject(sequence, entityID, 0, "ENTITY_TYPE", "EVENT");
  		insertObject(sequence, entityID, 0, "EVENT_TYPE", "RESULT_SUMMARY");
  		insertObject(sequence, entityID, 0, "RESULT_INFO_EID", testNumber);
  		int head = ((Long) fields.get("HEAD_NUM")).intValue();
  		if (head == 255) {
  			insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "TOTAL");
  		} else {
  			int site = ((Long) fields.get("SITE_NUM")).intValue();
  	    insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(getSite(head,((Long)fields.get("SITE_NUM")).intValue())));
  			insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "SITE");
  		}
  		int opt;
  		if (fields.get("OPT_FLAG") == null) {
  			opt = 0;
  		} else {
  			opt = ((Byte) fields.get("OPT_FLAG")) & 0x37;
  		}
  		// insertObject(sequence, entityID, 0, "OPT_FLAG", opt);
  		Iterator<String> iterFieldNames = fields.keySet().iterator();
  		insertObject(sequence, entityID, 0, "RESULT_NAME", nameHash(tName));
  		while (iterFieldNames.hasNext()) {
  			String newName = null;
  			Object fieldValue = null;
  			String fieldName = (String) iterFieldNames.next();
  			fieldValue = fields.get(fieldName); // set to null to drop
  			// start the name mapping section
  			if (fieldName.equals("TEST_MAX")) {
  				if (((opt & 0x02) == 0)) {
  					newName = "MAXIMUM_TEST_VALUE";
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("TEST_MIN")) {
  				if (((opt & 0x01) == 0)) {
  					newName = "MINIMUM_TEST_VALUE";
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("FAIL_CNT")) {
  				newName = "TEST_FAIL_COUNT";
  				if (((Number) fieldValue).longValue() != 4294967295L)
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  			} else if (fieldName.equals("ALRM_CNT")) {
  				newName = "TEST_ALARM_COUNT";
  				if (((Number) fieldValue).longValue() != 4294967295L) {
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("EXEC_CNT")) {
  				newName = "TEST_EXECUTION_COUNT";
  				if (((Number) fieldValue).longValue() != 4294967295L)
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  			} else if (fieldName.equals("TST_SUMS")) {
  				if (((opt & 0x10) == 0)) {
  					newName = "SUM_TEST_VALUES";
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("TST_SQRS")) {
  				if (((opt & 0x20) == 0)) {
  					newName = "SUMOFSQUARES_TEST_VALUES";
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("TEST_TIM")) {
  				newName = "AVERAGE_TEST_TIME";
  				if (((opt & 0x04) == 0)) {
  					insertObject(sequence, entityID, 0, newName, fieldValue);
  				}
  			} else if (fieldName.equals("TEST_NUM")) {
  				newName = "TEST_ID";
  				insertObject(sequence, entityID, 0, newName, fieldValue);
  			} else if (fieldName.equals("SEQ_NAME")) {
  				newName = "TEST_SEQUENCER_NAME";
  				insertObject(sequence, entityID, 0, newName, fieldValue);
  			} else if (fieldName.equals("TEST_LBL")) {
  				newName = "RESULT_LABEL";
  				insertObject(sequence, entityID, 0, newName, fieldValue);
  			} else if (fieldName.equals("TEST_TYP")) {
  				newName = "TEST_TYPE";
  				insertObject(sequence, entityID, 0, newName, fieldValue);
  			}
  		}
    }
	}

	/**
	 * start a part
	 * @param fields
	 */
	private void insertPir(HashMap<String, Object> fields) {
		int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
		    ((Long) fields.get("SITE_NUM")).intValue()  );
		entityID++;// start a new testEvent
		currentTE[site] = entityID;
		if(eventGroup == 0 && waferID == 0){
	    insertObject(sequence, runID, 0, "USECASE", "datalog.unit");
		}
		if (!inGroup) {
			inGroup = true;
			eventGroup++;
			dtrID = entityID;
		}
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "PART_RESULT_EVENT");
		insertObject(sequence, entityID, 0, "PART_RESULT_EVENT_GROUP", eventGroup);
    insertObject(sequence, entityID, 0, "PART_INFO_EID", partID);
		insertObject(sequence, entityID, 0, "PART_RESULT_EVENT_ORDER", ++eventCount);
		insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(site));
    insertObject(sequence, entityID, 0, "PROGRAM_TEST_CONFIG_EID", prodID);
		if (waferID != 0) {
			insertObject(sequence, entityID, 0, "SUBSTRATE_EVENT_EID", waferID);
		}
	}

	 /**
	  * Finish the part in the test event + add a Part_Instance_out entity
	  * @param fields
	  */
	private void insertPrr(HashMap<String, Object> fields) {
    int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
        ((Long) fields.get("SITE_NUM")).intValue()  );
		// MAKE A PIO AND PII
		entityID++;
		int pio = entityID;
    insertObject(sequence, pio, 0, "ENTITY_TYPE", "PART_INSTANCE_OUT");
    if(waferID != 0)insertObject(sequence, pio, 0, "SUBSTRATE_EVENT_EID", waferID);
		int te = currentTE[site];
		if (inGroup) {
			inGroup = false;
			if ((fields.get("TEST_T") != null) && ((Long) fields.get("TEST_T") != 0L)) {
				Long timeSecs = (Long) fields.get("TEST_T") * 100L; // millis to
																	// 10us
				realSequence = (timeSecs) + realSequence;
				insertObject(sequence, te, 0, "EVENT_TEST_TIME", ((double) timeSecs / 100000.0)); 
				// convert 19us steps to double seconds
			}
		}
		insertObject(sequence, te, 0, "RESULT_LIMIT_SET_EID", currentLimits);
		insertObject(sequence, te, 1, "BIN_EID", getHardbinEid((Long)fields.get("HARD_BIN")));
		// index = 0
		insertObject(sequence, pio, 0, "DISPOSITION_BIN_EID", getHardbinEid((Long)fields.get("HARD_BIN")));
		insertObject(sequence, pio, 1, "BIN_EID", getHardbinEid((Long)fields.get("HARD_BIN")));
    long tmpL = ((Long) fields.get("SOFT_BIN"));
    if (tmpL != 65535L) {
      insertObject(sequence, te, 2, "BIN_EID", getSoftbinEid(tmpL));   // index = 1
      insertObject(sequence, pio, 2, "BIN_EID", getSoftbinEid(tmpL));   // index = 1
    }
		int tmp = ((Integer) fields.get("X_COORD"));
		if (tmp != -32768) {
			insertObject(sequence, pio, 0, "PART_X", tmp);
		}
		tmp = ((Integer) fields.get("Y_COORD"));
		if (tmp != -32768) {
			insertObject(sequence, pio, 0, "PART_Y", tmp);
		}
		insertObject(sequence, te, 0, "NUM_TESTS", fields.get("NUM_TEST"));
		
		String partId = ((String) fields.get("PART_ID"));
		if(partId != null){
			String[] partIdSplit = partId.split(":");
			insertObject(sequence, te, 0, "PART_ID", partIdSplit[0]);
	     insertObject(sequence, pio, 0, "PART_ID", partIdSplit[0]);
       insertObject(sequence, pio, 0, "PART_ID_OUT", partIdSplit[0]);
		}

		String partTxt = ((String) fields.get("PART_TXT"));
		if(partTxt != null){
			String[] partTxtSplit = partTxt.split(":");
			insertObject(sequence, te, 0, "PART_TEXT", partTxtSplit[0]);
			if(partTxtSplit.length == 2){
			  insertObject(sequence, te, 0, "ECID", partTxtSplit[1]);			
	      insertObject(sequence, pio, 0, "ECID", partTxtSplit[1]);
			}
		}
		
		int flags = ((Byte) fields.get("PART_FLG")).intValue();
		if ((flags & 0x18) == 0x08) {
			insertObject(sequence, te, 0, "PF", "FAIL", "F");
		}
		if ((flags & 0x18) == 0x0) {
			insertObject(sequence, te, 0, "PF", "PASS", "P");
		}
		if ((flags & 0x14) == 0x10) {
			insertObject(sequence, te, 0, "PF", "TESTED", "T");
		}
		if ((flags & 0x04) == 0x04) {
			insertObject(sequence, te, 0, "PF", "ABORT", "A");
		}
		if ((flags & 0x03) != 0x0) {
			insertObject(sequence, te, 0, "RETEST_CODE", "RETEST", "R");
		}
	}

	private void insertPtr(HashMap<String, Object> fields) {
    int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
        ((Long) fields.get("SITE_NUM")).intValue()  );
		int te = currentTE[site];
		Integer tmp1 = ((Long) fields.get("TEST_NUM")).intValue();
		Integer testNumber = getTestEntityFor(tmp1, (String) fields.get("TEST_TXT"));
		if (!testUpdate.containsKey(testNumber)) {
			testUpdate.put(testNumber, new HashSet<Integer>());
			insertObject(sequence, testNumber, 0, "RESULT_DISTRIBUTION_TYPE", "CONTINUOUS");
	    insertObject(sequence, testNumber, 0, "ANALYZABLE", "Y");
	    insertObject(sequence, testNumber, 0, "RESULT_DATA_TYPE", "FLOAT");
			Byte opt = (Byte) fields.get("OPT_FLAG");
      if (opt == null) {
          // put default result scale
          insertObject(sequence, testNumber, 0, "RESULT_SCALE", testScaling.get(testNumber));
        }
			if (opt != null) {
        if ((opt & 0x01) == 0) { // insert results scale
          if (fields.get("RES_SCAL") != null) {
            testScaling.put(testNumber , Math.pow(10.0, (double) ((Integer) fields.get("RES_SCAL"))));
            String tscl = testUnits.get(testNumber);
            String tlbl = (String) fields.get("UNITS");
            String ncsl = " ";
            if(tlbl == null){
              ncsl = (scaleCharFromInt((Integer) fields.get("RES_SCAL")));          
            }else{
              ncsl = scaleCharFromInt((Integer) fields.get("RES_SCAL")) + tlbl;         
            }
            testUnits.put(testNumber, ncsl);
          }
        }
        insertObject(sequence, testNumber, 0, "RESULT_SCALE", testScaling.get(testNumber));
        if(!_cleanProp){  // LEAVE OUT LIMITS
  				if ((opt & 0x80) == 0) { // insert high limit
  					insertObject(sequence, currentLimits, testNumber, "UL", fields.get("HI_LIMIT"));
  				}
  				if ((opt & 0x40) == 0) { // insert low limit
  					insertObject(sequence, currentLimits, testNumber, "LL", fields.get("LO_LIMIT"));
  				}
          if ((opt & 0xc0) != 0xc0) { //  limit exists
            insertObject(sequence, currentLimits, testNumber, "LIMIT_COMPARE_TYPE", "I");
          }else{
            insertObject(sequence, currentLimits, testNumber, "LIMIT_COMPARE_TYPE", "N");
          }
  				/*TODO NOT IN SPEC
  				if ((opt & 0x04) == 0) { // insert lo spec
  					insertObject(sequence, testNumber, 0, "LSL", fields.get("LO_SPEC"));
  				}
  				if ((opt & 0x08) == 0) { // insert hi spec
  					insertObject(sequence, testNumber, 0, "USL", fields.get("HI_SPEC"));
  				}
  				*/
        }
			}
			String tUnits = testUnits.get(testNumber);
	    insertObject(sequence, testNumber, 0, "RESULT_UNITS_LABEL", tUnits);
	    if(tUnits.length() > 0) insertObject(sequence, testNumber, 0, "RESULT_UNITS", tUnits.substring(1));
		}
		if(site == 255) return;		
		Byte parm = ((Byte) fields.get("PARM_FLG")); 
		// can use for high low fail
		int flags = ((Byte) fields.get("TEST_FLG")).intValue();
		if ((flags & 0x2d) != 0) {
			// insertObject(sequence, te, testNumber, "CALC_TEST_FLAG", flags);
		}
		Double result = null; // check for valid result
		if ((flags & 0x10) == 0x0) { // test executed
			result = ((Number) fields.get("RESULT")).doubleValue();
			// tested but no pass/fail
			if ((flags & 0x40) == 0x40)
				insertObject(sequence, te, testNumber, "R", result, "T");
			// passed
			if ((flags & 0xc0) == 0x0)
				insertObject(sequence, te, testNumber, "R", result, "P");
			// failed
			if ((flags & 0xc0) == 0x80)
				insertObject(sequence, te, testNumber, "R", result, "F");
		} else { // no result no pass fail not executed
			//TODO insertObject(sequence, te, testNumber, "R", null, "X");
		}
		insertObject(sequence, te, testNumber, "ALARM_ID", fields.get("ALARM_ID"));
		// now update the testText
		updateTextText(testNumber, site, (String) fields.get("TEST_TXT"));
	}

	private void insertPcr(HashMap<String, Object> fields) {
	  Long head = (Long) fields.get("HEAD_NUM");
    Long tmp;
	  if(_includeSummaries){
    entityID++;
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "EVENT");
    insertObject(sequence, entityID, 0, "EVENT_TYPE", "RUN_SUMMARY");
		insertObject(sequence, entityID, 0, "PART_COUNT", fields.get("PART_CNT"));
		tmp = (Long) fields.get("RTST_CNT");
		if (tmp != null)
			if (tmp != 4294967295L)
				insertObject(sequence, entityID, 0, "RETEST_PART_COUNT", fields.get("RTST_CNT"));
		tmp = (Long) fields.get("ABRT_CNT");
		if (tmp != null)
			if (tmp != 4294967295L)
				insertObject(sequence, entityID, 0, "ABORT_PART_COUNT", fields.get("ABRT_CNT"));
		tmp = (Long) fields.get("GOOD_CNT");
		if (tmp != null) {
			if (tmp != 4294967295L) {
				insertObject(sequence, entityID, 0, "GOOD_PART_COUNT", fields.get("GOOD_CNT"));
				Long total = (Long) fields.get("PART_CNT");
				if (total > 0) {
					Long yield = (tmp * 100L) / total;
					insertObject(sequence, entityID, 0, "YIELD", yield.intValue());
				}
			}
		}
		if (head != 255L) {
	    insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(getSite(head.intValue(),((Long)fields.get("SITE_NUM")).intValue())));
			insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "SITE");
		} else {
			insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "TOTAL");
	    insertObject(sequence, entityID, 0, "TOUCHDOWN_COUNT", eventGroup);
	    insertObject(sequence, runID, 0, "MIN_PART", "1");
	    addToMetadata("ri.test.MIN_PART", "1");
	    insertObject(sequence, runID, 0, "MAX_PART", fields.get("PART_CNT").toString());
	    addToMetadata("ri.test.MAX_PART", fields.get("PART_CNT").toString());
      Long total = (Long) fields.get("PART_CNT");
      if (total > 0) {
        insertObject(sequence, runID, 0, "PART_COUNT", fields.get("PART_CNT"));
        addToMetadata("ri.test.PART_COUNT", fields.get("PART_CNT").toString());
        Long yield = (tmp * 100L) / total;
        insertObject(sequence, runID, 0, "YIELD", yield.intValue());
        addToMetadata("ri.test.YIELD", yield.toString());
      }
		}
		tmp = (Long) fields.get("FUNC_CNT");
		if (tmp != null)
			if (tmp != 4294967295L)
				insertObject(sequence, entityID, 0, "FUNCTIONAL_PART_COUNT", fields.get("FUNC_CNT"));
	  }else{
	    if (head == 255L) {
	      insertObject(sequence, runID, 0, "MIN_PART", "1");
	      addToMetadata("ri.test.MIN_PART", "1");
	      insertObject(sequence, runID, 0, "MAX_PART", fields.get("PART_CNT").toString());
	      addToMetadata("ri.test.MAX_PART", fields.get("PART_CNT").toString());
	      Long total = (Long) fields.get("PART_CNT");
	      tmp = (Long) fields.get("GOOD_CNT");
	      if (total > 0 && tmp != null) {
	        insertObject(sequence, runID, 0, "PART_COUNT", fields.get("PART_CNT"));
	        addToMetadata("ri.test.PART_COUNT", fields.get("PART_CNT").toString());
	        Long yield = (tmp * 100L) / total;
	        insertObject(sequence, runID, 0, "YIELD", yield.intValue());
	        addToMetadata("ri.test.YIELD", yield.toString());
	      }
	    }
	    
	  }
	}

	private void insertAtr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CHANGE_INFO");
		long time = (Long) fields.get("MOD_TIM");
		if (time != 0) {
			insertObject(time, entityID, 0, "MOD_DTTM_UTC", convertUnixTimeStampGMT(time));
			insertObject(time, entityID, 0, "MOD_DTTM", convertUnixTimeStamp(time));
		}
		insertObject(sequence, entityID, 0, "MOD_CMD", fields.get("CMD_LINE"));
	}

	private void insertBps(HashMap<String, Object> fields) {
		if (bpsID == 0) {
			entityID++;
			bpsID = entityID;
			insertObject(sequence, bpsID, 0, "ENTITY_TYPE", "BPS_RECS");
		}
		insertObject(sequence, bpsID, 0, "BPS", fields.get("SEQ_NAME"));
	}

	private void insertEps(HashMap<String, Object> fields) {
		if (epsID == 0) {
			entityID++;
			epsID = entityID;
			insertObject(sequence, epsID, 0, "ENTITY_TYPE", "EPS_RECS");
		}
		insertObject(sequence, epsID, 0, "EPS", "MARKER");
	}

	private void insertDtr(HashMap<String, Object> fields) {
		if (dtrID == 0) {
			entityID++;
			dtrID = entityID;
			insertObject(sequence, dtrID, 0, "ENTITY_TYPE", "DTR_RECS");
		}
		String dtr = (String) fields.get("TEXT_DAT");
		if(dtr.startsWith("RI:TIME")){
		  long time = Long.parseLong(dtr.split("=")[1]);
		  if(_indexTimeRef == 0L){
		    _indexTimeRef = time;
		  }else{
		    insertObject(sequence, dtrID, 0, "EVENT_CYCLE_TIME", time - _indexTimeRef);
		    _indexTimeRef = time;
		  }
		}else{
		  insertObject(sequence, dtrID, 0, "DTR_TXT", fields.get("TEXT_DAT"));
		}
	}

	private void insertGdr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
		Object[] tmp = (Object[]) fields.get("GEN_DATA");
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "GDR_DATA");
		insertObject(sequence, entityID, 0, "FIELD_CNT", fields.get("FLD_CNT"));
		Integer max = tmp.length;
		for (int i = 0; i < max; i++) {
			insertObject(sequence, entityID, i + 1, "DATA_ITEM", tmp[i]);
		}
	}

	private void insertSdr(HashMap<String, Object> fields) {
    insertObject(sequence, cellInventoryID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
    insertObject(sequence, ++cellInventoryID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
	  if(fields.get("HAND_TYP") != null){
	    entityID++;
	    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
	    insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "HANDLER");
	    insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("HAND_TYP"));
	    insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("HAND_ID")); 
      insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
	  }else{
	     entityID++;
	      insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "HANDLER");
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("MANUAL"));
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("MANUAL")); 
	      insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
	  }
	   if(fields.get("LASR_TYP") != null){
	      entityID++;
	      insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "LASER");
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("LASR_TYP"));
	      insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("LASR_ID"));
	       insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
	    }
		
    insertObject(sequence, prodID, 0, "SITE_COUNT", fields.get("SITE_CNT"));  
    // generate a hardware group and children entity for each site group 
    int hwCnt = 1;
    boolean inserted = false;
    entityID++; 
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("LOAD_TYP"));
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("LOAD_ID"));
    if(inserted){
       insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
       insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "LOADBOARD");
       insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
    }
    inserted = false;
    entityID++; 
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("DIB_TYP"));
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("DIB_ID"));
    if(inserted){
       insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
       insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "DIB");
       insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
    }
    inserted = false;
    entityID++; 
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("CONT_TYP"));
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("CONT_ID"));
    if(inserted){
       insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
       insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "SOCKET");
       insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
    }
    inserted = false;
    entityID++; 
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_TYPE", fields.get("CARD_TYP"));
    inserted = inserted | insertObject(sequence, entityID, 0, "CELL_INVENTORY_ID", fields.get("CARD_ID"));
    if(inserted){
       insertObject(sequence, entityID, 0, "ENTITY_TYPE", "CELL_INVENTORY");
       insertObject(sequence, entityID, 0, "CELL_INVENTORY_CLASS", "CIB");
       insertObject(sequence, entityID, 0, "SITE_GROUP", fields.get("SITE_GRP"));
    }
       
   // for each site in this group create a Site_Info
		int count = ((Number) fields.get("SITE_CNT")).intValue();
		if (count > 0) {
      for (int i = 0; i < count; i++) {
  			Object[] list = (Object[]) fields.get("SITE_NUM");
  	    int siteEid = ++entityID;
  	    siteInfoEid.put(Integer.parseInt(list[i].toString()), siteEid);
        insertObject(sequence, siteEid, 0, "ENTITY_TYPE", "SITE_INFO");
  	    insertObject(sequence, siteEid, 0, "SITE_ID", list[i]);
  	    insertObject(sequence, siteEid, 0, "PHYSICAL_SITE_NUMBER", list[i]);
  	    insertObject(sequence, siteEid, 0, "SITE_GROUP", fields.get("SITE_GRP"));
  	    insertObject(sequence, siteEid, 0, "ACTIVE_SITE", "Y");
  	   }
		}
	}

	private void insertHbr(HashMap<String, Object> fields) {
		int binEid = getHardbinEid((Long)fields.get("HBIN_NUM"));
		Long head = (Long) fields.get("HEAD_NUM");
    String bin = Long.toString((Long)fields.get("HBIN_NUM"));
    if(!hardBinUpdated.contains(bin)){
      hardBinUpdated.add(bin);
  		insertObject(sequence, binEid, 0, "BIN_NAME", fields.get("HBIN_NAM"));
  		if(fields.get("HBIN_NAM") == null){
  		  insertObject(sequence, binEid, 0, "BIN_NAME", "BIN" + String.format("%1$" + 3 + "s", bin).replace(' ', '0'));
  		}
  		insertObject(sequence, binEid, 0, "BIN_PF", fields.get("HBIN_PF"));
    // now the summary
  		if(_includeSummaries){
        entityID++;
        insertObject(sequence, entityID, 0, "ENTITY_TYPE", "EVENT");
        insertObject(sequence, entityID, 0, "EVENT_TYPE", "BIN_SUMMARY");
        insertObject(sequence, entityID, 0, "BIN_EID", binEid);
        insertObject(sequence, entityID, 0, "BIN_COUNT", fields.get("HBIN_CNT"));
        if (head != 255L) {
          insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(getSite(head.intValue(),
                                                              ((Long)fields.get("SITE_NUM")).intValue())));
          insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "SITE");
        }else{
          insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "TOTAL");
        }
  		}
    }
	}

	private void insertRdr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "RESCREEN");
		Number tmpStr = (Number) fields.get("NUM_BINS");
		// insertObject(sequence, entityID , 0, "RESCREEN_BIN_COUNT", tmpStr);
		int count = tmpStr.intValue();
		if (count > 0) {
			Object[] list = (Object[]) fields.get("RTST_BIN");
			for (int i = 0; i < count; i++) {
				insertObject(sequence, entityID, (i + 1), "RESCREEN_BIN", list[i]);
			}
		}
	}

	private void insertSbr(HashMap<String, Object> fields) {
	  String bin = Long.toString((Long)fields.get("SBIN_NUM"));
    int binEid = getSoftbinEid((Long)fields.get("SBIN_NUM"));
		Long head = (Long) fields.get("HEAD_NUM");
		Long binNum = (Long)fields.get("SBIN_NUM");
		Long siteNum = (Long) fields.get("SITE_NUM");
    if(!softBinInfoUpdated.contains(binNum)){
      softBinInfoUpdated.add(binNum);
      insertObject(sequence, binEid, 0, "BIN_NAME", fields.get("SBIN_NAM"));
      insertObject(sequence, binEid, 0, "BIN_PF", fields.get("SBIN_PF"));	
      if(fields.get("SBIN_NAM") == null){
        insertObject(sequence, binEid, 0, "BIN_NAME", "BIN" + String.format("%1$" + 3 + "s", bin).replace(' ', '0'));
      }
    }
		int binUpdate = Math.toIntExact((head * 65536 + siteNum * 256 + binNum));
		if(!softBinUpdated.contains(binUpdate)){
		  softBinUpdated.add(binUpdate);
		// now the summary
		  if(_includeSummaries){
    		entityID++;
        insertObject(sequence, entityID, 0, "ENTITY_TYPE", "EVENT");
        insertObject(sequence, entityID, 0, "EVENT_TYPE", "BIN_SUMMARY");
        insertObject(sequence, entityID, 0, "BIN_EID", binEid);
        insertObject(sequence, entityID, 0, "BIN_COUNT", fields.get("SBIN_CNT"));
        if (head != 255L) {
          insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(getSite(head.intValue(), siteNum.intValue())));
          insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "SITE");
        }else{
          insertObject(sequence, entityID, 0, "SUMMARY_TYPE", "TOTAL");
        }
		  }
	  }
	}

	private void insertPlr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
		pinlistID = entityID;
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "PIN_LIST");
		Integer max = ((Number) fields.get("GRP_CNT")).intValue();
		Object[] pmgi = (Object[]) fields.get("GRP_INDX");
		Object[] pmgm = (Object[]) fields.get("GRP_MODE");
		Object[] pmgr = (Object[]) fields.get("GRP_RADX");
		Object[] pmgpc = (Object[]) fields.get("PGM_CHAR");
		Object[] pmgrc = (Object[]) fields.get("RTN_CHAR");
		Object[] pmgpl = (Object[]) fields.get("PGM_CHAL");
		Object[] pmgrl = (Object[]) fields.get("RTN_CHAL");

		for (int i = 0; i < max; i++) {
			if ((Long) pmgi[i] != 0L)
				insertObject(sequence, entityID, i + 1, "GROUP_INDEX", pmgi[i]);
			if ((Long) pmgm[i] != 0L)
				insertObject(sequence, entityID, i + 1, "GROUP_MODE", pmgm[i]);
			if ((Long) pmgr[i] != 0L)
				insertObject(sequence, entityID, i + 1, "GROUP_RADIX", pmgr[i]);
			if (pmgpc != null)
				insertObject(sequence, entityID, i + 1, "PROGRAM_CHAR", pmgpc[i]);
			if (pmgrc != null)
				insertObject(sequence, entityID, i + 1, "RETURN_CHAR", pmgrc[i]);
			if (pmgpl != null)
				insertObject(sequence, entityID, i + 1, "PROGRAM_CHAL", pmgpl[i]);
			if (pmgrl != null)
				insertObject(sequence, entityID, i + 1, "RETURN_CHAL", pmgrl[i]);
		}
	}

	private void insertPgr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "PIN_GROUP");
		insertObject(sequence, entityID, 0, "GROUP_ID", fields.get("GRP_NAM"));
    insertObject(sequence, entityID, 0, "GROUP_NAME", fields.get("GRP_NAM"));
		insertObject(sequence, entityID, 0, "GROUP_INDEX", fields.get("GRP_INDX"));
		Integer max = ((Number) fields.get("INDX_CNT")).intValue();
		Object[] pmrs = (Object[]) fields.get("PMR_INDX");
		for (int i = 0; i < max; i++) {
			insertObject(sequence, entityID, i + 1, "PIN_INFO_EID", pmrIndex.get(((Long)pmrs[i]).intValue()));
		}
	}

	private void insertPmr(HashMap<String, Object> fields) {
		entityID++;// start a new entity
    int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
        ((Long) fields.get("SITE_NUM")).intValue());
    pmrIndex.put(((Long) fields.get("PMR_INDX")).intValue(), entityID);
		insertObject(sequence, entityID, 0, "ENTITY_TYPE", "PIN_INFO");
    insertObject(sequence, entityID, 0, "SITE_INFO_EID", siteInfoEid.get(site));
		insertObject(sequence, entityID, 0, "CHANNEL_NAME", fields.get("CHAN_NAM"));
		insertObject(sequence, entityID, 0, "PIN_ID", fields.get("PHY_NAM"));
		insertObject(sequence, entityID, 0, "PMR_INDEX", fields.get("PMR_INDX"));
		insertObject(sequence, entityID, 0, "CHANNEL_TYPE", fields.get("CHAN_TYP"));
		insertObject(sequence, entityID, 0, "LOGICAL_NAME", fields.get("LOG_NAM"));
	}

	private void insertMpr(HashMap<String, Object> fields) {
	  int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
	        ((Long) fields.get("SITE_NUM")).intValue()  );
		int te = currentTE[site];
		Integer testNum = ((Long) fields.get("TEST_NUM")).intValue();
		Integer primaryTestEid = 0;
		String resultId = "none";
		// first get the resultID and primaryEID for the primary test
    if (_testByNumber == true) {
      if (testMap.containsKey(testNum)) {
        primaryTestEid = testMap.get(testNum);
      } else {
        entityID++;
        testMap.put(testNum, entityID);
        testScaling.put(entityID, 1.0D);
        testUnits.put(entityID, " ");
        // put testNumber as result_number and result_id
        resultId = testNum.toString();
        primaryTestEid = entityID;
      }
    } else {
      if (testNameMap.containsKey((String) fields.get("TEST_TXT"))) {
        primaryTestEid = testNameMap.get((String) fields.get("TEST_TXT"));
      } else {
        entityID++;
        testNameMap.put((String) fields.get("TEST_TXT"), entityID);
        testScaling.put(entityID, 1.0D); // default scaling
        testUnits.put(entityID, " ");
        resultId = nameHash((String) fields.get("TEST_TXT"));
      }
    }
		if (!testUpdate.containsKey(primaryTestEid)) {
		  // the first test is the overall test info 
      testUpdate.put(primaryTestEid, new HashSet<Integer>());
			int count = ((Number) fields.get("RSLT_CNT")).intValue();
			//insertObject(sequence, primaryTestEid, 0, "RESULT_COUNT", count);
			//insertObject(sequence, primaryTestEid, 0, "RTN_ICNT", fields.get("RTN_ICNT"));

			Object[] list = (Object[]) fields.get("RTN_INDX");
			
			// now check if this is a shmoo or vs pins
			boolean shmoo = false;
      Double shmooValue = 0.0;
      Double shmooInc = 1.0;
			Byte opt = (Byte) fields.get("OPT_FLAG");
			if (opt != null) {
				if ((opt & 0x02) == 0) { // insert smhoo info
				  shmoo = true;
				  shmooValue = (Double) fields.get("START_IN");
				  shmooInc = (Double) fields.get("INCR_IN");
					//insertObject(sequence, primaryTestEid, 0, "START_IN", fields.get("START_IN"));
					//insertObject(sequence, primaryTestEid, 0, "INCR_IN", fields.get("INCR_IN"));
				}
			}
			// now create an entry for each 
			int subtest = 0;
			for (int j = 0; j < count; j++) {
				if (j == 0) {
					subtest = primaryTestEid;
				} else {
					entityID++;// start a new entity
					subtest = entityID;
				}
        insertObject(sequence, subtest, 0, "ENTITY_TYPE", "RESULT_INFO");
        insertObject(sequence, subtest, 0, "RESULT_NUMBER", testNum);
        if(j==0){
          insertObject(sequence, subtest, 0, "RESULT_ID", resultId);
        }else{
          insertObject(sequence, subtest, 0, "RESULT_ID", resultId + "_" + j);  
        }
        if(shmoo){
          insertObject(sequence, subtest, shmooCondID, "RESULT_COND_RANGE_VALUE", shmooValue);
          shmooValue = shmooValue + shmooInc;
        }else{
          insertObject(sequence, subtest, pinCondID, "RESULT_COND_RANGE_VALUE", pmrIndex.get(((Long)list[j]).intValue()));
        }
        insertObject(sequence, subtest, 0, "TEST_ORDER", ++testOrder);
        insertObject(sequence, subtest, 0, "RESULT_COND_RANGE_INDEX", j + 1);
				insertObject(sequence, subtest, 0, "RESULT_UNITS", fields.get("UNITS"));
				insertObject(sequence, subtest, 0, "UNITS_IN", fields.get("UNITS_IN"));
	      insertObject(sequence, subtest, 0, "RESULT_DISTRIBUTION_TYPE", "CONTINUOUS");
	      insertObject(sequence, subtest, 0, "ANALYZABLE", "Y");
	      insertObject(sequence, subtest, 0, "RESULT_DATA_TYPE", "FLOAT");
	      if (opt == null) {
          // put default result scale
          insertObject(sequence, subtest, 0, "RESULT_SCALE", testScaling.get(primaryTestEid));
        }
				if (opt != null) {
					if ((opt & 0xa0) == 0) { // insert high limit
						insertObject(sequence, currentLimits, subtest, "UL", fields.get("HI_LIMIT"));
					}
					if ((opt & 0x50) == 0) { // insert low limit
						insertObject(sequence, currentLimits, subtest, "LL", fields.get("LO_LIMIT"));
					}
	        if ((opt & 0x01) == 0) { // insert results scale
	          if (fields.get("RES_SCAL") != null) {
	            testScaling.put(primaryTestEid , Math.pow(10.0, (double) ((Integer) fields.get("RES_SCAL"))));
	            String tscl = testUnits.get(primaryTestEid);
	            String tlbl = (String) fields.get("UNITS");
	            String ncsl = " ";
	            if(tlbl == null){
	              ncsl = (scaleCharFromInt((Integer) fields.get("RES_SCAL")));          
	            }else{
	              ncsl = scaleCharFromInt((Integer) fields.get("RES_SCAL")) + tlbl;         
	            }
	            testUnits.put(primaryTestEid, ncsl);
	          }
	        }
					insertObject(sequence, subtest, 0, "RESULT_SCALE", testScaling.get(primaryTestEid));
          if (((opt & 0xa0) == 0) | ((opt & 0x50) == 0)) { //  limit exists
            insertObject(sequence, currentLimits, subtest, "LIMIT_COMPARE_TYPE", "I");
          }else{
            insertObject(sequence, currentLimits, subtest, "LIMIT_COMPARE_TYPE", "N");
          }
				}
		    String tUnits = testUnits.get(primaryTestEid);
		    insertObject(sequence, subtest, 0, "RESULT_UNITS_LABEL", tUnits);
		    if(tUnits.length() > 0) insertObject(sequence, subtest, 0, "RESULT_UNITS", tUnits.substring(1));	
			}
		}
		
		// now insert the results
		if(site == 255) return;
		Byte parm = ((Byte) fields.get("PARM_FLG")); // can use for high low
														// fail
		int flags = ((Byte) fields.get("TEST_FLG")).intValue();
		String pf = "P";
		if ((flags & 0xC0) == 0x80) {
			insertObject(sequence, te, primaryTestEid, "CALC_TEST_FLAG", flags & 0xff);
			pf = "F";
		}
		if ((flags & 0x20) == 0x20)
			pf = "A";
		if ((flags & 0x50) == 0x50)
			pf = "X";
		if ((flags & 0x7a) == 0x40)
			pf = "T";
		if ((flags & 0xa0) == 0xa0)
			pf = "FA";

//		String tmpStr = (String) fields.get("ALARM_ID");
//		if (tmpStr != null) {
//			if (!(tmpStr.trim().isEmpty())) {
//				insertObject(sequence, te, primaryTestEid, "ALARM_ID", tmpStr);
//			}
//		}
		int count = ((Number) fields.get("RSLT_CNT")).intValue();
		int statcount = ((Number) fields.get("RTN_ICNT")).intValue();
		String flag = "P";
		if (statcount == count && count > 0) {
			Object[] list = (Object[]) fields.get("RTN_RSLT");
			Object[] state = (Object[]) fields.get("RTN_STAT");
			if (count == 1) {
				Integer bin = (Integer) state[0];
				int binVal = (bin == null) ? 4 : bin.intValue();
				switch (binVal) {
				case 0:
					flag = "PL";
					break;
				case 1:
					flag = "PH";
					break;
				case 2:
					flag = "PM";
					break;
				case 3:
					flag = "PG";
					break;
				case 4:
					flag = "TX";
					break;
				case 5:
					flag = "FL";
					break;
				case 6:
					flag = "FH";
					break;
				case 7:
					flag = "FM";
					break;
				case 8:
					flag = "FG";
					break;
				case 9:
					flag = "TO";
					break;
				case 10:
					flag = "TS";
					break;
				}
				insertObject(sequence, te, primaryTestEid, "R", list[0], pf);
			} else {
				for (int i = 0; i < count; i++) {
					Integer bin = (Integer) state[i];
					int binVal = (bin == null) ? 4 : bin.intValue();
					switch (binVal) {
					case 0:
						flag = "PL";
						break;
					case 1:
						flag = "PH";
						break;
					case 2:
						flag = "PM";
						break;
					case 3:
						flag = "PG";
						break;
					case 4:
						flag = "TX";
						break;
					case 5:
						flag = "FL";
						break;
					case 6:
						flag = "FH";
						break;
					case 7:
						flag = "FM";
						break;
					case 8:
						flag = "FG";
						break;
					case 9:
						flag = "TO";
						break;
					case 10:
						flag = "TS";
						break;
					}
					insertObject(sequence, te, (primaryTestEid + i), "R", list[i], flag); 
				}
			}
		} else {
			if (count > 0) {
				Object[] list = (Object[]) fields.get("RTN_RSLT");
				if (count == 1) {
					insertObject(sequence, te, primaryTestEid, "R", list[0]);
				} else {
					for (int i = 0; i < count; i++) {
						insertObject(sequence, te, (primaryTestEid + i), "R", list[i]); 
					}
				}
			}
			if (statcount > 0) {
				Object[] list = (Object[]) fields.get("RTN_STAT");
				if (count == 1) {
					insertObject(sequence, te, primaryTestEid, "TEST_FLAG", list[0]);
				} else {
					for (int i = 0; i < statcount; i++) {
						insertObject(sequence, te, (primaryTestEid + i), "TEST_FLAG", list[i]);
					}
				}
			}
		}
		// now update the testText
		updateTextText(primaryTestEid, site, (String) fields.get("TEST_TXT"));
	}

	private void insertFtr(HashMap<String, Object> fields) {
    int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
        ((Long) fields.get("SITE_NUM")).intValue()  );
		int te = currentTE[site];
		Integer tmp1 = ((Long) fields.get("TEST_NUM")).intValue();
		Integer testNumber = getTestEntityFor(tmp1, (String) fields.get("TEST_TXT"));
		if (!testUpdate.containsKey(testNumber)) {
			insertObject(sequence, testNumber, 0, "RESULT_DISTRIBUTION_TYPE", "DISCRETE");
	    insertObject(sequence, testNumber, 0, "ANALYZABLE", "N");
	    insertObject(sequence, testNumber, 0, "RESULT_SCALE", 1.0);  // default
      testUpdate.put(testNumber, new HashSet<Integer>());
 
		}
		int flags = ((Byte) fields.get("TEST_FLG")).intValue();
		if ((flags & 0x2d) != 0) {
			insertObject(sequence, te, testNumber, "CALC_TEST_FLAG", flags);
		}
    if (pinlistID != 0) {
      insertObject(sequence, te, testNumber, "PIN_LIST_EID", pinlistID);
    }
		String pf = null;
		if ((flags & 0x40) == 0) {// pass/fail flag is valid
			if ((flags & 0x80) == 0x80) {
				pf = "F";
			} else {
				pf = "P";
			}
		}
		Long numFail = (Long) fields.get("NUM_FAIL");
		if(numFail == null){
		  numFail = 0L;
		}
		if ((flags & 0x50) == 0) { // tested with p/f
			insertObject(sequence, te, testNumber, "R", numFail, pf);
		}
		if ((flags & 0x20) == 0x20) { // aborted
			insertObject(sequence, te, testNumber, "R", numFail, "A");
		}
		if ((flags & 0x50) == 0x50) {// test not executed
			insertObject(sequence, te, testNumber, "R", numFail, "X");
		}
		if ((flags & 0x7a) == 0x40) {// tested no p/f
			insertObject(sequence, te, testNumber, "R", numFail, "T");
		}
		if ((flags & 0xa0) == 0xa0) {// failed due to abort
			insertObject(sequence, te, testNumber, "R", numFail, "FA");
		}
		String tmpStr = (String) fields.get("ALARM_ID");
		if (tmpStr != null) {
			if (!(tmpStr.trim().isEmpty())) {
				insertObject(sequence, te, testNumber, "ALARM_ID", tmpStr);
			}
		}
    if(site == 255) return;
    Byte opt = ((Byte) fields.get("OPT_FLAG")); // can be null
    if (opt != null) {
      insertObject(sequence, testNumber , 0, "FAIL_PIN", fields.get("FAIL_PIN"));
      insertObject(sequence, testNumber , 0, "VECT_NAM", fields.get("VECT_NAM"));
      insertObject(sequence, testNumber , 0, "TIME_SET", fields.get("TIME_SET"));
      insertObject(sequence, testNumber , 0, "OP_CODE", fields.get("OP_CODE"));
      insertObject(sequence, testNumber , 0, "PROG_TXT", fields.get("PROG_TXT"));
      insertObject(sequence, testNumber , 0, "RSLT_TXT", fields.get("RSLT_TXT"));
      int tmp = ((Long) fields.get("RTN_ICNT")).intValue();
      if (tmp != 0) {
        insertObject(sequence, testNumber , 0, "RTN_ICNT", fields.get("RTN_ICNT"));
        insertObject(sequence, testNumber , 0, "RTN_INDX", fields.get("RTN_INDX"));
        insertObject(sequence, testNumber , 0, "RTN_STAT", fields.get("RTN_STAT"));
      }
      tmp = ((Long) fields.get("PGM_ICNT")).intValue();
      if (tmp != 0) {
        insertObject(sequence, testNumber , 0, "PGM_ICNT", fields.get("PGM_ICNT"));
        insertObject(sequence, testNumber , 0, "PGM_INDX", fields.get("PGM_INDX"));
        insertObject(sequence, testNumber , 0, "PGM_STAT", fields.get("PGM_STAT"));
      }
      insertObject(sequence, testNumber , 0, "PATG_NUM", fields.get("PATG_NUM"));
      // these are arrays
      insertObject(sequence, testNumber , 0, "SPIN_MAP", fields.get("SPIN_MAP"));
      // handle optional data
      if ((opt & 0x01) == 0) {
        insertObject(sequence, testNumber , 0, "CYCL_CNT", fields.get("CYCL_CNT"));
      }
      if ((opt & 0x02) == 0) {
        insertObject(sequence, testNumber , 0, "REL_VADR", fields.get("REL_VADR"));
      }
      if ((opt & 0x04) == 0) {
        insertObject(sequence, testNumber , 0, "REPT_CNT", fields.get("REPT_CNT"));
      }
      if ((opt & 0x08) == 0) {
        insertObject(sequence, testNumber , 0, "NUM_FAIL", fields.get("NUM_FAIL"));
      }
      if ((opt & 0x10) == 0) {
        insertObject(sequence, testNumber , 0, "XFAIL_AD", fields.get("XFAIL_AD"));
      }
      if ((opt & 0x20) == 0) {
        insertObject(sequence, testNumber , 0, "YFAIL_AD", fields.get("YFAIL_AD"));
      }
      if ((opt & 0x40) == 0) {
        insertObject(sequence, testNumber , 0, "VECT_OFF", fields.get("VECT_OFF"));
      }
    }
		// now update the testText
		updateTextText(testNumber, site, (String) fields.get("TEST_TXT"));
	}

	private void insertVur(HashMap<String, Object> fields) {
		//TODO should we do anything with this?
		/*int count = ((Long) fields.get("UPD_CNT")).intValue(); // num vers
		Object[] list = (Object[]) fields.get("UPD_NAM");
		for( int i = 0; i < count;i++){
			insertObject(sequence, runID, i + 1, "VERSION", list[i]);
		}
		*/
	}
	private void insertPsr(HashMap<String, Object> fields) {
	  //TODO PAT_FILE, FILE_UID, ATPG_DSC, SRC_ID NOT SUPPORTED  
	  Byte continuation = (Byte) fields.get("CONT_FLG");
	  if(_continuationEid == 0){ // check if first pass   
	     // init the multi record buffers
	    _contBuffers = new SmCborBuffer[3];
	    _contBuffers[0] = new SmCborBuffer(); // begin
	    _contBuffers[1] = new SmCborBuffer(); // end 
	    _contBuffers[2] = new SmCborBuffer(); // labels
	    _contBuffers[0].startArray();
	    _contBuffers[1].startArray();
	    _contBuffers[2].startArray();
	  }
		Byte opt = ((Byte) fields.get("OPT_FLG"));
		int count = ((Long) fields.get("LOCP_CNT")).intValue(); // local count
		int total = 0; // total element
		int psrId = 0;
		if(continuation == 1){// there is more to follow only add extensions
		  _contTotal = _contTotal + count;
			if(_continuationEid == 0){
				entityID++; // get the next entity ID
				psrId = entityID;
				_continuationEid = psrId;
			}else{
				psrId = _continuationEid;
			}	
		}else{// this is the last or only record
		  total = _contTotal + count;
      _contTotal = 0;
			if(_continuationEid == 0){
				entityID++; // get the next entity ID
				psrId = entityID;
			}else{
				psrId = _continuationEid;
				_continuationEid = 0;
			}
		}
		// now insert the repeating records based on LOCP_CNT and _continuationIndex	
		// stored as unbounded arrays
		if ((opt & 0x01) == 0) { // insert label
			Object[] list = (Object[])fields.get("PAT_LBL");
			for(int i = 0; i < count; i++){		
			  _contBuffers[2].put((String)list[i]);
			}
    Object[] array = (Object[])fields.get("PAT_BGN");			
    for( int i = 0; i < array.length; i++){
        _contBuffers[0].put((Long)array[i]);
      }
    array = (Object[])fields.get("PAT_END");     
    for( int i = 0; i < array.length; i++){
        _contBuffers[1].put((Long)array[i]);
      }
		}
		// if last then save the repeating arrays
		if(continuation == 0){
	    insertObject(sequence, psrId, 0, "ENTITY_TYPE", "PATTERN_SEQ_RECORD");
	    insertObject(sequence, psrId, 0, "PATTERN_SEQ_INDEX", fields.get("PSR_INDX"));
	    insertObject(sequence, psrId, 0, "PATTERN_SEQ_NAME", fields.get("PSR_NAM"));
	    insertObject(sequence, psrId, 0, "PATTERN_SEQ_COUNT", total);
	    _contBuffers[0].end();
	    _contBuffers[1].end();
	    _contBuffers[2].end();
      insertObject(sequence, psrId, 0 , "PAT_BGN", _contBuffers[0].toBytes());  
      insertObject(sequence, psrId, 0 , "PAT_END", _contBuffers[1].toBytes()); 
      insertObject(sequence, psrId, 0 , "PAT_LABEL", _contBuffers[2].toBytes());
      _contBuffers = null;
		}
	}	
	private void insertNmr(HashMap<String, Object> fields) {
		//TODO not implemented
		System.out.println("NMR not inserted");
	}	
	private void insertCnr(HashMap<String, Object> fields) {
		//TODO not implemented
		System.out.println("CNR not inserted");
	}	
	private void insertSsr(HashMap<String, Object> fields) {
		//TODO not implemented
		System.out.println("SSR not inserted");
	}	
	private void insertCdr(HashMap<String, Object> fields) {
		//TODO not implemented
		System.out.println("CDR not inserted");
	}
	private void insertStr(HashMap<String, Object> fields) {
		//TODO not complete
	 Byte continuation = (Byte) fields.get("CONT_FLG");
	 if(_continuationEid == 0){ // check if first pass   
	   // init the multi record buffers
     _contBuffers = new SmCborBuffer[6];
     _contBuffers[0] = new SmCborBuffer(); // cyc_ofst
     _contBuffers[1] = new SmCborBuffer(); // pmr_indx 
     _contBuffers[2] = new SmCborBuffer(); // exp_data
     _contBuffers[3] = new SmCborBuffer(); // cap_data
     _contBuffers[4] = new SmCborBuffer(); // pat_num
     _contBuffers[5] = new SmCborBuffer(); // bit_pos
     for(int i = 0 ; i < 6 ;i++)_contBuffers[i].startArray();;
     // now the shared attributes
     int site = getSite(((Long) fields.get("HEAD_NUM")).intValue(),
         ((Long) fields.get("SITE_NUM")).intValue()  );
     int te = currentTE[site];
     _continuationEid = te;
     Integer tmp1 = ((Long) fields.get("TEST_NUM")).intValue();
     Integer testNumber = getTestEntityFor(tmp1, (String) fields.get("TEST_TXT"));
     _continuationEid2 = testNumber;
     if (!testUpdate.containsKey(testNumber)) {
       insertObject(sequence, testNumber, 0, "STDF_REC", "STR");
       insertObject(sequence, testNumber, 0, "RESULT_DISTRIBUTION_TYPE", "SCAN");
       insertObject(sequence, testNumber, 0, "PATTERN_SEQ", fields.get("PSR_REF"));
       insertObject(sequence, testNumber, 0, "LOG_TYPE", fields.get("LOG_TYP"));
       testUpdate.put(testNumber, new HashSet<Integer>());
     }
     if(site == 255) return;
     int flags = ((Byte) fields.get("TEST_FLG")).intValue();
     if ((flags & 0x10) == 0x0) { // test executed
       // tested but no pass/fail
       if ((flags & 0x40) == 0x40)
         insertObject(sequence, te, testNumber, "R", 0, "T");
       // passed
       if ((flags & 0xc0) == 0x0)
         insertObject(sequence, te, testNumber, "R", 0, "P");
       // failed
       if ((flags & 0xc0) == 0x80){
         int fails = ((Long) fields.get("TOTF_CNT")).intValue();
         insertObject(sequence, te, testNumber, "R", fails, "F");
       }
     } else { // no result no pass fail not executed
       //insertObject(sequence, te, testNumber, "R", null, "X");
     }
     int fmuFlags = ((Byte) fields.get("FMU_FLG")).intValue();
     byte[] fmap = (byte[])fields.get("FAL_MAP");
     if (fmap != null){// fail MAP
       SmCborBuffer buffer = new SmCborBuffer();
       buffer.startArray();
       for( int i = 0; i < fmap.length; i++){
         buffer.put(fmap[i]);
       }
       buffer.end();
       insertObject(sequence, te, testNumber, "FAL_MAP", buffer.toBytes());
     }
     fmap = (byte[])fields.get("MASK_MAP");
     if (fmap != null){// mask MAP
       SmCborBuffer buffer = new SmCborBuffer();
       buffer.startArray();
       for( int i = 0; i < fmap.length; i++){
         buffer.put(fmap[i]);
       }
       buffer.end();
       insertObject(sequence, te, testNumber, "MASK_MAP", buffer.toBytes());  
     }
     insertObject(sequence, te, testNumber, "FMU_FLG", fmuFlags);
     insertObject(sequence, te, testNumber, "RSLT_TXT", fields.get("RSLT_TXT"));
     insertObject(sequence, te, testNumber, "Z_VAL", fields.get("Z_VAL"));
     insertObject(sequence, te, testNumber, "CYC_CNT", fields.get("CYC_CNT"));
     insertObject(sequence, te, testNumber, "CYC_BASE", fields.get("CYC_BASE"));
     insertObject(sequence, te, testNumber, "TOTF_CNT", fields.get("TOTF_CNT"));
     insertObject(sequence, te, testNumber, "TOTL_CNT", fields.get("TOTL_CNT"));
     insertObject(sequence, te, testNumber, "COND_CNT", fields.get("COND_CNT"));
     insertObject(sequence, te, testNumber, "LIM_CNT", fields.get("LIM_CNT"));
     insertObject(sequence, te, testNumber, "CYC_SIZE", fields.get("CYC_SIZE"));
     insertObject(sequence, te, testNumber, "PMR_SIZE", fields.get("PMR_SIZE"));
     insertObject(sequence, te, testNumber, "PAT_SIZE", fields.get("PAT_SIZE"));
     insertObject(sequence, te, testNumber, "BIT_SIZE", fields.get("BIT_SIZE"));
     insertObject(sequence, te, testNumber, "BIT_BASE", fields.get("BIT_BASE"));
     insertObject(sequence, te, testNumber, "CAP_BGN", fields.get("CAP_BGN"));
     insertObject(sequence, te, testNumber, "PMR_CNT", fields.get("PMR_CNT"));
     insertObject(sequence, te, testNumber, "PAT_CNT", fields.get("PAT_CNT"));
     insertObject(sequence, te, testNumber, "EXP_CNT", fields.get("EXP_CNT"));
     insertObject(sequence, te, testNumber, "CAP_CNT", fields.get("CAP_CNT"));
     insertObject(sequence, te, testNumber, "BPOS_CNT", fields.get("BPOS_CNT"));
     insertObject(sequence, te, testNumber, "ALARM_ID", fields.get("ALARM_ID"));
     updateTextText(testNumber, site, (String) fields.get("TEST_TXT")); 
	 }
	 // fill buffers
   Object[] array = (Object[])fields.get("CYC_OFST");  
   if(array != null){
     for(int i = 0; i < array.length; i++){
       _contBuffers[0].put((Long)array[i]);
     }
   }
   array = (Object[])fields.get("PMR_INDX");  
   if(array != null){
     for(int i = 0; i < array.length; i++){
       _contBuffers[1].put((Long)array[i]);
     }
   }
   array = (Object[])fields.get("PAT_NUM");  
   if(array != null){
     for(int i = 0; i < array.length; i++){
       _contBuffers[4].put((Long)array[i]);
     }
   }
   array = (Object[])fields.get("BIT_POS");  
   if(array != null){
     for(int i = 0; i < array.length; i++){
       _contBuffers[5].put((Long)array[i]);
     }
   }
   if(continuation == 0){// there is nothing to follow only add arrays
     int te = _continuationEid;
   // handle multiple record fields
    for(int i = 0 ; i < 6 ;i++)_contBuffers[i].end();
    insertObject(sequence, te, _continuationEid2 , "CYC_OFST", _contBuffers[0].toBytes());  
    insertObject(sequence, te, _continuationEid2 , "PMR_INDX", _contBuffers[1].toBytes()); 
    insertObject(sequence, te, _continuationEid2 , "EXP_DATA", _contBuffers[2].toBytes());
    insertObject(sequence, te, _continuationEid2 , "CAP_DATA", _contBuffers[3].toBytes());
    insertObject(sequence, te, _continuationEid2 , "PAT_NUM", _contBuffers[4].toBytes());
    insertObject(sequence, te, _continuationEid2 , "BIT_POS", _contBuffers[5].toBytes());
    _contBuffers = null;
    _continuationEid = 0;
    _continuationEid2 = 0;
   }
	}
	/**
	 * given a bin number as string find a=the eid, create one if missing
	 * @param binNumber
	 * @return
	 */
	private int getHardbinEid(Long binNumber){
	  String bin = Long.toString(binNumber);
	  if(!hardBinInfoEid.containsKey(bin)){
	    entityID++;
	    hardBinInfoEid.put(bin, entityID);   
	    insertObject(sequence, entityID, 0, "ENTITY_TYPE", "BIN");
	    insertObject(sequence, entityID, 0, "BIN_TYPE", "HARDBIN");
	    insertObject(sequence, entityID, 0, "BIN_NUMBER", binNumber);
	  }
	  return hardBinInfoEid.get(bin);
	}
	
	 /**
   * given a bin number as string find a=the eid, create one if missing
   * @param binNumber
   * @return
   */
  private int getSoftbinEid(Long binNumber){
    String bin = Long.toString(binNumber);
    if(!softBinInfoEid.containsKey(bin)){
      entityID++;
      softBinInfoEid.put(bin, entityID);
      insertObject(sequence, entityID, 0, "ENTITY_TYPE", "BIN");
      insertObject(sequence, entityID, 0, "BIN_TYPE", "SOFTBIN");
      insertObject(sequence, entityID, 0, "BIN_NUMBER", binNumber);
    }
    return softBinInfoEid.get(bin);
  }
  
  private String generateScript(String limits){
    boolean setLimits = limits != null && !limits.isEmpty();
    StringBuffer buf = new StringBuffer();
    buf.append(
        "^+toppane+identifier=top+type=viewModel+windowSize=100@100+label=" + fileName
    );
    buf.append(
        "^+subpane+class=DatatableRlinda+owner=top+frameRatio=0@100;100@0+identifier=10+maintable=ritdb1+numColumns=10"
        + "+visRows=TEST_ORDER+visCols=PART_RESULT_EVENT_ORDER"
        + "^+subpane+class=DataBaseView+owner=10+type=x2Left+identifier=10_x2Left+frameRatio=0@100;10@0"
        + "+format=%.3f"
        + "+function=~f1~sort~ASC~visRows"
        + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value"
        + "+rule=~left~source~?testId~0~TEST_ORDER~#visRows"
        + "+rule=~left~source~?testId~0~ENTITY_TYPE~RESULT_INFO"
        + "+rule=~left~source~?testId~0~RESULT_NUMBER~?col1"
        + "+rule=~left~source~?testId~0~RESULT_NAME~?col2"
        + "+rule=~left~source~?testId~0~RESULT_UNITS_LABEL~?col3"
        + "+setRendering=~33~colors=`1`7``+setVarColor=~color~33"
        );
    if(setLimits){
      buf.append(
          "+columnTitles=~Test Num~name~units~Limit min~Limit max"
        + "+find=~left~?col1~?col2~?col3~?col4 * ?scale~?col5 * ?scale~#visRows"
        + "+rule=~left~source~?limitId~0~ENTITY_TYPE~RESULT_LIMIT_SET"
        + "+rule=~left~source~?limitId~?testId~LL~?col4"
        + "+rule=~left~source~?limitId~?testId~UL~?col5"
        + "+function=~left~nullable~limitId~col3~scale~col2"
        + "+rule=~left~source~?testId~0~RESULT_SCALE~?scale"
        + "+rule=~left~source~?limitId~0~LIMIT_SET_NAME~" + limits
      );
    }else{
      buf.append(
          "+columnTitles=~Test Num~name~units"
        + "+find=~left~?col1~?col2~?col3~#visRows"
        + "+function=~left~nullable~col3"
      );
    }
    buf.append(
      "^+subpane+class=DataBaseView+owner=10+type=x1Top+identifier=10_x1Top+frameRatio=0@100;100@90+function=~f1~sort~ASC~visCols"
        + "+columnTitles=~device~result~site+find=~top~?col1~?col2~col5~?color~#visCols"
        + "+setRendering=~33~colors=`7`15``"
        + "+setRendering=~32~colors=`1`7``+setRendering=~34~colors=`7`27``"
        + "+setVarColor=~color~32~FAIL~34"
        + "+tuple=~source~ritdb1.entityId~ritdb1.name~ritdb1.value"
        + "+rule=~top~source~?eventId~_~PART_RESULT_EVENT"
        + "+rule=~top~source~?eventId~PART_RESULT_EVENT_ORDER~#visCols"
        + "+rule=~top~source~?eventId~PART_ID~?col1"
        + "+rule=~top~source~?eventId~PF~?col2"
        + "+rule=~top~source~?eventId~SITE_INFO_EID~?siteId"
        + "+rule=~top~source~?siteId~PHYSICAL_SITE_NUMBER~?col5"
        + "+rule=~top~source~?eventId~PF~?color"
    );
    buf.append(
      "^+subpane+class=DataBaseView+owner=10+type=y+columnTitles=data"
      + "+find=~mid~?data * ?scale~?color~?eventId~?testId~#visRows~#visCols"
      + "+identifier=10_y+frameRatio=10@90;100@0+display=data+setRendering=~33~colors=`1`7``+setRendering=~34~colors=`27`7``"
      + "+alignX1=eventId+alignX2=testId"
      + "+scrollenable=on"
      + "+format=%.3f"
      + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value~ritdb1.value2"
      + "+rule=~data~source~?eventId~?testId~R~?data~?color"
      + "+rule=~data~source~?eventId~_~PART_RESULT_EVENT_ORDER~#visCols~_"
      + "+rule=~data~source~?testId~_~TEST_ORDER~#visRows~_"
      + "+rule=~data~source~?testId~_~RESULT_SCALE~?scale~_"
      + "+function=~foo~nullable~scale~data"
      );
    if(setLimits){
      buf.append("+setVarColor=~color~33~F~34~P~33~T~33~X~33");
    }else{
      buf.append("+setVarColor=~color~33~F~33~P~33~T~33~X~33");
    }
    buf.append(
        "^+menu+owner=10_y+selector=menuXY+identifier=xyMenu"
      + "+value=~%1031 Auto Width~%1032 Columns~%1033 JDebug"
    );
    buf.append(
        "^+menu+owner=10_x2Left+selector=menuX2+identifier=x2Menu+value=~%1031 Auto Width"
    );
    buf.append(
        "^+menu+owner=top+title=font+selector=menuFont+identifier=fontMenu+menuItem=~%1035 Font~10_y"
        + "+menuItem=~%1010 SaveCsv~10_y"
    );
    buf.append("^+command=createView");
    return buf.toString();
  }
  
  // generates a ascii riri version
  private String generateCsvScript(String limits){
    StringBuffer buf = new StringBuffer();
    buf.append(
         "^+subpane+type=x2Left"
        + "+find=~left~col1~col2~col4 * scale~col5 * scale~col3~#visRows"
        + "+columnTitles=~Test Num~name~Limit min~Limit max~units"
        + "+function=~f1~sort~ASC~visRows"
        + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value"
        + "+rule=~left~source~?testId~0~TEST_ORDER~#visRows"
        + "+rule=~left~source~?testId~0~ENTITY_TYPE~RESULT_INFO"
        + "+rule=~left~source~?testId~0~RESULT_NUMBER~?col1"
        + "+rule=~left~source~?testId~0~RESULT_NAME~?col2"
        + "+rule=~left~source~?testId~0~RESULT_UNITS_LABEL~?col3"
        + "+rule=~left~source~?limitId~0~ENTITY_TYPE~RESULT_LIMIT_SET"
        + "+rule=~left~source~?limitId~?testId~LL~?col4"
        + "+rule=~left~source~?limitId~?testId~UL~?col5"
        + "+function=~left~nullable~limitId~col3~scale~col2"
        + "+rule=~left~source~?testId~0~RESULT_SCALE~?scale"
        + "+rule=~left~source~?limitId~0~LIMIT_SET_NAME~" + limits
      );
    buf.append(
      "^+subpane+type=x1Top"
        + "+function=~f1~sort~ASC~visCols"
        + "+columnTitles=~device~result~site"
        + "+find=~top~col1~col2~col5~#visCols"
        + "+tuple=~source~ritdb1.entityId~ritdb1.name~ritdb1.value"
        + "+rule=~top~source~?eventId~_~PART_RESULT_EVENT"
        + "+rule=~top~source~?eventId~PART_RESULT_EVENT_ORDER~#visCols"
        + "+rule=~top~source~?eventId~PART_ID~?col1"
        + "+rule=~top~source~?eventId~PF~?col2"
        + "+rule=~top~source~?eventId~SITE_INFO_EID~?siteId"
        + "+rule=~top~source~?siteId~PHYSICAL_SITE_NUMBER~?col5"
    );
    buf.append(
      "^+subpane+type=y"
      + "+find=~mid~data * scale~#visRows~#visCols"
      + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value~ritdb1.value2"
      + "+rule=~data~source~?eventId~?testId~R~?data~_"
      + "+rule=~data~source~?eventId~_~PART_RESULT_EVENT_ORDER~#visCols~_"
      + "+rule=~data~source~?testId~_~TEST_ORDER~#visRows~_"
      + "+rule=~data~source~?testId~_~RESULT_SCALE~?scale~_"
      + "+function=~foo~nullable~scale~data"
      );
    return buf.toString();
  }

//  private String generateCsvScript(String limits){  // generates a CBOR map
//    SmCborBuffer buffer = new SmCborBuffer();
//    GuruUtilities.insertRiri(
//        "^+toppane+identifier=top+type=viewModel+windowSize=100@100+label=" + fileName
//    , buffer);
//    GuruUtilities.insertRiri(
//        "^+subpane+class=DatatableRlinda+owner=top+frameRatio=0@100;100@0+identifier=10+maintable=ritdb1+numColumns=10"
//        ,buffer);
//    GuruUtilities.insertRiri(
//         "^+subpane+class=DataBaseView+owner=10+type=x2Left+identifier=10_x2Left+frameRatio=0@100;10@0"
//        + "+function=~f1~sort~ASC~testId"
//        + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value"
//        + "+rule=~left~source~?testId~0~TEST_ORDER~?visRows"
//        + "+rule=~left~source~?testId~0~ENTITY_TYPE~RESULT_INFO"
//        + "+rule=~left~source~?testId~0~RESULT_NUMBER~?col1"
//        + "+rule=~left~source~?testId~0~RESULT_NAME~?col2"
//        + "+rule=~left~source~?testId~0~RESULT_UNITS_LABEL~?col3"
//        + "+columnTitles=~Test Num~name~units~Limit min~Limit max"
//        + "+find=~left~?col1~?col2~?col3~?col4 * ?scale~?col5 * ?scale~#visRows"
//        + "+rule=~left~source~?limitId~0~ENTITY_TYPE~RESULT_LIMIT_SET"
//        + "+rule=~left~source~?limitId~?testId~LL~?col4"
//        + "+rule=~left~source~?limitId~?testId~UL~?col5"
//        + "+function=~left~nullable~limitId~col3~scale~col2"
//        + "+rule=~left~source~?testId~0~RESULT_SCALE~?scale"
//        + "+rule=~left~source~?limitId~0~LIMIT_SET_NAME~" + limits
//        , buffer);
//    GuruUtilities.insertRiri(
//      "^+subpane+class=DataBaseView+owner=10+type=x1Top+identifier=10_x1Top+frameRatio=0@100;100@90+function=~f1~sort~ASC~visCols"
//        + "+columnTitles=~device~result~site"
//        + "+find=~top~?col1~?col2~col5"
//        + "+tuple=~source~ritdb1.entityId~ritdb1.name~ritdb1.value"
//        + "+rule=~top~source~?eventId~_~PART_RESULT_EVENT"
//        + "+rule=~top~source~?eventId~PART_RESULT_EVENT_ORDER~?visCols"
//        + "+rule=~top~source~?eventId~PART_ID~?col1"
//        + "+rule=~top~source~?eventId~PF~?col2"
//        + "+rule=~top~source~?eventId~SITE_INFO_EID~?siteId"
//        + "+rule=~top~source~?siteId~PHYSICAL_SITE_NUMBER~?col5"
//        , buffer);
//    GuruUtilities.insertRiri(
//      "^+subpane+class=DataBaseView+owner=10+type=y+columnTitles=data"
//      + "+find=~mid~?data * ?scale~?color~?eventId~?testId~#visRows~#visCols"
//      + "+identifier=10_y+frameRatio=10@90;100@0+display=data+setRendering=~33~colors=`1`7``+setRendering=~34~colors=`27`7``"
//      + "+alignX1=eventId+alignX2=testId"
//      + "+scrollenable=on"
//      + "+tuple=~source~ritdb1.entityId~ritdb1.indexId~ritdb1.name~ritdb1.value~ritdb1.value2"
//      + "+rule=~data~source~?eventId~?testId~R~?data~?color"
//      + "+rule=~data~source~?eventId~_~PART_RESULT_EVENT_ORDER~?visCols~_"
//      + "+rule=~data~source~?testId~_~TEST_ORDER~?visRows~_"
//      + "+rule=~data~source~?testId~_~RESULT_SCALE~?scale~_"
//      + "+function=~foo~nullable~scale~data"
//      , buffer);
//    return GuruUtilities.asString(buffer.toBytes());
//  }
  
  /**Return the 16 char SHA1 hash hex string for bytes
   * Used to hide names
  */
  private String nameHash(Object string) {
    if(!_cleanProp) return (String) string;
    try { 
      MessageDigest md=MessageDigest.getInstance("SHA"); 
      return (GuruUtilities.hexIt(md.digest(GuruUtilities.asBytes((String)string))).substring(25));
    } 
    catch (Exception e) { return ""; } //this would only happen if "SHA" was no longer a known thing
  }
  /**
   * convent sites > 255 using head mod 16.  Max = 1024
   * @param head
   * @param site
   * @return
   */
  public int getSite(int head, int site){
    int finalSite = site;
    if(head == 17) finalSite = finalSite + 255;
    if(head == 33) finalSite = finalSite + 511;
    if(head == 49) finalSite = finalSite + 768;
    if(head == 65) finalSite = 1024;
    return finalSite;
  }
  
}

