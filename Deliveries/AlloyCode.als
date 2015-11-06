module myTaxiService

//DATA TYPES

sig Text{}

sig Double{}

enum DriverState {
	available,
	unavailable
}

enum RequestState {
	pending,
	accepted,
	ongoing,
	completed
}

sig gpsCoord {
	latitude : one Double,
	longitude : one Double
}

//SIGNATURES

abstract sig User {
	name : one Text,
	surname : one Text,
	email : one Text,
	phoneNumber : one Text,
	username : one Text,
	password : one Text
}

sig TaxiDriver extends User {
	licenseNumber : one Text,
	taxiCode : one Text,
	state : one DriverState,
	position : one Location
}

sig Client extends User {
}

abstract sig Request {
	startingLoc : one Location,
	arriveLoc : one Location,
	ID : one Text,
	date : one Text,
	timeStamp : Text,
	client : one Client,
	driver : lone TaxiDriver,
	state : one RequestState
}

sig Demand extends Request {
}

sig Booking extends Request {
	bookedTime : one Text
}

sig Notification {
	ID : one Text,
	message : one Text,
	date : one Text,
	time : one Text,
	request : one Request
}

sig Location {
	coord : one gpsCoord,
	zone : one Zone,
	address : one Text,
	city : one Text,
	state : one Text,
	details : one Text
}

sig QueueNode {
	next : lone QueueNode,
	taxi : one TaxiDriver
}

sig TaxiQueue {
	root : lone QueueNode
}

sig Zone {
	vertex : one gpsCoord,
	distance : one Double,
	queue : one TaxiQueue
}

//FACTS

//Reject registrations that uses an email, username or phone number already registered 
fact noDoubleUser {
	(no disj u1, u2 : User | u1.email = u2.email) and
	(no disj u1, u2 : User | u1.username = u2.username) and
	(no disj u1, u2 : User | u1.phoneNumber = u2.phoneNumber)
}

//Avoid creation of a request in which the starting location coincide with the arrival one
fact noSamePlaceForRequest {
	all r : Request | r.startingLoc!=r.arriveLoc
}

//ID is a unique value for requests
fact noDoubleRequest {
	no disj r1,r2 : Request | r1.ID=r2.ID
}

//Every notification refers only to one request
fact notifyToOneRequest {
	no disj n1, n2 : Notification | n1.request = n2.request
}

//Unless is pending, every request has at least one notification
fact atLeastOneNotification {
	all r : Request | some n : Notification | 
			r.state!=pending and  
			r=n.request
}

//Only completed or ongoing requests are related to a driver
fact driverForCompletedAndOngoing {
	all r : Request | (r.state=pending or r.state=accepted) iff no r.driver
}

//A Client cannot be related to more than one ongoing request
fact noClientsUbiquity {
	no disj r1,r2 : Request | 
		r1.state=ongoing and r2.state=ongoing and
		r1.client=r2.client
}

//A driver can only be related to one ongoing request
fact noDriverUbiquity {
	all t : TaxiDriver | lone r : Request | r.driver=t and r.state=ongoing
}

//An ongoing request is related to one unavailable driver
fact ongoingRequestOccupiesDriver {
	all r : Request | r.state=ongoing iff r.driver.state=unavailable
}

//Two gpsCoords have the same latitude and longitude value if and only are the same one
fact UniqueCoordsUniqueValues {
	all g1,g2 : gpsCoord | 
		(g1.latitude=g2.latitude and g1.longitude=g2.longitude) iff g1=g2
}

//Two Locations have the same coords if and only are the same one
fact uniqueLocationUniqueCoords {
	all l1,l2 : Location | l1.coord=l2.coord iff l1=l2
}

//Two Zones has the same vertex and the same queue if and only are the same one
fact uniqueZoneUniqueQueue {
	all z1,z2 : Zone | (z1.vertex=z2.vertex or z1.queue=z2.queue) iff z1=z2
}

//Taxi code and license are unique values for taxi drivers
fact noDoubleTaxi {
	(no disj t1,t2 : TaxiDriver | t1.taxiCode=t2.taxiCode) and
	(no disj t1,t2 : TaxiDriver | t1.licenseNumber=t2.licenseNumber)
}

//A Driver is not in a Queue if and only is unavailable, else is available and in a queue
fact driverInQueue {
	all t : TaxiDriver | all q : TaxiQueue | (t in q.root.*next.taxi) iff (t.state=available)
}

//There is always at least a driver available in each queue
fact AtLeastADriver {
	all q : TaxiQueue | some t : TaxiDriver | t in q.root.*next.taxi
}

fact allNodesBelongToOneQueue {
	all n:QueueNode | one q:TaxiQueue | n in q.root.*next
}

//A driver cannot be the next one to himself
fact nextNotReflexive { 
	no n : QueueNode | n = n.next 
}

//The queue cannot be cyclic
fact nextNotCyclic { 
	no n:QueueNode | n in n.^next 
}

//Two drivers are in the same node if and only are the same one
fact singleNodeToSingleDriver {
	no disj n1, n2 : QueueNode | n1.taxi = n2.taxi
}

//Driver position is related to his current zone and queue
fact driverPosition{
 	all t : TaxiDriver | lone z : Zone| 
		t.state=available iff (t.position.zone=z and t.position.zone.queue=z.queue)
}

pred show{}
run show for 5 
