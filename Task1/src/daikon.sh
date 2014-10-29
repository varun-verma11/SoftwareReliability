source /vol/lab/cs4/SoftwareReliability/coursework1.sh
javac bookings/*.java
java daikon.Chicory bookings.SeatReservationDemo
java daikon.Daikon SeatReservationDemo.dtrace.gz
