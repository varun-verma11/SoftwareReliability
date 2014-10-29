package bookings;

public class SeatReservationDemo {

    public static void main(String[] args) throws ReservationException {
      SeatReservationManager m = new SeatReservationManager();
      m.reserve(new Seat('A', 5), new Customer());
      m.reserve(new Seat('D', 14), new Customer());
      m.reserve(new Seat('G', 11), new Customer());
    }
    
}
