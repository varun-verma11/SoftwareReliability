package bookings;

import java.util.Random;

public class SeatReservationDemo {

	private static final Random r = new Random();
	
    public static void main(String[] args) throws ReservationException {
      for (int k = 0; k < 10; k++) {
        SeatReservationManager m = new SeatReservationManager();
        for (int i = 0; i < 50; i++) {
          try {
            m.reserve(getRandomSeat(), new Customer());
          } catch (ReservationException e) {};
        }

        for (int i = 0; i < 50; i++) {
          try {
            m.reserveNextFree(new Customer());
          } catch (ReservationException e) {};
        }

        for (int i = 0; i < 50; i++) {
          try {
            m.unreserve(getRandomSeat());
          } catch (ReservationException e) {};
        }

        System.out.println(m);
      }
    }
    
    private static Seat getRandomSeat() {
    	return new Seat(
    		(char)(Seat.MIN_ROW + r.nextInt(Seat.MAX_ROW - Seat.MIN_ROW + 1)),
    		Seat.MIN_NUMBER + r.nextInt(Seat.MAX_NUMBER - Seat.MIN_NUMBER + 1));
    }
}
