package bookings;

public class SeatReservationManager {
    
    //@ non_null
    //@ invariant \nonnullelements(seatReservations)
    private final Customer[][] seatReservations;
    
    public SeatReservationManager() {
        seatReservations = new Customer[rowToIndex(Seat.MAX_ROW) + 1]
                                       [numberToIndex(Seat.MAX_NUMBER) + 1];
    }

    public boolean isReserved(/*@ non_null @*/Seat s) {
        return seatReservations[rowToIndex(s.getRow())]
                               [numberToIndex(s.getNumber())] != null;
    }

    public void reserve(/*@ non_null @*/Seat s, /*@ non_null @*/ Customer c) 
            throws ReservationException {
        if(isReserved(s)) {
            throw new ReservationException();
        }
        seatReservations[rowToIndex(s.getRow())]
                        [numberToIndex(s.getNumber())] = c;
    }
    
    public void unreserve(/*@ non_null @*/Seat s)
            throws ReservationException {
        if(!isReserved(s)) {
            throw new ReservationException();
              
        }
        seatReservations[rowToIndex(s.getRow())]
                        [numberToIndex(s.getNumber())] = null;
    }

    public void reserveNextFree(/*@non_null@*/Customer c) throws ReservationException {
        for(int rowIndex = 0; rowIndex < seatReservations.length; rowIndex++) {
            for(int numberIndex = 0; 
                    numberIndex < seatReservations[rowIndex].length; 
                    numberIndex++) {
                Seat current = new Seat(indexToRow(rowIndex), 
                    indexToNumber(numberIndex));
                if(!isReserved(current)) {
                    reserve(current, c);
                    return;
                }
            }
        }
        throw new ReservationException();
    }
    
    /*@ ghost String toStringResult; in privateState;
        represents theString <- toStringResult;
    @*/
 
    public String toString() {

        String result = " ";
        
        for(int numberIndex = 0; numberIndex < seatReservations[0].length; 
                numberIndex++) {
            result += " " + indexToNumber(numberIndex);
        }
        result += "\n";

        for(int rowIndex = 0;
            rowIndex < seatReservations.length;
            rowIndex++) {
            result += indexToRow(rowIndex);
            for(int numberIndex = 0; numberIndex < 
                    seatReservations[rowIndex].length; numberIndex++) {
                for(int j = numberIndex; j >= 10; j /= 10) {
                    result += " ";
                }
                result += " " + (isReserved(new Seat(indexToRow(rowIndex), 
                    indexToNumber(numberIndex))) ? "X" : " ");
            }
            result += "\n";
        }
        
        //@ set toStringResult = result;
        return result;
    }

    /*@ requires row >= Seat.MIN_ROW;
        ensures \result >= 0;
    @*/
    private static int rowToIndex(char row) {
        return row - Seat.MIN_ROW;
    }

    /*@ requires number >= Seat.MIN_NUMBER;
        ensures \result >= 0;
    @*/
    private static int numberToIndex(int number) {
        return number - Seat.MIN_NUMBER;
    }
    
    private static char indexToRow(int index) {
        return (char)(Seat.MIN_ROW + index);
    }

    private static int indexToNumber(int index) {
        return index + Seat.MIN_NUMBER;
    }
    
}
