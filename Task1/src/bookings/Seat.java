package bookings;

public class Seat {

    //@ invariant row >= 'A';
    //@ invariant number >= 0;

    public static final char MIN_ROW = 'A';
    public static final char MAX_ROW = 'G';
    public static final int MIN_NUMBER = 1;
    public static final int MAX_NUMBER = 20;

    private final char row;
    private final int number;
    
    //@ requires row >= 'A';
    //@ requires number >= 0;
    public Seat(char row, int number) {
        this.row = row;
        this.number = number;
    }

    //@ ensures \result >= 'A';
    public final char getRow() {
        return row;
    }

    //@ ensures \result >= 0;
    public final int getNumber() {
        return number;
    }

}
