module MyDatatypes {
    datatype Maybe<T> = Error(string) | Just(value : T)
}