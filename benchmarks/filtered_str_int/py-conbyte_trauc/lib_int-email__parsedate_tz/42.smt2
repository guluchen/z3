(declare-fun data () String)


(assert (not ( or ( or ( or ( or ( or ( or ( = "mon" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  ) ( = "tue" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  ) ( = "wed" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  ) ( = "thu" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  ) ( = "fri" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  ) ( = "sat" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  ) ( = "sun" "\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"  )  )))

(assert (not ( str.suffixof "," ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  )  )))

(assert (not ( = ( str.len data  ) 0  )))
(assert ( >= ( str.indexof ( str.substr data 0 ( - ( str.indexof data " " 0  ) 0  )  ) "," 0  ) 0  ))


(check-sat)


(get-value (data))