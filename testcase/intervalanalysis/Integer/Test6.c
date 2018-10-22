	void test1(int r, int t) {
	  if ( (r==347) && (t>10 && t<1000) ) {
	    if (r != t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test2(int r, int t) {
	  if ( (r==347) && (t>10 && t<1000) ) {
	    if (r == t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test3(int r, int t) {
	  if ( (r==347) && (t>10 && t<1000) ) {
	    if (t != r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test4(int r, int t) {
	  if ( (r==347) && (t>10 && t<1000) ) {
	    if (t == r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test5(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r != t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test6(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r == t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test7(int r, int t, int c, int d) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( (d=t) >= (c=r) ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test8(int r, int t, int c) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( t >= (c=r) ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test9(int r, int t, int c) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( (c=t) >= r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test10(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( t >= r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test11(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( t > r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test12(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( t <= r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test13(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( t < r ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test14(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r >= t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test15(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r > t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test16(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r <= t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
	
	void test17(int r, int t) {
	  if ( (r < 10 || r > 100) && (t>10 && t<1000) ) {
	    if ( r < t ) {
	      r = r;
	    } else {
	      t = t;
	    }
	  } else {
	    t = t;
	  }
	  return;
	}
