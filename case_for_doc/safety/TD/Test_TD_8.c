void func1(void* socket) {
     char manager[10];
     int result;
     fgets(manager, sizeof(manager), socket);

     if ( ( rc = ldap_search_ext_s( ld, FIND_DN, LDAP_SCOPE_BASE,
       manager, 0, 0, 0, 0, LDAP_NO_LIMIT,
       LDAP_NO_LIMIT, &result ) ) == 0 ) {
		int i;
		i = 0;
     }
}
