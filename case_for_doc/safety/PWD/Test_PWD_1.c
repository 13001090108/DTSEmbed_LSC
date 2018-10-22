#include <stdlib.h>
#include <stdio.h>
#include <mysql.h>

int main(int argc, char *argv[])
{
    int res;
    MYSQL connection;

    mysql_init(&connection);
    if(mysql_real_connect(&connection, "localhost", "root", "pwd", "test", 0, NULL, 0))
    {
        printf("Connection success\n");

        res = mysql_query(&connection, "INSERT INTO children(fname, age) VALUES('ann', 3)");

        if(!res)
        {
            printf("Inserted %lu rows\n", (unsigned long)mysql_affected_rows(&connection)); //打印受影响的行数
        }
        else
        {
            fprintf(stderr, "Insert error %d: %s\n", mysql_errno(&connection), mysql_error(&connection));
        }

        mysql_close(&connection);
    }
    else
    {
        fprintf(stderr, "Connection failed\n");
        if(mysql_errno(&connection))
        {
            fprintf(stderr, "Connection error %d: %s\n", mysql_errno(&connection), mysql_error(&connection));
        }
    }

    return EXIT_SUCCESS;
}
