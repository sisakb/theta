int main()
{
	int i, j, *p, *q, **r, **s, **t;
	p = &i;
	r = &p;
	s = &q;
	*s = p;
	s = *r;
	t = r;
	/*
	int i, j, *p, *q, **r, **s; // 1
	p = &i;						// 2
	q = &j;						// 3
	r = &p;						// 4
	s = &q;						// 5
	*r = q;						// 6
	*s = *r;					// 7
	r = s;						// 8
	return (0);					// 9
	*/
}