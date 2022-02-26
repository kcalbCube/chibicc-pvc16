
void main(void)
{
	*((unsigned short*)((void*)0x100us)) = 10us + 5us;
}

void _start(void)
{
	asm("mov %sp FFFFh");
	main();
	asm("mov %a [100h]");
}