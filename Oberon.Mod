MODULE Oberon; (*JG 6.9.90 / 23.9.93 / 13.8.94 / NW 14.4.2013 / 22.12.2013*)
  IMPORT Texts;

  VAR
    Log*: Texts.Text;
  (* Only logging remains, the rest is not needed *)
  PROCEDURE OpenLog*(T: Texts.Text);
  BEGIN Log := T
  END OpenLog;

BEGIN

END Oberon.