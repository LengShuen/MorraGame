'reach 0.1';

//enum declaration
const [ isFinger, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [ isGuess, ZEROG, ONEG, TWOG, THREEG, FOURG, FIVEG, SIXG, SEVENG, EIGHTG, NINEG, TENG ] = makeEnum(11);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

//winner
const winner = (fingerAlice, fingerBob, guessAlice, guessBob) => {
  if(guessAlice == guessBob )
  {
    const Goutcome = DRAW; //tie
    return Goutcome;
  } 
  else {
    if (guessAlice == (fingerAlice + fingerBob)){
      const Goutcome = A_WINS;
      return Goutcome;//Alice wins
    }
    else{
      if (guessBob == (fingerAlice + fingerBob)){
        const Goutcome = B_WINS;
        return Goutcome;//Bob wins
      }
      else {
        const Goutcome = DRAW; //tie
        return Goutcome;
      }
    }
  }
};

//assert for combination (WIN & DRAW)
assert(winner(ONE, TWO, THREEG, TWOG) == A_WINS);
assert(winner(ONE, ONE, ONEG, TWOG) == B_WINS);
assert(winner(ONE, ONE, TWOG, TWOG) == DRAW);
assert(winner(ONE, ONE, ONEG, ONEG) == DRAW);

//assert for all combination (WIN & DRAW)
forall(UInt, fingerAlice =>
  forall(UInt, fingerBob =>
    forall(UInt, guessAlice =>
      forall(UInt, guessBob =>
        assert(isOutcome(winner(fingerAlice, fingerBob, guessAlice, guessBob)))))))

//assert for all combination (DRAW-same guess)
forall(UInt, (fingerAlice) =>
  forall(UInt, (fingerBob) =>
    forall(UInt, (guessAB) =>
        assert(winner(fingerAlice, fingerBob, guessAB, guessAB) == DRAW))))

//player function
const Player = {
  ...hasRandom,
  getFinger: Fun([], UInt),
  getGuess: Fun([UInt], UInt),
  seeOutcome: Fun([UInt], Null),
  seeTotal: Fun([UInt], Null),
  informTimeout: Fun([], Null)
}

//main
export const main = Reach.App(() => {
  const Alice = Participant('Alice', {
    //specify Alice's interact interface here
    ...Player,
    wager: UInt,
    deadline: UInt,
  })
  const Bob = Participant('Bob', {
    ...Player,
    acceptWager: Fun([UInt], Null)
  })
  init()

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    })
  }
  Alice.only(() => {  
    const amount = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  })
  Alice.publish(amount, deadline)
  .pay(amount);
  commit();

  Bob.only(() => {  
    interact.acceptWager(amount);
  })
  Bob.pay(amount)
  .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
  
  //must be in consensus step
  var outcome = DRAW;
  invariant(balance() == 2*amount && isOutcome(outcome))  //cannot change through the body of the loop
  while(outcome == DRAW){
    Alice.only(() => {
      const _fingerAlice = interact.getFinger();
      const _guessAlice = interact.getGuess(_fingerAlice);
      const [_commitAlice, _saltAlice] = makeCommitment(interact, _fingerAlice);
      const commitAlice = declassify(_commitAlice);
      const [_commitGAlice, _saltGAlice] = makeCommitment(interact, _guessAlice)
      const commitGAlice = declassify(_commitGAlice);
    });
    commit();
    Alice.publish(commitAlice, commitGAlice)
    .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));

    commit();
    unknowable(Bob, Alice(_fingerAlice, _saltAlice));
    unknowable(Bob, Alice(_guessAlice, _saltGAlice));
    Bob.only(() => {
      const fingerBob = declassify(interact.getFinger())
      const guessBob = declassify(interact.getGuess(fingerBob))
    })
    Bob.publish(fingerBob, guessBob)
    .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout))
    commit()

    Alice.only(() => {
      const [saltAlice, fingerAlice] = declassify([_saltAlice, _fingerAlice]);
      const [saltGAlice, guessAlice] = declassify([_saltGAlice, _guessAlice]);
    })

    Alice.publish(saltAlice, fingerAlice)
    .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    checkCommitment(commitAlice, saltAlice, fingerAlice);
    commit()
    
    Alice.publish(saltGAlice, guessAlice)
    .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    checkCommitment(commitGAlice, saltGAlice, guessAlice);
    commit()

    Alice.only(() => {
      const totalNumber = fingerAlice + fingerBob;
      interact.seeTotal(totalNumber);
    })
    
    Alice.publish(totalNumber)
    .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    
    outcome = winner(fingerAlice, fingerBob, guessAlice, guessBob);
    continue; //update variable and continue
  }
  assert(outcome == A_WINS || outcome == B_WINS);
  transfer(2*amount).to(outcome == A_WINS ? Alice : Bob);
  commit();

  each([Alice, Bob], () => {
      interact.seeOutcome(outcome);
  })
});
