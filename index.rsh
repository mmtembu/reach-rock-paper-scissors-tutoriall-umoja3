'reach 0.1';
 
const [isHand, ROCK, PAPER, SCISSORS] = makeEnum(3);//Lines 3 and 4 define enumerations for the hands that may be played,
const [isOutcome, B_WINS, DRAW, A_WINS] = makeEnum(3);//as well as the outcomes of the game

const winner = (handAlice, handBob) => //Lines 6 and 7 define the function that computes the winner of the game.176
    ((handAlice + (4 - handBob)) % 3);
    
assert(winner(ROCK, PAPER) == B_WINS)
assert(winner(PAPER, ROCK) == A_WINS)
assert(winner(ROCK, ROCK) == DRAW)

forall(UInt, handAlice => 
    forall(UInt, handBob =>
        assert(isOutcome(winner(handAlice, handBob)))));

forall(UInt, (hand) =>
    assert(winner(hand, hand) == DRAW));

const Player = {
    ...hasRandom,
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {
    const Alice = Participant('Alice', {// 9 through 12 define Alice's interface as the Player interface, plus an integer value called wager
        ...Player,
        wager: UInt,  // atomic units of currency
        deadline: UInt, // time delta (blocks/rounds)
    });
    const Bob = Participant('Bob', {// 13 through 16 do the same for Bob, where he has a method called acceptWager that can look at the wager value
        ...Player,
        acceptWager: Fun([UInt], Null),
    });
    init();

    const informTimeout = () => {
        each([Alice, Bob], () => {
            interact.informTimeout();
        });
    };

    Alice.only(()=>{
        const wager = declassify(interact.wager);//Line 20 has Alice declassify the wager for transmission
        const deadline = declassify(interact.deadline);
    });
    Alice.publish(wager, deadline)//Line 23 is updated so that Alice shares the wager amount with Bob
    .pay(wager);//24 has her transfer the amount as part of her publication.The Reach compiler would throw an exception if wager did not appear on line 23, but did appear on line 24. Change the program and try it. This is because the consensus network needs to be able to verify that the amount of network tokens included in Alice's publication match some computation available to consensus network.
    commit();
    // unknowable(Bob, Alice(_handAlice,_saltAlice));
    Bob.only(() =>{
        interact.acceptWager(wager);
    });
    Bob.pay(wager)//Line 32 has Bob pay the wager as well
    .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));//Line 63 adds a timeout handler to Bob's publication.

    var outcome = DRAW;
    invariant( balance() == 2 * wager && isOutcome(outcome) );
    while( outcome == DRAW ){
        commit();

        Alice.only(()=>{//Lines 57 and 58 have Alice declassify the secret information
            const _handAlice = interact.getHand();
            const [_commitAlice, _saltAlice] = makeCommitment(interact, _handAlice);
            const commitAlice = declassify(_commitAlice);
        });
        Alice.publish(commitAlice)
        .timeout(relativeTime(deadline), ()=> closeTo(Bob, informTimeout));
        commit();

        unknowable(Bob, Alice(_handAlice, _saltAlice));
        Bob.only(()=>{
            const handBob = declassify(interact.getHand())
        })
        Bob.publish(handBob)
        .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
        commit();

        Alice.only(()=>{//Lines 57 and 58 have Alice declassify the secret information
            const saltAlice = declassify(_saltAlice);
            const handAlice = declassify(_handAlice);
        });
        Alice.publish(saltAlice, handAlice)
        .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
        checkCommitment(commitAlice, saltAlice, handAlice);//Line 61 checks that the published values match the original values

        outcome = winner(handAlice, handBob);// assert(outcome == 0);//conducts proof by including an assert statement in the program
        continue;   
    }

    assert(outcome == A_WINS || outcome == B_WINS);
    transfer(2 * wager).to(outcome == A_WINS ? Alice : Bob);
    commit();
    
    // const               [forAlice, forBob] = 
    //     outcome == A_WINS ?  [       2,      0] :
    //     outcome == B_WINS ?  [       0,      2] :
    //                          [       1,      1];
    //     transfer(forAlice * wager).to(Alice);
    //     transfer(forBob * wager).to(Bob);
    //     commit();
    
    each([Alice, Bob], ()=>{
        interact.seeOutcome(outcome);
    });
})