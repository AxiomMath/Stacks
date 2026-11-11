module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageQcqs
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekPseudofunctor.Pseudofunctor
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDuality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryDivisor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryFinite
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryKoszul
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheoryProperDuality
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DualityTheorySmooth
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
import StacksCore.Tactic.StacksAttribute

/-!
# A duality theory

[Stacks, Section 0AU3] lists nine properties of the upper shriek functors `f^!` on `FTS_S`, the
schemes separated and of finite type over a Noetherian scheme `S`. Each is proved in the library,
with `f^!` the functor `Stacks.Duality.upperShriek f j` of [Stacks, Tag 0A9Y] at an arbitrary
compactification `j` (on `D⁺_QCoh` it does not depend on `j`, [Stacks, Tag 0AA0]), and each
carries `@[stacks 0AU3]` with the clause it states:

1. pseudofunctor on `FTS_S` with values `D⁺_QCoh`: `Stacks.Duality.exists_upperShriekPseudofunctor`
   ([Stacks, Tag 0ATY]);
2. `f` proper: `Stacks.Duality.upperShriek_rightAdjoint_and_duality_of_isProper`;
3. `D_X = R𝓗om(-, ω_X^•)` an involution of `D_Coh` exchanging `D⁺_Coh` and `D⁻_Coh` and fixing
   `D^b_Coh`: `Stacks.Duality.coherentDuality_spec` ([Stacks, Tag 0A89]), for any locally
   Noetherian scheme, the objects of `FTS_S` being Noetherian;
4. (a) `f^!ω_Y^•` is dualizing: `Stacks.Duality.isDualizingComplex_upperShriek_obj`
   ([Stacks, Tag 0AA3]); (b) `f^!M = D_X(Lf^*D_Y(M))`:
   `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso` ([Stacks, Tag 0AU2]); (c) `f` proper:
   `Stacks.Duality.sheafHomDualizingIsoOfIsProper`, registered through
   `Stacks.Duality.nonempty_sheafHomDualizingIsoOfIsProper`;
5. closed immersion: `Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts`
   ([Stacks, Tag 0AA2]);
6. finite morphism: `Stacks.Duality.nonempty_upperShriekFiniteIsoDerivedHomSheaf`;
7. effective Cartier divisor: `Stacks.Duality.isNormalTensorPullbackRightAdjoint_of_fts`;
8. Koszul-regular immersion: `Stacks.Duality.nonempty_upperShriekIsoPullbackTensorOfKoszulRegular`;
9. smooth proper morphism:
   `Stacks.Duality.nonempty_upperShriekIsoPullbackTensorOfSmoothOfIsProper`.

This file records the registrations of the clauses whose statement is that of a tag proved
elsewhere.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
-/

@[expose] public section

add_to_stacks 0AU3 "clause (1): the functors f^! of Tag 0AA0 on D^+_QCoh, with the canonical \
  isomorphisms (g o f)^! = f^! o g^! of Tag 0ATX, form a pseudofunctor on FTS_S (Tag 0ATY)"
  Stacks.Duality.exists_upperShriekPseudofunctor

add_to_stacks 0AU3 "clause (3): for a dualizing complex omega on a locally Noetherian scheme X \
  (in particular an object of FTS_S), D = RHom(-, omega) is an anti-equivalence of D_Coh(O_X) \
  with the canonical isomorphism id = D o D, exchanging D^+_Coh and D^-_Coh and inducing an \
  anti-equivalence of D^b_Coh when X is quasi-compact (Tag 0A89)"
  Stacks.Duality.coherentDuality_spec

add_to_stacks 0AU3 "clause (4)(a): for f : X to Y in FTS_S and omega_Y a dualizing complex on Y, \
  f^! omega_Y (at any compactification) is a dualizing complex on X (Tag 0AA3)"
  Stacks.Duality.isDualizingComplex_upperShriek_obj

add_to_stacks 0AU3 "clause (4)(b): for f : X to Y in FTS_S and K a dualizing complex on Y, \
  f^! M = D_X(Lf^* D_Y(M)) naturally in M in D^+_Coh(O_Y), D_Y = RHom(-, K), \
  D_X = RHom(-, f^! K) (Tag 0AU2)"
  Stacks.Duality.UpperShriekDuality.upperShriekDualityIso
