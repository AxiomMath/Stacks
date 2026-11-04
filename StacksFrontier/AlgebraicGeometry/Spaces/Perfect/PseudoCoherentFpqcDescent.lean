module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings
import StacksCore.Tactic.StacksAttribute

/-!
# `m`-pseudo-coherence descends along an fpqc covering of algebraic spaces

Let `{f_i : X_i ⟶ X}` be an fpqc covering of algebraic spaces over a scheme `S`, let `E` be an
object of `D_QCoh(𝒪_X)` and let `m` be an integer. Stacks 0DL1 says that `E` is
`m`-pseudo-coherent if and only if every derived pullback `Lf_i^*E` is.

`m`-pseudo-coherence is read on the small étale ringed site of Stacks 04KH, where it is
`AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` of Stacks 08FT part (3), and `Lf_i^*` is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, the derived pullback of Stacks 06YY
along the morphism of small étale ringed topoi of Stacks 03G8.

## The argument and what it rests on

The source reduces the covering to one whose members have *scheme* sources, and then quotes the
case of schemes. That reduction is what is proved here: Stacks 0419 refines the given covering
by morphisms `e_i : T_i ⟶ X_i` out of schemes of the site so that `{e_i ≫ f_i}` is again an
fpqc covering, the derived pullback along `e_i ≫ f_i` is the composite of the two derived
pullbacks, and pullback preserves `m`-pseudo-coherence, so the hypothesis on the `Lf_i^*E`
transfers to the refined family, where the case of schemes applies. The forward implication is
pullback preservation alone, with no hypothesis on the morphisms.

Three inputs of that argument are not available in this development and are carried as named
hypotheses, each a `Prop` in the shape of
`AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks`, the existence premise for
`Lf^*` itself:

* `AlgebraicGeometry.Space.DerivedPullbackPreservesPseudoCoherence` is Stacks 08H4 for a
  morphism of algebraic spaces. The library's form,
  `AlgebraicGeometry.RingedSite.Hom.isPseudoCoherentFrom_derivedPullback`, is stated for an
  `AlgebraicGeometry.RingedSite.Hom`, which carries a functor between the underlying sites, and
  at `AlgebraicGeometry.RingedSite.{0, 0, 0}`. The small étale site of an algebraic space is
  `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, and a morphism of algebraic spaces induces no
  functor between small étale sites, because the base change of an étale scheme chart of the
  target is an algebraic space and not a scheme. Both obstructions are the ones recorded in
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModulePullback.lean`.
* `AlgebraicGeometry.Space.HasDerivedModulePullbackCompIso` is Stacks 0D6D for the small étale
  ringed topoi. The library's composition isomorphism also presents a morphism of ringed topoi by
  a functor of the underlying sites, and
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries no such presentation; this is the
  obstruction already recorded for `AlgebraicGeometry.Space.BottomRankStratum.BottomRankBaseChange`.
* `AlgebraicGeometry.Space.FpqcDescentOfPseudoCoherenceOnSchemes` is the descent clause for a
  covering whose members have scheme sources — the "case for schemes" the source quotes. Its
  scheme-level content, `Stacks 09UE`, is formalized as
  `Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentFrom_iff_forall_fpqc`, but
  carrying it across needs the equivalence of Stacks 071Q between `D_QCoh` of the Zariski and
  of the small étale site and the agreement of the two resulting notions of pseudo-coherence,
  neither of which this development has for the small étale site of a scheme viewed inside the
  site of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_forall_fpqcCovering`: **Stacks 0DL1.**

## References

* [Stacks Project, Lemma 76.54.1 (0DL1)](https://stacks.math.columbia.edu/tag/0DL1)
* [Stacks Project, Lemma 36.12.4 (09UE)](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Lemma 21.45.3 (08H4)](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Lemma 73.9.5 (0419)](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Lemma 75.4.2 (071Q)](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Definition 20.47.1 (08FT)](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Section 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Lemma 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs carried as hypotheses -/

/-- **Stacks 08H4 for a morphism of algebraic spaces.** Derived pullback carries an
`m`-pseudo-coherent object of `D(𝒪_Y)` to an `m`-pseudo-coherent object of `D(𝒪_X)`.

This is the forward implication of Stacks 0DL1, and it asks nothing of the morphism. -/
def DerivedPullbackPreservesPseudoCoherence
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS) : Prop :=
  ∀ {Z W : AlgebraicSpaces B S hS} (g : Z ⟶ W)
      (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (m : ℤ),
    (smallEtaleRingedSite B S hS W.1 W.2).IsPseudoCoherentFrom E m →
      haveI := hL g
      (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherentFrom
        ((smallEtaleDerivedModulePullback B S hS g).obj E) m

/-- **Stacks 0D6D for the small étale ringed topoi of algebraic spaces.** The derived pullback
along a composite `a ≫ b` of morphisms of algebraic spaces is the composite of the derived
pullbacks along `b` and along `a`. -/
def HasDerivedModulePullbackCompIso
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS) : Prop :=
  ∀ {Z W V : AlgebraicSpaces B S hS} (a : Z ⟶ W) (b : W ⟶ V)
      (E : DerivedCategory (Modules.{u, u} B S hS V.1 V.2)),
    haveI := hL (a ≫ b)
    haveI := hL a
    haveI := hL b
    Nonempty ((smallEtaleDerivedModulePullback B S hS (a ≫ b)).obj E ≅
      (smallEtaleDerivedModulePullback B S hS a).obj
        ((smallEtaleDerivedModulePullback B S hS b).obj E))

/-- **The descent clause of Stacks 0DL1 for a covering whose members have scheme sources**, the
"case for schemes" the source quotes: if `{g_i : T_i ⟶ X}` is an fpqc covering of algebraic
spaces in which every `T_i` is the representable algebraic space of a scheme of the site, and
every `Lg_i^*E` is `m`-pseudo-coherent, then an object `E` of `D_QCoh(𝒪_X)` is
`m`-pseudo-coherent. -/
def FpqcDescentOfPseudoCoherenceOnSchemes
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS) : Prop :=
  ∀ {I : Type v} {X : AlgebraicSpaces B S hS} {T : I → AlgebraicSpaces B S hS}
      (g : ∀ i, T i ⟶ X),
    (∀ i, ∃ Z : BigFppfOver B S hS, Nonempty ((T i).obj ≅ yoneda.obj Z)) →
      IsFpqcCovering B S hS (fun i => (g i).hom) →
      ∀ (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ),
        (∀ n : ℤ, ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS X.1 X.2) n).obj E).IsQuasicoherentOnSite) →
        (∀ i, haveI := hL (g i)
          (smallEtaleRingedSite B S hS (T i).1 (T i).2).IsPseudoCoherentFrom
            ((smallEtaleDerivedModulePullback B S hS (g i)).obj E) m) →
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m

/-! ### Stacks 0DL1 -/

/-- `m`-pseudo-coherence on the small étale ringed site of an algebraic space transports along
an isomorphism of `D(𝒪_X)`: the witnessing `m`-pseudo-coherent complex is unchanged and its
comparison isomorphism is composed with the given one. -/
private theorem isPseudoCoherentFrom_transport {X : AlgebraicSpaces B S hS}
    {E E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (m : ℤ)
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) (ε : E ≅ E') :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E' m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := h
  exact ⟨K, hK, ⟨eK ≪≫ ε⟩⟩

/-- **Stacks 0DL1.** Let `{f_i : X_i ⟶ X}` be an fpqc covering of algebraic spaces over a
scheme `S`, let `E` be an object of `D_QCoh(𝒪_X)` and let `m` be an integer. Then `E` is
`m`-pseudo-coherent if and only if every derived pullback `Lf_i^*E` is.

The forward implication is pullback preservation of `m`-pseudo-coherence. For the converse,
Stacks 0419 refines the covering by morphisms `e_i : T_i ⟶ X_i` out of schemes of the site with
`{e_i ≫ f_i}` again an fpqc covering; the derived pullback along `e_i ≫ f_i` is `Le_i^*` of
`Lf_i^*E`, which is `m`-pseudo-coherent by pullback preservation, and the refined covering has
scheme sources, so the case of schemes applies. -/
@[stacks 0DL1 "carries 08H4 for spaces, the 0D6D comparison and the scheme case as hypotheses"]
theorem isPseudoCoherentFrom_iff_forall_fpqcCovering
    (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
    (hpull : DerivedPullbackPreservesPseudoCoherence B S hS hL)
    (hcomp : HasDerivedModulePullbackCompIso B S hS hL)
    (hschemes : FpqcDescentOfPseudoCoherenceOnSchemes.{u, v} B S hS hL)
    {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) n).obj E).IsQuasicoherentOnSite)
    (m : ℤ) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m ↔
      ∀ i, haveI := hL (f i)
        (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).IsPseudoCoherentFrom
          ((smallEtaleDerivedModulePullback B S hS (f i)).obj E) m := by
  refine ⟨fun h i => hpull (f i) E m h, fun h => ?_⟩
  obtain ⟨Z, e, -, hcov⟩ := exists_fpqc_scheme_refinement B S hS X.2 (fun i => (Xi i).2)
    (fun i => (f i).hom) hf
  set T : I → AlgebraicSpaces B S hS :=
    fun i => ⟨yoneda.obj (Z i), isAlgebraicSpace_yoneda B S hS (Z i)⟩
  set g : ∀ i, T i ⟶ X := fun i => ObjectProperty.homMk (e i) ≫ f i
  refine hschemes g (fun i => ⟨Z i, ⟨Iso.refl _⟩⟩) hcov E m hE fun i => ?_
  obtain ⟨ε⟩ := hcomp (ObjectProperty.homMk (e i) : T i ⟶ Xi i) (f i) E
  exact isPseudoCoherentFrom_transport B S hS m
    (hpull (ObjectProperty.homMk (e i) : T i ⟶ Xi i) _ m (h i)) ε.symm

end AlgebraicGeometry.Space

end
