module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigEtaleArrowAlgebraization
public import StacksFrontier.RingTheory.Rig.RigSmoothAlgEquiv

/-!
# Rig-smoothness and rig-étaleness of a morphism of completions, from one covering

This file continues `StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtale.lean`, in the
situation of Stacks 0GDB: `f : X' ⟶ X` a morphism of algebraic spaces over `S`, `T` a set of
points of `X`, `U ⊂ X` the open subspace with `|U| = |X| ∖ T` and `U' = f⁻¹U`.

There, the affine data of the source's proofs of **Stacks 0GDH** and **Stacks 0AR2** is asked
at every affine representable étale square over `f_{/T}`. Here it is asked where the source's
reduction produces it: on *one* affine étale covering of `X'_{/T'}` whose members lie over
charts of `X_{/T}`, in the shape of condition (3) of Stacks 0GCQ, respectively condition (4)
of Stacks 0GCZ. The passage to every square is then the descent (3) ⟹ (1) of Stacks 0GCQ,
respectively (4) ⟹ (1) of Stacks 0GCZ, which is performed rather than assumed; its three
inputs `hasc`, `hdesc` and `href` are hypotheses, as they are of the library's Stacks 0GCQ and
Stacks 0GCZ.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ChartSquareReducesToSmoothAwayFromOnCover` and
  `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutsideOnCover`: the algebraization
  datum of condition (8) of Stacks 0AKG — in its rig-smooth, respectively rig-étale, reading —
  asked on one covering. The witnesses are tied to each square by the identification of the
  square's ring with a completion, so neither predicate mentions the conclusion it yields.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap_onCover`: the statement of
  Stacks 0GDH from the datum on one covering, by the ring bridge
  `Rig.isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv` (part (1) of Stacks
  0GAK) followed by the descent of Stacks 0GCQ.
* `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_onCover`: the statement of
  Stacks 0AR2 from the datum on one covering, by the ring bridge
  `RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv` (part (1) of Stacks 0ALQ) followed by the
  descent of Stacks 0GCZ.
* `AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap_of_isEtale_onCover`: Stacks
  0GD0 applied to the latter.
* `AlgebraicGeometry.FormalSpace.completionOfFiniteTypeModification_onCover`: the arrow of
  Stacks 0AR5, with its rig-étaleness component from the datum on one covering.

## References

* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0GAK](https://stacks.math.columbia.edu/tag/0GAK)
* [Stacks Project, Tag 0GCQ](https://stacks.math.columbia.edu/tag/0GCQ)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GD0](https://stacks.math.columbia.edu/tag/0GD0)
* [Stacks Project, Tag 0GDB](https://stacks.math.columbia.edu/tag/0GDB)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The affine data, asked on one covering -/

/-- The affine data of the proof of **Stacks 0GDH**, asked on *one covering*: the rig-smooth
reading of condition (8) of **Stacks 0AKG** for the arrow presenting each square of an affine
étale covering of `X'_{/T'}` by charts lying over charts of `X_{/T}`.

Granted that `X` is locally Noetherian, `f` is locally of finite type and `U' → U` is smooth, it
produces an affine étale covering `{Uᵢ ⟶ X'_{/T'}}` in the sense of Definition 0AIM, and for
each member a factorization `Uᵢ ⟶ Vᵢ ⟶ X_{/T}` through an affine formal algebraic space
representable étale over `X_{/T}`, such that for every arrow `g : A → C` of `WAdm^{Noeth}`
presenting `Uᵢ ⟶ Vᵢ` there are an ideal of definition `I₀ ⊆ A`, a finite type `A`-algebra `C₀`
with `Spec C₀ → Spec A` smooth over `Spec A ∖ V(I₀)`, and an identification of `C` with the
`I₀`-adic completion `C₀^` compatible with `g` and the structure map of `C₀`.

This is `AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside` with
`Rig.IsEtaleOutside` replaced by `Rig.SmoothAwayFrom`, and it is the shape of condition (3) of
**Stacks 0GCQ** with rig-smoothness of the presenting arrow replaced by the algebraization datum
that yields it: what the source's reduction of Stacks 0GDH produces is exactly a covering, from
the four inputs recorded in the section "The structure of the two proofs" of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtale.lean`, and the
descent from it to every affine representable étale square is the implication (3) ⟹ (1) of
Stacks 0GCQ, which `AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap_onCover`
performs rather than assumes.

This predicate names *data*, and no part of it mentions the conclusion of
`AlgebraicGeometry.FormalSpace.isRigSmooth_completionSheafMap`; the passage from it to that
conclusion is the ring bridge
`Rig.isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv` followed by that descent.
In particular the witnesses are tied to the square: the identification `e` forces `C₀` to
algebraize that square's own `C`, so the trivial witnesses `A₀ = C₀ = PUnit`, `I₀ = ⊤` that
satisfied the formulation this library carried before the rig-smooth transport
`Rig.isRigSmooth_of_algEquiv` was available vacuously do not satisfy this one. That is checked
and not merely asserted, twice over: the predicate now opens by demanding an affine étale
covering, whose index type lives in `Type (u + 1)` and whose members are sheaves, so `PUnit` is
not a witness of the right kind at all; and at a square
`Rig.isEmpty_ringEquiv_adicCompletionObj_of_subsingleton` refutes the existence of `e` outright
for every subsingleton `C₀`, `PUnit` among them, whenever `C` is nontrivial.

The base of the datum is `A`, the presenting ring of the chart `Vᵢ` of `X_{/T}`, rather than the
coordinate ring `A₀` of the étale chart of `X` with `A = A₀^∧` that the source's reduction
produces it over. Moving the datum from `(A₀, I₀)` to `(A₀^∧, I₀A₀^∧)` is **Stacks 0GAM**,
`Rig.isRigSmooth_of_completedBaseChange`, applied to the completion map; asking for it already
base changed is the shape the ring bridge consumes.

This is the cover-shaped variant of
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToSmoothAwayFrom`: it asks for the affine
data on ONE affine étale covering rather than on every chart square, so it needs the étale
ascent, descent and refinement inputs to reach every square. -/
abbrev ChartSquareReducesToSmoothAwayFromOnCover (f : X' ⟶ X) (T : Set (Space.points B S hS X)) :
    Prop :=
  Space.IsLocallyNoetherian B S hS X →
    Space.IsLocallyOfFiniteType B S hS f →
      Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T) →
        ∃ (ι : Type (u + 1)) (U : ι → FppfSheaf B S hS)
            (a : ∀ i, U i ⟶
              Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T)),
          IsAffineEtaleCover B S hS U a ∧
            ∀ i, ∃ (V : FppfSheaf B S hS) (b : V ⟶ Space.completionSheaf B S hS X T)
              (t : U i ⟶ V),
              IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS b ∧
                a i ≫ Space.completionSheafMap B S hS f T = t ≫ b ∧
                ∀ (A C : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
                  [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C]
                  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
                  [IsNoetherianRing C],
                  TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
                  ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
                    (E : QuotientSystem B S hS C) (eU : U i ≅ formalSpectrum E)
                    (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
                    t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
                      ∃ (I₀ : Ideal A) (_ : TopologicalRing.IsIdealOfDefinition I₀)
                        (_ : Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom)
                        (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra A C₀)
                        (_ : Algebra.FiniteType A C₀)
                        (e : C ≃+* (Rig.adicCompletionObj I₀ (B := C₀)).carrier),
                        (∀ x : A, e (g.toRingHom x) =
                            algebraMap A (Rig.adicCompletionObj I₀ (B := C₀)).carrier x) ∧
                          Rig.SmoothAwayFrom A I₀ C₀

/-- The affine data of the proof of **Stacks 0AR2**, asked on *one covering*: condition (8) of
**Stacks 0AKG** for the arrow presenting each square of an affine étale covering of `X'_{/T'}`
by charts lying over charts of `X_{/T}`.

Granted that `X` is locally Noetherian, `f` is locally of finite type and `U' → U` is étale, it
produces an affine étale covering `{Uᵢ ⟶ X'_{/T'}}` in the sense of Definition 0AIM, and for
each member a factorization `Uᵢ ⟶ Vᵢ ⟶ X_{/T}` through an affine formal algebraic space
representable étale over `X_{/T}`, such that for every arrow `g : A → C` of `WAdm^{Noeth}`
presenting `Uᵢ ⟶ Vᵢ` there are an ideal of definition `I₀ ⊆ A`, a finite type `A`-algebra `C₀`
with `Spec C₀ → Spec A` étale over `Spec A ∖ V(I₀)`, and an identification of `C` with the
`I₀`-adic completion `C₀^` compatible with `g` and the structure map of `C₀`.

The shape is condition (4) of **Stacks 0GCZ** with rig-étaleness of the presenting arrow
replaced by the algebraization datum that yields it: what the source's reduction of Stacks 0AR2
produces is exactly a covering, from the four inputs recorded in the section "The structure of
the two proofs" of `StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtale.lean`, and
the descent from it to every affine representable étale square is the implication (4) ⟹ (1) of
Stacks 0GCZ, which
`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_onCover` performs rather than
assumes.

This predicate names *data*, and no part of it mentions the conclusion of
`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap`; the passage from it to that
conclusion is the ring bridge `RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv` followed by
that descent. In particular the witnesses are tied to the square: the identification `e` forces
`C₀` to algebraize that square's own `C`, so the trivial witnesses that satisfied the
formulation this library carried before Stacks 0ALQ (1) was available vacuously no longer do.

The base of the datum is `A`, the presenting ring of the chart `Vᵢ` of `X_{/T}`, rather than the
coordinate ring `A₀` of the étale chart of `X` with `A = A₀^∧` that the source's reduction
produces it over. Moving the datum from `(A₀, I₀)` to `(A₀^∧, I₀A₀^∧)` is **Stacks 0GB2**,
`Rig.isRigEtale_of_completedBaseChange`, applied to the completion map; asking for it already
base changed is the shape the ring bridge consumes.

This is the cover-shaped variant of
`AlgebraicGeometry.FormalSpace.ChartSquareReducesToIsEtaleOutside`: it asks for the affine
data on ONE affine étale covering rather than on every chart square, so it needs the étale
ascent, descent and refinement inputs to reach every square. -/
abbrev ChartSquareReducesToIsEtaleOutsideOnCover (f : X' ⟶ X) (T : Set (Space.points B S hS X)) :
    Prop :=
  Space.IsLocallyNoetherian B S hS X →
    Space.IsLocallyOfFiniteType B S hS f →
      Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T) →
        ∃ (ι : Type (u + 1)) (U : ι → FppfSheaf B S hS)
            (a : ∀ i, U i ⟶
              Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T)),
          IsAffineEtaleCover B S hS U a ∧
            ∀ i, ∃ (V : FppfSheaf B S hS) (b : V ⟶ Space.completionSheaf B S hS X T)
              (t : U i ⟶ V),
              IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS b ∧
                a i ≫ Space.completionSheafMap B S hS f T = t ≫ b ∧
                ∀ (A C : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
                  [IsLinearTopology A A] [IsNoetherianRing A] [CommRing C]
                  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
                  [IsNoetherianRing C],
                  TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
                  ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
                    (E : QuotientSystem B S hS C) (eU : U i ≅ formalSpectrum E)
                    (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
                    t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
                      ∃ (I₀ : Ideal A) (_ : TopologicalRing.IsIdealOfDefinition I₀)
                        (_ : Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom)
                        (C₀ : Type u) (_ : CommRing C₀) (_ : Algebra A C₀)
                        (_ : Algebra.FiniteType A C₀)
                        (e : C ≃+* (Rig.adicCompletionObj I₀ (B := C₀)).carrier),
                        (∀ x : A, e (g.toRingHom x) =
                            algebraMap A (Rig.adicCompletionObj I₀ (B := C₀)).carrier x) ∧
                          Rig.IsEtaleOutside I₀ C₀

/-! ### Stacks 0GDH and Stacks 0AR2, from one covering -/

variable {B S hS}

/-- The statement of **Stacks 0GDH**, conditional on `hred`: in the situation of Stacks 0GDB,
if `X` is locally Noetherian, `f` is locally of finite type and `U' → U` is smooth, then
`f_{/T}` is rig-smooth.

The tag is **not established** by this theorem, because none of its four remaining hypotheses
is carried by this library. But `hred` is no longer a restatement of the conclusion, and it is
now asked where the source's reduction produces it: it names only the rig-smooth reading of the
algebraization datum of condition (8) of Stacks 0AKG, on one affine étale covering of
`X'_{/T'}` whose members lie over charts of `X_{/T}`, with the witnesses tied to each square by
the identification it carries. The step from it to the conclusion is the ring bridge
`Rig.isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv` through part (1) of
Stacks 0GAK, which turns `hred` into condition (3) of Stacks 0GCQ, followed by the descent
(3) ⟹ (1) of that lemma, for which `hasc`, `hdesc` and `href` are the inputs. This is now
exactly the shape of `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_onCover`
for Stacks 0AR2. See the section "The structure of the two proofs" of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtale.lean`. -/
theorem isRigSmooth_completionSheafMap_onCover {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsm : Space.IsSmooth B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToSmoothAwayFromOnCover B S hS f T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic RingHom.IsRigSmoothArrow)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic RingHom.IsRigSmoothArrow)
    (href : HasEtaleRefinementOfSourceCover B S hS
      (Space.completionSheafMap B S hS f T)) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) := by
  obtain ⟨ι, U, a, hcover, hfac⟩ := hred hX hf hsm
  refine (isRigSmooth_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS _ _ _ hasc hdesc href
      ⟨ι, U, a, hcover, fun i ↦ ?_⟩)
  obtain ⟨V, b, t, hV, hb, hsq, hdatum⟩ := hfac i
  refine ⟨V, b, t, hV, hb, hsq, ?_⟩
  intro A C _ _ _ _ _ _ _ _ ⟨hAadic, _⟩ ⟨hCadic, _⟩ hA D E eU eV g hg _ _ _ _
  obtain ⟨I₀, hI₀, hft, C₀, _, _, _, e, he, hsmooth⟩ := hdatum A C hAadic hCadic hA D E eU eV g hg
  exact ⟨g.continuous, hft, I₀, hI₀,
    Rig.isRigSmooth_adicFiniteTypeAlgebra_of_smoothAwayFrom_of_ringEquiv g.toRingHom hft I₀ hI₀
      e he hsmooth⟩

/-- The statement of **Stacks 0AR2**, conditional on `hred`: in the situation of Stacks 0GDB,
if `X` is locally Noetherian, `f` is locally of finite type and `U' → U` is étale, then
`f_{/T}` is rig-étale.

The tag is **not established** by this theorem, because none of its four remaining hypotheses
is carried by this library. But `hred` is no longer a restatement of the conclusion, and it is
now asked where the source's reduction produces it: it names only the algebraization datum of
condition (8) of Stacks 0AKG, on one affine étale covering of `X'_{/T'}` whose members lie over
charts of `X_{/T}`, with the witnesses tied to each square by the identification it carries.
The step from it to the conclusion is the ring bridge
`RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv` through part (1) of Stacks 0ALQ, which
turns `hred` into condition (4) of Stacks 0GCZ, followed by the descent (4) ⟹ (1) of that
lemma, for which `hasc`, `hdesc` and `href` are the inputs. See the section "The structure of
the two proofs" of `StacksFrontier/AlgebraicGeometry/FormalSpace/CompletionRigEtale.lean`. -/
theorem isRigEtale_completionSheafMap_onCover {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToIsEtaleOutsideOnCover B S hS f T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : HasEtaleRefinementOfSourceCover B S hS
      (Space.completionSheafMap B S hS f T)) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) := by
  obtain ⟨ι, U, a, hcover, hfac⟩ := hred hX hf het
  refine (isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr
    (hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover B S hS _ _ _ hasc hdesc href
      ⟨ι, U, a, hcover, fun i ↦ ?_⟩)
  obtain ⟨V, b, t, hV, hb, hsq, hdatum⟩ := hfac i
  refine ⟨V, b, t, hV, hb, hsq, ?_⟩
  intro A C _ _ _ _ _ _ _ _ ⟨hAadic, _⟩ ⟨hCadic, _⟩ hA D E eU eV g hg _ _ _ _
  obtain ⟨I₀, hI₀, hft, C₀, _, _, _, e, he, hetale⟩ := hdatum A C hAadic hCadic hA D E eU eV g hg
  exact ⟨g.continuous,
    RingHom.isRigEtale_of_isEtaleOutside_of_ringEquiv g.toRingHom hft I₀ hI₀ e he hetale⟩

/-- **Stacks 0GD0** applied to the conditional statement of Stacks 0AR2 above: in the
situation of Stacks 0GDB, if `X` is locally Noetherian, `f` is locally of finite type and
`U' → U` is étale, then `f_{/T}` is rig-smooth.

Only Stacks 0GD0 is new here; the rig-étaleness it is applied to is the conclusion of
`AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_onCover`, so this statement too is
conditional on that theorem's `hred`, the algebraization datum on one covering, and on the
three locality inputs of Stacks 0GCZ it descends along. -/
theorem isRigSmooth_completionSheafMap_of_isEtale_onCover
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T))
    (hred : ChartSquareReducesToIsEtaleOutsideOnCover B S hS f T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : HasEtaleRefinementOfSourceCover B S hS
      (Space.completionSheafMap B S hS f T)) :
    IsRigSmooth B S hS (Space.completionSheafMap B S hS f T) :=
  isRigSmooth_of_isRigEtale B S hS _
    (isRigEtale_completionSheafMap_onCover f T hX hf het hred hasc hdesc href)

/-! ### Stacks 0AR5, the completion arrow, from one covering -/

section Completion

attribute [local instance] Space.pointTopology

/-- **Stacks 0AR5.** The arrow of the displayed equation: a morphism `f : X' ⟶ X` of algebraic
spaces over `S` which is locally of finite type and an isomorphism over `U` is sent to
`f_{/T} : X'_{/T'} ⟶ X_{/T}`, a rig-étale morphism with locally Noetherian source.

That `f_{/T}` is rig-étale is the conditional statement of Stacks 0AR2 above applied to
`U' ⟶ U`, which is an isomorphism — and hence étale — because `U'` is the fibre product of
`U` with `f`. The four hypotheses that statement is conditional on are forwarded, so the
rig-étaleness component of this arrow holds granted the algebraization datum on one covering
and the three locality inputs of Stacks 0GCZ. -/
def completionOfFiniteTypeModification_onCover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideOnCover B S hS M.obj.hom T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : HasEtaleRefinementOfSourceCover B S hS
      (Space.completionSheafMap B S hS M.obj.hom T)) :
    RigEtaleOverCompletion B S hS X T :=
  ⟨Over.mk (Space.completionSheafMap B S hS M.obj.hom T),
    h0AIZ hT M.obj.hom M.property.1.1,
    hnoeth hT hX M.obj.hom M.property.1.1 M.property.2,
    isRigEtale_completionSheafMap_onCover M.obj.hom T hX M.property.2
      (Space.isEtale_openComplementRestriction B S hS M.obj.hom T M.property.1.2) hred
      hasc hdesc href⟩

/-- The arrow of Stacks 0AR5 sends `f : X' ⟶ X` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. -/
theorem completionOfFiniteTypeModification_onCover_obj {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hX : Space.IsLocallyNoetherian B S hS X)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (h0AIZ : IsFormalAlgebraicSpaceCompletionSheaf B S hS X T)
    (hnoeth : IsLocallyNoetherianCompletionSheaf B S hS X T)
    (hred : ChartSquareReducesToIsEtaleOutsideOnCover B S hS M.obj.hom T)
    (hasc : ChartPropertyAscendsAlongAffineEtale B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : HasEtaleRefinementOfSourceCover B S hS
      (Space.completionSheafMap B S hS M.obj.hom T)) :
    (completionOfFiniteTypeModification_onCover T hT hX M h0AIZ hnoeth hred
        hasc hdesc href).obj =
      Over.mk (Space.completionSheafMap B S hS M.obj.hom T) :=
  rfl

end Completion

end AlgebraicGeometry.FormalSpace

end
