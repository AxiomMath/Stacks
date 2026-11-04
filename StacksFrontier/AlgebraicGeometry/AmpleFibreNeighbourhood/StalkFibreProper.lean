module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.StalkBaseChange

/-!
# The fibre subscheme over the local ring is proper over the residue field, and carries an
ample restriction

Continuing `StacksFrontier/AlgebraicGeometry/AmpleFibreNeighbourhood/StalkBaseChange.lean`: for
`f : X ⟶ S` and `y` a point of `S`, write `X' = X ×_S Spec 𝒪_{S, y}` and let `V ⊂ X'` be the
closed subscheme cut out by `𝔪 𝒪_{X'}`, which that file identifies with the fibre `X_y`.  The
two assertions of [Stacks, Tag 0D2M] over the local base `𝒪_{S, y}` ask for exactly three things
about `V` beyond the closed immersion itself: a morphism `V ⟶ Spec κ(y)` lying over `𝔪`, its
properness, and ampleness of the restriction of the invertible module.  This file supplies all
three.

## Main results

* `Stacks.AmpleFibreNeighbourhood.stalkFibreToResidueField`: the structure morphism
  `V ⟶ Spec κ(y)`, with `stalkFibreToResidueField_comp` the commutative square it sits in and
  `isProper_stalkFibreToResidueField` its properness.
* `Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_stalkFibre`: if `ℒ_y` is ample on the
  fibre `X_y`, then the restriction to `V` of the pullback of `ℒ` to `X'` is ample.

## The route

The morphism is the second projection of the presentation of `V` as `X' ×_{Spec 𝒪} Spec κ(y)`
(`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback`); the square is
`CategoryTheory.Limits.pullback.condition` read through
`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst`, and properness is
properness of `X' ⟶ Spec 𝒪_{S, y}` — itself a base change of `f` — carried along the same base
change and then composed with an isomorphism.

Ampleness is `Stacks.AmpleFibreNeighbourhood.stalkFibreIso_hom_fiberι`: the composite
`V ≅ X_y ⟶ X` is the closed immersion of `V` followed by `X' ⟶ X`, so the restriction of
`(X' ⟶ X)^* ℒ` to `V` is the pullback of `ℒ_y` along an isomorphism, ample by
`Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_comp_of_isIso`.

## No attribute

No `@[stacks]` attribute is attached: this is the data the local-base form of
[Stacks, Tag 0D2M] consumes, not the assertion of a numbered result.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.ClosedImmersion.IdealSheafAffine (quotHom quotRing)

universe u

namespace Stacks.AmpleFibreNeighbourhood

variable {X S : Scheme.{u}} (f : X ⟶ S) (A : Type u) [CommRing A] (I : Ideal A)
  (c : Spec (CommRingCat.of A) ⟶ S)

/-! ### The structure morphism of the fibre subscheme -/

/-- The presentation of the subscheme cut out by `I 𝒪` on `X ×_S Spec A` as the fibre product
`(X ×_S Spec A) ×_{Spec A} Spec(A ⧸ I)`, abbreviated.  This is
`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback` at the second projection. -/
abbrev baseFibrePullbackIso :
    (baseIdealSheaf A I (pullback.snd f c)).subscheme ≅
      Limits.pullback (pullback.snd f c)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback A I (pullback.snd f c)

/-- **The structure morphism `V ⟶ Spec(A ⧸ I)` of the subscheme of `X ×_S Spec A` cut out by
`I 𝒪`.** It is the second projection of the presentation of that subscheme as a fibre product
over `Spec A`. -/
def baseFibreToQuot :
    (baseIdealSheaf A I (pullback.snd f c)).subscheme ⟶ Spec (CommRingCat.of (A ⧸ I)) :=
  (baseFibrePullbackIso f A I c).hom ≫
    pullback.snd (pullback.snd f c) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- **The square the structure morphism sits in**: the closed immersion of the subscheme followed
by `X ×_S Spec A ⟶ Spec A` is the structure morphism followed by `Spec(A ⧸ I) ⟶ Spec A`.
This is the hypothesis `hsq` of the two assertions of [Stacks, Tag 0D2M] over a local base. -/
theorem baseFibreToQuot_comp :
    (baseIdealSheaf A I (pullback.snd f c)).subschemeι ≫ pullback.snd f c =
      baseFibreToQuot f A I c ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [baseFibreToQuot, Category.assoc, ← pullback.condition, ←
    Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst A I
      (pullback.snd f c), Category.assoc]

/-- **The structure morphism is proper** when `f` is: `X ×_S Spec A ⟶ Spec A` is a base change of
`f`, the structure morphism is a base change of that, and the presentation isomorphism is an
isomorphism. -/
instance isProper_baseFibreToQuot [IsProper f] : IsProper (baseFibreToQuot f A I c) := by
  rw [baseFibreToQuot]
  infer_instance

/-! ### Ampleness on the fibre subscheme, in general -/

/-- Ampleness of a pullback of `L` passes to any invertible module isomorphic to it. -/
private theorem isAmple_of_iso_pullbackModule {P Q : Scheme.{u}} (a : P ⟶ Q) (L : Q.Modules)
    [IsInvertibleModule Q L] (N : P.Modules) [IsInvertibleModule P N]
    (e : pullbackModule a L ≅ N) (h : IsAmple P (pullbackModule a L)) : IsAmple P N :=
  have : IsInvertibleModule P (pullbackModule a L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback a L
  (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp h

/-- **Ampleness of the restriction of the pullback of `ℒ` to the subscheme cut out by `I 𝒪`**,
from ampleness on the base change `X ×_S Spec(A ⧸ I)`.

`Stacks.AmpleFibreNeighbourhood.baseIdealSubschemeBaseChangeIso_hom_fst` says that the
presentation isomorphism followed by the first projection is the closed immersion followed by
`X ×_S Spec A ⟶ X`, so the two modules differ by a pullback along an isomorphism
(`Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_comp_of_isIso`) and a reassociation
(`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`). -/
theorem isAmple_pullbackModule_baseFibre (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (Limits.pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c))
      (pullbackModule
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c)) L)) :
    IsAmple (baseIdealSheaf A I (pullback.snd f c)).subscheme
      (pullbackModule (baseIdealSheaf A I (pullback.snd f c)).subschemeι
        (pullbackModule (pullback.fst f c) L)) := by
  have h1 : IsAmple (baseIdealSheaf A I (pullback.snd f c)).subscheme
      (pullbackModule ((baseIdealSubschemeBaseChangeIso f A I c).hom ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c)) L) :=
    isAmple_pullbackModule_comp_of_isIso (baseIdealSubschemeBaseChangeIso f A I c).hom _ L hL
  rw [baseIdealSubschemeBaseChangeIso_hom_fst] at h1
  exact isAmple_of_iso_pullbackModule _ L _
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
      (baseIdealSheaf A I (pullback.snd f c)).subschemeι (pullback.fst f c) L) h1

/-! ### Ampleness on the fibre of `f` at `y` -/

variable (y : S)

/-- **If `ℒ_y` is ample on the fibre `X_y`, the restriction to the subscheme cut out by `𝔪 𝒪` of
the pullback of `ℒ` to `X ×_S Spec 𝒪_{S, y}` is ample.**

`Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_baseFibre` at `A = 𝒪_{S, y}`, `I = 𝔪`,
with its hypothesis supplied by transporting ampleness across
`CategoryTheory.Limits.pullback.congrHom` along
`Stacks.AmpleFibreNeighbourhood.specResidueFieldToSpecStalk_comp`: the base change of `f` along
`Spec κ(y) ⟶ Spec 𝒪_{S, y} ⟶ S` is the fibre `X_y`.

This is the hypothesis `hL` of the two assertions of [Stacks, Tag 0D2M] over a local base, and it
is exactly the hypothesis of [Stacks, Tag 0D2N] on the fibre. -/
theorem isAmple_pullbackModule_stalkFibre (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    IsAmple (stalkBaseChangeFibreIdeal f y).subscheme
      (pullbackModule (stalkBaseChangeFibreIdeal f y).subschemeι
        (pullbackModule (pullback.fst f (S.fromSpecStalk y)) L)) := by
  refine isAmple_pullbackModule_baseFibre f ↥(S.presheaf.stalk y)
    (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y)) (S.fromSpecStalk y) L ?_
  have h1 := isAmple_pullbackModule_comp_of_isIso
    (Limits.pullback.congrHom (f₁ := f) rfl (specResidueFieldToSpecStalk_comp S y)).hom
    (f.fiberι y) L hL
  exact isAmple_of_iso_pullbackModule _ L _
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
      (congrHom_hom_fst f (specResidueFieldToSpecStalk_comp S y)) L) h1

end Stacks.AmpleFibreNeighbourhood

end
