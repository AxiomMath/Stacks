module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafAffine
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of the base change to the local ring of the base

Let `f : X ⟶ S` be a morphism of schemes and `y` a point of `S`.  The proof of
[Stacks, Tag 0D2M] — and through it of [Stacks, Tag 0D2N] — replaces `S` by `Spec 𝒪_{S, y}`,
over which the closed point's fibre is cut out by the maximal ideal.  This file assembles the
two identifications that reduction needs:

* the closed subscheme of `X ×_S Spec A` cut out by `I 𝒪` is `X ×_S Spec(A ⧸ I)`, for any ring
  `A` mapping to `S` and any ideal `I` of it;
* at `A = 𝒪_{S, y}` and `I = 𝔪`, that subscheme is the **fibre `X_y` of `f` at `y`**, because
  `Spec κ(y) ⟶ Spec 𝒪_{S, y} ⟶ S` is the canonical `Spec κ(y) ⟶ S`.

Both come with their compatibility with the two closed immersions into `X`, which is what makes
them usable: a statement about the subscheme becomes a statement about `X_y` only together with
the identification of `v` with `X_y ⟶ X`.

## Main results

* `Stacks.AmpleFibreNeighbourhood.specResidueFieldToSpecStalk_comp`: the composite
  `Spec κ(y) ⟶ Spec 𝒪_{S, y} ⟶ S` is `AlgebraicGeometry.Scheme.fromSpecResidueField`.
* `Stacks.AmpleFibreNeighbourhood.baseIdealSubschemeBaseChangeIso` and
  `..._hom_fst`: the subscheme cut out by `I 𝒪` on `X ×_S Spec A` is `X ×_S Spec(A ⧸ I)`,
  compatibly with the maps to `X`.
* `Stacks.AmpleFibreNeighbourhood.stalkFibreIso` and `stalkFibreIso_hom_fiberι`: at the local
  ring of `S` at `y` and its maximal ideal, that subscheme **is** `X_y`, compatibly with
  `AlgebraicGeometry.Scheme.Hom.fiberι`.
* `Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_comp_of_isIso`: ampleness of a pullback
  is unchanged by precomposition with an isomorphism — the transport that carries ampleness of
  `ℒ_y` on `X_y` onto the subscheme.

## The route

`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback` identifies the subscheme cut out
by `I 𝒪` on a scheme over `Spec A` with the base change along `Spec(A ⧸ I) ⟶ Spec A`, and
`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst` records its compatibility
with the two closed immersions.  Applied on `X ×_S Spec A`, whose structure morphism to `Spec A`
is the second projection, it is followed by
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, which pastes the two cartesian squares into
one over `S`.  Specialising `A = 𝒪_{S, y}` and `I = 𝔪` and rewriting the base of the pasted
square by `specResidueFieldToSpecStalk_comp` — through
`CategoryTheory.Limits.pullback.congrHom`, since a `rewrite` would leave a `HasPullback` instance
in a motive that does not typecheck — gives the fibre.

The residue field of a scheme at a point is by definition the residue field of its local ring,
so `Spec κ(y)` and `Spec(𝒪_{S, y} ⧸ 𝔪)` are the same scheme and `Spec.map` of the quotient map is
`Spec.map` of `AlgebraicGeometry.Scheme.residue`; that is why
`specResidueFieldToSpecStalk_comp` is proved by `simp` after one `show`.

## No attribute

No `@[stacks]` attribute is attached: these are transports between two presentations of one
fibre, not the assertion of a numbered result.

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

/-! ### `Spec κ(y) ⟶ Spec 𝒪_{S,y} ⟶ S` -/

/-- **The closed point of `Spec 𝒪_{S, y}` followed by the canonical morphism to `S` is the
canonical morphism `Spec κ(y) ⟶ S`.**

The residue field `S.residueField y` is by definition `𝒪_{S, y} ⧸ 𝔪`, so
`Stacks.ClosedImmersion.IdealSheafAffine.quotHom 𝔪` is `AlgebraicGeometry.Scheme.residue y`, and
`AlgebraicGeometry.Scheme.fromSpecResidueField` is `Spec.map` of that followed by
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
theorem specResidueFieldToSpecStalk_comp (S : Scheme.{u}) (y : S) :
    Spec.map (quotHom (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y))) ≫ S.fromSpecStalk y =
      S.fromSpecResidueField y := by
  change Spec.map (S.residue y) ≫ S.fromSpecStalk y = _
  simp [AlgebraicGeometry.Scheme.fromSpecResidueField]

/-! ### The subscheme cut out by `I 𝒪` on a base change -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (A : Type u) [CommRing A] (I : Ideal A)
  (c : Spec (CommRingCat.of A) ⟶ S)

/-- **The closed subscheme of `X ×_S Spec A` cut out by `I 𝒪` is `X ×_S Spec(A ⧸ I)`.**

`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback` presents it as the base change of
`Spec(A ⧸ I) ⟶ Spec A` along the second projection, and
`CategoryTheory.Limits.pullbackLeftPullbackSndIso` pastes that square onto the defining one. -/
@[ega "IV 11.3.4" "(iv), special case"]
def baseIdealSubschemeBaseChangeIso :
    (baseIdealSheaf A I (pullback.snd f c)).subscheme ≅
      Limits.pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c) :=
  Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback A I (pullback.snd f c) ≪≫
    pullbackLeftPullbackSndIso f c (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- `Stacks.AmpleFibreNeighbourhood.baseIdealSubschemeBaseChangeIso` is compatible with the two
morphisms to `X`. -/
theorem baseIdealSubschemeBaseChangeIso_hom_fst :
    (baseIdealSubschemeBaseChangeIso f A I c).hom ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c) =
      (baseIdealSheaf A I (pullback.snd f c)).subschemeι ≫ pullback.fst f c := by
  simp only [baseIdealSubschemeBaseChangeIso, Iso.trans_hom, Category.assoc]
  rw [show (pullbackLeftPullbackSndIso f c
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).hom ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ c) =
      pullback.fst (pullback.snd f c) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
        pullback.fst f c from by simp, ← Category.assoc,
    Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback_hom_fst]

/-- The compatibility of `CategoryTheory.Limits.pullback.congrHom` with the first projection,
which `rewrite` cannot supply because the `HasPullback` instance sits in the motive. -/
theorem congrHom_hom_fst {C : Type*} [Category C] {P Q Z : C} (a : P ⟶ Z) {b b' : Q ⟶ Z}
    (h : b = b') [HasPullback a b] [HasPullback a b'] :
    (Limits.pullback.congrHom (f₁ := a) rfl h).hom ≫ pullback.fst a b' = pullback.fst a b := by
  simp only [pullback.congrHom, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

/-! ### At the local ring of `S` at `y`: the subscheme is the fibre -/

variable (y : S)

/-- The ideal sheaf `𝔪 𝒪` on the base change `X ×_S Spec 𝒪_{S, y}`. -/
abbrev stalkBaseChangeFibreIdeal :
    (Limits.pullback f (S.fromSpecStalk y)).IdealSheafData :=
  baseIdealSheaf ↥(S.presheaf.stalk y) (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y))
    (pullback.snd f (S.fromSpecStalk y))

/-- **The closed subscheme of `X ×_S Spec 𝒪_{S, y}` cut out by `𝔪 𝒪` is the fibre `X_y`.**

`Stacks.AmpleFibreNeighbourhood.baseIdealSubschemeBaseChangeIso` presents it as
`X ×_S Spec κ(y)` for the base `Spec κ(y) ⟶ Spec 𝒪_{S, y} ⟶ S`, and
`Stacks.AmpleFibreNeighbourhood.specResidueFieldToSpecStalk_comp` identifies that composite with
`AlgebraicGeometry.Scheme.fromSpecResidueField`, whose base change is by definition
`AlgebraicGeometry.Scheme.Hom.fiber`. -/
def stalkFibreIso : (stalkBaseChangeFibreIdeal f y).subscheme ≅ f.fiber y :=
  baseIdealSubschemeBaseChangeIso f ↥(S.presheaf.stalk y)
      (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y)) (S.fromSpecStalk y) ≪≫
    Limits.pullback.congrHom rfl (specResidueFieldToSpecStalk_comp S y)

/-- `Stacks.AmpleFibreNeighbourhood.stalkFibreIso` carries the inclusion of the fibre into `X` to
the closed immersion of the subscheme followed by the first projection. -/
theorem stalkFibreIso_hom_fiberι :
    (stalkFibreIso f y).hom ≫ f.fiberι y =
      (stalkBaseChangeFibreIdeal f y).subschemeι ≫ pullback.fst f (S.fromSpecStalk y) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (baseIdealSubschemeBaseChangeIso f ↥(S.presheaf.stalk y)
          (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y)) (S.fromSpecStalk y)).hom ≫ t)
        (congrHom_hom_fst f (specResidueFieldToSpecStalk_comp S y))).trans
      (baseIdealSubschemeBaseChangeIso_hom_fst f ↥(S.presheaf.stalk y)
        (IsLocalRing.maximalIdeal ↥(S.presheaf.stalk y)) (S.fromSpecStalk y)))

/-! ### Ampleness across an isomorphism of the source -/

/-- **Ampleness of a pullback is unchanged by precomposition with an isomorphism.**
[Stacks, Tag 0B3E] for an isomorphism (`Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso`)
followed by the reassociation `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`. -/
theorem isAmple_pullbackModule_comp_of_isIso {P Q R : Scheme.{u}} (a : P ⟶ Q) [IsIso a]
    (b : Q ⟶ R) (N : R.Modules) [IsInvertibleModule R N]
    (h : IsAmple Q (pullbackModule b N)) :
    IsAmple P (pullbackModule (a ≫ b) N) :=
  have : IsInvertibleModule Q (pullbackModule b N) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback b N
  (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso a b N)).mpr
    (Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso a _ h)

end Stacks.AmpleFibreNeighbourhood

end
