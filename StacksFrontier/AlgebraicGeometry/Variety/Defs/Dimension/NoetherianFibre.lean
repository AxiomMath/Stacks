module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally Noetherian fibres after base change

If the fibres of a morphism of schemes are locally Noetherian, then their base changes along a
locally finite-type morphism are locally Noetherian. The relevant extension of residue fields is
finitely generated, and the new fibre is canonically the corresponding field base change of the
old fibre.

## Main definitions

* `AlgebraicGeometry.fiberPullbackIso` identifies a fibre after base change with the base change
  of the original fibre along the induced extension of residue fields.

## Main results

* `AlgebraicGeometry.residueField_essFiniteType_of_locallyOfFiniteType` says that the induced
  residue-field extension is finitely generated.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_pullback` says that the corresponding fibre of
  the base-changed morphism is locally Noetherian.

## Implementation notes

The base-changed morphism is represented by the second projection from Mathlib's chosen
pullback. A finitely generated extension of fields is expressed by `Algebra.EssFiniteType`. The
equality of the two models of the fibre is represented by a canonical scheme isomorphism.

## References

* [Stacks Project, *Duality for Schemes*, Lemma
  `base_changed_fibres_are_locally_noetherian`](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- The fibre of a base-changed morphism is canonically the base change of the original fibre
along the induced extension of residue fields. -/
def fiberPullbackIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (y' : Y') :
    (pullback.snd f g).fiber y' ≅
      pullback (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y')) :=
  (isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y').isoPullback

/-- A locally finite-type morphism induces a finitely generated extension of residue fields at
every point. -/
theorem residueField_essFiniteType_of_locallyOfFiniteType
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [LocallyOfFiniteType g] (y' : Y') :
    let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
      (g.residueFieldMap y').hom.toAlgebra
    Algebra.EssFiniteType (Y.residueField (g y')) (Y'.residueField y') := by
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  exact RingHom.essFiniteType_algebraMap.mp
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap g y'))

/-- The base change of a locally Noetherian scheme over a field along a finitely generated
field extension is locally Noetherian. -/
@[ega "IV 4.7.3" "(i)", ega "IV 6.7.1" "partial"]
private lemma isLocallyNoetherian_pullback_of_essFiniteType
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsLocallyNoetherian X] :
    IsLocallyNoetherian (pullback f (Spec.map (ofHom (algebraMap K L)))) := by
  let g := Spec.map (ofHom (algebraMap K L))
  rw [isLocallyNoetherian_iff_openCover
    (X.affineOpenCover.openCover.pullbackCoverOfLeft f g)]
  intro i
  have hg : affineAnd RingHom.EssFiniteType g := by
    dsimp [g]
    show IsAffine _ ∧ _
    refine ⟨inferInstance, ?_⟩
    apply (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff
      (arrowIsoΓSpecOfIsAffine (ofHom (algebraMap K L)))).mp
    show (algebraMap K L).EssFiniteType
    rw [RingHom.essFiniteType_algebraMap]
    infer_instance
  have hb : affineAnd RingHom.EssFiniteType
      (pullback.fst (X.affineOpenCover.f i ≫ f) g) :=
    (affineAnd_isStableUnderBaseChange RingHom.EssFiniteType.respectsIso
      RingHom.EssFiniteType.isStableUnderBaseChange) (.of_hasPullback _ _) hg
  have hright : IsLocallyNoetherian (pullback (X.affineOpenCover.f i ≫ f) g) := by
    have : IsAffine (pullback (X.affineOpenCover.f i ≫ f) g) := hb.1
    let := (pullback.fst (X.affineOpenCover.f i ≫ f) g).appTop.hom.toAlgebra
    let : Algebra.EssFiniteType Γ(Spec (X.affineOpenCover.X i), ⊤)
        Γ(pullback (X.affineOpenCover.f i ≫ f) g, ⊤) :=
      RingHom.essFiniteType_algebraMap.mp hb.2
    let : IsOpenImmersion (X.affineOpenCover.f i) :=
      X.affineOpenCover.map_prop i
    let : IsLocallyNoetherian (Spec (X.affineOpenCover.X i)) :=
      isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f i)
    have : IsNoetherianRing Γ(Spec (X.affineOpenCover.X i), ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    have : IsNoetherianRing Γ(pullback (X.affineOpenCover.f i ≫ f) g, ⊤) :=
      Algebra.EssFiniteType.isNoetherianRing Γ(Spec (X.affineOpenCover.X i), ⊤) _
    exact isLocallyNoetherian_of_affine_cover
      (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top _⟩) (by simp) fun _ ↦ inferInstance
  exact hright

/-- If every fibre of `f` is locally Noetherian and `g` is locally of finite type, then every
fibre of the base-changed morphism is locally Noetherian. -/
theorem isLocallyNoetherian_fiber_pullback {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType g]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (y' : Y') :
    IsLocallyNoetherian ((pullback.snd f g).fiber y') := by
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have : Algebra.EssFiniteType (Y.residueField (g y')) (Y'.residueField y') :=
    residueField_essFiniteType_of_locallyOfFiniteType g y'
  have hp : IsLocallyNoetherian
      (pullback (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y'))) := by
    let := hf (g y')
    have hp' := isLocallyNoetherian_pullback_of_essFiniteType
      (K := Y.residueField (g y')) (L := Y'.residueField y')
      (f.fiberToSpecResidueField (g y'))
    rw [RingHom.algebraMap_toAlgebra] at hp'
    have he : ofHom (g.residueFieldMap y').hom = g.residueFieldMap y' := by ext; rfl
    rw [he] at hp'
    exact hp'
  let := hp
  let e := fiberPullbackIso f g y'
  let : IsOpenImmersion e.hom := by dsimp [e]; infer_instance
  exact isLocallyNoetherian_of_isOpenImmersion e.hom

end AlgebraicGeometry

end
