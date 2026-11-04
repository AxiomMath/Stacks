module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeAffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PushforwardUnitBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08IB] over an affine base: the base-change map read as a map of tensor products

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and `S`, `S'`
affine, and let `K` be a complex on `X` with quasi-coherent cohomology.  The previous step,
`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map`, reduces
[Stacks, Tag 08IB] for the square to invertibility of `Rg_*` of the derived base-change map.
This module transports that map across the two isomorphisms of [Stacks, Tag 08I9] — at `g`,
which is affine because both bases are, and at its base change `g'`, which is affine with it —
and across `Rg_*Rf'_* ≅ Rf_*Rg'_*`, so that it becomes a morphism

`g_*𝒪_{S'} ⊗^𝐋_{𝒪_S} Rf_*K ⟶ Rf_*(g'_*𝒪_{X'} ⊗^𝐋_{𝒪_X} K)`.

This is the shape in which the source's proof of [Stacks, Tag 08IB] concludes: that morphism is
the projection-formula morphism of [Stacks, Tag 08EU] at `A = g_*𝒪_{S'}`, after
`Lf^*(g_*𝒪_{S'}) ≅ f^*(g_*𝒪_{S'}) ≅ g'_*𝒪_{X'}` — the first identification being where Tor
independence enters and the second being [Stacks, Tag 02KG], which is
`AlgebraicGeometry.pullbackPushforwardUnitIso`.

## Main definitions

* `AlgebraicGeometry.derivedPushforwardSquareIso`: the identification
  `Rg_*Rf'_* ≅ Rf_*Rg'_*` of the two derived direct images around the square.
* `AlgebraicGeometry.affineBaseTensorComparison`: the transported morphism displayed above.

## Main results

* `AlgebraicGeometry.isIso_derivedPushforward_map_derivedBaseChangeMap_iff_tensorComparison`:
  the transport is invertible exactly when `Rg_*` of the base-change map is.
* `AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_affineBaseTensorComparison`:
  [Stacks, Tag 08IB] for the square follows from invertibility of the transport.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPullback derivedPushforward derivedPushforwardCompIso)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open RingedSpaceModuleAdjunction (modulePushforward)
open Stacks.AlgebraicGeometry.AffinePushforwardTExactness
  (derivedPushforwardDerivedPullbackTensorIso)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- **The two derived direct images around a commutative square agree.**  For
`g' ≫ f = f' ≫ g`, the composite `Rg_* ∘ Rf'_*` and the composite `Rf_* ∘ Rg'_*` are both the
derived direct image along the common composite, by the composition isomorphism of
[Stacks, Tag 0D5T]. -/
def derivedPushforwardSquareIso
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) :
    derivedPushforward f'.toLRSHom.toShHom ⋙ derivedPushforward g.toLRSHom.toShHom ≅
      derivedPushforward g'.toLRSHom.toShHom ⋙ derivedPushforward f.toLRSHom.toShHom :=
  derivedPushforwardCompIso f'.toLRSHom.toShHom g.toLRSHom.toShHom ≪≫
    eqToIso (congrArg
      (fun h : X'.toRingedSpace ⟶ S.toRingedSpace => derivedPushforward h) sq.symm) ≪≫
    (derivedPushforwardCompIso g'.toLRSHom.toShHom f.toLRSHom.toShHom).symm

/-- **The derived base-change map over an affine base, read as a morphism of derived tensor
products.**  For a Cartesian square with both bases affine, `Rg_*` of the derived base-change
map of [Stacks, Tag 08HY] at a complex with quasi-coherent cohomology, transported across the
isomorphism of [Stacks, Tag 08I9] at `g` on the source, across `Rg_*Rf'_* ≅ Rf_*Rg'_*`, and
across [Stacks, Tag 08I9] at `g'` on the target.

The hypothesis of [Stacks, Tag 08I9] at `g` is quasi-coherence of the cohomology of `Rf_*K`,
which is `AlgebraicGeometry.isQuasicoherent_homologyFunctor_derivedPushforward`; at `g'` it is
quasi-coherence of the cohomology of `K`. -/
def affineBaseTensorComparison [IsAffine S] [IsAffine S']
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
          ((modulePushforward g.toLRSHom.toShHom).obj
            (SheafOfModules.unit (structureSheafRing S'.toRingedSpace))))).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj K) ⟶
      (derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
              ((modulePushforward g'.toLRSHom.toShHom).obj
                (SheafOfModules.unit (structureSheafRing X'.toRingedSpace))))).obj K) :=
  haveI := hqc
  haveI := hqs
  haveI : IsAffineHom g := isAffineHom_of_isAffine g
  haveI : IsAffineHom g' := isAffineHom_of_isPullback_right hsq
  (derivedPushforwardDerivedPullbackTensorIso g
        ((derivedPushforward f.toLRSHom.toShHom).obj K)
        (fun j => isQuasicoherent_homologyFunctor_derivedPushforward f K hK j)).hom ≫
    (derivedPushforward g.toLRSHom.toShHom).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K) ≫
    (derivedPushforwardSquareIso sq).hom.app
      ((derivedPullback g'.toLRSHom.toShHom).obj K) ≫
    (derivedPushforward f.toLRSHom.toShHom).map
      (derivedPushforwardDerivedPullbackTensorIso g' K hK).inv

/-- The forward map of an isomorphism is invertible, with the ambient category instance taken
from the isomorphism rather than from instance search. -/
private theorem isIso_iso_hom {C : Type*} [Category* C] {A B : C} (i : A ≅ B) : IsIso i.hom :=
  ⟨⟨i.inv, i.hom_inv_id, i.inv_hom_id⟩⟩

/-- The backward map of an isomorphism is invertible. -/
private theorem isIso_iso_inv {C : Type*} [Category* C] {A B : C} (i : A ≅ B) : IsIso i.inv :=
  ⟨⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩⟩

/-- Every component of the forward map of a natural isomorphism is invertible. -/
private theorem isIso_natIso_hom_app {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (i : F ≅ G) (A : C) : IsIso (i.hom.app A) :=
  ⟨⟨i.inv.app A, by rw [← NatTrans.comp_app, i.hom_inv_id, NatTrans.id_app],
    by rw [← NatTrans.comp_app, i.inv_hom_id, NatTrans.id_app]⟩⟩

/-- A functor carries an invertible morphism to an invertible morphism, with the witness an
explicit argument. -/
private theorem isIso_functor_map {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} (u : A ⟶ B) (hu : IsIso u) : IsIso (F.map u) := by
  have := hu
  infer_instance

/-- A composite of two invertible morphisms is invertible, with both witnesses explicit. -/
private theorem isIso_comp₂ {C : Type*} [Category* C] {A B D : C} (a : A ⟶ B) (b : B ⟶ D)
    (ha : IsIso a) (hb : IsIso b) : IsIso (a ≫ b) := by
  have := ha
  have := hb
  infer_instance

/-- Cancelling an isomorphism on each side of a composite of three morphisms. -/
private theorem isIso_of_isIso_comp₃ {C : Type*} [Category* C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (ha : IsIso a) (hc : IsIso c)
    (h : IsIso (a ≫ b ≫ c)) : IsIso b := by
  have := ha
  have := hc
  have := h
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_right b c

/-- The transport of `AlgebraicGeometry.affineBaseTensorComparison` is invertible exactly when
`Rg_*` of the derived base-change map is: the three morphisms it is composed with are
isomorphisms. -/
theorem isIso_derivedPushforward_map_derivedBaseChangeMap_iff_tensorComparison
    [IsAffine S] [IsAffine S']
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent) :
    IsIso ((derivedPushforward g.toLRSHom.toShHom).map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
          f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K)) ↔
      IsIso (affineBaseTensorComparison hsq hqc hqs sq K hK) := by
  rw [affineBaseTensorComparison]
  refine ⟨fun h => isIso_comp₂ _ _ (isIso_iso_hom _) (isIso_comp₂ _ _ h ?_),
    isIso_of_isIso_comp₃ _ _ _ (isIso_iso_hom _) ?_⟩
  all_goals
    exact isIso_comp₂ _ _ (isIso_natIso_hom_app _ _) (isIso_functor_map _ _ (isIso_iso_inv _))

/-- **[Stacks, Tag 08IB] over an affine base from the tensor-product form of the base-change
map.**  For a Cartesian square of schemes with `f` quasi-compact and quasi-separated and both
bases affine, and for a complex `K` on `X` with quasi-coherent cohomology, the derived
base-change map of [Stacks, Tag 08HY] is invertible as soon as its transport

`g_*𝒪_{S'} ⊗^𝐋_{𝒪_S} Rf_*K ⟶ Rf_*(g'_*𝒪_{X'} ⊗^𝐋_{𝒪_X} K)`

is.  This is
`AlgebraicGeometry.isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map` composed with
`AlgebraicGeometry.isIso_derivedPushforward_map_derivedBaseChangeMap_iff_tensorComparison`. -/
theorem isIso_derivedBaseChangeMap_of_isIso_affineBaseTensorComparison
    [IsAffine S] [IsAffine S']
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K).IsQuasicoherent)
    (h : IsIso (affineBaseTensorComparison hsq hqc hqs sq K hK)) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
      f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K) :=
  isIso_derivedBaseChangeMap_of_isIso_derivedPushforward_map hsq hqc hqs sq K hK
    ((isIso_derivedPushforward_map_derivedBaseChangeMap_iff_tensorComparison
      hsq hqc hqs sq K hK).2 h)

end AlgebraicGeometry

end
