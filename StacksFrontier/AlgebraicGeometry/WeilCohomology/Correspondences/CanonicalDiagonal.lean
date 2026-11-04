module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductSymmetry
public import StacksFrontier.AlgebraicGeometry.Chow.SelfIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# The canonical family of diagonal classes

Let `k` be a field. For a scheme `W` smooth over `k` of constant dimension `n`, the
diagonal `Δ : W ⟶ W ×_k W` is a regular immersion, and Stacks 0FBR attaches to it its Gysin class
`Δ^! ∈ A^n(W ⟶ W ×_k W)`, the class `c(W ⟶ W ×_k W, 𝒩)` of the normal bundle `𝒩` of the diagonal
(Stacks 0FEZ, 0FBK). The intersection product of Stacks 0FC0 on `W` is `α · β = Δ^!(α × β)`, and
composition of correspondences (Section 0FFZ) is formed with these products on products of smooth
projective schemes.

The constructions of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition`
take the Gysin classes of the diagonals as a `Stacks.WeilCohomology.DiagonalClassFamily`, one
class for every such `W`. This file supplies the canonical family, the class of Stacks 0FBR of
every diagonal, records that each of its classes commutes with every bivariant class
(Stacks 0FBP), and proves the two properties of the family that the compatibilities of
Stacks 0FG0 (2) and (3) consume: its intersection products are transported by isomorphisms over
`k`, and they are commutative.

Both rest on one statement about `Δ^!`. Let `φ : Y' ⟶ Y` and `Φ : Y' ×_Z Y' ⟶ Y ×_Z Y` be
isomorphisms with `Δ_{Y'} ≫ Φ = φ ≫ Δ_Y`. Then `Φ` restricts to an isomorphism `U' ≅ U` of the
open subschemes in which the two diagonals are closed, the closed factors of the diagonals form a
cartesian square with `φ` and `U' ≅ U`, and by the base-change clause of Stacks 0FBK the class
`c(Y ⟶ U, 𝒩)` restricts to `c(Y' ⟶ U', φ^*𝒩)`. The bundle `φ^*𝒩` and the normal bundle `𝒩'` of the
diagonal of `Y'` both have invertible structural surjection onto the conormal sheaf of the closed
factor (the conormal sheaf commutes with flat base change, Stacks 0473), so they give the same
class. Hence `Δ_{Y'}^!` caps as `Δ_Y^!` does along `Φ`. Applied to `Φ = φ × φ` this transports the
product along `φ`, the exterior product being natural with respect to isomorphisms; applied to the
exchange `σ` of the two factors, which fixes the diagonal, it gives `Δ^!(x × y) = Δ^!(y × x)`, the
exterior product being symmetric (Stacks 0FBV). The action of `σ` on the normal bundle, which is
`-1`, is absorbed by the invariance of `c(Z ⟶ X, 𝒩)` under isomorphisms of virtual normal bundles
compatible with the surjections.

## Main definitions

* `Stacks.WeilCohomology.canonicalDiagonalClassFamily`: the family `W ↦ Δ_W^!` of Gysin classes of
  the diagonals of schemes smooth over `k` of constant dimension.
* `Stacks.Chow.coborderRangeIsoOfIsIso`: the isomorphism of the open subschemes in which two
  immersions are closed, induced by an isomorphism of the ambient schemes carrying one immersion
  to the other.

## Main results

* `Stacks.Chow.virtualNormalGysinClass_eq_of_isIso_surjection`: two virtual normal bundles of the
  same rank with invertible surjections onto the conormal sheaf give the same class of Stacks
  0FBK.
* `Stacks.Chow.diagonalGysinClass_cap_eq_of_isIso`: the Gysin class of the diagonal is
  transported by isomorphisms carrying one diagonal to the other.
* `Stacks.Chow.chowPushforwardOfIso_pullbackMap_chowExteriorProduct_tmul`: the exterior product is
  natural with respect to isomorphisms, `(φ₁ × φ₂)_*(α × β) = φ₁_* α × φ₂_* β`.
* `Stacks.Chow.diagonalGysinClass_cap_exteriorSelfProduct_heq_swap`: `Δ^!(x × y)` and
  `Δ^!(y × x)` agree on `W`.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_cap`: the cap operation of the canonical
  class is that of `Stacks.Chow.diagonalGysinClass`.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_commutesWithEveryClass`: each canonical
  class commutes with every bivariant class over `W ×_k W`, by Stacks 0FBP for the class of
  Stacks 0FBK of the closed factor of the diagonal.
* `Stacks.WeilCohomology.canonicalDiagonalClassFamily_isoInvariant`,
  `Stacks.WeilCohomology.canonicalDiagonalClassFamily_isSymmetric`: the canonical intersection
  products are transported by isomorphisms over `k` and are commutative.
* `Stacks.WeilCohomology.corrToPointEquiv_pullback_canonicalDiagonalClassFamily`: **Stacks 0FG0
  (2)**, `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)` with pullback by correspondences corresponding to
  composition.
* `Stacks.WeilCohomology.corrFromPointEquiv_pushforward_canonicalDiagonalClassFamily`: **Stacks
  0FG0 (3)**, `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` with pushforward by correspondences corresponding to
  composition.

## Implementation notes

`Stacks.Chow.diagonalGysinClass` is stated for an arbitrary smooth morphism `g : Y ⟶ Z` with `Y`
over the base, the source of the class lying over the base through `Δ ≫ pr₁ ≫ s_Y`; a
`Stacks.Chow.BivariantClass` records this structure morphism in its type. At `g = s_W` and
`Z = Spec k` that composite equals `s_W` (`Stacks.Chow.diagonal_comp_selfProductStructure`), and
the class is read in the presentation `DiagonalClassFamily` asks for through
`Stacks.Chow.bivariantClassCongrBase`; no other class is constructed.

The transport of `Δ^!` along `Φ` is stated on cap operations against an arbitrary test scheme
`t : T ⟶ Y' ×_Z Y'`, read through any isomorphism `Y ×_{Y ×_Z Y} T ≅ Y' ×_{Y' ×_Z Y'} T` over `T`;
such an isomorphism is unique, the diagonal being a monomorphism, so the statement does not depend
on the choice. The symmetry is first proved for an arbitrary automorphism of `W ×_k W` fixing the
diagonal (`Stacks.Chow.diagonalGysinClass_cap_heq_of_automorphism`) and then specialised to the
exchange of the factors.

The two parts of Stacks 0FG0 are stated for the mixed-dimensional correspondences of Section 0FFZ
(`Stacks.WeilCohomology.Corr`), with the identifications `Stacks.WeilCohomology.corrToPointEquiv`
and `Stacks.WeilCohomology.corrFromPointEquiv`, which carry the same registrations. Properness of
the schemes is what the source's projectivity is used for: proper pushforward along the
projections.

## References

* [Stacks Project, Tag 0FBR](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FEZ](https://stacks.math.columbia.edu/tag/0FEZ)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Geometry

variable {Y Y' P P' : Scheme.{u}} (i : Y ⟶ P) (i' : Y' ⟶ P') [IsImmersion i] [IsImmersion i']
  (φ : Y' ⟶ Y) [IsIso φ] (Φ : P' ⟶ P) [IsIso Φ] (h : i' ≫ Φ = φ ≫ i)

include h in
/-- An isomorphism `Φ : P' ⟶ P` carrying an immersion `i' : Y' ⟶ P'` to an immersion `i : Y ⟶ P`
through an isomorphism `φ : Y' ⟶ Y` carries the open subscheme in which `i'` is closed to the one
in which `i` is closed: the coborder of the image is preserved by homeomorphisms. -/
theorem coborderRange_eq_preimage_of_isIso :
    i'.coborderRange = Φ ⁻¹ᵁ i.coborderRange := by
  apply TopologicalSpace.Opens.ext
  show coborder (Set.range i') = Φ.base ⁻¹' coborder (Set.range i)
  rw [← Φ.isOpenEmbedding.coborder_preimage]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨φ y, by rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (Scheme.homeoOfIso (asIso φ)).surjective y
    refine ⟨z, Φ.isOpenEmbedding.injective ?_⟩
    show (i' ≫ Φ) z = _
    rw [h]
    exact hy

/-- A test scheme `t : T ⟶ P'` has an isomorphism `Y ×_P T ≅ Y' ×_{P'} T` over `T`, lying over the
inverse of `φ`, when `Φ` carries `i'` to `i` through `φ`. -/
private theorem exists_pullback_iso_of_comp_eq {P P' Y Y' T : Scheme.{u}} (i : Y ⟶ P)
    (i' : Y' ⟶ P') (φ : Y' ⟶ Y) (Φ : P' ⟶ P) [IsIso φ] [IsIso Φ] (h : i' ≫ Φ = φ ≫ i)
    (t : T ⟶ P') : ∃ e : pullback i (t ≫ Φ) ⟶ pullback i' t, IsIso e ∧
      e ≫ pullback.snd _ _ = pullback.snd _ _ ∧ e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv φ :=
  ⟨pullback.map _ _ _ _ (inv φ) (𝟙 _) (inv Φ) 
    (by rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]) (by simp), inferInstance, by simp, by simp⟩

/-- An isomorphism `Φ : P' ⟶ P` carrying an immersion `i' : Y' ⟶ P'` to an immersion
`i : Y ⟶ P` through an isomorphism `Y' ≅ Y` restricts to an isomorphism of the open
subschemes in which the two immersions are closed. -/
def coborderRangeIsoOfIsIso : i'.coborderRange.toScheme ≅ i.coborderRange.toScheme where
  hom := Φ.resLE _ _ (coborderRange_eq_preimage_of_isIso i i' φ Φ h).le
  inv := (inv Φ).resLE _ _ (coborderRange_eq_preimage_of_isIso i' i (inv φ) (inv Φ)
    (by rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id])).le
  hom_inv_id := by
    rw [← cancel_mono i'.coborderRange.ι]
    simp [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
  inv_hom_id := by
    rw [← cancel_mono i.coborderRange.ι]
    simp [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

/-- The isomorphism of open subschemes induced by `Φ` is the restriction of `Φ`. -/
@[reassoc (attr := simp)]
theorem coborderRangeIsoOfIsIso_hom_ι :
    (coborderRangeIsoOfIsIso i i' φ Φ h).hom ≫ i.coborderRange.ι = i'.coborderRange.ι ≫ Φ :=
  Scheme.Hom.resLE_comp_ι _ _

include h in
/-- The closed factors of the two immersions form a cartesian square with `φ` and the isomorphism
of open subschemes induced by `Φ`, both vertical arrows being isomorphisms. -/
theorem isPullback_liftCoborder_of_isIso :
    IsPullback i'.liftCoborder φ (coborderRangeIsoOfIsIso i i' φ Φ h).hom i.liftCoborder :=
  IsPullback.of_vert_isIso ⟨by
    rw [← cancel_mono i.coborderRange.ι]
    simp [h]⟩

/-- The comparison `U' ×_{P'} T ⟶ U ×_P T` of the restrictions of a test scheme `t : T ⟶ P'` to
the open subschemes in which `i'` and `i` are closed, induced by `Φ`. -/
abbrev coborderRangeTestMap {T : Scheme.{u}} (t : T ⟶ P') :
    pullback i'.coborderRange.ι t ⟶ pullback i.coborderRange.ι (t ≫ Φ) :=
  pullback.map _ _ _ _ (coborderRangeIsoOfIsIso i i' φ Φ h).hom (𝟙 T) Φ
    (coborderRangeIsoOfIsIso_hom_ι i i' φ Φ h).symm (by rw [Category.id_comp])

/-- The comparison of the restrictions of a test scheme lies over the isomorphism of the open
subschemes. -/
@[reassoc]
theorem coborderRangeTestMap_fst {T : Scheme.{u}} (t : T ⟶ P') :
    coborderRangeTestMap i i' φ Φ h t ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (coborderRangeIsoOfIsIso i i' φ Φ h).hom :=
  pullback.lift_fst _ _ _

/-- The comparison of the restrictions of a test scheme lies over the test scheme. -/
@[reassoc]
theorem coborderRangeTestMap_snd {T : Scheme.{u}} (t : T ⟶ P') :
    coborderRangeTestMap i i' φ Φ h t ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [pullback.lift_snd, Category.comp_id]

end Geometry

section NormalBundle

/-- The base change of a virtual normal bundle along a cartesian square with flat right edge has
invertible structural surjection when the original bundle has: the conormal sheaf commutes with
flat base change (Stacks 0473). -/
theorem VirtualNormalBundle.isIso_baseChange_surjection {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    (i' : Z' ⟶ X') [IsImmersion i] [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) [Flat f]
    (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i) [IsIso 𝒩.surjection] :
    IsIso (𝒩.baseChange i i' g f sq).surjection := by
  have hmap : IsIso ((RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).map
      𝒩.surjection) := @Functor.map_isIso _ _ _ _ _ _ _ _ (by assumption)
  dsimp only [VirtualNormalBundle.baseChange]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' hmap
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i' i g f sq))

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

/-- **`c(Z ⟶ X, 𝒩)` for a virtual normal bundle with invertible surjection.** Two virtual normal
bundles of the same rank whose surjections onto the conormal sheaf are isomorphisms give the
same class of Stacks 0FBK: their duals are identified compatibly with the surjections. -/
theorem virtualNormalGysinClass_eq_of_isIso_surjection (𝒩 𝒩' : VirtualNormalBundle i)
    [IsIso 𝒩.surjection] [IsIso 𝒩'.surjection] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r] :
    virtualNormalBundleClass C sZ sX i hi 𝒩 r = virtualNormalBundleClass C sZ sX i hi 𝒩' r :=
  virtualNormalGysinClass_eq_of_dualIso C sZ sX i hi 𝒩 𝒩'
    (asIso 𝒩'.surjection ≪≫ (asIso 𝒩.surjection).symm)
    ((Category.assoc 𝒩'.surjection (inv 𝒩.surjection) 𝒩.surjection).trans
      ((congrArg (𝒩'.surjection ≫ ·) (IsIso.inv_hom_id 𝒩.surjection)).trans
        (Category.comp_id _))) r

/-- The cap operation of the class of Stacks 0FBK depends on the structure morphism of the
ambient scheme only up to equality. -/
theorem virtualNormalGysinClass_cap_heq_of_structure_eq {sX' : X ⟶ C.S} [LocallyOfFiniteType sX']
    (h : sX = sX') (hi' : i ≫ sX' = sZ) (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r] {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k)
    (α' : chowGroup C (t ≫ sX') k) (hα : α ≍ α') :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap t k α ≍
      (virtualNormalBundleClass C sZ sX' i hi' 𝒩 r).cap t k α' := by
  subst h
  obtain rfl := eq_of_heq hα
  rfl

end NormalBundle

section Crux

variable (C : ChowSituation.{u}) {Y Y' Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (g : Y ⟶ Z) [Smooth g] (g' : Y' ⟶ Z) [Smooth g']
  {d : ℕ} (hd : RelativeDimension g d) (hd' : RelativeDimension g' d)
  (φ : Y' ⟶ Y) [IsIso φ] (Φ : pullback g' g' ⟶ pullback g g) [IsIso Φ]
  (hΔ : pullback.diagonal g' ≫ Φ = φ ≫ pullback.diagonal g)
  (hΦ : Φ ≫ (pullback.fst g g ≫ sY) = pullback.fst g' g' ≫ sY')

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [Smooth g] [Smooth g'] [IsIso Φ] in
include hΦ in
/-- An isomorphism `Y ×_{Y ×_Z Y} T ≅ Y' ×_{Y' ×_Z Y'} T` over `T` is one over the base. -/
theorem diagonal_testIso_comp_structure {T : Scheme.{u}} (t : T ⟶ pullback g' g')
    (e : pullback (pullback.diagonal g) (t ≫ Φ) ⟶ pullback (pullback.diagonal g') t)
    (he : e ≫ pullback.snd _ _ = pullback.snd _ _) :
    e ≫ (pullback.fst (pullback.diagonal g') t ≫
        (pullback.diagonal g' ≫ (pullback.fst g' g' ≫ sY'))) =
      pullback.fst (pullback.diagonal g) (t ≫ Φ) ≫
        (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) := by
  rw [pullback.condition_assoc, reassoc_of% he, pullback.condition_assoc, Category.assoc, hΦ]

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [Smooth g] [Smooth g'] in
include hΔ hΦ in
/-- The comparison `U' ×_{P'} T ⟶ U ×_P T` of the restrictions of a test scheme to the open
subschemes in which the two diagonals are closed is a morphism over the base. -/
theorem diagonal_coborderRangeTestMap_comp_structure {T : Scheme.{u}} (t : T ⟶ pullback g' g') :
    coborderRangeTestMap _ _ φ Φ hΔ t ≫
        (pullback.fst (pullback.diagonal g).coborderRange.ι (t ≫ Φ) ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) =
      pullback.fst (pullback.diagonal g').coborderRange.ι t ≫
        ((pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY')) := by
  rw [coborderRangeTestMap_fst_assoc, coborderRangeIsoOfIsIso_hom_ι_assoc, hΦ]

include hΦ in
/-- The flat pullback to the open subscheme in which the diagonal is closed is transported along
an isomorphism carrying one diagonal to the other. -/
theorem diagonalOpenPullbackClass_cap_heq_of_isIso {T : Scheme.{u}} (t : T ⟶ pullback g' g')
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (pullback.fst g' g' ≫ sY')) k) :
    (diagonalOpenPullbackClass C sY g).cap (t ≫ Φ) k
        (chowGroupCongr C (by rw [Category.assoc, hΦ]) k α) ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal g').coborderRange.ι t ≫
          ((pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY')))
        (pullback.fst (pullback.diagonal g).coborderRange.ι (t ≫ Φ) ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
        (coborderRangeTestMap _ _ φ Φ hΔ t)
        (diagonal_coborderRangeTestMap_comp_structure C sY sY' g g' φ Φ hΔ hΦ t)
        (k - -((0 : ℕ) : ℤ)) ((diagonalOpenPullbackClass C sY' g').cap t k α) := by
  have h0 : 𝟙 T ≫ ((t ≫ Φ) ≫ (pullback.fst g g ≫ sY)) = t ≫ (pullback.fst g' g' ≫ sY') := by
    rw [Category.id_comp, Category.assoc, hΦ]
  refine (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _
        (pullback.diagonal g).coborderRange.ι rfl 0 (relativeDimension_of_isOpenImmersion _))
      (t ≫ Φ) k _).trans ?_
  refine (flatPullbackChow_heq_congr C _ _ _
    (pullback.snd (pullback.diagonal g).coborderRange.ι (t ≫ Φ)) _
    (pullbackSnd_comp_structureMorphism rfl (t ≫ Φ)) rfl rfl _
    (relativeDimension_of_isOpenImmersion _) rfl _
    (flatPullbackDescends C _ _ _ _ _ _ _) _
    (chowPushforwardOfIso C _ _ (𝟙 T) h0 k α)
    ((chowGroupCongr_heq C _ k α).trans
      (chowPushforwardOfIso_heq_of_eq_id (𝟙 T) rfl h0 α).symm)).trans ?_
  rw [flatPullbackChow_chowPushforwardOfIso C _ _ _ _ (𝟙 T) h0
    (coborderRangeTestMap _ _ φ Φ hΔ t)
    (diagonal_coborderRangeTestMap_comp_structure C sY sY' g g' φ Φ hΔ hΦ t)
    (pullback.snd (pullback.diagonal g').coborderRange.ι t)
    (pullbackSnd_comp_structureMorphism rfl t)
    (pullback.snd (pullback.diagonal g).coborderRange.ι (t ≫ Φ))
    (pullbackSnd_comp_structureMorphism rfl (t ≫ Φ))
    (by rw [Category.comp_id, coborderRangeTestMap_snd]) 0
    (relativeDimension_of_isOpenImmersion _) (relativeDimension_of_isOpenImmersion _) k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) α]
  exact chowPushforwardOfIso_heq_congr C _ _ _ _ (by simp) _ _
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _
        (pullback.diagonal g').coborderRange.ι rfl 0 (relativeDimension_of_isOpenImmersion _))
      t k α).symm

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] [Smooth g] [Smooth g'] in
include hΔ hΦ in
/-- The isomorphism `U' ≅ U` of the open subschemes in which the two diagonals are closed is a
morphism over the base. -/
theorem diagonal_coborderRangeIso_comp_structure :
    (pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY') =
      (coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)) := by
  rw [coborderRangeIsoOfIsIso_hom_ι_assoc, hΦ]

include hΔ hΦ in
/-- **The base-change clause of Stacks 0FBK for the closed factor of the diagonal.** The class
`c(Y' ⟶ U', 𝒩')` of the closed factor of the diagonal of `g'` caps as the class
`c(Y ⟶ U, 𝒩)` of the closed factor of the diagonal of `g` does, along the isomorphism `U' ≅ U`
induced by `Φ`: the normal bundles correspond under the cartesian square of the two closed
factors, the conormal sheaf commuting with flat base change. -/
theorem diagonalClosedFactorClass_cap_eq_of_isIso {T : Scheme.{u}}
    (s : T ⟶ (pullback.diagonal g').coborderRange) [LocallyOfFiniteType s] (k : ℤ)
    (β : chowGroup C (s ≫ ((pullback.diagonal g').coborderRange.ι ≫
      (pullback.fst g' g' ≫ sY'))) k) :
    (diagonalClosedFactorClass C sY' g' hd').cap s k β =
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal g).liftCoborder
            (s ≫ (coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom) ≫
          ((pullback.diagonal g).liftCoborder ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))))
        (pullback.fst (pullback.diagonal g').liftCoborder s ≫
          ((pullback.diagonal g').liftCoborder ≫
            ((pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY'))))
        (subschemeTestBaseChangeIso (pullback.diagonal g).liftCoborder
          (pullback.diagonal g').liftCoborder φ (coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom
          (isPullback_liftCoborder_of_isIso _ _ φ Φ hΔ) s).hom
        (by
          rw [diagonal_coborderRangeIso_comp_structure C sY sY' g g' φ Φ hΔ hΦ]
          exact subschemeTestBaseChangeIso_hom_comp_structure _ _ φ _ _ s _)
        (k - d)
        ((diagonalClosedFactorClass C sY g hd).cap
          (s ≫ (coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom) k
          (chowGroupCongr C (by
            rw [diagonal_coborderRangeIso_comp_structure C sY sY' g g' φ Φ hΔ hΦ,
              Category.assoc]) k β)) := by
  have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g' hd'
  have sq := isPullback_liftCoborder_of_isIso (pullback.diagonal g) (pullback.diagonal g') φ Φ hΔ
  have hstr := diagonal_coborderRangeIso_comp_structure C sY sY' g g' φ Φ hΔ hΦ
  have : IsIso (((diagonalVirtualNormalBundle g).baseChange _ _ φ _ sq).surjection) :=
    VirtualNormalBundle.isIso_baseChange_surjection _ _ φ _ sq _
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((diagonalVirtualNormalBundle g).baseChange _ _ φ _ sq).bundle d :=
    isFiniteLocallyFreeOfRank_modulePullback φ _ d inferInstance
  have hC : diagonalClosedFactorClass C sY' g' hd' =
      virtualNormalBundleClass C _ _ (pullback.diagonal g').liftCoborder rfl
        ((diagonalVirtualNormalBundle g).baseChange _ _ φ _ sq) d :=
    virtualNormalGysinClass_eq_of_isIso_surjection C _ _ _ rfl _ _ d
  have hi' : (pullback.diagonal g').liftCoborder ≫
      ((coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))) =
      (pullback.diagonal g').liftCoborder ≫
        ((pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY')) := by
    rw [hstr]
  have hD := virtualNormalGysinClass_cap_baseChange C
    ((pullback.diagonal g).liftCoborder ≫
      ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
    ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))
    (pullback.diagonal g).liftCoborder rfl (pullback.diagonal g').liftCoborder φ _ sq
    (diagonalVirtualNormalBundle g) d
    ((pullback.diagonal g').liftCoborder ≫
      ((pullback.diagonal g').coborderRange.ι ≫ (pullback.fst g' g' ≫ sY'))) hi' s k
    (chowGroupCongr C (by rw [hstr]) k β)
  rw [hC]
  refine eq_of_heq ((virtualNormalGysinClass_cap_heq_of_structure_eq C _ _ _ rfl hstr hi' _ d s
    _ β _ (chowGroupCongr_heq C _ _ β).symm).trans (heq_of_eq hD) |>.trans ?_)
  refine chowPushforwardOfIso_heq _ _ _ rfl rfl rfl ?_
  exact BivariantClass.cap_heq _ _ rfl ((chowGroupCongr_heq C _ _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCongr_heq C _ _ _).symm))

include hΔ hΦ in
/-- **The Gysin class of the diagonal is transported by isomorphisms.** Let `φ : Y' ⟶ Y` and
`Φ : Y' ×_Z Y' ⟶ Y ×_Z Y` be isomorphisms with `Δ_{g'} ≫ Φ = φ ≫ Δ_g`, compatible with the
structure morphisms over the base. Then for a test scheme `t : T ⟶ Y' ×_Z Y'` the cap
`Δ_{g'}^! ∩ α` is the cap `Δ_g^! ∩ α` against `t ≫ Φ`, read through any isomorphism
`e : Y ×_{Y ×_Z Y} T ≅ Y' ×_{Y' ×_Z Y'} T` over `T`. This is the base-change clause of Stacks 0FBK
for the cartesian square formed by the two diagonals, `φ` and `Φ`. -/
theorem diagonalGysinClass_cap_eq_of_isIso {T : Scheme.{u}} (t : T ⟶ pullback g' g')
    [LocallyOfFiniteType t]
    (e : pullback (pullback.diagonal g) (t ≫ Φ) ⟶ pullback (pullback.diagonal g') t) [IsIso e]
    (he : e ≫ pullback.snd _ _ = pullback.snd _ _) (k : ℤ)
    (α : chowGroup C (t ≫ (pullback.fst g' g' ≫ sY')) k) :
    (diagonalGysinClass C sY' g' hd').cap t k α =
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal g) (t ≫ Φ) ≫
          (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)))
        (pullback.fst (pullback.diagonal g') t ≫
          (pullback.diagonal g' ≫ (pullback.fst g' g' ≫ sY')))
        e (diagonal_testIso_comp_structure C sY sY' g g' Φ hΦ t e he) (k - d)
        ((diagonalGysinClass C sY g hd).cap (t ≫ Φ) k
          (chowGroupCongr C (by rw [Category.assoc, hΦ]) k α)) := by
  have hA := diagonalGysinClass_cap_heq C sY' g' hd' t k α
  have hB := diagonalGysinClass_cap_heq C sY g hd (t ≫ Φ) k
    (chowGroupCongr C (by rw [Category.assoc, hΦ]) k α)
  have hxy := diagonalClosedFactorClass_cap_eq_of_isIso C sY sY' g g' hd hd' φ Φ hΔ hΦ
    (pullback.fst (pullback.diagonal g').coborderRange.ι t) (k - -((0 : ℕ) : ℤ))
    ((diagonalOpenPullbackClass C sY' g').cap t k α)
  have hy := diagonalOpenPullbackClass_cap_heq_of_isIso C sY sY' g g' φ Φ hΔ hΦ t k α
  have hE := BivariantClass.cap_heq_chowPushforwardOfIso (diagonalClosedFactorClass C sY g hd)
    (pullback.fst (pullback.diagonal g).coborderRange.ι (t ≫ Φ))
    (coborderRangeTestMap _ _ φ Φ hΔ t)
    (pullback.fst (pullback.diagonal g').coborderRange.ι t ≫
      (coborderRangeIsoOfIsIso _ _ φ Φ hΔ).hom)
    (coborderRangeTestMap_fst _ _ φ Φ hΔ t) rfl _ _
    (diagonal_coborderRangeTestMap_comp_structure C sY sY' g g' φ Φ hΔ hΦ t) hy
    (chowGroupCongr C (by
      rw [Category.assoc, ← diagonal_coborderRangeIso_comp_structure C sY sY' g g' φ Φ hΔ hΦ])
      _ ((diagonalOpenPullbackClass C sY' g').cap t k α))
    (chowGroupCongr_heq C _ _ _)
  have hL := hA.trans (chowPushforwardOfIso_heq_comp_of_comp_eq (C := C) _
    ((pullbackRightPullbackFstIso (pullback.diagonal g').coborderRange.ι t
      (pullback.diagonal g').liftCoborder).hom ≫
        (pullback.congrHom (pullback.diagonal g').liftCoborder_ι rfl).hom) _ rfl _
    (by simp) rfl (rfl : pullback.fst (pullback.diagonal g') t ≫
      (pullback.diagonal g' ≫ (pullback.fst g' g' ≫ sY')) = _) rfl _ _ (heq_of_eq hxy))
  have hR₁ := chowPushforwardOfIso_heq_comp_of_comp_eq (C := C) _
    ((pullbackRightPullbackFstIso (pullback.diagonal g).coborderRange.ι (t ≫ Φ)
      (pullback.diagonal g).liftCoborder).hom ≫
        (pullback.congrHom (pullback.diagonal g).liftCoborder_ι rfl).hom) _ rfl
    (by simp) (by simp) rfl (rfl : pullback.fst (pullback.diagonal g) (t ≫ Φ) ≫
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) = _) rfl _ _ hE
  have hR₂ := chowPushforwardOfIso_heq_comp_of_comp_eq (C := C) _ e _ rfl
    (by simp) (diagonal_testIso_comp_structure C sY sY' g g' Φ hΦ t e he) rfl
    (rfl : pullback.fst (pullback.diagonal g') t ≫
      (pullback.diagonal g' ≫ (pullback.fst g' g' ≫ sY')) = _)
    (show k - -((0 : ℕ) : ℤ) - d = k - d by simp) _ _ (hB.trans hR₁)
  refine eq_of_heq (hL.trans (HEq.trans ?_ hR₂.symm))
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  refine (cancel_mono (pullback.snd (pullback.diagonal g') t)).1 ?_
  simp [he, pullback.congrHom]

end Crux

section ExteriorProductIso

variable (C : ChowSituation.{u}) {A A' B B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
  (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (φ₁ : A' ⟶ A) [IsIso φ₁] (φ₂ : B' ⟶ B) [IsIso φ₂]
  (h₁ : φ₁ ≫ sA = sA') (h₂ : φ₂ ≫ sB = sB')

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [IsIso φ₁] [IsIso φ₂] in
include h₁ in
/-- The product `φ₁ × φ₂ : A' ×_S B' ⟶ A ×_S B` of two morphisms over the base is a morphism over
the base. -/
theorem pullbackMap_comp_fst_comp :
    pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂]) ≫
        (pullback.fst sA sB ≫ sA) = pullback.fst sA' sB' ≫ sA' := by
  simp [h₁]

/-- **The exterior product is natural with respect to isomorphisms, on coefficients.** For
isomorphisms `φ₁ : A' ⟶ A` and `φ₂ : B' ⟶ B` over the base, the coefficient of
`φ₁_* α × φ₂_* β` at the image of a point `z` of `A' ×_S B'` under `φ₁ × φ₂` is the coefficient of
`α × β` at `z`. -/
theorem exteriorProductCoeff_pullbackMap (n m : ℤ) (α : CycleGroup C sA' n)
    (β : CycleGroup C sB' m) (z : (pullback sA' sB' : Scheme.{u})) :
    exteriorProductCoeff C sA sB n m (properPushforward C sA' sA φ₁ h₁ n α)
        (properPushforward C sB' sB φ₂ h₂ m β)
        ((pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂])).base z) =
      exteriorProductCoeff C sA' sB' n m α β z := by
  set Ψ := pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂]) with hΨ
  have hΨ₁ : Ψ ≫ pullback.fst sA sB = pullback.fst sA' sB' ≫ φ₁ := pullback.lift_fst _ _ _
  have hΨ₂ : Ψ ≫ pullback.snd sA sB = pullback.snd sA' sB' ≫ φ₂ := pullback.lift_snd _ _ _
  have hfst : (pullback.fst sA sB).base (Ψ.base z) = φ₁.base ((pullback.fst sA' sB').base z) := by
    rw [← Scheme.Hom.comp_apply, hΨ₁, Scheme.Hom.comp_apply]
  have hsnd : (pullback.snd sA sB).base (Ψ.base z) = φ₂.base ((pullback.snd sA' sB').base z) := by
    rw [← Scheme.Hom.comp_apply, hΨ₂, Scheme.Hom.comp_apply]
  have hideal : exteriorProductIdeal sA' sB' ((pullback.fst sA' sB').base z)
        ((pullback.snd sA' sB').base z) =
      (exteriorProductIdeal sA sB (φ₁.base ((pullback.fst sA' sB').base z))
        (φ₂.base ((pullback.snd sA' sB').base z))).comap Ψ := by
    rw [exteriorProductIdeal, exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hΨ₁, hΨ₂,
      Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      comap_vanishingIdeal_closure_singleton_of_isIso φ₁ ((pullback.fst sA' sB').base z),
      comap_vanishingIdeal_closure_singleton_of_isIso φ₂ ((pullback.snd sA' sB').base z)]
  have hbase := pullbackMap_comp_fst_comp C sA sA' sB sB' φ₁ φ₂ h₁ h₂
  rw [exteriorProductCoeff, exteriorProductCoeff, hfst, hsnd, properPushforward_apply_of_isIso,
    properPushforward_apply_of_isIso, exteriorProductWeight, exteriorProductWeight,
    closedSubschemeCycleCoeff_congr_idealSheaf C _ hideal,
    closedSubschemeCycleCoeff_of_isIso_ambient C _ _ Ψ hbase]
  congr 1
  exact (closedSubschemeCycleCoeff_eq_of_iso C _ _ _ (comapSubschemeIsoOfIsIso Ψ _)
    (comapSubschemeIsoOfIsIso_hom_subschemeι Ψ _) _ _).symm

/-- **The exterior product is natural with respect to isomorphisms, on cycles**:
`(φ₁ × φ₂)_*(α × β) = φ₁_* α × φ₂_* β`. -/
theorem properPushforward_pullbackMap_exteriorProduct (n m : ℤ) (α : CycleGroup C sA' n)
    (β : CycleGroup C sB' m) :
    properPushforward C (pullback.fst sA' sB' ≫ sA') (pullback.fst sA sB ≫ sA)
        (pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂]))
        (pullbackMap_comp_fst_comp C sA sA' sB sB' φ₁ φ₂ h₁ h₂) (n + m)
        (exteriorProduct C sA' sB' n m α β) =
      exteriorProduct C sA sB n m (properPushforward C sA' sA φ₁ h₁ n α)
        (properPushforward C sB' sB φ₂ h₂ m β) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun w ↦ ?_)
  obtain ⟨z, rfl⟩ := (Scheme.homeoOfIso (asIso (pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S)
    (by simp [h₁]) (by simp [h₂])))).surjective w
  show (properPushforward C _ _ _ _ (n + m) (exteriorProduct C sA' sB' n m α β)).1
      ((pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂])).base z) =
    (exteriorProduct C sA sB n m _ _).1
      ((pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂])).base z)
  rw [properPushforward_apply_of_isIso]
  exact (exteriorProductCoeff_pullbackMap C sA sA' sB sB' φ₁ φ₂ h₁ h₂ n m α β z).symm

/-- **Stacks 0FBV, naturality with respect to isomorphisms, on Chow groups**: for isomorphisms
`φ₁ : A' ⟶ A` and `φ₂ : B' ⟶ B` over the base, `(φ₁ × φ₂)_*(α × β) = φ₁_* α × φ₂_* β`. -/
theorem chowPushforwardOfIso_pullbackMap_chowExteriorProduct_tmul [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (n m : ℤ)
    (α : chowGroup C sA' n) (β : chowGroup C sB' m) :
    chowPushforwardOfIso C (pullback.fst sA' sB' ≫ sA') (pullback.fst sA sB ≫ sA)
        (pullback.map sA' sB' sA sB φ₁ φ₂ (𝟙 C.S) (by simp [h₁]) (by simp [h₂]))
        (pullbackMap_comp_fst_comp C sA sA' sB sB' φ₁ φ₂ h₁ h₂) (n + m)
        (chowExteriorProduct C hδ sA' sB' n m (α ⊗ₜ[ℤ] β)) =
      chowExteriorProduct C hδ sA sB n m
        (chowPushforwardOfIso C sA' sA φ₁ h₁ n α ⊗ₜ[ℤ]
          chowPushforwardOfIso C sB' sB φ₂ h₂ m β) := by
  induction α using QuotientAddGroup.induction_on with | H a => ?_
  induction β using QuotientAddGroup.induction_on with | H b => ?_
  rw [chowExteriorProduct_tmul_mk]
  refine (chowPushforwardOfIso_mk C _ _ _ _ (n + m) (exteriorProduct C sA' sB' n m a b)).trans ?_
  show _ = chowExteriorProduct C hδ sA sB n m
    (QuotientAddGroup.mk (properPushforward C sA' sA φ₁ h₁ n a) ⊗ₜ[ℤ]
      QuotientAddGroup.mk (properPushforward C sB' sB φ₂ h₂ m b))
  rw [chowExteriorProduct_tmul_mk]
  exact congrArg _
    (properPushforward_pullbackMap_exteriorProduct C sA sA' sB sB' φ₁ φ₂ h₁ h₂ n m a b)

end ExteriorProductIso

section SelfIntersection

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] [LocallyOfFiniteType sW] in
/-- The identification `W ×_{W ×_k W} (W ×_k W) ≅ W ×_W W ≅ W` underlying the self-intersection
product is the first projection. -/
theorem pullbackDiagonalMapIdIso_hom_fst_id :
    (pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W) =
      pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) := by
  rw [pullbackDiagonalMapIdIso_hom_fst]
  symm
  calc pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W))
      = pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) ≫
          pullback.diagonal sW ≫ pullback.fst sW sW := by
        rw [pullback.diagonal_fst, Category.comp_id]
    _ = _ := by
        rw [pullback.condition_assoc]
        exact congrArg (_ ≫ ·) ((pullback.lift_fst _ _ _).trans (Category.comp_id _))

/-- **The self-intersection product, unfolded**: `x · y` is the cap of `Dc` against the exterior
product `x × y` on `W ×_k W`, carried to `W` along the first projection. -/
theorem selfIntersectionProduct_eq (D : ℤ)
    (Dc : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
      (diagonal_comp_selfProductStructure C sW) D) (n m : ℤ) (x : chowGroup C sW n)
    (y : chowGroup C sW m) :
    selfIntersectionProduct C hδ G sW D Dc n m x y =
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) ≫ sW) sW
        ((pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W))
        (by rw [pullbackDiagonalMapIdIso_hom_fst_id])
        (n + m - D)
        (Dc.cap (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) (n + m)
          (chowGroupCongr C
            (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm (n + m)
            (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) n m
              (chowGroupCongr C (Category.id_comp sW).symm n x ⊗ₜ[ℤ]
                chowGroupCongr C (Category.id_comp sW).symm m y)))) := by
  show chowPushforwardOfIso C _ sW (pullback.fst (𝟙 W) (𝟙 W)) _ _
    (properChowPushforward C _ _ _ _ _ (properPushforwardDescends C _ _ _ _ _) _) = _
  exact chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ _

include hδ in
omit [LocallyOfFiniteType sW] in
/-- For an isomorphism `φ : W' ⟶ W` over the base, `φ_* x × φ_* y` is the pushforward of `x × y`
along `φ × φ`, read as classes on the test schemes `W' ×_k W' ⟶ W' ×_k W'` and
`W ×_k W ⟶ W ×_k W` of the self-intersection products. -/
theorem chowExteriorSelfProduct_heq_of_isIso {W' : Scheme.{u}} [LocallyOfFiniteType sW]
    (sW' : W' ⟶ C.S) [LocallyOfFiniteType sW'] (φ : W' ⟶ W) [IsIso φ] (hφ : φ ≫ sW = sW')
    (a b : ℤ) (x : chowGroup C sW' a) (y : chowGroup C sW' b) :
    chowGroupCongr C (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm
        (a + b)
        (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) a b
          (chowGroupCongr C (Category.id_comp sW).symm a
              (chowPushforwardOfIso C sW' sW φ hφ a x) ⊗ₜ[ℤ]
            chowGroupCongr C (Category.id_comp sW).symm b
              (chowPushforwardOfIso C sW' sW φ hφ b y))) ≍
      chowPushforwardOfIso C
        (exteriorToSelfProduct C sW' (𝟙 W') (𝟙 W') ≫ selfProductStructure C sW')
        (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W) ≫ selfProductStructure C sW)
        (pullback.map (𝟙 W' ≫ sW') (𝟙 W' ≫ sW') (𝟙 W ≫ sW) (𝟙 W ≫ sW) φ φ (𝟙 C.S)
          (by simp [hφ]) (by simp [hφ]))
        (by
          rw [exteriorToSelfProduct_comp_selfProductStructure,
            exteriorToSelfProduct_comp_selfProductStructure]
          simp [hφ]) (a + b)
        (chowGroupCongr C
          (exteriorToSelfProduct_comp_selfProductStructure C sW' (𝟙 W') (𝟙 W')).symm (a + b)
          (chowExteriorProduct C hδ (𝟙 W' ≫ sW') (𝟙 W' ≫ sW') a b
            (chowGroupCongr C (Category.id_comp sW').symm a x ⊗ₜ[ℤ]
              chowGroupCongr C (Category.id_comp sW').symm b y))) := by
  have h₁ : φ ≫ (𝟙 W ≫ sW) = 𝟙 W' ≫ sW' := by simp [hφ]
  have hcongr : ∀ (j : ℤ) (z : chowGroup C sW' j),
      chowGroupCongr C (Category.id_comp sW).symm j (chowPushforwardOfIso C sW' sW φ hφ j z) =
        chowPushforwardOfIso C (𝟙 W' ≫ sW') (𝟙 W ≫ sW) φ h₁ j
          (chowGroupCongr C (Category.id_comp sW').symm j z) := fun j z ↦
    eq_of_heq ((chowGroupCongr_heq C _ j _).trans (chowPushforwardOfIso_heq φ hφ h₁
      (Category.id_comp sW').symm (Category.id_comp sW).symm rfl
      (chowGroupCongr_heq C _ j z).symm))
  rw [hcongr, hcongr, ← chowPushforwardOfIso_pullbackMap_chowExteriorProduct_tmul C _ _ _ _ φ φ
    h₁ h₁ hδ a b]
  refine (chowGroupCongr_heq C _ _ _).trans ?_
  exact chowPushforwardOfIso_heq _ _ _
    (exteriorToSelfProduct_comp_selfProductStructure C sW' (𝟙 W') (𝟙 W')).symm
    (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm rfl
    (chowGroupCongr_heq C _ _ _).symm

end SelfIntersection

section Symmetry

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Smooth sW] {n : ℕ}
  (hn : RelativeDimension sW n)

omit [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S] in
/-- **The Gysin class of the diagonal is invariant under an automorphism fixing the diagonal**, on
a test scheme `t : T ⟶ W ×_k W` along which the diagonal pulls back isomorphically to `T`: if
`Φ` is an automorphism of `W ×_k W` over the base with `Δ ≫ Φ = Δ`, lifted to an automorphism
`w` of `T`, then `Δ^!` caps a class and its pushforward along `w` to the same class on `W`. -/
theorem diagonalGysinClass_cap_heq_of_automorphism (Φ : pullback sW sW ⟶ pullback sW sW)
    [IsIso Φ] (hΔ : pullback.diagonal sW ≫ Φ = pullback.diagonal sW)
    (hΦ : Φ ≫ (pullback.fst sW sW ≫ sW) = pullback.fst sW sW ≫ sW) {T : Scheme.{u}}
    (t : T ⟶ pullback sW sW) [LocallyOfFiniteType t]
    [IsIso (pullback.fst (pullback.diagonal sW) t)] (w : T ⟶ T) [IsIso w] (hw : w ≫ t = t ≫ Φ)
    (hwb : w ≫ (t ≫ (pullback.fst sW sW ≫ sW)) = t ≫ (pullback.fst sW sW ≫ sW))
    {k k' : ℤ} (hk : k' = k) (X : chowGroup C (t ≫ (pullback.fst sW sW ≫ sW)) k)
    (Y : chowGroup C (t ≫ (pullback.fst sW sW ≫ sW)) k')
    (hXY : X ≍ chowPushforwardOfIso C _ _ w hwb k' Y) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sW) t ≫ (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW)))
        sW (pullback.fst (pullback.diagonal sW) t) (by simp) (k - n)
        ((diagonalGysinClass C sW sW hn).cap t k X) ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sW) t ≫ (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW)))
        sW (pullback.fst (pullback.diagonal sW) t) (by simp) (k' - n)
        ((diagonalGysinClass C sW sW hn).cap t k' Y) := by
  have hΔ' : pullback.diagonal sW ≫ Φ = 𝟙 W ≫ pullback.diagonal sW := by
    rw [hΔ, Category.id_comp]
  obtain ⟨e, _, he, he₁⟩ := exists_pullback_iso_of_comp_eq _ _ (𝟙 W) Φ hΔ' t
  have h2 := diagonalGysinClass_cap_eq_of_isIso C sW sW sW sW hn hn (𝟙 W) Φ hΔ' hΦ t e he k' Y
  have h4 := BivariantClass.cap_heq_chowPushforwardOfIso (diagonalGysinClass C sW sW hn) t w
    (t ≫ Φ) hw hk Y X hwb hXY
    (chowGroupCongr C (q' := (t ≫ Φ) ≫ (pullback.fst sW sW ≫ sW)) (by rw [Category.assoc, hΦ])
      k' Y)
    (chowGroupCongr_heq _ _ _ _)
  have hv0 : pullback.fst (pullback.diagonal sW) t ≫ sW = pullback.fst (pullback.diagonal sW) t ≫
      (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW)) := by
    rw [pullback.diagonal_fst_assoc]
  have hL := chowPushforwardOfIso_heq_comp_of_comp_eq (C := C)
    (testBaseChangeIso (pullback.diagonal sW) t w (t ≫ Φ) hw).hom
    (pullback.fst (pullback.diagonal sW) t) _ rfl (testBaseChangeIso_hom_fst_assoc _ _ _ _ _ _)
    hv0 rfl (rfl : sW = sW) (by rw [hk]) _ _ h4
  have hR := chowPushforwardOfIso_heq_comp_of_comp_eq (C := C) e
    (pullback.fst (pullback.diagonal sW) t) _ rfl
    (diagonal_testIso_comp_structure _ sW sW sW sW _ hΦ _ e he)
    hv0 rfl (rfl : sW = sW) rfl _ _ (heq_of_eq h2)
  refine hL.trans (HEq.trans ?_ hR.symm)
  refine heq_of_eq (chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _)
  simp [testBaseChangeIso_hom_fst, he₁]

omit [Smooth sW] in
include hδ in
/-- The exchange of the factors of `W ×_k W` carries `x × y` to `y × x`, read as classes on the
test scheme `W ×_k W ⟶ W ×_k W` of the self-intersection product. -/
theorem chowExteriorSelfProduct_heq_pullbackSymmetry (a b : ℤ) (x : chowGroup C sW a)
    (y : chowGroup C sW b) :
    chowGroupCongr C
        (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm (a + b)
        (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) a b
          (chowGroupCongr C (Category.id_comp sW).symm a x ⊗ₜ[ℤ]
            chowGroupCongr C (Category.id_comp sW).symm b y)) ≍
      chowPushforwardOfIso C
        (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W) ≫ selfProductStructure C sW)
        (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W) ≫ selfProductStructure C sW)
        (pullbackSymmetry (𝟙 W ≫ sW) (𝟙 W ≫ sW)).hom
        (by
          rw [exteriorToSelfProduct_comp_selfProductStructure]
          exact Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base _ _) (b + a)
        (chowGroupCongr C
          (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm (b + a)
          (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) b a
            (chowGroupCongr C (Category.id_comp sW).symm b y ⊗ₜ[ℤ]
              chowGroupCongr C (Category.id_comp sW).symm a x))) := by
  refine (chowGroupCongr_heq _ _ _ _).trans ?_
  refine HEq.trans ?_ (chowPushforwardOfIso_heq _
    (Stacks.WeilCohomology.pullbackSymmetry_hom_comp_base _ _) _
    (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm
    (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm rfl
    (chowGroupCongr_heq _ _ _ _).symm)
  rw [chowPushforwardOfIso_pullbackSymmetry_chowExteriorProduct_tmul]
  exact (chowGroupDegreeEquiv_heq _ _ _ _).symm

/-- **The intersection product formed with the Gysin class of the diagonal is commutative**, before
the identification of the class: `Δ^!(x × y)` and `Δ^!(y × x)`, carried to `W`, agree. The
exchange `σ` of the factors of `W ×_k W` carries `x × y` to `y × x` (Stacks 0FBV) and fixes the
diagonal, and `Δ^!` is invariant under `σ` by the base-change clause of Stacks 0FBK, the action of
`σ` on the normal bundle being absorbed by
`Stacks.Chow.virtualNormalGysinClass_eq_of_isIso_surjection`, an instance of
`Stacks.Chow.virtualNormalGysinClass_eq_of_dualIso`. -/
theorem diagonalGysinClass_cap_exteriorSelfProduct_heq_swap (a b : ℤ) (x : chowGroup C sW a)
    (y : chowGroup C sW b) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) ≫
          (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW))) sW
        ((pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W))
        (by rw [pullbackDiagonalMapIdIso_hom_fst_id]; simp) (a + b - n)
        ((diagonalGysinClass C sW sW hn).cap (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) (a + b)
          (chowGroupCongr C
            (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm (a + b)
            (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) a b
              (chowGroupCongr C (Category.id_comp sW).symm a x ⊗ₜ[ℤ]
                chowGroupCongr C (Category.id_comp sW).symm b y)))) ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) ≫
          (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW))) sW
        ((pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W))
        (by rw [pullbackDiagonalMapIdIso_hom_fst_id]; simp) (b + a - n)
        ((diagonalGysinClass C sW sW hn).cap (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) (b + a)
          (chowGroupCongr C
            (exteriorToSelfProduct_comp_selfProductStructure C sW (𝟙 W) (𝟙 W)).symm (b + a)
            (chowExteriorProduct C hδ (𝟙 W ≫ sW) (𝟙 W ≫ sW) b a
              (chowGroupCongr C (Category.id_comp sW).symm b y ⊗ₜ[ℤ]
                chowGroupCongr C (Category.id_comp sW).symm a x)))) := by
  have hΔ : pullback.diagonal sW ≫ (pullbackSymmetry sW sW).hom = pullback.diagonal sW := by
    ext <;> simp
  have hΦ : (pullbackSymmetry sW sW).hom ≫ (pullback.fst sW sW ≫ sW) =
      pullback.fst sW sW ≫ sW := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullback.condition]
  have hm : (pullbackSymmetry (𝟙 W ≫ sW) (𝟙 W ≫ sW)).hom ≫
      exteriorToSelfProduct C sW (𝟙 W) (𝟙 W) =
      exteriorToSelfProduct C sW (𝟙 W) (𝟙 W) ≫ (pullbackSymmetry sW sW).hom := by
    ext <;> simp [exteriorToSelfProduct, exteriorToSelfProductMap]
  have hfst := pullbackDiagonalMapIdIso_hom_fst_id C sW
  have : IsIso (pullback.fst (pullback.diagonal sW) (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W))) :=
    hfst ▸ inferInstance
  have hy := chowExteriorSelfProduct_heq_pullbackSymmetry C hδ sW a b x y
  have key := diagonalGysinClass_cap_heq_of_automorphism C sW hn (pullbackSymmetry sW sW).hom hΔ hΦ
    (exteriorToSelfProduct C sW (𝟙 W) (𝟙 W)) (pullbackSymmetry (𝟙 W ≫ sW) (𝟙 W ≫ sW)).hom hm
    _ (add_comm b a) _ _ hy
  refine (heq_of_eq ?_).trans (key.trans (heq_of_eq ?_))
  · exact chowPushforwardOfIso_congr_apply _ _ _ _ _ hfst _ _ _ _
  · exact chowPushforwardOfIso_congr_apply _ _ _ _ _ hfst.symm _ _ _ _

end Symmetry

end Stacks.Chow

open Stacks.Chow

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- **The canonical family of diagonal classes**: for `W` smooth over `k` of constant
dimension `n`, the Gysin class `Δ^! ∈ A^n(W ⟶ W ×_k W)` of Stacks 0FBR of its diagonal,
`Stacks.Chow.diagonalGysinClass` at the structure morphism `s_W : W ⟶ Spec k`, read with its
source over `Spec k` through `s_W` rather than through the equal composite `Δ ≫ pr₁ ≫ s_W`. -/
def canonicalDiagonalClassFamily : DiagonalClassFamily k :=
  fun {_} sW _ _ n hn ↦
    bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k) (pullback.diagonal sW)
      (diagonal_comp_selfProductStructure (fieldChowSituation k) sW) rfl (n : ℤ)
      (diagonalGysinClass (fieldChowSituation k) sW sW hn)

variable {k} {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
  [Smooth sW] {n : ℕ} (hn : RelativeDimension sW n)

/-- The canonical diagonal class caps as `Stacks.Chow.diagonalGysinClass` does. The two values lie
in the Chow groups of `W ×_{W ×_k W} T` over `Spec k` through `s_W` and through the equal
composite `Δ ≫ pr₁ ≫ s_W`, whence the heterogeneous equality. -/
theorem canonicalDiagonalClassFamily_cap {T : Scheme.{u}} (t : T ⟶ Limits.pullback sW sW)
    [LocallyOfFiniteType t] (m : ℤ)
    (α : chowGroup (fieldChowSituation k) (t ≫ selfProductStructure (fieldChowSituation k) sW) m) :
    (canonicalDiagonalClassFamily k sW n hn).cap t m α ≍
      (diagonalGysinClass (fieldChowSituation k) sW sW hn).cap t m α :=
  bivariantClassCongrBase_cap (fieldChowSituation k) (fieldGysinSystem k) (pullback.diagonal sW)
    _ rfl (n : ℤ) _ t m α α HEq.rfl

/-- **Stacks 0FBP for the canonical diagonal class.** The Gysin class `Δ^!` of the diagonal of a
scheme `W` smooth over `k` of constant dimension commutes, in the sense of Stacks
0FA2, with every bivariant class over `W ×_k W`: it is the composite of the class of Stacks 0FBK
of the closed factor of the diagonal, which commutes with every class
(`Stacks.Chow.virtualNormalBundleClass_bivariantCommute`), with flat pullback along an open
immersion (`Stacks.Chow.diagonalGysinClass_commute_of`). -/
theorem canonicalDiagonalClassFamily_commutesWithEveryClass :
    (canonicalDiagonalClassFamily k sW n hn).CommutesWithEveryClass := by
  intro Y g _ q d
  have key : bivariantClassCongrBase (fieldChowSituation k) (fieldGysinSystem k)
      (pullback.diagonal sW) (diagonal_comp_selfProductStructure (fieldChowSituation k) sW).symm
      rfl (hv := diagonal_comp_selfProductStructure (fieldChowSituation k) sW) (hv' := rfl)
      (n : ℤ) (canonicalDiagonalClassFamily k sW n hn) =
        diagonalGysinClass (fieldChowSituation k) sW sW hn :=
    BivariantClass.ext _ _ _ _ _ _ _ fun t _ m α ↦ eq_of_heq <|
      (bivariantClassCongrBase_cap (fieldChowSituation k) (fieldGysinSystem k)
        (pullback.diagonal sW) _ rfl (n : ℤ) _ t m α α HEq.rfl).trans
        (canonicalDiagonalClassFamily_cap sW hn t m α)
  rw [key]
  intro T t _ m α
  exact diagonalGysinClass_commute_of (fieldChowSituation k) sW sW hn
    (fun f₂' _ p₂' c₂' ↦
      have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle sW hn
      virtualNormalBundleClass_bivariantCommute (fieldChowSituation k) (r := n)
        (𝒩 := diagonalVirtualNormalBundle sW) (g := f₂') (p := p₂') (c := c₂')) g q d t m α

section Properties

variable (k)

/-- **The canonical intersection products are transported by isomorphisms.** For an isomorphism
`φ : W' ⟶ W` over `k` the product on `W'` is the pushforward along `φ⁻¹` of the product on `W` of
the pushforwards along `φ`: `φ × φ` carries `x × y` to `φ_* x × φ_* y` (Stacks 0FBV) and the
diagonal of `W'` to that of `W`, and `Δ_{W'}^!` is the base change of `Δ_W^!` along `φ × φ` by
the base-change clause of Stacks 0FBK (`Stacks.Chow.diagonalGysinClass_cap_eq_of_isIso`). -/
theorem canonicalDiagonalClassFamily_isoInvariant :
    DiagonalClassFamily.IsoInvariant (canonicalDiagonalClassFamily k) := by
  intro W W' sW _ _ sW' _ _ φ _ hφ n hn hn' a b x y
  suffices key : chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ (a + b - n)
      (selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW' n (canonicalDiagonalClassFamily k sW' n hn') a b x y) =
      selfIntersectionProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW n (canonicalDiagonalClassFamily k sW n hn) a b
        (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ a x)
        (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ b y) by
    rw [← key, chowPushforwardOfIso_inv_comp]
  set Φ : Limits.pullback sW' sW' ⟶ Limits.pullback sW sW :=
    pullback.map sW' sW' sW sW φ φ (𝟙 _) (by simp [hφ]) (by simp [hφ]) with hΦdef
  have hΔ : pullback.diagonal sW' ≫ Φ = φ ≫ pullback.diagonal sW := by
    ext <;> simp [hΦdef]
  have hΦ : Φ ≫ (pullback.fst sW sW ≫ sW) = pullback.fst sW' sW' ≫ sW' := by
    simp [hΦdef, hφ]
  set Ψ : Limits.pullback (𝟙 W' ≫ sW') (𝟙 W' ≫ sW') ⟶ Limits.pullback (𝟙 W ≫ sW) (𝟙 W ≫ sW) :=
    pullback.map (𝟙 W' ≫ sW') (𝟙 W' ≫ sW') (𝟙 W ≫ sW) (𝟙 W ≫ sW) φ φ (𝟙 _)
      (by simp [hφ]) (by simp [hφ]) with hΨdef
  have hm : Ψ ≫ exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W) =
      exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W') ≫ Φ := by
    ext <;> simp [hΨdef, hΦdef, exteriorToSelfProduct, exteriorToSelfProductMap]
  obtain ⟨e, _, he, he₁⟩ := exists_pullback_iso_of_comp_eq (pullback.diagonal sW)
    (pullback.diagonal sW') φ Φ hΔ (exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W'))
  rw [selfIntersectionProduct_eq, selfIntersectionProduct_eq]
  set E' := chowGroupCongr (fieldChowSituation k)
    (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sW' (𝟙 W')
      (𝟙 W')).symm (a + b)
    (chowExteriorProduct (fieldChowSituation k) (fieldChowSituation_dimensionFunction_of_isClosed k)
        (𝟙 W' ≫ sW')
      (𝟙 W' ≫ sW') a b
      (chowGroupCongr (fieldChowSituation k) (Category.id_comp sW').symm a x ⊗ₜ[ℤ]
        chowGroupCongr (fieldChowSituation k) (Category.id_comp sW').symm b y)) with hE'
  have hux : Ψ ≫ (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W) ≫
      selfProductStructure (fieldChowSituation k) sW) =
      exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W') ≫
        selfProductStructure (fieldChowSituation k) sW' := by
    simp only [selfProductStructure]
    rw [← Category.assoc, hm, Category.assoc, hΦ]
  have h1 := canonicalDiagonalClassFamily_cap sW' hn'
    (exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W')) (a + b) E'
  have h2 := diagonalGysinClass_cap_eq_of_isIso (fieldChowSituation k) sW sW' sW sW' hn hn' φ Φ
    hΔ hΦ (exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W')) e he (a + b) E'
  have h4 := BivariantClass.cap_heq_chowPushforwardOfIso (diagonalGysinClass _ sW sW hn)
    (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)) Ψ
    (exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W') ≫ Φ) hm rfl E' _ hux
    (chowExteriorSelfProduct_heq_of_isIso (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
      sW sW' φ hφ a b x y)
    (chowGroupCongr _ (by rw [Category.assoc, hΦ]) (a + b) E') (chowGroupCongr_heq _ _ _ E')
  have h3 := canonicalDiagonalClassFamily_cap sW hn
    (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)) (a + b)
    (chowGroupCongr (fieldChowSituation k)
      (exteriorToSelfProduct_comp_selfProductStructure (fieldChowSituation k) sW (𝟙 W)
        (𝟙 W)).symm (a + b)
      (chowExteriorProduct (fieldChowSituation k)
          (fieldChowSituation_dimensionFunction_of_isClosed k) (𝟙 W ≫ sW)
        (𝟙 W ≫ sW) a b
        (chowGroupCongr (fieldChowSituation k) (Category.id_comp sW).symm a
            (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ a x) ⊗ₜ[ℤ]
          chowGroupCongr (fieldChowSituation k) (Category.id_comp sW).symm b
            (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ b y))))
  have hL₁ := chowPushforwardOfIso_heq_comp_of_comp_eq (C := fieldChowSituation k) e
    ((pullbackDiagonalMapIdIso (𝟙 W') (𝟙 W') sW').hom ≫ pullback.fst (𝟙 W') (𝟙 W')) _ rfl
    (diagonal_testIso_comp_structure _ sW sW' sW sW' Φ hΦ _ e he)
    (by rw [pullbackDiagonalMapIdIso_hom_fst_id]) (by simp) rfl rfl _ _ (h1.trans (heq_of_eq h2))
  have hL := chowPushforwardOfIso_heq_comp_of_comp_eq (C := fieldChowSituation k) _ φ _ rfl _ hφ
    rfl rfl rfl _ _ hL₁
  have hR := chowPushforwardOfIso_heq_comp_of_comp_eq (C := fieldChowSituation k)
    (testBaseChangeIso (pullback.diagonal sW)
      (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)) Ψ
      (exteriorToSelfProduct (fieldChowSituation k) sW' (𝟙 W') (𝟙 W') ≫ Φ) hm).hom
    ((pullbackDiagonalMapIdIso (𝟙 W) (𝟙 W) sW).hom ≫ pullback.fst (𝟙 W) (𝟙 W)) _ rfl
    (by simp) (by rw [pullbackDiagonalMapIdIso_hom_fst_id]) (by simp) rfl rfl _ _ (h3.trans h4)
  refine eq_of_heq (hL.trans (HEq.trans ?_ hR.symm))
  refine heq_of_eq (chowPushforwardOfIso_congr_apply _ _ _ _ _ ?_ _ _ _ _)
  simp only [Category.assoc, pullbackDiagonalMapIdIso_hom_fst_id, testBaseChangeIso_hom_fst,
    reassoc_of% he₁, IsIso.inv_hom_id, Category.comp_id]

/-- **The canonical intersection product is commutative**, Section 0FC0: `x · y = y · x`. The
exchange of the factors of `W ×_k W` carries `x × y` to `y × x` (Stacks 0FBV) and fixes the
diagonal, and `Δ^!` is invariant under it
(`Stacks.Chow.diagonalGysinClass_cap_exteriorSelfProduct_heq_swap`). -/
theorem canonicalDiagonalClassFamily_isSymmetric :
    DiagonalClassFamily.IsSymmetric (canonicalDiagonalClassFamily k) := by
  intro W sW _ _ n hn a b x y
  rw [selfIntersectionProduct_eq, selfIntersectionProduct_eq]
  have hsA : pullback.fst (pullback.diagonal sW)
      (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)) ≫ sW =
      pullback.fst (pullback.diagonal sW)
        (exteriorToSelfProduct (fieldChowSituation k) sW (𝟙 W) (𝟙 W)) ≫
          (pullback.diagonal sW ≫ (pullback.fst sW sW ≫ sW)) := by
    rw [pullback.diagonal_fst_assoc]
  refine eq_of_heq ((chowPushforwardOfIso_heq _ _ _ hsA rfl rfl
    (canonicalDiagonalClassFamily_cap sW hn _ _ _)).trans
    ((diagonalGysinClass_cap_exteriorSelfProduct_heq_swap _
        (fieldChowSituation_dimensionFunction_of_isClosed k) sW
      hn a b x y).trans ?_))
  exact (chowPushforwardOfIso_heq _ _ _ hsA.symm rfl rfl
    (canonicalDiagonalClassFamily_cap sW hn _ _ _).symm).trans
    (chowGroupDegreeEquiv_heq _ _ _ _).symm

end Properties

/-! ### Stacks 0FG0 (2) and (3) -/

section BasePoint

variable {X X' Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sX' : X' ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sX'] [Smooth sY] [IsSeparated sY]

/-- **Stacks Project, Tag 0FG0 (2).** For schemes `X'`, `X` smooth and proper over `k`, of
arbitrary, not necessarily constant, dimension, the canonical isomorphism
`CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)` of `Stacks.WeilCohomology.corrToPointEquiv` turns pullback by
correspondences into composition: for `c ∈ Corrˢ(X', X)` and `β ∈ CH_{-r}(X) ⊗ ℚ`, the class
`c^*(β) ∈ CH_{-(s+r)}(X') ⊗ ℚ` corresponds to `β ∘ c ∈ Corr^{s+r}(X', Spec k)`, the
intersection products being formed with the Gysin classes of the diagonals of Stacks 0FBR. -/
@[stacks 0FG0 "(2): CH_{-r}(X) ⊗ Q = Corr^r(X, Spec k), under which pullback by \
correspondences corresponds to composition"]
theorem corrToPointEquiv_pullback_canonicalDiagonalClassFamily [IsProper sX'] [IsProper sX]
    (s r : ℤ) (c : Corr k sX' sX s)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) :
    corrToPointEquiv k sX' (s + r)
        ((chowGroupDegreeEquiv _ sX' (show -r - s = -(s + r) by ring)).toIntLinearEquiv.baseChange
          ℤ ℚ _ _ (pullback k sX' sX (canonicalDiagonalClassFamily k) s (-r) c β)) =
      comp k sX' sX (𝟙 _) (canonicalDiagonalClassFamily k) s r c (corrToPointEquiv k sX r β) :=
  corrToPointEquiv_pullback (k := k) (Δ := canonicalDiagonalClassFamily k) (sX := sX)
    (sX' := sX') (canonicalDiagonalClassFamily_isoInvariant k) s r c β

add_to_stacks 0FG0 "(2): CH_{-r}(X) ⊗ Q = Corr^r(X, Spec k), under which pullback by \
correspondences corresponds to composition" Stacks.WeilCohomology.corrToPointEquiv

/-- **Stacks Project, Tag 0FG0 (3).** For schemes `X`, `Y` smooth over `k`, of arbitrary, not
necessarily constant, dimension, with `X` proper, the canonical isomorphism
`CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` of `Stacks.WeilCohomology.corrFromPointEquiv` turns pushforward
by correspondences into composition: for `c ∈ Corrˢ(X, Y)` and `α ∈ CH^i(X) ⊗ ℚ`, the class
`c_*(α) ∈ CH^{i+s}(Y) ⊗ ℚ` corresponds to `c ∘ α ∈ Corr^{i+s}(Spec k, Y)`, the intersection
products being formed with the Gysin classes of the diagonals of Stacks 0FBR. -/
@[stacks 0FG0 "(3): CH^r(X) ⊗ Q = Corr^r(Spec k, X), under which pushforward by \
correspondences corresponds to composition"]
theorem corrFromPointEquiv_pushforward_canonicalDiagonalClassFamily [IsProper sX] (i s : ℤ)
    (c : Corr k sX sY s) (α : CodimChow k sX i) :
    corrFromPointEquiv k sY (i + s) (pushforward k sX sY (canonicalDiagonalClassFamily k) s i c α) =
      comp k (𝟙 _) sX sY (canonicalDiagonalClassFamily k) i s (corrFromPointEquiv k sX i α) c :=
  corrFromPointEquiv_pushforward (k := k) (Δ := canonicalDiagonalClassFamily k) (sX := sX)
    (sY := sY) (canonicalDiagonalClassFamily_isoInvariant k)
    (canonicalDiagonalClassFamily_isSymmetric k) i s c α

add_to_stacks 0FG0 "(3): CH^r(X) ⊗ Q = Corr^r(Spec k, X), under which pushforward by \
correspondences corresponds to composition" Stacks.WeilCohomology.corrFromPointEquiv

end BasePoint

end Stacks.WeilCohomology

end
