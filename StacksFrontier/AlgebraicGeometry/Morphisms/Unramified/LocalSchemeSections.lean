module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local

/-!
# Morphisms from a local scheme into an unramified scheme

Let `f : X ⟶ Y` be a morphism of schemes and let `O` be a local ring. Two morphisms
`a b : Spec O ⟶ X` with `a ≫ f = b ≫ f` coincide as soon as they agree on the closed point of
`Spec O` together with its residue field, and `f` is unramified at the image of the closed
point.

Agreement on the closed point as a point is not enough: the two morphisms
`Spec ℂ ⟶ Spec ℂ` induced by the identity and by complex conjugation agree on the unique point,
lie over the same morphism to `Spec ℝ`, and `Spec ℂ ⟶ Spec ℝ` is étale. The hypothesis used
below is therefore that the composites `Spec κ ⟶ Spec O ⟶ X` agree, where `κ` is the residue
field of `O`.

## Main results

* `AlgebraicGeometry.eq_of_comp_eq_of_isOpenImmersion_diagonal`: the statement for a morphism
  whose diagonal is an open immersion.
* `AlgebraicGeometry.eq_of_comp_eq_of_unramifiedAt`: the statement for a morphism unramified at
  the image of the closed point.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits IsLocalRing

/-- The canonical morphism from the spectrum of the residue field of a local ring `O` to the
spectrum of `O`. -/
noncomputable abbrev specResidueToSpec (O : Type u) [CommRing O] [IsLocalRing O] :
    Spec (.of (ResidueField O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (residue O))

/-- The morphism `Spec κ ⟶ Spec O` sends the unique point to the closed point. -/
theorem specResidueToSpec_closedPoint (O : Type u) [CommRing O] [IsLocalRing O] :
    specResidueToSpec O (closedPoint (ResidueField O)) = closedPoint O := by
  have : IsLocalHom (CommRingCat.ofHom (residue O)).hom :=
    inferInstanceAs (IsLocalHom (residue O))
  exact Spec_closedPoint

/-- A morphism from the spectrum of a local ring whose closed point lies in an open set `U` has
image contained in `U`. -/
theorem range_subset_of_apply_closedPoint_mem {X : Scheme.{u}} {O : Type u} [CommRing O]
    [IsLocalRing O] (c : Spec (.of O) ⟶ X) {U : Set X} (hU : IsOpen U)
    (hc : c (closedPoint O) ∈ U) : Set.range c ⊆ U := by
  rintro _ ⟨p, rfl⟩
  exact ((specializes_closedPoint p).map c.continuous).mem_open hU hc

/-- Let `f : X ⟶ Y` have open-immersion diagonal and let `O` be a local ring with residue field
`κ`. Two morphisms `a b : Spec O ⟶ X` with `a ≫ f = b ≫ f` whose composites with
`Spec κ ⟶ Spec O` agree are equal. -/
theorem eq_of_comp_eq_of_isOpenImmersion_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal f)] {O : Type u} [CommRing O] [IsLocalRing O]
    {a b : Spec (.of O) ⟶ X} (hab : a ≫ f = b ≫ f)
    (hκ : specResidueToSpec O ≫ a = specResidueToSpec O ≫ b) : a = b := by
  obtain ⟨y, hy⟩ : ∃ y, specResidueToSpec O y = closedPoint O :=
    ⟨_, specResidueToSpec_closedPoint O⟩
  have hl : specResidueToSpec O ≫ pullback.lift a b hab =
      (specResidueToSpec O ≫ a) ≫ pullback.diagonal f :=
    pullback.hom_ext
      (by
        simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        exact congrArg _ (pullback.lift_fst a b hab))
      (by
        simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact (congrArg _ (pullback.lift_snd a b hab)).trans hκ.symm)
  have hc : pullback.lift a b hab (closedPoint O) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨(specResidueToSpec O ≫ a) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hl, Scheme.Hom.comp_apply, hy]
  have hrange : Set.range (pullback.lift a b hab) ⊆ Set.range (pullback.diagonal f) :=
    range_subset_of_apply_closedPoint_mem _
      (pullback.diagonal f).isOpenEmbedding.isOpen_range hc
  have hfac := IsOpenImmersion.lift_fac _ _ hrange
  have ha : a = IsOpenImmersion.lift _ _ hrange :=
    calc a = pullback.lift a b hab ≫ pullback.fst f f := (pullback.lift_fst a b hab).symm
      _ = (IsOpenImmersion.lift _ _ hrange ≫ pullback.diagonal f) ≫ pullback.fst f f := by
        rw [hfac]
      _ = _ := by rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hb : b = IsOpenImmersion.lift _ _ hrange :=
    calc b = pullback.lift a b hab ≫ pullback.snd f f := (pullback.lift_snd a b hab).symm
      _ = (IsOpenImmersion.lift _ _ hrange ≫ pullback.diagonal f) ≫ pullback.snd f f := by
        rw [hfac]
      _ = _ := by rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  exact ha.trans hb.symm

/-- Restricting a morphism to affine opens `U ≤ f ⁻¹ᵁ V` on which the map of sections is
unramified gives an unramified morphism. -/
theorem unramified_resLE_of_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (h : letI : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(Y, V) Γ(X, U)) :
    Unramified (f.resLE V U e) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine
    (P := fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ Unramified f)]
  let : Algebra Γ(Y, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  refine ((RingHom.FormallyUnramified.propertyIsLocal.and
    RingHom.finiteType_isLocal).respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U e)).mpr ?_
  exact ⟨RingHom.formallyUnramified_algebraMap.mpr h.formallyUnramified,
    RingHom.finiteType_algebraMap.mpr h.finiteType⟩

/-- Let `f : X ⟶ Y` be a morphism of schemes and let `O` be a local ring with residue field
`κ`. Two morphisms `a b : Spec O ⟶ X` with `a ≫ f = b ≫ f`, whose composites with
`Spec κ ⟶ Spec O` agree, and such that `f` is unramified at the image of the closed point, are
equal. -/
theorem eq_of_comp_eq_of_unramifiedAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    {O : Type u} [CommRing O] [IsLocalRing O] {a b : Spec (.of O) ⟶ X} (hab : a ≫ f = b ≫ f)
    (hκ : specResidueToSpec O ≫ a = specResidueToSpec O ≫ b)
    (hf : UnramifiedAt f (a (closedPoint O))) : a = b := by
  obtain ⟨U, hU, hxU, V, hV, e, halg⟩ := hf
  have hx : a (closedPoint O) = b (closedPoint O) := by
    obtain ⟨y, hy⟩ : ∃ y, specResidueToSpec O y = closedPoint O :=
      ⟨_, specResidueToSpec_closedPoint O⟩
    rw [← hy, ← Scheme.Hom.comp_apply, hκ, Scheme.Hom.comp_apply]
  have hra : Set.range a ⊆ Set.range U.ι := by
    rw [U.range_ι]; exact range_subset_of_apply_closedPoint_mem a U.2 hxU
  have hrb : Set.range b ⊆ Set.range U.ι := by
    rw [U.range_ι]; exact range_subset_of_apply_closedPoint_mem b U.2 (hx ▸ hxU)
  have ha := IsOpenImmersion.lift_fac U.ι a hra
  have hb := IsOpenImmersion.lift_fac U.ι b hrb
  have := unramified_resLE_of_isAffineOpen f hU hV e halg
  have hab' : IsOpenImmersion.lift U.ι a hra ≫ f.resLE V U e =
      IsOpenImmersion.lift U.ι b hrb ≫ f.resLE V U e := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, ← Category.assoc, ha, hb, hab]
  have hκ' : specResidueToSpec O ≫ IsOpenImmersion.lift U.ι a hra =
      specResidueToSpec O ≫ IsOpenImmersion.lift U.ι b hrb := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ha, hb, hκ]
  rw [← ha, ← hb, eq_of_comp_eq_of_isOpenImmersion_diagonal _ hab' hκ']

end AlgebraicGeometry
