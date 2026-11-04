module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedFibreCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.CancelEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Slicing a smooth morphism into affine pieces with a section

A smooth morphism of schemes admits an étale covering of its source each member of which maps to
the base through an étale morphism, the first factor being a smooth morphism of affine schemes
which has a section and has geometrically connected fibres.

## Main results

* `AlgebraicGeometry.exists_etaleCover_factors_affine_smooth_section`: a smooth morphism admits
  such a covering, together with the factorizations and the sections.

## Implementation notes

The covering is a `AlgebraicGeometry.Scheme.Cover` for the étale precoverage, so joint surjectivity
and étaleness of its members are part of the datum, and the factorization is recorded as an
equality of the two composites to the base.

## References

* [Stacks Project, Tag 0EY4](https://stacks.math.columbia.edu/tag/0EY4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section ProofImplementation

/-- A geometrically irreducible morphism is geometrically connected. -/
private theorem geometricallyConnected_of_geometricallyIrreducible' {X Y : Scheme.{u}}
    (p : X ⟶ Y) [GeometricallyIrreducible p] : GeometricallyConnected p := by
  rw [GeometricallyConnected.eq_geometrically]
  intro K _ y Z fst snd hpull
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd hpull
  infer_instance

/-- The local datum produced at a point `x` of the source of a smooth morphism `f`: an étale
morphism onto a neighbourhood of `x` which maps to the base through an étale morphism, the first
factor being a smooth morphism of affine schemes with a section and geometrically connected
fibres. -/
private structure SlicedPiece {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The member of the covering. -/
  source : Scheme.{u}
  /-- The scheme étale over the base through which the member factors. -/
  base : Scheme.{u}
  /-- The étale morphism to the source of `f`. -/
  toSource : source ⟶ X
  /-- The étale morphism to the base of `f`. -/
  toBase : base ⟶ S
  /-- The smooth first factor. -/
  toBaseScheme : source ⟶ base
  /-- The section of the first factor. -/
  sec : base ⟶ source
  /-- The morphism to the source of `f` is étale. -/
  etaleSource : Etale toSource
  /-- The morphism to the base of `f` is étale. -/
  etaleBase : Etale toBase
  /-- The member of the covering is affine. -/
  isAffineSource : IsAffine source
  /-- The scheme étale over the base is affine. -/
  isAffineBase : IsAffine base
  /-- The first factor is smooth. -/
  smooth : Smooth toBaseScheme
  /-- The section equation. -/
  sec_comp : sec ≫ toBaseScheme = 𝟙 base
  /-- The first factor has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected toBaseScheme
  /-- The factorization of the composite to the base of `f`. -/
  factors : toBaseScheme ≫ toBase = toSource ≫ f
  /-- The chosen point is in the image. -/
  coversPoint : ∃ y : source, toSource y = x

/-- Every point of the source of a smooth morphism carries a sliced piece. -/
private theorem nonempty_slicedPiece {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    Nonempty (SlicedPiece f x) := by
  classical
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  obtain ⟨𝒱, h𝒱⟩ := exists_etaleCover_factors_geometricallyConnected f
  have hmem := (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
    𝒱.toPreZeroHypercover).mp 𝒱.mem₀
  obtain ⟨j, u, hu⟩ := hmem.1 x
  have : Etale (𝒱.f j) := hmem.2 j
  obtain ⟨B, hb, g, hbet, hgflat, hgfp, hgconn, -, hfac⟩ := h𝒱 j
  have : Smooth (g ≫ hb) := by rw [hfac]; infer_instance
  have : Smooth g := Smooth.of_comp_of_etale g hb
  have : LocallyOfFinitePresentation g := hgfp.locallyOfFinitePresentation
  have : LocallyOfFiniteType g := inferInstance
  have : QuasiCompact g := hgfp.quasiCompact
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth g hgconn
  obtain ⟨B₁, hB₁, hvB₁, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := B) (x := g u) (U := ⊤) trivial
  obtain ⟨U₂, hU₂, huU₂, hU₂le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := 𝒱.X j) (x := u) (U := g ⁻¹ᵁ B₁) hvB₁
  have hWopen : IsOpen (g.base '' (U₂ : Set (𝒱.X j))) := g.isOpenMap _ U₂.2
  set W : B.Opens := ⟨g.base '' (U₂ : Set (𝒱.X j)), hWopen⟩
  have hvW : g u ∈ W := ⟨u, huU₂, rfl⟩
  obtain ⟨r, hrW, hvr⟩ := hB₁.exists_basicOpen_le (V := W) ⟨g u, hvW⟩ hvB₁
  have hB₂ : IsAffineOpen (B.basicOpen r) := hB₁.basicOpen r
  have hU₃ : IsAffineOpen (U₂ ⊓ g ⁻¹ᵁ B.basicOpen r) :=
    Scheme.basicOpen_appLE g U₂ B₁ hU₂le r ▸ hU₂.basicOpen (g.appLE B₁ U₂ hU₂le r)
  set U₃ : (𝒱.X j).Opens := U₂ ⊓ g ⁻¹ᵁ B.basicOpen r
  have huU₃ : u ∈ U₃ := ⟨huU₂, hvr⟩
  have hU₃le : U₃ ≤ g ⁻¹ᵁ B.basicOpen r := inf_le_right
  have : IsAffine U₃.toScheme := hU₃
  have : IsAffine (B.basicOpen r).toScheme := hB₂
  set g₃ := g.resLE (B.basicOpen r) U₃ hU₃le with hg₃def
  have hsurj : Function.Surjective g₃.base := by
    rintro ⟨w, hw⟩
    obtain ⟨u', hu'U₂, hu'⟩ := hrW hw
    have hu'U₃ : u' ∈ U₃ := ⟨hu'U₂, show g.base u' ∈ B.basicOpen r from hu' ▸ hw⟩
    exact ⟨⟨u', hu'U₃⟩, Subtype.ext (by rw [hg₃def, Scheme.Hom.coe_resLE_apply]; exact hu')⟩
  have : Surjective g₃ := ⟨hsurj⟩
  have hcomp : g₃ = (𝒱.X j).homOfLE hU₃le ≫ g ∣_ B.basicOpen r := by
    rw [hg₃def, ← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.map_resLE]
  have : Surjective ((𝒱.X j).homOfLE hU₃le ≫ g ∣_ B.basicOpen r) := hcomp ▸ ‹Surjective g₃›
  have : GeometricallyIrreducible g₃ := hcomp ▸ inferInstance
  have : GeometricallyConnected g₃ := geometricallyConnected_of_geometricallyIrreducible' g₃
  have hrange : (⟨g u, hvr⟩ : (B.basicOpen r).toScheme) ∈ Set.range g₃.base :=
    ⟨⟨u, huU₃⟩, Subtype.ext (by rw [hg₃def, Scheme.Hom.coe_resLE_apply])⟩
  obtain ⟨N, sec, hsec⟩ := exists_etaleNeighborhood_lift_of_smooth g₃ ⟨g u, hvr⟩ hrange
  have := N.etale_toBase
  obtain ⟨A, hA, hptA, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := N.scheme) (x := N.point) (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  set a : A.toScheme ⟶ (B.basicOpen r).toScheme := A.ι ≫ N.toBase with hadef
  refine ⟨{
    source := pullback g₃ a
    base := A.toScheme
    toSource := pullback.fst g₃ a ≫ U₃.ι ≫ 𝒱.f j
    toBase := a ≫ (B.basicOpen r).ι ≫ hb
    toBaseScheme := pullback.snd g₃ a
    sec := pullback.lift (A.ι ≫ sec) (𝟙 _) (by rw [Category.assoc, hsec, hadef, Category.id_comp])
    etaleSource := inferInstance
    etaleBase := inferInstance
    isAffineSource := inferInstance
    isAffineBase := inferInstance
    smooth := inferInstance
    sec_comp := pullback.lift_snd _ _ _
    geometricallyConnected := inferInstance
    factors := ?_
    coversPoint := ?_ }⟩
  · have hι : U₃.ι ≫ g = g₃ ≫ (B.basicOpen r).ι := (Scheme.Hom.resLE_comp_ι g hU₃le).symm
    rw [← pullback.condition_assoc, ← reassoc_of% hι, hfac]
    simp only [Category.assoc]
  · have ha : a.base ⟨N.point, hptA⟩ = ⟨g u, hvr⟩ := by
      rw [hadef]; exact N.map_point
    have hpt : g₃.base ⟨u, huU₃⟩ = a.base ⟨N.point, hptA⟩ := by
      rw [ha]
      exact Subtype.ext (by rw [hg₃def, Scheme.Hom.coe_resLE_apply])
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpt
    exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]; exact hu⟩

end ProofImplementation

/-- A smooth morphism of schemes admits an étale covering of its source each member of which maps
to the base through an étale morphism, the first factor being a smooth morphism of affine schemes
which has a section and has geometrically connected fibres. -/
@[stacks 0EY4]
theorem exists_etaleCover_factors_affine_smooth_section {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] :
    ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      ∃ (Bᵢ : Scheme.{u}) (h : Bᵢ ⟶ S) (g : 𝒰.X i ⟶ Bᵢ) (σ : Bᵢ ⟶ 𝒰.X i),
        Etale h ∧ IsAffine (𝒰.X i) ∧ IsAffine Bᵢ ∧ Smooth g ∧ σ ≫ g = 𝟙 Bᵢ ∧
          GeometricallyConnected g ∧ g ≫ h = 𝒰.f i ≫ f := by
  classical
  let P : (x : X) → SlicedPiece f x := fun x => Classical.choice (nonempty_slicedPiece f x)
  let 𝒰 : X.Cover Scheme.etalePrecoverage :=
    Scheme.Cover.mkOfCovers (P := @Etale) X (fun x => (P x).source) (fun x => (P x).toSource)
      (fun x => by obtain ⟨y, hy⟩ := (P x).coversPoint; exact ⟨x, y, hy⟩)
      (fun x => (P x).etaleSource)
  exact ⟨𝒰, fun i => ⟨(P i).base, (P i).toBase, (P i).toBaseScheme, (P i).sec, (P i).etaleBase,
    (P i).isAffineSource, (P i).isAffineBase, (P i).smooth, (P i).sec_comp,
    (P i).geometricallyConnected, (P i).factors⟩⟩

end AlgebraicGeometry

end
