module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity
public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth

/-!
# Étale coordinates along an étale divisor of a smooth relative curve

Let `g : U ⟶ W` be smooth of relative dimension one and `i : Z ⟶ U` a closed immersion with
`Z ⟶ W` étale. Every point of `Z` has an open neighbourhood `V ⊆ U` with an étale `W`-morphism
`π : V ⟶ 𝔸¹_W` such that `Z ∩ V = π⁻¹(0_W)` scheme-theoretically
(`Stacks.EtaleCohomology.Purity.exists_etale_affineLine_chart`). When `W` is smooth over a field
`k`, the composite `V ⟶ 𝔸¹_W ⟶ 𝔸¹_k` is smooth and `Z ∩ V` is its fibre over the origin
(`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`).

## Main results

* `AlgebraicGeometry.SmoothOfRelativeDimension.eq_of_mem`: the relative dimension of a smooth
  morphism with nonempty source is unique.
* `Stacks.EtaleCohomology.Purity.exists_etale_affineLine_chart`: étale coordinates `V ⟶ 𝔸¹_W`
  along `Z` in which `Z ∩ V` is the inverse image of the zero section.
* `Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`: smooth coordinates `V ⟶ 𝔸¹_k`
  along `Z` in which `Z ∩ V` is the fibre over the origin.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The relative dimension of a smooth morphism is determined at each point**: if `f` is
smooth of relative dimension `a` and of relative dimension `b`, and its source is nonempty, then
`a = b`. -/
theorem SmoothOfRelativeDimension.eq_of_mem {X S : Scheme.{u}} (f : X ⟶ S) (a b : ℕ)
    [SmoothOfRelativeDimension a f] (hb : SmoothOfRelativeDimension b f) (x : X) : a = b := by
  exact_mod_cast (fiberDimensionAt_eq_of_smoothOfRelativeDimension f a x).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension f b x)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology.Purity

open AlgebraicGeometry.AffineSpace Stacks.AlgebraicGeometry

/-- If two étale maps `e`, `e'` out of a nonempty `X` have composites with smooth `f`, `f'` of
relative dimensions `a`, `b` that agree, then `a = b`. -/
private theorem eq_of_etale_comp_eq {X Y Y' S : Scheme.{u}} (e : X ⟶ Y) (e' : X ⟶ Y') [Etale e]
    [Etale e'] (f : Y ⟶ S) (f' : Y' ⟶ S) (h : e ≫ f = e' ≫ f') (a b : ℕ)
    [SmoothOfRelativeDimension a f] [SmoothOfRelativeDimension b f'] (x : X) : a = b := by
  have h₁ : SmoothOfRelativeDimension a (e ≫ f) := SmoothOfRelativeDimension.etale_comp a e f
  rw [h] at h₁
  exact SmoothOfRelativeDimension.eq_of_mem _ a b (SmoothOfRelativeDimension.etale_comp b e' f') x

/-- **Étale coordinates along an étale divisor of a smooth relative curve.** Let `g : U ⟶ W` be
smooth of relative dimension one and `i : Z ⟶ U` a closed immersion with `Z ⟶ W` étale. Every
point `z` of `Z` has an open neighbourhood `V ⊆ U` with an étale `W`-morphism `π : V ⟶ 𝔸¹_W`
under which `Z ∩ V` is the inverse image of the zero section `𝔸⁰_W ⟶ 𝔸¹_W`. -/
theorem exists_etale_affineLine_chart {U W Z : Scheme.{u}} (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 g] (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (z : Z) :
    ∃ (V : U.Opens) (_ : i.base z ∈ V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin (0 + 1)); W))
      (q : (i ⁻¹ᵁ V).toScheme ⟶ 𝔸(ULift.{u} (Fin 0); W)),
      Etale π ∧ π ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W) ↘ W) = V.ι ≫ g ∧
        IsPullback (i ∣_ V) q π (coordinateSubspaceEmbedding W 0 1) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : Smooth (i ≫ g) := inferInstance
  obtain ⟨m, n, V, hzV, π, q, hπ, hover, hpb⟩ :=
    exists_etale_coordinateSubspaceEmbedding_isPullback g i z
  have hover' : π ≫ (𝔸(ULift.{u} (Fin (m + n)); W) ↘ W) = V.ι ≫ g := hover
  have hq : Etale q := MorphismProperty.of_isPullback (P := @Etale) hpb hπ
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver W (m + n)
  have := Stacks.Chow.smoothOfRelativeDimension_affineSpaceOver W m
  have hZ : (i ⁻¹ᵁ V).ι ≫ i ≫ g = q ≫ (𝔸(ULift.{u} (Fin m); W) ↘ W) := by
    rw [← coordinateSubspaceEmbedding_over W m n, ← Category.assoc q, ← hpb.w,
      Category.assoc, hover', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Scheme.Hom.resLE_eq_morphismRestrict, morphismRestrict_ι]
  have hmn : 1 = m + n :=
    eq_of_etale_comp_eq V.ι π g _ hover'.symm 1 (m + n) ⟨i.base z, hzV⟩
  have hm : 0 = m := eq_of_etale_comp_eq (i ⁻¹ᵁ V).ι q (i ≫ g) _ hZ 0 m ⟨z, hzV⟩
  subst hm
  obtain rfl : n = 1 := by lia
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at hpb
  exact ⟨V, hzV, π, q, hπ, hover, hpb⟩

variable (k : Type u) [Field k]

/-- The smooth map `𝔸¹_W ⟶ 𝔸¹_k` for a `k`-scheme `W`. -/
noncomputable def affineLineBaseMap {W : Scheme.{u}} (pW : W ⟶ Spec (.of k)) :
    𝔸(ULift.{u} (Fin (0 + 1)); W) ⟶ affineLine k :=
  AffineSpace.map (ULift.{u} (Fin (0 + 1))) pW ≫ lastCoordinateProjection k 0

/-- If `W` is smooth over `k`, then the map `𝔸¹_W ⟶ 𝔸¹_k` is smooth. -/
instance smooth_affineLineBaseMap {W : Scheme.{u}} (pW : W ⟶ Spec (.of k)) [Smooth pW] :
    Smooth (affineLineBaseMap k pW) := by
  have : Smooth (AffineSpace.map (ULift.{u} (Fin (0 + 1))) pW) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin (0 + 1))) pW).flip inferInstance
  rw [affineLineBaseMap]
  infer_instance

/-- The zero section `𝔸⁰_W ⟶ 𝔸¹_W` is the fibre of `𝔸¹_W ⟶ 𝔸¹_k` over the origin. -/
theorem isPullback_coordinateSubspaceEmbedding_affineLineBaseMap {W : Scheme.{u}}
    (pW : W ⟶ Spec (.of k)) :
    IsPullback (coordinateSubspaceEmbedding W 0 1)
      (AffineSpace.map (ULift.{u} (Fin 0)) pW ≫ (𝔸(ULift.{u} (Fin 0); Spec (.of k)) ↘ Spec (.of k)))
      (affineLineBaseMap k pW) (origin k) :=
  (isPullback_coordinateSubspaceEmbedding_map pW 0 1).paste_vert
    (isPullback_coordinateSubspaceEmbedding_one k 0)

/-- **Smooth coordinates along an étale divisor of a smooth relative curve over a smooth
`k`-scheme.** Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one
and `i : Z ⟶ U` a closed immersion with `Z ⟶ W` étale. Every point `z` of `Z` has an open
neighbourhood `V ⊆ U` with a smooth `φ : V ⟶ 𝔸¹_k`, factoring as an étale `W`-morphism
`π : V ⟶ 𝔸¹_W` followed by `𝔸¹_W ⟶ 𝔸¹_k`, whose fibre over the origin is `Z ∩ V`. -/
theorem exists_smooth_affineLine_chart {U W Z : Scheme.{u}} (pW : W ⟶ Spec (.of k)) [Smooth pW]
    (g : U ⟶ W) [SmoothOfRelativeDimension 1 g] (i : Z ⟶ U) [IsClosedImmersion i]
    [Etale (i ≫ g)] (z : Z) :
    ∃ (V : U.Opens) (_ : i.base z ∈ V) (π : V.toScheme ⟶ 𝔸(ULift.{u} (Fin (0 + 1)); W))
      (ψ : (i ⁻¹ᵁ V).toScheme ⟶ Spec (.of k)),
      Etale π ∧ π ≫ (𝔸(ULift.{u} (Fin (0 + 1)); W) ↘ W) = V.ι ≫ g ∧
        Smooth (π ≫ affineLineBaseMap k pW) ∧
        IsPullback (i ∣_ V) ψ (π ≫ affineLineBaseMap k pW) (origin k) := by
  obtain ⟨V, hzV, π, q, hπ, hover, hpb⟩ := exists_etale_affineLine_chart g i z
  have : Smooth π := SmoothOfRelativeDimension.smooth 0 π
  exact ⟨V, hzV, π, _, hπ, hover, inferInstance,
    hpb.paste_vert (isPullback_coordinateSubspaceEmbedding_affineLineBaseMap k pW)⟩

end Stacks.EtaleCohomology.Purity

end
