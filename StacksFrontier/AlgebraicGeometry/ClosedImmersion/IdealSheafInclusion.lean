module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The defining ideal sheaf of an inclusion of closed subschemes

Let `X` be a scheme and let `I ≤ J` be two `AlgebraicGeometry.Scheme.IdealSheafData` on `X`. The
closed subscheme cut out by `J` is a closed subscheme of the one cut out by `I`, by
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, and this file computes the defining ideal
sheaf of that inclusion: on the chart `I.subschemeι ⁻¹ᵁ U` over an affine open `U ⊆ X` it is the
image of `J.ideal U` in `Γ(X, U) ⧸ I.ideal U`, i.e. `J(U)/I(U)`.

## Main results

* `Stacks.ClosedImmersion.ker_ideal_preimage`: for `f : Y ⟶ Z` and `g : Z ⟶ X` with `g.app U`
  surjective, the ideal that `AlgebraicGeometry.Scheme.Hom.ker f` assigns to the chart `g ⁻¹ᵁ U`
  is the image under `g.app U` of the ideal that `AlgebraicGeometry.Scheme.Hom.ker (f ≫ g)`
  assigns to `U`.
* `Stacks.ClosedImmersion.ker_inclusion_ideal` and `Stacks.ClosedImmersion.ker_app_inclusion` are
  the computation of the defining ideal sheaf of
  `AlgebraicGeometry.Scheme.IdealSheafData.inclusion`, as an ideal-sheaf datum and as the kernel
  of the map on sections.
* `Stacks.ClosedImmersion.map_ker_app_inclusion` reads the same computation through
  `AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso`, where it becomes literally the image
  of `J.ideal U` under `Ideal.Quotient.mk (I.ideal U)`.
* `Stacks.ClosedImmersion.comap_ker_inclusion_ideal`: the contraction of that ideal along the
  chart map is `J.ideal U`.
* `Stacks.ClosedImmersion.bijOn_subschemeι_app_ideal_ker_inclusion`: when two closed subschemes
  cover `X` scheme-theoretically, restriction to one of them maps the ideal of the other
  bijectively onto the ideal of their intersection inside it.
* `Stacks.ClosedImmersion.isClosedImmersion_inclusion`: the inclusion is a closed immersion.

## Implementation notes

In `Stacks.ClosedImmersion.ker_ideal_preimage` the affineness of the chart `g ⁻¹ᵁ U` is a
hypothesis; `AlgebraicGeometry.IsAffineOpen.preimage` supplies it for an affine morphism.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ClosedImmersion

variable {X Y Z : Scheme.{u}}

/-! ### The defining ideal sheaf of a factor -/

/-- **The defining ideal sheaf of a factor, on a chart.** Let `f : Y ⟶ Z` and `g : Z ⟶ X` with
`g` quasi-compact, let `U ⊆ X` be an affine open whose preimage in `Z` is affine, and suppose the
section map `g.app U` is surjective. Then the ideal that `AlgebraicGeometry.Scheme.Hom.ker f`
assigns to `g ⁻¹ᵁ U` is the image under `g.app U` of the ideal that
`AlgebraicGeometry.Scheme.Hom.ker (f ≫ g)` assigns to `U`. -/
theorem ker_ideal_preimage (f : Y ⟶ Z) (g : Z ⟶ X) [QuasiCompact g] (U : X.affineOpens)
    (hU : IsAffineOpen (g ⁻¹ᵁ U.1)) (hg : Function.Surjective (g.app U.1).hom) :
    f.ker.ideal ⟨g ⁻¹ᵁ U.1, hU⟩ = Ideal.map (g.app U.1).hom ((f ≫ g).ker.ideal U) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ideal_map f.ker g U hU,
    Ideal.map_comap_of_surjective _ hg]

/-! ### The inclusion of closed subschemes -/

variable {I J : X.IdealSheafData}

/-- The inclusion of the closed subscheme cut out by `J` into the one cut out by `I ≤ J` is a
closed immersion. -/
instance isClosedImmersion_inclusion (h : I ≤ J) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

/-- **The defining ideal sheaf of an inclusion of closed subschemes.** For `I ≤ J` on `X` and an
affine open `U ⊆ X`, the ideal that `AlgebraicGeometry.Scheme.Hom.ker` assigns to the chart
`I.subschemeι ⁻¹ᵁ U` of the closed subscheme cut out by `I` is the image of `J.ideal U` under the
quotient map `Γ(X, U) ⟶ Γ(𝒪_X/I, I.subschemeι ⁻¹ᵁ U)`. -/
theorem ker_inclusion_ideal (h : I ≤ J) (U : X.affineOpens) :
    (Scheme.IdealSheafData.inclusion h).ker.ideal ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩ =
      Ideal.map (I.subschemeι.app U.1).hom (J.ideal U) := by
  rw [ker_ideal_preimage _ I.subschemeι U _ (I.subschemeι_app_surjective U),
    Scheme.IdealSheafData.inclusion_subschemeι, Scheme.IdealSheafData.ker_subschemeι]

/-- **The kernel of the inclusion on sections.** The section map of
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion` over the chart `I.subschemeι ⁻¹ᵁ U` has the
image of `J.ideal U` as its kernel. -/
theorem ker_app_inclusion (h : I ≤ J) (U : X.affineOpens) :
    RingHom.ker ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U.1)).hom =
      Ideal.map (I.subschemeι.app U.1).hom (J.ideal U) :=
  (Scheme.Hom.ker_apply (Scheme.IdealSheafData.inclusion h)
    ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩).symm.trans (ker_inclusion_ideal h U)

/-- The chart identification `Γ(𝒪_X/I, I.subschemeι ⁻¹ᵁ U) ≅ Γ(X, U) ⧸ I.ideal U` of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso` turns the section map of
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` into the quotient map. -/
theorem subschemeObjIso_hom_comp_subschemeι_app (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.subschemeObjIso U).hom.hom.comp (I.subschemeι.app U.1).hom =
      Ideal.Quotient.mk (I.ideal U) := by
  rw [congrArg CommRingCat.Hom.hom (I.subschemeι_app U)]
  exact congrArg CommRingCat.Hom.hom
    (by simp : (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫ (I.subschemeObjIso U).inv) ≫
      (I.subschemeObjIso U).hom = CommRingCat.ofHom _)

/-- **The defining ideal sheaf of an inclusion of closed subschemes is `J(U)/I(U)`.** Transported
along the chart identification
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso`, the kernel computed by
`Stacks.ClosedImmersion.ker_app_inclusion` is the image of `J.ideal U` in `Γ(X, U) ⧸ I.ideal U`. -/
theorem map_ker_app_inclusion (h : I ≤ J) (U : X.affineOpens) :
    Ideal.map (I.subschemeObjIso U).hom.hom
        (RingHom.ker ((Scheme.IdealSheafData.inclusion h).app (I.subschemeι ⁻¹ᵁ U.1)).hom) =
      Ideal.map (Ideal.Quotient.mk (I.ideal U)) (J.ideal U) := by
  rw [ker_app_inclusion h U, Ideal.map_map, subschemeObjIso_hom_comp_subschemeι_app]

/-- **`J.ideal U` is recovered from the defining ideal sheaf of the inclusion.** The contraction
along the chart map `Γ(X, U) ⟶ Γ(𝒪_X/I, I.subschemeι ⁻¹ᵁ U)` of the ideal that the defining ideal
sheaf of the inclusion assigns to the chart is `J.ideal U`. -/
theorem comap_ker_inclusion_ideal (h : I ≤ J) (U : X.affineOpens) :
    Ideal.comap (I.subschemeι.app U.1).hom
        ((Scheme.IdealSheafData.inclusion h).ker.ideal
          ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) = J.ideal U := by
  rw [ker_inclusion_ideal h U, Ideal.comap_map_of_surjective _ (I.subschemeι_app_surjective U),
    ← RingHom.ker_eq_comap_bot, I.ker_subschemeι_app U, sup_eq_left]
  exact Scheme.IdealSheafData.le_def.mp h U

/-- **The ideal of one of two covering closed subschemes is that of their intersection in the
other.** If the closed subschemes cut out by `I` and `J` cover `X` scheme-theoretically,
`I ⊓ J = ⊥`, and `K` cuts out their intersection, `K = I ⊔ J`, then over every affine open `U`
restriction to the subscheme cut out by `J` maps `I(U)` bijectively onto the ideal of the
intersection in that subscheme. On quasi-coherent ideal sheaves this says that the ideal sheaf of
`I` is the direct image of the ideal sheaf of the intersection inside the subscheme cut out by
`J`. -/
theorem bijOn_subschemeι_app_ideal_ker_inclusion {K : X.IdealSheafData} (hbot : I ⊓ J = ⊥)
    (hIK : I ≤ K) (hJK : J ≤ K) (hK : K ≤ I ⊔ J) (U : X.affineOpens) :
    Set.BijOn (J.subschemeι.app U.1) (I.ideal U)
      ((Scheme.IdealSheafData.inclusion hJK).ker.ideal
        ⟨J.subschemeι ⁻¹ᵁ U.1, U.2.preimage _⟩) := by
  rw [ker_inclusion_ideal]
  refine ⟨fun a ha => Ideal.mem_map_of_mem _ (hIK U ha),
    fun a ha b hb hab => ?_, fun t ht => ?_⟩
  · have hsub : a - b ∈ J.ideal U := by
      rw [← J.ker_subschemeι_app U, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hab
    have hmem : a - b ∈ (I ⊓ J).ideal U := ⟨(I.ideal U).sub_mem ha hb, hsub⟩
    rw [hbot] at hmem
    exact sub_eq_zero.mp hmem
  · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (J.subschemeι_app_surjective U)).mp ht
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (hK U hx)
    refine ⟨b, hb, ?_⟩
    have hc0 : J.subschemeι.app U.1 c = 0 := by
      rw [← RingHom.mem_ker, J.ker_subschemeι_app U]
      exact hc
    rw [map_add, hc0, add_zero]

end Stacks.ClosedImmersion

end
