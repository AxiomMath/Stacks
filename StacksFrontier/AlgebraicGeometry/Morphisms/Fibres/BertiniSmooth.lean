module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFamilyDivisors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# Smooth Bertini for a linear system

Let `X` be a scheme smooth over a field `k`, let `V` be a finite dimensional linear system of
sections of an invertible module on `X`, and let `q : H_univ → 𝔸^r_k` be the projection from the
universal divisor. If the non-smooth locus of `q` misses the preimage of a nonempty open of
`𝔸^r_k`, then the divisor `H_v` cut out by `v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.universalFamilyMap`: the morphism `q : H_univ → 𝔸^r_k`.
* `Stacks.Bertini.FamilyDivisors.specializedToUniversal`: the closed immersion `H_v → H_univ`.

## Main results

* `AlgebraicGeometry.smooth_restrict_of_subset_smoothLocus`: a morphism locally of finite
  presentation is smooth over the preimage of an open of the target that its non-smooth locus
  avoids.
* `AlgebraicGeometry.smooth_of_isPullback_of_subset_smoothLocus`: a base change of such a
  morphism along a map landing in that open is smooth.
* `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_comap`: the closed subscheme of a
  pulled-back ideal sheaf is the fibred product of the closed subscheme with the base.
* `Stacks.Bertini.FamilyDivisors.locallyOfFinitePresentation_universalFamilyMap`:
  `q : H_univ → 𝔸^r_k` is locally of finite presentation when `X` is smooth over `k`.
* `Stacks.Bertini.FamilyDivisors.isPullback_universalFamilyMap`: `H_v` is the fibre of
  `q : H_univ → 𝔸^r_k` over the `k'`-point of `𝔸^r_k` determined by the coordinate tuple of `v`.
* `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral`: for general `v` the
  divisor `H_v` is smooth over `k'`, given the hypothesis `hsing` on the non-smooth locus of `q`.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- If `g` is locally of finite presentation and every point of `g ⁻¹ᵁ W` lies in the smooth
locus of `g`, then the restriction of `g` to that open is smooth. -/
public theorem smooth_restrict_of_subset_smoothLocus {A B : Scheme.{u}} (g : A ⟶ B)
    [LocallyOfFinitePresentation g] (W : B.Opens)
    (hW : ((g ⁻¹ᵁ W : A.Opens) : Set A) ⊆ (g.smoothLocus : Set A)) :
    Smooth ((g ⁻¹ᵁ W).ι ≫ g) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
  exact fun x _ => hW x.2

/-- If `g` is locally of finite presentation, its non-smooth locus misses `g ⁻¹ᵁ W`, and the square
with corners `F, A, T, B` is cartesian over a morphism `t : T ⟶ B` whose image lies in `W`, then
`F ⟶ T` is smooth. -/
public theorem smooth_of_isPullback_of_subset_smoothLocus {A B T F : Scheme.{u}}
    (g : A ⟶ B) [LocallyOfFinitePresentation g] (W : B.Opens)
    (hW : ((g ⁻¹ᵁ W : A.Opens) : Set A) ⊆ (g.smoothLocus : Set A))
    (t : T ⟶ B) (ht : ∀ p : T, t p ∈ W) (c : F ⟶ A) (h : F ⟶ T)
    (hsq : IsPullback c h g t) : Smooth h := by
  have hrange : Set.range c ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show g (c x) ∈ W
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
    exact ht _
  have hbig := (IsOpenImmersion.isPullback_lift_id c (g ⁻¹ᵁ W).ι hrange).paste_vert hsq
  rw [Category.id_comp] at hbig
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hbig
    (smooth_restrict_of_subset_smoothLocus g W hW)

/-- The closed subscheme of a pulled-back ideal sheaf is a fibred product: the square formed by
`(I.comap f).subscheme`, `I.subscheme`, the two closed immersions and `f` is cartesian. -/
public theorem Scheme.IdealSheafData.isPullback_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) :
    IsPullback (I.comap f).subschemeι (subschemeMap _ _ f (I.le_map_comap f)) f I.subschemeι :=
  IsPullback.of_iso_pullback ⟨(subschemeMap_subschemeι _ _ f _).symm⟩ (I.comapIso f)
    (I.comapIso_hom_fst f) (I.comapIso_hom_snd f)

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- The morphism `q : H_univ → 𝔸^r_k`: the closed immersion of the universal divisor into
`𝔸^r_X`, followed by the projection `𝔸^r_X = 𝔸^r_k ×_k X → 𝔸^r_k`. -/
public def universalFamilyMap : D.universalDivisor.subscheme ⟶ D.parameterBase :=
  D.universalDivisor.subschemeι ≫ AffineSpace.map D.basisIndex D.toBase

/-- The parameter space `𝔸^r_k` is locally Noetherian. -/
public instance isLocallyNoetherian_parameterBase : IsLocallyNoetherian D.parameterBase :=
  isLocallyNoetherian_of_isOpenImmersion (AffineSpace.SpecIso D.basisIndex (.of D.k)).hom

/-- The morphism `q : H_univ → 𝔸^r_k` is locally of finite presentation when `X` is smooth over
`k`. -/
public instance locallyOfFinitePresentation_universalFamilyMap [Smooth D.toBase] :
    LocallyOfFinitePresentation D.universalFamilyMap :=
  haveI : LocallyOfFiniteType D.universalFamilyMap := D.locallyOfFiniteType_universalFamily
  inferInstance

variable (K : Type u) [Field K] [Algebra D.k K]

/-- The closed immersion `H_v → H_univ` of the divisor of a vector into the universal divisor,
over the classifying morphism `X_{k'} → 𝔸^r_X` of its coordinate tuple. -/
public def specializedToUniversal (a : Fin (Module.finrank D.k D.V) → K) :
    (D.universalDivisor.comap (D.fibreParameterMap K a)).subscheme ⟶
      D.universalDivisor.subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ (D.fibreParameterMap K a)
    (D.universalDivisor.le_map_comap _)

/-- `H_v` is the fibre of `q : H_univ → 𝔸^r_k` over the `k'`-point of `𝔸^r_k` determined by the
coordinate tuple of `v`: the square of `H_v`, `H_univ`, `Spec k'` and `𝔸^r_k` is cartesian. -/
public theorem isPullback_universalFamilyMap (a : Fin (Module.finrank D.k D.V) → K) :
    IsPullback (D.specializedToUniversal K a)
      ((D.universalDivisor.comap (D.fibreParameterMap K a)).subschemeι ≫ D.baseChangeToSpec K)
      D.universalFamilyMap (D.parameterPoint a) :=
  ((D.universalDivisor.isPullback_comap (D.fibreParameterMap K a)).flip).paste_vert
    (D.isPullback_fibreParameterMap K a)

/-- A vector of `V ⊗_k k'` determines its coordinate tuple in the basis
`v₁ ⊗ 1, …, v_r ⊗ 1`. -/
public theorem coord_injective {a b : Fin (Module.finrank D.k D.V) → K}
    (h : ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) =
      ∑ i, TensorProduct.tmul D.k (D.basis i) (b i)) : a = b := by
  have h' := congrArg (TensorProduct.comm D.k D.V K) h
  simp only [map_sum, TensorProduct.comm_tmul] at h'
  funext j
  have h'' := congrArg (fun z => (D.basis.baseChange K).repr z j) h'
  simpa [Module.Basis.repr_self_apply, eq_comm] using h''

/-- In the standing situation of `Stacks.Bertini.FamilyDivisors` with `X` smooth over `k`, the
divisor `H_v` is smooth over `k'` for general `v ∈ V ⊗_k k'`.

It takes as hypothesis `hsing`: there is a nonempty open `U` of `𝔸^r_k` whose preimage under
`q : H_univ → 𝔸^r_k` lies in the smooth locus of `q`. It also takes the instance argument
`LocallyOfFinitePresentation q`, which `locallyOfFinitePresentation_universalFamilyMap` supplies
from the smoothness of `X` over `k`. -/
@[stacks 0FD6 "carrying the Tag 0B2L dimension bound on the singular locus of q"]
public theorem smooth_specializedDivisor_forGeneral [Smooth D.toBase]
    [LocallyOfFinitePresentation D.universalFamilyMap]
    (U : D.parameterBase.Opens) (hU : (U : Set D.parameterBase).Nonempty)
    (hsing : ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisor.subscheme.Opens) :
        Set D.universalDivisor.subscheme) ⊆
      (D.universalFamilyMap.smoothLocus : Set D.universalDivisor.subscheme)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  refine ⟨U, hU, fun K _ _ a ha a' ha' => ?_⟩
  obtain rfl : a = a' := D.coord_injective K ha'
  rw [D.specializedDivisor_eq_comap K a]
  exact smooth_of_isPullback_of_subset_smoothLocus D.universalFamilyMap U hsing
    (D.parameterPoint a) ha (D.specializedToUniversal K a) _
    (D.isPullback_universalFamilyMap K a)

end Stacks.Bertini.FamilyDivisors

end
