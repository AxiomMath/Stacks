module

public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Unconditional
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeFieldExtension
public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
import all StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.BaseChange

/-!
# The degree of the dualizing sheaf on a subcurve, and rational tails

Let `X` be a proper scheme of dimension one over a field `k`, let `C ⊆ X` be a closed subscheme
whose global functions form a field `k' ⊇ k`, and let `X'` be the closure of the complement of
`C`. For an invertible extension `ℒ` of `𝒪_{C ∩ X'}` by `ω_C` (for instance `ℒ = ω_X|_C`, by
[Stacks, Tag 0E34]) one has `deg ℒ = deg(C ∩ X') - 2 χ(C, 𝒪_C)`, and both `deg(C ∩ X')` and
`dim_k H¹(C, 𝒪_C)` are multiples of `[k' : k]`. Hence if `deg ℒ < dim_k H¹(C, 𝒪_C)` and `C ∩ X'`
is nonempty, then `C ∩ X'` is a single `k'`-rational point and `H¹(C, 𝒪_C) = 0`. This is the
numerical core of the proof of [Stacks, Tag 0E3J].

## Main results

* `AlgebraicGeometry.finrank_globalSections_intersection_eq_mul`: `deg(C ∩ X')` is
  `[k' : k]` times its dimension over `k'`.
* `AlgebraicGeometry.finrank_cohomologyOverField_one_unit_eq_mul_genus`:
  `dim_k H¹(C, 𝒪_C) = [k' : k] g'`, with `g'` the genus of `C` over `k'`.
* `AlgebraicGeometry.isRationalTail_of_finrank_globalSections_intersection_eq_one`: an integral
  subcurve meeting the rest in one `k'`-rational point, of genus zero, is a rational tail.
* `AlgebraicGeometry.exists_componentDegree_neg_of_invertibleCurveDegree_neg` and
  `AlgebraicGeometry.exists_idealSheafData_componentDegree`: an invertible module of negative
  degree on a subcurve has negative degree on an integral component of it ([Stacks, Tag 0AYW]).
* `AlgebraicGeometry.finrank_globalSections_intersection_eq_one_of_invertibleCurveDegree_lt`:
  if `deg ℒ < dim_k H¹(C, 𝒪_C)` and `C ∩ X'` is nonempty, then `Γ(C ∩ X', 𝒪)` is
  one-dimensional over `k'` and `g' = 0`.

## References

* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **`deg(C ∩ X')` is a multiple of `[k' : k]`.** If `C ⟶ Spec k` factors through `Spec k'`, the
global functions of `C ∩ X'` are a `k'`-algebra and the `k`-structure is restricted from it. -/
theorem finrank_globalSections_intersection_eq_mul (C : X.IdealSheafData)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      C.subschemeι ≫ (X ↘ Spec (.of k))) :
    letI : Algebra k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
          (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    letI : Algebra k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f').appTop).hom.toAlgebra
    Module.finrank k Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) =
      Module.finrank k k' *
        Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) := by
  let I := intersectionWithComplementaryCurveIdeal C
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra k' Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (iC ≫ f').appTop).hom.toAlgebra
  have hI : I.subschemeι ≫ (X ↘ Spec (.of k)) =
      iC ≫ f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) := by
    rw [hf, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have : IsScalarTower k k' Γ(I.subscheme, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom r =
      ((Scheme.ΓSpecIso (.of k')).inv ≫ (iC ≫ f').appTop).hom (algebraMap k k' r)
    rw [hI, ← Category.assoc iC, Scheme.Hom.comp_appTop (iC ≫ f'), ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  exact (Module.finrank_mul_finrank k k' Γ(I.subscheme, ⊤)).symm

/-- **`dim_k H¹(C, 𝒪_C) = [k' : k] g'`** for `C ⟶ Spec k` factoring through `Spec k'`, with `g'`
the genus of `C` over `k'`. -/
theorem finrank_cohomologyOverField_one_unit_eq_mul_genus (k' : Type u) [Field k'] [Algebra k k']
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) (f' : Y ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = g) :
    Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) 1) =
      Module.finrank k k' * genus f' := by
  subst hf
  exact (finrank_cohomologyOverField_comp_SpecMap k k' f' _ 1).trans
    (congrArg (Module.finrank k k' * ·) (finrank_cohomologyOverField_one_unit_eq_genus k' f'))

/-- **`χ(C, 𝒪_C) = [k' : k](1 - g')`** for `C` proper of dimension at most one over `k` with
`C ⟶ Spec k` factoring through `Spec k'` and inducing `k' ≅ Γ(C, 𝒪_C)`. -/
theorem finsum_finrank_unit_eq_mul_one_sub_genus (k' : Type u) [Field k'] [Algebra k k']
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1)
    (f' : Y ⟶ Spec (.of k')) (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = g)
    [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)] :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        (Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ)) =
      (Module.finrank k k' : ℤ) * (1 - genus f') := by
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k g
      (SheafOfModules.unit Y.ringCatSheaf) (isZero_cohomologyOverField_two_le k g hdim _),
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k g,
    finrank_globalSections_eq_finrank_of_factor k' g f' hf,
    finrank_cohomologyOverField_one_unit_eq_mul_genus k' g f' hf]
  push_cast
  ring

/-- **If `deg ℒ < dim_k H¹(C, 𝒪_C)`, then `C ∩ X'` is a single `k'`-rational point and `C` has
genus zero over `k'`.** Let `ℒ` be an invertible extension of `𝒪_{C ∩ X'}` by `ω_C` on a closed
subscheme `C` of a proper curve over `k`, where `C ⟶ Spec k` factors through `Spec k'` inducing
`k' ≅ Γ(C, 𝒪_C)` and `ω_C` is invertible over `k'`, and suppose `C ∩ X'` is nonempty. Writing
`d = [k' : k]`, `a = dim_{k'} Γ(C ∩ X', 𝒪)` and `g'` for the genus over `k'`, the degree is
`d a - 2 d (1 - g')` and `dim_k H¹(C, 𝒪_C) = d g'`, so the inequality forces `a + g' < 2`, while
`a ≥ 1` as `C ∩ X'` is nonempty. This is the numerical step of [Stacks, Tag 0E3J]. -/
theorem finrank_globalSections_intersection_eq_one_of_invertibleCurveDegree_lt
    [IsProper (X ↘ Spec (.of k))]
    (C : X.IdealSheafData) (hCdim : topologicalKrullDim C.subscheme ≤ 1)
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f')]
    {S : ShortComplex C.subscheme.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible C.subscheme.presheaf C.subscheme.ringCatSheaf.2 S.X₂]
    (e₁ : S.X₁ ≅ Stacks.Duality.dualizingSheafOverField (C.subschemeι ≫ (X ↘ Spec (.of k))))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C))).obj
        (SheafOfModules.unit _))
    (hX : topologicalKrullDim X ≤ 1)
    (hne : Nonempty (intersectionWithComplementaryCurveIdeal C).subscheme)
    (hlt : invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim S.X₂ <
      Module.finrank k (cohomologyOverField k (C.subschemeι ≫ (X ↘ Spec (.of k)))
        (SheafOfModules.unit C.subscheme.ringCatSheaf) 1)) :
    letI : Algebra k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f').appTop).hom.toAlgebra
    Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) = 1 ∧
      genus f' = 0 := by
  let I := intersectionWithComplementaryCurveIdeal C
  let : Algebra k Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra k' Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ I) ≫ f').appTop).hom.toAlgebra
  have : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k
      (X ↘ Spec (.of k))
  have hdeg := invertibleCurveDegree_eq_sub_two_mul_of_shortExact C hCdim k' f' hf hS e₁ e₃
  have hP := finsum_alternating_finrank_unit_eq_finrank_of_topologicalKrullDim_le_zero
    (I.subschemeι ≫ (X ↘ Spec (.of k)))
    (topologicalKrullDim_intersectionWithComplementaryCurve_le_zero hX C)
  have hO := finsum_finrank_unit_eq_mul_one_sub_genus k' _ hCdim f' hf
  have hh1 := finrank_cohomologyOverField_one_unit_eq_mul_genus k' _ f' hf
  have hmul := finrank_globalSections_intersection_eq_mul C k' f' hf
  obtain ⟨pt⟩ := hne
  have : Nontrivial Γ(I.subscheme, ⊤) :=
    Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty I.subscheme pt
  have : FiniteDimensional k Γ(I.subscheme, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k
      (I.subschemeι ≫ (X ↘ Spec (.of k))) 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k
      (I.subschemeι ≫ (X ↘ Spec (.of k)))
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).toLinearEquiv
  have hpos : 0 < Module.finrank k Γ(I.subscheme, ⊤) := Module.finrank_pos
  rw [hmul] at hpos
  have hd' : (0 : ℤ) < Module.finrank k k' := by exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have ha : 0 < Module.finrank k' Γ(I.subscheme, ⊤) := Nat.pos_of_mul_pos_left hpos
  rw [hdeg, hP, hO, hh1, hmul] at hlt
  push_cast at hlt
  have hsum : (Module.finrank k' Γ(I.subscheme, ⊤) : ℤ) + genus f' < 2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h1 : Module.finrank k' Γ(I.subscheme, ⊤) = 1 := by omega
  exact ⟨h1, by omega⟩

/-- **An integral one-dimensional closed subcurve meeting the rest of the curve in one
`k'`-rational point, with genus zero, is a rational tail.** Let `C ⊊ X` be integral of dimension
one in a proper curve of dimension at most one over `k`, with `C ⟶ Spec k` factoring through
`Spec k'` and inducing `k' ≅ Γ(C, 𝒪_C)`. If `Γ(C ∩ X', 𝒪)` is one-dimensional over `k'` and `C`
has genus zero over `k'`, then `C` is a rational tail: `C ∩ X'` is finite over `k`, hence affine,
so it is `Spec k'`, which is the reduced attaching point of
`AlgebraicGeometry.exists_isIso_Γevaluation_of_isIso_inclusion_comp`. This is the last step of
the proof of [Stacks, Tag 0E3J]. -/
theorem isRationalTail_of_finrank_globalSections_intersection_eq_one
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1)
    (C : X.IdealSheafData) [IsIntegral C.subscheme] (hCdim : topologicalKrullDim C.subscheme = 1)
    (hne : Nonempty (complementaryCurve C))
    (k' : Type u) [Field k'] [Algebra k k'] (f' : C.subscheme ⟶ Spec (.of k'))
    (hf : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = C.subschemeι ≫ (X ↘ Spec (.of k)))
    [IsProper f'] [IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)]
    (h1 :
      letI : Algebra k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k')).inv ≫ (Scheme.IdealSheafData.inclusion
          (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫ f').appTop).hom.toAlgebra
      Module.finrank k' Γ((intersectionWithComplementaryCurveIdeal C).subscheme, ⊤) = 1)
    (hg : genus f' = 0) :
    IsRationalTail k X C := by
  let I := intersectionWithComplementaryCurveIdeal C
  let iC := Scheme.IdealSheafData.inclusion (le_sup_left : C ≤ I)
  let : Algebra k' Γ(I.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (iC ≫ f').appTop).hom.toAlgebra
  have : IsNoetherian X :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k
      (X ↘ Spec (.of k))
  have : Nontrivial Γ(I.subscheme, ⊤) := Module.nontrivial_of_finrank_eq_succ h1
  have hbij : Function.Bijective (algebraMap k' Γ(I.subscheme, ⊤)) := by
    refine ⟨(algebraMap k' Γ(I.subscheme, ⊤)).injective, ?_⟩
    show Function.Surjective (Algebra.linearMap k' Γ(I.subscheme, ⊤))
    have : FiniteDimensional k' Γ(I.subscheme, ⊤) := Module.finite_of_finrank_eq_succ h1
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [h1, Module.finrank_self])).mp (algebraMap k' Γ(I.subscheme, ⊤)).injective
  have : IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ (iC ≫ f').appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (iC ≫ f').appTop :=
    IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k')).inv (iC ≫ f').appTop
  have : IsFinite (I.subschemeι ≫ (X ↘ Spec (.of k))) :=
    isFinite_of_isProper_of_topologicalKrullDim_le_zero _
      (topologicalKrullDim_intersectionWithComplementaryCurve_le_zero hX C)
  have : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ (X ↘ Spec (.of k)))
  have : IsIso (iC ≫ f') :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
      (arrowIsoSpecΓOfIsAffine (iC ≫ f'))).mpr
        (inferInstanceAs (IsIso (Spec.map (iC ≫ f').appTop)))
  obtain ⟨x, hx, hI, hΓ⟩ := exists_isIso_Γevaluation_of_isIso_inclusion_comp C k' f'
  exact ⟨inferInstance, support_mem_irreducibleComponents_of_dimension_one C hX hCdim, hne, x, hx,
    hI, hΓ, genus_eq_zero_of_genus_eq_zero f' _ hg⟩

/-- **An invertible module of negative degree on a curve has negative degree on some reduced
component.** By [Stacks, Tag 0AYW] the degree is the multiplicity-weighted sum of the degrees on
the reduced one-dimensional components, and multiplicities are nonnegative. -/
theorem exists_componentDegree_neg_of_invertibleCurveDegree_neg {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1) (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hneg : invertibleCurveDegree k g hdim L < 0) :
    ∃ ξ : Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y,
      Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree k g hdim L 1 ξ < 0 := by
  classical
  rw [invertibleCurveDegree_eq_curveDegree,
    Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree_of_isProper]
    at hneg
  by_contra hcon
  push Not at hcon
  have : IsNoetherian Y :=
    Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k g
  have : Finite (Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y) :=
    (Stacks.AlgebraicGeometry.ComponentDegrees.finite_genericPointsOne Y).to_subtype
  exact absurd hneg <| not_lt.mpr <| finsum_nonneg fun ξ => mul_nonneg (by positivity) (hcon ξ)

/-- **The degree of an invertible module is unchanged by an isomorphism of curves over `k`.**
This is [Stacks, Tag 0B59] for the trivial extension `k = k`, the isomorphism being a base change
along the identity of `Spec k`. -/
theorem invertibleCurveDegree_pullback_of_isIso {A B : Scheme.{u}} (e : A ⟶ B) [IsIso e]
    (g : B ⟶ Spec (.of k)) [IsProper g] (hA : topologicalKrullDim A ≤ 1)
    (hB : topologicalKrullDim B ≤ 1) (L : B.Modules)
    [SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 L] :
    invertibleCurveDegree k (e ≫ g) hA ((Scheme.Modules.pullback e).obj L) =
      invertibleCurveDegree k g hB L := by
  have hsq : IsPullback e (e ≫ g) g (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) by simp]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [invertibleCurveDegree_eq_curveDegree, invertibleCurveDegree_eq_curveDegree]
  exact curveDegree_baseChange_field k k e (e ≫ g) g hsq hB L 1

/-- **A reduced component of a closed subscheme, as a closed subscheme of the ambient scheme.**
For a closed subscheme `Y` of `X` and a one-dimensional component `ξ` of `Y`, the kernel `C` of
the composite closed immersion is an integral one-dimensional closed subscheme of `X` contained
in `Y`, and the degree over `k` of an invertible `ℳ` restricted to `C` is its component degree on
`Y`. -/
theorem exists_idealSheafData_componentDegree [IsProper (X ↘ Spec (.of k))]
    (Y : X.IdealSheafData) (hYdim : topologicalKrullDim Y.subscheme ≤ 1) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (ξ : Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne Y.subscheme) :
    ∃ (C : X.IdealSheafData) (_ : IsIntegral C.subscheme)
      (hCdim : topologicalKrullDim C.subscheme = 1),
      (C.support : Set X) ⊆ Y.support ∧
        invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le
            ((Scheme.Modules.pullback C.subschemeι).obj M) =
          Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree k
            (Y.subschemeι ≫ (X ↘ Spec (.of k))) hYdim
            ((Scheme.Modules.pullback Y.subschemeι).obj M) 1 ξ := by
  let ρ := Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι Y.subscheme ξ
  let j := ρ ≫ Y.subschemeι
  let C := j.ker
  let e : Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent Y.subscheme ξ ≅ C.subscheme :=
    asIso j.toImage
  have he : e.hom ≫ C.subschemeι = j := j.toImage_imageι
  have := Stacks.AlgebraicGeometry.ComponentDegrees.isIntegral_reducedComponent Y.subscheme ξ
  have : IsIntegral C.subscheme := IsIntegral.of_isIso e.hom
  have hdimρ := Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_reducedComponent
    Y.subscheme ξ
  have hCdim : topologicalKrullDim C.subscheme = 1 := by
    rwa [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
  have hsub : (C.support : Set X) ⊆ Y.support := by
    rw [← C.range_subschemeι, ← Y.range_subschemeι]
    rintro _ ⟨c, rfl⟩
    refine ⟨ρ (e.inv c), ?_⟩
    have hc : C.subschemeι c = j (e.inv c) := by
      rw [← he]
      simp
    rw [hc]
    rfl
  refine ⟨C, inferInstance, hCdim, hsub, ?_⟩
  rw [← invertibleCurveDegree_pullback_of_isIso e.hom (C.subschemeι ≫ (X ↘ Spec (.of k)))
    hdimρ.le hCdim.le ((Scheme.Modules.pullback C.subschemeι).obj M)]
  have hg : e.hom ≫ C.subschemeι ≫ (X ↘ Spec (.of k)) =
      ρ ≫ Y.subschemeι ≫ (X ↘ Spec (.of k)) := by
    rw [← Category.assoc, he]
    rfl
  have iso : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback C.subschemeι).obj M) ≅
      (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback Y.subschemeι).obj M) :=
    (Scheme.Modules.pullbackComp e.hom C.subschemeι).app M ≪≫
      (Scheme.Modules.pullbackCongr he).app M ≪≫
      ((Scheme.Modules.pullbackComp ρ Y.subschemeι).app M).symm
  unfold Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree
  rw [← invertibleCurveDegree_eq_curveDegree, invertibleCurveDegree_eq_of_iso k _ _ iso]
  congr 1

end AlgebraicGeometry

end
