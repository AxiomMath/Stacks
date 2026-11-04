module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafRank
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GenericPointSupport
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# More vanishing results: twisting by the ideal of a zero-dimensional subscheme

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — assume `X` integral of genus `g`, let `ℒ` be invertible and let `Z ⊆ X` be a
closed subscheme of dimension at most zero with ideal sheaf `ℐ_Z`. This file studies the twist
`ℐ_Z ℒ = ℒ ⊗ ℐ_Z` and proves [Stacks, Tag 0E3A]:

  `H^1(X, ℐ_Z ℒ) ≠ 0 ⟹ deg(ℒ) ≤ 2g - 2 + deg(Z)`, with strict inequality unless `ℐ_Z ℒ ≅ ω_X`.

## Main definitions

* `AlgebraicGeometry.CohenMacaulayCurveSituation.idealSheafModule`: the ideal sheaf `ℐ_Z`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.idealTwist`: the module `ℐ_Z ℒ = ℒ ⊗ ℐ_Z`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.idealTwistι`: its inclusion into `ℒ`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.subschemeDegree`: `deg(Z) = dim_k Γ(Z, 𝒪_Z)`.

## Main results

* `mono_idealTwistι`: `ℐ_Z ℒ ⟶ ℒ` is injective.
* `eulerCharacteristic_idealTwist`: `χ(X, ℐ_Z ℒ) = deg(ℒ) + 1 - g - deg(Z)`.
* `exists_mono_idealTwist_dualizingSheaf`: a nonvanishing `H^1(X, ℐ_Z ℒ)` gives an injective map
  `ℐ_Z ℒ ⟶ ω_X`.
* `invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist`: the degree bound.
* `nonempty_iso_dualizingSheaf_of_invertibleCurveDegree_eq`: the equality case.
* `invertibleCurveDegree_le_and_lt_or_nonempty_iso_of_not_isZero_cohomology_idealTwist`:
  **[Stacks, Tag 0E3A]**.

## Implementation notes

The tensor product is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, with the
invertible factor first, the order in which Riemann-Roch [Stacks, Tag 0AYV] is stated; it is
tensoring on the left by `ℒ`, which is an equivalence of categories, whence the injectivity of
`ℐ_Z ℒ ⟶ ℒ`. The ideal sheaf is `Stacks.ClosedImmersion.idealSheaf`, the kernel of
`𝒪_X ⟶ i_* 𝒪_Z`, and `ω_X` is `Stacks.Duality.dualizingSheafOverField`.

The degree bound needs no more than the source's first two steps: a nonzero map `ℐ_Z ℒ ⟶ ω_X`
from duality, which is injective, so that `h^0(ℐ_Z ℒ) ≤ h^0(ω_X) = g`, while `h^1(ℐ_Z ℒ) ≥ 1`.
In the equality case these become `h^0(ℐ_Z ℒ) = g` and `h^1(ℐ_Z ℒ) = 1`, so the cokernel `𝒬` of
`ℐ_Z ℒ ⟶ ω_X` has no global sections. The source concludes from the zero-dimensionality of
`Supp 𝒬`, which it derives from the invertibility of `ω_X` on the Gorenstein locus; here the same
role is played by the rank bound of
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingSheafRank.lean`, which is proved
from duality and Riemann-Roch.

## References

* [Stacks Project, Tag 0E3A](https://stacks.math.columbia.edu/tag/0E3A)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- **The twist `ℐ_Z ℒ = ℒ ⊗ ℐ_Z`** of a module `ℒ` by the ideal sheaf of a closed subscheme
`Z`. -/
abbrev idealTwist (Z : S.X.IdealSheafData) (L : S.X.Modules) : S.X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨S.X.toRingedSpace.presheaf, S.X.toRingedSpace.IsSheaf⟩).obj L).obj
    (Stacks.ClosedImmersion.idealSheaf Z.subschemeι.toLRSHom.toShHom))

/-- **The degree `deg(Z) = dim_k Γ(Z, 𝒪_Z)`** of a closed subscheme `Z` of `X`, for the
`k`-algebra structure the structure morphism induces. -/
abbrev subschemeDegree (Z : S.X.IdealSheafData) : ℕ :=
  letI : Algebra S.k Γ(Z.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (Z.subschemeι ≫ S.f).appTop).hom.toAlgebra
  Module.finrank S.k Γ(Z.subscheme, ⊤)

/-- The ideal sheaf `ℐ_Z` of a closed subscheme, the kernel of `𝒪_X ⟶ i_* 𝒪_Z`. -/
abbrev idealSheafModule (Z : S.X.IdealSheafData) : S.X.Modules :=
  Stacks.ClosedImmersion.idealSheaf Z.subschemeι.toLRSHom.toShHom

/-- The structure sheaf of `X`, as a module over the structure sheaf of the underlying ringed
space, is coherent. -/
theorem isCoherent_unit_ringedSpace :
    (SheafOfModules.unit (structureSheafRing S.X.toRingedSpace)).IsCoherent :=
  Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k S.f

/-- **The ideal sheaf of a closed subscheme of `X` is coherent**: it is the kernel of a map
between the coherent modules `𝒪_X` and `i_* 𝒪_Z`. -/
theorem isCoherent_idealSheafModule (Z : S.X.IdealSheafData) :
    (S.idealSheafModule Z).IsCoherent := by
  have := S.isCoherent_unit_ringedSpace
  have : ((RingedSpaceModuleAdjunction.modulePushforward Z.subschemeι.toLRSHom.toShHom).obj
      (SheafOfModules.unit (structureSheafRing Z.subscheme.toRingedSpace))).IsCoherent :=
    Stacks.Chow.isCoherent_pushforwardStructureSheaf Z.subschemeι
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_kernel
    (Stacks.IdealSheafSequence.divisorQuotientMap Z)

/-- **The twist `ℐ_Z ℒ` of an invertible module by the ideal of a closed subscheme is
coherent.** -/
theorem isCoherent_idealTwist [IsIntegral S.X] (Z : S.X.IdealSheafData) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    (S.idealTwist Z L).IsCoherent :=
  have := S.isCurve
  have := S.isCoherent_idealSheafModule Z
  isCoherent_tensorSheaf_of_isCurve S.k S.f L 1 (S.idealSheafModule Z)

/-- **The inclusion `ℐ_Z ℒ ⟶ ℒ`**: `ℒ ⊗ ℐ_Z ⟶ ℒ ⊗ 𝒪_X ≅ ℒ`. -/
def idealTwistι (Z : S.X.IdealSheafData) (L : S.X.Modules) : S.idealTwist Z L ⟶ L :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf (forget₂ CommRingCat RingCat)
        S.X.ringCatSheaf.2⟩).obj L)).map
      (Stacks.IdealSheafSequence.divisorIdealMap Z) ≫
    (SheafOfModules.tensorSheafUnitRightIso S.X.toRingedSpace L).hom

/-- **`ℐ_Z ℒ ⟶ ℒ` is injective**: tensoring with an invertible module is an equivalence of
categories, so it preserves the monomorphism `ℐ_Z ⟶ 𝒪_X`. -/
instance mono_idealTwistι (Z : S.X.IdealSheafData) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    Mono (S.idealTwistι Z L) := by
  have e := (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp ‹_›
  have h1 : Mono (Stacks.IdealSheafSequence.divisorIdealMap Z) :=
    (inferInstance : Mono (kernel.ι (Stacks.IdealSheafSequence.divisorQuotientMap Z)))
  have hpm : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf (forget₂ CommRingCat RingCat)
        S.X.ringCatSheaf.2⟩).obj L)).PreservesMonomorphisms :=
    @Functor.preservesMonomorphisms_of_isRightAdjoint _ _ _ _ _
      (@Functor.asEquivalence _ _ _ _ _ e).symm.toAdjunction.isRightAdjoint
  have h2 := @Functor.map_mono _ _ _ _ _ hpm _ _ _ h1
  exact @mono_comp _ _ _ _ _ _ h2 _
    (@IsIso.mono_of_iso _ _ _ _ _
      (SheafOfModules.tensorSheafUnitRightIso S.X.toRingedSpace L).isIso_hom)

/-! ### Euler characteristics -/

/-- **A closed subscheme of dimension at most zero misses the generic point**: otherwise it would
be all of the one-dimensional irreducible scheme `X`. -/
theorem genericPoint_notMem_range_subschemeι [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) :
    genericPoint S.X ∉ Set.range Z.subschemeι.base := by
  intro h
  have hcl : IsClosed (Set.range Z.subschemeι.base) :=
    Z.subschemeι.isClosedEmbedding.isClosed_range
  have huniv : Set.range Z.subschemeι.base = Set.univ := by
    by_contra hne
    exact notMem_of_isClosed_of_ne_univ _ hcl hne h
  have hhomeo : IsHomeomorph Z.subschemeι.base :=
    (isHomeomorph_iff_isEmbedding_surjective).mpr
      ⟨Z.subschemeι.isClosedEmbedding.isEmbedding, Set.range_eq_univ.mp huniv⟩
  have h1 := IsHomeomorph.topologicalKrullDim_eq _ hhomeo
  have h2 : topologicalKrullDim S.X = 1 := S.dimension_one
  rw [h1, h2] at hZ
  exact absurd hZ (by norm_num)

/-- **`χ(X, i_* 𝒪_Z) = deg(Z)`** for a closed subscheme `Z` of dimension at most zero: `Z` is
finite over `k`, hence affine, so its higher cohomology vanishes, and a closed immersion does not
change cohomology. -/
theorem eulerCharacteristic_pushforward_unit_subscheme (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) :
    @eulerCharacteristic S.k _ S.X S.f _
      ((Scheme.Modules.pushforward Z.subschemeι).obj (SheafOfModules.unit Z.subscheme.ringCatSheaf))
      (Stacks.Chow.isCoherent_pushforwardStructureSheaf Z.subschemeι) =
      (S.subschemeDegree Z : ℤ) := by
  have : IsFinite (Z.subschemeι ≫ S.f) := isFinite_of_isProper_of_topologicalKrullDim_le_zero _ hZ
  have : IsAffine Z.subscheme := isAffine_of_isAffineHom (Z.subschemeι ≫ S.f)
  have : (SheafOfModules.unit Z.subscheme.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have hvan : ∀ i : ℕ, 0 < i → IsZero (cohomologyOverField S.k S.f
      ((Scheme.Modules.pushforward Z.subschemeι).obj
        (SheafOfModules.unit Z.subscheme.ringCatSheaf)) i) := fun i hi =>
    ((isZero_cohomologyOverField_iff_isZero_hgroup S.k (Z.subschemeι ≫ S.f) _ i).mpr
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ _ ⊤ (isAffineOpen_top _) i hi)).of_iso
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion S.k Z.subschemeι S.f _ i).symm
  rw [eulerCharacteristic_eq_finsum,
    finsum_alternating_finrank_cohomologyOverField_eq_finrank_zero S.k S.f _ hvan]
  exact_mod_cast ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion S.k Z.subschemeι S.f _
      0).toLinearEquiv.finrank_eq.symm).trans
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections S.k (Z.subschemeι ≫ S.f))

/-- **`χ(X, ℐ_Z) = 1 - g - deg(Z)`**, from the ideal sequence `0 ⟶ ℐ_Z ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0`
and `χ(X, 𝒪_X) = 1 - g`. -/
theorem eulerCharacteristic_idealSheafModule (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) :
    @eulerCharacteristic S.k _ S.X S.f _ (S.idealSheafModule Z) (S.isCoherent_idealSheafModule Z) =
      1 - (genus S.f : ℤ) - (S.subschemeDegree Z : ℤ) := by
  obtain ⟨hz, hS⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact Z
  have h1 : SheafOfModules.IsCoherent
      (Stacks.ClosedImmersion.idealSheaf Z.subschemeι.toLRSHom.toShHom) :=
    S.isCoherent_idealSheafModule Z
  have h2 := S.isCoherent_unit_ringedSpace
  have h3 : ((RingedSpaceModuleAdjunction.modulePushforward Z.subschemeι.toLRSHom.toShHom).obj
      (SheafOfModules.unit (structureSheafRing Z.subscheme.toRingedSpace))).IsCoherent :=
    Stacks.Chow.isCoherent_pushforwardStructureSheaf Z.subschemeι
  have h := @eulerCharacteristic_add_of_shortExact S.k _ S.X S.f _ _ hS h1 h2 h3
  have := S.isCoherent_idealSheafModule Z
  change @eulerCharacteristic S.k _ S.X S.f _ (SheafOfModules.unit S.X.ringCatSheaf) _ =
    @eulerCharacteristic S.k _ S.X S.f _ (S.idealSheafModule Z) _ +
      @eulerCharacteristic S.k _ S.X S.f _ ((Scheme.Modules.pushforward Z.subschemeι).obj
        (SheafOfModules.unit Z.subscheme.ringCatSheaf)) _ at h
  rw [eulerCharacteristic_unit_eq_one_sub_genus S.k S.f (le_of_eq S.dimension_one),
    S.eulerCharacteristic_pushforward_unit_subscheme Z hZ] at h
  linarith

/-- **The ideal sheaf of a closed subscheme of dimension at most zero has rank one**: its stalk at
the generic point is the function field, since `i_* 𝒪_Z` vanishes there. -/
theorem fiberRank_idealSheafModule_genericPoint [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) :
    Scheme.Modules.fiberRank (S.idealSheafModule Z) (genericPoint S.X) = 1 := by
  obtain ⟨hz, hS⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact Z
  have hfield : IsField (S.X.presheaf.stalk (genericPoint S.X)) :=
    (inferInstance : Field S.X.functionField).toIsField
  have hlen := length_stalk_add_of_shortExact hS (genericPoint S.X)
  have := S.isCoherent_idealSheafModule Z
  have : (S.idealSheafModule Z).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have h1 := length_stalk_eq_fiberRank_of_isField (S.idealSheafModule Z) _ hfield
  have hO := length_stalk_eq_fiberRank_of_isField (structureSheafModule S.X) _ hfield
  rw [Scheme.Modules.fiberRank_unit_eq_one] at hO
  have hnot : genericPoint S.X ∉ SheafOfModules.supp ((Scheme.Modules.pushforward
      Z.subschemeι).obj (Stacks.Ample.unitModule Z.subscheme)) := by
    rw [Stacks.Chow.supp_pushforwardStructureSheaf]
    exact S.genericPoint_notMem_range_subschemeι Z hZ
  have h3 : ∀ M : S.X.Modules, genericPoint S.X ∉ SheafOfModules.supp M →
      Module.length (S.X.presheaf.stalk (genericPoint S.X))
        (M.presheaf.stalk (genericPoint S.X)) = 0 := fun M hM => by
    have := subsingleton_stalk_of_notMem_supp M hM
    exact Module.length_eq_zero
  have hQ := h3 (ShortComplex.mk _ _ hz).X₃ hnot
  rw [hQ, add_zero] at hlen
  rw [← h1]
  exact (congrArg ENat.toNat hlen.symm).trans hO

/-- **`χ(X, ℐ_Z ℒ) = deg(ℒ) + 1 - g - deg(Z)`**: Riemann-Roch [Stacks, Tag 0AYV] for the rank
one module `ℐ_Z`, together with `χ(X, ℐ_Z) = 1 - g - deg(Z)`. -/
theorem eulerCharacteristic_idealTwist [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    @eulerCharacteristic S.k _ S.X S.f _ (S.idealTwist Z L) (S.isCoherent_idealTwist Z L) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L + 1 - (genus S.f : ℤ) -
        (S.subschemeDegree Z : ℤ) := by
  have := S.isCurve
  have := S.isCoherent_idealSheafModule Z
  have h := eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add S.k S.f L 1
    (S.idealSheafModule Z) (S.isCoherent_idealTwist Z L)
  rw [S.fiberRank_idealSheafModule_genericPoint Z hZ, S.eulerCharacteristic_idealSheafModule Z hZ]
    at h
  rw [invertibleCurveDegree_eq_curveDegree]
  refine h.trans ?_
  push_cast
  ring

/-- **`Γ(Z, 𝒪_Z)` is finite dimensional over `k`** for a closed subscheme `Z` of a proper
`k`-scheme: it is `H^0(Z, 𝒪_Z)`. -/
theorem finiteDimensional_globalSections_subscheme (Z : S.X.IdealSheafData) :
    letI : Algebra S.k Γ(Z.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (Z.subschemeι ≫ S.f).appTop).hom.toAlgebra
    FiniteDimensional S.k Γ(Z.subscheme, ⊤) := by
  let : Algebra S.k Γ(Z.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (Z.subschemeι ≫ S.f).appTop).hom.toAlgebra
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k (Z.subschemeι ≫ S.f)
  have := finiteDimensional_cohomologyOverField_of_isProper S.k (Z.subschemeι ≫ S.f)
    (SheafOfModules.unit Z.subscheme.ringCatSheaf) 0
  exact LinearEquiv.finiteDimensional
    (cohomologyOverFieldZeroIsoSections S.k (Z.subschemeι ≫ S.f)
      (SheafOfModules.unit Z.subscheme.ringCatSheaf)).toLinearEquiv

/-! ### The degree bound -/

/-- **A nonzero map `ℐ_Z ℒ ⟶ ω_X` out of nonvanishing `H^1(X, ℐ_Z ℒ)`, and it is injective**: by
clause (5) of [Stacks, Tag 0BS2] a nonzero linear form on `H^1(X, ℐ_Z ℒ)` is a nonzero map into
the dualizing sheaf, and a nonzero map into `ω_X` out of a submodule of an invertible module is
injective. -/
theorem exists_mono_idealTwist_dualizingSheaf [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (h : ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1)) :
    ∃ φ : S.idealTwist Z L ⟶ Stacks.Duality.dualizingSheafOverField S.f, φ ≠ 0 ∧ Mono φ := by
  have hc := S.isCoherent_idealTwist Z L
  obtain ⟨φ, hφ⟩ := Stacks.Duality.exists_ne_zero_hom_dualizingSheaf S.f
    (le_of_eq S.dimension_one) _ (isQuasicoherent_of_isCoherent _) h
  exact ⟨φ, hφ, S.mono_of_ne_zero_of_mono (S.idealTwistι Z L) hc φ hφ⟩

/-- For `H^0(φ)` injective with `φ : ℐ_Z ℒ ⟶ ω_X`: `h^0 ≤ g`, `h^1 > 0` and the Euler
characteristic formula for `ℐ_Z ℒ`. -/
private theorem finrank_cohomology_idealTwist_facts [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (h : ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1))
    (φ : S.idealTwist Z L ⟶ Stacks.Duality.dualizingSheafOverField S.f)
    (hinj : Function.Injective (cohomologyOverFieldMap S.k S.f φ 0).hom) :
    Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 0) ≤ genus S.f ∧
      0 < Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 1) ∧
      (Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 0) : ℤ) -
        Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 1) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L + 1 - (genus S.f : ℤ) -
        (S.subschemeDegree Z : ℤ) := by
  have := S.isCoherent_idealTwist Z L
  have := Stacks.Duality.finiteDimensional_cohomologyOverField_zero_dualizingSheafOverField S.f
    (le_of_eq S.dimension_one)
  have := finiteDimensional_cohomologyOverField_of_isProper S.k S.f (S.idealTwist Z L) 1
  refine ⟨(LinearMap.finrank_le_finrank_of_injective (f := (cohomologyOverFieldMap S.k S.f φ 0).hom)
      hinj).trans_eq
      (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField S.f
        (le_of_eq S.dimension_one)), ?_, ?_⟩
  · rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial] at h
    exact Module.finrank_pos
  · have hχ := S.eulerCharacteristic_idealTwist Z hZ L
    rw [eulerCharacteristic_eq_finsum,
      finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero S.k S.f _
        (isZero_cohomologyOverField_two_le S.k S.f (le_of_eq S.dimension_one) _)] at hχ
    exact hχ

/-- **The degree bound of [Stacks, Tag 0E3A]**: if `H^1(X, ℐ_Z ℒ) ≠ 0` then
`deg(ℒ) ≤ 2g - 2 + deg(Z)`. An injective map `ℐ_Z ℒ ⟶ ω_X` gives `h^0(ℐ_Z ℒ) ≤ h^0(ω_X) = g`, and
`h^1(ℐ_Z ℒ) ≥ 1`, so `χ(ℐ_Z ℒ) = deg(ℒ) + 1 - g - deg(Z) ≤ g - 1`. -/
theorem invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist [IsIntegral S.X]
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (Z : S.X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (h : ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1)) :
    invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L ≤
      2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ) := by
  have hc := S.isCoherent_idealTwist Z L
  obtain ⟨φ, -, hmono⟩ := S.exists_mono_idealTwist_dualizingSheaf Z L h
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ) hmono inferInstance
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence S.k S.f hS
  obtain ⟨h0, h1, hχ⟩ := S.finrank_cohomology_idealTwist_facts Z hZ L h φ hinj
  omega

/-- **The twist `ℐ_Z ℒ` has rank one.** -/
theorem fiberRank_idealTwist_genericPoint [IsIntegral S.X] (Z : S.X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    Scheme.Modules.fiberRank (S.idealTwist Z L) (genericPoint S.X) = 1 := by
  have := S.isCoherent_idealSheafModule Z
  have := S.isCoherent_idealTwist Z L
  have : (S.idealSheafModule Z).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : (S.idealTwist Z L).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f L 1
  have : L.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have h := CoherentReflexive.fiberRank_genericPoint_tensorSheaf L (S.idealSheafModule Z)
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank L 1,
    S.fiberRank_idealSheafModule_genericPoint Z hZ] at h
  exact h

/-- **The equality case of [Stacks, Tag 0E3A]**: if `H^1(X, ℐ_Z ℒ) ≠ 0` and
`deg(ℒ) = 2g - 2 + deg(Z)`, then `ℐ_Z ℒ ≅ ω_X`. Then `h^0(ℐ_Z ℒ) = g = h^0(ω_X)` and
`h^1(ℐ_Z ℒ) = 1`, so for the injective map `φ : ℐ_Z ℒ ⟶ ω_X` the cokernel has no global sections:
`H^0(φ)` is bijective and `H^1(φ)` is injective, being nonzero by duality. A rank one submodule of
`ω_X` with such a cokernel is all of `ω_X` (`isIso_of_subsingleton_sections_cokernel`). -/
theorem nonempty_iso_dualizingSheaf_of_invertibleCurveDegree_eq [IsIntegral S.X]
    (L : S.X.Modules) [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (Z : S.X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (h : ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1))
    (heq : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L =
      2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ)) :
    Nonempty (S.idealTwist Z L ≅ Stacks.Duality.dualizingSheafOverField S.f) := by
  have hdim : topologicalKrullDim S.X ≤ 1 := le_of_eq S.dimension_one
  have hc := S.isCoherent_idealTwist Z L
  have hq : (S.idealTwist Z L).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  obtain ⟨φ, hφ, hmono⟩ := S.exists_mono_idealTwist_dualizingSheaf Z L h
  have hS : (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ) hmono inferInstance
  obtain ⟨δ, hinj, hex, hexδ, hexd⟩ := exists_cohomologyOverField_longExactSequence S.k S.f hS
  have := Stacks.Duality.finiteDimensional_cohomologyOverField_zero_dualizingSheafOverField S.f
    hdim
  have := finiteDimensional_cohomologyOverField_of_isProper S.k S.f (S.idealTwist Z L) 0
  have := finiteDimensional_cohomologyOverField_of_isProper S.k S.f (S.idealTwist Z L) 1
  have hω0 := Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField S.f hdim
  obtain ⟨h0, h1, hχ⟩ := S.finrank_cohomology_idealTwist_facts Z hZ L h φ hinj
  have h0eq : Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 0) =
      genus S.f := by omega
  have h1eq : Module.finrank S.k (cohomologyOverField S.k S.f (S.idealTwist Z L) 1) = 1 := by
    omega
  -- `H^0(φ)` is bijective.
  have hsurj : Function.Surjective (cohomologyOverFieldMap S.k S.f φ 0).hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h0eq.trans hω0.symm)).mp hinj
  -- `H^1(φ)` is nonzero, hence injective.
  have hH1ne : cohomologyOverFieldMap S.k S.f φ 1 ≠ 0 := by
    intro h0'
    apply hφ
    have hnat := Stacks.Duality.homDualizingSheafAddEquiv_naturality S.f hdim hq
      (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f) φ
      (𝟙 (Stacks.Duality.dualizingSheafOverField S.f))
    rw [Category.comp_id, h0', zero_comp] at hnat
    exact (Stacks.Duality.homDualizingSheafAddEquiv S.f hdim _ hq).injective
      (hnat.trans (map_zero _).symm)
  have hinj1 : Function.Injective (cohomologyOverFieldMap S.k S.f φ 1).hom := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    have hpos : Module.finrank S.k (LinearMap.ker (cohomologyOverFieldMap S.k S.f φ 1).hom) ≠ 0 :=
      fun h0' => hker (Submodule.finrank_eq_zero.mp h0')
    have hle := Submodule.finrank_le (LinearMap.ker (cohomologyOverFieldMap S.k S.f φ 1).hom)
    have htop : LinearMap.ker (cohomologyOverFieldMap S.k S.f φ 1).hom = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by omega)
    exact hH1ne (ModuleCat.hom_ext (LinearMap.ker_eq_top.mp htop))
  -- Hence the cokernel has no global sections.
  have hQ0 : Subsingleton (cohomologyOverField S.k S.f (cokernel φ) 0) := by
    suffices hz : ∀ v : cohomologyOverField S.k S.f (cokernel φ) 0, v = 0 from
      ⟨fun v w => (hz v).trans (hz w).symm⟩
    intro v
    have hδ : δ 0 v = 0 :=
      hinj1 ((((hexd 0) (δ 0 v)).mpr ⟨v, rfl⟩).trans (map_zero _).symm)
    obtain ⟨w', hw'⟩ := ((hexδ 0) v).mp hδ
    obtain ⟨u, rfl⟩ := hsurj w'
    rw [← hw']
    exact (hex 0).apply_apply_eq_zero u
  have hΓ : Subsingleton Γ(cokernel φ, ⊤) :=
    (cohomologyOverFieldZeroEquivSections S.k S.f (cokernel φ)).symm.subsingleton
  have := S.isIso_of_subsingleton_sections_cokernel (S.idealTwist Z L)
    (S.fiberRank_idealTwist_genericPoint Z hZ L) φ hΓ
  exact ⟨asIso φ⟩

/-- **Stacks Project, Tag 0E3A.** In Situation [Stacks, Tag 0B5D] assume `X` is integral of genus
`g`. Let `ℒ` be an invertible `𝒪_X`-module and let `Z ⊆ X` be a closed subscheme of dimension at
most zero with ideal sheaf `ℐ`. If `H^1(X, ℐℒ) ≠ 0`, then

  `deg(ℒ) ≤ 2g - 2 + deg(Z)`,

with strict inequality unless `ℐℒ ≅ ω_X`. Here `ℐℒ` is `ℒ ⊗ ℐ`, `deg(Z) = dim_k Γ(Z, 𝒪_Z)` and
`ω_X` is the dualizing sheaf of [Stacks, Tag 0BS2]. -/
@[stacks 0E3A]
theorem invertibleCurveDegree_le_and_lt_or_nonempty_iso_of_not_isZero_cohomology_idealTwist
    [IsIntegral S.X] (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (Z : S.X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (h : ¬ IsZero (cohomologyOverField S.k S.f (S.idealTwist Z L) 1)) :
    invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L ≤
        2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ) ∧
      (invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L <
          2 * (genus S.f : ℤ) - 2 + (S.subschemeDegree Z : ℤ) ∨
        Nonempty (S.idealTwist Z L ≅ Stacks.Duality.dualizingSheafOverField S.f)) := by
  have hle := S.invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist L Z hZ h
  refine ⟨hle, ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr (S.nonempty_iso_dualizingSheaf_of_invertibleCurveDegree_eq L Z hZ h heq)

end AlgebraicGeometry.CohenMacaulayCurveSituation
