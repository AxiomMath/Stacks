module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.TracePairing
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent

/-!
# The trace pairing of a coherent module on a proper scheme over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, let
`ω_X^• = a(𝒪_{Spec k})` be as in [Stacks, Tag 0FVV] and `t : H⁰(X, ω_X^•) ⟶ k` the trace of
[Stacks, Tag 0FVW]. For a coherent `𝒪_X`-module `ℱ` the pairings
`⟨α, β⟩ = t(α(β))` of `Ext^i_X(ℱ, ω_X^•)` with `H^{-i}(X, ℱ)` are perfect pairings of finite
dimensional `k`-vector spaces ([Stacks, Tag 0FVX]): `ℱ[0]` lies in `D^b_Coh(𝒪_X)`, since coherent
modules form a weak Serre subcategory ([Stacks, Tag 01BY]), so this is the coherent case of
[Stacks, Tag 0FVW]. They are functorial: for `φ : ℱ ⟶ 𝒢`,
`⟨α ∘ φ, β⟩ = ⟨α, φ(β)⟩`, so that the map `Ext^i_X(𝒢, ω_X^•) ⟶ Ext^i_X(ℱ, ω_X^•)` induced by `φ`
is, via the pairings, the `k`-linear dual of `H^{-i}(X, ℱ) ⟶ H^{-i}(X, 𝒢)`; in this form the
statement holds for quasi-coherent `ℱ` and `𝒢`.

## Main results

* `DerivedCategoryB.derivedCategoryBBounded_singleFunctor_obj` — an object of a weak Serre
  subcategory, placed in degree zero, lies in `D^b_B`.
* `Stacks.Duality.extPrecompLinearMap` — the `k`-linear map
  `Ext^i_X(L, ω_X^•) ⟶ Ext^i_X(K, ω_X^•)` induced by `K ⟶ L`.
* `Stacks.Duality.coherentTracePairing_isPerfPair_and_dualMap` — [Stacks, Tag 0FVX].

## References

* [Stacks Project, Tag 0FVX](https://stacks.math.columbia.edu/tag/0FVX)
* [Stacks Project, Tag 0FVW](https://stacks.math.columbia.edu/tag/0FVW)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v w u

namespace DerivedCategoryB

open DerivedCategory WeakSerre

variable {A : Type w} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- **An object of a weak Serre subcategory, placed in degree zero, lies in `D^b_B`.** Its
cohomology is the object itself in degree zero and vanishes elsewhere. -/
theorem derivedCategoryBBounded_singleFunctor_obj (B : ObjectProperty A) (hB : IsWeakSerre B)
    (M : A) (hM : B M) :
    derivedCategoryBBounded B ((singleFunctor A 0).obj M) :=
  have h := derivedCategoryBPlus_singleFunctor_obj B hB M hM
  ⟨⟨h.1, 0, fun n hn ↦ isZero_of_isLE _ 0 n hn⟩, h.2⟩

end DerivedCategoryB

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- Degree-zero cohomology on `D(k)`. -/
local notation "H⁰" => DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)`, whose shift sequence is `H^n(X, -)`. -/
local notation "HX" => derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- A module placed in degree zero. -/
local notation "single₀" => DerivedCategory.singleFunctor X.Modules 0

/-- **Precomposition on `Ext` into `ω_X^•`.** A morphism `g : K ⟶ L` of `D(𝒪_X)` induces the
`k`-linear map `Ext^i_X(L, ω_X^•) ⟶ Ext^i_X(K, ω_X^•)`, `α ↦ α ∘ g`. -/
def extPrecompLinearMap {K L : DerivedCategory X.Modules} (g : K ⟶ L) (i : ℤ) :
    letI := Scheme.linearOver f
    DerivedCategory.Ext L (ωX).obj i →ₗ[k] DerivedCategory.Ext K (ωX).obj i :=
  let := Scheme.linearOver f
  { toFun α := g ≫ α
    map_add' := Preadditive.comp_add _ _ _ g
    map_smul' := Linear.comp_smul _ _ _ g }

/-- `extPrecompLinearMap f g i` sends `α` to the composite `g ≫ α`. -/
@[simp]
theorem extPrecompLinearMap_apply {K L : DerivedCategory X.Modules} (g : K ⟶ L) (i : ℤ)
    (α : DerivedCategory.Ext L (ωX).obj i) :
    letI := Scheme.linearOver f
    extPrecompLinearMap f g i α = g ≫ α :=
  rfl

/-- **[Stacks, Tag 0FVX].** Let `X` be a proper scheme over a field `k`, `ω_X^•` and
`t : H⁰(X, ω_X^•) ⟶ k` as in [Stacks, Tag 0FVW], and `i ∈ ℤ`.
1. For a coherent `𝒪_X`-module `ℱ`, `Ext^i_X(ℱ, ω_X^•)` and `H^{-i}(X, ℱ)` are finite dimensional
   and the pairing `⟨α, β⟩ = t(α(β))` between them (`α` regarded as a morphism
   `ℱ[-i] ⟶ ω_X^•`, `β` as an element of `H⁰(X, ℱ[-i])`) is perfect.
2. For a homomorphism `φ : ℱ ⟶ 𝒢` of coherent `𝒪_X`-modules, `⟨α ∘ φ, β⟩ = ⟨α, φ(β)⟩` for
   `α ∈ Ext^i_X(𝒢, ω_X^•)` and `β ∈ H^{-i}(X, ℱ)`.
3. For a homomorphism `φ : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules, the map
   `Ext^i_X(𝒢, ω_X^•) ⟶ Ext^i_X(ℱ, ω_X^•)` induced by `φ` is, via the identifications of
   `Ext^i_X(-, ω_X^•)` with `H^{-i}(X, -)^∨` given by the pairings, the `k`-linear dual of the map
   `H^{-i}(X, ℱ) ⟶ H^{-i}(X, 𝒢)` induced by `φ`. -/
@[stacks 0FVX]
theorem coherentTracePairing_isPerfPair_and_dualMap (i : ℤ) :
    letI := Scheme.linearOver f
    (∀ F : X.Modules, F.IsCoherent →
      FiniteDimensional k (DerivedCategory.Ext ((single₀).obj F) (ωX).obj i) ∧
      FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj ((single₀).obj F))) ∧
      (dualityLinearMap f ((single₀).obj F) i).IsPerfPair ∧
      ∀ (α : DerivedCategory.Ext ((single₀).obj F) (ωX).obj i)
        (β : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
          ((derivedGlobalSectionsOver f).obj ((single₀).obj F))),
        dualityLinearMap f ((single₀).obj F) i α β =
          (traceOverField f).hom
            (((H⁰).map ((derivedGlobalSectionsOver f).map (extShiftHom α))).hom
              ((((HX).shiftIso (-i) 0 (-i) (add_zero _)).inv.app ((single₀).obj F)).hom β))) ∧
    (∀ (F G : X.Modules) (φ : F ⟶ G), F.IsCoherent → G.IsCoherent →
      ∀ (α : DerivedCategory.Ext ((single₀).obj G) (ωX).obj i)
        (β : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
          ((derivedGlobalSectionsOver f).obj ((single₀).obj F))),
        dualityLinearMap f ((single₀).obj F) i ((single₀).map φ ≫ α) β =
          dualityLinearMap f ((single₀).obj G) i α
            (((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
              ((derivedGlobalSectionsOver f).map ((single₀).map φ))).hom β)) ∧
    ∀ (F G : X.Modules) (φ : F ⟶ G) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent),
      (dualityEquiv f (singleQuasiCoherent F hF 0) i).toLinearMap ∘ₗ
          extPrecompLinearMap f ((single₀).map φ) i =
        ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).map
            ((derivedGlobalSectionsOver f).map ((single₀).map φ))).hom.dualMap ∘ₗ
          (dualityEquiv f (singleQuasiCoherent G hG 0) i).toLinearMap := by
  let := Scheme.linearOver f
  refine ⟨fun F hF => ?_, fun F G φ _ _ α β => ?_, fun F G φ hF hG => ?_⟩
  · have hb := DerivedCategoryB.derivedCategoryBBounded_singleFunctor_obj
      (fun M : X.Modules => M.IsCoherent)
      (Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_isWeakSerre X) F hF
    obtain ⟨-, hExt, hH, hP⟩ := finiteDimensional_and_isPerfPair_of_coherent f _ hb
    exact ⟨hExt i, hH (-i), hP i, fun α β =>
      dualityEquiv_apply_eq_traceOverField f (quasiCoherentOfCoherent _ hb.2) i α β⟩
  · change (dualityPairing f _ i ((single₀).map φ ≫ α)).hom β = (dualityPairing f _ i α).hom _
    rw [dualityPairing_comp]
    rfl
  · ext α β
    exact dualityEquiv_comp f (singleQuasiCoherent F hF 0) (singleQuasiCoherent G hG 0) i
      ((single₀).map φ) α β

end Stacks.Duality
