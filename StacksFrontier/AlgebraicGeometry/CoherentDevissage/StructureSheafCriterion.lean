module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IrreducibleSupportCriterion
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Devissage of coherent modules down to the structure sheaves of the closed subvarieties

[Stacks, Tag 01YG] checks a property `P` of coherent modules on a Noetherian scheme `X` on the
direct images `i_* ℐ` of the quasi-coherent ideals `ℐ ⊆ 𝒪_Z` of the integral closed subschemes
`i : Z ⟶ X`. That family is still large: it carries one module for every ideal on every integral
closed subscheme. This file runs the criterion down to the much smaller family of the structure
sheaves `𝒪_{\overline{\{x\}}}` themselves, one for each point of `X`, at the price of one extra
closure property of `P`: `P` must descend from the middle term of a short exact sequence to the
sub when the sub has the same support.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_structureSheafAt`: a
  property of coherent modules that is invariant under isomorphism, holds on the zero modules, is
  stable under extensions, descends to a submodule of full support, and holds on every
  `AlgebraicGeometry.TorFormula.structureSheafAt x`, holds on every coherent module.

## Implementation notes

The proof is a Noetherian induction over `TopologicalSpace.Closeds X`, in the shape of the
induction of [Stacks, Tag 01YI]: the auxiliary statement is "`P` holds on every coherent module
supported inside `T`", and at `T` the criterion of [Stacks, Tag 01YG] is applied to the property
`fun F => SheafOfModules.supp F ⊆ T → P F`.

What makes that application go through is the dichotomy on the test object `i_* ℐ`. If `ℐ = 0`
then `i_* ℐ` is zero. Otherwise `Supp (i_* ℐ)` is the whole of `Set.range i.base`
(`Stacks.AlgebraicGeometry.IrreducibleSupportDevissage.supp_pushforward_ideal_eq_range`), which
is a
closed subset of `T`; if it is strictly smaller the induction hypothesis applies directly, and if
it is all of `T` the sequence

`0 ⟶ i_* ℐ ⟶ i_* 𝒪_Z ⟶ i_* (𝒪_Z / ℐ) ⟶ 0`

is short exact. Its middle term is the structure sheaf of the integral closed subscheme attached
to `i (genericPoint Z)` (`Stacks.Chow.pushforwardUnitIsoIntegralComponent`), which is exactly
`AlgebraicGeometry.TorFormula.structureSheafAt (i (genericPoint Z))`, so the test family gives
`P` on it. Its quotient term is supported inside `Set.range i.base` but not at
`i (genericPoint Z)`, because the stalk of `𝒪_Z` at the generic point of the integral scheme `Z`
is a field and the stalk of `ℐ` there is a nonzero submodule of it
(`AlgebraicGeometry.notMem_supp_cokernel_genericPoint_of_mono`), so the induction hypothesis
applies to it. The descent hypothesis then transfers `P` to `i_* ℐ`, its support hypothesis
holding because
both `i_* ℐ` and `i_* 𝒪_Z` are supported exactly on `Set.range i.base`.

**Coherence is spelled `_root_.SheafOfModules.IsCoherent`.** The predicate is declared twice on
this branch and inside the `Stacks.` namespace an unqualified spelling can resolve to
`Stacks.SheafOfModules.IsCoherent`; [Stacks, Tag 01YG] is stated against the root constant, so a
relative name would state a different theorem.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.instCategory
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pushforward
/-- **The test family of [Stacks, Tag 01YG] in the Noetherian induction.** Let `T` be a closed
subset of `X` for which the property is already known on every coherent module supported inside
a strictly smaller closed subset. Then it holds on the direct image of every quasi-coherent
ideal of an integral closed subscheme whose direct image is supported inside `T`.

If the ideal is zero so is its direct image. Otherwise the direct image is supported on the
whole range of `i`, which is a closed subset of `T`; if it is strictly smaller the induction
hypothesis applies, and if it is all of `T` the sequence
`0 ⟶ i_* ℐ ⟶ i_* 𝒪_Z ⟶ i_* (𝒪_Z / ℐ) ⟶ 0` is short exact with middle term the structure sheaf of
the integral closed subscheme attached to `i (genericPoint Z)` and with quotient term supported
strictly inside `T`. -/
private theorem property_pushforward_ideal_of_structureSheafAt {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop)
    (hiso : ∀ {F F' : X.Modules}, (F ≅ F') → P F → P F')
    (hzero : ∀ F : X.Modules, CategoryTheory.Limits.IsZero F → P F)
    (hsub : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      SheafOfModules.supp S.X₂ = SheafOfModules.supp S.X₁ →
      P S.X₂ → P S.X₃ → P S.X₁)
    (hstr : ∀ x : X, P (AlgebraicGeometry.TorFormula.structureSheafAt x))
    (T : TopologicalSpace.Closeds X)
    (ih : ∀ T' : TopologicalSpace.Closeds X, T' < T → ∀ F : X.Modules,
      _root_.SheafOfModules.IsCoherent F → SheafOfModules.supp F ⊆ (T' : Set X) → P F)
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : (_root_.SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hI : I.toSheafOfModules.IsQuasicoherent)
    (hsuppT : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
      ⊆ (T : Set X)) :
    P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) := by
  let : I.toSheafOfModules.IsQuasicoherent := hI
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : (Scheme.Modules.pushforward i).Additive :=
    Stacks.SchemeCohomology.pushforward_additive i
  have := CoherenceCriteria.structureSheaf_isCoherent Z
  have hmono : Mono I.ι := _root_.SheafOfModules.Submodule.instMonoι I
  have hIc : I.toSheafOfModules.IsCoherent := CoherentSubquotients.isCoherent_of_mono I.ι
  let := hIc
  have hX1c : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
    IrreducibleSupportDevissage.coherent_pushforward_ideal i I
  by_cases hIz : IsZero I.toSheafOfModules
  · exact hzero _ ((Scheme.Modules.pushforward i).map_isZero hIz)
  -- The nonzero case: the direct image is supported exactly on the range of `i`.
  have hsupp1 : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)
      = Set.range (ConcreteCategory.hom i.base) :=
    IrreducibleSupportDevissage.supp_pushforward_ideal_eq_range i I hIc hIz
  have hclosed : IsClosed (Set.range (ConcreteCategory.hom i.base)) :=
    i.isClosedEmbedding.isClosed_range
  have hrange : Set.range (ConcreteCategory.hom i.base) ⊆ (T : Set X) := by
    rw [← hsupp1]; exact hsuppT
  have hle : (⟨Set.range (ConcreteCategory.hom i.base), hclosed⟩ :
      TopologicalSpace.Closeds X) ≤ T := SetLike.coe_subset_coe.mp hrange
  by_cases hlt : (⟨Set.range (ConcreteCategory.hom i.base), hclosed⟩ :
      TopologicalSpace.Closeds X) < T
  · exact ih _ hlt _ hX1c hsupp1.subset
  -- The range of `i` is all of `T`; compare with the structure sheaf of `Z`.
  have hTeq : (T : Set X) = Set.range (ConcreteCategory.hom i.base) :=
    congrArg (fun S : TopologicalSpace.Closeds X => (S : Set X))
      ((hle.lt_or_eq).resolve_left hlt).symm
  have hS := _root_.AlgebraicGeometry.shortExact_map_pushforward_cokernelSequence_of_mono
    i I.ι hmono
  have e2 : (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit Z.ringCatSheaf) ≅
      AlgebraicGeometry.TorFormula.structureSheafAt (i (genericPoint Z)) :=
    Stacks.Chow.pushforwardUnitIsoIntegralComponent i
  have hP2 : P ((Scheme.Modules.pushforward i).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf)) :=
    hiso e2.symm (hstr (i (genericPoint Z)))
  have hsupp2 : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf))
      = Set.range (ConcreteCategory.hom i.base) := by
    rw [_root_.SheafOfModules.supp_eq_of_iso e2,
      AlgebraicGeometry.TorFormula.supp_structureSheafAt,
      ← Stacks.Chow.range_eq_closure_singleton i]
  have hX2c : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward i).obj
      (_root_.SheafOfModules.unit Z.ringCatSheaf)) :=
    PushforwardCoherent.pushforward_isCoherent_of_isFinite i
      (_root_.SheafOfModules.unit Z.ringCatSheaf)
  have hcokc : (cokernel I.ι).IsCoherent := _root_.SheafOfModules.cokernel_isCoherent I.ι
  let := hcokc
  have hcokq : (cokernel I.ι).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent (cokernel I.ι)
  let := hcokq
  have hX3c : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj (cokernel I.ι)) :=
    @PushforwardCoherent.pushforward_isCoherent_of_isFinite Z X i inferInstance inferInstance
      (cokernel I.ι) hcokq hcokc
  -- The generic point of `Z` lies in the support of the ideal, so not in that of the quotient.
  have hmem_iff : ∀ M : Z.Modules, i (genericPoint Z) ∈
      SheafOfModules.supp ((Scheme.Modules.pushforward i).obj M) ↔
      genericPoint Z ∈ SheafOfModules.supp M := fun M => by
    rw [_root_.AlgebraicGeometry.supp_pushforward_of_isClosedImmersion i M,
      i.isClosedEmbedding.injective.mem_set_image]
  have hηI : genericPoint Z ∈ SheafOfModules.supp I.toSheafOfModules :=
    (hmem_iff _).mp (hsupp1 ▸ Set.mem_range_self _)
  have hcok : genericPoint Z ∉ SheafOfModules.supp (cokernel I.ι) :=
    _root_.AlgebraicGeometry.notMem_supp_cokernel_genericPoint_of_mono I.ι hmono hηI
  have hsupp3 : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (cokernel I.ι))
      = ConcreteCategory.hom i.base '' SheafOfModules.supp (cokernel I.ι) :=
    _root_.AlgebraicGeometry.supp_pushforward_of_isClosedImmersion i (cokernel I.ι)
  have hxinot : i (genericPoint Z) ∉ SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (cokernel I.ι)) := fun h => hcok ((hmem_iff _).mp h)
  have hX3closed : IsClosed (SheafOfModules.supp
      ((Scheme.Modules.pushforward i).obj (cokernel I.ι))) :=
    DevissageNoetherian.isClosed_supp_of_isCoherent _ hX3c
  have hX3lt : (⟨SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (cokernel I.ι)),
      hX3closed⟩ : TopologicalSpace.Closeds X) < T := by
    have hsub3 : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (cokernel I.ι))
        ⊆ (T : Set X) := by
      rw [hTeq, hsupp3]; exact Set.image_subset_range _ _
    refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub3) ?_
    intro hEq
    apply hxinot
    have h : SheafOfModules.supp ((Scheme.Modules.pushforward i).obj (cokernel I.ι))
        = (T : Set X) :=
      congrArg (fun S : TopologicalSpace.Closeds X => (S : Set X)) hEq
    rw [h, hTeq]
    exact Set.mem_range_self _
  have hP3 : P ((Scheme.Modules.pushforward i).obj (cokernel I.ι)) :=
    ih _ hX3lt _ hX3c subset_rfl
  exact hsub _ hS hX1c hX2c hX3c (hsupp2.trans hsupp1.symm) hP2 hP3

/-- **The Noetherian induction behind `property_of_isCoherent_of_structureSheafAt`.** For every
closed subset `T` of `X`, the property holds on every coherent module supported inside `T`.

The induction is over `TopologicalSpace.Closeds X`, which is well-founded under strict inclusion
because `X` is Noetherian. At `T` the criterion of [Stacks, Tag 01YG] is applied to the property
`fun F => SheafOfModules.supp F ⊆ T → P F`: the zero module is handled by `hzero`, extensions by
`hext` because the outer terms of a short exact sequence are supported inside the middle one, and
the test family by `property_pushforward_ideal_of_structureSheafAt`. -/
private theorem property_of_supp_subset_of_structureSheafAt (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop)
    (hiso : ∀ {F F' : X.Modules}, (F ≅ F') → P F → P F')
    (hzero : ∀ F : X.Modules, CategoryTheory.Limits.IsZero F → P F)
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hsub : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      SheafOfModules.supp S.X₂ = SheafOfModules.supp S.X₁ →
      P S.X₂ → P S.X₃ → P S.X₁)
    (hstr : ∀ x : X, P (AlgebraicGeometry.TorFormula.structureSheafAt x)) :
    ∀ T : TopologicalSpace.Closeds X, ∀ F : X.Modules,
      _root_.SheafOfModules.IsCoherent F → SheafOfModules.supp F ⊆ (T : Set X) → P F := by
  intro T
  refine (wellFounded_lt : WellFounded ((· < ·) :
    TopologicalSpace.Closeds X → TopologicalSpace.Closeds X → Prop)).induction
      (C := fun T => ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F →
        SheafOfModules.supp F ⊆ (T : Set X) → P F) T ?_
  clear T
  intro T ih
  refine property_of_isCoherent X (fun F => SheafOfModules.supp F ⊆ (T : Set X) → P F)
    (fun _ => hzero _ isZero_terminal) ?_ ?_
  · intro S hS h1 h2 h3 hp1 hp3 hsupp2
    have := hS.mono_f
    have := hS.epi_g
    exact hext S hS h1 h2 h3
      (hp1 ((Stacks.Chow.supp_subset_of_mono S.f).trans hsupp2))
      (hp3 ((Stacks.Chow.supp_subset_of_epi S.g).trans hsupp2))
  · intro Z i hci hint I hI
    let : IsClosedImmersion i := hci
    let : IsIntegral Z := hint
    exact property_pushforward_ideal_of_structureSheafAt P hiso hzero hsub hstr T ih i I hI

/-- **Dévissage down to the structure sheaves of the closed subvarieties.** Let `X` be a
Noetherian scheme and let `P` be a property of coherent `𝒪_X`-modules which

1. is invariant under isomorphism,
2. holds on every zero module,
3. is stable under extensions of coherent modules,
4. descends from the middle term of a short exact sequence of coherent modules to the sub, as
   soon as the sub has the same support as the middle term and the quotient has `P`, and
5. holds on the structure sheaf `𝒪_{\overline{\{x\}}}` of the reduced closure of every point `x`
   of `X`, pushed forward to `X`.

Then `P` holds on every coherent `𝒪_X`-module.

This is [Stacks, Tag 01YG] run down to the structure sheaves: see the implementation notes of
this file. -/
@[ega "III 3.1.2" "Case X' = X"]
public theorem property_of_isCoherent_of_structureSheafAt (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop)
    (hiso : ∀ {F F' : X.Modules}, (F ≅ F') → P F → P F')
    (hzero : ∀ F : X.Modules, CategoryTheory.Limits.IsZero F → P F)
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hsub : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ →
      SheafOfModules.supp S.X₂ = SheafOfModules.supp S.X₁ →
      P S.X₂ → P S.X₃ → P S.X₁)
    (hstr : ∀ x : X, P (AlgebraicGeometry.TorFormula.structureSheafAt x)) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F := fun F hF =>
  property_of_supp_subset_of_structureSheafAt X P hiso hzero hext hsub hstr ⊤ F hF
    (by simp)

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
