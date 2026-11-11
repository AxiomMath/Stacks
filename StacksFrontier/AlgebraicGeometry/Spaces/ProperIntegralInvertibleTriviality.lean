module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIntegral

/-!
# Triviality of an invertible module on a proper integral algebraic space over a field

Let `k` be a field, let `X` be a proper integral algebraic space over `k` and let `L` be an
invertible `𝒪_X`-module.  If `H⁰(X, L)` and `H⁰(X, L^{⊗ -1})` are both nonzero then
`L ≅ 𝒪_X`.  This is Tag 0DMZ at the hypotheses of its source.

## Main results

* `AlgebraicGeometry.Space.isDomain_globalFunctions_of_isIntegralSpace`: the global regular
  functions of an integral algebraic space form a domain.
* `AlgebraicGeometry.Space.isField_globalFunctions_of_isProper_of_isIntegralSpace`: the global
  regular functions of a proper integral algebraic space over a field form a field.
* `AlgebraicGeometry.Space.isTrivial_of_nontrivial_sections_of_isProper` is **Stacks 0DMZ**.

## Implementation notes

The source uses properness through Tag 0DMY, to know that `H⁰(X, 𝒪_X)` is a field;
`AlgebraicGeometry.Space.isTrivial_of_nontrivial_sections` proves the conclusion under that
hypothesis over an arbitrary base.  Here the field property is obtained without the finiteness
of Tag 0DMY part (1):  every global function of a proper reduced space
over `k` is integral over `k` (Stacks 0A0Q read at the terminal chart,
`AlgebraicGeometry.Space.isIntegralElem_globalFunctions_of_isProper`), the global functions of
an integral space form a domain, and a domain integral over a field is a field.

The domain property is proved as in the source's proof of 0DMZ:  two nonzero global functions
are nonzero on some étale charts, both are nonvanishing at one point of a common chart because
`|X|` is irreducible and the charts are reduced
(`AlgebraicGeometry.Space.exists_common_chart_mem_basicOpen`), so their product is nonzero.

## References

* [Stacks Project, Tag 0DMZ](https://stacks.math.columbia.edu/tag/0DMZ)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.SheafOfModules (IsInvertible IsTrivial)
open Stacks.SheafOfModules.TensorPower (tensorPower)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Domain

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

include hF in
/-- **The global regular functions of an integral algebraic space form a domain.**

The ring is nontrivial because `|F|` is nonempty, so a surjective étale chart has a point and
restriction to it is a ring homomorphism into a nontrivial ring.  Two nonzero global functions
are nonzero on some étale charts, and by
`AlgebraicGeometry.Space.exists_common_chart_mem_basicOpen` their restrictions to a common
chart are both nonvanishing at one of its points; so is the restriction of their product. -/
theorem isDomain_globalFunctions_of_isIntegralSpace (hint : IsIntegralSpace B S hS F) :
    IsDomain (globalFunctions B S hS F) := by
  classical
  let r := globalFunctionsChartRestriction B S hS ⟨F, hF⟩
  have hnat : ∀ {U W : SmallEtale B S hS F} (p : W ⟶ U) (a : globalFunctions B S hS F),
      ((BigFppfOver.toScheme B S hS).map p.hom.left).appTop (r U a) = r W a := fun p a =>
    congrFun (globalFunctionsChartRestriction_naturality B S hS ⟨F, hF⟩ p) a
  have hex : ∀ a : globalFunctions B S hS F, a ≠ 0 → ∃ U : SmallEtale B S hS F, r U a ≠ 0 := by
    intro a ha
    by_contra! h
    exact ha (Subtype.ext (funext fun j => h j.unop))
  have hnontriv : Nontrivial (globalFunctions B S hS F) := by
    obtain ⟨U, φ, hsurj, hetale, -⟩ := hint.1
    have hφ := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U φ).1 hsurj
    have _ := hint.2.2
    obtain ⟨x⟩ := (inferInstance : Nonempty (points B S hS F))
    obtain ⟨y, -⟩ := hφ x
    let V : SmallEtale B S hS F := ⟨CostructuredArrow.mk φ, hetale⟩
    have _ : Nonempty (⊤ : (chartScheme V).Opens) := ⟨⟨pointsToScheme B S hS U y, trivial⟩⟩
    exact (r V).domain_nontrivial
  have hnzd : NoZeroDivisors (globalFunctions B S hS F) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra! h
    obtain ⟨U, hU⟩ := hex a h.1
    obtain ⟨V, hV⟩ := hex b h.2
    obtain ⟨W, p, q, w, hwa, hwb⟩ :=
      exists_common_chart_mem_basicOpen B S hS F hF hint U V _ _ hU hV
    rw [hnat p a] at hwa
    rw [hnat q b] at hwb
    have hmem : pointsToScheme B S hS W.obj.left w ∈
        (chartScheme W).basicOpen (r W (a * b)) := by
      rw [map_mul, Scheme.basicOpen_mul]
      exact ⟨hwa, hwb⟩
    rw [hab, map_zero, Scheme.basicOpen_zero] at hmem
    exact hmem
  exact NoZeroDivisors.to_isDomain _

end Domain

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **The global regular functions of a proper integral algebraic space over a field form a
field.**  This is what Tag 0DMZ uses properness for, through Tag 0DMY.

Every global function is integral over `k`
(`AlgebraicGeometry.Space.isIntegralElem_globalFunctions_of_isProper`, the space being reduced),
the global functions form a domain
(`AlgebraicGeometry.Space.isDomain_globalFunctions_of_isIntegralSpace`), and a domain integral
over a field is a field. -/
theorem isField_globalFunctions_of_isProper_of_isIntegralSpace
    (hf : IsProper B (Spec (.of k)) hS f)
    (hint : IsIntegralSpace B (Spec (.of k)) hS X) :
    IsField (globalFunctions B (Spec (.of k)) hS X) := by
  have _ := isDomain_globalFunctions_of_isIntegralSpace B (Spec (.of k)) hS X hX hint
  have _ : Algebra.IsIntegral k (globalFunctions B (Spec (.of k)) hS X) :=
    ⟨fun a => isIntegralElem_globalFunctions_of_isProper k B hS X hX f hf hint.1 a⟩
  exact isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)

/-- **Stacks 0DMZ.**  Let `k` be a field, let `X` be a proper integral algebraic space over `k`
and let `L` be an invertible `𝒪_X`-module.  If `H⁰(X, L)` and `H⁰(X, L^{⊗ -1})` are both
nonzero then `L ≅ 𝒪_X`.

This is `AlgebraicGeometry.Space.isTrivial_of_nontrivial_sections` with its hypothesis that
`H⁰(X, 𝒪_X)` be a field discharged from properness and integrality by
`AlgebraicGeometry.Space.isField_globalFunctions_of_isProper_of_isIntegralSpace`. -/
@[stacks 0DMZ]
theorem isTrivial_of_nontrivial_sections_of_isProper
    (hf : IsProper B (Spec (.of k)) hS f)
    (hint : IsIntegralSpace B (Spec (.of k)) hS X)
    (L : SheafOfModules.{u} (modulesRingSheaf B (Spec (.of k)) hS X hX))
    [IsInvertible (structureSheaf B (Spec (.of k)) hS X hX).obj
      (structureRingPresheaf_isSheaf B (Spec (.of k)) hS X hX) L]
    (hL : Nontrivial L.sections)
    (hLinv : Nontrivial (tensorPower (structureSheaf B (Spec (.of k)) hS X hX).obj
      (structureRingPresheaf_isSheaf B (Spec (.of k)) hS X hX) L (-1)).sections) :
    IsTrivial (structureSheaf B (Spec (.of k)) hS X hX).obj
      (structureRingPresheaf_isSheaf B (Spec (.of k)) hS X hX) L :=
  isTrivial_of_nontrivial_sections B (Spec (.of k)) hS X hX hint
    (isField_globalFunctions_of_isProper_of_isIntegralSpace k B hS X hX f hf hint)
    L hL hLinv

end AlgebraicGeometry.Space

end
