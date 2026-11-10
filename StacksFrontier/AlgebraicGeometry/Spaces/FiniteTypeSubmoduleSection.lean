module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubmoduleExhaustionQcqs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# A section of a quasi-coherent module over an affine chart lies in a finite type submodule

Let `X` be a quasi-compact and quasi-separated algebraic space and `ℱ` a quasi-coherent
`𝒪_X`-module.  Every section of `ℱ` over an affine étale chart of `X` is a section of a
quasi-coherent submodule of `ℱ` of finite type; and if the section lies in a quasi-coherent
submodule `𝒩 ⊆ ℱ`, the finite type submodule can be chosen inside `𝒩`.  This is the sectionwise
form of the exhaustion of a quasi-coherent module by its quasi-coherent submodules of finite
type, Stacks 07UV for algebraic spaces, and it is the input of the proof of Stacks 085M.

## Main results

* `AlgebraicGeometry.Space.exists_sieve_mem_of_finiteTypeGermExhaustion`: locally on the small
  étale site every section lies in a finite type quasi-coherent submodule.
* `AlgebraicGeometry.Space.exists_finiteType_mem_of_isAffine`: over an affine chart of a qcqs
  space, globally on the chart.
* `AlgebraicGeometry.Space.exists_finiteType_le_mem_of_isAffine`: inside a given quasi-coherent
  submodule.

## Implementation notes

The germ exhaustion of `AlgebraicGeometry.Space.finiteTypeGermExhaustion_of_isQuasiCompactSpace`
puts the germ of the section at every geometric point into a finite type quasi-coherent
submodule, so the section lies in one locally; an affine chart is a quasi-compact object of the
small étale site and the finite type quasi-coherent submodules form a directed family, so it lies
in one globally on the chart.  The version inside `𝒩` applies this to `𝒩` itself and carries the
result into `ℱ` as the range of a monomorphism
(`Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule`).

## References

* [Stacks Project, Tag 07UV](https://stacks.math.columbia.edu/tag/07UV)
* [Stacks Project, Tag 085M](https://stacks.math.columbia.edu/tag/085M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Every local section of a quasi-coherent module lies locally in a finite type quasi-coherent
submodule**, on an algebraic space with the germ exhaustion property. -/
theorem exists_sieve_mem_of_finiteTypeGermExhaustion (hX : FiniteTypeGermExhaustion B S hS X)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1) (s : F.val.obj (op V)) :
    ∃ T : Sieve V, T ∈ SmallEtale.topology B S hS X.1 V ∧
      ∀ ⦃Z : SmallEtale B S hS X.1⦄ (f : Z ⟶ V), T f →
        ∃ K : {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
            K.toSheafOfModules.IsFiniteType},
          F.val.map f.op s ∈ K.1.obj (op Z) := by
  let T : Sieve V :=
    { arrows := fun Z f => ∃ K : {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
          K.toSheafOfModules.IsFiniteType}, F.val.map f.op s ∈ K.1.obj (op Z)
      downward_closed := by
        rintro Z W f ⟨K, hK⟩ h
        refine ⟨K, ?_⟩
        have e : F.val.map (h ≫ f).op s = F.val.map h.op (F.val.map f.op s) :=
          PresheafOfModules.map_comp_apply F.val f.op h.op s
        rw [e]
        exact K.1.map_mem h.op hK }
  refine ⟨T, smallEtale_sieve_of_pointwise_covering B S hS X.1 V T fun z => ?_, fun _ _ hf => hf⟩
  obtain ⟨x, p, z', hz'⟩ := exists_geo_lift_at_chart_point B S hS X.1 V z
  let w : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V := p
  obtain ⟨K, hKq, hKf, hK⟩ := hX F hF x V w s
  obtain ⟨V', ψ, p', hp', hmem⟩ :=
    exists_map_mem_of_toPresheafFiber_mem_submoduleGermSet B S hS K w s hK
  refine ⟨V', ψ, ⟨⟨K, hKq, hKf⟩, hmem⟩, (BigFppfOver.toScheme B S hS).map p'.1 z', ?_⟩
  rw [← hz', ← show (etaleSitePoint B S hS X.1 x X.2).fiber.map ψ p' = p from hp']
  change _ = (BigFppfOver.toScheme B S hS).map (p'.1 ≫ (SmallEtale.toOver B S hS X.1).map ψ) z'
  rw [Functor.map_comp]
  rfl

/-- **A section of a quasi-coherent module over an affine chart of a qcqs algebraic space lies in
a quasi-coherent submodule of finite type.** -/
theorem exists_finiteType_mem_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (s : F.val.obj (op V)) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ s ∈ K.obj (op V) := by
  let ι := {K : F.Submodule // K.toSheafOfModules.IsQuasicoherentOnSite ∧
    K.toSheafOfModules.IsFiniteType}
  have : Nonempty ι := ⟨⟨⊥, isQuasicoherentOnSite_isFiniteType_bot B S hS⟩⟩
  obtain ⟨T, hT, hTK⟩ := exists_sieve_mem_of_finiteTypeGermExhaustion
    (finiteTypeGermExhaustion_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs) hF V s
  obtain ⟨K, hK⟩ := Stacks.SheafOfModules.exists_mem_of_isQuasiCompactObject
    (fun K : ι => K.1)
    (fun K₁ K₂ => ⟨⟨K₁.1 ⊔ K₂.1, isQuasicoherentOnSite_isFiniteType_sup B S hS hF _ _ K₁.2 K₂.2⟩,
      le_sup_left, le_sup_right⟩)
    (isQuasiCompactObject_of_isAffine B S hS X.1 V hV) s T hT hTK
  exact ⟨K.1, K.2.1, K.2.2, hK⟩

/-- **A section of a quasi-coherent submodule over an affine chart lies in a finite type
quasi-coherent submodule contained in it**, on a qcqs algebraic space: for `𝒩 ⊆ ℱ`
quasi-coherent and a section `s` of `𝒩` over an affine chart `V` there is a quasi-coherent
`𝒦 ⊆ 𝒩` of finite type with `s ∈ 𝒦(V)`. -/
theorem exists_finiteType_le_mem_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {F : Modules.{u, u} B S hS X.1 X.2} {N : F.Submodule}
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    {s : F.val.obj (op V)} (hs : s ∈ N.obj (op V)) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ K ≤ N ∧ s ∈ K.obj (op V) := by
  obtain ⟨K, hKq, hKf, hK⟩ := exists_finiteType_mem_of_isAffine hZ hXqc hXqs
    (F := N.toSheafOfModules) hN V hV ⟨s, hs⟩
  let e := Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmoduleIso (K.ι ≫ N.ι)
  refine ⟨Stacks.SheafOfModules.ImageSubsheaf.monoRangeSubmodule (K.ι ≫ N.ι), hKq.of_iso e,
    Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso e hKf,
    _root_.SheafOfModules.Submodule.le_iff.2 fun U x hx => ?_, ⟨⟨⟨s, hs⟩, hK⟩, rfl⟩⟩
  obtain ⟨y, rfl⟩ := hx
  exact (K.ι.val.app U y).2

end AlgebraicGeometry.Space

end
