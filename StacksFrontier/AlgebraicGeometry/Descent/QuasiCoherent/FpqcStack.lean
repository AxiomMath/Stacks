module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StackReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent modules as a stack for the fpqc topology

Quasi-coherent modules form a prestack for the fpqc topology, and they form a stack for the fpqc
topology if and only if every quasi-coherent descent datum along every fpqc covering family is
effective.

## Main results

* `Stacks.Descent.presheafHomIso`: the morphism presheaf of `Stacks.Descent.qcohPseudofunctor`
  is the morphism presheaf of `AlgebraicGeometry.modulePullbackPseudofunctor` at the underlying
  sheaves of modules.
* `Stacks.Descent.isPrestack_qcohPseudofunctor_fpqc`: quasi-coherent modules form a prestack for
  the fpqc topology.
* `Stacks.Descent.isStackFor_of_forall_isEffective` and
  `Stacks.Descent.isStack_qcohPseudofunctor_of_forall_isEffective`: the fpqc stack condition
  from effectivity.
* `Stacks.Descent.isStack_qcohPseudofunctor_fpqc`: the fpqc stack condition, assuming
  `AlgebraicGeometry.QuasicoherentDescentData.StandardSigmaEssSurj` and
  `AlgebraicGeometry.QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes`.
* `Stacks.Descent.isStack_qcohPseudofunctor_iff`: the fpqc stack condition is equivalent to the
  effectivity of all quasi-coherent descent data along fpqc covering families.

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite

universe v u

namespace Stacks.Descent

/-! ### The prestack condition for the fpqc topology -/

section Prestack

variable {S : Scheme.{u}} (M N : quasicoherentProperty.{u}.Obj (.mk (op S)))

/-- The morphism presheaf of the pseudofunctor of quasi-coherent modules is the morphism
presheaf of the pseudofunctor of all sheaves of modules, read at the underlying modules. -/
noncomputable def presheafHomIso :
    qcohPseudofunctor.presheafHom M N ≅
      modulePullbackPseudofunctor.presheafHom M.obj N.obj :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso
      { toFun := fun φ ↦ φ.hom
        invFun := fun ψ ↦ ⟨ψ⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })
    (fun _ ↦ by
      ext φ
      rfl)

/-- Quasi-coherent modules form a prestack for the fpqc topology. -/
@[sga "1 VIII 1.1" "partial"]
instance isPrestack_qcohPseudofunctor_fpqc :
    qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology.{u} where
  isSheaf M N :=
    haveI : M.obj.IsQuasicoherent := M.property
    haveI : N.obj.IsQuasicoherent := N.property
    (Presheaf.isSheaf_of_iso_iff (presheafHomIso M N)).2 (isSheaf_presheafHom' M.obj N.obj)

end Prestack

/-! ### Effectivity is the essential surjectivity of the descent functor -/

section EssSurj

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- For an fpqc covering family whose quasi-coherent descent data are all effective,
`CategoryTheory.Pseudofunctor.IsStackFor` holds for the presieve it generates. -/
theorem isStackFor_of_forall_isEffective
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (h : ∀ D : QuasicoherentDescentData f, D.IsEffective) :
    qcohPseudofunctor.IsStackFor (Presieve.ofArrows X f) := by
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  have hff := qcohPseudofunctor.fullyFaithfulToDescentData f
    (sieve_ofArrows_mem_fpqcTopology hfpqc)
  have := hff.full
  have := hff.faithful
  have := essSurj_toDescentData_of_forall_isEffective h
  exact { }

end EssSurj

/-! ### The fpqc stack condition -/

/-- Quasi-coherent modules form a stack for the fpqc topology as soon as every quasi-coherent
descent datum for every fpqc covering family is effective. -/
theorem isStack_qcohPseudofunctor_of_forall_isEffective
    (h : ∀ {S : Scheme.{u}} {I : Type (u + 1)} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S),
      Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S →
        ∀ D : QuasicoherentDescentData f, D.IsEffective) :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u} :=
  Pseudofunctor.IsStack.of_precoverage (J := Scheme.fpqcPrecoverage.{u}) fun _ R hR ↦ by
    obtain ⟨_, _, f, rfl⟩ := R.exists_eq_ofArrows
    exact isStackFor_of_forall_isEffective hR (h f hR)

/-- Assuming `AlgebraicGeometry.QuasicoherentDescentData.StandardSigmaEssSurj` and
`AlgebraicGeometry.QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes`, the pseudofunctor of
quasi-coherent modules is a stack for the fpqc topology. -/
theorem isStack_qcohPseudofunctor_fpqc
    (hess : QuasicoherentDescentData.StandardSigmaEssSurj.{u})
    (hglob : QuasicoherentDescentData.EffectiveOverSpecBaseGlobalizes.{u + 1, u}) :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u} :=
  isStack_qcohPseudofunctor_of_forall_isEffective fun f hf D ↦
    QuasicoherentDescentData.isEffective_of_mem_fpqcPrecoverage hess hglob ⟨_, _, f⟩ hf D

/-- Quasi-coherent modules form a stack for the fpqc topology if and only if every quasi-coherent
descent datum along every fpqc covering family is effective. -/
theorem isStack_qcohPseudofunctor_iff :
    qcohPseudofunctor.{u}.IsStack Scheme.fpqcTopology.{u} ↔
      ∀ {S : Scheme.{u}} {I : Type (u + 1)} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S),
        Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S →
          ∀ D : QuasicoherentDescentData f, D.IsEffective :=
  ⟨fun _ _ _ _ _ hf D ↦ isEffective_of_isStack hf D,
    isStack_qcohPseudofunctor_of_forall_isEffective⟩

end Stacks.Descent

end
