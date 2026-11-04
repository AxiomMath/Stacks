module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.ModuleStalkTensor.Naturality
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer

/-!
# Flat pullback preserves the equalizer of two morphisms of algebras

Let `g : T ⟶ S` be a flat morphism of schemes and let `φ, ψ : A ⟶ B` be two morphisms of sheaves
of commutative `𝒪_S`-algebras. Extension of scalars along `g` carries the equalizer of `φ` and
`ψ` to the equalizer of `g⁺φ` and `g⁺ψ`.

This is the exactness statement that formation of the equalizer algebra needs in order to commute
with base change. It is *false* for an arbitrary morphism `g` — extension of scalars is only right
exact in general — and flatness is exactly what repairs it.

The proof passes to underlying `𝒪`-modules, where three things are available: the equalizer
algebra's underlying module is the equalizer of the underlying modules (`isLimitForkModule`,
both being computed on sections, where the equalizer of two ring maps and of the two underlying
additive maps are the same subset); the underlying module of an extension of scalars is the
module pullback (`Stacks.ModuleStalkTensor.comparison`, naturally in the algebra); and the module
pullback along a flat morphism is left exact
(`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`). A morphism of algebra
sheaves whose underlying module morphism is invertible is invertible
(`Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap`), which converts the module statement back
into the statement about algebras.

## Main definitions

* `Stacks.QuasicoherentAlgebraEqualizer.moduleLift` — the factorisation of a morphism of
  `𝒪_X`-modules equalizing `φ` and `ψ` through the underlying module of the equalizer algebra.
* `Stacks.QuasicoherentAlgebraEqualizer.pullbackEqualizerComparison` — the canonical morphism
  `g⁺Eq(φ, ψ) ⟶ Eq(g⁺φ, g⁺ψ)`.

## Main results

* `Stacks.QuasicoherentAlgebraEqualizer.isLimitForkModule` — **the underlying `𝒪_X`-module of the
  equalizer algebra is the equalizer of the underlying modules.**
* `Stacks.QuasicoherentAlgebraEqualizer.isIso_pullbackEqualizerComparison` and
  `Stacks.QuasicoherentAlgebraEqualizer.isLimitForkPullback` — **extension of scalars along a flat
  morphism preserves the equalizer of two morphisms of algebra sheaves.**
* `Stacks.QuasicoherentAlgebraEqualizer.isLimitForkQcohPullback` and
  `Stacks.QuasicoherentAlgebraEqualizer.preservesLimit_parallelPair_qcohAlgebraPullback` — the
  same statement for quasi-coherent algebras, as a preservation-of-limits instance.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AlgebraPullbackQcoh

universe u

namespace Stacks.QuasicoherentAlgebraEqualizer

/-! ### The underlying module of the equalizer algebra -/

section Module

variable {X : Scheme.{u}} {A B : AlgebraSheaf X} (φ ψ : A ⟶ B)

/-- Passing to the underlying module is functorial. -/
theorem moduleMap_comp {C : AlgebraSheaf X} (f : A ⟶ B) (g : B ⟶ C) :
    moduleMap (f ≫ g) = moduleMap f ≫ moduleMap g := by
  ext U x
  rfl

/-- The inclusion of the equalizer algebra equalizes `φ` and `ψ` on underlying modules. -/
theorem moduleMap_equalizerAlgebraι_comp :
    moduleMap (equalizerAlgebraι φ ψ) ≫ moduleMap φ =
      moduleMap (equalizerAlgebraι φ ψ) ≫ moduleMap ψ := by
  ext U x
  exact x.2

/-- Equal morphisms of `𝒪_X`-modules agree on sections. -/
private theorem app_apply_congr {M N : X.Modules} {f g : M ⟶ N} (h : f = g) (U : (Opens X)ᵒᵖ)
    (m : M.val.obj U) : (f.val.app U) m = (g.val.app U) m := by
  rw [h]

/-- A morphism of `𝒪_X`-modules into the underlying module of `A` equalizing `φ` and `ψ` takes
values in the subring of agreement. -/
theorem mem_eqSubring_of_moduleMap_comp_eq {M : X.Modules}
    {u : M ⟶ AlgebraSheaf.underlyingModule A} (hu : u ≫ moduleMap φ = u ≫ moduleMap ψ)
    (U : (Opens X)ᵒᵖ) (m : M.val.obj U) : (u.val.app U) m ∈ eqSubring φ ψ U := by
  exact app_apply_congr hu U m

/-- The factorisation through the underlying module of the equalizer algebra of a morphism of
`𝒪_X`-modules equalizing `φ` and `ψ`. -/
def moduleLift {M : X.Modules} (u : M ⟶ AlgebraSheaf.underlyingModule A)
    (hu : u ≫ moduleMap φ = u ≫ moduleMap ψ) :
    M ⟶ AlgebraSheaf.underlyingModule (equalizerAlgebra φ ψ) where
  val.app U := ModuleCat.homMk
    (AddCommGrpCat.ofHom
      (((u.val.app U).hom.toAddMonoidHom).codRestrict (eqSubring φ ψ U).toAddSubgroup
        (mem_eqSubring_of_moduleMap_comp_eq φ ψ hu U)))
    (fun r => by
      ext m
      exact Subtype.ext (((u.val.app U).hom.map_smul r m).symm))
  val.naturality f := by
    ext m
    exact Subtype.ext (ConcreteCategory.congr_hom (u.val.naturality f) m)

/-- On sections, the value of `moduleLift φ ψ u hu` in the subring of agreement is the value of
`u`. -/
@[simp]
theorem moduleLift_val_app_val {M : X.Modules} (u : M ⟶ AlgebraSheaf.underlyingModule A)
    (hu : u ≫ moduleMap φ = u ≫ moduleMap ψ) (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    (show ↥(eqSubring φ ψ U) from (moduleLift φ ψ u hu).val.app U m).val = (u.val.app U) m :=
  rfl

/-- The factorisation `moduleLift φ ψ u hu` followed by the inclusion of the equalizer algebra
is `u`. -/
theorem moduleLift_comp_ι {M : X.Modules} (u : M ⟶ AlgebraSheaf.underlyingModule A)
    (hu : u ≫ moduleMap φ = u ≫ moduleMap ψ) :
    moduleLift φ ψ u hu ≫ moduleMap (equalizerAlgebraι φ ψ) = u := by
  ext U m
  rfl

/-- Two morphisms of `𝒪_X`-modules into the underlying module of the equalizer algebra which
agree after the inclusion into `A` are equal. -/
theorem module_hom_ext {M : X.Modules}
    {f g : M ⟶ AlgebraSheaf.underlyingModule (equalizerAlgebra φ ψ)}
    (h : f ≫ moduleMap (equalizerAlgebraι φ ψ) = g ≫ moduleMap (equalizerAlgebraι φ ψ)) :
    f = g := by
  ext U m
  exact Subtype.ext (app_apply_congr h (op U) m)

/-- **The underlying `𝒪_X`-module of the equalizer algebra is the equalizer of the underlying
modules.** Both are computed on sections, where the equalizer of two ring maps and the
equalizer of the underlying additive maps are the same subset. -/
def isLimitForkModule :
    IsLimit (Fork.ofι (moduleMap (equalizerAlgebraι φ ψ))
      (moduleMap_equalizerAlgebraι_comp φ ψ)) :=
  Fork.IsLimit.mk _ (fun s => moduleLift φ ψ s.ι s.condition)
    (fun s => moduleLift_comp_ι φ ψ s.ι s.condition)
    (fun s _m hm => module_hom_ext φ ψ
      (hm.trans (moduleLift_comp_ι φ ψ s.ι s.condition).symm))

end Module

/-! ### Flat pullback -/

section Flat

open Stacks.AffineAlgebraEquivalence Stacks.ModuleStalkTensor

variable {T S : Scheme.{u}} (g : T ⟶ S) {A B : AlgebraSheaf S} (φ ψ : A ⟶ B)

/-- The pullback of the inclusion of the equalizer algebra equalizes the pullbacks of `φ` and
`ψ`. -/
theorem map_equalizerAlgebraι_comp :
    (algebraPullback g).map (equalizerAlgebraι φ ψ) ≫ (algebraPullback g).map φ =
      (algebraPullback g).map (equalizerAlgebraι φ ψ) ≫ (algebraPullback g).map ψ := by
  rw [← Functor.map_comp, ← Functor.map_comp, equalizerAlgebraι_comp]

/-- The canonical comparison from the pullback of the equalizer algebra to the equalizer algebra
of the pullbacks. -/
def pullbackEqualizerComparison :
    (algebraPullback g).obj (equalizerAlgebra φ ψ) ⟶
      equalizerAlgebra ((algebraPullback g).map φ) ((algebraPullback g).map ψ) :=
  lift _ _ ((algebraPullback g).map (equalizerAlgebraι φ ψ)) (map_equalizerAlgebraι_comp g φ ψ)

/-- The pullback of the inclusion of the equalizer algebra equalizes the pullbacks of `φ` and
`ψ` on underlying modules. -/
theorem moduleMap_map_equalizerAlgebraι_comp :
    moduleMap ((algebraPullback g).map (equalizerAlgebraι φ ψ)) ≫
        moduleMap ((algebraPullback g).map φ) =
      moduleMap ((algebraPullback g).map (equalizerAlgebraι φ ψ)) ≫
        moduleMap ((algebraPullback g).map ψ) := by
  rw [← moduleMap_comp, ← moduleMap_comp, map_equalizerAlgebraι_comp]

/-- **Pullback along a flat morphism preserves the equalizer, on underlying modules.** -/
def isLimitForkModulePullback [Flat g] :
    IsLimit (Fork.ofι (moduleMap ((algebraPullback g).map (equalizerAlgebraι φ ψ)))
      (moduleMap_map_equalizerAlgebraι_comp g φ ψ)) := by
  have := preservesFiniteLimits_modulesPullback_of_flat g
  have := isIso_comparison g A
  have := isIso_comparison g B
  have := isIso_comparison g (equalizerAlgebra φ ψ)
  refine Fork.isLimitOfIsos _
    (isLimitForkMapOfIsLimit (Scheme.Modules.pullback g)
      (moduleMap_equalizerAlgebraι_comp φ ψ) (isLimitForkModule φ ψ))
    _ (asIso (comparison g A)) (asIso (comparison g B))
    (asIso (comparison g (equalizerAlgebra φ ψ)))
    ((comparison_naturality g φ).symm) ((comparison_naturality g ψ).symm)
    ((comparison_naturality g (equalizerAlgebraι φ ψ)).symm)

/-- **Pullback of quasi-coherent algebras along a flat morphism of schemes preserves the
equalizer.** -/
theorem isIso_pullbackEqualizerComparison [Flat g] :
    IsIso (pullbackEqualizerComparison g φ ψ) := by
  refine isIso_of_isIso_moduleMap _ ?_
  have hfac : moduleMap (pullbackEqualizerComparison g φ ψ) ≫
      moduleMap (equalizerAlgebraι ((algebraPullback g).map φ) ((algebraPullback g).map ψ)) =
        moduleMap ((algebraPullback g).map (equalizerAlgebraι φ ψ)) := by
    rw [← moduleMap_comp]
    exact congrArg moduleMap (lift_comp_ι _ _ _ _)
  have hc := IsLimit.conePointUniqueUpToIso_hom_comp (isLimitForkModulePullback g φ ψ)
    (isLimitForkModule ((algebraPullback g).map φ) ((algebraPullback g).map ψ))
    WalkingParallelPair.zero
  have he : moduleMap (pullbackEqualizerComparison g φ ψ) =
      (IsLimit.conePointUniqueUpToIso (isLimitForkModulePullback g φ ψ)
        (isLimitForkModule ((algebraPullback g).map φ) ((algebraPullback g).map ψ))).hom :=
    Fork.IsLimit.hom_ext
      (isLimitForkModule ((algebraPullback g).map φ) ((algebraPullback g).map ψ))
      (hfac.trans hc.symm)
  rw [he]
  infer_instance

/-- The comparison `pullbackEqualizerComparison g φ ψ` followed by the inclusion of the equalizer
algebra of the pullbacks is the pullback of the inclusion of the equalizer algebra. -/
theorem pullbackEqualizerComparison_comp_ι :
    pullbackEqualizerComparison g φ ψ ≫
        equalizerAlgebraι ((algebraPullback g).map φ) ((algebraPullback g).map ψ) =
      (algebraPullback g).map (equalizerAlgebraι φ ψ) :=
  lift_comp_ι _ _ _ _

/-- **Pullback along a flat morphism of schemes preserves the equalizer of two morphisms of
algebra sheaves**: the image of the equalizer fork is again an equalizer fork. -/
def isLimitForkPullback [Flat g] :
    IsLimit (Fork.ofι ((algebraPullback g).map (equalizerAlgebraι φ ψ))
      (map_equalizerAlgebraι_comp g φ ψ)) := by
  have := isIso_pullbackEqualizerComparison g φ ψ
  refine IsLimit.ofIsoLimit (isLimitFork ((algebraPullback g).map φ) ((algebraPullback g).map ψ))
    (Fork.ext (asIso (pullbackEqualizerComparison g φ ψ)).symm ?_)
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact (pullbackEqualizerComparison_comp_ι g φ ψ).symm

end Flat

/-! ### Flat pullback of quasi-coherent algebras -/

section FlatQcoh

open Stacks.AffineAlgebraEquivalence Stacks.AlgebraPullbackQcoh

variable {T S : Scheme.{u}} (g : T ⟶ S) {A' B' : QuasicoherentAlgebra S} (φ' ψ' : A' ⟶ B')

/-- The pullback of the inclusion of the quasi-coherent equalizer algebra equalizes the
pullbacks of `φ'` and `ψ'`. -/
theorem map_quasicoherentEqualizerι_comp :
    (qcohAlgebraPullback g).map (quasicoherentEqualizerι φ' ψ') ≫
        (qcohAlgebraPullback g).map φ' =
      (qcohAlgebraPullback g).map (quasicoherentEqualizerι φ' ψ') ≫
        (qcohAlgebraPullback g).map ψ' := by
  rw [← Functor.map_comp, ← Functor.map_comp, quasicoherentEqualizerι_comp]

/-- **Pullback along a flat morphism of schemes preserves the equalizer of two morphisms of
quasi-coherent algebras.** -/
def isLimitForkQcohPullback [Flat g] :
    IsLimit (Fork.ofι ((qcohAlgebraPullback g).map (quasicoherentEqualizerι φ' ψ'))
      (map_quasicoherentEqualizerι_comp g φ' ψ')) := by
  refine isLimitOfReflects (IsQuasicoherentAlgebra T).ι ?_
  exact (isLimitMapConeForkEquiv _ _).symm (isLimitForkPullback g φ'.hom ψ'.hom)

/-- Pullback of quasi-coherent algebras along a flat morphism preserves the equalizer of any
pair of parallel morphisms. -/
instance preservesLimit_parallelPair_qcohAlgebraPullback [Flat g] :
    PreservesLimit (parallelPair φ' ψ') (qcohAlgebraPullback g) :=
  preservesLimit_of_preserves_limit_cone (isLimitQuasicoherentFork φ' ψ')
    ((isLimitMapConeForkEquiv _ _).symm (isLimitForkQcohPullback g φ' ψ'))

end FlatQcoh

end Stacks.QuasicoherentAlgebraEqualizer

end
