module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.GlobalSectionsUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Modules.DeRham

/-!
# Vanishing of the bottom de Rham differential

Let `X` be a smooth proper scheme over a field `k`. The degree-zero differential of the relative
de Rham complex of `X` over `k`,

`d : H⁰(X, 𝒪_X) ⟶ H⁰(X, Ω¹_{X/k})`,

is zero on global sections. The reason is that the global functions of a smooth proper scheme
over `k` are a finite product of finite *separable* extensions of `k`, so they are unramified
over `k` and carry no nonzero `k`-derivation; the degree-zero de Rham differential on global
sections is the universal relative derivation, so it vanishes.

## Main results

* `AlgebraicGeometry.SheafOfModules.derivation_eq_zero_of_formallyUnramified`: a relative
  derivation out of a formally unramified algebra vanishes.
* `AlgebraicGeometry.deRhamComplex_d_zero_app_top_eq_zero`: the degree-zero de Rham differential
  of a smooth proper scheme over a field is zero on global sections.

## Implementation notes

The statement is made for an arbitrary package `B` of the three algebras of Stacks Section 17.21
on the sheaf of relative differentials and an arbitrary de Rham differential `D` on it, so it
applies in particular to the canonical de Rham complex
`AlgebraicGeometry.SheafOfModules.relativeDeRhamComplex`, which by
`AlgebraicGeometry.SheafOfModules.deRhamDifferential_unique` is the only one.

Two inputs combine. The first is that the degree-zero arrow of the de Rham complex is the
universal relative derivation read on degree-zero forms, which is
`AlgebraicGeometry.SheafOfModules.deRhamComplex_degreeZero_apply`. The second is that the
`k`-algebra of global functions is unramified over `k`
(`AlgebraicGeometry.formallyUnramified_globalSections_of_smooth`), so that
`derivation_eq_zero_of_formallyUnramified` applies to the universal derivation over the whole
space. The compatibility of the two `k`-algebra structures involved — the one on the global
sections of the inverse image of the structure sheaf of `Spec k`, and the one on the global
functions of `X` — is the triangle identity of the adjunction `f⁻¹ ⊣ f_*` applied to the
structural map, which is what `AlgebraicGeometry.inverseImageStructureMap` is defined by.

## References

* [Stacks Project, Tag 0FW5](https://stacks.math.columbia.edu/tag/0FW5)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 090W](https://stacks.math.columbia.edu/tag/090W)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **A relative derivation out of a formally unramified algebra vanishes.** If `hom : R ⟶ S` is
a morphism of commutative rings under a base ring `k`, and `S` is formally unramified over `k`,
then every derivation of `S` relative to `hom` with values in an `S`-module is zero: such a
derivation is `k`-linear, hence factors through `Ω_{S/k}`, which vanishes. -/
theorem SheafOfModules.derivation_eq_zero_of_formallyUnramified {baseRing : Type*}
    [CommRing baseRing] {domain codomain : CommRingCat.{u}} [Algebra baseRing domain]
    [Algebra baseRing codomain] [Algebra.FormallyUnramified baseRing codomain]
    {target : ModuleCat.{v} codomain} (hom : domain ⟶ codomain)
    (commutes : ∀ scalar : baseRing,
      hom (algebraMap baseRing domain scalar) = algebraMap baseRing codomain scalar)
    (derivation : target.Derivation hom) (element : codomain) :
    derivation.d element = 0 := by
  let : Module baseRing target := Module.compHom target (algebraMap baseRing codomain)
  let restricted : Derivation baseRing codomain target :=
    { toFun := derivation.d
      map_add' := derivation.d_add
      map_smul' := fun scalar element => by
        rw [Algebra.smul_def, derivation.d_mul, ← commutes, derivation.d_map, smul_zero, add_zero,
          commutes]
        rfl
      map_one_eq_zero' := by simpa using derivation.d_map 1
      leibniz' := derivation.d_mul }
  have : IsScalarTower baseRing codomain target := IsScalarTower.of_compHom ..
  let equivalence :=
    KaehlerDifferential.linearMapEquivDerivation baseRing codomain (M := target)
  have : Subsingleton Ω[codomain⁄baseRing] :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hlinear : equivalence.symm restricted = 0 := by
    refine LinearMap.ext fun differential => ?_
    simp [Subsingleton.elim differential 0]
  exact DFunLike.congr_fun (equivalence.symm.injective (by simpa using hlinear)) element

/-- **The degree-zero de Rham differential of a smooth proper scheme over a field vanishes on
global sections.** -/
@[stacks 0FW5]
theorem deRhamComplex_d_zero_app_top_eq_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]
    (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier)
      (SheafOfModules.moduleOfDifferentials.{u, u, u} (inverseImageStructureMap f)))
    (D : SheafOfModules.DeRhamDifferential B) :
    ((SheafOfModules.deRhamComplex B D).d 0 1).val.app (op ⊤) = 0 := by
  let A := (TopCat.Sheaf.pullback CommRingCat f.base).obj (Spec (.of k)).sheaf
  let φ := inverseImageStructureMap f
  let U := op (⊤ : Opens X.carrier)
  let : Algebra k (X.sheaf.obj.obj U) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let baseAdjunction := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base
  let baseUnit := baseAdjunction.unit.app (Spec (.of k)).sheaf
  let structureMap : (Spec (.of k)).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf := ⟨f.c⟩
  let α : k →+* A.obj.obj U :=
    ((baseUnit.hom.app (op (⊤ : Opens (Spec (.of k))))).hom).comp
      (Scheme.ΓSpecIso (.of k)).inv.hom
  have hcompatible (r : k) : (φ.hom.app U).hom (α r) = algebraMap k (X.sheaf.obj.obj U) r := by
    have htriangle : baseUnit ≫ (TopCat.Sheaf.pushforward CommRingCat f.base).map φ =
        structureMap := by
      change baseAdjunction.homEquiv (Spec (.of k)).sheaf X.sheaf φ = structureMap
      exact (baseAdjunction.homEquiv (Spec (.of k)).sheaf X.sheaf).apply_symm_apply structureMap
    exact congrArg (fun morphism =>
      (morphism.hom.app (op (⊤ : Opens (Spec (.of k))))).hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom r)) htriangle
  let : Algebra k (A.obj.obj U) := α.toAlgebra
  let universal := (SheafOfModules.universalDerivation φ).app U
  have huniversal : ∀ z : X.sheaf.obj.obj U, universal.d z = 0 := by
    have : Algebra.FormallyUnramified k (X.sheaf.obj.obj U) :=
      formallyUnramified_globalSections_of_smooth k f
    exact fun z => SheafOfModules.derivation_eq_zero_of_formallyUnramified
      (φ.hom.app U) hcompatible universal z
  ext ω
  rw [eq_of_heq (SheafOfModules.deRhamComplex_degreeZero_apply B D U ω)]
  change (B.exteriorGenerator.val.app U)
    (universal.d (B.exteriorPieceZeroIsoUnit.hom.val.app U ω)) = 0
  exact (congrArg (B.exteriorGenerator.val.app U) (huniversal _)).trans (map_zero _)

end AlgebraicGeometry

end
