module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.EffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.InvariantsEffective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse of the module descent equivalence is `H⁰` of the descent complex

Let `R → A` be a faithfully flat ring map.  Stacks 023N (2) says that base extension
`M ↦ (A ⊗[R] M, can)` is an equivalence from `R`-modules onto the category of descent data for
modules along `R → A`, and Stacks 023N (3) says that the inverse of that equivalence is
`(N, φ) ↦ H⁰(s(N_•))`.  The source identifies

`H⁰(s(N_•)) = {n ∈ N | 1 ⊗ n = φ(n ⊗ 1)}`,

which is `ModuleCat.invariantSubmodule R A`, the object part of the functor
`ModuleCat.pushforward R A` of Stacks 08X5.  This file builds the equivalence of part (2) *with
that functor as its inverse*, which is the content of part (3).

## Main definitions

* `Stacks.Descent.invariantsUnitNatIso` is the unit `𝟭 ≅ baseExtension ⋙ pushforward`, the
  natural isomorphism `M ≅ H⁰(s((A ⊗[R] M)_•))` given by `m ↦ 1 ⊗ m`.
* `Stacks.Descent.invariantsCounitNatIso` is the counit
  `pushforward ⋙ baseExtension ≅ 𝟭`, the natural isomorphism `A ⊗[R] H⁰(s(N_•)) ≅ N` given by
  `a ⊗ m ↦ a • m`.
* `Stacks.Descent.invariantsEquivalence` is the resulting equivalence, for a universally
  injective ring map.
* `Stacks.Descent.faithfullyFlatInvariantsEquivalence` is part (3) of Stacks 023N: the
  equivalence of part (2) whose inverse functor is `(N, φ) ↦ H⁰(s(N_•))`.

## Main results

* `ModuleCat.DescentData.isoOfBijective`: a morphism of module descent data whose underlying
  `A`-linear map is bijective is an isomorphism of descent data.
* `Stacks.Descent.faithfullyFlatInvariantsEquivalence_functor` and
  `Stacks.Descent.faithfullyFlatInvariantsEquivalence_inverse` identify the two functors of the
  equivalence with base extension and with `ModuleCat.pushforward`, and
  `Stacks.Descent.faithfullyFlatInvariantsEquivalence_inverse_obj` reads the inverse off on a
  single descent datum as `H⁰(s(N_•))`.

## Implementation notes

`CategoryTheory.Equivalence.mk` turns a unit and a counit isomorphism into an equivalence
*without changing either functor*, so the `functor` and `inverse` fields of the result are base
extension and `ModuleCat.pushforward` by definition; that is what makes the three identification
lemmas `rfl`.

The objectwise isomorphisms are already available: `ModuleCat.baseExtensionUnitEquiv` for the
unit and `Stacks.Descent.invariantsTensorEquiv` for the counit.  What this file adds is their
naturality, the descent-datum compatibility of the counit, and the assembly.  The counit is
first built as a morphism of descent data, whose `comm` field is
`Stacks.Descent.transition_smul_tmul` read on a pure tensor, and then inverted with
`ModuleCat.DescentData.isoOfBijective`.

## References

* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 08X5](https://stacks.math.columbia.edu/tag/08X5)
* [Stacks Project, Tag 08WY](https://stacks.math.columbia.edu/tag/08WY)
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory TensorProduct

namespace ModuleCat.DescentData

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The inverse of a bijective morphism of module descent data is again compatible with the
transition isomorphisms. -/
theorem inverse_comm {D E : DescentData.{u, u, w} R A} (g : D ⟶ E)
    (hg : Function.Bijective g.hom.hom) :
    (D.transition.toLinearMap.restrictScalars R).comp
        ((restrictHom R A (ModuleCat.ofHom
          (LinearEquiv.ofBijective g.hom.hom hg).symm.toLinearMap)).rTensor A) =
      ((restrictHom R A (ModuleCat.ofHom
          (LinearEquiv.ofBijective g.hom.hom hg).symm.toLinearMap)).lTensor A).comp
        (E.transition.toLinearMap.restrictScalars R) := by
  let e : D.module ≃ₗ[A] E.module := LinearEquiv.ofBijective g.hom.hom hg
  let G : restrictModule R A D.module →ₗ[R] restrictModule R A E.module :=
    restrictHom R A g.hom
  let Gi : restrictModule R A E.module →ₗ[R] restrictModule R A D.module :=
    restrictHom R A (ModuleCat.ofHom e.symm.toLinearMap)
  have hGGi : G.comp Gi = LinearMap.id := by
    ext x
    exact e.apply_symm_apply (show E.module from x)
  have hGiG : Gi.comp G = LinearMap.id := by
    ext x
    exact e.symm_apply_apply (show D.module from x)
  change (D.transition.toLinearMap.restrictScalars R).comp (Gi.rTensor A) =
    (Gi.lTensor A).comp (E.transition.toLinearMap.restrictScalars R)
  refine LinearMap.ext fun x => ?_
  have hx : G.rTensor A (Gi.rTensor A x) = x := by
    change (G.rTensor A ∘ₗ Gi.rTensor A) x = x
    rw [← LinearMap.rTensor_comp, hGGi, LinearMap.rTensor_id, LinearMap.id_apply]
  have h1 : E.transition.toLinearMap.restrictScalars R (G.rTensor A (Gi.rTensor A x)) =
      (G.lTensor A) (D.transition.toLinearMap.restrictScalars R (Gi.rTensor A x)) :=
    LinearMap.congr_fun g.comm (Gi.rTensor A x)
  rw [hx] at h1
  change D.transition.toLinearMap.restrictScalars R (Gi.rTensor A x) =
    (Gi.lTensor A) (E.transition.toLinearMap.restrictScalars R x)
  rw [h1]
  change _ = (Gi.lTensor A ∘ₗ G.lTensor A)
    (D.transition.toLinearMap.restrictScalars R (Gi.rTensor A x))
  rw [← LinearMap.lTensor_comp, hGiG, LinearMap.lTensor_id, LinearMap.id_apply]

/-- A morphism of module descent data whose underlying `A`-linear map is bijective is an
isomorphism of descent data. -/
def isoOfBijective {D E : DescentData.{u, u, w} R A} (g : D ⟶ E)
    (hg : Function.Bijective g.hom.hom) : D ≅ E where
  hom := g
  inv :=
    { hom := ModuleCat.ofHom (LinearEquiv.ofBijective g.hom.hom hg).symm.toLinearMap
      comm := inverse_comm R A g hg }
  hom_inv_id := by
    refine DescentData.Hom.ext (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact (LinearEquiv.ofBijective g.hom.hom hg).symm_apply_apply x
  inv_hom_id := by
    refine DescentData.Hom.ext (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact (LinearEquiv.ofBijective g.hom.hom hg).apply_symm_apply x

end ModuleCat.DescentData

namespace Stacks.Descent

open ModuleCat

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The transition isomorphism of a base extension, on pure tensors. -/
private theorem baseExtension_transition_tmul (M : ModuleCat.{max u w} R) (a b : A) (m : M) :
    ((baseExtension.{u, u, w} R A).functor.obj M).transition
        ((show ((baseExtension.{u, u, w} R A).functor.obj M).module from
          (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
      a ⊗ₜ[R] (show restrictModule R A ((baseExtension.{u, u, w} R A).functor.obj M).module from
        (b ⊗ₜ[R] m : ((baseExtension.{u, u, w} R A).functor.obj M).module)) :=
  (baseExtension.{u, u, w} R A).transition_tmul M a b m

/-- The counit `a ⊗ m ↦ a • m` is compatible with the transition isomorphisms, on a pure tensor
`n ⊗ b`. -/
theorem invariantsCounitHom_comm_tmul (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A)
    (n : restrictModule R A
      ((baseExtension.{u, u, w} R A).functor.obj ((pushforward R A).obj D)).module) (b : A) :
    D.transitionRestrictScalars R A
        (restrictHom R A (ModuleCat.ofHom (invariantsTensorEquiv R A h D).toLinearMap) n ⊗ₜ[R] b) =
      ((restrictHom R A (ModuleCat.ofHom (invariantsTensorEquiv R A h D).toLinearMap)).lTensor A)
        (((baseExtension.{u, u, w} R A).functor.obj
          ((pushforward R A).obj D)).transitionRestrictScalars R A (n ⊗ₜ[R] b)) := by
  let C := (baseExtension.{u, u, w} R A).functor.obj ((pushforward R A).obj D)
  let e := invariantsTensorEquiv R A h D
  let g : restrictModule R A C.module →ₗ[R] restrictModule R A D.module :=
    restrictHom R A (ModuleCat.ofHom e.toLinearMap)
  change D.transitionRestrictScalars R A ((g n) ⊗ₜ[R] b) =
    (g.lTensor A) (C.transitionRestrictScalars R A (n ⊗ₜ[R] b))
  induction n using TensorProduct.inductionOn with
  | add n₁ n₂ h₁ h₂ =>
    let n₁' : restrictModule R A C.module := n₁
    let n₂' : restrictModule R A C.module := n₂
    calc
      D.transitionRestrictScalars R A (g (n₁' + n₂') ⊗ₜ[R] b) =
          D.transitionRestrictScalars R A (g n₁ ⊗ₜ[R] b) +
            D.transitionRestrictScalars R A (g n₂ ⊗ₜ[R] b) := by
        rw [map_add, add_tmul, map_add]
      _ = (g.lTensor A) (C.transitionRestrictScalars R A (n₁ ⊗ₜ[R] b)) +
            (g.lTensor A) (C.transitionRestrictScalars R A (n₂ ⊗ₜ[R] b)) := by
        rw [h₁, h₂]
      _ = (g.lTensor A) (C.transitionRestrictScalars R A ((n₁ + n₂) ⊗ₜ[R] b)) := by
        change _ = (g.lTensor A)
          (C.transitionRestrictScalars R A ((n₁' + n₂') ⊗ₜ[R] b))
        rw [add_tmul n₁' n₂' b, map_add, map_add]
  | tmul a m =>
    change D.transitionRestrictScalars R A ((e (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
      (g.lTensor A) (C.transitionRestrictScalars R A
        ((show C.module from (a ⊗ₜ[R] m)) ⊗ₜ[R] b))
    rw [show C.transitionRestrictScalars R A
          ((show C.module from (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A C.module from (b ⊗ₜ[R] m : C.module)) from
          baseExtension_transition_tmul.{u, w} R A ((pushforward R A).obj D) a b m,
      LinearMap.lTensor_tmul]
    change D.transitionRestrictScalars R A ((e (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
      a ⊗ₜ[R] (show restrictModule R A D.module from e (b ⊗ₜ[R] m))
    rw [invariantsTensorEquiv_tmul R A h D a m, invariantsTensorEquiv_tmul R A h D b m]
    exact transition_smul_tmul R A D a b m

/-- The counit `a ⊗ m ↦ a • m` is compatible with the transition isomorphisms. -/
theorem invariantsCounitHom_comm (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (D.transition.toLinearMap.restrictScalars R).comp
        ((restrictHom R A (ModuleCat.ofHom
          (invariantsTensorEquiv R A h D).toLinearMap)).rTensor A) =
      ((restrictHom R A (ModuleCat.ofHom
          (invariantsTensorEquiv R A h D).toLinearMap)).lTensor A).comp
        (((baseExtension.{u, u, w} R A).functor.obj
          ((pushforward R A).obj D)).transition.toLinearMap.restrictScalars R) := by
  let C := (baseExtension.{u, u, w} R A).functor.obj ((pushforward R A).obj D)
  let g : restrictModule R A C.module →ₗ[R] restrictModule R A D.module :=
    restrictHom R A (ModuleCat.ofHom (invariantsTensorEquiv R A h D).toLinearMap)
  change (D.transition.toLinearMap.restrictScalars R).comp (g.rTensor A) =
    (g.lTensor A).comp (C.transition.toLinearMap.restrictScalars R)
  exact TensorProduct.ext' fun n b => invariantsCounitHom_comm_tmul.{u, w} R A h D n b

/-- The counit of the base-extension/invariants pair, as a morphism of descent data: the
base extension of `H⁰(s(N_•))` maps to `N` by `a ⊗ m ↦ a • m`. -/
def invariantsCounitHom (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (baseExtension.{u, u, w} R A).functor.obj ((pushforward R A).obj D) ⟶ D where
  hom := ModuleCat.ofHom (invariantsTensorEquiv R A h D).toLinearMap
  comm := invariantsCounitHom_comm.{u, w} R A h D

/-- The counit is an isomorphism of descent data. -/
def invariantsCounitIso (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, max u w} R A) :
    (baseExtension.{u, u, w} R A).functor.obj ((pushforward R A).obj D) ≅ D :=
  DescentData.isoOfBijective R A (invariantsCounitHom.{u, w} R A h D)
    (invariantsTensorEquiv R A h D).bijective

/-- The unit `𝟭 ≅ baseExtension ⋙ pushforward`: an `R`-module is the invariants of the canonical
descent datum on its base extension, by `m ↦ 1 ⊗ m`. -/
def invariantsUnitNatIso (h : Algebra.UniversallyInjective R A) :
    𝟭 (ModuleCat.{max u w} R) ≅
      (baseExtension.{u, u, w} R A).functor ⋙ pushforward R A :=
  NatIso.ofComponents
    (fun M => (baseExtensionUnitEquiv R A h M).toModuleIso)
    (fun {M N} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => Subtype.ext ?_)
      change (1 : A) ⊗ₜ[R] f.hom m = LinearMap.baseChange A f.hom ((1 : A) ⊗ₜ[R] m)
      rw [LinearMap.baseChange_tmul])

/-- The counit `pushforward ⋙ baseExtension ≅ 𝟭`: a descent datum is the base extension of its
invariants, by `a ⊗ m ↦ a • m`. -/
def invariantsCounitNatIso (h : Algebra.UniversallyInjective R A) :
    pushforward R A ⋙ (baseExtension.{u, u, w} R A).functor ≅
      𝟭 (DescentData.{u, u, max u w} R A) :=
  NatIso.ofComponents
    (fun D => invariantsCounitIso.{u, w} R A h D)
    (fun {D E} g => by
      refine DescentData.Hom.ext (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
      change invariantsTensorEquiv R A h E
          (LinearMap.baseChange A (pushforwardMap R A g) x) =
        g.hom.hom (invariantsTensorEquiv R A h D x)
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a m =>
        have hL : invariantsTensorEquiv R A h E
              (LinearMap.baseChange A (pushforwardMap R A g) (a ⊗ₜ[R] m)) =
            a • ((pushforwardMap R A g m).1 : E.module) := by
          rw [LinearMap.baseChange_tmul]
          exact invariantsTensorEquiv_tmul R A h E a _
        have hR : g.hom.hom (invariantsTensorEquiv R A h D (a ⊗ₜ[R] m)) =
            a • g.hom.hom (m.1 : D.module) := by
          rw [invariantsTensorEquiv_tmul R A h D a m]
          exact map_smul g.hom.hom a _
        rw [hL, hR]
        rfl)

/-- For a universally injective ring map, base extension is an equivalence from `R`-modules onto
descent data for modules along `R → A`, with inverse `ModuleCat.pushforward`, that is
`(N, φ) ↦ H⁰(s(N_•))`. -/
def invariantsEquivalence (h : Algebra.UniversallyInjective R A) :
    ModuleCat.{max u w} R ≌ DescentData.{u, u, max u w} R A :=
  CategoryTheory.Equivalence.mk (baseExtension.{u, u, w} R A).functor (pushforward R A)
    (invariantsUnitNatIso.{u, w} R A h) (invariantsCounitNatIso.{u, w} R A h)

/-- **Stacks 023N, part (3).** For a faithfully flat ring map `R → A` the functor
`M ↦ (A ⊗[R] M, can)` from `R`-modules to descent data for modules along `R → A` is an
equivalence whose inverse functor is `(N, φ) ↦ H⁰(s(N_•))`, the kernel of the descent complex.
Only part (3) is registered here; part (2), that the functor is an equivalence, is
`ModuleCat.isEffectiveDescentMorphismForModules_of_faithfullyFlat`. -/
@[stacks 023N "(3)", sga "1 VIII 1.6" "more general"]
def faithfullyFlatInvariantsEquivalence [Module.FaithfullyFlat R A] :
    ModuleCat.{max u w} R ≌ DescentData.{u, u, max u w} R A :=
  invariantsEquivalence.{u, w} R A (.of_faithfullyFlat R A)

/-- The forward functor of the equivalence of Stacks 023N is base extension. -/
theorem faithfullyFlatInvariantsEquivalence_functor [Module.FaithfullyFlat R A] :
    (faithfullyFlatInvariantsEquivalence.{u, w} R A).functor =
      (baseExtension.{u, u, w} R A).functor := rfl

/-- **Stacks 023N, part (3).** The inverse functor of the equivalence of Stacks 023N is
`ModuleCat.pushforward`, that is `(N, φ) ↦ H⁰(s(N_•))`. -/
@[stacks 023N "(3)"]
theorem faithfullyFlatInvariantsEquivalence_inverse [Module.FaithfullyFlat R A] :
    (faithfullyFlatInvariantsEquivalence.{u, w} R A).inverse = pushforward R A := rfl

/-- The inverse functor of the equivalence of Stacks 023N, read off at a single descent datum
`(N, φ)`: it is `H⁰(s(N_•)) = {n ∈ N | φ(n ⊗ 1) = 1 ⊗ n}`. -/
theorem faithfullyFlatInvariantsEquivalence_inverse_obj [Module.FaithfullyFlat R A]
    (D : DescentData.{u, u, max u w} R A) :
    (faithfullyFlatInvariantsEquivalence.{u, w} R A).inverse.obj D =
      ModuleCat.of R (invariantSubmodule R A D) := rfl

/-- The inverse functor of the equivalence of Stacks 023N sends a descent datum `(N, φ)` to the
sections of `N` on which the two pullbacks agree. -/
theorem mem_faithfullyFlatInvariantsEquivalence_inverse_obj [Module.FaithfullyFlat R A]
    (D : DescentData.{u, u, max u w} R A) (n : restrictModule R A D.module) :
    n ∈ invariantSubmodule R A D ↔
      D.transition (n ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] n := Iff.rfl

end Stacks.Descent

end
