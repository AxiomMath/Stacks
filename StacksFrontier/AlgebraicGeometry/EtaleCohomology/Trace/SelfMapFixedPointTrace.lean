module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.HomologyTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of an endomorphism over the base on `RΓ(Y, f^{-1} C)`, and its trace

Let `f : Y ⟶ S` be a morphism of schemes, `φ : Y ⟶ Y` an endomorphism over `S` (so
`φ ≫ f = f`), and `C` a bounded below complex of sheaves of `Λ`-modules on `S_étale`. The
complex `f^{-1} C` carries a canonical twist `f^{-1} C ⟶ φ_* f^{-1} C`: the adjoint, under
`f^{-1} ⊣ f_*`, of the unit `C ⟶ f_* f^{-1} C` followed by `f_* ≅ f_* ∘ φ_*`. Equivalently it is
the unit of `φ^{-1} ⊣ φ_*` followed by `φ_*` of the canonical isomorphism
`φ^{-1} f^{-1} C ≅ (φ ≫ f)^{-1} C = f^{-1} C`. Applying `RΓ(S, Rf_* -)` gives the pullback
action `φ^*` on `RΓ(Y, f^{-1} C)`.

For `S = Spec k̄`, `Y = Ȳ_k̄` the base change of a smooth projective curve over a finite field
`k`, `C = Z/ℓ^n` and `φ = g^{-1} π` a deck transformation composed with the geometric Frobenius,
this is the endomorphism `(g^{-1} π_Y)^*` of `RΓ(Ȳ_k̄, Z/ℓ^n)` whose trace Step 9 of the proof
of [Stacks, Tag 03UG] computes as the number of fixed points of `g^{-1} π_Y`, from Weil's
formula [Stacks, Tag 03U1].

## Main definitions

* `Stacks.EtaleCohomology.selfMapTwistAdj`, `Stacks.EtaleCohomology.selfMapTwist` — the twist
  `f^{-1} ⟶ f^{-1} ⋙ φ_*` and its adjoint.
* `Stacks.EtaleCohomology.selfMapCohomologyEndo` — the endomorphism `φ^*` of
  `RΓ(S, Rf_*(f^{-1} C))`.
* `Stacks.EtaleCohomology.fixedSections` — the sections `y : S ⟶ Y` of `f` fixed by `φ`; for
  `S = Spec k̄` these are the fixed `k̄`-points of `φ`.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_selfMapCohomologyEndo_eq_sum` — the trace of `φ^*`
  is the alternating sum of the traces of `φ^*` on the cohomology modules, when these are finite
  projective (from `CategoryTheory.FilteredDerived.perfectDerivedTrace_eq_homologyTrace`).
* `Stacks.EtaleCohomology.perfectDerivedTrace_selfMapCohomologyEndo_eq_card` — Step 9's form:
  the trace of `φ^*` is the number of fixed points, given that the cohomology modules are finite
  projective and that the alternating sum of the degreewise traces is the number of fixed points.
  Neither declaration is registered: for a curve, the two inputs are the computation of
  `H^i(Ȳ_k̄, Z/ℓ^n)` ([Stacks, Tag 03RQ], with the Jacobian) and Weil's formula
  [Stacks, Tag 03U1] read in étale cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Twist

variable (Λ : Type r) [Ring Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)

/-- The identification `φ_* ⋙ f_* ≅ f_*` of direct images for an endomorphism `φ` over `S`. -/
public abbrev selfMapDirectImageComp :
    etaleModuleDirectImage.{u, r} Λ φ ⋙ etaleModuleDirectImage.{u, r} Λ f ≅
      etaleModuleDirectImage.{u, r} Λ f :=
  etaleModuleDirectImageComp.{u, r} Λ φ f f w.symm

/-- The transformation `M ⟶ f_* φ_* f^{-1} M` adjoint to the twist: the unit of `f^{-1} ⊣ f_*`
followed by the identification `f_* ≅ f_* ∘ φ_*`. -/
public def selfMapTwistAdj :
    𝟭 (EtaleModules.{u, r} Λ S) ⟶
      (etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ φ) ⋙
        etaleModuleDirectImage.{u, r} Λ f :=
  (etaleModuleInverseImageAdj.{u, r} Λ f).unit ≫
    Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ f)
      (selfMapDirectImageComp.{u, r} Λ f φ w).inv ≫
    (Functor.associator _ _ _).inv

/-- **The twist `f^{-1} ⟶ φ_* ∘ f^{-1}`** for an endomorphism `φ` of `Y` over `S`: the adjoint,
under `f^{-1} ⊣ f_*`, of `Stacks.EtaleCohomology.selfMapTwistAdj`. On a sheaf pulled back from
`S` it is the map `f^{-1} M ⟶ φ_* f^{-1} M` adjoint to the canonical isomorphism
`φ^{-1} f^{-1} M ≅ f^{-1} M`. -/
public def selfMapTwist :
    etaleModuleInverseImage.{u, r} Λ f ⟶
      etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ φ :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (selfMapTwistAdj.{u, r} Λ f φ w) (etaleModuleInverseImage.{u, r} Λ f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleDirectImage.{u, r} Λ φ)
      (etaleModuleInverseImageAdj.{u, r} Λ f).counit ≫
    (Functor.rightUnitor _).hom

/-- The component of the twist at `M` is the adjoint of the component of
`Stacks.EtaleCohomology.selfMapTwistAdj`. -/
public lemma selfMapTwist_app (M : EtaleModules.{u, r} Λ S) :
    (selfMapTwist.{u, r} Λ f φ w).app M =
      ((etaleModuleInverseImageAdj.{u, r} Λ f).homEquiv _ _).symm
        ((selfMapTwistAdj.{u, r} Λ f φ w).app M) := by
  simp [selfMapTwist, Adjunction.homEquiv_counit]

/-- The twist of a bounded below complex `f^{-1} C` pulled back from `S`, as a morphism of
bounded below complexes `f^{-1} C ⟶ φ_*(f^{-1} C)`. -/
public def selfMapComplexTwist (C : CochainComplex.Plus (EtaleModules.{u, r} Λ S)) :
    (etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C ⟶
      (etaleModuleDirectImage.{u, r} Λ φ).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C) :=
  ObjectProperty.homMk (X := (etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C)
    (Y := (etaleModuleDirectImage.{u, r} Λ φ).mapCochainComplexPlus.obj
      ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C))
    ((NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w)
      (ComplexShape.up ℤ)).app C.obj)

/-- The complex `RΓ(S, Rf_*(f^{-1} C))`; for `S = Spec k̄` it is `RΓ(Y, f^{-1} C)`. -/
public abbrev selfMapCohomology (C : CochainComplex.Plus (EtaleModules.{u, r} Λ S)) :
    DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ S).obj
    ((etaleModuleDerivedDirectImage.{u, r} Λ f).obj
      (DerivedCategory.Plus.Q.obj
        ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C)))

/-- **The pullback action `φ^*` on `RΓ(S, Rf_*(f^{-1} C))`** of an endomorphism `φ` of `Y` over
`S`: the derived endomorphism `Stacks.EtaleCohomology.CategoryTheory.Functor.derivedTwistEndo`
attached to the twist `f^{-1} C ⟶ φ_*(f^{-1} C)` and to `φ_* ⋙ f_* ≅ f_*`, with `F₂` the global
sections over `S`. -/
@[sga "5 XII 6.1" "special case"]
public def selfMapCohomologyEndo (C : CochainComplex.Plus (EtaleModules.{u, r} Λ S)) :
    selfMapCohomology.{u, r} Λ f C ⟶ selfMapCohomology.{u, r} Λ f C :=
  Functor.derivedTwistEndo (etaleModuleDirectImage.{u, r} Λ φ) (etaleModuleDirectImage.{u, r} Λ f)
    (etaleModuleGlobalSections.{u, r} Λ S) (selfMapDirectImageComp.{u, r} Λ f φ w)
    ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.obj C)
    (selfMapComplexTwist.{u, r} Λ f φ w C)

end Twist

/-- The sections `y : S ⟶ Y` of `f : Y ⟶ S` fixed by an endomorphism `φ` of `Y`. For
`S = Spec k̄` these are the `k̄`-points of `Y` over `k̄` fixed by `φ`. -/
public def fixedSections {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) : Type u :=
  {y : S ⟶ Y // y ≫ f = 𝟙 S ∧ y ≫ φ = y}

section Trace

open CategoryTheory.FilteredDerived

variable (Λ : Type r) [Ring Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (C : CochainComplex.Plus (EtaleModules.{u, r} Λ S))

/-- **The trace of `φ^*` on `RΓ(S, Rf_*(f^{-1} C))` degree by degree.** When every cohomology
module `H^i` of the perfect complex `RΓ(S, Rf_*(f^{-1} C))` is finite projective, the trace of
`φ^*` is `∑_i (-1)^i Tr(φ^* | H^i)`. -/
public theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_sum
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hH : HasFiniteProjectiveHomology Λ
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) =
      ∑ᶠ i : ℤ, signedByDegree Λ i (derivedHomologyTrace Λ _ hH
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) i) :=
  perfectDerivedTrace_eq_homologyTrace Λ ⟨_, hperf⟩ _ hH

/-- **Step 9 of [Stacks, Tag 03UG], reduced to its two inputs.** The trace of `φ^*` on
`RΓ(S, Rf_*(f^{-1} C))` is the number of sections of `f` fixed by `φ`, provided every cohomology
module is finite projective (`hH`) and the alternating sum of the traces of `φ^*` on the
cohomology modules is that number (`hweil`). For `Y = Ȳ_k̄` a smooth projective curve,
`S = Spec k̄`, `C = Z/ℓ^n` and `φ = g^{-1} π`, the first is the computation of `H^i(Ȳ_k̄, Z/ℓ^n)`
of [Stacks, Tag 03RQ] and the second is Weil's formula [Stacks, Tag 03U1] with
`H^1(Ȳ_k̄, μ_{ℓ^n}) = J[ℓ^n]`, `φ^*` acting on `H^2` by `deg φ`, and the fixed points of
`g^{-1} π` having multiplicity one. -/
public theorem perfectDerivedTrace_selfMapCohomologyEndo_eq_card
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hH : HasFiniteProjectiveHomology Λ
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, r} Λ f C)))
    (hweil : ∑ᶠ i : ℤ, signedByDegree Λ i (derivedHomologyTrace Λ _ hH
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) i) =
      additiveCommutatorQuotientMk Λ (Nat.card (fixedSections f φ))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (selfMapCohomologyEndo.{u, r} Λ f φ w C)) =
      additiveCommutatorQuotientMk Λ (Nat.card (fixedSections f φ)) := by
  rw [perfectDerivedTrace_selfMapCohomologyEndo_eq_sum Λ f φ w C hperf hH, hweil]

end Trace

end Stacks.EtaleCohomology

end
