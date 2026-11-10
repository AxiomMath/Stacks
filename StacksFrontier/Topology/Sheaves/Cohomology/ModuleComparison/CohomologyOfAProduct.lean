module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksCore.Algebra.Homology.ShortComplex.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology of a product

Let `G : 𝒜 ⥤ ℬ` be a left exact additive functor between abelian categories, with `𝒜` having
enough injectives, and let `(F i)_{i ∈ I}` be a family of objects of `𝒜`.  The projections
`∏ F j ⟶ F i` induce comparison morphisms `R ⁱ G (∏ F j) ⟶ ∏ R ⁱ G (F j)`.  In degree `0` the
comparison is an isomorphism, because `R ⁰ G ≅ G` and `G` preserves the product.  In degree `1`
it is a monomorphism as soon as `I`-indexed products are exact in `ℬ`: embed each `F i` into an
injective object `J i`, compare the four-term exact sequence attached to
`0 ⟶ ∏ F i ⟶ ∏ J i ⟶ ∏ (J i / F i) ⟶ 0` with the product of the four-term exact sequences of
the `0 ⟶ F i ⟶ J i ⟶ J i / F i ⟶ 0`, and apply the four lemma.  The outer two comparison maps
are isomorphisms by the degree-zero statement, and the rightmost one is a monomorphism because
`R ¹ G` vanishes on the injective object `∏ J i`.

Applied to the module-valued sections functor over an open `U` of a topological space this is
the assertion that the canonical map from the degree-zero cohomology of a product of sheaves of
modules over `U` to the product of their degree-zero cohomologies is an isomorphism, and that
the corresponding map in degree one is injective.

## Main results

* `isIso_piComparison_rightDerivedPlus_zero`: the degree-zero comparison for a left exact
  additive functor is an isomorphism.
* `mono_piComparison_rightDerivedPlus_one`: the degree-one comparison for a left exact additive
  functor is a monomorphism.
* `isIso_piComparison_rightDerivedPlus_evaluation_zero` and
  `mono_piComparison_rightDerivedPlus_evaluation_one`: the two assertions for the cohomology of
  sheaves of modules over an open of a topological space.
* `isZero_hgroup_pi_one`: the consequence for cohomology groups — the first cohomology of a
  product of sheaves of modules over an open vanishes as soon as that of every factor does.

## References

* [Stacks Project, Tag 0D0A](https://stacks.math.columbia.edu/tag/0D0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Cohomology.ModuleComparison

universe u

/-- A product of zero objects is zero. -/
private theorem isZero_pi_aux {C : Type*} [Category* C] [HasZeroMorphisms C] {I : Type*}
    {M : I → C} [HasProduct M] (h : ∀ i, IsZero (M i)) : IsZero (∏ᶜ M) := by
  rw [IsZero.iff_id_eq_zero]
  exact Limits.Pi.hom_ext _ _ fun i => (h i).eq_of_tgt _ _

/-- A product of exact short complexes is exact, when `I`-indexed products are exact: the
homology of the product short complex is the product of the homologies, which vanishes. -/
private theorem exact_shortComplex_pi {E : Type*} [Category* E] [Abelian E] {I : Type*}
    [HasProductsOfShape I E] [HasExactLimitsOfShape (Discrete I) E] (S : I → ShortComplex E)
    (hS : ∀ i, (S i).Exact) : (ShortComplex.pi S).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  exact (isZero_pi_aux fun i =>
    (ShortComplex.exact_iff_isZero_homology (S i)).1 (hS i)).of_iso (ShortComplex.piHomologyIso S)

section LeftExact

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
  {I : Type*} [HasProductsOfShape I A] [HasProductsOfShape I B]
  [PreservesLimitsOfShape (Discrete I) G]

/-- **Degree-zero cohomology commutes with products.** For a left exact additive functor `G`
out of an abelian category with enough injectives, the comparison morphism
`R ⁰ G (∏ F j) ⟶ ∏ R ⁰ G (F j)` induced by the projections is an isomorphism. -/
theorem isIso_piComparison_rightDerivedPlus_zero (F : I → A) :
    IsIso (piComparison (G.rightDerivedPlus 0) F) :=
  have : PreservesLimitsOfShape (Discrete I) (G.rightDerivedPlus 0) :=
    preservesLimitsOfShape_of_natIso (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso G).symm
  inferInstance

/-- **Degree-one cohomology injects into the product.** For a left exact additive functor `G`
out of an abelian category with enough injectives, and with `I`-indexed products exact in the
target, the comparison morphism `R ¹ G (∏ F j) ⟶ ∏ R ¹ G (F j)` induced by the projections is a
monomorphism. -/
theorem mono_piComparison_rightDerivedPlus_one [HasExactLimitsOfShape (Discrete I) B]
    (F : I → A) : Mono (piComparison (G.rightDerivedPlus 1) F) := by
  let R0 := G.rightDerivedPlus 0
  let R1 := G.rightDerivedPlus 1
  have hdelta := Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal G
    (DerivedIndexing.derivedDeltaFunctorStructure G) (DerivedIndexing.canonicalδ G)
    (fun _ _ => rfl)
  obtain ⟨_, _, _, hleft, hright, hnat⟩ := hdelta.1
  let Ires : (i : I) → InjectiveResolution (F i) := fun i => injectiveResolution (F i)
  let J : I → A := fun i => (Ires i).cocomplex.X 0
  let ι : (i : I) → F i ⟶ J i := fun i => (Ires i).ι.f 0
  let P := ∏ᶜ F
  let Q := ∏ᶜ J
  let η : P ⟶ Q := Limits.Pi.map ι
  have hιmono (i : I) : Mono (ι i) := mono_of_isLimit_fork (Ires i).isLimitKernelFork
  have : ∀ i, Mono (ι i) := hιmono
  have hη : Mono η := by
    apply Preadditive.mono_of_cancel_zero η
    intro W f hf
    apply Limits.Pi.hom_ext
    intro i
    apply (cancel_mono (ι i)).1
    simpa [η] using congrArg (fun g => g ≫ Limits.Pi.π J i) hf
  have : Injective Q := by
    dsimp [Q]
    have : ∀ i, Injective (J i) := fun i => inferInstanceAs (Injective (J i))
    infer_instance
  let Cprod := ∏ᶜ (fun i => cokernel (ι i))
  let q : Q ⟶ Cprod := Limits.Pi.map (fun i => cokernel.π (ι i))
  have hηq : η ≫ q = 0 := by
    apply Limits.Pi.hom_ext
    intro i
    simp [η, q]
  let γ := cokernel.desc η q hηq
  have hker : IsLimit (KernelFork.ofι η hηq) := by
    refine KernelFork.IsLimit.ofι η hηq (fun {W} a ha =>
      Limits.Pi.lift fun i =>
        Abelian.monoLift (ι i) (a ≫ Limits.Pi.π J i) (by
          simpa [q] using congrArg
            (fun f => f ≫ Limits.Pi.π (fun i => cokernel (ι i)) i) ha)) ?_ ?_
    · intro W a ha
      apply Limits.Pi.hom_ext
      intro i
      simp [η]
    · intro W a ha m hm
      apply (cancel_mono η).1
      rw [hm]
      apply Limits.Pi.hom_ext
      intro i
      simp [η]
  have hkerExact : (ShortComplex.mk η q hηq).Exact := ShortComplex.exact_of_f_is_kernel _ hker
  have hγ : Mono γ := hkerExact.mono_cokernelDesc
  let Si (i : I) : ShortComplex A :=
    ShortComplex.mk (ι i) (cokernel.π (ι i)) (cokernel.condition (ι i))
  have hSi (i : I) : (Si i).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (ι i)) (hιmono i)
      (inferInstanceAs (Epi (cokernel.π (ι i))))
  let S : ShortComplex A := ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact η) hη
      (inferInstanceAs (Epi (cokernel.π η)))
  let e0 := Stacks.RightDerivedPlus.rightDerivedPlusZeroIso G
  have : PreservesLimitsOfShape (Discrete I) R0 := preservesLimitsOfShape_of_natIso e0.symm
  have : PreservesFiniteLimits R0 := preservesFiniteLimits_of_natIso e0.symm
  let Ti (i : I) : ShortComplex B :=
    ShortComplex.mk (R0.map (Si i).g) (DerivedIndexing.canonicalδ G (hSi i) 0)
      (Classical.choose (hleft (hSi i) 0))
  have hTi (i : I) : (Ti i).Exact := by
    simpa [Ti] using Classical.choose_spec (hleft (hSi i) 0)
  let Tlim := ShortComplex.pi Ti
  have hTlim : Tlim.Exact := exact_shortComplex_pi Ti hTi
  have hTf : Tlim.f = Limits.Pi.map (fun i => R0.map (Si i).g) := rfl
  have hTg : Tlim.g = Limits.Pi.map (fun i => DerivedIndexing.canonicalδ G (hSi i) 0) := rfl
  let χ : Tlim.X₃ ⟶ ∏ᶜ (fun i => R1.obj (J i)) := Limits.Pi.map (fun i => R1.map (ι i))
  let Rupper : ComposableArrows B 3 :=
    ComposableArrows.mk₃ (R0.map S.g) (DerivedIndexing.canonicalδ G hS 0) (R1.map S.f)
  let Rlower : ComposableArrows B 3 := ComposableArrows.mk₃ Tlim.f Tlim.g χ
  let α₀ : R0.obj Q ⟶ Rlower.obj' 0 := piComparison R0 J
  let α₁ : R0.obj (cokernel η) ⟶ Rlower.obj' 1 :=
    R0.map γ ≫ piComparison R0 (fun i => cokernel (ι i))
  let α₂ : R1.obj P ⟶ Rlower.obj' 2 := piComparison R1 F
  let α₃ : R1.obj Q ⟶ Rlower.obj' 3 := piComparison R1 J
  let ψ (i : I) : S ⟶ Si i :=
    ShortComplex.homMk (Limits.Pi.π F i) (Limits.Pi.π J i)
      (cokernel.desc η (Limits.Pi.π J i ≫ cokernel.π (ι i)) (by simp [η]))
      (by change Limits.Pi.π F i ≫ ι i = η ≫ Limits.Pi.π J i; simp [η])
      (by simp [S, Si])
  have hSγ : S.g ≫ γ = q := by simp [S, γ]
  let Φ : Rupper ⟶ Rlower := ComposableArrows.homMk₃ α₀ α₁ α₂ α₃
    (by
      change R0.map S.g ≫ (R0.map γ ≫ piComparison R0 (fun i => cokernel (ι i))) =
        piComparison R0 J ≫ Tlim.f
      rw [hTf, ← Category.assoc, ← Functor.map_comp, hSγ]
      simpa [q] using
        (DerivedProducts.piComparison_naturality R0 J (fun i => cokernel (ι i))
          (fun i => cokernel.π (ι i))).symm)
    (by
      change DerivedIndexing.canonicalδ G hS 0 ≫ piComparison R1 F =
        (R0.map γ ≫ piComparison R0 (fun i => cokernel (ι i))) ≫ Tlim.g
      rw [hTg]
      apply Limits.Pi.hom_ext
      intro i
      have hproj :
          Limits.Pi.map (fun j => DerivedIndexing.canonicalδ G (hSi j) 0) ≫
              Limits.Pi.π (fun j => R1.obj (F j)) i =
            Limits.Pi.π (fun j => R0.obj (cokernel (ι j))) i ≫
              DerivedIndexing.canonicalδ G (hSi i) 0 :=
        Limits.Pi.map_π (fun j => DerivedIndexing.canonicalδ G (hSi j) 0) i
      have hψi : γ ≫ Limits.Pi.π (fun i => cokernel (ι i)) i = (ψ i).τ₃ := by
        apply (cancel_epi (cokernel.π η)).1
        simp [ψ, q, γ]
      calc
        (DerivedIndexing.canonicalδ G hS 0 ≫ piComparison R1 F) ≫
            Limits.Pi.π (fun j => R1.obj (F j)) i =
          DerivedIndexing.canonicalδ G hS 0 ≫ R1.map (Limits.Pi.π F i) := by
            simp [Limits.piComparison_comp_π]
        _ = R0.map ((ψ i).τ₃) ≫ DerivedIndexing.canonicalδ G (hSi i) 0 :=
          (hnat hS (hSi i) (ψ i) 0).symm
        _ = ((R0.map γ ≫ piComparison R0 (fun j => cokernel (ι j))) ≫
            Limits.Pi.map (fun j => DerivedIndexing.canonicalδ G (hSi j) 0)) ≫
              Limits.Pi.π (fun j => R1.obj (F j)) i := by
            rw [Category.assoc, hproj, ← Category.assoc, Category.assoc (R0.map γ),
              Limits.piComparison_comp_π, ← Functor.map_comp, hψi])
    (by
      change R1.map S.f ≫ piComparison R1 J =
        piComparison R1 F ≫ Limits.Pi.map (fun i => R1.map (ι i))
      exact (DerivedProducts.piComparison_naturality R1 F J ι).symm)
  have hupperZero : Rupper.map' 0 2 = 0 := by
    change R0.map S.g ≫ DerivedIndexing.canonicalδ G hS 0 = 0
    exact Classical.choose (hleft hS 0)
  have hupperExact :
      (ComposableArrows.mk₂ (Rupper.map' 1 2) (Rupper.map' 2 3)).Exact := by
    change (ComposableArrows.mk₂ (DerivedIndexing.canonicalδ G hS 0) (R1.map S.f)).Exact
    exact (Classical.choose_spec (hright hS 0)).exact_toComposableArrows
  have hlowerExact :
      (ComposableArrows.mk₂ (Rlower.map' 0 1) (Rlower.map' 1 2)).Exact := by
    change (ComposableArrows.mk₂ Tlim.f Tlim.g).Exact
    exact hTlim.exact_toComposableArrows
  have hα₀ : Epi (ComposableArrows.app' Φ 0) := by
    dsimp [Φ, α₀]
    infer_instance
  have hα₁ : Mono (ComposableArrows.app' Φ 1) := by
    dsimp [Φ, α₁]
    infer_instance
  have hα₃ : Mono (ComposableArrows.app' Φ 3) := by
    have hzero : IsZero (R1.obj Q) :=
      Functor.isZero_rightDerivedPlus_obj_injective G 1 (by norm_num) Q
    exact hzero.mono α₃
  exact Abelian.mono_of_epi_of_mono_of_mono' Φ hupperZero hupperExact hlowerExact hα₀ hα₁ hα₃

end LeftExact

/-- Products of sheaves of modules indexed by a type in the universe of the sections; named so
that instance search does not time out finding them (Mathlib v4.35.0). -/
instance (priority := high) hasLimitsOfShape_discrete_sheafOfModules
    {X : Type u} [TopologicalSpace X] (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (I : Type u) : HasLimitsOfShape (Discrete I) (SheafOfModules.{u} O) :=
  SheafOfModules.hasLimitsOfShape.{u} _ _

/-- The limit of a discrete diagram of sheaves of modules, from
`hasLimitsOfShape_discrete_sheafOfModules`, ahead of the generic instances whose search times
out. -/
instance (priority := high) hasLimit_discrete_sheafOfModules
    {X : Type u} [TopologicalSpace X] {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {I : Type u} (K : Discrete I ⥤ SheafOfModules.{u} O) : HasLimit K :=
  (hasLimitsOfShape_discrete_sheafOfModules O I).has_limit K

section Space

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]

/-- **Degree-zero cohomology of modules on a ringed space commutes with arbitrary products**:
the canonical map from the degree-zero cohomology over an open `U` of a product of sheaves of
modules to the product of their degree-zero cohomologies is an isomorphism. -/
@[stacks 0D0A "degree zero"]
theorem isIso_piComparison_rightDerivedPlus_evaluation_zero
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    {I : Type u} (F : I → SheafOfModules.{u} O) :
    IsIso (piComparison ((SheafOfModules.evaluation O (op U)).rightDerivedPlus 0) F) :=
  isIso_piComparison_rightDerivedPlus_zero _ F

/-- **Degree-one cohomology of modules on a ringed space injects into the product**: the
canonical map from the degree-one cohomology over an open `U` of a product of sheaves of
modules to the product of their degree-one cohomologies is a monomorphism. -/
@[stacks 0D0A "degree one"]
theorem mono_piComparison_rightDerivedPlus_evaluation_one
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    {I : Type u} (F : I → SheafOfModules.{u} O) :
    Mono (piComparison ((SheafOfModules.evaluation O (op U)).rightDerivedPlus 1) F) :=
  mono_piComparison_rightDerivedPlus_one _ F

end Space

/-! ### Vanishing of the first cohomology of a product -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- A product of zero objects is zero. -/
theorem isZero_pi {C : Type*} [Category* C] [HasZeroMorphisms C] {I : Type*} {M : I → C}
    [HasProduct M] (h : ∀ i, IsZero (M i)) : IsZero (∏ᶜ M) :=
  isZero_pi_aux h

/-- The cohomology group `H^n(U, P)` vanishes exactly when the `n`-th right derived functor of
module-valued sections over `U` does. -/
theorem isZero_hgroup_iff_isZero_rightDerivedPlus_evaluation (U : Opens X) {m : ℤ} {n : ℕ}
    (hmn : m = n) (P : SheafOfModules.{u} O) :
    IsZero (Hgroup O U n P) ↔
      IsZero (((SheafOfModules.evaluation O (op U)).rightDerivedPlus m).obj P) := by
  have hiso : Hgroup O U n P ≅
      (forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).obj
        (((SheafOfModules.evaluation O (op U)).rightDerived n).obj P) :=
    ((rightDerivedEvaluationForgetIso O U n).app P).symm
  rw [DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ hmn]
  exact ⟨fun h ↦ ModuleCat.isZero_iff_subsingleton.mpr
      (AddCommGrpCat.subsingleton_of_isZero (h.of_iso hiso.symm)),
    fun h ↦ ((forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).map_isZero h).of_iso
      hiso⟩

/-- **The first cohomology of a product vanishes when that of every factor does.** This is the
cohomology-group form of the degree-one clause of Stacks 0D0A: the comparison map into the
product of the first cohomologies is a monomorphism, and the product vanishes. -/
theorem isZero_hgroup_pi_one (U : Opens X) {I : Type u} (F : I → SheafOfModules.{u} O)
    (h : ∀ i, IsZero (Hgroup O U 1 (F i))) :
    IsZero (Hgroup O U 1 (∏ᶜ F)) := by
  have hfac : ∀ i, IsZero
      (((SheafOfModules.evaluation O (op U)).rightDerivedPlus 1).obj (F i)) := fun i =>
    (isZero_hgroup_iff_isZero_rightDerivedPlus_evaluation O U (by norm_num) (F i)).1 (h i)
  have : Mono (piComparison ((SheafOfModules.evaluation O (op U)).rightDerivedPlus 1) F) :=
    mono_piComparison_rightDerivedPlus_evaluation_one O U F
  refine (isZero_hgroup_iff_isZero_rightDerivedPlus_evaluation O U
    (m := (1 : ℤ)) (n := 1) (by norm_num) (∏ᶜ F)).2 ?_
  exact IsZero.of_mono (piComparison ((SheafOfModules.evaluation O (op U)).rightDerivedPlus 1) F)
    (isZero_pi hfac)

end Vanishing

end Stacks.Cohomology.ModuleComparison
