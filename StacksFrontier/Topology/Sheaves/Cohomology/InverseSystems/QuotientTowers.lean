module

import StacksFrontier.RingTheory.Filtration.AssociatedGradedGenerators
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedLinear
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksFrontier.Topology.Algebra.OpenMapping
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The topology on a limit of cohomology groups

Let `I` be an ideal of a ring `A` and let `(F_n)` be a tower of sheaves of `A`-modules on `X`
whose transition maps are the quotient maps `F_{n+1} → F_{n+1} / I^{n+1} F_{n+1} ≅ F_n`. If the
graded module of stable images in the cohomology groups `Hᵖ(X, IⁿF_n)` satisfies ACC over
`gr_I(A)`, then the inverse-limit topology on `lim Hᵖ(X, F_n)` is the `I`-adic topology.

## Main definitions

* `Stacks.Cohomology.QuotientTowers.CohomologyTowerLimit`: the inverse limit of a tower of
  modules, with its inverse-limit topology `CohomologyTowerLimit.limitTopology`.
* `Stacks.Cohomology.QuotientTowers.powerSheaf`: the subsheaf `IⁿF` of a sheaf of modules `F`.
* `Stacks.Cohomology.QuotientTowers.cohomology`: sheaf cohomology, the right derived functors of
  global sections.
* `Stacks.Cohomology.QuotientTowers.IsQuotientTower`: the transition maps of the tower are the
  cokernels of the inclusions `I^{n+1}F_{n+1} → F_{n+1}`.
* `Stacks.Cohomology.QuotientTowers.stableImage`: the intersection of the images of the maps
  `Hᵖ(X, IⁿF_m) → Hᵖ(X, IⁿF_n)` for `m ≥ n`.
* `Stacks.Cohomology.QuotientTowers.StableImagesHaveGradedACC`: the direct sum of the stable
  images, with its canonical action of `AssociatedGraded.gradedRing I`, is a Noetherian module.

## Main results

* `Stacks.Cohomology.QuotientTowers.cohomologyTowerLimit_topology_eq_adic`: the inverse-limit
  topology on `lim Hᵖ(X, F_n)` is the `I`-adic topology.

## Implementation notes

The ring, the space and the sheaf values have independent universe parameters.

## References

* [Stacks Project, Tag 0GYN](https://stacks.math.columbia.edu/tag/0GYN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v w

namespace Stacks.Cohomology.QuotientTowers

variable {A : Type u} [CommRing A]

/-- The inverse limit of a tower of modules, as the submodule of compatible
sequences. -/
def CohomologyTowerLimit (C : ℕ → Type v)
    [∀ n, AddCommGroup (C n)] [∀ n, Module A (C n)]
    (f : ∀ n, C (n + 1) →ₗ[A] C n) : Submodule A (∀ n, C n) where
  carrier := {x | ∀ n, f n (x (n + 1)) = x n}
  zero_mem' n := by simp
  add_mem' hx hy n := by simp [hx n, hy n]
  smul_mem' a x hx n := by simp [hx n]

/-- Projection from the inverse limit to a term of the tower. -/
def CohomologyTowerLimit.proj (C : ℕ → Type v)
    [∀ n, AddCommGroup (C n)] [∀ n, Module A (C n)]
    (f : ∀ n, C (n + 1) →ₗ[A] C n) (n : ℕ) :
    CohomologyTowerLimit C f →ₗ[A] C n :=
  LinearMap.comp (LinearMap.proj n) (CohomologyTowerLimit C f).subtype

section

attribute [-instance] CompleteLattice.toCompletePartialOrder

/-- The inverse-limit topology: every term of the tower is discrete and the
limit has the topology induced from their product. -/
@[instance_reducible]
def CohomologyTowerLimit.limitTopology (C : ℕ → Type v)
    [∀ n, AddCommGroup (C n)] [∀ n, Module A (C n)]
    (f : ∀ n, C (n + 1) →ₗ[A] C n) :
    TopologicalSpace (CohomologyTowerLimit C f) :=
  @TopologicalSpace.induced (CohomologyTowerLimit C f) (∀ n, C n)
    (fun x ↦ x.1) (@Pi.topologicalSpace ℕ C (fun _ ↦ ⊥))

end

/-- The forgetful functor from `A`-modules to types preserves filtered colimits. -/
local instance moduleFiltered [Small.{v} A] : PreservesFilteredColimits
    (forget (ModuleCat.{v} A)) := by
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv.{v} A)
  change PreservesFilteredColimits (e.functor ⋙ forget (ModuleCat.{v} (Shrink.{v} A)))
  infer_instance

/-- The category of `A`-modules is a Grothendieck abelian category. -/
local instance moduleGrothendieck [Small.{v} A] :
    IsGrothendieckAbelian.{v} (ModuleCat.{v} A) :=
  IsGrothendieckAbelian.of_equivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv.{v} A)).symm

/-- The forgetful functor from `A`-modules to types preserves filtered colimits indexed by
categories in universe `w`. -/
local instance moduleFilteredSmall [Small.{v} A] [UnivLE.{max w v, v}] :
    PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{v} A)) :=
  preservesFilteredColimitsOfSize_of_univLE.{v, v, w, w} _

variable {X : Type w} [TopologicalSpace X]

/-- Sheaves of modules, with independent coefficient, value, and space universes. -/
abbrev ModuleSheaf (A : Type u) [CommRing A] (X : Type w) [TopologicalSpace X] :=
  Sheaf (Opens.grothendieckTopology X) (ModuleCat.{v} A)

/-- The category of sheaves of `A`-modules on `X` is a Grothendieck abelian category. -/
local instance sheafGrothendieck [Small.{v} A] [UnivLE.{max w v, v}] :
    IsGrothendieckAbelian.{v} (ModuleSheaf.{u, v, w} A X) := by
  let : ∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow U (equivSmallModel.{v} (Opens X)).inverse.op) (ModuleCat.{v} A) :=
    fun _ => ModuleCat.hasLimitsOfShape
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{v} _ _

/-- Modules multiplied by an ideal, functorially in the module. -/
def idealMultipleFunctor (J : Ideal A) : ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj M := ModuleCat.of A ↥(J • (⊤ : Submodule A M))
  map f := ModuleCat.ofHom (f.hom.restrict (Submodule.smul_top_le_comap_smul_top J f.hom))
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

section

attribute [-instance] CategoryTheory.catToReflQuiver

/-- The sectionwise inclusion of the ideal multiple. -/
def idealMultipleι (J : Ideal A) : idealMultipleFunctor.{u, v} J ⟶ 𝟭 _ where
  app M := ModuleCat.ofHom (J • (⊤ : Submodule A M)).subtype

end

/-- Multiplication by a fixed element of an ideal, with codomain restricted to the ideal
multiple. -/
private def idealMultipleFromScalar (J : Ideal A) (a : A) (ha : a ∈ J) :
    𝟭 (ModuleCat.{v} A) ⟶ idealMultipleFunctor.{u, v} J where
  app M := ModuleCat.ofHom
    { toFun x := ⟨a • x, Submodule.smul_mem_smul ha (by simp)⟩
      map_add' x y := Subtype.ext (smul_add _ _ _)
      map_smul' b x := Subtype.ext (smul_comm a b x) }
  naturality {M N} f := by
    ext x
    exact Subtype.ext (f.hom.map_smul a x).symm

private theorem idealMultipleFromScalar_comp_ι (J : Ideal A) (a : A) (ha : a ∈ J) :
    idealMultipleFromScalar.{u, v} J a ha ≫ idealMultipleι J = a • 𝟙 _ := by
  ext M x
  rfl

/-- Composing the transition maps of a functor on `ℕᵒᵖ` composes the corresponding morphisms. -/
private theorem map_homOfLE_comp {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C) {a b c : ℕ}
    (h₁ : b ≤ a) (h₂ : c ≤ b) :
    F.map (homOfLE h₁).op ≫ F.map (homOfLE h₂).op = F.map (homOfLE (h₂.trans h₁)).op := by
  rw [← F.map_comp]
  rfl

section SheafConstructions

variable [Small.{v} A] [UnivLE.{max w v, v}]

/-- The power-ideal subsheaf: sheafify the sectionwise ideal multiple. -/
@[implicit_reducible]
def powerSheaf (I : Ideal A) (n : ℕ) (F : ModuleSheaf.{u, v, w} A X) : ModuleSheaf.{u, v, w} A X :=
  (presheafToSheaf _ _).obj (F.obj ⋙ idealMultipleFunctor (I ^ n))

section

attribute [-instance] CategoryTheory.catToReflQuiver

/-- The canonical inclusion `IⁿF → F`. -/
def powerSheafι (I : Ideal A) (n : ℕ) (F : ModuleSheaf.{u, v, w} A X) : powerSheaf I n F ⟶ F :=
  ((sheafificationAdjunction _ _).homEquiv _ F).symm
    (Functor.whiskerLeft F.obj (idealMultipleι (I ^ n)))

end

/-- A scalar belonging to `I^n` acts through the inclusion of `I^n F`. -/
private def powerSheaf_scalarFactor (I : Ideal A) (n : ℕ) (F : ModuleSheaf.{u, v, w} A X)
    (a : A) (ha : a ∈ I ^ n) : F ⟶ powerSheaf I n F :=
  (asIso ((sheafificationAdjunction _ _).counit.app F)).inv ≫
    (presheafToSheaf _ _).map
      (Functor.whiskerLeft F.obj (idealMultipleFromScalar (I ^ n) a ha))

private theorem powerSheaf_scalarFactor_comp_ι (I : Ideal A) (n : ℕ)
    (F : ModuleSheaf.{u, v, w} A X) (a : A) (ha : a ∈ I ^ n) :
    powerSheaf_scalarFactor I n F a ha ≫ powerSheafι I n F = a • 𝟙 F := by
  let η := Functor.whiskerLeft F.obj (idealMultipleFromScalar (I ^ n) a ha)
  let ι := Functor.whiskerLeft F.obj (idealMultipleι (I ^ n))
  have hη : η ≫ ι = a • 𝟙 F.obj := by
    dsimp [η, ι]
    rw [← Functor.whiskerLeft_comp, idealMultipleFromScalar_comp_ι]
    ext U x
    rfl
  let e := asIso ((sheafificationAdjunction _ _).counit.app F)
  show e.inv ≫ (presheafToSheaf _ _).map η ≫ powerSheafι I n F = _
  rw [show powerSheafι I n F = (presheafToSheaf _ _).map ι ≫ e.hom by
    dsimp [powerSheafι, ι, e]
    rw [Adjunction.homEquiv_counit]]
  calc
    e.inv ≫ (presheafToSheaf _ _).map η ≫
        ((presheafToSheaf _ _).map ι ≫ e.hom) =
        e.inv ≫ (presheafToSheaf _ _).map (η ≫ ι) ≫ e.hom := by
          rw [Functor.map_comp (presheafToSheaf _ _) η ι]
          simp only [Category.assoc]
    _ = e.inv ≫ (presheafToSheaf _ _).map (a • 𝟙 F.obj) ≫ e.hom := by rw [hη]
    _ = e.inv ≫ (presheafToSheaf _ _).map
        ((sheafToPresheaf _ _).map (a • 𝟙 F)) ≫ e.hom := by
          congr 2
    _ = a • 𝟙 F := by
      have hn := (sheafificationAdjunction _ _).counit.naturality (a • 𝟙 F)
      simpa [e, Functor.comp_map, Functor.map_smul, Functor.map_id,
        Linear.smul_comp, Linear.comp_smul] using congrArg (fun g => e.inv ≫ g) hn

section

attribute [-instance] CategoryTheory.catToReflQuiver

/-- The map on power-ideal subsheaves induced by a sheaf morphism. -/
def powerSheafMap (I : Ideal A) (n : ℕ) {F G : ModuleSheaf.{u, v, w} A X} (f : F ⟶ G) :
    powerSheaf I n F ⟶ powerSheaf I n G :=
  (presheafToSheaf _ _).map (Functor.whiskerRight f.hom (idealMultipleFunctor (I ^ n)))

/-- Multiplication by `a ∈ Iᵏ` on ideal multiples, before sheafification. -/
def idealMultipleSMul (I : Ideal A) (k n : ℕ) (a : ↥(I ^ k)) :
    idealMultipleFunctor.{u, v} (I ^ n) ⟶ idealMultipleFunctor (I ^ (k + n)) where
  app M := ModuleCat.ofHom
    { toFun x := ⟨a.1 • x.1, AssociatedGraded.smul_mem_power I
        (by simpa only [AssociatedGraded.ring_power_eq] using a.2) x.2⟩
      map_add' x y := Subtype.ext (smul_add _ _ _)
      map_smul' b x := Subtype.ext (smul_comm _ _ _) }
  naturality {M N} f := by
    ext x
    exact Subtype.ext (f.hom.map_smul a.1 x.1).symm

/-- Multiplication `IⁿF → Iᵏ⁺ⁿF` by a homogeneous scalar representative. -/
def powerSheafSMul (I : Ideal A) (k n : ℕ) (a : ↥(I ^ k)) (F : ModuleSheaf.{u, v, w} A X) :
    powerSheaf I n F ⟶ powerSheaf I (k + n) F :=
  (presheafToSheaf _ _).map (Functor.whiskerLeft F.obj (idealMultipleSMul I k n a))

end

/-- The global sections functor on sheaves of `A`-modules is additive. -/
local instance sections_additive : ((sheafSections (Opens.grothendieckTopology X)
    (ModuleCat.{v} A)).obj (op ⊤)).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤)).Additive
  infer_instance

/-- Sheaf cohomology as the right derived functors of global sections. -/
def cohomology (p : ℕ) : ModuleSheaf.{u, v, w} A X ⥤ ModuleCat.{v} A :=
  ((sheafSections (Opens.grothendieckTopology X)
    (ModuleCat.{v} A)).obj (op ⊤)).rightDerived p

private theorem cohomology_linear (p : ℕ) :
    Functor.Linear A (cohomology.{u, v, w} (A := A) (X := X) p) := by
  let sections : ModuleSheaf.{u, v, w} A X ⥤ ModuleCat.{v} A :=
    (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{v} A)).obj (op ⊤)
  let : Linear A (ModuleSheaf.{u, v, w} A X) := inferInstance
  let : Linear A ((Opens X)ᵒᵖ ⥤ ModuleCat.{v} A) := inferInstance
  let : Functor.Linear A
      ((evaluation (Opens X)ᵒᵖ (ModuleCat.{v} A)).obj (op ⊤)) := by
    rw [Functor.linear_iff]
    intro F a
    rfl
  let : Functor.Linear A
      (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{v} A)) := by
    rw [Functor.linear_iff]
    intro F a
    rfl
  let : Functor.Linear A sections := by
    show Functor.Linear A
      (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op ⊤))
    infer_instance
  exact Stacks.DerivedLinear.rightDerived_linear (R := A)
    (D := ModuleSheaf.{u, v, w} A X) (E := ModuleCat.{v} A) sections p

/-- The transition map `F_{n+1} → F_n` of the tower is, up to an isomorphism, the cokernel of
the inclusion `I^{n+1}F_{n+1} → F_{n+1}`, for every `n`. -/
def IsQuotientTower (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) : Prop :=
  ∀ n : ℕ, ∃ e : cokernel (powerSheafι I (n + 1) (F.obj (op (n + 1)))) ≅ F.obj (op n),
    cokernel.π (powerSheafι I (n + 1) (F.obj (op (n + 1)))) ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op

/-- The intersection of the images of `Hᵖ(X, IⁿF_m) → Hᵖ(X, IⁿF_n)` over all `m ≥ n`. -/
def stableImage (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ) :
    Submodule A ((cohomology p).obj (powerSheaf I n (F.obj (op n)))) :=
  ⨅ (m : ℕ) (h : n ≤ m), LinearMap.range
    ((cohomology p).map (powerSheafMap I n (F.map (homOfLE h).op))).hom

/-- The direct sum of the stable images. -/
abbrev StableImageSum (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :=
  ⨁ n, stableImage I F p n

/-- Inclusion into the direct sum of the ambient cohomology groups. -/
def stableImageSumι (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :
    StableImageSum I F p →ₗ[A]
      ⨁ n, ((cohomology p).obj (powerSheaf I n (F.obj (op n)))) :=
  DirectSum.toModule A ℕ _ fun n =>
    (DirectSum.lof A ℕ _ n).comp (stableImage I F p n).subtype

/-- An action of `gr_I(A)` on the stable images is the canonical one: for `a ∈ Iᵏ` and `x` in
the stable image of degree `n`, lifted to `y ∈ Hᵖ(X, IⁿF_{k+n})`, the product of the class of
`a` with `x` is the image of `y` under multiplication by `a`,
`Hᵖ(X, IⁿF_{k+n}) → Hᵖ(X, I^{k+n}F_{k+n})`. -/
def IsCanonicalStableImageAction (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (StableImageSum I F p)] : Prop :=
  ∀ (k n : ℕ) (a : ↥(I ^ k)) (x : stableImage I F p n)
    (y : (cohomology p).obj (powerSheaf I n (F.obj (op (k + n))))),
    ((cohomology p).map (powerSheafMap I n
      (F.map (homOfLE (Nat.le_add_left n k)).op))).hom y = x.1 →
    stableImageSumι I F p
      (DirectSum.of (fun i => AssociatedGraded.piece (M := A) I i) k
          (AssociatedGraded.mk I k
            ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩) •
        DirectSum.of (fun i => stableImage I F p i) n x) =
      DirectSum.of (fun i => (cohomology p).obj (powerSheaf I i (F.obj (op i)))) (k + n)
        (((cohomology p).map (powerSheafSMul I k n a (F.obj (op (k + n))))).hom y)

/-- The direct sum of the stable images carries the canonical action of the associated graded
ring `AssociatedGraded.gradedRing I`, and is a Noetherian module for it. -/
def StableImagesHaveGradedACC (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) : Prop :=
  ∃ action : Module (AssociatedGraded.gradedRing I) (StableImageSum I F p),
    letI := action
    IsCanonicalStableImageAction I F p ∧
      IsNoetherian (AssociatedGraded.gradedRing I) (StableImageSum I F p)

/-- The cohomology modules of the tower. -/
abbrev cohomologyModule (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ) :=
  (cohomology p).obj (F.obj (op n))

/-- The transition map `Hᵖ(X, F_{n+1}) → Hᵖ(X, F_n)` on cohomology. -/
def cohomologyTransition (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ) :
    cohomologyModule F p (n + 1) →ₗ[A] cohomologyModule F p n :=
  ((cohomology p).map (F.map (homOfLE (Nat.le_succ n)).op)).hom

private theorem quotientTower_transition_comp_powerSheafι_eq_zero
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n : ℕ) :
    powerSheafι I (n + 1) (F.obj (op (n + 1))) ≫
      F.map (homOfLE (Nat.le_succ n)).op = 0 := by
  obtain ⟨e, he⟩ := hquotient n
  calc
    _ = powerSheafι I (n + 1) (F.obj (op (n + 1))) ≫
        (cokernel.π (powerSheafι I (n + 1) (F.obj (op (n + 1)))) ≫ e.hom) := by
      rw [he]
    _ = (powerSheafι I (n + 1) (F.obj (op (n + 1))) ≫
        cokernel.π (powerSheafι I (n + 1) (F.obj (op (n + 1))))) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = 0 := by rw [cokernel.condition]; simp

/-- A morphism `f : F ⟶ G` vanishes on `IⁿF` if and only if `a • f = 0` for every `a ∈ Iⁿ`. -/
theorem powerSheafι_comp_eq_zero_iff
    (I : Ideal A) (n : ℕ) {F G : ModuleSheaf.{u, v, w} A X} (f : F ⟶ G) :
    powerSheafι I n F ≫ f = 0 ↔ ∀ a ∈ I ^ n, a • f = 0 := by
  constructor
  · intro hf a ha
    have h := congrArg (fun g => powerSheaf_scalarFactor I n F a ha ≫ g) hf
    simpa only [← Category.assoc, powerSheaf_scalarFactor_comp_ι,
      Linear.smul_comp, Category.id_comp, comp_zero] using h
  · intro hf
    apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [powerSheafι, Equiv.apply_symm_apply]
    ext U x
    show (f.hom.app U).hom x.1 = 0
    have hh : (I ^ n • (⊤ : Submodule A (F.obj.obj U))) ≤
        LinearMap.ker (f.hom.app U).hom := by
      apply Submodule.smul_le.mpr
      intro a ha y hy
      have h := congrArg (fun g : F ⟶ G => (g.hom.app U).hom y) (hf a ha)
      show (f.hom.app U).hom (a • y) = 0
      rw [map_smul]
      exact h
    exact hh x.2

/-- The inclusion `IⁿF → F` is a monomorphism. -/
theorem powerSheafι_mono (I : Ideal A) (n : ℕ)
    (F : ModuleSheaf.{u, v, w} A X) : Mono (powerSheafι I n F) := by
  let i := Functor.whiskerLeft F.obj (idealMultipleι (I ^ n))
  have : ∀ U, Mono (i.app U) := fun U =>
    (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  have : Mono i := NatTrans.mono_of_mono_app i
  dsimp only [powerSheafι]
  rw [Adjunction.homEquiv_counit]
  show Mono ((presheafToSheaf _ _).map i ≫ _)
  infer_instance

/-- The inclusions `IⁿF → F` are natural in `F`. -/
theorem powerSheafMap_ι (I : Ideal A) (n : ℕ)
    {F G : ModuleSheaf.{u, v, w} A X} (f : F ⟶ G) :
    powerSheafMap I n f ≫ powerSheafι I n G = powerSheafι I n F ≫ f := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  rw [powerSheafMap, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [powerSheafι, Equiv.apply_symm_apply]
  ext U x
  rfl

/-- Multiplication `IⁿF → Iᵏ⁺ⁿF` by `a ∈ Iᵏ`, followed by the inclusion into `F`, is `a` times
the inclusion `IⁿF → F`. -/
theorem powerSheafSMul_ι (I : Ideal A) (k n : ℕ) (a : ↥(I ^ k))
    (F : ModuleSheaf.{u, v, w} A X) :
    powerSheafSMul I k n a F ≫ powerSheafι I (k + n) F = a.1 • powerSheafι I n F := by
  rw [show a.1 • powerSheafι I n F = powerSheafι I n F ≫ (a.1 • 𝟙 F) by simp]
  apply ((sheafificationAdjunction _ _).homEquiv _ F).injective
  rw [powerSheafSMul, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [powerSheafι, Equiv.apply_symm_apply]
  ext U x
  rfl

private theorem quotientTower_transition_epi
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n m : ℕ) (h : n ≤ m) :
    Epi (F.map (homOfLE h).op) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (inferInstance : Epi (𝟙 (F.obj (op n))))
  | succ m h ih =>
    have : Epi (F.map (homOfLE (Nat.le_succ m)).op) := by
      obtain ⟨e, he⟩ := hquotient m
      rw [← he]
      infer_instance
    have : Epi (F.map (homOfLE h).op) := ih
    rw [← map_homOfLE_comp F (Nat.le_succ m) h]
    infer_instance

private theorem quotientTower_transition_annihilates
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n m : ℕ) (h : n + 1 ≤ m) :
    powerSheafι I (n + 1) (F.obj (op m)) ≫ F.map (homOfLE (by omega : n ≤ m)).op = 0 := by
  apply (powerSheafι_comp_eq_zero_iff I (n + 1) _).mpr
  intro a ha
  have hz := (powerSheafι_comp_eq_zero_iff I (n + 1) _).mp
    (quotientTower_transition_comp_powerSheafι_eq_zero I F hquotient n) a ha
  rw [← map_homOfLE_comp F h (Nat.le_succ n), ← Linear.comp_smul, hz, comp_zero]

private theorem quotientTower_transition_desc
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n m : ℕ) (h : n + 1 ≤ m)
    {G : ModuleSheaf.{u, v, w} A X} (f : F.obj (op m) ⟶ G)
    (hf : powerSheafι I (n + 1) (F.obj (op m)) ≫ f = 0) :
    ∃ g : F.obj (op n) ⟶ G, F.map (homOfLE (by omega : n ≤ m)).op ≫ g = f := by
  induction m, h using Nat.le_induction with
  | base =>
    obtain ⟨e, he⟩ := hquotient n
    refine ⟨e.inv ≫ cokernel.desc _ f hf, ?_⟩
    rw [← he]
    simp
  | succ m h ih =>
    have hkill := (powerSheafι_comp_eq_zero_iff I (n + 1) f).mp hf
    have hm : powerSheafι I (m + 1) (F.obj (op (m + 1))) ≫ f = 0 := by
      apply (powerSheafι_comp_eq_zero_iff I (m + 1) f).mpr
      intro a ha
      exact hkill a (Ideal.pow_le_pow_right (by omega) ha)
    obtain ⟨e, he⟩ := hquotient m
    let g := e.inv ≫ cokernel.desc _ f hm
    have hg : F.map (homOfLE (Nat.le_succ m)).op ≫ g = f := by
      rw [← he]
      simp [g]
    have hgkill : powerSheafι I (n + 1) (F.obj (op m)) ≫ g = 0 := by
      apply (powerSheafι_comp_eq_zero_iff I (n + 1) g).mpr
      intro a ha
      have : Epi (F.map (homOfLE (Nat.le_succ m)).op) :=
        quotientTower_transition_epi I F hquotient m (m + 1) (Nat.le_succ m)
      apply (cancel_epi (F.map (homOfLE (Nat.le_succ m)).op)).mp
      rw [Linear.comp_smul, hg, hkill a ha, comp_zero]
    obtain ⟨g', hg'⟩ := ih g hgkill
    refine ⟨g', ?_⟩
    rw [← map_homOfLE_comp F (Nat.le_succ m) (by omega : n ≤ m), Category.assoc, hg', hg]

private theorem quotientTower_transition_shortExact
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n m : ℕ) (h : n + 1 ≤ m) :
    (ShortComplex.mk (powerSheafι I (n + 1) (F.obj (op m)))
      (F.map (homOfLE (by omega : n ≤ m)).op)
      (quotientTower_transition_annihilates I F hquotient n m h)).ShortExact := by
  let S := ShortComplex.mk _ _ (quotientTower_transition_annihilates I F hquotient n m h)
  have : Mono S.f := powerSheafι_mono I (n + 1) _
  have : Epi S.g := quotientTower_transition_epi I F hquotient n m (by omega)
  refine ⟨S.exact_of_g_is_cokernel ?_⟩
  exact CokernelCofork.IsColimit.ofπ _ _
    (fun f hf => (quotientTower_transition_desc I F hquotient n m h f hf).choose)
    (fun f hf => (quotientTower_transition_desc I F hquotient n m h f hf).choose_spec)
    fun f hf g hg => (cancel_epi S.g).mp
      (hg.trans (quotientTower_transition_desc I F hquotient n m h f hf).choose_spec.symm)

private theorem quotientTower_annihilated
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) :
    a • 𝟙 (F.obj (op n)) = 0 := by
  have : Epi (F.map (homOfLE (Nat.le_succ n)).op) :=
    quotientTower_transition_epi I F hquotient n (n + 1) (Nat.le_succ n)
  apply (cancel_epi (F.map (homOfLE (Nat.le_succ n)).op)).mp
  simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using
    (powerSheafι_comp_eq_zero_iff I (n + 1) _).mp
      (quotientTower_transition_comp_powerSheafι_eq_zero I F hquotient n) a ha

private theorem quotientTower_scalar_desc
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X)
    (hquotient : IsQuotientTower I F) (k n : ℕ) (a : ↥(I ^ k)) :
    ∃ g : F.obj (op n) ⟶ F.obj (op (k + n)),
      F.map (homOfLE (Nat.le_add_left n k)).op ≫ g = a.1 • 𝟙 _ := by
  by_cases hk : k = 0
  · subst k
    let e : op n ⟶ op (0 + n) := eqToHom (congrArg op (Nat.zero_add n).symm)
    refine ⟨F.map e ≫ (a.1 • 𝟙 _), ?_⟩
    rw [← Category.assoc, ← F.map_comp]
    have he : (homOfLE (Nat.le_add_left n 0)).op ≫ e = 𝟙 (op (0 + n)) :=
      Subsingleton.elim _ _
    rw [he, F.map_id, Category.id_comp]
  · apply quotientTower_transition_desc I F hquotient n (k + n) (by omega)
    apply (powerSheafι_comp_eq_zero_iff I (n + 1) _).mpr
    intro b hb
    rw [smul_smul]
    apply quotientTower_annihilated I F hquotient
    have hh := Ideal.mul_mem_mul hb a.2
    rw [← pow_add] at hh
    convert hh using 1
    congr 1
    omega

omit [Small.{v} A] [UnivLE.{max w v, v}] in
private theorem cohomologyTowerLimit_map_coord
    (H : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (x : CohomologyTowerLimit (fun n => H.obj (op n))
      (fun n => (H.map (homOfLE (Nat.le_succ n)).op).hom))
    (n m : ℕ) (h : n ≤ m) : (H.map (homOfLE h).op).hom (x.1 m) = x.1 n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [← map_homOfLE_comp H (Nat.le_succ m) h, ModuleCat.hom_comp, LinearMap.comp_apply, x.2 m, ih]

private theorem cohomologyTowerLimit_smul_coord
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F) (k n : ℕ) (a : ↥(I ^ k)) :
    ∃ g : cohomologyModule F p n →ₗ[A] cohomologyModule F p (k + n),
      (∀ z, g (((cohomology p).map (F.map (homOfLE (Nat.le_add_left n k)).op)).hom z) = a.1 • z) ∧
      ∀ x : CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p),
        g (x.1 n) = a.1 • x.1 (k + n) := by
  obtain ⟨g, hg⟩ := quotientTower_scalar_desc I F hquotient k n a
  let H := cohomology.{u, v, w} (A := A) (X := X) p
  have : Functor.Linear A H := cohomology_linear p
  have hz (z : cohomologyModule F p (k + n)) :
      (H.map g).hom ((H.map (F.map (homOfLE (Nat.le_add_left n k)).op)).hom z) = a.1 • z := by
    show (H.map (F.map (homOfLE (Nat.le_add_left n k)).op) ≫ H.map g).hom z = _
    rw [← H.map_comp, hg, Functor.map_smul, H.map_id]
    rfl
  refine ⟨(H.map g).hom, hz, fun x => ?_⟩
  have hx := cohomologyTowerLimit_map_coord (F ⋙ H) x n (k + n) (Nat.le_add_left n k)
  change (H.map (F.map (homOfLE (Nat.le_add_left n k)).op)).hom (x.1 (k + n)) = x.1 n at hx
  rw [← hx]
  exact hz _

private theorem cohomologyTransition_idealPower_le_ker
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p n : ℕ)
    (hquotient : IsQuotientTower I F) :
    I ^ (n + 1) • (⊤ : Submodule A (cohomologyModule F p (n + 1))) ≤
      LinearMap.ker (cohomologyTransition F p n) := by
  refine Submodule.smul_le.mpr fun a ha x _ => ?_
  let H := cohomology.{u, v, w} (A := A) (X := X) p
  let ι := powerSheafι I (n + 1) (F.obj (op (n + 1)))
  let g := powerSheaf_scalarFactor I (n + 1) (F.obj (op (n + 1))) a ha
  let : Functor.Linear A H := cohomology_linear p
  have hfactor : H.map g ≫ H.map ι = a • 𝟙 _ := by
    rw [← H.map_comp, powerSheaf_scalarFactor_comp_ι, Functor.map_smul, H.map_id]
  have hzero : H.map ι ≫ H.map (F.map (homOfLE (Nat.le_succ n)).op) = 0 := by
    rw [← H.map_comp, quotientTower_transition_comp_powerSheafι_eq_zero I F hquotient n]
    simpa using H.map_smul (R := A) (0 : A) (0 : powerSheaf I (n + 1) (F.obj (op (n + 1))) ⟶ _)
  show (H.map (F.map (homOfLE (Nat.le_succ n)).op)).hom (a • x) = 0
  rw [← show (H.map ι).hom ((H.map g).hom x) = a • x by
    simpa using congrArg (fun q => q.hom x) hfactor]
  simpa using congrArg (fun q => q.hom ((H.map g).hom x)) hzero

end SheafConstructions

private theorem iInf_induced_eq_adicModuleTopology
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {N : ℕ → Type w} [∀ n, AddCommGroup (N n)]
    [∀ n, Module R (N n)]
    (f : ∀ n, M →ₗ[R] N n)
    (hmono : ∀ i j, i ≤ j → (f j).ker ≤ (f i).ker)
    (hpow : ∀ n, ∃ k, (I ^ k • (⊤ : Submodule R M) : Submodule R M) ≤ (f n).ker)
    (hker : ∀ k, ∃ n, (f n).ker ≤ I ^ k • (⊤ : Submodule R M)) :
    (⨅ n, TopologicalSpace.induced (fun x : M => f n x) ⊥) =
      I.adicModuleTopology M := by
  classical
  let T₁ : TopologicalSpace M :=
    ⨅ n, TopologicalSpace.induced (fun x : M => f n x) ⊥
  let T₂ : TopologicalSpace M := I.adicModuleTopology M
  have hker_nhds (n : ℕ) (y : N n) :
      @nhds (N n) (⊥ : TopologicalSpace (N n)) y = pure y := by
    let : TopologicalSpace (N n) := ⊥
    let : DiscreteTopology (N n) := ⟨rfl⟩
    exact congrFun (nhds_discrete (N n)) y
  have h₁basis (x : M) : (@nhds M T₁ x).HasBasis (fun n : ℕ => True)
      (fun n => (fun y : M => x + y) '' ((f n).ker : Set M)) := by
    have hcoset (n : ℕ) :
        ((fun y : M => f n y) ⁻¹' {f n x}) =
          (fun y : M => x + y) '' ((f n).ker : Set M) := by
      ext y
      constructor
      · intro hy
        change f n y = f n x at hy
        refine ⟨y - x, ?_, ?_⟩
        · show f n (y - x) = 0
          simp [map_sub, hy]
        · simp
      · rintro ⟨z, hz, rfl⟩
        simp [LinearMap.mem_ker.mp hz]
    have hfilter : @nhds M T₁ x = ⨅ n, Filter.principal
        ((fun y : M => x + y) '' ((f n).ker : Set M)) := by
      show @nhds M (⨅ n, TopologicalSpace.induced (fun y : M => f n y) ⊥) x = _
      rw [nhds_iInf]
      congr 1
      funext n
      let : TopologicalSpace (N n) := ⊥
      rw [nhds_induced, hker_nhds n (f n x), Filter.comap_pure, hcoset]
    rw [hfilter]
    exact Filter.hasBasis_iInf_principal fun i j => ⟨max i j,
      Set.image_mono (hmono i _ (le_max_left _ _)), Set.image_mono (hmono j _ (le_max_right _ _))⟩
  let : TopologicalSpace R := I.adicTopology
  let B : ModuleFilterBasis R M := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  have h₂basis (x : M) : (@nhds M T₂ x).HasBasis (fun n : ℕ => True)
      (fun n => (fun y : M => x + y) ''
        ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) := by
    have hb := B.toAddGroupFilterBasis.nhds_hasBasis x
    show (@nhds M (I.adicModuleTopology M) x).HasBasis _ _
    refine hb.to_hasBasis ?_ ?_
    · intro U hU
      change (∃ n, U = ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M)) at hU
      rcases hU with ⟨n, rfl⟩
      exact ⟨n, trivial, Set.Subset.rfl⟩
    · intro n _
      refine ⟨((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M), ?_, Set.Subset.rfl⟩
      show ∃ m, ((I ^ n • (⊤ : Submodule R M) : Submodule R M) : Set M) =
        ((I ^ m • (⊤ : Submodule R M) : Submodule R M) : Set M)
      exact ⟨n, rfl⟩
  refine TopologicalSpace.ext_nhds fun x =>
    (h₁basis x).ext (h₂basis x) (fun n _ => ?_) fun k _ => ?_
  · obtain ⟨k, hk⟩ := hpow n
    exact ⟨k, trivial, Set.image_mono hk⟩
  · obtain ⟨n, hn⟩ := hker k
    exact ⟨n, trivial, Set.image_mono hn⟩

private theorem cohomologyTowerLimit_proj_ker_antitone
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (f : ∀ n, C (n + 1) →ₗ[R] C n) (i j : ℕ) (hij : i ≤ j) :
    LinearMap.ker (CohomologyTowerLimit.proj C f j) ≤
      LinearMap.ker (CohomologyTowerLimit.proj C f i) := by
  intro x hx
  change x.1 j = 0 at hx
  show x.1 i = 0
  induction hij with
  | refl => exact hx
  | step _ ih => exact ih (by rw [← x.2, hx, map_zero])

private theorem cohomologyTowerLimit_ideal_power_le_proj_ker
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (I : Ideal R) (f : ∀ n, C (n + 1) →ₗ[R] C n)
    (hkill : ∀ n, (I ^ (n + 1) • (⊤ : Submodule R (C (n + 1))) : Submodule R (C (n + 1))) ≤
      LinearMap.ker (f n)) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (CohomologyTowerLimit C f)) ≤
      LinearMap.ker (CohomologyTowerLimit.proj C f n) := by
  refine Submodule.smul_le.mpr fun a ha x _ => ?_
  show a • x.1 n = 0
  rw [show x.1 n = f n (x.1 (n + 1)) from (x.2 n).symm, ← map_smul]
  apply LinearMap.mem_ker.mp
  exact (Submodule.smul_le.mp (hkill n) a ha (x.1 (n + 1)) (by simp))

private theorem cohomologyTowerLimit_cohomology_ideal_power_le_proj_ker
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A
      (CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p))) ≤
      LinearMap.ker (CohomologyTowerLimit.proj (fun j => cohomologyModule F p j)
        (cohomologyTransition F p) n) := by
  apply cohomologyTowerLimit_ideal_power_le_proj_ker
    (R := A) (C := fun j => cohomologyModule F p j) I (cohomologyTransition F p)
  exact fun j => cohomologyTransition_idealPower_le_ker I F p j hquotient

private theorem cohomologyTowerLimit_limitTopology_eq_iInf_induced_proj
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (f : ∀ n, C (n + 1) →ₗ[R] C n) :
    CohomologyTowerLimit.limitTopology C f =
      ⨅ n, TopologicalSpace.induced (fun x => CohomologyTowerLimit.proj C f n x) ⊥ := by
  simp [CohomologyTowerLimit.limitTopology, Pi.topologicalSpace,
    CohomologyTowerLimit.proj, induced_iInf, induced_compose, Function.comp_def]

private theorem ideal_smul_top_le_linearMap_ker
    {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (J : Ideal R) (f : M →ₗ[R] N)
    (h : ∀ a ∈ J, ∀ x, f (a • x) = 0) :
    J • (⊤ : Submodule R M) ≤ LinearMap.ker f :=
  Submodule.smul_le.mpr fun a ha x _ => h a ha x

/-- A series of compatible sequences whose terms vanish in successively more
coordinates has a compatible, coordinatewise finite sum. -/
private theorem cohomologyTowerLimit_exists_sum
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (f : ∀ n, C (n + 1) →ₗ[R] C n)
    (a : ℕ → CohomologyTowerLimit C f)
    (ha : ∀ i, a i ∈ LinearMap.ker (CohomologyTowerLimit.proj C f i)) :
    ∃ s : CohomologyTowerLimit C f, ∀ j,
      s.1 j = ∑ i ∈ Finset.range (j + 1), (a i).1 j := by
  let s : ∀ j, C j := fun j => ∑ i ∈ Finset.range (j + 1), (a i).1 j
  refine ⟨⟨s, ?_⟩, fun _ => rfl⟩
  intro j
  show f j (∑ i ∈ Finset.range (j + 1 + 1), (a i).1 (j + 1)) =
    ∑ i ∈ Finset.range (j + 1), (a i).1 j
  rw [map_sum]
  simp only [(a _).2 j]
  rw [Finset.sum_range_succ]
  have hz := cohomologyTowerLimit_proj_ker_antitone f j (j + 1)
    (Nat.le_succ j) (ha (j + 1))
  change (a (j + 1)).1 j = 0 at hz
  rw [hz, add_zero]

/-- If every element vanishing in coordinate `n + 1` is approximated modulo coordinate `n + 2`
by a combination `∑ aᵢ yᵢ` with `yᵢ` vanishing in coordinate `n`, then every such element is
exactly such a combination. -/
private theorem cohomologyTowerLimit_exists_smul_sum
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (f : ∀ n, C (n + 1) →ₗ[R] C n)
    {ι : Type w} [Fintype ι] (a : ι → R) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : CohomologyTowerLimit C f,
      x ∈ LinearMap.ker (CohomologyTowerLimit.proj C f (n + 1)) →
      ∃ y : ι → CohomologyTowerLimit C f,
        (∀ i, y i ∈ LinearMap.ker (CohomologyTowerLimit.proj C f n)) ∧
        x - ∑ i, a i • y i ∈
          LinearMap.ker (CohomologyTowerLimit.proj C f (n + 2)))
    (n : ℕ) (hn : c ≤ n) (x : CohomologyTowerLimit C f)
    (hx : x ∈ LinearMap.ker (CohomologyTowerLimit.proj C f (n + 1))) :
    ∃ y : ι → CohomologyTowerLimit C f,
      (∀ i, y i ∈ LinearMap.ker (CohomologyTowerLimit.proj C f n)) ∧
      x = ∑ i, a i • y i := by
  classical
  let K := fun j => LinearMap.ker (CohomologyTowerLimit.proj C f j)
  let chooseTerms : ∀ j, K (n + j + 1) → (ι → CohomologyTowerLimit C f) :=
    fun j z => (happrox (n + j) (hn.trans (Nat.le_add_right n j)) z.1 z.2).choose
  have hterms (j : ℕ) (z : K (n + j + 1)) :
      (∀ i, chooseTerms j z i ∈ K (n + j)) ∧
      z.1 - ∑ i, a i • chooseTerms j z i ∈ K (n + j + 2) :=
    (happrox (n + j) (hn.trans (Nat.le_add_right n j)) z.1 z.2).choose_spec
  let residual : ∀ j, K (n + j + 1) := fun j => Nat.rec
    (motive := fun j => K (n + j + 1)) ⟨x, hx⟩
    (fun j z => ⟨z.1 - ∑ i, a i • chooseTerms j z i, hterms j z |>.2⟩) j
  let b : ℕ → ι → CohomologyTowerLimit C f := fun j => chooseTerms j (residual j)
  have hb (j : ℕ) (i : ι) : b j i ∈ K (n + j) := (hterms j (residual j)).1 i
  have hres (j : ℕ) :
      (residual j).1 = x - ∑ k ∈ Finset.range j, ∑ i, a i • b k i := by
    induction j with
    | zero => simp [residual]
    | succ j ih =>
      show (residual j).1 - ∑ i, a i • b j i = _
      rw [ih, Finset.sum_range_succ, sub_sub]
  have hs (i : ι) := cohomologyTowerLimit_exists_sum f (fun j => b j i)
    (fun j => cohomologyTowerLimit_proj_ker_antitone f j (n + j)
      (Nat.le_add_left j n) (hb j i))
  choose s hs using hs
  refine ⟨s, ?_, ?_⟩
  · intro i
    show (s i).1 n = 0
    rw [hs]
    apply Finset.sum_eq_zero
    intro j hj
    exact cohomologyTowerLimit_proj_ker_antitone f n (n + j)
      (Nat.le_add_right n j) (hb j i)
  · apply Subtype.ext
    funext j
    have hz := cohomologyTowerLimit_proj_ker_antitone f j (n + (j + 1) + 1)
      (by omega) (residual (j + 1)).2
    change (residual (j + 1)).1.1 j = 0 at hz
    rw [hres] at hz
    have hz' : x.1 j = ∑ k ∈ Finset.range (j + 1), ∑ i, a i • (b k i).1 j := by
      simpa only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
        Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, sub_eq_zero] using hz
    show x.1 j = (∑ i, a i • s i).1 j
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    simp_rw [hs, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact hz'

private theorem cohomologyTowerLimit_ker_le_ideal_power_of_approx
    {R : Type u} [CommRing R] {C : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
    (f : ∀ n, C (n + 1) →ₗ[R] C n) (I : Ideal R)
    {ι : Type w} [Fintype ι] (a : ι → R) (ha : ∀ i, a i ∈ I) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : CohomologyTowerLimit C f,
      x ∈ LinearMap.ker (CohomologyTowerLimit.proj C f (n + 1)) →
      ∃ y : ι → CohomologyTowerLimit C f,
        (∀ i, y i ∈ LinearMap.ker (CohomologyTowerLimit.proj C f n)) ∧
        x - ∑ i, a i • y i ∈
          LinearMap.ker (CohomologyTowerLimit.proj C f (n + 2)))
    (k : ℕ) :
    LinearMap.ker (CohomologyTowerLimit.proj C f (c + k)) ≤
      I ^ k • (⊤ : Submodule R (CohomologyTowerLimit C f)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := cohomologyTowerLimit_exists_smul_sum f a c happrox
      (c + k) (Nat.le_add_right c k) x hx
    rw [pow_succ', ← Ideal.smul_eq_mul, Submodule.smul_assoc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (ha i) (ih (hy i))

/-- If the span of `⋃ n, s n` is finitely generated, it is already the span of `⋃ n ≤ c, s n`
for some `c`. -/
private theorem exists_span_degrees_le
    {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
    (s : ℕ → Set M) (hfg : (Submodule.span R (⋃ n, s n)).FG) :
    ∃ c : ℕ, Submodule.span R (⋃ n, s n) =
      Submodule.span R (⋃ n ≤ c, s n) := by
  let P : ℕ →o Submodule R M :=
    { toFun := fun c => Submodule.span R (⋃ n ≤ c, s n)
      monotone' := fun c d hcd => Submodule.span_mono <| by
        simp only [Set.iUnion_subset_iff]
        intro n hn
        exact Set.subset_iUnion_of_subset n
          (Set.subset_iUnion_of_subset (hn.trans hcd) Set.Subset.rfl) }
  apply hfg.stabilizes_of_iSup_eq P
  apply le_antisymm
  · refine iSup_le fun c => Submodule.span_mono ?_
    simp only [Set.iUnion_subset_iff]
    exact fun n _ => Set.subset_iUnion s n
  · refine Submodule.span_le.mpr ?_
    simp only [Set.iUnion_subset_iff]
    exact fun n x hx => le_iSup P n <| Submodule.subset_span <| Set.mem_iUnion.mpr ⟨n,
      Set.mem_iUnion.mpr ⟨le_rfl, hx⟩⟩

private theorem stableImageSumι_eq_lmap
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :
    stableImageSumι I F p = DirectSum.lmap (fun n => (stableImage I F p n).subtype) := by
  ext n x
  simp [stableImageSumι]

/-- The `n`-th component of `stableImageSumι I F p x` is the underlying element of `x n`. -/
theorem stableImageSumι_apply
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (x : StableImageSum I F p) (n : ℕ) :
    (stableImageSumι I F p x) n = (x n).1 := by
  rw [stableImageSumι_eq_lmap]
  rfl

/-- The inclusion `stableImageSumι I F p` is injective. -/
theorem stableImageSumι_injective
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ) :
    Function.Injective (stableImageSumι I F p) := by
  rw [stableImageSumι_eq_lmap]
  exact (DirectSum.lmap_injective _).mpr fun _ => Subtype.val_injective

private theorem canonicalStableImageAction_is_graded
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    [Module (AssociatedGraded.gradedRing I) (StableImageSum I F p)]
    (hcanonical : IsCanonicalStableImageAction I F p)
    (k n : ℕ) (a : ↥(I ^ k)) (x : stableImage I F p n) :
    ∃ y : stableImage I F p (k + n),
      AssociatedGraded.classOfPow I k a • DirectSum.of (fun j => stableImage I F p j) n x =
        DirectSum.of (fun j => stableImage I F p j) (k + n) y := by
  have hx := (Submodule.mem_iInf _).mp x.2 (k + n)
  obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp hx (Nat.le_add_left n k)
  let z := AssociatedGraded.classOfPow I k a • DirectSum.of (fun j => stableImage I F p j) n x
  have hz := hcanonical k n a x y hy
  change stableImageSumι I F p z = _ at hz
  refine ⟨z (k + n), ?_⟩
  apply stableImageSumι_injective I F p
  have hv := congrArg (fun t => t (k + n)) hz
  rw [stableImageSumι_apply] at hv
  simp only [DirectSum.of_eq_same] at hv
  rw [hz, stableImageSumι_eq_lmap]
  show _ = DirectSum.lmap (fun j => (stableImage I F p j).subtype)
    (DirectSum.lof A ℕ _ (k + n) (z (k + n)))
  rw [DirectSum.lmap_lof]
  show _ = DirectSum.of (fun j =>
    ((cohomology p).obj (powerSheaf I j (F.obj (op j))))) (k + n) ((z (k + n)).1)
  rw [hv]

/-- In a commutative diagram of linear maps with exact rows, an element `s` of the lower row
whose image comes from the upper row lies in the range of the vertical map `b`. -/
private theorem mem_range_of_exact_commutative_diagram
    {R K B B' C C' D : Type*} [CommRing R]
    [AddCommGroup K] [Module R K] [AddCommGroup B] [Module R B]
    [AddCommGroup B'] [Module R B'] [AddCommGroup C] [Module R C]
    [AddCommGroup C'] [Module R C'] [AddCommGroup D] [Module R D]
    (f : K →ₗ[R] B) (f' : K →ₗ[R] B') (b : B' →ₗ[R] B)
    (g : B →ₗ[R] C) (g' : B' →ₗ[R] C') (c : C' →ₗ[R] C) (h : C' →ₗ[R] D)
    (hex : LinearMap.range f = LinearMap.ker g)
    (hex' : LinearMap.range g' = LinearMap.ker h)
    (hf : b.comp f' = f) (hg : g.comp b = c.comp g')
    (s : B) (t : C') (ht : h t = 0) (hs : c t = g s) : s ∈ LinearMap.range b := by
  obtain ⟨z, hz⟩ : t ∈ LinearMap.range g' := by
    rw [hex']
    exact ht
  have hsz : s - b z ∈ LinearMap.range f := by
    rw [hex]
    show g (s - b z) = 0
    rw [map_sub, ← LinearMap.comp_apply, hg, LinearMap.comp_apply, hz, hs, sub_self]
  obtain ⟨a, ha⟩ := hsz
  refine ⟨f' a + z, ?_⟩
  rw [map_add, ← LinearMap.comp_apply, hf, ha, sub_add_cancel]

private theorem stableImageSum_moduleFinite
    {X : Type w} [TopologicalSpace X] [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hACC : StableImagesHaveGradedACC.{u, v, w} I F p) :
    ∃ action : Module (AssociatedGraded.gradedRing I) (StableImageSum I F p),
      letI := action
      Module.Finite (AssociatedGraded.gradedRing I) (StableImageSum I F p) := by
  obtain ⟨action, _, hnoetherian⟩ := hACC
  exact ⟨action, inferInstance⟩

section DerivedDelta

open CategoryTheory.Pretriangulated CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

section DerivedComparison

attribute [local instance] HasDerivedCategory.standard

variable (C : Type*) [Category* C] [Abelian C] [EnoughInjectives C]
private def injectiveResolutionsPlus : C ⥤ HomotopyCategory.Plus C :=
  ObjectProperty.lift _
    (injectiveResolutions C ⋙ ComplexShape.embeddingUpNat.extendHomotopyFunctor C)
    (by
      intro X
      apply (HomotopyCategory.plus_quotient_obj_iff _).mpr
      exact ⟨0, inferInstanceAs ((injectiveResolution X).cochainComplex.IsStrictlyGE 0)⟩)

/-- The comparison isomorphism in `DerivedCategory C` between the single complex on `X`
and the image of the chosen injective resolution of `X`. -/
private def injectiveResolutionIso (X : C) :
    (DerivedCategory.singleFunctor C 0).obj X ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (injectiveResolution X).cochainComplex) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
    asIso (DerivedCategory.Q.map (injectiveResolution X).ι') ≪≫
    ((DerivedCategory.quotientCompQhIso C).app (injectiveResolution X).cochainComplex).symm

private lemma injectiveResolutionIso_naturality {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.singleFunctor C 0).map f ≫ (injectiveResolutionIso C Y).hom =
      (injectiveResolutionIso C X).hom ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (DerivedIndexing.descHom f).hom') := by
  dsimp only [injectiveResolutionIso]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [NatTrans.naturality_assoc]
  congr 1
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← InjectiveResolution.Hom.ι'_comp_hom' (DerivedIndexing.descHom f),
    Functor.map_comp_assoc, DerivedCategory.quotientCompQhIso_inv_naturality]

/-- The comparison isomorphism, after composing with the fully faithful `Plus.ι`. -/
private def singleCompιIsoInjectiveResolutions :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ DerivedCategory.Plus.ι ≅
      (injectiveResolutionsPlus C ⋙ DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι :=
  NatIso.ofComponents (fun X => injectiveResolutionIso C X)
    (fun {_ _} f => injectiveResolutionIso_naturality C f)

private def singleIsoInjectiveResolutionsPlus :
    DerivedCategory.Plus.singleFunctor C 0 ≅
      injectiveResolutionsPlus C ⋙ DerivedCategory.Plus.Qh :=
  fullyFaithfulCancelRight DerivedCategory.Plus.ι (singleCompιIsoInjectiveResolutions C)

variable {C}
variable {D : Type*} [Category* D] [Abelian D]

private def extendHomologyIso (p : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor D ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) (p : ℤ) ≅
      HomologicalComplex.homologyFunctor D (.up ℕ) p :=
  NatIso.ofComponents (fun K => K.extendHomologyIso ComplexShape.embeddingUpNat rfl)
    (fun f => HomologicalComplex.extendHomologyIso_hom_naturality f _ rfl)

private def extendedHomotopyHomologyIso (F : C ⥤ D) [F.Additive] (p : ℕ) :
    ComplexShape.embeddingUpNat.extendHomotopyFunctor C ⋙
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        DerivedCategory.homologyFunctor D (p : ℤ) ≅
      F.mapHomotopyCategory (.up ℕ) ⋙ HomotopyCategory.homologyFunctor D (.up ℕ) p := by
  apply CategoryTheory.Quotient.natIsoLift
  let E := ComplexShape.embeddingUpNat.extendFunctor C
  let M := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor D (p : ℤ)
  exact isoWhiskerRight (isoWhiskerLeft E (F.mapHomotopyCategoryFactors (.up ℤ)))
      (DerivedCategory.Qh ⋙ H) ≪≫
    isoWhiskerLeft E (Functor.associator M _ _ ≪≫
      isoWhiskerLeft M (isoWhiskerRight (DerivedCategory.quotientCompQhIso D) H ≪≫
        DerivedCategory.homologyFunctorFactors D (p : ℤ))) ≪≫
    (Functor.associator E M _).symm ≪≫
    isoWhiskerRight (Stacks.DerivedIndexing.mapExtendNatIsoSymm F ComplexShape.embeddingUpNat) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex (.up ℕ)) (extendHomologyIso p) ≪≫
    (isoWhiskerLeft (F.mapHomologicalComplex (.up ℕ))
      (HomotopyCategory.homologyFunctorFactors D (.up ℕ) p)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℕ)) _).symm

private def rightDerivedPlusIso (F : C ⥤ D) [F.Additive] (p : ℕ) :
    F.rightDerivedPlus (p : ℤ) ≅ F.rightDerived p := by
  let R := injectiveResolutionsPlus C
  let H := DerivedCategory.Plus.homologyFunctor D (p : ℤ)
  let η := whiskerLeft R F.rightDerivedFunctorPlusUnith
  have (X : C) : IsIso (η.app X) := by
    have : ∀ n : ℤ, Injective (((R.obj X).obj).as.X n) := fun n =>
      inferInstanceAs (Injective ((injectiveResolution X).cochainComplex.X n))
    exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app (R.obj X)))
  have : IsIso η := NatIso.isIso_of_isIso_app η
  change DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ H ≅ _
  refine isoWhiskerRight (singleIsoInjectiveResolutionsPlus C)
      (F.rightDerivedFunctorPlus ⋙ H) ≪≫ ?_
  refine Functor.associator R DerivedCategory.Plus.Qh (F.rightDerivedFunctorPlus ⋙ H) ≪≫
    isoWhiskerLeft R
      (Functor.associator DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus H).symm ≪≫
    (Functor.associator R (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus) H).symm ≪≫ ?_
  refine isoWhiskerRight (asIso η).symm H ≪≫ ?_
  refine Functor.associator R (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) H ≪≫
    isoWhiskerLeft R (Functor.associator F.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh H) ≪≫ ?_
  exact isoWhiskerLeft (injectiveResolutions C) (extendedHomotopyHomologyIso F p)

end DerivedComparison

/-- The connecting morphism `S.X₃ ⟶ S.X₁[1]` in `DerivedCategory.Plus C` of a short exact
sequence `S` of objects placed in degree `0`. -/
noncomputable def singleFunctorPlusδ
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
      (shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)).obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) :=
  DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))

/-- The triangle `S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ S.X₁[1]` in `DerivedCategory.Plus C` attached to a
short exact sequence `S`. -/
noncomputable def singleTrianglePlus
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map S.g) (singleFunctorPlusδ hS)

/-- The image of `singleTrianglePlus hS` in `DerivedCategory C` is `hS.singleTriangle`. -/
lemma ι_mapTriangle_obj_singleTrianglePlus
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    DerivedCategory.Plus.ι.mapTriangle.obj (singleTrianglePlus hS) = hS.singleTriangle := by
  rw [Functor.mapTriangle_obj]
  dsimp only [singleTrianglePlus, singleFunctorPlusδ, Triangle.mk_mor₁,
    Triangle.mk_mor₂, Triangle.mk_mor₃, Triangle.mk_obj₁]
  rw [Functor.map_preimage]
  exact congrArg (Triangle.mk ((DerivedCategory.singleFunctor C 0).map S.f)
    ((DerivedCategory.singleFunctor C 0).map S.g))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => hS.singleδ ≫ m)
          (Iso.inv_hom_id_app (Functor.commShiftIso DerivedCategory.Plus.ι (1 : ℤ))
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))).trans
        (Category.comp_id hS.singleδ)))

/-- The triangle `singleTrianglePlus hS` is distinguished in `DerivedCategory.Plus C`. -/
lemma singleTrianglePlus_distinguished
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    singleTrianglePlus hS ∈ distTriang (DerivedCategory.Plus C) := by
  show DerivedCategory.Plus.ι.mapTriangle.obj (singleTrianglePlus hS) ∈
    distTriang (DerivedCategory C)
  rw [ι_mapTriangle_obj_singleTrianglePlus hS]
  exact hS.singleTriangle_distinguished

/-- The connecting morphism of a short exact sequence in `DerivedCategory C`, with its source
and target spelled through `DerivedCategory.Plus.ι`. -/
private noncomputable def singleδι
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃) ⟶
      (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj
        (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) :=
  hS.singleδ

/-- The degree-`0` single functor `C ⥤ DerivedCategory.Plus C` as a δ-functor, with connecting
morphisms `singleFunctorPlusδ`. -/
noncomputable def singleFunctorPlusDelta
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] :
    Functor.DeltaFunctorStructure C (DerivedCategory.Plus C)
      (DerivedCategory.Plus.singleFunctor C 0) where
  δ hS := singleFunctorPlusδ hS
  distinguished hS := singleTrianglePlus_distinguished hS
  δ_naturality := by
    intro S₁ S₂ hS hS' φ
    let ι : DerivedCategory.Plus C ⥤ DerivedCategory C := DerivedCategory.Plus.ι
    let ξ := ι.commShiftIso (1 : ℤ)
    have hδ {S : ShortComplex C} (h : S.ShortExact) :
        ι.map (singleFunctorPlusδ h) ≫
        ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = singleδι h := by
      change DerivedCategory.Plus.ι.map (singleFunctorPlusδ h) ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = h.singleδ
      dsimp only [singleFunctorPlusδ]
      rw [Functor.map_preimage]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun m => h.singleδ ≫ m)
            (Iso.inv_hom_id_app (Functor.commShiftIso DerivedCategory.Plus.ι (1 : ℤ))
              ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))).trans
          (Category.comp_id _))
    have hξ :
        ι.map ((shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)).map
          ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) ≫
          ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁) =
        ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₁.X₁) ≫
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
            (ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) := by
      simpa only [Functor.comp_map] using
        ξ.hom.naturality ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)
    have hcomm : singleδι hS ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
          (ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) =
        ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃) ≫ singleδι hS' :=
      (ShortComplex.ShortExact.singleTriangle.map hS hS' φ).comm₃
    apply (Functor.map_injective ι)
    apply (cancel_mono (ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁))).mp
    simp only [Functor.map_comp]
    change (ι.map (singleFunctorPlusδ hS) ≫
        ι.map ((shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)).map
          ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁))) ≫
      ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁) =
      (ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃) ≫
        ι.map (singleFunctorPlusδ hS')) ≫
          ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁)
    calc
      _ = ι.map (singleFunctorPlusδ hS) ≫
            (ι.map ((shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)).map
              ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) ≫
                ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁)) := by
        simp [Category.assoc]
      _ = ι.map (singleFunctorPlusδ hS) ≫
            (ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₁.X₁) ≫
              (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
                (ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁))) := by
        rw [hξ]
      _ = singleδι hS ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
            (ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₁)) := by
        rw [← Category.assoc, hδ hS]
      _ = ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃) ≫ singleδι hS' := hcomm
      _ = ι.map ((DerivedCategory.Plus.singleFunctor C 0).map φ.τ₃) ≫
            (ι.map (singleFunctorPlusδ hS') ≫
              ξ.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁)) := by
        rw [hδ hS']
      _ = _ := by rw [Category.assoc]

end DerivedDelta

section StableLifts

attribute [local instance] HasDerivedCategory.standard

variable [Small.{v} A] [UnivLE.{max w v, v}]

private def cohomologyDelta : DeltaFunctor (ModuleSheaf.{u, v, w} A X) (ModuleCat.{v} A) := by
  let E := (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{v} A)).obj (op ⊤)
  have : E.Additive := sections_additive
  exact Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives E

private theorem cohomologyTowerLimit_exists_stable_lift
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F) (n : ℕ)
    (x : CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p))
    (hx : x.1 n = 0) :
    ∃ s : stableImage I F p (n + 1),
      ((cohomology p).map (powerSheafι I (n + 1) (F.obj (op (n + 1))))).hom s.1 =
        x.1 (n + 1) := by
  let H := cohomologyDelta (A := A) (X := X)
  have hH (q : ℕ) : H.functor q = cohomology q := rfl
  let S (m : ℕ) (hm : n + 1 ≤ m) : ShortComplex (ModuleSheaf.{u, v, w} A X) :=
    ShortComplex.mk _ _ (quotientTower_transition_annihilates I F hquotient n m hm)
  have hS (m : ℕ) (hm : n + 1 ≤ m) : (S m hm).ShortExact :=
    quotientTower_transition_shortExact I F hquotient n m hm
  have hex (m : ℕ) (hm : n + 1 ≤ m) :
      LinearMap.range (((H.functor p).map (S m hm).f).hom) =
        LinearMap.ker (((H.functor p).map (S m hm).g).hom) :=
    (H.exact_map (hS m hm) p).moduleCat_range_eq_ker
  have hzero (m : ℕ) (hm : n + 1 ≤ m) :
      (((H.functor p).map (S m hm).g).hom) (x.1 m) = 0 :=
    (cohomologyTowerLimit_map_coord (F ⋙ cohomology p) x n m (by omega)).trans hx
  obtain ⟨s, hs⟩ : x.1 (n + 1) ∈
      LinearMap.range (((H.functor p).map (S (n + 1) le_rfl).f).hom) := by
    rw [hex (n + 1) le_rfl]
    exact hzero (n + 1) le_rfl
  refine ⟨⟨s, ?_⟩, hs⟩
  apply (Submodule.mem_iInf _).mpr
  intro m
  apply (Submodule.mem_iInf _).mpr
  intro hm
  let φ : S m hm ⟶ S (n + 1) le_rfl :=
    { τ₁ := powerSheafMap I (n + 1) (F.map (homOfLE hm).op)
      τ₂ := F.map (homOfLE hm).op
      τ₃ := 𝟙 _
      comm₁₂ := powerSheafMap_ι I (n + 1) _
      comm₂₃ := by
        dsimp [S]
        rw [Category.comp_id, ← F.map_comp]
        rfl }
  have hcomm : (((H.functor p).map (S (n + 1) le_rfl).f).hom).comp
        (((H.functor p).map φ.τ₁).hom) =
      (((H.functor p).map φ.τ₂).hom).comp (((H.functor p).map (S m hm).f).hom) := by
    show ((H.functor p).map φ.τ₁ ≫ (H.functor p).map (S (n + 1) le_rfl).f).hom = _
    rw [← Functor.map_comp, φ.comm₁₂, Functor.map_comp]
    rfl
  have hxmap : (((H.functor p).map φ.τ₂).hom) (x.1 m) =
      (((H.functor p).map (S (n + 1) le_rfl).f).hom) s := by
    rw [hs]
    exact cohomologyTowerLimit_map_coord (F ⋙ cohomology p) x (n + 1) m hm
  cases p with
  | zero =>
    have := H.mono_map_f (hS (n + 1) le_rfl)
    obtain ⟨z, hz⟩ : x.1 m ∈ LinearMap.range
        (((H.functor 0).map (S m hm).f).hom) := by
      rw [hex m hm]
      exact hzero m hm
    refine ⟨z, ?_⟩
    apply (ModuleCat.mono_iff_injective ((H.functor 0).map
      (S (n + 1) le_rfl).f)).mp (H.mono_map_f (hS (n + 1) le_rfl))
    show (((H.functor 0).map (S (n + 1) le_rfl).f).hom)
      ((((H.functor 0).map φ.τ₁).hom) z) =
        (((H.functor 0).map (S (n + 1) le_rfl).f).hom) s
    rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hz, hxmap]
  | succ p =>
    apply mem_range_of_exact_commutative_diagram
      (H.δ (hS (n + 1) le_rfl) p).hom (H.δ (hS m hm) p).hom
      (((H.functor (p + 1)).map φ.τ₁).hom)
      (((H.functor (p + 1)).map (S (n + 1) le_rfl).f).hom)
      (((H.functor (p + 1)).map (S m hm).f).hom)
      (((H.functor (p + 1)).map φ.τ₂).hom)
      (((H.functor (p + 1)).map (S m hm).g).hom)
      (H.exact_δ₂ (hS (n + 1) le_rfl) p).moduleCat_range_eq_ker
      (hex m hm) ?_ hcomm s (x.1 m) (hzero m hm) hxmap
    have he := H.δ_naturality (hS m hm) (hS (n + 1) le_rfl) φ p
    have hid : φ.τ₃ = 𝟙 _ := rfl
    rw [hid, (H.functor p).map_id, Category.id_comp] at he
    exact congrArg ModuleCat.Hom.hom he.symm

private theorem canonicalStableImageAction_eval
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F)
    [Module (AssociatedGraded.gradedRing I) (StableImageSum I F p)]
    (hcanonical : IsCanonicalStableImageAction I F p)
    (k n : ℕ) (a : ↥(I ^ k)) (s : stableImage I F p n)
    (t : stableImage I F p (k + n))
    (hst : AssociatedGraded.classOfPow I k a • DirectSum.of (fun j => stableImage I F p j) n s =
      DirectSum.of (fun j => stableImage I F p j) (k + n) t)
    (x : CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p))
    (hs : ((cohomology p).map (powerSheafι I n (F.obj (op n)))).hom s.1 = x.1 n) :
    ((cohomology p).map (powerSheafι I (k + n) (F.obj (op (k + n))))).hom t.1 =
      a.1 • x.1 (k + n) := by
  let H := cohomology.{u, v, w} (A := A) (X := X) p
  have : Functor.Linear A H := cohomology_linear p
  obtain ⟨z, hz⟩ := (Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp s.2 (k + n)) (Nat.le_add_left n k)
  have ht := hcanonical k n a s z hz
  change stableImageSumι I F p
    (AssociatedGraded.classOfPow I k a • DirectSum.of (fun j => stableImage I F p j) n s) = _ at ht
  rw [hst] at ht
  have hval := congrArg (fun q => q (k + n)) ht
  rw [stableImageSumι_apply] at hval
  simp only [DirectSum.of_eq_same] at hval
  obtain ⟨g, hg, hgx⟩ := cohomologyTowerLimit_smul_coord I F p hquotient k n a
  have hcompat : (H.map (F.map (homOfLE (Nat.le_add_left n k)).op)).hom
      ((H.map (powerSheafι I n (F.obj (op (k + n))))).hom z) = x.1 n := by
    show (H.map (powerSheafι I n (F.obj (op (k + n)))) ≫
      H.map (F.map (homOfLE (Nat.le_add_left n k)).op)).hom z = _
    rw [← H.map_comp, ← powerSheafMap_ι, H.map_comp]
    show (H.map (powerSheafι I n (F.obj (op n)))).hom
      ((H.map (powerSheafMap I n (F.map (homOfLE (Nat.le_add_left n k)).op))).hom z) = _
    rw [hz, hs]
  show (H.map (powerSheafι I (k + n) _)).hom t.1 = _
  rw [hval]
  show (H.map (powerSheafSMul I k n a _) ≫ H.map (powerSheafι I (k + n) _)).hom z = _
  rw [← H.map_comp, powerSheafSMul_ι, Functor.map_smul]
  show a.1 • (H.map (powerSheafι I n _)).hom z = _
  rw [← hg, hcompat, hgx]

private theorem canonicalStableImageAction_eval_component
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F)
    [Module (AssociatedGraded.gradedRing I) (StableImageSum I F p)]
    (hcanonical : IsCanonicalStableImageAction I F p)
    (k n m : ℕ) (hm : k + n = m) (a : ↥(I ^ k)) (s : stableImage I F p n)
    (x : CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p))
    (hs : ((cohomology p).map (powerSheafι I n (F.obj (op n)))).hom s.1 = x.1 n) :
    ((cohomology p).map (powerSheafι I m (F.obj (op m)))).hom
      ((AssociatedGraded.classOfPow I k a • DirectSum.of (fun j => stableImage I F p j) n s) m).1 =
        a.1 • x.1 m := by
  subst m
  obtain ⟨t, ht⟩ := canonicalStableImageAction_is_graded I F p hcanonical k n a s
  rw [ht, DirectSum.of_eq_same]
  exact canonicalStableImageAction_eval I F p hquotient hcanonical k n a s t ht x hs

private theorem cohomologyTowerLimit_exists_approx
    (I : Ideal A) (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower I F) (hACC : StableImagesHaveGradedACC I F p) :
    ∃ (r : ℕ) (a : Fin r → A) (c : ℕ), (∀ i, a i ∈ I) ∧
      ∀ n, c ≤ n → ∀ x : CohomologyTowerLimit
        (fun j => cohomologyModule F p j) (cohomologyTransition F p),
        x.1 (n + 1) = 0 →
        ∃ y : Fin r → CohomologyTowerLimit
          (fun j => cohomologyModule F p j) (cohomologyTransition F p),
          (∀ i, (y i).1 n = 0) ∧ (x - ∑ i, a i • y i).1 (n + 2) = 0 := by
  classical
  obtain ⟨action, hcanonical, hnoeth⟩ := hACC
  let := action
  let := hnoeth
  let B : ℕ → Type v := fun n => stableImage I F p n
  let M := CohomologyTowerLimit (fun j => cohomologyModule F p j) (cohomologyTransition F p)
  let π := fun n => CohomologyTowerLimit.proj (fun j => cohomologyModule F p j)
    (cohomologyTransition F p) n
  let β (n : ℕ) : B n →ₗ[A] cohomologyModule F p n :=
    (((cohomology p).map (powerSheafι I n (F.obj (op n)))).hom).comp (stableImage I F p n).subtype
  let P : ∀ n, AddSubgroup (B n)
    | 0 => ⊥
    | n + 1 => (((π n).ker.map (π (n + 1))).comap (β (n + 1))).toAddSubgroup
  have hPmem (n : ℕ) (s : B (n + 1)) : s ∈ P (n + 1) ↔
      ∃ x : M, x.1 n = 0 ∧ β (n + 1) s = x.1 (n + 1) := by
    show (∃ x : M, x ∈ (π n).ker ∧ π (n + 1) x = β (n + 1) s) ↔ _
    exact exists_congr fun x => and_congr_right fun _ => eq_comm
  have hgraded := fun k (a : ↥(I ^ k)) n (x : B n) =>
    canonicalStableImageAction_is_graded I F p hcanonical k n a x
  have hP : ∀ k (a : ↥(I ^ k)) n (s : B n), s ∈ P n →
      ∃ t : B (k + n), t ∈ P (k + n) ∧
        AssociatedGraded.classOfPow I k a • DirectSum.of B n s = DirectSum.of B (k + n) t := by
    intro k a n s hs
    cases n with
    | zero =>
      have hs0 : s = 0 := hs
      subst s
      refine ⟨0, (P k).zero_mem, ?_⟩
      simp
    | succ n =>
      obtain ⟨x, hx, hsx⟩ := (hPmem n s).mp hs
      obtain ⟨t, ht⟩ := hgraded k a (n + 1) s
      refine ⟨t, ?_, ht⟩
      apply (hPmem (k + n) t).mpr
      refine ⟨a.1 • x, ?_, ?_⟩
      · obtain ⟨g, hg, hgx⟩ := cohomologyTowerLimit_smul_coord I F p hquotient k n a
        show a.1 • x.1 (k + n) = 0
        rw [← hgx, hx, map_zero]
      · exact canonicalStableImageAction_eval I F p hquotient hcanonical k (n + 1) a s t ht x hsx
  let E := AssociatedGraded.homogeneousSubmodule I P hP
  have hhom : ∀ n x, x ∈ E → AssociatedGraded.homogeneousPart B n x ∈ E := fun n x hx =>
    (AssociatedGraded.of_mem_homogeneousSubmodule_iff I P hP n (x n)).mpr
      ((AssociatedGraded.mem_homogeneousSubmodule I P hP x).mp hx n)
  obtain ⟨s, a, c, hc⟩ := AssociatedGraded.exists_eventual_degree_one_generators I hgraded E hhom
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (a (e.symm i)).1, c, ?_, ?_⟩
  · intro i
    simpa only [pow_one] using (a (e.symm i)).2
  · intro n hn x hx
    obtain ⟨t, ht⟩ := cohomologyTowerLimit_exists_stable_lift I F p hquotient (n + 1) x hx
    have htE : DirectSum.of B (n + 2) t ∈ E :=
      (AssociatedGraded.of_mem_homogeneousSubmodule_iff I P hP (n + 2) t).mpr
        ((hPmem (n + 1) t).mpr ⟨x, hx, ht⟩)
    obtain ⟨z, hz, htz⟩ := hc (n + 1) (by omega) t htE
    have hzx (i : s) : ∃ y : M, y.1 n = 0 ∧ β (n + 1) (z i) = y.1 (n + 1) :=
      (hPmem n (z i)).mp ((AssociatedGraded.of_mem_homogeneousSubmodule_iff I P hP _ _).mp (hz i))
    choose y hy hzy using hzx
    refine ⟨fun i => y (e.symm i), fun i => hy (e.symm i), ?_⟩
    have heval (i : s) :
        ((cohomology p).map (powerSheafι I (n + 2) (F.obj (op (n + 2))))).hom
            ((AssociatedGraded.classOfPow I 1 (a i) • DirectSum.of B (n + 1) (z i)) (n + 2)).1 =
          (a i).1 • (y i).1 (n + 2) :=
      canonicalStableImageAction_eval_component I F p hquotient hcanonical
        1 (n + 1) (n + 2) (by omega) (a i) (z i) (y i) (hzy i)
    let ev : StableImageSum I F p →ₗ[A] cohomologyModule F p (n + 2) :=
      (β (n + 2)).comp (DirectSum.component A ℕ B (n + 2))
    have hsum := congrArg ev htz
    rw [map_sum] at hsum
    have hevt : ev (DirectSum.of B (n + 1 + 1) t) = β (n + 2) t := by
      show β (n + 2) (DirectSum.of B (n + 2) t (n + 2)) = _
      rw [DirectSum.of_eq_same]
    rw [hevt] at hsum
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    apply sub_eq_zero.mpr
    rw [← ht]
    show β (n + 2) t = _
    rw [hsum]
    calc
      _ = ∑ i : s, (a i).1 • (y i).1 (n + 2) :=
        Finset.sum_congr rfl (fun i _ => heval i)
      _ = _ := (Equiv.sum_comp e.symm
        (fun i : s => (a i).1 • (y i).1 (n + 2))).symm

end StableLifts

/-- For a quotient tower of sheaves `F` whose stable images satisfy ACC over `gr_I(A)`, the
inverse-limit topology on `lim Hᵖ(X, F_n)` equals the `I`-adic topology. -/
@[stacks 0GYN,
  stacks 0GYM "the same conclusion under the stronger ACC hypothesis on the ambient graded"]
public theorem cohomologyTowerLimit_topology_eq_adic
    [Small.{v} A] [UnivLE.{max w v, v}]
    (I : Ideal A) (X : Type w) [TopologicalSpace X]
    (F : ℕᵒᵖ ⥤ ModuleSheaf.{u, v, w} A X) (p : ℕ)
    (hquotient : IsQuotientTower.{u, v, w} I F)
    (hACC : StableImagesHaveGradedACC.{u, v, w} I F p) :
    CohomologyTowerLimit.limitTopology (fun n => cohomologyModule.{u, v, w} F p n)
        (cohomologyTransition.{u, v, w} F p) =
      I.adicModuleTopology
        (CohomologyTowerLimit (fun n => cohomologyModule.{u, v, w} F p n)
          (cohomologyTransition.{u, v, w} F p)) := by
  let C : ℕ → Type v := fun n => cohomologyModule.{u, v, w} F p n
  let f : ∀ n, C (n + 1) →ₗ[A] C n := cohomologyTransition.{u, v, w} F p
  let M := CohomologyTowerLimit C f
  let π := fun n => CohomologyTowerLimit.proj C f n
  have happrox : ∃ (r : ℕ) (a : Fin r → A) (c : ℕ),
      (∀ i, a i ∈ I) ∧ ∀ n, c ≤ n → ∀ x : M,
        x ∈ (π (n + 1)).ker → ∃ y : Fin r → M,
          (∀ i, y i ∈ (π n).ker) ∧
            x - ∑ i, a i • y i ∈ (π (n + 2)).ker := by
    exact cohomologyTowerLimit_exists_approx I F p hquotient hACC
  obtain ⟨r, a, c, ha, happrox⟩ := happrox
  rw [cohomologyTowerLimit_limitTopology_eq_iInf_induced_proj f]
  apply iInf_induced_eq_adicModuleTopology (R := A) (M := M) I π
  · intro i j hij
    exact cohomologyTowerLimit_proj_ker_antitone f i j hij
  · intro n
    refine ⟨n + 1, ?_⟩
    exact cohomologyTowerLimit_cohomology_ideal_power_le_proj_ker I F p hquotient n
  · intro k
    exact ⟨c + k, cohomologyTowerLimit_ker_le_ideal_power_of_approx
      f I a ha c happrox k⟩

end Stacks.Cohomology.QuotientTowers
