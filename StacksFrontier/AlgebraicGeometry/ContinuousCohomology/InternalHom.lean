module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.HomInvariants
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal hom of continuous group modules, and `M ⊗ -` as its left adjoint

Let `G` be a topological group, `R` a commutative ring, and let `M` be a continuous discrete
`R`-`G`-module which is finite projective over `R`. The conjugation action of `G` on
`Hom_R(M, N)`, given by `(g · f)(m) = g · f(g⁻¹ · m)`, makes `Hom_R(M, N)` into a continuous
discrete `R`-`G`-module functorially in `N`, and the diagonal action does the same for
`M ⊗_R N`. The two functors are adjoint: this is the identification
`Hom(M ⊗_R E, N) = Hom(E, Hom_R(M, N))` used in [Stacks, Tag 0DVE].

For `M` finite projective the internal hom is the module `Mᵛ ⊗_R N` of that tag, with the
contragredient action on the dual factor and the diagonal action overall; the identification is
`Stacks.ContinuousCohomology.dualTensorIsoInternalHom`.

## Main definitions

* `Stacks.ContinuousCohomology.internalHomFunctor` — the functor `N ↦ Hom_R(M, N)` with the
  conjugation action of `G`.
* `Stacks.ContinuousCohomology.tensorLeftFunctor` — the functor `N ↦ M ⊗_R N` with the diagonal
  action of `G`.
* `Stacks.ContinuousCohomology.tensorInternalHomAdjunction` — the adjunction between them.
* `Stacks.ContinuousCohomology.dualTensorIsoInternalHom` — the identification of `Mᵛ ⊗_R N` with
  `Hom_R(M, N)` as continuous discrete `R`-`G`-modules.

## Main results

* `Stacks.ContinuousCohomology.internalHomFunctor_preservesInjectiveObjects` — `Hom_R(M, -)`
  carries injective objects to injective objects.
* `Stacks.ContinuousCohomology.preservesFiniteLimits_internalHomFunctor` and
  `Stacks.ContinuousCohomology.preservesFiniteColimits_internalHomFunctor` — `Hom_R(M, -)` is
  exact.

## Implementation notes

The adjunction is built on representations rather than by restricting Mathlib's
`MonoidalClosed (Rep R G)`: that instance is available only when the universe of the modules
agrees with the universe of the ring, whereas the coefficient universe of a continuous discrete
`R`-`G`-module is independent of the two others. What is taken from Mathlib is the internal hom
`Rep.ihom`, which is universe polymorphic, and `Representation.tprod`; the hom-set bijection and
its naturality are those of `Rep.tensorHomEquiv`, reproved with the universes unconstrained.

## References

* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/


@[expose] public noncomputable section

open CategoryTheory Limits TensorProduct

universe u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

section Representations

/-- Tensoring on the left by a representation `A`, with the diagonal action of `G`. This is the
functor left adjoint to `Rep.ihom A`, at unconstrained universes. -/
def repTensorLeft (A : Rep.{w} R G) : Rep.{w} R G ⥤ Rep.{w} R G where
  obj B := Rep.of (Representation.tprod A.ρ B.ρ)
  map {B B'} f := Rep.ofHom ⟨TensorProduct.map LinearMap.id f.hom.toLinearMap, by
    intro g
    ext x y
    change A.ρ g x ⊗ₜ[R] f.hom.toLinearMap (B.ρ g y) =
      A.ρ g x ⊗ₜ[R] B'.ρ g (f.hom.toLinearMap y)
    exact congrArg (fun z => A.ρ g x ⊗ₜ[R] z)
      (congrArg (fun q : B.V →ₗ[R] B'.V => q y) (f.hom.isIntertwining' g))⟩
  map_id B := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl

/-- The underlying map of a morphism of representations `B ⟶ Hom_R(A, C)`, read as a bilinear
map `B → A → C`. -/
abbrev ihomBilin {A B C : Rep.{w} R G} (f : B ⟶ (Rep.ihom A).obj C) :
    B.V →ₗ[R] A.V →ₗ[R] C.V := f.hom.toLinearMap

/-- The hom-set bijection `Hom(A ⊗ B, C) ≃ Hom(B, Hom_R(A, C))` of representations: curry the
underlying bilinear map and flip its arguments. -/
@[sga "3 VIIB 0.3.5" "(1), special case"]
def repTensorHomEquiv (A B C : Rep.{w} R G) :
    ((repTensorLeft R G A).obj B ⟶ C) ≃ (B ⟶ (Rep.ihom A).obj C) where
  toFun f := Rep.ofHom ⟨(TensorProduct.curry f.hom.toLinearMap).flip, by
    intro g
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    have h : f.hom.toLinearMap (x ⊗ₜ[R] B.ρ g y)
        = C.ρ g (f.hom.toLinearMap ((A.ρ g⁻¹) x ⊗ₜ[R] y)) := by
      have h0 : f.hom.toLinearMap (Representation.tprod A.ρ B.ρ g ((A.ρ g⁻¹) x ⊗ₜ[R] y))
          = C.ρ g (f.hom.toLinearMap ((A.ρ g⁻¹) x ⊗ₜ[R] y)) := Rep.hom_comm_apply f g _
      simpa [Representation.tprod_apply] using h0
    exact h⟩
  invFun f := Rep.ofHom ⟨TensorProduct.uncurry (.id R) _ _ _ (ihomBilin R G f).flip, by
    intro g
    apply TensorProduct.ext'
    intro x y
    have h0 : ihomBilin R G f ∘ₗ B.ρ g
        = (Representation.linHom A.ρ C.ρ g).comp (ihomBilin R G f) := f.hom.isIntertwining' g
    have h := LinearMap.congr_fun (LinearMap.congr_fun h0 y) (A.ρ g x)
    simpa using h⟩
  left_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl
  right_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro x
    rfl

/-- Tensoring by `A` is left adjoint to the internal hom out of `A`, for representations at
unconstrained universes. -/
def repTensorAdjunction (A : Rep.{w} R G) : repTensorLeft R G A ⊣ Rep.ihom A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := repTensorHomEquiv R G A
      homEquiv_naturality_left_symm := fun _ _ => by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply TensorProduct.ext'
        intro x y
        rfl
      homEquiv_naturality_right := fun _ _ => by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        rfl }

end Representations

section Actions

/-- Tensoring on the left by an object of `Action (ModuleCat R) G`, with the diagonal action. -/
abbrev actionTensorLeft (A : Action (ModuleCat.{w} R) G) :
    Action (ModuleCat.{w} R) G ⥤ Action (ModuleCat.{w} R) G :=
  Rep.ActionToRep R G ⋙ repTensorLeft R G ((Rep.ActionToRep R G).obj A) ⋙ Rep.RepToAction R G

/-- The internal hom out of an object of `Action (ModuleCat R) G`, with the conjugation
action. -/
abbrev actionInternalHom (A : Action (ModuleCat.{w} R) G) :
    Action (ModuleCat.{w} R) G ⥤ Action (ModuleCat.{w} R) G :=
  Rep.ActionToRep R G ⋙ Rep.ihom ((Rep.ActionToRep R G).obj A) ⋙ Rep.RepToAction R G

/-- Tensoring by `A` is left adjoint to the internal hom out of `A`, transported from
representations to actions along the equivalence between the two. -/
def actionTensorAdjunction (A : Action (ModuleCat.{w} R) G) :
    actionTensorLeft R G A ⊣ actionInternalHom R G A :=
  (((Rep.repIsoAction R G).symm.toAdjunction.comp
    (repTensorAdjunction R G ((Rep.ActionToRep R G).obj A))).comp
      (Rep.repIsoAction R G).toAdjunction)

end Actions

section Continuity

variable (M N : Stacks.Injectives.ContinuousModule.{u, v, w} R G)

/-- An action on a discrete module is continuous once each orbit map is locally constant. -/
private theorem isContinuous_of_isLocallyConstant {X : Action (ModuleCat.{w} R) G}
    (h : ∀ x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X,
      IsLocallyConstant fun g : G =>
        ((X.ρ g).hom x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X)) :
    Action.IsContinuous X := by
  rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
  let _ : TopologicalSpace X.V := ⊥
  exact fun x => (h x).continuous

/-- For `M` finite projective, the conjugation action of `G` on `Hom_R(M, N)` is locally constant
in the group variable. -/
lemma isLocallyConstant_linHom [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]
    (f : M.obj.obj.V →ₗ[R] N.obj.obj.V) :
    IsLocallyConstant (fun g : G => Representation.linHom (rep R G M) (rep R G N) g f) := by
  obtain ⟨z, rfl⟩ := (smallModelEquivHom R G M N).surjective f
  convert (isLocallyConstant_dualTensorSmallRep R G M N z).comp (smallModelEquivHom R G M N)
    using 1
  exact funext fun g => smallModelEquivHom_intertwines R G M N g z |>.symm

/-- The conjugation action on `Hom_R(M, N)` is continuous for the discrete topology when `M` is
finite projective over `R`. -/
lemma actionInternalHom_isContinuous [Module.Finite R M.obj.obj.V]
    [Module.Projective R M.obj.obj.V] :
    Action.IsContinuous (V := ModuleCat.{w} R)
      ((actionInternalHom R G M.obj.obj).obj N.obj.obj) := by
  exact isContinuous_of_isLocallyConstant R G (isLocallyConstant_linHom R G M N)

/-- **Local constancy of the diagonal action on `M ⊗_R N`.** Every `g₀ : G` has an open
neighbourhood on whose elements the diagonal action on a fixed `x` agrees with that of `g₀`. -/
lemma exists_isOpen_tprod_eq (x : M.obj.obj.V ⊗[R] N.obj.obj.V) (g₀ : G) :
    ∃ U : Set G, IsOpen U ∧ g₀ ∈ U ∧ ∀ g ∈ U,
      (Representation.tprod (rep R G M) (rep R G N)) g x
        = (Representation.tprod (rep R G M) (rep R G N)) g₀ x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨Set.univ, isOpen_univ, trivial, fun g _ => by simp⟩
  | tmul m y =>
    refine ⟨{g : G | rep R G M g m = rep R G M g₀ m} ∩
      {g : G | rep R G N g y = rep R G N g₀ y},
      ((isLocallyConstant_rep R G M m).isOpen_fiber _).inter
        ((isLocallyConstant_rep R G N y).isOpen_fiber _),
      ⟨rfl, rfl⟩, fun g hg => ?_⟩
    have hM : rep R G M g m = rep R G M g₀ m := hg.1
    have hN : rep R G N g y = rep R G N g₀ y := hg.2
    simp only [Representation.tprod_apply, TensorProduct.map_tmul, hM, hN]
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨U₁, hU₁, hg₁, he₁⟩ := h₁
    obtain ⟨U₂, hU₂, hg₂, he₂⟩ := h₂
    exact ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, fun g hg => by
      rw [map_add, map_add, he₁ g hg.1, he₂ g hg.2]⟩

/-- Local constancy of the diagonal action on `M ⊗_R N`, as an `IsLocallyConstant` statement. -/
lemma isLocallyConstant_tprod (x : M.obj.obj.V ⊗[R] N.obj.obj.V) :
    IsLocallyConstant (fun g : G => (Representation.tprod (rep R G M) (rep R G N)) g x) := by
  rw [IsLocallyConstant.iff_exists_open]
  exact fun g₀ => exists_isOpen_tprod_eq R G M N x g₀

/-- The diagonal action on `M ⊗_R N` is continuous for the discrete topology. -/
lemma actionTensorLeft_isContinuous :
    Action.IsContinuous (V := ModuleCat.{w} R)
      ((actionTensorLeft R G M.obj.obj).obj N.obj.obj) := by
  exact isContinuous_of_isLocallyConstant R G (isLocallyConstant_tprod R G M N)

end Continuity

section Functors

variable (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G)

/-- The functor `N ↦ M ⊗_R N` on continuous discrete `R`-`G`-modules, with the diagonal action
of `G`. -/
def tensorLeftFunctor :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤
      Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (continuousModuleToAction R G ⋙ actionTensorLeft R G M.obj.obj)
      (fun N => actionTensorLeft_isContinuous R G M N))
    (fun _ => ⟨rfl⟩)

variable [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- The functor `N ↦ Hom_R(M, N)` on continuous discrete `R`-`G`-modules, with the conjugation
action of `G`. -/
def internalHomFunctor :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤
      Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (continuousModuleToAction R G ⋙ actionInternalHom R G M.obj.obj)
      (fun N => actionInternalHom_isContinuous R G M N))
    (fun _ => ⟨rfl⟩)

/-- The internal hom out of `M` is additive. -/
instance internalHomFunctor_additive : (internalHomFunctor R G M).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    rfl

/-- Tensoring by `M` is left adjoint to the internal hom out of `M`, for continuous discrete
`R`-`G`-modules. This is the identification `Hom(M ⊗_R E, N) = Hom(E, Hom_R(M, N))` of
[Stacks, Tag 0DVE]. -/
def tensorInternalHomAdjunction :
    tensorLeftFunctor R G M ⊣ internalHomFunctor R G M :=
  (actionTensorAdjunction R G M.obj.obj).restrictFullyFaithful
    (iC := continuousModuleToAction R G) (iD := continuousModuleToAction R G)
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _))
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      apply Action.hom_ext
      rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      apply Action.hom_ext
      rfl))

/-- Tensoring by `M` is additive. -/
instance tensorLeftFunctor_additive : (tensorLeftFunctor R G M).Additive :=
  (tensorInternalHomAdjunction R G M).left_adjoint_additive

end Functors

section Exactness

/-- The underlying `R`-module of a continuous discrete `R`-`G`-module. -/
abbrev continuousModuleUnderlying :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} R :=
  continuousModuleToAction R G ⋙ Action.forget (ModuleCat.{w} R) G

/-- The underlying `R`-module functor is additive. -/
instance additive_continuousModuleUnderlying :
    (continuousModuleUnderlying.{u, v, w} R G).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    rfl

/-- The underlying `R`-module functor is left exact. -/
instance preservesFiniteLimits_continuousModuleUnderlying :
    PreservesFiniteLimits (continuousModuleUnderlying.{u, v, w} R G) :=
  Limits.comp_preservesFiniteLimits _ _

/-- The underlying `R`-module functor is right exact. -/
instance preservesFiniteColimits_continuousModuleUnderlying :
    PreservesFiniteColimits (continuousModuleUnderlying.{u, v, w} R G) :=
  Limits.comp_preservesFiniteColimits _ _

/-- A monomorphism of continuous discrete `R`-`G`-modules is injective on underlying
modules. -/
instance preservesMonomorphisms_continuousModuleUnderlying :
    (continuousModuleUnderlying.{u, v, w} R G).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_preserves_shortExact_left _
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).1 inferInstance)

variable (M : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
  [Module.Finite R M.obj.obj.V] [Module.Projective R M.obj.obj.V]

/-- Tensoring by a finite projective `M` preserves monomorphisms. -/
instance tensorLeftFunctor_preservesMonomorphisms :
    (tensorLeftFunctor R G M).PreservesMonomorphisms := by
  let _ : Module.Flat R M.obj.obj.V := Module.Flat.of_projective
  refine ⟨fun {X Y} f hf => ?_⟩
  have hinj : Function.Injective
      ((continuousModuleUnderlying.{u, v, w} R G).map f).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hmono : Mono ((continuousModuleUnderlying.{u, v, w} R G).map
      ((tensorLeftFunctor R G M).map f)) := by
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M.obj.obj.V)
      ((continuousModuleUnderlying.{u, v, w} R G).map f).hom hinj
  exact (continuousModuleUnderlying.{u, v, w} R G).mono_of_mono_map hmono

/-- For `M` finite projective, `Hom_R(M, -)` preserves epimorphisms. -/
instance internalHomFunctor_preservesEpimorphisms :
    (internalHomFunctor R G M).PreservesEpimorphisms := by
  refine ⟨fun {X Y} f hf => ?_⟩
  have hsurj : Function.Surjective
      ((continuousModuleUnderlying.{u, v, w} R G).map f).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hepi : Epi ((continuousModuleUnderlying.{u, v, w} R G).map
      ((internalHomFunctor R G M).map f)) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun φ => ?_
    obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property
      ((continuousModuleUnderlying.{u, v, w} R G).map f).hom
      (show M.obj.obj.V →ₗ[R] Y.obj.obj.V from φ) hsurj
    exact ⟨ψ, hψ⟩
  exact (continuousModuleUnderlying.{u, v, w} R G).epi_of_epi_map hepi

/-- `Hom_R(M, -)` is left exact. -/
instance preservesFiniteLimits_internalHomFunctor :
    PreservesFiniteLimits (internalHomFunctor R G M) :=
  letI : PreservesLimitsOfSize (internalHomFunctor R G M) :=
    (tensorInternalHomAdjunction R G M).rightAdjoint_preservesLimits
  inferInstance

/-- For `M` finite projective, `Hom_R(M, -)` is right exact. -/
instance preservesFiniteColimits_internalHomFunctor :
    PreservesFiniteColimits (internalHomFunctor R G M) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun S hS => by
    refine ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (internalHomFunctor R G M)).1 inferInstance S hS).1, ?_⟩
    have := hS.epi_g
    exact inferInstance

/-- For `M` finite projective, `Hom_R(M, -)` carries injective objects to injective objects. -/
instance internalHomFunctor_preservesInjectiveObjects :
    (internalHomFunctor R G M).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (tensorInternalHomAdjunction R G M)

/-- For `M` finite projective over `R`, the continuous discrete `R`-`G`-module `Mᵛ ⊗_R N` with the
contragredient action on the dual factor and the diagonal action overall is `Hom_R(M, N)` with the
conjugation action. -/
@[sga "3 III 0.6" "special case"]
def dualTensorIsoInternalHom (N : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    dualTensorContinuousModule.{u, v, w} R G M N ≅ (internalHomFunctor R G M).obj N :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    ((Rep.RepToAction R G).mapIso (Rep.mkIso
      (Representation.Equiv.mk (smallModelEquivHom R G M N) (fun g => by
        apply LinearMap.ext
        intro z
        exact smallModelEquivHom_intertwines R G M N g z)))))

end Exactness

end Stacks.ContinuousCohomology
