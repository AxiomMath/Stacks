module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Restriction and coinduction of discrete modules

Let `G` be a topological group. A continuous homomorphism `φ : G' → G` turns a discrete
`G`-module into a discrete `G'`-module by restricting the action along `φ`. For a subgroup
`H ⊆ G`, the right adjoint of restriction from `G` to `H` is *coinduction*: the coinduced module
of a discrete `H`-module `N` is the group of functions `f : G → N` satisfying `f (h * x) = h • f x`
for `h ∈ H` which are invariant under right translation by an open subgroup of `G`, and `G` acts
on it by right translation, `(g • f) x = f (x * g)`.

Restriction is exact. When `G` is profinite, coinduction is exact as well: a surjection of
discrete `H`-modules induces a surjection on coinduced modules.

## Main definitions

* `Stacks.GroupCohomology.restriction`: restriction of discrete modules along a continuous
  homomorphism.
* `Stacks.GroupCohomology.coinduction`: the coinduced discrete `G`-module of a discrete
  `H`-module.
* `Stacks.GroupCohomology.restrictionCoinductionAdjunction`: restriction from `G` to `H` is left
  adjoint to coinduction.

## Main results

* `Stacks.GroupCohomology.epi_iff_surjective` and `Stacks.GroupCohomology.mono_iff_injective`:
  epimorphisms and monomorphisms of discrete modules are the surjective and the injective
  equivariant maps.
* `Stacks.GroupCohomology.surjective_coinduction_map`: over a profinite group, coinduction
  preserves surjections.
* The instances `PreservesFiniteLimits` and `PreservesFiniteColimits` for restriction and, over
  a profinite group, for coinduction.

## Implementation notes

Discrete `G`-modules are the objects of `Stacks.GroupCohomology.ContinuousGModule G`, continuous
actions of `G` on discrete `ℤ`-modules. Coinduced modules are built from a representation by
`Stacks.GroupCohomology.ofRepresentation`, and morphisms are built and read through
`Stacks.GroupCohomology.gModuleHomEquiv`. Coinduction raises the universe of the coefficients to
contain that of the group, so the two categories are taken at a coefficient universe
`max v w` for a group in `Type v`.

The condition of being invariant under an open subgroup is stated through
`Stacks.GroupCohomology.rightStabilizer`, the subgroup of right translations fixing a function;
it is exactly the stabilizer of the function for the action by right translation, which is what
makes the coinduced module discrete.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [J.-P. Serre, *Galois cohomology*, I.2.5][serre1997galois]
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v v' w

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology (continuousModuleUnderlying continuousModuleToAction)

section Underlying

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- An epimorphism of discrete `G`-modules is a surjective equivariant map. -/
theorem epi_iff_surjective {X Y : ContinuousGModule.{v, w} G} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f.hom.hom.hom.hom := by
  rw [← ModuleCat.epi_iff_surjective]
  exact ((continuousModuleUnderlying ℤ G).epi_map_iff_epi f).symm

/-- A monomorphism of discrete `G`-modules is an injective equivariant map. -/
theorem mono_iff_injective {X Y : ContinuousGModule.{v, w} G} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.hom.hom.hom.hom := by
  rw [← ModuleCat.mono_iff_injective]
  exact ((continuousModuleUnderlying ℤ G).mono_map_iff_mono f).symm

/-- The action of a product is the composite of the actions. -/
theorem ρ_mul_apply (X : ContinuousGModule.{v, w} G) (a b : G) (x : X.obj.obj.V) :
    (X.obj.obj.ρ (a * b)).asHom.hom x = (X.obj.obj.ρ a).asHom.hom ((X.obj.obj.ρ b).asHom.hom x) :=
  (congrArg (fun e : End X.obj.obj.V ↦ e.asHom.hom x) (map_mul X.obj.obj.ρ a b)).trans rfl

/-- The identity acts trivially. -/
@[simp]
theorem ρ_one_apply (X : ContinuousGModule.{v, w} G) (x : X.obj.obj.V) :
    (X.obj.obj.ρ 1).asHom.hom x = x :=
  (congrArg (fun e : End X.obj.obj.V ↦ e.asHom.hom x) (map_one X.obj.obj.ρ)).trans rfl

/-- Acting by `a⁻¹` undoes acting by `a`. -/
@[simp]
theorem ρ_inv_apply_ρ_apply (X : ContinuousGModule.{v, w} G) (a : G) (x : X.obj.obj.V) :
    (X.obj.obj.ρ a⁻¹).asHom.hom ((X.obj.obj.ρ a).asHom.hom x) = x := by
  rw [← ρ_mul_apply, inv_mul_cancel, ρ_one_apply]

/-- Acting by `a` undoes acting by `a⁻¹`. -/
@[simp]
theorem ρ_apply_ρ_inv_apply (X : ContinuousGModule.{v, w} G) (a : G) (x : X.obj.obj.V) :
    (X.obj.obj.ρ a).asHom.hom ((X.obj.obj.ρ a⁻¹).asHom.hom x) = x := by
  rw [← ρ_mul_apply, mul_inv_cancel, ρ_one_apply]

/-- Two morphisms of discrete `G`-modules agreeing on elements are equal. -/
theorem hom_ext {X Y : ContinuousGModule.{v, w} G} {f g : X ⟶ Y}
    (h : ∀ x, f.hom.hom.hom.hom x = g.hom.hom.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  exact ModuleCat.hom_ext (LinearMap.ext h)

/-- A morphism of discrete `G`-modules commutes with the action. -/
theorem hom_comm {X Y : ContinuousGModule.{v, w} G} (f : X ⟶ Y) (g : G) (x : X.obj.obj.V) :
    f.hom.hom.hom.hom ((X.obj.obj.ρ g).asHom.hom x) =
      (Y.obj.obj.ρ g).asHom.hom (f.hom.hom.hom.hom x) :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) x

/-- A short complex of discrete `G`-modules is short exact when it is so on underlying
groups. -/
theorem shortExact_of_underlying {S : ShortComplex (ContinuousGModule.{v, w} G)}
    (h : (S.map (continuousModuleUnderlying ℤ G)).ShortExact) : S.ShortExact :=
  ShortExact.reflects_shortExact_of_faithful (continuousModuleUnderlying ℤ G) h

end Underlying

section Restriction

variable {G : Type v} [Group G] [TopologicalSpace G] {G' : Type v'} [Group G']
  [TopologicalSpace G']

section

open scoped Stacks.DiscreteModuleTopology

/-- The action of `G'` through a continuous homomorphism `G' → G` on a discrete `G`-module is
continuous. -/
lemma isContinuous_res_obj {φ : G' →* G} (hφ : Continuous φ)
    (X : ContinuousGModule.{v, w} G) :
    ((Action.res (ModuleCat.{w} ℤ) φ).obj X.obj.obj).IsContinuous := by
  rw [Action.isContinuous_def]
  exact ((Action.isContinuous_def _).mp X.obj.property).comp (hφ.prodMap continuous_id)

end

variable (φ : G' →* G) (hφ : Continuous φ)

/-- **Restriction of discrete modules along a continuous homomorphism** `φ : G' → G`: a discrete
`G`-module, with `G'` acting through `φ`. -/
def restriction (φ : G' →* G) (hφ : Continuous φ) :
    ContinuousGModule.{v, w} G ⥤ ContinuousGModule.{v', w} G' :=
  ObjectProperty.lift _ (ObjectProperty.lift _
    (continuousModuleToAction ℤ G ⋙ Action.res (ModuleCat.{w} ℤ) φ)
      (isContinuous_res_obj hφ)) (fun _ ↦ ⟨rfl⟩)

/-- An element `g` of `G'` acts on the restriction of `X` as `φ g` acts on `X`. -/
@[simp]
lemma restriction_obj_ρ (X : ContinuousGModule.{v, w} G) (g : G') (x : X.obj.obj.V) :
    (((restriction φ hφ).obj X).obj.obj.ρ g).asHom.hom x = (X.obj.obj.ρ (φ g)).asHom.hom x := rfl

/-- Restriction does not change the underlying map of a morphism. -/
@[simp]
lemma restriction_map_apply {X Y : ContinuousGModule.{v, w} G} (f : X ⟶ Y) (x : X.obj.obj.V) :
    ((restriction φ hφ).map f).hom.hom.hom.hom x = f.hom.hom.hom.hom x := rfl

/-- Restriction is an additive functor. -/
instance restriction_additive : (restriction.{v, v', w} φ hφ).Additive where
  map_add := hom_ext fun _ ↦ rfl

/-- Restriction is faithful. -/
instance : (restriction.{v, v', w} φ hφ).Faithful where
  map_injective {X Y} f g h := hom_ext fun x ↦ by
    have := congrArg (fun k ↦ k.hom.hom.hom.hom x) h
    exact this

/-- Restriction maps short exact sequences to short exact sequences: on underlying groups it
does nothing. -/
theorem restriction_shortExact {S : ShortComplex (ContinuousGModule.{v, w} G)}
    (hS : S.ShortExact) : (S.map (restriction φ hφ)).ShortExact :=
  shortExact_of_underlying (hS.map_of_exact (continuousModuleUnderlying ℤ G))

/-- Restriction preserves finite limits. -/
instance : PreservesFiniteLimits (restriction.{v, v', w} φ hφ) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun _ hS ↦
    ⟨(restriction_shortExact φ hφ hS).exact, (restriction_shortExact φ hφ hS).mono_f⟩

/-- Restriction preserves finite colimits. -/
instance : PreservesFiniteColimits (restriction.{v, v', w} φ hφ) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun _ hS ↦
    ⟨(restriction_shortExact φ hφ hS).exact, (restriction_shortExact φ hφ hS).epi_g⟩

/-- Restriction preserves monomorphisms. -/
instance restriction_preservesMonomorphisms :
    (restriction.{v, v', w} φ hφ).PreservesMonomorphisms :=
  Functor.preservesMonomorphisms_of_preserves_shortExact_left _
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).1 inferInstance)

end Restriction

section Coinduction

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- The subgroup of right translations of `G` fixing a function on `G`. -/
def rightStabilizer {X : Type*} (f : G → X) : Subgroup G where
  carrier := {g | ∀ x, f (x * g) = f x}
  one_mem' := by simp
  mul_mem' {a b} ha hb x := by
    rw [← mul_assoc, hb (x * a), ha x]
  inv_mem' {a} ha x := by
    simpa using (ha (x * a⁻¹)).symm

omit [TopologicalSpace G] in
/-- `g` lies in the right stabilizer of `f` if and only if `f (x * g) = f x` for every `x`. -/
lemma mem_rightStabilizer {X : Type*} {f : G → X} {g : G} :
    g ∈ rightStabilizer f ↔ ∀ x, f (x * g) = f x := Iff.rfl

variable [IsTopologicalGroup G] (H : Subgroup G)

/-- The functions `f : G → N` with `f (h * x) = h • f x` for `h ∈ H` which are invariant under
right translation by an open subgroup: the underlying group of the coinduced module. -/
def coinductionCarrier (N : ContinuousGModule.{v, w} H) : AddSubgroup (G → N.obj.obj.V) where
  carrier := {f | (∀ (h : H) x, f (h * x) = (N.obj.obj.ρ h).asHom.hom (f x)) ∧
    IsOpen (rightStabilizer f : Set G)}
  zero_mem' := ⟨fun h x ↦ by simp, by
    have : rightStabilizer (0 : G → N.obj.obj.V) = ⊤ := by
      ext g
      simp [mem_rightStabilizer]
    rw [this]
    exact isOpen_univ⟩
  add_mem' {f f'} hf hf' := ⟨fun h x ↦ by simp [hf.1 h x, hf'.1 h x],
    Subgroup.isOpen_mono (H₁ := rightStabilizer f ⊓ rightStabilizer f')
      (fun g hg x ↦ by simp [hg.1 x, hg.2 x]) (hf.2.inter hf'.2)⟩
  neg_mem' {f} hf := ⟨fun h x ↦ by simp [hf.1 h x],
    Subgroup.isOpen_mono (H₁ := rightStabilizer f) (fun g hg x ↦ by simp [hg x]) hf.2⟩

variable {H}

/-- A function `f` in the coinduced module satisfies `f (h * x) = h • f x` for `h ∈ H`. -/
lemma coinductionCarrier_apply_mul {N : ContinuousGModule.{v, w} H}
    (f : coinductionCarrier H N) (h : H) (x : G) :
    (f : G → N.obj.obj.V) (h * x) = (N.obj.obj.ρ h).asHom.hom ((f : G → N.obj.obj.V) x) :=
  f.2.1 h x

/-- The right stabilizer of a function in the coinduced module is open. -/
lemma isOpen_rightStabilizer {N : ContinuousGModule.{v, w} H} (f : coinductionCarrier H N) :
    IsOpen (rightStabilizer (f : G → N.obj.obj.V) : Set G) :=
  f.2.2

/-- Right translation of a function in the coinduced module. -/
def coinductionTranslate {N : ContinuousGModule.{v, w} H} (g : G) (f : coinductionCarrier H N) :
    coinductionCarrier H N :=
  ⟨fun x ↦ (f : G → N.obj.obj.V) (x * g), fun h x ↦ by
      simp only [mul_assoc, coinductionCarrier_apply_mul],
    by
      have : (rightStabilizer (fun x ↦ (f : G → N.obj.obj.V) (x * g)) : Set G) =
          (fun y ↦ g⁻¹ * y * g) ⁻¹' (rightStabilizer (f : G → N.obj.obj.V) : Set G) := by
        ext y
        simp only [SetLike.mem_coe, Set.mem_preimage, mem_rightStabilizer]
        refine ⟨fun hy x ↦ ?_, fun hy x ↦ ?_⟩
        · have := hy (x * g⁻¹)
          simpa [mul_assoc] using this
        · have := hy (x * g)
          simpa [mul_assoc] using this
      rw [this]
      exact (isOpen_rightStabilizer f).preimage (by fun_prop)⟩

/-- The right translate of `f` by `g` takes the value `f (x * g)` at `x`. -/
@[simp]
lemma coinductionTranslate_apply {N : ContinuousGModule.{v, w} H} (g : G)
    (f : coinductionCarrier H N) (x : G) :
    (coinductionTranslate g f : G → N.obj.obj.V) x = (f : G → N.obj.obj.V) (x * g) := rfl

variable (H) in
/-- The action of `G` on the coinduced module by right translation. -/
def coinductionRepresentation (N : ContinuousGModule.{v, w} H) :
    Representation ℤ G (coinductionCarrier H N) where
  toFun g :=
    { toFun := coinductionTranslate g
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ by
    change (f : G → N.obj.obj.V) (x * 1) = (f : G → N.obj.obj.V) x
    rw [mul_one])
  map_mul' g g' := LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ by
    change (f : G → N.obj.obj.V) (x * (g * g')) = (f : G → N.obj.obj.V) (x * g * g')
    rw [mul_assoc])

/-- `(g • f) x = f (x * g)` in the coinduced module. -/
lemma coinductionRepresentation_apply {N : ContinuousGModule.{v, w} H} (g : G)
    (f : coinductionCarrier H N) (x : G) :
    (coinductionRepresentation H N g f : G → N.obj.obj.V) x = (f : G → N.obj.obj.V) (x * g) :=
  rfl

section

open scoped Stacks.DiscreteModuleTopology

/-- The action of `G` on the coinduced module by right translation is continuous for the discrete
topology. -/
lemma isContinuous_coinductionRepresentation (N : ContinuousGModule.{v, w} H) :
    (actionOfRepresentation ℤ G _ (coinductionRepresentation H N)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro f
  have : {g : G | coinductionRepresentation H N g f = f} =
      (rightStabilizer (f : G → N.obj.obj.V) : Set G) := by
    ext g
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_rightStabilizer]
    refine ⟨fun hg x ↦ congrFun (congrArg Subtype.val hg) x, fun hg ↦ Subtype.ext ?_⟩
    funext x
    exact hg x
  rw [this]
  exact isOpen_rightStabilizer f

end

/-- The coinduced module on objects. -/
def coinductionObj (N : ContinuousGModule.{v, max v w} H) : ContinuousGModule.{v, max v w} G :=
  ofRepresentation (coinductionRepresentation H N) (isContinuous_coinductionRepresentation N)

/-- Composition with a morphism of discrete `H`-modules, on coinduced modules. -/
def coinductionMapAddHom {N N' : ContinuousGModule.{v, w} H} (φ : N ⟶ N') :
    coinductionCarrier H N →+ coinductionCarrier H N' where
  toFun f := ⟨fun x ↦ φ.hom.hom.hom.hom ((f : G → N.obj.obj.V) x), fun h x ↦ by
      change φ.hom.hom.hom.hom ((f : G → N.obj.obj.V) (h * x)) = _
      rw [coinductionCarrier_apply_mul, hom_comm],
    Subgroup.isOpen_mono (H₁ := rightStabilizer (f : G → N.obj.obj.V))
      (fun g hg x ↦ by simp only [hg x]) (isOpen_rightStabilizer f)⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

/-- The image of `f` under composition with `φ` takes the value `φ (f x)` at `x`. -/
lemma coinductionMapAddHom_apply {N N' : ContinuousGModule.{v, w} H} (φ : N ⟶ N')
    (f : coinductionCarrier H N) (x : G) :
    (coinductionMapAddHom φ f : G → N'.obj.obj.V) x =
      φ.hom.hom.hom.hom ((f : G → N.obj.obj.V) x) := rfl

variable (H) in
/-- **Coinduction** from a subgroup `H` of a topological group `G`: the discrete `G`-module of
functions `f : G → N` with `f (h * x) = h • f x`, invariant under right translation by an open
subgroup, on which `G` acts by right translation. -/
def coinduction : ContinuousGModule.{v, max v w} H ⥤ ContinuousGModule.{v, max v w} G where
  obj := coinductionObj
  map φ := (gModuleHomEquiv G _ _).symm ⟨coinductionMapAddHom φ, fun _ _ ↦ rfl⟩
  map_id _ := hom_ext fun _ ↦ rfl
  map_comp _ _ := hom_ext fun _ ↦ rfl

/-- `G` acts on the coinduced module by right translation: `(g • f) x = f (x * g)`. -/
@[simp]
lemma coinduction_obj_ρ (N : ContinuousGModule.{v, max v w} H) (g : G)
    (f : coinductionCarrier H N) (x : G) :
    ((((coinduction H).obj N).obj.obj.ρ g).asHom.hom f : coinductionCarrier H N).1 x =
      (f : G → N.obj.obj.V) (x * g) := rfl

/-- Coinduction of a morphism `φ` sends `f` to the function `x ↦ φ (f x)`. -/
@[simp]
lemma coinduction_map_apply {N N' : ContinuousGModule.{v, max v w} H} (φ : N ⟶ N')
    (f : coinductionCarrier H N) (x : G) :
    (((coinduction H).map φ).hom.hom.hom.hom f : coinductionCarrier H N').1 x =
      φ.hom.hom.hom.hom ((f : G → N.obj.obj.V) x) := rfl

variable (G) in
/-- The stabilizer of an element of a discrete `G`-module, an open subgroup. -/
def elementStabilizer (M : ContinuousGModule.{v, w} G) (m : M.obj.obj.V) : Subgroup G where
  carrier := {g | (M.obj.obj.ρ g).asHom.hom m = m}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change (M.obj.obj.ρ (a * b)).asHom.hom m = m
    rw [ρ_mul_apply, show (M.obj.obj.ρ b).asHom.hom m = m from hb, ha]
  inv_mem' {a} ha := by
    change (M.obj.obj.ρ a⁻¹).asHom.hom m = m
    conv_lhs => rw [← show (M.obj.obj.ρ a).asHom.hom m = m from ha]
    exact ρ_inv_apply_ρ_apply M a m

/-- The function `x ↦ ψ (x • m)` attached to an `H`-equivariant map `ψ` out of a discrete
`G`-module and an element `m`, as an element of the coinduced module. -/
def coinductionLift {M : ContinuousGModule.{v, max v w} G} {N : ContinuousGModule.{v, max v w} H}
    (ψ : (restriction H.subtype continuous_subtype_val).obj M ⟶ N) (m : M.obj.obj.V) :
    coinductionCarrier H N :=
  ⟨fun x ↦ ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom m), fun h x ↦ by
      change ψ.hom.hom.hom.hom ((M.obj.obj.ρ (h * x)).asHom.hom m) = _
      rw [ρ_mul_apply]
      exact hom_comm ψ h _,
    Subgroup.isOpen_mono (H₁ := elementStabilizer G M m)
      (fun g hg x ↦ by
        change ψ.hom.hom.hom.hom ((M.obj.obj.ρ (x * g)).asHom.hom m) = _
        rw [ρ_mul_apply, show (M.obj.obj.ρ g).asHom.hom m = m from hg])
      (isOpen_stabilizer ℤ G M m)⟩

variable (H) in
/-- **Restriction from `G` to a subgroup `H` is left adjoint to coinduction.** -/
def restrictionCoinductionAdjunction :
    restriction.{v, v, max v w} H.subtype continuous_subtype_val ⊣ coinduction.{v, w} H :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun ψ := (gModuleHomEquiv G _ _).symm
            ⟨{ toFun m := coinductionLift ψ m
               map_zero' := Subtype.ext (funext fun x ↦ by
                 change ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom 0) = 0
                 rw [map_zero]
                 exact LinearMap.map_zero _)
               map_add' a b := Subtype.ext (funext fun x ↦ by
                 change ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom (a + b)) =
                   ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom a) +
                     ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom b)
                 rw [map_add]
                 exact LinearMap.map_add _ _ _) },
              fun g m ↦ Subtype.ext (funext fun x ↦ by
                change ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom ((M.obj.obj.ρ g).asHom.hom m)) =
                  ψ.hom.hom.hom.hom ((M.obj.obj.ρ (x * g)).asHom.hom m)
                rw [ρ_mul_apply])⟩
          invFun χ := (gModuleHomEquiv H _ _).symm
            ⟨{ toFun m := (χ.hom.hom.hom.hom m : coinductionCarrier H N).1 1
               map_zero' := by
                 change (χ.hom.hom.hom.hom 0 : coinductionCarrier H N).1 1 = 0
                 exact (congrArg (fun f : coinductionCarrier H N ↦ f.1 1)
                   (LinearMap.map_zero χ.hom.hom.hom.hom)).trans rfl
               map_add' a b := by
                 change (χ.hom.hom.hom.hom (a + b) : coinductionCarrier H N).1 1 =
                   (χ.hom.hom.hom.hom a : coinductionCarrier H N).1 1 +
                     (χ.hom.hom.hom.hom b : coinductionCarrier H N).1 1
                 exact (congrArg (fun f : coinductionCarrier H N ↦ f.1 1)
                   (LinearMap.map_add χ.hom.hom.hom.hom a b)).trans rfl },
              fun h m ↦ by
                change (χ.hom.hom.hom.hom ((M.obj.obj.ρ (h : G)).asHom.hom m) :
                  coinductionCarrier H N).1 1 =
                  (N.obj.obj.ρ h).asHom.hom ((χ.hom.hom.hom.hom m : coinductionCarrier H N).1 1)
                rw [hom_comm χ (h : G) m]
                change (χ.hom.hom.hom.hom m : coinductionCarrier H N).1 (1 * (h : G)) = _
                have := coinductionCarrier_apply_mul (χ.hom.hom.hom.hom m : coinductionCarrier H N)
                  h 1
                rw [mul_one] at this
                rw [one_mul]
                exact this⟩
          left_inv ψ := hom_ext fun m ↦ by
            change ψ.hom.hom.hom.hom ((M.obj.obj.ρ 1).asHom.hom m) = _
            exact congrArg ψ.hom.hom.hom.hom (ρ_one_apply M m)
          right_inv χ := by
            beta_reduce
            apply hom_ext
            intro m
            apply Subtype.ext
            funext x
            change (χ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom m) : coinductionCarrier H N).1 1 =
              (χ.hom.hom.hom.hom m : coinductionCarrier H N).1 x
            rw [hom_comm χ x m]
            change (χ.hom.hom.hom.hom m : coinductionCarrier H N).1 (1 * x) =
              (χ.hom.hom.hom.hom m : coinductionCarrier H N).1 x
            rw [one_mul] }
      homEquiv_naturality_left_symm _ _ := hom_ext fun _ ↦ rfl
      homEquiv_naturality_right _ _ := hom_ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl) }

/-- The adjoint of an `H`-equivariant map `ψ : M → N` sends `m` to the function
`x ↦ ψ (x • m)`. -/
lemma restrictionCoinductionAdjunction_homEquiv_apply {M : ContinuousGModule.{v, max v w} G}
    {N : ContinuousGModule.{v, max v w} H}
    (ψ : (restriction H.subtype continuous_subtype_val).obj M ⟶ N) (m : M.obj.obj.V) (x : G) :
    (((restrictionCoinductionAdjunction H).homEquiv M N ψ).hom.hom.hom.hom m :
      coinductionCarrier H N).1 x = ψ.hom.hom.hom.hom ((M.obj.obj.ρ x).asHom.hom m) := by
  simp only [restrictionCoinductionAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The unit of the adjunction sends `m` to the function `x ↦ x • m`. -/
lemma restrictionCoinductionAdjunction_unit_app_apply (M : ContinuousGModule.{v, max v w} G)
    (m : M.obj.obj.V) (x : G) :
    (((restrictionCoinductionAdjunction H).unit.app M).hom.hom.hom.hom m :
      coinductionCarrier H _).1 x = (M.obj.obj.ρ x).asHom.hom m := by
  rw [← Adjunction.homEquiv_id, restrictionCoinductionAdjunction_homEquiv_apply]
  rfl

/-- Coinduction is an additive functor. -/
instance : (coinduction.{v, w} H).Additive :=
  letI := restriction_additive.{v, v, max v w} H.subtype continuous_subtype_val
  (restrictionCoinductionAdjunction H).right_adjoint_additive

/-- Coinduction preserves finite limits. -/
instance : PreservesFiniteLimits (coinduction.{v, w} H) :=
  letI : PreservesLimitsOfSize (coinduction.{v, w} H) :=
    (restrictionCoinductionAdjunction H).rightAdjoint_preservesLimits
  inferInstance

/-- Coinduction sends injective objects to injective objects. -/
instance : (coinduction.{v, w} H).PreservesInjectiveObjects :=
  letI := restriction_preservesMonomorphisms.{v, v, max v w} H.subtype continuous_subtype_val
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (restrictionCoinductionAdjunction H)

/-- A function on a compact group invariant under right translation by an open subgroup takes
finitely many values. -/
theorem finite_range_of_forall_mul_eq [CompactSpace G] {X : Type*} {N₀ : Subgroup G}
    (hN₀ : IsOpen (N₀ : Set G)) {F : G → X} (hF : ∀ n ∈ N₀, ∀ x, F (x * n) = F x) :
    (Set.range F).Finite := by
  have := Subgroup.quotient_finite_of_isOpen N₀ hN₀
  refine (Set.finite_range (fun q : G ⧸ N₀ ↦ F q.out)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨n, hn, hxn⟩ : ∃ n ∈ N₀, (x : G ⧸ N₀).out = x * n :=
    ⟨x⁻¹ * (x : G ⧸ N₀).out, QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm, by group⟩
  exact ⟨x, (congrArg F hxn).trans (hF n hn x)⟩

omit [IsTopologicalGroup G] in
/-- An element of a discrete `H`-module is fixed by the elements of `H` lying in some open
neighbourhood of `1` in `G`. -/
theorem exists_isOpen_forall_ρ_apply_eq (N : ContinuousGModule.{v, w} H) (s : N.obj.obj.V) :
    ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ h : H, (h : G) ∈ O → (N.obj.obj.ρ h).asHom.hom s = s := by
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (isOpen_stabilizer ℤ H N s)
  refine ⟨O, hO, ?_, fun h hh ↦ ?_⟩
  · have : (1 : H) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      simp
    exact this
  · have : h ∈ Subtype.val ⁻¹' O := hh
    rw [hOeq] at this
    exact this

omit [IsTopologicalGroup G] in
/-- If `a * y * n = b * y * m` with `n, m` in a normal subgroup `T` of `G`, and `s` is fixed by
the elements of `H` lying in `T`, then `a` and `b` act on `s` in the same way. -/
theorem ρ_apply_eq_of_mul_eq {N : ContinuousGModule.{v, w} H} {T : Subgroup G} (hT : T.Normal)
    {s : N.obj.obj.V} (hs : ∀ k : H, (k : G) ∈ T → (N.obj.obj.ρ k).asHom.hom s = s) {a b : H}
    {y n m : G} (hn : n ∈ T) (hm : m ∈ T) (he : (a : G) * y * n = b * y * m) :
    (N.obj.obj.ρ b).asHom.hom s = (N.obj.obj.ρ a).asHom.hom s := by
  have hmem : ((a⁻¹ * b : H) : G) ∈ T := by
    have key : ((a⁻¹ * b : H) : G) = y * (n * m⁻¹) * y⁻¹ := by
      calc ((a⁻¹ * b : H) : G)
          = (a : G)⁻¹ * ((b : G) * y * m) * m⁻¹ * y⁻¹ := by
            push_cast
            group
        _ = (a : G)⁻¹ * ((a : G) * y * n) * m⁻¹ * y⁻¹ := by rw [he]
        _ = y * (n * m⁻¹) * y⁻¹ := by group
    rw [key]
    exact hT.conj_mem _ (T.mul_mem hn (T.inv_mem hm)) _
  calc (N.obj.obj.ρ b).asHom.hom s
      = (N.obj.obj.ρ (a * (a⁻¹ * b))).asHom.hom s := by rw [mul_inv_cancel_left]
    _ = (N.obj.obj.ρ a).asHom.hom ((N.obj.obj.ρ (a⁻¹ * b)).asHom.hom s) := ρ_mul_apply N _ _ _
    _ = (N.obj.obj.ρ a).asHom.hom s := by rw [hs _ hmem]

/-- The double cosets `S x T` of two subgroups of a group admit representatives `q x`, constant on
each double coset. -/
theorem exists_doubleCoset_rep {K : Type*} [Group K] (S T : Subgroup K) :
    ∃ q : K → K, (∀ x, ∃ h : S, ∃ n ∈ T, x = h * q x * n) ∧
      ∀ x (h : S), ∀ n ∈ T, q (h * x * n) = q x := by
  let r : Setoid K :=
    { r := fun x y ↦ ∃ h : S, ∃ n ∈ T, y = h * x * n
      iseqv :=
        { refl := fun x ↦ ⟨1, 1, T.one_mem, by simp⟩
          symm := fun {x y} ⟨h, n, hn, hxy⟩ ↦
            ⟨h⁻¹, n⁻¹, T.inv_mem hn, by
              rw [hxy, Subgroup.coe_inv]
              group⟩
          trans := fun {x y z} ⟨h, n, hn, hxy⟩ ⟨h', n', hn', hyz⟩ ↦
            ⟨h' * h, n * n', T.mul_mem hn hn', by simp [hyz, hxy, mul_assoc]⟩ } }
  let q : K → K := fun x ↦ (Quotient.mk r x).out
  have hqeq : ∀ x y, r x y → q x = q y := fun x y hxy ↦ by
    simp only [q, Quotient.sound hxy]
  exact ⟨q, fun x ↦ Quotient.mk_out (s := r) x,
    fun x h n hn ↦ (hqeq _ _ (show r x (h * x * n) from ⟨h, n, hn, rfl⟩)).symm⟩

section Profinite

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Over a profinite group, coinduction preserves surjections**: a surjection `N → N''` of
discrete `H`-modules induces a surjection of coinduced modules. -/
theorem surjective_coinduction_map {N N'' : ContinuousGModule.{v, max v w} H} (φ : N ⟶ N'')
    (hφ : Function.Surjective φ.hom.hom.hom.hom) :
    Function.Surjective ((coinduction H).map φ).hom.hom.hom.hom := by
  intro f''
  set F : G → N''.obj.obj.V := (f'' : coinductionCarrier H N'').1
  set π : N.obj.obj.V → N''.obj.obj.V := fun y ↦ φ.hom.hom.hom.hom y
  set lift : N''.obj.obj.V → N.obj.obj.V := Function.surjInv hφ
  have hlift : ∀ s, π (lift s) = s := Function.surjInv_eq hφ
  have : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.2
    (connectedComponent_eq_singleton (1 : G) ▸ isClosed_connectedComponent)
  obtain ⟨N₀, hN₀⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_rightStabilizer f'') (rightStabilizer F).one_mem
  have hfin : (Set.range F).Finite :=
    finite_range_of_forall_mul_eq N₀.isOpen' fun n hn x ↦ hN₀ hn x
  choose O hO h1O hOfix using fun s ↦ exists_isOpen_forall_ρ_apply_eq N (lift s)
  obtain ⟨N₁, hN₁⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((hfin.isOpen_biInter fun s _ ↦ hO s).inter N₀.isOpen')
    ⟨Set.mem_iInter₂.mpr fun s _ ↦ h1O s, N₀.toSubgroup.one_mem⟩
  have hN₁N₀ : ∀ n ∈ N₁.toSubgroup, n ∈ N₀.toSubgroup := fun n hn ↦ (hN₁ hn).2
  have hN₁O : ∀ n ∈ N₁.toSubgroup, ∀ x, n ∈ O (F x) := fun n hn x ↦
    Set.mem_iInter₂.mp (hN₁ hn).1 (F x) ⟨x, rfl⟩
  obtain ⟨q, hq, hqeq⟩ := exists_doubleCoset_rep H N₁.toSubgroup
  choose hx nx hnx hxq using hq
  have hwd : ∀ x (h : H), ∀ n ∈ N₁.toSubgroup, x = h * q x * n →
      (N.obj.obj.ρ (hx x)).asHom.hom (lift (F (q x))) =
        (N.obj.obj.ρ h).asHom.hom (lift (F (q x))) :=
    fun x _ _ hn hxe ↦ ρ_apply_eq_of_mul_eq N₁.isNormal'
      (fun k hk ↦ hOfix (F (q x)) k (hN₁O _ hk (q x))) hn (hnx x) (hxe.symm.trans (hxq x))
  let f : G → N.obj.obj.V := fun x ↦ (N.obj.obj.ρ (hx x)).asHom.hom (lift (F (q x)))
  have hf_mul : ∀ (h : H) x, f (h * x) = (N.obj.obj.ρ h).asHom.hom (f x) := by
    intro h x
    have hqx : q (h * x) = q x := by simpa using hqeq x h 1 N₁.toSubgroup.one_mem
    have := hwd (h * x) (h * hx x) (nx x) (hnx x) (by
      rw [hqx]
      push_cast
      rw [mul_assoc, mul_assoc, ← mul_assoc (hx x : G), ← hxq x])
    simp only [f, hqx] at this ⊢
    rw [this, ρ_mul_apply]
  have hf_right : ∀ x, ∀ n ∈ N₁.toSubgroup, f (x * n) = f x := by
    intro x n hn
    have hqx : q (x * n) = q x := by simpa using hqeq x 1 n hn
    have := hwd (x * n) (hx x) (nx x * n) (N₁.toSubgroup.mul_mem (hnx x) hn)
      (by rw [hqx, ← mul_assoc, ← hxq x])
    simpa only [f, hqx] using this
  refine ⟨⟨f, hf_mul, Subgroup.isOpen_mono (H₁ := N₁.toSubgroup)
    (fun n hn x ↦ hf_right x n hn) N₁.isOpen'⟩, Subtype.ext (funext fun x ↦ ?_)⟩
  change φ.hom.hom.hom.hom ((N.obj.obj.ρ (hx x)).asHom.hom (lift (F (q x)))) = F x
  rw [hom_comm φ]
  change (N''.obj.obj.ρ (hx x)).asHom.hom (π (lift (F (q x)))) = F x
  rw [hlift]
  have e1 : F (↑(hx x) * q x * nx x) = F (↑(hx x) * q x) := hN₀ (hN₁N₀ _ (hnx x)) _
  conv_rhs => rw [hxq x]
  rw [e1]
  exact (coinductionCarrier_apply_mul f'' (hx x) (q x)).symm

/-- Over a profinite group, coinduction preserves epimorphisms. -/
instance : (coinduction.{v, w} H).PreservesEpimorphisms where
  preserves {N N''} φ hφ := by
    rw [epi_iff_surjective] at hφ ⊢
    exact surjective_coinduction_map φ hφ

/-- Over a profinite group, coinduction preserves finite colimits. -/
instance : PreservesFiniteColimits (coinduction.{v, w} H) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun S hS ↦
    ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (coinduction H)).1
      inferInstance S hS).1, by
        have := hS.epi_g
        exact (coinduction H).map_epi S.g⟩

end Profinite

end Coinduction

end Stacks.GroupCohomology

end
