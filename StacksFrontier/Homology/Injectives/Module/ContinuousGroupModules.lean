module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Equivalence
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.Algebra.Module.CharacterModule.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import StacksCore.Tactic.StacksAttribute

/-!
# Functorial injective embeddings for continuous group modules

Let `G` be a topological group and `R` a ring. We consider Mathlib's category
of continuous actions on discrete `R`-modules.

## Main definitions

* `Stacks.Injectives.ContinuousModule`: the category of `R`-modules with a continuous
  `G`-action, each underlying module carrying the discrete topology. It is an abbreviation for
  Mathlib's `CategoryTheory.DiscreteContAction (ModuleCat R) G`.
* `Stacks.Injectives.continuousModuleUnderlying`: the functor sending such a module to the
  `R`-module underlying it, forgetting both the action and its continuity.

## Main results

* `Stacks.Injectives.continuousModule_hasFunctorialInjectiveEmbeddings`: that category has
  functorial injective embeddings.

Taking `R = ℤ` gives the source's category of discrete `G`-modules.

## Implementation notes

The category is expressed as Mathlib's `DiscreteContAction (ModuleCat R) G`, i.e. the full
subcategory of continuous actions whose underlying topology is discrete, rather than by
equipping modules with a topology by hand.

## References

* [Stacks Project, Tag 04JF](https://stacks.math.columbia.edu/tag/04JF)
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u v w

namespace Stacks.Injectives

private theorem moduleCat_hasFunctorialInjectiveEmbeddings
    (R : Type u) [Ring R] :
    HasFunctorialInjectiveEmbeddings (ModuleCat.{max u w} R) := by
  let uR : ModuleCat.{max u w} ℤ ⥤ ModuleCat.{max u w} R :=
    ModuleCat.coextendScalars.{0, u, max u w} (algebraMap ℤ R)
  let vR : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} ℤ :=
    ModuleCat.restrictScalars.{max u w} (algebraMap ℤ R)
  let adj : vR ⊣ uR :=
    ModuleCat.restrictCoextendScalarsAdj.{max u w, 0, u} (algebraMap ℤ R)
  let : uR.Additive := ⟨by
    intro X Y f g
    ext x
    rfl⟩
  apply hasFunctorialInjectiveEmbeddings_of_adjunction
      (ModuleCat.{max u w} ℤ) (ModuleCat.{max u w} R) uR vR adj
  · intro X Y f hf
    exact (ModuleCat.restrictScalars (algebraMap ℤ R)).map_mono f
  · intro X hX
    have h : Subsingleton (vR.obj X) := ModuleCat.isZero_iff_subsingleton.mp hX
    exact ModuleCat.isZero_iff_subsingleton.mpr (show Subsingleton X from h)
  · exact _root_.moduleCat_hasFunctorialInjectiveEmbeddings'.{0, max u w} (R := ℤ)

private def coindLinear (R : Type u) [Ring R] (G : Type (max u w)) [Group G]
    (M : ModuleCat.{max u w} R) (g : G) : (G → M) →ₗ[R] (G → M) where
  toFun f x := f (x * g)
  map_add' f₁ f₂ := by
    ext x
    rfl
  map_smul' r f := by
    ext x
    rfl

private def coindAction (R : Type u) [Ring R] (G : Type (max u w)) [Group G]
    (M : ModuleCat.{max u w} R) : Action (ModuleCat.{max u w} R) G where
  V := ModuleCat.of.{max u w} R (G → M)
  ρ := {
    toFun g := End.of (ModuleCat.ofHom (coindLinear R G M g))
    map_one' := by
      apply End.ext
      apply ModuleCat.hom_ext
      ext f x
      simp [coindLinear, End.one_asHom]
    map_mul' := by
      intro g h
      apply End.ext
      apply ModuleCat.hom_ext
      ext f x
      simp [coindLinear, mul_assoc, End.mul_asHom]
  }

private def coindFunctor (R : Type u) [Ring R] (G : Type (max u w)) [Group G] :
    ModuleCat.{max u w} R ⥤ Action (ModuleCat.{max u w} R) G where
  obj := coindAction R G
  map {M N} f := {
    hom := ModuleCat.ofHom {
      toFun := fun a g => f.hom (a g)
      map_add' := by
        intro a b
        funext g
        exact map_add f.hom (a g) (b g)
      map_smul' := by
        intro r a
        funext g
        exact map_smul f.hom r (a g)
    }
    comm := by
      intro g
      apply ModuleCat.hom_ext
      ext a
      rfl
  }
  map_id M := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext a
    rfl
  map_comp f g := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext a
    rfl

private def coindHomEquiv (R : Type u) [Ring R] (G : Type (max u w)) [Group G]
    (X : Action (ModuleCat.{max u w} R) G) (M : ModuleCat.{max u w} R) :
    ((Action.forget (ModuleCat.{max u w} R) G).obj X ⟶ M) ≃
      (X ⟶ (coindFunctor R G).obj M) where
  toFun f := {
    hom := ModuleCat.ofHom {
      toFun := fun x g => f.hom (((X.ρ g).asHom.hom) x)
      map_add' := by
        intro x y
        ext g
        rw [map_add ((X.ρ g).asHom.hom)]
        exact map_add f.hom _ _
      map_smul' := by
        intro r x
        ext g
        change f.hom ((X.ρ g).asHom.hom (r • x)) = _
        rw [map_smul ((X.ρ g).asHom.hom)]
        exact map_smul f.hom _ _
    }
    comm := by
      intro h
      apply ModuleCat.hom_ext
      ext x
      funext g
      change f.hom (((X.ρ g).asHom.hom) (((X.ρ h).asHom.hom) x)) =
        f.hom (((X.ρ (g * h)).asHom.hom) x)
      congr 1
      rw [X.ρ.map_mul g h, End.mul_asHom]
      rfl
  }
  invFun f := ModuleCat.ofHom {
    toFun := fun x => (f.hom.hom x) 1
    map_add' := by
      intro x y
      change (f.hom.hom (x + y)) 1 = _
      rw [map_add f.hom.hom x y]
      rfl
    map_smul' := by
      intro r x
      change (f.hom.hom (r • x)) 1 = _
      rw [map_smul f.hom.hom r x]
      rfl
  }
  left_inv f := by
    apply ModuleCat.hom_ext
    ext x
    change f.hom (((X.ρ 1).asHom.hom) x) = f.hom x
    simp
  right_inv f := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    funext g
    have h := congrArg (fun q => (ConcreteCategory.hom q) x) (f.comm g)
    change f.hom.hom (((X.ρ g).asHom.hom) x) =
      coindLinear R G M g (f.hom.hom x) at h
    have h' := congrArg (fun z : G → M => z 1) h
    change (f.hom.hom (((X.ρ g).asHom.hom) x)) 1 = (f.hom.hom x) g
    simpa [coindLinear] using h'

private def forgetCoindAdjunction (R : Type u) [Ring R] (G : Type (max u w)) [Group G] :
    Action.forget (ModuleCat.{max u w} R) G ⊣ coindFunctor R G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X M => coindHomEquiv R G X M
    homEquiv_naturality_left_symm := by
      intros
      apply ModuleCat.hom_ext
      ext x
      rfl
    homEquiv_naturality_right := by
      intros
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext x
      funext g
      rfl
  }

private theorem action_hasFunctorialInjectiveEmbeddings
    (R : Type u) [Ring R] (G : Type (max u w)) [Group G] :
    HasFunctorialInjectiveEmbeddings
      (Action (ModuleCat.{max u w} R) G) := by
  let U := Action.forget (ModuleCat.{max u w} R) G
  let C := coindFunctor R G
  let adj := forgetCoindAdjunction R G
  let : U.Additive := ⟨by intros; rfl⟩
  let : C.Additive := ⟨by
    intro X Y f g
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    funext h
    rfl⟩
  apply hasFunctorialInjectiveEmbeddings_of_adjunction
      (ModuleCat.{max u w} R) (Action (ModuleCat.{max u w} R) G) C U adj
  · intro X Y f hf
    exact U.map_mono f
  · intro X hX
    have hs : Subsingleton X.V := ModuleCat.isZero_iff_subsingleton.mp hX
    apply (Limits.IsZero.iff_id_eq_zero X).2
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    exact hs.elim x 0
  · exact moduleCat_hasFunctorialInjectiveEmbeddings.{u, w} R

section

variable (R : Type u) [Ring R] (G : Type (max u w)) [Group G] [TopologicalSpace G]

local instance : HasForget₂ (ModuleCat.{max u w} R) TopCat.{max u w} :=
  { forget₂ := forget (ModuleCat.{max u w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

local instance : HasForget₂ (Action (ModuleCat.{max u w} R) G) TopCat.{max u w} :=
  { forget₂ := Action.forget (ModuleCat.{max u w} R) G ⋙
      forget (ModuleCat.{max u w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

private instance action_discreteTopology (X : Action (ModuleCat.{max u w} R) G) :
    DiscreteTopology ((forget₂ (Action (ModuleCat.{max u w} R) G) TopCat).obj X) := ⟨rfl⟩

private instance action_nonempty (X : Action (ModuleCat.{max u w} R) G) :
    Nonempty ((forget₂ (Action (ModuleCat.{max u w} R) G) TopCat).obj X) := ⟨(0 : X.V)⟩

private abbrev continuousActionProperty
    (X : Action (ModuleCat.{max u w} R) G) : Prop :=
  Action.IsContinuous (V := ModuleCat.{max u w} R) (G := G) X

private lemma continuous_of_comp_injective_discrete
    {X Y : Type (w)} {Z : Type (w)}
    [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y]
    [TopologicalSpace Z] (f : X → Y) (hf : Function.Injective f) {g : Z → X}
    (h : Continuous (f ∘ g)) : Continuous g := by
  obtain ⟨s, hs⟩ := hf.hasLeftInverse
  convert (continuous_of_discreteTopology : Continuous s).comp h using 1
  ext z
  exact (hs _).symm

/-- A discrete action is continuous iff all its orbit maps are continuous. -/
private lemma isContinuous_iff_continuous_orbit (X : Action (ModuleCat.{max u w} R) G)
    [TopologicalSpace X.V] [DiscreteTopology X.V] :
    continuousActionProperty R G X ↔ ∀ x : X.V, Continuous fun g : G => (X.ρ g).asHom.hom x := by
  obtain rfl : ‹TopologicalSpace X.V› = ⊥ := DiscreteTopology.eq_bot
  exact ⟨fun h => continuous_prod_of_discrete_right.mp h.continuous_smul,
    fun h => ⟨continuous_prod_of_discrete_right.mpr h⟩⟩

/-- Orbit maps of a discrete action are carried to orbit maps by morphisms of actions. -/
private lemma continuous_orbit_map {X Y : Action (ModuleCat.{max u w} R) G}
    [TopologicalSpace X.V] [DiscreteTopology X.V] [TopologicalSpace Y.V] (f : X ⟶ Y) {x : X.V}
    (hx : Continuous fun g : G => (X.ρ g).asHom.hom x) :
    Continuous fun g : G => (Y.ρ g).asHom.hom (f.hom.hom x) :=
  ((continuous_of_discreteTopology : Continuous fun z : X.V => f.hom.hom z).comp hx).congr
    fun g => ConcreteCategory.congr_hom (f.comm g) x

private instance continuous_closedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (continuousActionProperty (R := R) (G := G)) where
  prop_of_mono {X Y} f _ hY := by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget _ G).map f))
    have hf := (ModuleCat.mono_iff_injective f.hom).mp inferInstance
    let : TopologicalSpace X.V := ⊥
    let : DiscreteTopology X.V := ⟨rfl⟩
    let : TopologicalSpace Y.V := ⊥
    let : DiscreteTopology Y.V := ⟨rfl⟩
    refine (isContinuous_iff_continuous_orbit R G X).2 fun x => ?_
    have h := (isContinuous_iff_continuous_orbit R G Y).1 hY (f.hom x)
    exact continuous_of_comp_injective_discrete (fun y => f.hom y) hf
      (h.congr fun g => (ConcreteCategory.congr_hom (f.comm g) x).symm)

private instance continuous_closedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (continuousActionProperty (R := R) (G := G)) where
  prop_of_epi {X Y} f _ hX := by
    have : Epi f.hom := inferInstanceAs (Epi ((Action.forget _ G).map f))
    have hf := (ModuleCat.epi_iff_surjective f.hom).mp inferInstance
    let : TopologicalSpace X.V := ⊥
    let : DiscreteTopology X.V := ⟨rfl⟩
    let : TopologicalSpace Y.V := ⊥
    let : DiscreteTopology Y.V := ⟨rfl⟩
    refine (isContinuous_iff_continuous_orbit R G Y).2 fun y => ?_
    obtain ⟨x, rfl⟩ := hf y
    exact continuous_orbit_map R G f ((isContinuous_iff_continuous_orbit R G X).1 hX x)

private instance continuous_closedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (continuousActionProperty (R := R) (G := G)) where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩
    let F := Action.forget (ModuleCat.{max u w} R) G
    have hi := Concrete.to_product_injective_of_isLimit _ (isLimitOfPreserves F p.isLimit)
    have hi' : Function.Injective (fun y : X.V => fun j => (p.π.app j).hom y) :=
      fun x y hxy => hi (funext fun j => congrFun hxy j)
    let : TopologicalSpace X.V := ⊥
    let : DiscreteTopology X.V := ⟨rfl⟩
    refine (isContinuous_iff_continuous_orbit R G X).2 fun x => ?_
    let D (j : Discrete J) :=
      (forget₂ (Action (ModuleCat.{max u w} R) G) TopCat).obj (p.diag.obj j)
    apply continuous_of_comp_injective_discrete
      (Y := ∀ j, D j)
      (fun y => fun j => (p.π.app j).hom y) hi'
    refine continuous_pi fun j => ?_
    let : TopologicalSpace (p.diag.obj j).V := ⊥
    let : DiscreteTopology (p.diag.obj j).V := ⟨rfl⟩
    have h := (isContinuous_iff_continuous_orbit R G (p.diag.obj j)).1 (p.prop_diag_obj j)
      ((p.π.app j).hom x)
    change Continuous (fun g => (p.π.app j).hom (((X.ρ g).asHom.hom) x))
    exact h.congr fun g => (ConcreteCategory.congr_hom ((p.π.app j).comm g) x).symm⟩

private instance continuous_containsZero :
    ObjectProperty.ContainsZero
      (continuousActionProperty (R := R) (G := G)) where
  exists_zero := by
    let Z := (0 : Action (ModuleCat.{max u w} R) G)
    refine ⟨Z, isZero_zero _, ?_⟩
    have hZ := (Action.forget (ModuleCat.{max u w} R) G).map_isZero (isZero_zero _)
    have hsub : Subsingleton Z.V := ModuleCat.isZero_iff_subsingleton.mp hZ
    refine ⟨(continuous_const
      (Y := (forget₂ (Action (ModuleCat.{max u w} R) G) TopCat).obj Z)
      (y := (0 : Z.V))).congr fun _ => hsub.elim _ _⟩

/-- Continuous actions on discrete modules form an abelian category: they are a full
subcategory of `Action (ModuleCat R) G`, which is abelian, closed under kernels, cokernels,
finite products and containing the zero object. -/
private noncomputable instance contActionAbelian :
    Abelian (ContAction (ModuleCat.{max u w} R) G) := by
  have h0 : ObjectProperty.ContainsZero
    (continuousActionProperty (R := R) (G := G)) := inferInstance
  have h1 : ObjectProperty.IsClosedUnderKernels
    (continuousActionProperty (R := R) (G := G)) := inferInstance
  have h2 : ObjectProperty.IsClosedUnderCokernels
    (continuousActionProperty (R := R) (G := G)) := inferInstance
  have h3 : ObjectProperty.IsClosedUnderFiniteProducts
    (continuousActionProperty (R := R) (G := G)) := inferInstance
  exact inferInstanceAs (Abelian (ObjectProperty.FullSubcategory
    (continuousActionProperty (R := R) (G := G))))

private instance discrete_closedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) where
  prop_of_mono _ _ _ := ⟨rfl⟩

private instance discrete_closedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) where
  prop_of_epi _ _ _ := ⟨rfl⟩

private instance discrete_closedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) where
  isClosedUnderLimitsOfShape _ _ := ⟨fun _ _ => ⟨rfl⟩⟩

private instance discrete_containsZero :
    ObjectProperty.ContainsZero
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) where
  exists_zero := ⟨0, isZero_zero _, ⟨rfl⟩⟩

private noncomputable instance continuousModuleAbelian :
    Abelian (DiscreteContAction (ModuleCat.{max u w} R) G) := by
  letI : ObjectProperty.ContainsZero
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) := inferInstance
  letI : ObjectProperty.IsClosedUnderKernels
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) := inferInstance
  letI : ObjectProperty.IsClosedUnderCokernels
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) := inferInstance
  letI : ObjectProperty.IsClosedUnderFiniteProducts
      (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) := inferInstance
  exact inferInstanceAs (Abelian (ObjectProperty.FullSubcategory
    (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G))))

section Smooth

variable [IsTopologicalGroup G]

local instance : HasForget₂ (ModuleCat.{max u w} R) TopCat.{max u w} :=
  { forget₂ := forget (ModuleCat.{max u w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

local instance : HasForget₂ (Action (ModuleCat.{max u w} R) G) TopCat.{max u w} :=
  { forget₂ := Action.forget (ModuleCat.{max u w} R) G ⋙
      forget (ModuleCat.{max u w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

private def smoothSubmodule (X : Action (ModuleCat.{max u w} R) G) : Submodule R X.V := by
  letI : TopologicalSpace X.V := ⊥
  letI : DiscreteTopology X.V := ⟨rfl⟩
  refine {
    toAddSubmonoid := {
      carrier := {x | Continuous (fun g : G => (X.ρ g).asHom.hom x)}
      add_mem' := ?_
      zero_mem' := ?_ }
    smul_mem' := ?_ }
  · intro x y hx hy
    have h : Continuous (fun g : G => (X.ρ g).asHom.hom x + (X.ρ g).asHom.hom y) :=
      (continuous_add.comp (hx.prodMk hy))
    simpa [map_add] using h
  · simpa using (continuous_const : Continuous (fun _ : G => (0 : X.V)))
  · intro r x hx
    have h : Continuous (fun z : X.V => r • z) := continuous_of_discreteTopology
    simpa [Function.comp_def, map_smul] using h.comp hx

private lemma smooth_shift (X : Action (ModuleCat.{max u w} R) G) (g : G)
    {x : X.V} (hx : x ∈ smoothSubmodule R G X) :
    ((X.ρ g).asHom.hom x) ∈ smoothSubmodule R G X := by
  let : TopologicalSpace X.V := ⊥
  let : DiscreteTopology X.V := ⟨rfl⟩
  have hmul : Continuous (fun h : G => h * g) := continuous_id.mul continuous_const
  have h := hx.comp hmul
  show Continuous (fun h : G => (X.ρ h).asHom.hom ((X.ρ g).asHom.hom x))
  convert h using 1
  funext h
  show ((X.ρ h).asHom.hom ((X.ρ g).asHom.hom x)) = (X.ρ (h * g)).asHom.hom x
  rw [X.ρ.map_mul h g, End.mul_asHom]
  rfl

private def smoothActionLinear (X : Action (ModuleCat.{max u w} R) G) (g : G) :
    smoothSubmodule R G X →ₗ[R] smoothSubmodule R G X where
  toFun x := ⟨(X.ρ g).asHom.hom x.1, smooth_shift R G X g x.2⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

private def smoothAction (X : Action (ModuleCat.{max u w} R) G) :
    Action (ModuleCat.{max u w} R) G where
  V := ModuleCat.of R (smoothSubmodule R G X)
  ρ := {
    toFun g := End.of (ModuleCat.ofHom (smoothActionLinear R G X g))
    map_one' := by
      apply End.ext
      apply ModuleCat.hom_ext
      ext x
      simp [smoothActionLinear, End.one_asHom]
    map_mul' := by
      intro g h
      apply End.ext
      apply ModuleCat.hom_ext
      ext x
      simp [smoothActionLinear, X.ρ.map_mul, End.mul_asHom]
  }

private lemma smoothAction_continuous (X : Action (ModuleCat.{max u w} R) G) :
    continuousActionProperty R G (smoothAction R G X) := by
  let : TopologicalSpace X.V := ⊥
  let : DiscreteTopology X.V := ⟨rfl⟩
  let : TopologicalSpace ((smoothAction R G X).V) := ⊥
  let : DiscreteTopology ((smoothAction R G X).V) := ⟨rfl⟩
  refine (isContinuous_iff_continuous_orbit R G _).2 fun x => ?_
  apply continuous_discrete_rng.2
  intro y
  have heq : ((fun g : G => ((smoothAction R G X).ρ g).asHom.hom x) ⁻¹' {y}) =
      ((fun g : G => (X.ρ g).asHom.hom x.1) ⁻¹' {y.1}) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    dsimp [smoothAction, smoothActionLinear]
    exact Subtype.ext_iff
  rw [heq]
  exact x.2.isOpen_preimage _ (isOpen_discrete _)

omit [IsTopologicalGroup G] in
private lemma smoothMap_preserves (X Y : Action (ModuleCat.{max u w} R) G)
    (f : X ⟶ Y) {x : X.V} (hx : x ∈ smoothSubmodule R G X) :
    f.hom.hom x ∈ smoothSubmodule R G Y := by
  let : TopologicalSpace X.V := ⊥
  let : DiscreteTopology X.V := ⟨rfl⟩
  let : TopologicalSpace Y.V := ⊥
  exact continuous_orbit_map R G f hx

private def smoothActionMap {X Y : Action (ModuleCat.{max u w} R) G} (f : X ⟶ Y) :
    smoothAction R G X ⟶ smoothAction R G Y where
  hom := ModuleCat.ofHom {
    toFun := fun x => ⟨f.hom.hom x.1, smoothMap_preserves R G X Y f x.2⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by intro r x; ext; simp
  }
  comm := by
    intro g
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change f.hom.hom ((X.ρ g).asHom.hom x.1) = (Y.ρ g).asHom.hom (f.hom.hom x.1)
    exact ConcreteCategory.congr_hom (f.comm g) x.1

private def smoothActionCore :
    Action (ModuleCat.{max u w} R) G ⥤ Action (ModuleCat.{max u w} R) G where
  obj := smoothAction R G
  map := smoothActionMap R G
  map_id X := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    rfl

private def smoothActionContFunctor :
    Action (ModuleCat.{max u w} R) G ⥤ ContAction (ModuleCat.{max u w} R) G :=
  ObjectProperty.lift (Action.IsContinuous (V := ModuleCat.{max u w} R) (G := G))
    (smoothActionCore R G) (smoothAction_continuous R G)

private def smoothActionFunctor :
    Action (ModuleCat.{max u w} R) G ⥤ DiscreteContAction (ModuleCat.{max u w} R) G :=
  ObjectProperty.lift (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G))
    (smoothActionContFunctor R G) (fun _ => ⟨rfl⟩)

private def continuousActionInclusion :
    DiscreteContAction (ModuleCat.{max u w} R) G ⥤ Action (ModuleCat.{max u w} R) G :=
  ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)) ⋙
    ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{max u w} R) (G := G))

omit [IsTopologicalGroup G] in
private lemma continuousImage_smooth (Y : DiscreteContAction (ModuleCat.{max u w} R) G)
    (X : Action (ModuleCat.{max u w} R) G)
    (f : (continuousActionInclusion R G).obj Y ⟶ X) (y : Y.obj.obj.V) :
    f.hom.hom y ∈ smoothSubmodule R G X := by
  let : TopologicalSpace ((continuousActionInclusion R G).obj Y).V := ⊥
  let : DiscreteTopology ((continuousActionInclusion R G).obj Y).V := ⟨rfl⟩
  let : TopologicalSpace X.V := ⊥
  let : DiscreteTopology X.V := ⟨rfl⟩
  have hY : continuousActionProperty R G ((continuousActionInclusion R G).obj Y) :=
    Y.obj.property
  exact continuous_orbit_map R G f ((isContinuous_iff_continuous_orbit R G _).1 hY y)

private def liftSmoothHom (Y : DiscreteContAction (ModuleCat.{max u w} R) G)
    (X : Action (ModuleCat.{max u w} R) G)
    (f : (continuousActionInclusion R G).obj Y ⟶ X) :
    (continuousActionInclusion R G).obj Y ⟶ smoothAction R G X where
  hom := ModuleCat.ofHom {
    toFun := fun y => ⟨f.hom.hom y, continuousImage_smooth R G Y X f y⟩
    map_add' := by intro x y; ext; simp
    map_smul' := by intro r x; ext; simp
  }
  comm := by
    intro g
    apply ModuleCat.hom_ext
    ext y
    apply Subtype.ext
    change f.hom.hom ((Y.obj.obj.ρ g).asHom.hom y) = (X.ρ g).asHom.hom (f.hom.hom y)
    exact ConcreteCategory.congr_hom (f.comm g) y

private def smoothSubactionι (X : Action (ModuleCat.{max u w} R) G) :
    smoothAction R G X ⟶ X where
  hom := ModuleCat.ofHom {
    toFun := fun x => x.1
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl
  }
  comm := by
    intro g
    apply ModuleCat.hom_ext
    ext x
    rfl

private def smoothHomEquiv (Y : DiscreteContAction (ModuleCat.{max u w} R) G)
    (X : Action (ModuleCat.{max u w} R) G) :
    ((continuousActionInclusion R G).obj Y ⟶ X) ≃
      (Y ⟶ (smoothActionFunctor R G).obj X) where
  toFun f := ObjectProperty.homMk (ObjectProperty.homMk (liftSmoothHom R G Y X f))
  invFun f := (continuousActionInclusion R G).map f ≫ smoothSubactionι R G X
  left_inv f := by
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext y
    rfl
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext y
    apply Subtype.ext
    rfl

private def smoothAdjunction :
    continuousActionInclusion R G ⊣ smoothActionFunctor R G :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun Y X => smoothHomEquiv R G Y X
    homEquiv_naturality_left_symm := by
      intros
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext y
      rfl
    homEquiv_naturality_right := by
      intros
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext y
      apply Subtype.ext
      rfl
  }

end Smooth

end

/-- The category of `R`-modules with a continuous action of `G`, with the
underlying modules carrying the discrete topology. -/
abbrev ContinuousModule (R : Type u) [Ring R]
    (G : Type v) [Group G] [TopologicalSpace G] :=
    let _ : HasForget₂ (ModuleCat.{w} R) TopCat.{w} :=
    { forget₂ := forget (ModuleCat.{w} R) ⋙ TopCat.discrete
      forget_comp := rfl }
  DiscreteContAction (ModuleCat.{w} R) G

/-- The underlying `R`-module of a continuous discrete `R`-`G`-module, obtained by forgetting
the continuity of the action, then the discreteness of the module, then the action itself. -/
abbrev continuousModuleUnderlying (R : Type u) [Ring R]
    (G : Type v) [Group G] [TopologicalSpace G] :
    ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget (ModuleCat.{w} R) G

private theorem continuousModule_hasFunctorialInjectiveEmbeddings_sameUniverse
    (R : Type u) [Ring R]
    (G : Type (max u w)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    HasFunctorialInjectiveEmbeddings (ContinuousModule.{u, max u w, max u w} R G) := by
  let : HasForget₂ (ModuleCat.{max u w} R) TopCat.{max u w} :=
    { forget₂ := forget (ModuleCat.{max u w} R) ⋙ TopCat.discrete
      forget_comp := rfl }
  let A := Action (ModuleCat.{max u w} R) G
  let B := ContinuousModule.{u, max u w, max u w} R G
  let : Abelian B := inferInstance
  let : Preadditive (ContAction (ModuleCat.{max u w} R) G) := Abelian.toPreadditive
  let : Preadditive B := Abelian.toPreadditive
  let i := smoothActionFunctor R G
  let u := continuousActionInclusion R G
  let adj := smoothAdjunction R G
  let : (smoothActionCore R G).Additive := ⟨by
    intro X Y f g
    let : (Action.forget (ModuleCat.{max u w} R) G).Additive := ⟨by intros; rfl⟩
    have hfg : (f + g).hom = f.hom + g.hom := by
      show (Action.forget (ModuleCat.{max u w} R) G).map (f + g) =
        (Action.forget (ModuleCat.{max u w} R) G).map f +
          (Action.forget (ModuleCat.{max u w} R) G).map g
      exact (Action.forget (ModuleCat.{max u w} R) G).map_add
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    have hfgx := congrArg (fun h : X.V ⟶ Y.V => h x.1) hfg
    dsimp [smoothActionCore, smoothActionMap]
    show (f + g).hom.hom x.1 = f.hom.hom x.1 + g.hom.hom x.1
    exact hfgx⟩
  let : (smoothActionContFunctor R G).Additive := ⟨by
    intro X Y f g
    apply ObjectProperty.hom_ext
    show (smoothActionCore R G).map (f + g) =
      (smoothActionCore R G).map f + (smoothActionCore R G).map g
    exact (smoothActionCore R G).map_add (f := f) (g := g)⟩
  let : i.Additive := ⟨by
    intro X Y f g
    apply ObjectProperty.hom_ext
    show (smoothActionContFunctor R G).map (f + g) =
      (smoothActionContFunctor R G).map f + (smoothActionContFunctor R G).map g
    exact (smoothActionContFunctor R G).map_add (f := f) (g := g)⟩
  let : u.Additive := by
    let P : ObjectProperty (ContAction (ModuleCat.{max u w} R) G) :=
      ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)
    let Q : ObjectProperty (Action (ModuleCat.{max u w} R) G) :=
      Action.IsContinuous (V := ModuleCat.{max u w} R) (G := G)
    let : P.ι.Additive := inferInstance
    let : Q.ι.Additive := inferInstance
    exact ⟨by
      intro X Y f g
      dsimp [u, continuousActionInclusion]
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      ext x
      rfl⟩
  let hA := action_hasFunctorialInjectiveEmbeddings R G
  let : EnoughInjectives A :=
    enoughInjectives_of_hasFunctorialInjectiveEmbeddings (𝒜 := A) hA
  apply hasFunctorialInjectiveEmbeddings_of_adjunction A B i u adj
  · intro X Y f hf
    let : Mono f := hf
    let P : ObjectProperty (ContAction (ModuleCat.{max u w} R) G) :=
      ContAction.IsDiscrete (V := ModuleCat.{max u w} R) (G := G)
    let Q : ObjectProperty (Action (ModuleCat.{max u w} R) G) :=
      Action.IsContinuous (V := ModuleCat.{max u w} R) (G := G)
    let : IsNormalEpiCategory (ContAction (ModuleCat.{max u w} R) G) :=
      Abelian.toIsNormalEpiCategory
    let : IsNormalEpiCategory (Action (ModuleCat.{max u w} R) G) :=
      Abelian.toIsNormalEpiCategory
    let : P.ι.PreservesMonomorphisms := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    let : Q.ι.PreservesMonomorphisms := Q.preservesMonomorphisms_ι_of_isNormalEpiCategory
    let : (P.ι ⋙ Q.ι).PreservesMonomorphisms := inferInstance
    show Mono ((P.ι ⋙ Q.ι).map f)
    exact @Functor.PreservesMonomorphisms.preserves _ _ _ _
      (P.ι ⋙ Q.ι) (inferInstance) X Y f hf
  · intro X hX
    have hsub : Subsingleton (u.obj X).V := ModuleCat.isZero_iff_subsingleton.mp
      ((Action.forget (ModuleCat.{max u w} R) G).map_isZero hX)
    apply (Limits.IsZero.iff_id_eq_zero X).2
    apply ObjectProperty.hom_ext (P := ContAction.IsDiscrete
      (V := ModuleCat.{max u w} R) (G := G))
    apply ObjectProperty.hom_ext (P := Action.IsContinuous
      (V := ModuleCat.{max u w} R) (G := G))
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    ext x
    exact hsub.elim _ _
  · exact hA

/-- **Stacks Project, Tag 04JF.** The category of `R`-modules with continuous
`G`-action has functorial injective embeddings. In particular, taking
`R = ℤ` gives this result for discrete `G`-modules. -/
@[stacks 04JF]
theorem continuousModule_hasFunctorialInjectiveEmbeddings
    (R : Type u) [Ring R]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    HasFunctorialInjectiveEmbeddings (ContinuousModule.{u, v, max u v w} R G) := by
  let H := ULift.{max u v w, v} G
  let hLift : G ≃ₜ* H :=
    ContinuousMulEquiv.mk' (Homeomorph.ulift (X := G)).symm
      fun _ _ => rfl
  let hH : HasFunctorialInjectiveEmbeddings
      (ContinuousModule.{u, max u v w, max u v w} R H) :=
    continuousModule_hasFunctorialInjectiveEmbeddings_sameUniverse.{u, max v w} R H
  let : HasForget₂ (ModuleCat.{max u v w} R) TopCat.{max u v w} :=
    { forget₂ := forget (ModuleCat.{max u v w} R) ⋙ TopCat.discrete
      forget_comp := rfl }
  let Econt : ContAction.{max u v w, max ((max u v w) + 1) u,
      max u v w, max u v w, max u v w} (ModuleCat.{max u v w} R) H ≌
      ContAction.{max u v w, max ((max u v w) + 1) u,
        max u v w, max u v w, v} (ModuleCat.{max u v w} R) G :=
    ContAction.resEquiv (ModuleCat.{max u v w} R) hLift
  let P : ObjectProperty (ContAction.{max u v w, max ((max u v w) + 1) u,
      max u v w, max u v w, max u v w} (ModuleCat.{max u v w} R) H) :=
    ContAction.IsDiscrete (V := ModuleCat.{max u v w} R) (G := H)
  let Q : ObjectProperty (ContAction.{max u v w, max ((max u v w) + 1) u,
      max u v w, max u v w, v} (ModuleCat.{max u v w} R) G) :=
    ContAction.IsDiscrete (V := ModuleCat.{max u v w} R) (G := G)
  have hP : P = ⊤ := by
    ext
    exact ⟨fun _ => trivial, fun _ => ⟨rfl⟩⟩
  have hQ : Q = ⊤ := by
    ext
    exact ⟨fun _ => trivial, fun _ => ⟨rfl⟩⟩
  let : Q.IsClosedUnderIsomorphisms := by rw [hQ]; infer_instance
  have hPQ : Q.inverseImage Econt.functor = P := by
    rw [hQ, hP]
    ext X
    trivial
  let Edisc : ContinuousModule.{u, max u v w, max u v w} R H ≌
      ContinuousModule.{u, v, max u v w} R G :=
    Econt.congrFullSubcategory hPQ
  let : Abelian (ContinuousModule.{u, max u v w, max u v w} R H) :=
    continuousModuleAbelian.{u, max v w} R H
  let : Preadditive (ContinuousModule.{u, v, max u v w} R G) :=
    Preadditive.ofFullyFaithful Edisc.symm.fullyFaithfulFunctor
  let : Edisc.symm.functor.Additive := Edisc.symm.fullyFaithfulFunctor.additive_ofFullyFaithful
  let : HasFiniteProducts (ContinuousModule.{u, v, max u v w} R G) :=
    ⟨fun n => Adjunction.hasLimitsOfShape_of_equivalence Edisc.symm.functor⟩
  let : Abelian (ContinuousModule.{u, v, max u v w} R G) :=
    abelianOfEquivalence Edisc.symm.functor
  let : Edisc.functor.Additive := Edisc.symm.additive_inverse_of_FullyFaithful
  exact hasFunctorialInjectiveEmbeddings_of_equivalence Edisc hH
end Stacks.Injectives
