module

public import StacksFrontier.Algebra.Module.CharacterModule.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian

/-!
# Pontryagin duality for finite modules with a continuous action

Let `R` be a finite ring, not necessarily commutative, and `G` a topological group. For a finite
left `R`-module `M` with a continuous action of `G` its character module `M^∨ = Hom_ℤ(M, ℚ/ℤ)` is a
finite left `Rᵐᵒᵖ`-module (a right `R`-module) and carries the contragredient action
`(g • c)(m) = c(g⁻¹ • m)`, again continuous. Dually the character module of a finite
`Rᵐᵒᵖ`-module with continuous action is a finite `R`-module with continuous action. Evaluation
`M → (M^∨)^∨` is an isomorphism (Pontryagin duality for finite groups,
`CharacterModule.evalEquiv`), so `M ↦ M^∨` is an anti-equivalence between finite `R`-modules and
finite `Rᵐᵒᵖ`-modules with continuous `G`-action. In particular it is exact.

This is the "trivial duality" of the source (Section 03VI): it exchanges discrete and compact
modules, and the homology of a profinite group with finite coefficients is the dual of its
cohomology with dual coefficients. The source's coefficient ring is a finite ring, possibly
noncommutative, whose modules are left modules ([Stacks, Section 03SZ]); the dual of a left
module is a right module, which is why the dual lands in `Rᵐᵒᵖ`-modules.

## Main definitions

* `Stacks.GroupCohomology.characterRepresentation`,
  `Stacks.GroupCohomology.characterRepresentationOfMulOpposite` — the contragredient
  representations on characters.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleDual` — `M ↦ M^∨`, a functor
  `(FiniteTypeContinuousModule R G)ᵒᵖ ⥤ FiniteTypeContinuousModule Rᵐᵒᵖ G`.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleDualOfMulOpposite` — `N ↦ N^∨`, a functor
  `(FiniteTypeContinuousModule Rᵐᵒᵖ G)ᵒᵖ ⥤ FiniteTypeContinuousModule R G`.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleEvalIso` — `M ≅ (M^∨)^∨`, and
  `Stacks.GroupCohomology.finiteTypeContinuousModuleEvalOfMulOppositeIso` — `N ≅ (N^∨)^∨`.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleDualEquivalence` — the anti-equivalence.

## Main results

* `Stacks.GroupCohomology.preservesFiniteLimits_finiteTypeContinuousModuleDual`,
  `Stacks.GroupCohomology.preservesFiniteColimits_finiteTypeContinuousModuleDual`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Stacks.DiscreteModuleTopology CharacterModule.MulOppositeAction

universe u v w

namespace Stacks.GroupCohomology

section Representation

variable {R : Type u} [Ring R] {G : Type v} [Group G] {M : Type w} [AddCommGroup M]

/-- **The contragredient representation on the characters of a left `R`-module**:
`(g • c)(m) = c(g⁻¹ • m)`, a representation over `Rᵐᵒᵖ`. -/
def characterRepresentation [Module R M] (ρ : Representation R G M) :
    Representation Rᵐᵒᵖ G (CharacterModule M) where
  toFun g := CharacterModule.dualMulOpposite (ρ g⁻¹)
  map_one' := LinearMap.ext fun c ↦ DFunLike.ext _ _ fun m ↦ by
    change c (ρ 1⁻¹ m) = c m
    rw [inv_one, map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun c ↦ DFunLike.ext _ _ fun m ↦ by
    change c (ρ (g * h)⁻¹ m) = c (ρ h⁻¹ (ρ g⁻¹ m))
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]

/-- The contragredient representation sends a character `c` to `m ↦ c(g⁻¹ • m)`. -/
lemma characterRepresentation_apply [Module R M] (ρ : Representation R G M) (g : G)
    (c : CharacterModule M) (m : M) : characterRepresentation ρ g c m = c (ρ g⁻¹ m) :=
  rfl

/-- **The contragredient representation on the characters of a left `Rᵐᵒᵖ`-module**:
`(g • c)(m) = c(g⁻¹ • m)`, a representation over `R`. -/
def characterRepresentationOfMulOpposite [Module Rᵐᵒᵖ M] (ρ : Representation Rᵐᵒᵖ G M) :
    Representation R G (CharacterModule M) where
  toFun g := CharacterModule.dualOfMulOpposite (ρ g⁻¹)
  map_one' := LinearMap.ext fun c ↦ DFunLike.ext _ _ fun m ↦ by
    change c (ρ 1⁻¹ m) = c m
    rw [inv_one, map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun c ↦ DFunLike.ext _ _ fun m ↦ by
    change c (ρ (g * h)⁻¹ m) = c (ρ h⁻¹ (ρ g⁻¹ m))
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]

/-- The contragredient representation sends a character `c` to `m ↦ c(g⁻¹ • m)`. -/
lemma characterRepresentationOfMulOpposite_apply [Module Rᵐᵒᵖ M] (ρ : Representation Rᵐᵒᵖ G M)
    (g : G) (c : CharacterModule M) (m : M) :
    characterRepresentationOfMulOpposite ρ g c m = c (ρ g⁻¹ m) :=
  rfl

/-- The dual of an equivariant map is equivariant for the contragredient actions. -/
lemma dual_characterRepresentation [Module R M] {N : Type*} [AddCommGroup N] [Module R N]
    (ρ : Representation R G M) (σ : Representation R G N) (f : M →ₗ[R] N)
    (hf : ∀ g m, f (ρ g m) = σ g (f m)) (g : G) (c : CharacterModule N) :
    CharacterModule.dualMulOpposite f (characterRepresentation σ g c) =
      characterRepresentation ρ g (CharacterModule.dualMulOpposite f c) :=
  DFunLike.ext _ _ fun m ↦ by
    show c (σ g⁻¹ (f m)) = c (f (ρ g⁻¹ m))
    rw [hf]

/-- The dual of an equivariant map is equivariant for the contragredient actions. -/
lemma dual_characterRepresentationOfMulOpposite [Module Rᵐᵒᵖ M] {N : Type*} [AddCommGroup N]
    [Module Rᵐᵒᵖ N] (ρ : Representation Rᵐᵒᵖ G M) (σ : Representation Rᵐᵒᵖ G N)
    (f : M →ₗ[Rᵐᵒᵖ] N) (hf : ∀ g m, f (ρ g m) = σ g (f m)) (g : G) (c : CharacterModule N) :
    CharacterModule.dualOfMulOpposite f (characterRepresentationOfMulOpposite σ g c) =
      characterRepresentationOfMulOpposite ρ g (CharacterModule.dualOfMulOpposite f c) :=
  DFunLike.ext _ _ fun m ↦ by
    show c (σ g⁻¹ (f m)) = c (f (ρ g⁻¹ m))
    rw [hf]

/-- Evaluation into the double character module is equivariant. -/
lemma evalMulOpposite_characterRepresentation [Module R M] (ρ : Representation R G M) (g : G)
    (m : M) :
    CharacterModule.evalMulOpposite R M (ρ g m) =
      characterRepresentationOfMulOpposite (characterRepresentation ρ) g
        (CharacterModule.evalMulOpposite R M m) :=
  DFunLike.ext _ _ fun c ↦ by
    show c (ρ g m) = c (ρ g⁻¹⁻¹ m)
    rw [inv_inv]

/-- Evaluation into the double character module is equivariant. -/
lemma evalOfMulOpposite_characterRepresentation [Module Rᵐᵒᵖ M] (ρ : Representation Rᵐᵒᵖ G M)
    (g : G) (m : M) :
    CharacterModule.evalOfMulOpposite R M (ρ g m) =
      characterRepresentation (characterRepresentationOfMulOpposite ρ) g
        (CharacterModule.evalOfMulOpposite R M m) :=
  DFunLike.ext _ _ fun c ↦ by
    show c (ρ g m) = c (ρ g⁻¹⁻¹ m)
    rw [inv_inv]

end Representation

/-- An open subgroup acting trivially on `M` acts trivially on the characters of `M`, for any
action on characters of the form `c ↦ c ∘ ρ(g⁻¹)`. -/
lemma isOpen_stabilizer_character {G : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type w}
    [AddCommGroup M] (τ : G → CharacterModule M → CharacterModule M)
    (hτ1 : ∀ c, τ 1 c = c) (hτmul : ∀ a b c, τ (a * b) c = τ a (τ b c)) (H : Subgroup G)
    (hHopen : IsOpen (H : Set G)) (hH : ∀ g ∈ H, ∀ c, τ g c = c) (c : CharacterModule M) :
    IsOpen {g : G | τ g c = c} := by
  let S : Subgroup G :=
    { carrier := {g | τ g c = c}
      one_mem' := hτ1 c
      mul_mem' := fun {a b} ha hb ↦ by
        show τ (a * b) c = c
        change τ a c = c at ha
        change τ b c = c at hb
        rw [hτmul, hb, ha]
      inv_mem' := fun {a} ha ↦ by
        change τ a c = c at ha
        show τ a⁻¹ c = c
        conv_lhs => rw [← ha]
        rw [← hτmul, inv_mul_cancel, hτ1] }
  exact Subgroup.isOpen_mono (show H ≤ S from fun g hg ↦ hH g hg c) hHopen

section Functors

variable (R : Type u) [Ring R] [Finite R] (G : Type v) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The opposite of a finite ring is finite. -/
instance : Finite Rᵐᵒᵖ := Finite.of_equiv R MulOpposite.opEquiv

omit [Finite R] in
/-- The opposite of a finite ring is finite, with the same number of elements. -/
instance fintypeMulOpposite [Fintype R] : Fintype Rᵐᵒᵖ := Fintype.ofEquiv R MulOpposite.opEquiv

omit [Finite R] in
/-- The contragredient action on the characters of a finite `R`-module with a continuous action
is continuous: an open subgroup acting trivially on the module acts trivially on its
characters. -/
theorem isContinuous_characterRepresentation (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    (actionOfRepresentation Rᵐᵒᵖ G _
      (characterRepresentation (finiteTypeContinuousModuleRepresentation R G M))).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro c
  obtain ⟨H, -, hHopen, hH⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType R G M
  refine isOpen_stabilizer_character
    (fun g ↦ characterRepresentation (finiteTypeContinuousModuleRepresentation R G M) g)
    (fun c ↦ by simp) (fun a b c ↦ by simp) H hHopen (fun g hg c ↦ ?_) c
  refine DFunLike.ext _ _ fun m ↦ ?_
  rw [characterRepresentation_apply, finiteTypeContinuousModuleRepresentation_apply,
    hH g⁻¹ (H.inv_mem hg)]
  rfl

omit [Finite R] in
/-- The contragredient action on the characters of a finite `Rᵐᵒᵖ`-module with a continuous
action is continuous. -/
theorem isContinuous_characterRepresentationOfMulOpposite
    (N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G) :
    (actionOfRepresentation R G _ (characterRepresentationOfMulOpposite
      (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N))).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro c
  obtain ⟨H, -, hHopen, hH⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Rᵐᵒᵖ G N
  refine isOpen_stabilizer_character
    (fun g ↦ characterRepresentationOfMulOpposite
      (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N) g)
    (fun c ↦ by simp) (fun a b c ↦ by simp) H hHopen (fun g hg c ↦ ?_) c
  refine DFunLike.ext _ _ fun m ↦ ?_
  rw [characterRepresentationOfMulOpposite_apply, finiteTypeContinuousModuleRepresentation_apply,
    hH g⁻¹ (H.inv_mem hg)]
  rfl

/-- The character module of a finite `R`-module with a continuous `G`-action, a finite
`Rᵐᵒᵖ`-module with the contragredient action. -/
def finiteTypeContinuousModuleDualObj (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G :=
  ⟨ofRepresentation (characterRepresentation (finiteTypeContinuousModuleRepresentation R G M))
      (isContinuous_characterRepresentation R G M), by
    have : Module.Finite R M.obj.obj.obj.V := M.property
    have : Finite M.obj.obj.obj.V := Module.finite_of_finite R
    change Module.Finite Rᵐᵒᵖ (CharacterModule M.obj.obj.obj.V)
    exact Module.Finite.of_finite⟩

/-- The underlying module of the dual of `M` is the character module of `M`. -/
lemma finiteTypeContinuousModuleDualObj_V (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    (finiteTypeContinuousModuleDualObj R G M).obj.obj.obj.V =
      ModuleCat.of Rᵐᵒᵖ (CharacterModule M.obj.obj.obj.V) :=
  rfl

/-- The action of `g` on the dual of `M` is the contragredient action
`characterRepresentation`. -/
lemma finiteTypeContinuousModuleDualObj_ρ_hom (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (g : G) :
    ((finiteTypeContinuousModuleDualObj R G M).obj.obj.obj.ρ g).asHom.hom =
      characterRepresentation (finiteTypeContinuousModuleRepresentation R G M) g :=
  rfl

/-- The character module of a finite `Rᵐᵒᵖ`-module with a continuous `G`-action, a finite
`R`-module with the contragredient action. -/
def finiteTypeContinuousModuleDualOfMulOppositeObj
    (N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G) :
    FiniteTypeContinuousModule.{u, v, w} R G :=
  ⟨ofRepresentation (characterRepresentationOfMulOpposite
      (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N))
      (isContinuous_characterRepresentationOfMulOpposite R G N), by
    have : Module.Finite Rᵐᵒᵖ N.obj.obj.obj.V := N.property
    have : Finite N.obj.obj.obj.V := Module.finite_of_finite Rᵐᵒᵖ
    change Module.Finite R (CharacterModule N.obj.obj.obj.V)
    exact Module.Finite.of_finite⟩

/-- The underlying module of the dual of `N` is the character module of `N`. -/
lemma finiteTypeContinuousModuleDualOfMulOppositeObj_V
    (N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G) :
    (finiteTypeContinuousModuleDualOfMulOppositeObj R G N).obj.obj.obj.V =
      ModuleCat.of R (CharacterModule N.obj.obj.obj.V) :=
  rfl

variable {R G} in
/-- The dual of an equivariant map of `R`-modules, `c ↦ c ∘ f`. -/
def finiteTypeContinuousModuleDualMap {M N : FiniteTypeContinuousModule.{u, v, w} R G}
    (f : M ⟶ N) :
    finiteTypeContinuousModuleDualObj R G N ⟶ finiteTypeContinuousModuleDualObj R G M :=
  ObjectProperty.homMk ((homEquiv Rᵐᵒᵖ G _ _).symm
    ⟨CharacterModule.dualMulOpposite f.hom.hom.hom.hom.hom, fun g c ↦
      dual_characterRepresentation _ _ _ (fun g m ↦ finiteTypeContinuousModule_hom_comm f g m) g c⟩)

/-- The underlying linear map of the dual of `f` is `c ↦ c ∘ f`. -/
lemma finiteTypeContinuousModuleDualMap_hom {M N : FiniteTypeContinuousModule.{u, v, w} R G}
    (f : M ⟶ N) :
    (finiteTypeContinuousModuleDualMap f).hom.hom.hom.hom.hom =
      CharacterModule.dualMulOpposite f.hom.hom.hom.hom.hom :=
  rfl

variable {R G} in
/-- The dual of an equivariant map of `Rᵐᵒᵖ`-modules, `c ↦ c ∘ f`. -/
def finiteTypeContinuousModuleDualOfMulOppositeMap
    {M N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G} (f : M ⟶ N) :
    finiteTypeContinuousModuleDualOfMulOppositeObj R G N ⟶
      finiteTypeContinuousModuleDualOfMulOppositeObj R G M :=
  ObjectProperty.homMk ((homEquiv R G _ _).symm
    ⟨CharacterModule.dualOfMulOpposite f.hom.hom.hom.hom.hom, fun g c ↦
      dual_characterRepresentationOfMulOpposite _ _ _
        (fun g m ↦ finiteTypeContinuousModule_hom_comm f g m) g c⟩)

/-- The underlying linear map of the dual of `f` is `c ↦ c ∘ f`. -/
lemma finiteTypeContinuousModuleDualOfMulOppositeMap_hom
    {M N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G} (f : M ⟶ N) :
    (finiteTypeContinuousModuleDualOfMulOppositeMap (R := R) f).hom.hom.hom.hom.hom =
      CharacterModule.dualOfMulOpposite f.hom.hom.hom.hom.hom :=
  rfl

/-- **`M ↦ M^∨`**, the contravariant duality functor from finite `R`-modules with a continuous
`G`-action to finite `Rᵐᵒᵖ`-modules with a continuous `G`-action. -/
def finiteTypeContinuousModuleDual :
    (FiniteTypeContinuousModule.{u, v, w} R G)ᵒᵖ ⥤ FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G where
  obj M := finiteTypeContinuousModuleDualObj R G M.unop
  map f := finiteTypeContinuousModuleDualMap f.unop
  map_id _ := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- The duality functor sends a morphism `f` to `c ↦ c ∘ f` on characters. -/
lemma finiteTypeContinuousModuleDual_map_hom {M N : (FiniteTypeContinuousModule.{u, v, w} R G)ᵒᵖ}
    (f : M ⟶ N) :
    ((finiteTypeContinuousModuleDual R G).map f).hom.hom.hom.hom.hom =
      CharacterModule.dualMulOpposite f.unop.hom.hom.hom.hom.hom :=
  rfl

/-- **`N ↦ N^∨`**, the contravariant duality functor from finite `Rᵐᵒᵖ`-modules with a
continuous `G`-action to finite `R`-modules with a continuous `G`-action. -/
def finiteTypeContinuousModuleDualOfMulOpposite :
    (FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G)ᵒᵖ ⥤ FiniteTypeContinuousModule.{u, v, w} R G where
  obj N := finiteTypeContinuousModuleDualOfMulOppositeObj R G N.unop
  map f := finiteTypeContinuousModuleDualOfMulOppositeMap f.unop
  map_id _ := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- The duality functor sends a morphism `f` to `c ↦ c ∘ f` on characters. -/
lemma finiteTypeContinuousModuleDualOfMulOpposite_map_hom
    {M N : (FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G)ᵒᵖ} (f : M ⟶ N) :
    ((finiteTypeContinuousModuleDualOfMulOpposite R G).map f).hom.hom.hom.hom.hom =
      CharacterModule.dualOfMulOpposite f.unop.hom.hom.hom.hom.hom :=
  rfl

/-- **Pontryagin duality `M ≅ (M^∨)^∨`** for a finite `R`-module with a continuous `G`-action. -/
def finiteTypeContinuousModuleEvalIso (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    M ≅ finiteTypeContinuousModuleDualOfMulOppositeObj R G
      (finiteTypeContinuousModuleDualObj R G M) :=
  haveI : Module.Finite R M.obj.obj.obj.V := M.property
  haveI : Finite M.obj.obj.obj.V := Module.finite_of_finite R
  { hom := ObjectProperty.homMk ((homEquiv R G _ _).symm
      ⟨CharacterModule.evalMulOpposite R M.obj.obj.obj.V, fun g m ↦
        evalMulOpposite_characterRepresentation (finiteTypeContinuousModuleRepresentation R G M)
          g m⟩)
    inv := ObjectProperty.homMk ((homEquiv R G _ _).symm
      ⟨(CharacterModule.evalEquiv M.obj.obj.obj.V R).symm.toLinearMap, fun g x ↦ by
        obtain ⟨m, rfl⟩ := (CharacterModule.evalEquiv M.obj.obj.obj.V R).surjective x
        apply (CharacterModule.evalEquiv M.obj.obj.obj.V R).injective
        change CharacterModule.evalEquiv M.obj.obj.obj.V R
            ((CharacterModule.evalEquiv M.obj.obj.obj.V R).symm
              (characterRepresentationOfMulOpposite (characterRepresentation
                (finiteTypeContinuousModuleRepresentation R G M)) g
                (CharacterModule.evalEquiv M.obj.obj.obj.V R m))) =
          CharacterModule.evalEquiv M.obj.obj.obj.V R
            (finiteTypeContinuousModuleRepresentation R G M g
              ((CharacterModule.evalEquiv M.obj.obj.obj.V R).symm
                (CharacterModule.evalEquiv M.obj.obj.obj.V R m)))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
        exact (evalMulOpposite_characterRepresentation
          (finiteTypeContinuousModuleRepresentation R G M) g m).symm⟩)
    hom_inv_id := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <| ModuleCat.hom_ext <|
        LinearMap.ext (CharacterModule.evalEquiv M.obj.obj.obj.V R).symm_apply_apply
    inv_hom_id := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <| ModuleCat.hom_ext <|
        LinearMap.ext (CharacterModule.evalEquiv M.obj.obj.obj.V R).apply_symm_apply }

/-- **Pontryagin duality `N ≅ (N^∨)^∨`** for a finite `Rᵐᵒᵖ`-module with a continuous
`G`-action. -/
def finiteTypeContinuousModuleEvalOfMulOppositeIso
    (N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G) :
    N ≅ finiteTypeContinuousModuleDualObj R G
      (finiteTypeContinuousModuleDualOfMulOppositeObj R G N) :=
  haveI : Module.Finite Rᵐᵒᵖ N.obj.obj.obj.V := N.property
  haveI : Finite N.obj.obj.obj.V := Module.finite_of_finite Rᵐᵒᵖ
  { hom := ObjectProperty.homMk ((homEquiv Rᵐᵒᵖ G _ _).symm
      ⟨CharacterModule.evalOfMulOpposite R N.obj.obj.obj.V, fun g m ↦
        evalOfMulOpposite_characterRepresentation
          (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N) g m⟩)
    inv := ObjectProperty.homMk ((homEquiv Rᵐᵒᵖ G _ _).symm
      ⟨(CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).symm.toLinearMap, fun g x ↦ by
        obtain ⟨m, rfl⟩ := (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).surjective x
        apply (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).injective
        change CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R
            ((CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).symm
              (characterRepresentation (characterRepresentationOfMulOpposite
                (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N)) g
                (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R m))) =
          CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R
            (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N g
              ((CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).symm
                (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R m)))
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
        exact (evalOfMulOpposite_characterRepresentation
          (finiteTypeContinuousModuleRepresentation Rᵐᵒᵖ G N) g m).symm⟩)
    hom_inv_id := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <| ModuleCat.hom_ext <|
        LinearMap.ext (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).symm_apply_apply
    inv_hom_id := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <|
      ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <| ModuleCat.hom_ext <|
        LinearMap.ext (CharacterModule.evalEquivOfMulOpposite N.obj.obj.obj.V R).apply_symm_apply }

/-- Evaluation `M → (M^∨)^∨` is natural in `M`. -/
lemma finiteTypeContinuousModuleEvalIso_hom_naturality
    {M N : FiniteTypeContinuousModule.{u, v, w} R G} (f : M ⟶ N) :
    f ≫ (finiteTypeContinuousModuleEvalIso R G N).hom =
      (finiteTypeContinuousModuleEvalIso R G M).hom ≫
        finiteTypeContinuousModuleDualOfMulOppositeMap (finiteTypeContinuousModuleDualMap f) := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- Evaluation `N → (N^∨)^∨` is natural in `N`. -/
lemma finiteTypeContinuousModuleEvalOfMulOppositeIso_hom_naturality
    {M N : FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G} (f : M ⟶ N) :
    f ≫ (finiteTypeContinuousModuleEvalOfMulOppositeIso R G N).hom =
      (finiteTypeContinuousModuleEvalOfMulOppositeIso R G M).hom ≫
        finiteTypeContinuousModuleDualMap (finiteTypeContinuousModuleDualOfMulOppositeMap f) := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- **Duality is an anti-equivalence** between finite `R`-modules and finite `Rᵐᵒᵖ`-modules with
continuous `G`-action. -/
def finiteTypeContinuousModuleDualEquivalence :
    (FiniteTypeContinuousModule.{u, v, w} R G)ᵒᵖ ≌ FiniteTypeContinuousModule.{u, v, w} Rᵐᵒᵖ G :=
  CategoryTheory.Equivalence.mk (finiteTypeContinuousModuleDual R G)
    (finiteTypeContinuousModuleDualOfMulOpposite R G).rightOp
    (NatIso.ofComponents (fun M ↦ (finiteTypeContinuousModuleEvalIso R G M.unop).symm.op)
      (fun {M N} f ↦ by
        apply Quiver.Hom.unop_inj
        change (finiteTypeContinuousModuleEvalIso R G N.unop).inv ≫ f.unop =
          finiteTypeContinuousModuleDualOfMulOppositeMap
              (finiteTypeContinuousModuleDualMap f.unop) ≫
            (finiteTypeContinuousModuleEvalIso R G M.unop).inv
        rw [Iso.inv_comp_eq, ← Category.assoc, ← finiteTypeContinuousModuleEvalIso_hom_naturality,
          Category.assoc, Iso.hom_inv_id, Category.comp_id]))
    (NatIso.ofComponents (fun N ↦ (finiteTypeContinuousModuleEvalOfMulOppositeIso R G N).symm)
      (fun {M N} f ↦ by
        change finiteTypeContinuousModuleDualMap
              (finiteTypeContinuousModuleDualOfMulOppositeMap f) ≫
            (finiteTypeContinuousModuleEvalOfMulOppositeIso R G N).inv =
          (finiteTypeContinuousModuleEvalOfMulOppositeIso R G M).inv ≫ f
        rw [Iso.eq_inv_comp, ← Category.assoc,
          ← finiteTypeContinuousModuleEvalOfMulOppositeIso_hom_naturality, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]))

/-- The functor of the duality anti-equivalence is `finiteTypeContinuousModuleDual`. -/
lemma finiteTypeContinuousModuleDualEquivalence_functor :
    (finiteTypeContinuousModuleDualEquivalence.{u, v, w} R G).functor =
      finiteTypeContinuousModuleDual R G :=
  rfl

/-- The duality functor `M ↦ M^∨` is an equivalence of categories. -/
instance finiteTypeContinuousModuleDual_isEquivalence :
    (finiteTypeContinuousModuleDual.{u, v, w} R G).IsEquivalence :=
  (finiteTypeContinuousModuleDualEquivalence.{u, v, w} R G).isEquivalence_functor

/-- The duality functor `M ↦ M^∨` preserves finite limits. -/
instance preservesFiniteLimits_finiteTypeContinuousModuleDual :
    PreservesFiniteLimits (finiteTypeContinuousModuleDual.{u, v, w} R G) :=
  inferInstance

/-- The duality functor `M ↦ M^∨` preserves finite colimits. -/
instance preservesFiniteColimits_finiteTypeContinuousModuleDual :
    PreservesFiniteColimits (finiteTypeContinuousModuleDual.{u, v, w} R G) :=
  inferInstance

/-- The duality functor `M ↦ M^∨` is additive. -/
instance finiteTypeContinuousModuleDual_additive :
    (finiteTypeContinuousModuleDual.{u, v, w} R G).Additive :=
  Functor.additive_of_preserves_binary_products _

end Functors

end Stacks.GroupCohomology

end
