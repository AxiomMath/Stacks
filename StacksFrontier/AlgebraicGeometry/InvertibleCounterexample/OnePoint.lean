module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.PUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The one-point ringed space, and invertibility without local freeness

Fix a commutative ring `R`. The one-point topological space carries the ringed space whose
sections over an open `U` are the functions `U → R`: over the whole space this is `R`, and over
the empty open it is the trivial ring, which is the sheaf condition on a one-point space
(`TopCat.Presheaf.isSheaf_on_punit_of_isTerminal`). Every `R`-module `M` gives a sheaf of modules
on it in the same way, with sections `U → M` over `U`.

This construction is the counterexample of Tag 0B8M: on a one-point space the only open covering
of the whole space is the trivial one, so a sheaf of modules is finite locally free of rank one
exactly when it is globally isomorphic to the structure sheaf, i.e. exactly when `M` is a free
`R`-module; while invertibility of the sheaf is exactly invertibility of `M` as an `R`-module,
because the sectionwise tensor product computes the tensor product of sheaves of modules here.
So an invertible `R`-module that is not free — equivalently, a nontrivial class in the Picard
group of `R`, which exists because the Picard group of a commutative ring need not vanish —
produces an invertible sheaf of modules that is not finite locally free of rank one.

## Main definitions

* `Stacks.OnePointRingedSpace.ringedSpace`: the one-point ringed space with structure ring `R`.
* `Stacks.OnePointRingedSpace.moduleSheaf`: the sheaf of modules attached to an `R`-module.

## Main results

* `Stacks.OnePointRingedSpace.isInvertible_moduleSheaf`: the sheaf of modules attached to an
  invertible `R`-module is invertible.
* `Stacks.OnePointRingedSpace.not_isFiniteLocallyFreeOfRank_one`: the sheaf of modules attached
  to a non-free `R`-module is not finite locally free of rank one.
* `Stacks.RingedSpace.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one_of`: clause 3
  of Tag 0B8M, with the required invertible non-free module taken as a hypothesis.

## Implementation notes

The sections over `U` are modelled as the function type `↥U → R`, which is uniform in `U` — no
case distinction on whether `U` is the empty open or the whole space enters any definition. The
distinction is made only inside proofs, where `↥U` is either empty (and then every module of
sections is a subsingleton) or a singleton (and then a section is constant). That is what keeps
the pairing isomorphism of Tag 0B8K available sectionwise, hence available as an isomorphism of
presheaves of modules, which is the only input `Stacks.SheafOfModules.isInvertible_of_pairing`
needs: on a one-point space the sheafification of a presheaf of modules whose sections over the
empty open are zero is the presheaf itself, so no comparison with a sheafification has to be
computed.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits TensorProduct
open MonoidalCategory

universe u

namespace Stacks.OnePointRingedSpace

variable (R : Type u) [CommRing R]

/-- The one-point topological space. -/
abbrev space : TopCat.{u} := TopCat.of PUnit.{u + 1}

/-- The sections of the structure sheaf over an open `U` of the one-point space: the functions
from `U` to `R`. -/
abbrev sectionRing (U : (Opens space.{u})ᵒᵖ) : Type u := ↥(unop U) → R

/-- The restriction map of the structure sheaf: precomposition with the inclusion of opens. -/
def restrictionHom {U V : (Opens space.{u})ᵒᵖ} (i : U ⟶ V) : sectionRing R U →+* sectionRing R V
    where
  toFun f x := f ⟨x.1, i.unop.le x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The structure sheaf of the one-point ringed space: `U ↦ (↥U → R)`. -/
def structurePresheaf : space.{u}.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of (sectionRing R U)
  map i := CommRingCat.ofHom (restrictionHom R i)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of (not necessarily commutative) rings of the structure sheaf. -/
abbrev ringPresheaf : (Opens space.{u})ᵒᵖ ⥤ RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (structurePresheaf R)

/-- The empty open of the one-point space has no points. -/
instance : IsEmpty ↥(⊥ : Opens space.{u}) := ⟨fun x => x.2⟩

/-- The ring of sections of the structure sheaf over the empty open is trivial. -/
instance subsingleton_sectionRing_bot :
    Subsingleton (sectionRing R (op (⊥ : Opens space.{u}))) :=
  ⟨fun _ _ => funext fun x => (IsEmpty.false x).elim⟩

/-- Every open of the one-point space has at most one point. -/
instance subsingleton_open (U : (Opens space.{u})ᵒᵖ) : Subsingleton ↥(unop U) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-- A subsingleton object of `CommRingCat` is a terminal object. -/
def commRingCatIsTerminal (X : CommRingCat.{u}) [Subsingleton X] : IsTerminal X := by
  refine IsTerminal.ofUnique (h := fun Y => ?_) X
  refine ⟨⟨CommRingCat.ofHom ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩⟩,
    fun _ => ?_⟩
  ext
  exact Subsingleton.elim _ _

/-- A subsingleton object of `RingCat` is a terminal object. -/
def ringCatIsTerminal (X : RingCat.{u}) [Subsingleton X] : IsTerminal X := by
  refine IsTerminal.ofUnique (h := fun Y => ?_) X
  refine ⟨⟨RingCat.ofHom ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩⟩,
    fun _ => ?_⟩
  ext
  exact Subsingleton.elim _ _

/-- The structure presheaf of the one-point ringed space is a sheaf: its sections over the empty
open form the trivial ring, which is terminal. -/
theorem structurePresheaf_isSheaf : (structurePresheaf R).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_on_punit_of_isTerminal _ ?_
  refine @commRingCatIsTerminal _ ?_
  exact inferInstanceAs (Subsingleton (sectionRing R (op (⊥ : Opens space.{u}))))

/-- The underlying presheaf of rings of the structure sheaf is a sheaf. -/
theorem ringPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology space.{u}) (ringPresheaf R) := by
  refine TopCat.Presheaf.isSheaf_on_punit_of_isTerminal _ ?_
  refine @ringCatIsTerminal _ ?_
  exact inferInstanceAs (Subsingleton (sectionRing R (op (⊥ : Opens space.{u}))))

/-- The one-point ringed space with structure ring `R`. -/
def ringedSpace : AlgebraicGeometry.RingedSpace.{u, u} where
  carrier := space
  presheaf := structurePresheaf R
  IsSheaf := structurePresheaf_isSheaf R

/-- The structure sheaf of rings of the one-point ringed space. -/
noncomputable abbrev ringSheaf : Sheaf (Opens.grothendieckTopology space.{u}) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (structurePresheaf R)
    (ringPresheaf_isSheaf R)

/-- The sections of the sheaf of modules attached to `M` over an open `U`: the functions from `U`
to `M`. -/
abbrev moduleSections (M : Type u) (U : (Opens space.{u})ᵒᵖ) : Type u := ↥(unop U) → M

/-- The sections of `M` over `U` form a module over the sections of the structure sheaf over `U`,
acting pointwise. -/
instance moduleSections_isModule (M : Type u) [AddCommGroup M] [Module R M]
    (U : (Opens space.{u})ᵒᵖ) : Module ↥((ringPresheaf R).obj U) (moduleSections M U) :=
  inferInstanceAs (Module (sectionRing R U) (moduleSections M U))

variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The presheaf of modules on the one-point space attached to an `R`-module `M`, with sections
`↥U → M` over `U` and precomposition as restriction. -/
noncomputable def modulePresheaf : PresheafOfModules.{u} (ringPresheaf R) where
  obj U := ModuleCat.of ((ringPresheaf R).obj U) (moduleSections M U)
  map {_U V} i := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((ringPresheaf R).map i).hom).obj
        (ModuleCat.of ((ringPresheaf R).obj V) (moduleSections M V)))
    { toFun := fun f x => f ⟨x.1, i.unop.le x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The presheaf of modules attached to `M` is a sheaf: its sections over the empty open are
zero. -/
theorem modulePresheaf_isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology space.{u})
    (modulePresheaf R M).presheaf := by
  refine TopCat.Presheaf.isSheaf_on_punit_of_isTerminal _ ?_
  refine IsZero.isTerminal (@AddCommGrpCat.isZero_of_subsingleton _ ?_)
  exact inferInstanceAs (Subsingleton (moduleSections M (op (⊥ : Opens space.{u}))))

/-- The sheaf of modules on the one-point ringed space attached to an `R`-module `M`. -/
@[ega "I 1.8.4"]
noncomputable def moduleSheaf : SheafOfModules.{u} (ringSheaf R) where
  val := modulePresheaf R M
  isSheaf := modulePresheaf_isSheaf R M

section Pairing

variable (N : Type u) [AddCommGroup N] [Module R N] (e : N ⊗[R] M ≃ₗ[R] R)

/-- The sectionwise pairing of `moduleSections N` with `moduleSections M`, obtained by applying a
pairing `N ⊗[R] M ≃ₗ[R] R` pointwise. -/
noncomputable def pairingBilin (U : (Opens space.{u})ᵒᵖ) :
    moduleSections N U →ₗ[sectionRing R U] moduleSections M U →ₗ[sectionRing R U]
      sectionRing R U :=
  LinearMap.mk₂ (sectionRing R U) (fun g f x => e (g x ⊗ₜ[R] f x))
    (fun _ _ _ => funext fun _ => by simp [TensorProduct.add_tmul])
    (fun a g f => by
      funext x
      change e ((a x • g x) ⊗ₜ[R] f x) = a x * e (g x ⊗ₜ[R] f x)
      rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul])
    (fun _ _ _ => funext fun _ => by simp [TensorProduct.tmul_add])
    (fun a g f => by
      funext x
      change e (g x ⊗ₜ[R] (a x • f x)) = a x * e (g x ⊗ₜ[R] f x)
      rw [TensorProduct.tmul_smul, map_smul, smul_eq_mul])

/-- The pairing map on the sectionwise tensor product over an open `U`. -/
noncomputable def pairingMap (U : (Opens space.{u})ᵒᵖ) :
    (moduleSections N U) ⊗[sectionRing R U] (moduleSections M U) →ₗ[sectionRing R U]
      sectionRing R U :=
  TensorProduct.lift (pairingBilin R M N e U)

/-- The pairing map sends `g ⊗ₜ f` to the section `x ↦ e (g x ⊗ₜ f x)`. -/
@[simp] theorem pairingMap_tmul (U : (Opens space.{u})ᵒᵖ) (g : moduleSections N U)
    (f : moduleSections M U) :
    pairingMap R M N e U (g ⊗ₜ[sectionRing R U] f) = fun x => e (g x ⊗ₜ[R] f x) := rfl

/-- Constant sections give an additive map from the tensor product over `R` to the sectionwise
tensor product over `↥U → R`. -/
noncomputable def constTensorHom (U : (Opens space.{u})ᵒᵖ) :
    N ⊗[R] M →+ (moduleSections N U) ⊗[sectionRing R U] (moduleSections M U) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun n =>
      AddMonoidHom.mk' (fun m => (fun _ => n) ⊗ₜ[sectionRing R U] (fun _ => m))
        (fun m₁ m₂ => by
          rw [← TensorProduct.tmul_add]
          rfl))
      (fun n₁ n₂ => by
        ext m
        change (fun _ => n₁ + n₂) ⊗ₜ[sectionRing R U] (fun _ => m)
            = (fun _ => n₁) ⊗ₜ[sectionRing R U] (fun _ => m)
              + (fun _ => n₂) ⊗ₜ[sectionRing R U] (fun _ => m)
        rw [← TensorProduct.add_tmul]
        rfl))
    (fun r n m => by
      change (fun _ => r • n) ⊗ₜ[sectionRing R U] (fun _ => m)
          = (fun _ => n) ⊗ₜ[sectionRing R U] (fun _ => r • m)
      have h₁ : (fun _ => r • n : moduleSections N U)
          = (fun _ => r : sectionRing R U) • (fun _ => n : moduleSections N U) := rfl
      have h₂ : (fun _ => r • m : moduleSections M U)
          = (fun _ => r : sectionRing R U) • (fun _ => m : moduleSections M U) := rfl
      rw [h₁, h₂, TensorProduct.smul_tmul])

/-- `constTensorHom` sends `n ⊗ₜ m` to the tensor product of the constant sections `n` and `m`. -/
@[simp] theorem constTensorHom_tmul (U : (Opens space.{u})ᵒᵖ) (n : N) (m : M) :
    constTensorHom R M N U (n ⊗ₜ[R] m)
      = (fun _ => n) ⊗ₜ[sectionRing R U] (fun _ => m) := rfl

/-- The pairing map sends a constant tensor to the constant section given by the pairing. -/
theorem pairingMap_constTensorHom (U : (Opens space.{u})ᵒᵖ) (z : N ⊗[R] M) :
    pairingMap R M N e U (constTensorHom R M N U z) = fun _ => e z := by
  induction z with
  | tmul n m => rfl
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂]
    funext x
    simp

/-- Over an open with a point, every element of the sectionwise tensor product is a constant
tensor, because every section is constant. -/
theorem constTensorHom_surjective (U : (Opens space.{u})ᵒᵖ) (x₀ : ↥(unop U)) :
    Function.Surjective (constTensorHom R M N U) := by
  intro t
  induction t with
  | tmul g f =>
      refine ⟨g x₀ ⊗ₜ[R] f x₀, ?_⟩
      rw [constTensorHom_tmul]
      congr 1 <;> funext x <;> rw [Subsingleton.elim x x₀]
  | add t₁ t₂ h₁ h₂ =>
      obtain ⟨z₁, rfl⟩ := h₁
      obtain ⟨z₂, rfl⟩ := h₂
      exact ⟨z₁ + z₂, map_add _ _ _⟩

/-- The pairing map is bijective over every open: over the empty open both sides are
subsingletons, and over the whole space every section is constant. -/
theorem pairingMap_bijective (U : (Opens space.{u})ᵒᵖ) :
    Function.Bijective (pairingMap R M N e U) := by
  rcases isEmpty_or_nonempty ↥(unop U) with hU | hne
  · have hone : (1 : sectionRing R U) = 0 := funext fun x => (hU.false x).elim
    have hsrc : ∀ t : (moduleSections N U) ⊗[sectionRing R U] (moduleSections M U), t = 0 := by
      intro t
      calc t = (1 : sectionRing R U) • t := (one_smul _ t).symm
        _ = (0 : sectionRing R U) • t := by rw [hone]
        _ = 0 := zero_smul _ t
    refine ⟨fun a b _ => by rw [hsrc a, hsrc b], fun _ => ⟨0, ?_⟩⟩
    exact funext fun x => (hU.false x).elim
  · obtain ⟨x₀⟩ := hne
    refine ⟨?_, ?_⟩
    · intro a b hab
      obtain ⟨za, rfl⟩ := constTensorHom_surjective R M N U x₀ a
      obtain ⟨zb, rfl⟩ := constTensorHom_surjective R M N U x₀ b
      rw [pairingMap_constTensorHom, pairingMap_constTensorHom] at hab
      rw [e.injective (congrFun hab x₀)]
    · intro r
      refine ⟨constTensorHom R M N U (e.symm (r x₀)), ?_⟩
      rw [pairingMap_constTensorHom]
      funext x
      rw [Subsingleton.elim x x₀]
      exact e.apply_symm_apply _

/-- The pairing, as a linear equivalence on sections over `U`. -/
noncomputable def pairingEquiv (U : (Opens space.{u})ᵒᵖ) :
    (moduleSections N U) ⊗[sectionRing R U] (moduleSections M U) ≃ₗ[sectionRing R U]
      sectionRing R U :=
  LinearEquiv.ofBijective _ (pairingMap_bijective R M N e U)

/-- The pairing, as an isomorphism of presheaves of modules. This is the geometric input of
Tag 0B8K on the one-point space. -/
noncomputable def pairingIso :
    modulePresheaf R N ⊗ modulePresheaf R M ≅ 𝟙_ (PresheafOfModules.{u} (ringPresheaf R)) :=
  PresheafOfModules.isoMk (fun U => (pairingEquiv R M N e U).toModuleIso)
    (fun {_U _V} _i => ModuleCat.MonoidalCategory.tensor_ext (fun _ _ => rfl))

end Pairing

/-- **The sheaf of modules attached to an invertible module is invertible.** The pairing of `M`
with its dual is an isomorphism of presheaves of modules sectionwise, which is what
`Stacks.SheafOfModules.isInvertible_of_pairing` asks for. -/
theorem isInvertible_moduleSheaf [Module.Invertible R M] :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf R) (ringPresheaf_isSheaf R)
      (moduleSheaf R M) := by
  let e₁ := pairingIso R M (Module.Dual R M) (Module.Invertible.linearEquiv R M)
  let e₂ := pairingIso R (Module.Dual R M) M
    ((TensorProduct.comm R M (Module.Dual R M)).trans (Module.Invertible.linearEquiv R M))
  exact Stacks.SheafOfModules.isInvertible_of_pairing (moduleSheaf R M)
    (moduleSheaf R (Module.Dual R M)) e₁.hom e₂.hom (Functor.map_isIso _ e₁.hom)
    (Functor.map_isIso _ e₂.hom)

section NotFree

/-- Evaluation of a sheaf of modules on the localized site over the whole space, at the identity
of the whole space. -/
noncomputable abbrev evaluationTop :
    SheafOfModules.{u} ((ringSheaf R).over (⊤ : Opens space.{u})) ⥤
      ModuleCat.{u} ↥(((ringSheaf R).over (⊤ : Opens space.{u})).obj.obj
        (op (Over.mk (𝟙 (⊤ : Opens space.{u}))))) :=
  SheafOfModules.evaluation ((ringSheaf R).over (⊤ : Opens space.{u}))
    (op (Over.mk (𝟙 (⊤ : Opens space.{u}))))

/-- The point of the one-point space, as a point of the whole space viewed as an open. -/
abbrev topPoint : ↥(⊤ : Opens space.{u}) := ⟨PUnit.unit, trivial⟩

/-- A linear map between sections of constant modules over the whole space restricts to an
`R`-linear map, by evaluating at the point on constant sections. -/
private noncomputable def constEvalLinearMap (X Y : Type u) [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    (f : moduleSections X (op (⊤ : Opens space.{u})) →ₗ[sectionRing R (op (⊤ : Opens space.{u}))]
      moduleSections Y (op (⊤ : Opens space.{u}))) (x₀ : ↥(⊤ : Opens space.{u})) : X →ₗ[R] Y where
  toFun m := f (fun _ => m) x₀
  map_add' m₁ m₂ := by
    change f ((fun _ => m₁) + (fun _ => m₂)) x₀ = f (fun _ => m₁) x₀ + f (fun _ => m₂) x₀
    rw [map_add]
    rfl
  map_smul' r m := by
    change f ((fun _ => r : sectionRing R (op (⊤ : Opens space.{u}))) • (fun _ => m)) x₀
      = r • f (fun _ => m) x₀
    rw [map_smul]
    rfl

/-- **A trivialization over the whole space makes `M` free.** Over the whole one-point space a
section is constant, so an isomorphism of the sheaf of modules with the structure sheaf is an
`R`-linear isomorphism `M ≃ₗ[R] R`. -/
theorem free_of_iso_unit_top
    (i : (moduleSheaf R M).over (⊤ : Opens space.{u}) ≅
      SheafOfModules.unit ((ringSheaf R).over (⊤ : Opens space.{u}))) :
    Module.Free R M := by
  have φ : moduleSections M (op (⊤ : Opens space.{u})) ≃ₗ[sectionRing R
      (op (⊤ : Opens space.{u}))] sectionRing R (op (⊤ : Opens space.{u})) :=
    ((evaluationTop R).mapIso i).toLinearEquiv
  have hconst : ∀ (X : Type u) (g : ↥(⊤ : Opens space.{u}) → X),
      (fun _ => g topPoint.{u}) = g := by
    intro X g
    funext y
    rw [Subsingleton.elim y topPoint.{u}]
  have ψ : M ≃ₗ[R] R := by
    refine LinearEquiv.ofLinearMap (constEvalLinearMap R M R φ.toLinearMap topPoint.{u})
      (constEvalLinearMap R R M φ.symm.toLinearMap topPoint.{u}) ?_ ?_
    · refine LinearMap.ext fun r => ?_
      change φ (fun _ => φ.symm (fun _ => r) topPoint.{u}) topPoint.{u} = r
      rw [hconst _ (φ.symm (fun _ => r)), LinearEquiv.apply_symm_apply]
    · refine LinearMap.ext fun m => ?_
      change φ.symm (fun _ => φ (fun _ => m) topPoint.{u}) topPoint.{u} = m
      rw [hconst _ (φ (fun _ => m)), LinearEquiv.symm_apply_apply]
  exact Module.Free.of_equiv ψ.symm

/-- **The sheaf of modules attached to a non-free module is not finite locally free of rank
one.** On a one-point space every open covering of the whole space has a member equal to the
whole space, so a rank-one trivializing covering trivializes the sheaf globally, and then
`free_of_iso_unit_top` makes `M` free. -/
theorem not_isFiniteLocallyFreeOfRank_one (hfree : ¬ Module.Free R M) :
    ¬ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens space.{u}) (J := Opens.grothendieckTopology space.{u}) (moduleSheaf R M) 1 := by
  intro h
  obtain ⟨I, X, hX, hiso⟩ :=
    Stacks.InvertibleLocallyFree.exists_coversTop_nonempty_iso_unit_of_isFiniteLocallyFreeOfRank_one
      (structurePresheaf R) (ringPresheaf_isSheaf R) (moduleSheaf R M)
  have hmem : (PUnit.unit : ↥space.{u}) ∈ ⨆ i, X i := by
    rw [(Opens.coversTop_iff _ X).mp hX]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hmem
  have hXi : X i = ⊤ := by
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y (PUnit.unit : ↥space.{u})]
    exact hi
  exact hfree (free_of_iso_unit_top R M (hXi ▸ (hiso i).some))

end NotFree

end Stacks.OnePointRingedSpace

namespace Stacks.RingedSpace

open AlgebraicGeometry TopologicalSpace

/-- **Clause 3 of Stacks Tag 0B8M, with the commutative algebra as a hypothesis.** If some
commutative ring carries an invertible module that is not free, then there is a ringed space with
an invertible sheaf of modules that is not finite locally free of rank one.

The ringed space is `Stacks.OnePointRingedSpace.ringedSpace` above, whose stalk is the
given ring — not a local ring, since over a local ring every invertible module is free. This is
why the local-ring hypothesis of
`Stacks.RingedSpace.isInvertible_iff_isFiniteLocallyFreeOfRank_one` cannot be dropped. -/
theorem exists_isInvertible_not_isFiniteLocallyFreeOfRank_one_of
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Invertible R M]
    (hfree : ¬ Module.Free R M) :
    ∃ (X : AlgebraicGeometry.RingedSpace.{u})
      (L : SheafOfModules.{u} (structureSheaf X.sheaf)),
      Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L ∧
        ¬AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
          (C := Opens X) (J := Opens.grothendieckTopology X) L 1 :=
  ⟨OnePointRingedSpace.ringedSpace R, OnePointRingedSpace.moduleSheaf R M,
    OnePointRingedSpace.isInvertible_moduleSheaf R M,
    OnePointRingedSpace.not_isFiniteLocallyFreeOfRank_one R M hfree⟩

end Stacks.RingedSpace

end
