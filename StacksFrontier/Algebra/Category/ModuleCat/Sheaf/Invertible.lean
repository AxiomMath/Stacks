module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.PicardGroup
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Invertible modules and locally free modules of rank one

Let `R` be a sheaf of rings on a site. A sheaf of `R`-modules `M` is *finite locally free of
rank one* when, locally on a covering of the terminal object, it admits a basis of exactly one
element; it is *locally trivial* when, locally on such a covering, it is isomorphic to the
structure sheaf. This file proves that these two conditions agree, which is the geometric half
of the comparison between invertible modules and finite locally free modules of rank one.

The algebraic half is pointwise: over a *local* ring, a module is invertible (in the sense that
the canonical map `Mᵛ ⊗ M → R` is bijective) exactly when it is free of rank one. This file
records that characterization in the two shapes that the sheaf-theoretic statement consumes:
`Nonempty (M ≃ₗ[A] A)` and `Nonempty (Module.Basis (Fin 1) A M)`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank`: a sheaf of modules is finite
  locally free of rank `r` if it admits local generators (`SheafOfModules.LocalGeneratorsData`)
  which are locally free data and whose indexing types are equivalent to `Fin r`.
* `Stacks.SheafOfModules.Invertible.IsLocallyTrivial`: a sheaf of modules is locally trivial if
  there is a covering `X : I → C` of the terminal object such that each restriction
  `M.over (X i)` is isomorphic to the structure sheaf `SheafOfModules.unit (R.over (X i))`.
* `Stacks.SheafOfModules.Invertible.freeUniqueIso`: the free sheaf of modules on a type with a
  unique element is the structure sheaf.

## Main results

* `Stacks.SheafOfModules.Invertible.isLocallyTrivial_iff_isFiniteLocallyFreeOfRank_one`: a sheaf
  of modules is locally trivial if and only if it is finite locally free of rank one.
* `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.isLocallyFree` and
  `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.isFiniteType`: a finite locally
  free sheaf of modules of rank `r` is locally free and of finite type.
* `Stacks.SheafOfModules.Invertible.isLocallyTrivial_unit` and
  `Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_unit`: the structure sheaf,
  viewed as a module over itself, satisfies both conditions.
* `Stacks.SheafOfModules.Invertible.module_invertible_iff_nonempty_linearEquiv` and
  `Stacks.SheafOfModules.Invertible.module_invertible_iff_nonempty_basis`: over a local ring, a
  module is invertible if and only if it is free of rank one.

## Implementation notes

The definition `IsFiniteLocallyFreeOfRank` is a reducible spelling of the canonical class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of
[Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6) (3), so the two names denote
one class; it is stated on top of
Mathlib's `SheafOfModules.LocalGeneratorsData` and
`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`, which already carry Tag 01C6 (1). Rank is
pinned by an equivalence of the indexing type with `Fin r` rather than by a cardinality equation,
so that no finiteness side condition is needed.

The predicate `IsLocallyTrivial` is new here. It is the local form of
[Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS) "trivial", quantified over a
covering of the terminal object; `SheafOfModules.unit` is the structure sheaf viewed as a module
over itself.

No sheaf-level notion of *invertible* is defined. Mathlib's monoidal structure on modules over a
sheaf of rings lives at the level of presheaves of modules over a `CommRingCat`-valued presheaf
(`PresheafOfModules.monoidalCategory`), and the tensor functor on sheaves of modules — which is
what "tensoring by `M` is an equivalence" refers to — would have to be assembled from it by
sheafification. What is proved here is therefore the reduction
`IsFiniteLocallyFreeOfRank M 1 ↔ IsLocallyTrivial M` together with the pointwise statement about
`Module.Invertible`; the descent step from "locally the tensor functor is an equivalence" to
"the tensor functor is an equivalence" is not formalized, so no clause of Tag 0B8M is claimed and
no Stacks attribute is attached.

**Do not read that as "Tag 0B8M is unavailable in this repository".** It is not available *in
this direction*. The **converse** half — an invertible sheaf of modules on a ringed space with
local stalks is locally free of rank one — **is** proved, as
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` and
`Stacks.SheafOfModules.exists_nonempty_linearEquiv_of_isInvertible` in
`StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Basic.lean`, with a `Scheme` form
where local-ringness of the stalks is automatic. That proof needs **no finiteness on the stalk**:
the stalk pairing exhibits the stalk as an invertible module over the local ring directly, and an
invertible module over a local ring is already free of rank one, so Nakayama never appears. The
two halves have to be kept apart when citing what is available.

At the module level everything is assembled from Mathlib: `Module.Invertible`, the triviality of
the Picard group of a local ring (`CommRing.Pic`, `Subsingleton (CommRing.Pic A)` for
`IsLocalRing A`) and `Module.Invertible.free_iff_linearEquiv`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory Limits

universe u v u₁ v₁

namespace Stacks.SheafOfModules.Invertible

section Module

variable (A : Type u) [CommSemiring A] (M : Type v) [AddCommMonoid M] [Module A M]

/-- A module isomorphic to the base ring is invertible. No hypothesis on `A` is needed. -/
theorem module_invertible_of_linearEquiv (e : M ≃ₗ[A] A) : Module.Invertible A M :=
  Module.Invertible.congr e.symm

/-- An invertible module over a local ring is isomorphic to the ring: the Picard group of a
local ring is trivial, so an invertible module is free, and an invertible free module is
isomorphic to the ring. -/
@[ega "I 2.4.8" "partial"]
theorem nonempty_linearEquiv_of_module_invertible [IsLocalRing A] [Module.Invertible A M] :
    Nonempty (M ≃ₗ[A] A) :=
  Module.Invertible.free_iff_linearEquiv.mp inferInstance

/-- Over a local ring, a module is invertible exactly when it is isomorphic to the ring, that is,
exactly when it is free of rank one. -/
theorem module_invertible_iff_nonempty_linearEquiv [IsLocalRing A] :
    Module.Invertible A M ↔ Nonempty (M ≃ₗ[A] A) :=
  ⟨fun _ ↦ nonempty_linearEquiv_of_module_invertible A M,
    fun ⟨e⟩ ↦ module_invertible_of_linearEquiv A M e⟩

/-- Having a basis indexed by `Fin 1` is the same as being isomorphic to the base ring. -/
theorem nonempty_basis_iff_nonempty_linearEquiv :
    Nonempty (Module.Basis (Fin 1) A M) ↔ Nonempty (M ≃ₗ[A] A) :=
  ⟨fun ⟨b⟩ ↦ ⟨b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite A A (Fin 1) ≪≫ₗ
      LinearEquiv.funUnique (Fin 1) A A⟩,
    fun ⟨e⟩ ↦ ⟨Module.Basis.ofEquivFun (e ≪≫ₗ (LinearEquiv.funUnique (Fin 1) A A).symm)⟩⟩

/-- Over a local ring, a module is invertible exactly when it admits a basis indexed by
`Fin 1`. This is the form of "free of rank one" that matches `IsFiniteLocallyFreeOfRank _ 1`. -/
theorem module_invertible_iff_nonempty_basis [IsLocalRing A] :
    Module.Invertible A M ↔ Nonempty (Module.Basis (Fin 1) A M) :=
  (module_invertible_iff_nonempty_linearEquiv A M).trans
    (nonempty_basis_iff_nonempty_linearEquiv A M).symm

end Module

section Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

section Free

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of `R`-modules on a type with a unique element is the structure sheaf: the
coproduct of a single copy of `SheafOfModules.unit R` is that copy. -/
noncomputable def freeUniqueIso (I : Type u) [Unique I] :
    SheafOfModules.free (R := R) I ≅ SheafOfModules.unit R :=
  coproductUniqueIso _

end Free

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules is finite locally free of rank `r` if it admits local generators which are
locally free data and whose indexing types are all equivalent to `Fin r`.

This is a compatibility spelling of the canonical class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`: it is reducible, so instances and
hypotheses of either spelling are the same class to instance search. Its universe parameters keep
their original order (ring, objects, morphisms). -/
abbrev IsFiniteLocallyFreeOfRank (M : SheafOfModules.{u} R) (r : ℕ) : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, v₁, u₁} M r

/-- A sheaf of modules is locally trivial if there is a covering of the terminal object over each
member of which it becomes isomorphic to the structure sheaf. -/
class IsLocallyTrivial (M : SheafOfModules.{u} R) : Prop where
  /-- There is a covering of the terminal object trivializing the sheaf of modules. -/
  exists_trivializing_cover :
    ∃ (I : Type u₁) (X : I → C) (_ : J.CoversTop X),
      ∀ i, Nonempty (M.over (X i) ≅ SheafOfModules.unit (R.over (X i)))

/-- A locally trivial sheaf of modules is finite locally free of rank one: a trivialization
`M.over (X i) ≅ SheafOfModules.unit (R.over (X i))` is, up to the identification of the structure
sheaf with the free module on a one-element type, a basis of one element. -/
theorem isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial (M : SheafOfModules.{u} R)
    [h : IsLocallyTrivial M] : IsFiniteLocallyFreeOfRank M 1 := by
  obtain ⟨I, X, hX, e⟩ := h.exists_trivializing_cover
  have key i := freeUniqueIso PUnit.{u + 1} ≪≫ (e i).some.symm
  exact ⟨⟨I, X, hX, fun i ↦ ⟨PUnit.{u + 1}, (M.over (X i)).freeHomEquiv (key i).hom,
      by rw [Equiv.symm_apply_apply]; infer_instance⟩⟩,
    ⟨fun i ↦ by simpa [SheafOfModules.GeneratingSections.π] using (key i).isIso_hom⟩,
    fun i ↦ ⟨Equiv.ofUnique _ _⟩⟩

/-- A finite locally free sheaf of modules of rank one is locally trivial: over each member of
the covering, the free module on the one-element basis is the structure sheaf. -/
theorem isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one (M : SheafOfModules.{u} R)
    [h : IsFiniteLocallyFreeOfRank M 1] : IsLocallyTrivial M := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  refine ⟨q.I, q.X, q.coversTop, fun i ↦ ?_⟩
  have := (hr i).some.unique
  exact ⟨(asIso (q.generators i).π).symm ≪≫ freeUniqueIso _⟩

/-- The structure sheaf, viewed as a module over itself, is locally trivial: the identity
covering of the terminal object trivializes it. -/
instance isLocallyTrivial_unit : IsLocallyTrivial (SheafOfModules.unit R) :=
  ⟨C, id, fun _ ↦ GrothendieckTopology.covering_of_eq_top J (by simp), fun _ ↦ ⟨Iso.refl _⟩⟩

/-- The structure sheaf, viewed as a module over itself, is finite locally free of rank one. -/
instance isFiniteLocallyFreeOfRank_one_unit :
    IsFiniteLocallyFreeOfRank (SheafOfModules.unit R) 1 :=
  isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial _

/-- A sheaf of modules is locally trivial if and only if it is finite locally free of rank one. -/
theorem isLocallyTrivial_iff_isFiniteLocallyFreeOfRank_one (M : SheafOfModules.{u} R) :
    IsLocallyTrivial M ↔ IsFiniteLocallyFreeOfRank M 1 :=
  ⟨fun _ ↦ isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial M,
    fun _ ↦ isLocallyTrivial_of_isFiniteLocallyFreeOfRank_one M⟩

/-- A finite locally free sheaf of modules of rank `r` is locally free. -/
theorem IsFiniteLocallyFreeOfRank.isLocallyFree (M : SheafOfModules.{u} R) (r : ℕ)
    [h : IsFiniteLocallyFreeOfRank M r] : M.IsLocallyFree := by
  obtain ⟨q, hq, -⟩ := h.exists_isFiniteLocallyFreeOfRankData
  exact ⟨q, hq⟩

/-- A finite locally free sheaf of modules of rank `r` is of finite type: its local bases are
indexed by types equivalent to `Fin r`, hence finite. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteType (M : SheafOfModules.{u} R) (r : ℕ)
    [h : IsFiniteLocallyFreeOfRank M r] : SheafOfModules.IsFiniteType M := by
  obtain ⟨q, -, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  exact ⟨q, ⟨fun i ↦ ⟨Finite.of_equiv (Fin r) (hr i).some.symm⟩⟩⟩

end Sheaf

end Stacks.SheafOfModules.Invertible

end
