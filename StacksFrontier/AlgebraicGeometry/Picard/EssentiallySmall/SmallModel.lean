module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Smallness of a class of sheaves of modules from a bound on its sections

A sheaf of modules over a sheaf of rings `R` on a site `(C, J)`, with `C : Type u` a category
with morphisms in `Type v` and with module sections in `Type w`, is a large object: the type of
such sheaves is not `max u v w`-small, because the sections over an object may be an arbitrary
type of `Type w` and the isomorphism classes of those are not bounded by any universe below
`w + 1`.

This file shows that a *class* of sheaves of modules becomes essentially small as soon as its
sections are uniformly bounded: if there is a family of types `T X`, independent of the sheaf,
and every sheaf `L` in the class admits an injection `L(X) ↪ T X` for every object `X` of the
site, then the class is essentially small relative to the universe of `T`
(`Stacks.SheafOfModules.essentiallySmall_of_exists_injective_sections`). The mechanism is that
such an injection lets one record `L` by raw unstructured data — the images of the sections, and
the addition, scalar multiplication and restriction maps read through the injections — and that
raw data determines `L` up to isomorphism.

## Main definitions

* `Stacks.SheafOfModules.SmallModel.RawModel` — the raw data of a presheaf of modules whose
  sections are subsets of a fixed family of types: the subsets, and the addition, scalar
  multiplication and restriction maps as bare functions, with no axioms.
* `Stacks.SheafOfModules.SmallModel.RawModel.Realizes` — the assertion that a presheaf of
  modules is carried bijectively onto such raw data, compatibly with all the structure.

## Main results

* `Stacks.SheafOfModules.SmallModel.RawModel.nonempty_iso` — two presheaves of modules realized
  by the same raw data are isomorphic.
* `Stacks.SheafOfModules.SmallModel.exists_realizes` — a presheaf of modules whose sections
  inject into a fixed family of types is realized by some raw data.
* `Stacks.SheafOfModules.essentiallySmall_of_exists_injective_sections` — a class of sheaves of
  modules with uniformly bounded sections is essentially small.
* `Stacks.SheafOfModules.locallySmall` — the category of sheaves of modules is locally
  `max u v w`-small.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t v u w

namespace Stacks.SheafOfModules

namespace SmallModel

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {T : Cᵒᵖ → Type t}

/-- The raw data of a presheaf of `R`-modules whose sections over `X` are a subset of `T X`:
the subsets themselves together with the addition, the scalar multiplication and the
restriction maps, as bare functions. No axioms are imposed — the point of this type is only
that it is small, and that a presheaf of modules isomorphic to one carrying given raw data is
determined up to isomorphism by that data. -/
structure RawModel (R : Cᵒᵖ ⥤ RingCat.{w}) (T : Cᵒᵖ → Type t) where
  /-- The set of sections over each object. -/
  carrier : ∀ X : Cᵒᵖ, Set (T X)
  /-- The addition of sections. -/
  add : ∀ X : Cᵒᵖ, carrier X → carrier X → carrier X
  /-- The scalar multiplication on sections. -/
  smul : ∀ X : Cᵒᵖ, R.obj X → carrier X → carrier X
  /-- The restriction maps. -/
  res : ∀ {X Y : Cᵒᵖ}, (X ⟶ Y) → carrier X → carrier Y

/-- A presheaf of modules `M` is *realized* by the raw data `d` when its sections over every
object are carried bijectively onto `d`'s, compatibly with addition, scalar multiplication and
restriction. -/
def RawModel.Realizes (d : RawModel R T) (M : PresheafOfModules.{w} R) : Prop :=
  ∃ e : ∀ X : Cᵒᵖ, (M.obj X) ≃ (d.carrier X),
    (∀ (X : Cᵒᵖ) (a b : M.obj X), e X (a + b) = d.add X (e X a) (e X b)) ∧
    (∀ (X : Cᵒᵖ) (r : R.obj X) (a : M.obj X), e X (r • a) = d.smul X r (e X a)) ∧
    (∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (a : M.obj X), e Y (M.map f a) = d.res f (e X a))

/-- Two presheaves of modules realized by the same raw data are isomorphic: transporting the
sections through the two bijections is a family of linear equivalences, natural because both
bijections intertwine the restriction maps with the same raw restriction. -/
theorem RawModel.nonempty_iso {d : RawModel R T} {M N : PresheafOfModules.{w} R}
    (hM : d.Realizes M) (hN : d.Realizes N) : Nonempty (M ≅ N) := by
  obtain ⟨e, hadd, hsmul, hres⟩ := hM
  obtain ⟨e', hadd', hsmul', hres'⟩ := hN
  have key : ∀ (X : Cᵒᵖ) (a : M.obj X), e' X ((e' X).symm (e X a)) = e X a :=
    fun X a => (e' X).apply_symm_apply _
  refine ⟨PresheafOfModules.isoMk (fun X => LinearEquiv.toModuleIso
    { toFun := fun a => (e' X).symm (e X a)
      invFun := fun b => (e X).symm (e' X b)
      left_inv := fun a => by simp
      right_inv := fun b => by simp
      map_add' := fun a b => (e' X).injective (by
        rw [key, hadd, hadd', key, key])
      map_smul' := fun r a => (e' X).injective (by
        rw [key, hsmul, hsmul', key]; rfl) }) ?_⟩
  intro X Y f
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  change (e' Y).symm (e Y (M.map f a)) = N.map f ((e' X).symm (e X a))
  refine (e' Y).injective ?_
  have t1 : e' Y ((e' Y).symm (e Y (M.map f a))) = d.res f (e X a) :=
    ((e' Y).apply_symm_apply _).trans (hres X Y f a)
  have t2 : e' Y (N.map f ((e' X).symm (e X a))) = d.res f (e X a) :=
    (hres' X Y f ((e' X).symm (e X a))).trans
      (congrArg (d.res f) ((e' X).apply_symm_apply _))
  exact t1.trans t2.symm

/-- A presheaf of modules whose sections over every object inject into a fixed family of types
is realized by raw data: take the ranges of the injections, and read the structure through
them. -/
theorem exists_realizes {M : PresheafOfModules.{w} R}
    (h : ∀ X : Cᵒᵖ, ∃ f : M.obj X → T X, Function.Injective f) :
    ∃ d : RawModel R T, d.Realizes M := by
  choose f hf using h
  let e : ∀ X, M.obj X ≃ Set.range (f X) := fun X => Equiv.ofInjective (f X) (hf X)
  refine ⟨{ carrier := fun X => Set.range (f X)
            add := fun X a b => e X ((e X).symm a + (e X).symm b)
            smul := fun X r a => e X (r • (e X).symm a)
            res := fun {X Y} g a => e Y (M.map g ((e X).symm a)) }, e, ?_, ?_, ?_⟩
  · intro X a b; simp
  · intro X r a; simp
  · intro X Y g a; simp

/-- Isomorphism, as an equivalence relation on the objects of a category satisfying a given
property. -/
def isoSetoid {D : Type*} [Category* D] (P : ObjectProperty D) : Setoid (Subtype P) where
  r A B := Nonempty (A.1 ≅ B.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

end SmallModel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

open SmallModel in
/-- **A class of sheaves of modules with uniformly bounded sections is essentially small.**
If there is a family of types `T`, not depending on the sheaf, such that every sheaf of modules
with the property `P` has its sections over every object of the site injecting into `T`, then
the isomorphism classes of such sheaves form a set of size `max u v w t`.

The bound is what makes the statement non-trivial: the sections of a single sheaf of modules
always inject into themselves, but the class of all sheaves of modules is not essentially small
in any universe below `w + 1`. -/
theorem essentiallySmall_of_exists_injective_sections
    {R : Sheaf J RingCat.{w}} (P : ObjectProperty (SheafOfModules.{w} R))
    (T : Cᵒᵖ → Type t)
    (h : ∀ L : SheafOfModules.{w} R, P L → ∀ X : Cᵒᵖ,
      ∃ f : L.val.obj X → T X, Function.Injective f) :
    ObjectProperty.EssentiallySmall.{max u v w t} P := by
  classical
  have hd : ∀ A : Subtype P, ∃ d : RawModel R.obj T, d.Realizes A.1.val :=
    fun A => exists_realizes (h A.1 A.2)
  have hsmall : Small.{max u v w t} (Quotient (isoSetoid P)) := by
    let S : Subtype P → Set (RawModel R.obj T) := fun A =>
      {d | ∃ B : Subtype P, (isoSetoid P).r B A ∧ d.Realizes B.1.val}
    refine small_of_injective (f := Quotient.lift S ?_) ?_
    · intro A B hAB
      ext d
      exact ⟨fun ⟨E, hE, he⟩ => ⟨E, (isoSetoid P).trans hE hAB, he⟩,
             fun ⟨E, hE, he⟩ => ⟨E, (isoSetoid P).trans hE ((isoSetoid P).symm hAB), he⟩⟩
    · refine fun q q' => Quotient.inductionOn₂ q q' ?_
      intro A B hq
      obtain ⟨d, hdA⟩ := hd A
      obtain ⟨E, hEB, hdE⟩ : d ∈ S B :=
        (Set.ext_iff.1 (show S A = S B from hq) d).1 ⟨A, (isoSetoid P).refl A, hdA⟩
      refine Quotient.sound ((isoSetoid P).trans ?_ hEB)
      exact (RawModel.nonempty_iso hdA hdE).elim
        fun i => ⟨(SheafOfModules.fullyFaithfulForget R).preimageIso i⟩
  refine ⟨ObjectProperty.ofObj (fun q : Quotient (isoSetoid P) => (Quotient.out q).1),
    inferInstance, ?_⟩
  intro L hL
  refine ⟨(Quotient.out (Quotient.mk (isoSetoid P) ⟨L, hL⟩)).1, ⟨_⟩, ?_⟩
  exact (Quotient.mk_out (s := isoSetoid P) ⟨L, hL⟩).elim fun i => ⟨i.symm⟩

/-- The category of sheaves of modules on a site with objects in `Type u`, morphisms in
`Type v` and sections in `Type w` is locally `max u v w`-small: a morphism is a family, indexed
by the objects of the site, of maps between the sections. -/
theorem locallySmall {R : Sheaf J RingCat.{w}} :
    LocallySmall.{max u v w} (SheafOfModules.{w} R) where
  hom_small X Y := small_of_injective
    (f := fun (f : X ⟶ Y) => fun (Z : Cᵒᵖ) (a : X.val.obj Z) => (f.val.app Z a : Y.val.obj Z))
    (fun _ _ hfg => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Z =>
      ModuleCat.hom_ext (LinearMap.ext fun a => congrFun (congrFun hfg Z) a)))

end Stacks.SheafOfModules

end
