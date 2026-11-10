module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sectionwise exterior power preserves local surjectivity

Let `(C, J)` be a site, `O` a presheaf of commutative rings on it and `α : F ⟶ G` a morphism of
presheaves of `O`-modules. `PresheafOfModules.extPow n` is the presheaf of sectionwise `n`-th
exterior powers and `PresheafOfModules.extPowMap n α` is its action on `α`. This file proves that
**`extPowMap n α` is locally surjective whenever `α` is**.

Local surjectivity is phrased throughout by membership of `CategoryTheory.Presheaf.imageSieve` in
the topology, with the hypothesis taken explicitly rather than as a `Presheaf.IsLocallySurjective`
instance, since instance synthesis for the `Prop`-valued local-bijectivity classes can demand a
different spelling of the underlying presheaf than the one in context. The bridging lemmas
`PresheafOfModules.mem_imageSieve_of_app_eq` and
`PresheafOfModules.exists_app_eq_of_mem_imageSieve` are the two directions of the translation, and
they also keep the sections of a presheaf of modules spelled at `F.obj X` rather than at
`(toPresheaf _).obj F |>.obj X`, which carries no `Module` instance.

## Main results

* `CategoryTheory.GrothendieckTopology.exists_mem_forall_fin`: finitely many covering sieves on
  one object have a common covering refinement. This is what lets the `n` factors of a wedge be
  lifted simultaneously.
* `PresheafOfModules.mem_imageSieve_zero`, `mem_imageSieve_add`, `mem_imageSieve_smul`: the local
  liftability of a section is stable under the module operations, so it is a property of a
  submodule.
* `PresheafOfModules.mem_imageSieve_of_surjective`: a morphism surjective on every object is
  locally surjective.
* `PresheafOfModules.mem_imageSieve_comp`: local surjectivity is stable under composition.
* `PresheafOfModules.imageSieve_extPowMap_ιMulti_mem`: a wedge of `n` local sections lifts along
  `extPowMap n α` wherever its `n` factors lift along `α`.
* `PresheafOfModules.imageSieve_extPowMap_mem`: **`extPowMap n α` is locally surjective when `α`
  is.**

## Implementation notes

Wedges of `n` vectors span the `n`-th exterior power (`exteriorPower.ιMulti_span`), so a section
of `extPow n G` over `X` is a finite `O(X)`-linear combination of wedges; each wedge lifts on the
common refinement of the `n` image sieves of its factors, and the three closure lemmas assemble
the combination. Nothing here uses a sheaf condition.

The module universe is written `max w a` with `w` the ring universe, as in
`PresheafOfModules.extPow` itself; no universe is narrowed. The hypothesis and the conclusion are
both at the `(toPresheaf _).map` spelling because that is the only one
`CategoryTheory.Presheaf.imageSieve` accepts for a morphism of presheaves of modules.

`ExteriorAlgebra.mapₛₗ_ιMulti` (a semilinear base change carries a wedge to the wedge of the
images) comes from `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace CategoryTheory.GrothendieckTopology

/-- Finitely many covering sieves on one object have a common covering refinement. The topology
is closed under binary intersections, and this is the induction over a `Fin`-indexed family. -/
@[sga "3 IV 4.3.9", sga "4 II 1.1.1"]
theorem exists_mem_forall_fin {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U : C}
    {n : ℕ} (S : Fin n → Sieve U) (hS : ∀ i, S i ∈ J U) :
    ∃ T ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), T f → ∀ i, S i f := by
  induction n with
  | zero => exact ⟨⊤, J.top_mem U, fun _ _ _ i => i.elim0⟩
  | succ n ih =>
      obtain ⟨T, hT, hTle⟩ := ih (fun i => S i.succ) fun i => hS i.succ
      exact ⟨S 0 ⊓ T, J.intersection_covering (hS 0) hT,
        fun _ f hf => Fin.cases hf.1 fun i => hTle f hf.2 i⟩

end CategoryTheory.GrothendieckTopology

namespace PresheafOfModules

section ImageSieve

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G)

/-- Membership in the image sieve of a morphism of presheaves of modules, at the spelling a
presheaf of modules provides for its own sections. -/
theorem mem_imageSieve_of_app_eq {X : Cᵒᵖ} (y : G.obj X) {V : C} (f : V ⟶ X.unop)
    (z : F.obj (op V)) (h : α.app (op V) z = G.map f.op y) :
    Presheaf.imageSieve ((toPresheaf _).map α) y f := ⟨z, h⟩

/-- The local lift supplied by membership in the image sieve of a morphism of presheaves of
modules. -/
theorem exists_app_eq_of_mem_imageSieve {X : Cᵒᵖ} (y : G.obj X) {V : C} (f : V ⟶ X.unop)
    (hf : Presheaf.imageSieve ((toPresheaf _).map α) y f) :
    ∃ z : F.obj (op V), α.app (op V) z = G.map f.op y := hf

/-- A morphism of presheaves of modules is linear on sections. -/
theorem app_smul {X : Cᵒᵖ} (r : (O ⋙ forget₂ _ RingCat).obj X) (z : F.obj X) :
    α.app X (r • z) = r • α.app X z :=
  (α.app X).hom.map_smul r z

/-- Zero lifts along any morphism of presheaves of modules. -/
theorem mem_imageSieve_zero {X : Cᵒᵖ} {V : C} (f : V ⟶ X.unop) :
    Presheaf.imageSieve ((toPresheaf _).map α) (0 : G.obj X) f := by
  refine mem_imageSieve_of_app_eq α 0 f 0 ?_
  rw [map_zero]
  exact (map_zero (G.restrictₛₗ f.op)).symm

/-- A sum of two sections liftable along one arrow is liftable along it. -/
theorem mem_imageSieve_add {X : Cᵒᵖ} (y y' : G.obj X) {V : C} (f : V ⟶ X.unop)
    (hf : Presheaf.imageSieve ((toPresheaf _).map α) y f)
    (hf' : Presheaf.imageSieve ((toPresheaf _).map α) y' f) :
    Presheaf.imageSieve ((toPresheaf _).map α) (y + y') f := by
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve α y f hf
  obtain ⟨z', hz'⟩ := exists_app_eq_of_mem_imageSieve α y' f hf'
  refine mem_imageSieve_of_app_eq α (y + y') f (z + z') ?_
  rw [map_add, hz, hz']
  exact (map_add (G.restrictₛₗ f.op) y y').symm

/-- A scalar multiple of a section liftable along one arrow is liftable along it. -/
theorem mem_imageSieve_smul {X : Cᵒᵖ} (y : G.obj X) {V : C} (f : V ⟶ X.unop)
    (r : (O ⋙ forget₂ _ RingCat).obj X)
    (hf : Presheaf.imageSieve ((toPresheaf _).map α) y f) :
    Presheaf.imageSieve ((toPresheaf _).map α) (r • y) f := by
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve α y f hf
  refine mem_imageSieve_of_app_eq α (r • y) f ((O ⋙ forget₂ _ RingCat).map f.op r • z) ?_
  rw [app_smul, hz]
  exact (G.map_smul f.op r y).symm

end ImageSieve

section LocallySurjective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G)

/-- A morphism of presheaves of modules which is surjective on every object is locally
surjective. -/
theorem mem_imageSieve_of_surjective
    (hα : ∀ (X : Cᵒᵖ) (y : G.obj X), ∃ z : F.obj X, α.app X z = y)
    (X : Cᵒᵖ) (y : G.obj X) :
    Presheaf.imageSieve ((toPresheaf _).map α) y ∈ J X.unop := by
  refine J.superset_covering (fun V f _ => ?_) (J.top_mem X.unop)
  obtain ⟨z, hz⟩ := hα X y
  refine mem_imageSieve_of_app_eq α y f (F.map f.op z) ?_
  rw [naturality_apply, hz]

/-- A wedge of `n` local sections of `G` lifts along `extPowMap n α` wherever all `n` of its
factors lift along `α`. -/
theorem imageSieve_extPowMap_ιMulti_mem (n : ℕ)
    (hα : ∀ (X : Cᵒᵖ) (y : G.obj X), Presheaf.imageSieve ((toPresheaf _).map α) y ∈ J X.unop)
    (X : Cᵒᵖ) (s : Fin n → G.obj X) :
    Presheaf.imageSieve ((toPresheaf _).map (extPowMap n α))
        ((extPowSections n G X).symm
          (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n s)) ∈ J X.unop := by
  obtain ⟨T, hT, hTle⟩ := J.exists_mem_forall_fin
    (fun i => Presheaf.imageSieve ((toPresheaf _).map α) (s i)) fun i => hα X (s i)
  refine J.superset_covering (fun V f hf => ?_) hT
  choose t ht using fun i => exists_app_eq_of_mem_imageSieve α (s i) f (hTle f hf i)
  refine mem_imageSieve_of_app_eq (extPowMap n α) _ f
    ((extPowSections n F (op V)).symm
      (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj (op V)) n t)) ?_
  refine (extPowSections n G (op V)).injective (Subtype.ext ?_)
  refine Eq.trans (extPowMap_app_ιMulti n α (op V) t _ ?_) ?_
  · exact exteriorPower.ιMulti_apply_coe _ n t
  · refine Eq.trans ?_ (extPowSections_map n G f.op _).symm
    refine Eq.trans ?_ (ExteriorAlgebra.mapₛₗ_ιMulti _ _ n s).symm
    exact congrArg (ExteriorAlgebra.ιMulti _ n) (funext fun i => ht i)

/-- **The presheaf of sectionwise exterior powers preserves local surjectivity.** A section of
`extPow n G` is an `O(X)`-linear combination of wedges, and each wedge lifts on the common
refinement of the image sieves of its factors. -/
theorem imageSieve_extPowMap_mem (n : ℕ)
    (hα : ∀ (X : Cᵒᵖ) (y : G.obj X), Presheaf.imageSieve ((toPresheaf _).map α) y ∈ J X.unop)
    (X : Cᵒᵖ) (y : (extPow n G).obj X) :
    Presheaf.imageSieve ((toPresheaf _).map (extPowMap n α)) y ∈ J X.unop := by
  have hspan : ∀ t ∈ Submodule.span ((O ⋙ forget₂ _ RingCat).obj X)
      (Set.range (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n (M := G.obj X))),
      Presheaf.imageSieve ((toPresheaf _).map (extPowMap n α))
        ((extPowSections n G X).symm t) ∈ J X.unop := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨s, rfl⟩ := hw
        exact imageSieve_extPowMap_ιMulti_mem J α n hα X s
    | zero =>
        refine J.superset_covering (fun V f _ => ?_) (J.top_mem X.unop)
        rw [map_zero]
        exact mem_imageSieve_zero (extPowMap n α) f
    | add p q _ _ hp hq =>
        refine J.superset_covering (fun V f hf => ?_) (J.intersection_covering hp hq)
        rw [map_add]
        exact mem_imageSieve_add (extPowMap n α) _ _ f hf.1 hf.2
    | smul r p _ hp =>
        refine J.superset_covering (fun V f hf => ?_) hp
        rw [LinearEquiv.map_smul]
        exact mem_imageSieve_smul (extPowMap n α) _ f r hf
  have h := hspan (extPowSections n G X y)
    (by rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top)
  rwa [LinearEquiv.symm_apply_apply] at h

end LocallySurjective

section Comp

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G H : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} (α : F ⟶ G) (β : G ⟶ H)

/-- **Local surjectivity is stable under composition**, in the image-sieve form: lift along `β`
on a covering sieve, then lift each of those lifts along `α`, and apply transitivity of the
topology. -/
theorem mem_imageSieve_comp
    (hα : ∀ (X : Cᵒᵖ) (y : G.obj X), Presheaf.imageSieve ((toPresheaf _).map α) y ∈ J X.unop)
    (hβ : ∀ (X : Cᵒᵖ) (y : H.obj X), Presheaf.imageSieve ((toPresheaf _).map β) y ∈ J X.unop)
    (X : Cᵒᵖ) (y : H.obj X) :
    Presheaf.imageSieve ((toPresheaf _).map (α ≫ β)) y ∈ J X.unop := by
  refine J.transitive (hβ X y) _ fun V f hf => ?_
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve β y f hf
  refine J.superset_covering (fun W g hg => ?_) (hα (op V) z)
  obtain ⟨t, ht⟩ := exists_app_eq_of_mem_imageSieve α z g hg
  refine mem_imageSieve_of_app_eq (α ≫ β) y (g ≫ f) t ?_
  rw [comp_app]
  change Hom.app β (op W) (Hom.app α (op W) t) = _
  rw [ht, naturality_apply, hz, ← map_comp_apply]
  rfl

end Comp

end PresheafOfModules

end
