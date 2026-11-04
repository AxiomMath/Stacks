module

public import StacksFrontier.Deformation.Artin.Infinitesimal
import all StacksFrontier.Deformation.Artin.Infinitesimal

/-!
# Agreement of the two composition actions on morphisms of lifts

For two lifts `t₁`, `t₂` of one object of a category cofibered in groupoids, the relative
infinitesimal automorphisms of `t₁` act on the morphisms `t₁ ⟶ t₂` by precomposition and those
of `t₂` by postcomposition, and each action is simply transitive
(`StacksFrontier.Deformation.Artin.Infinitesimal`). A morphism of lifts identifies the two acting
groups by conjugation, and the two actions agree under that identification; when the acting
group is commutative the identification does not depend on the morphism chosen, so the two
actions are one simply transitive action of a single group.

## Main definitions

* `Deformation.Artin.liftFiberIsoOfHom` — the isomorphism of fibre objects underlying a
  morphism of lifts.
* `Deformation.Artin.infinitesimalAutTransport` — the identification, by conjugation along a
  morphism of lifts, of the relative infinitesimal automorphisms of its source with those of
  its target.

## Main results

* `Deformation.Artin.leftCompositionAction_eq_rightCompositionAction` — the two actions agree
  under the identification induced by the morphism they act on.
* `Deformation.Artin.leftCompositionAction_eq_rightCompositionAction_of_comm`,
  `Deformation.Artin.infinitesimalAutTransport_eq_of_comm` — for a commutative acting group
  the identification is independent of the morphism of lifts inducing it, and the two actions
  agree under it.

## Implementation notes

The identification of the two acting groups is conjugation by the isomorphism of fibre objects
underlying a morphism of lifts; that the two actions agree under it needs no further
hypothesis. Its independence of the chosen morphism does, and the hypothesis is exactly
commutativity of the relative infinitesimal automorphisms of the source lift: the two
conjugations differ by conjugation by a relative infinitesimal automorphism. Commutativity is
a hypothesis here, since neither the base nor the fibred category is restricted. In the
setting of Stacks 07YB, a category fibred in groupoids satisfying (RS*) over the big fppf site,
it is a consequence of (RS*), and the statement there, with the identifications
`Inf(x'/x) = Inf_x(I) = Inf(x''/x)` of Stacks 07Y9, is
`Deformation.Artin.InfComparisonData.actions_agree`. When the two lifts admit no morphism
at all, both actions are actions on an empty set and there is nothing to compare, which is why
the statements quantify over a morphism instead of assuming the lifts isomorphic.

## References

* [Stacks Project, Tag 07YB](https://stacks.math.columbia.edu/tag/07YB)
-/

@[expose] public section

namespace Deformation.Artin

section
open CategoryTheory

universe u v uF vF

variable {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ C} {A' A : C} {g : A' ⟶ A} {x : p.Fiber A}

/-- The isomorphism of fibre objects underlying a morphism of lifts. Every morphism of lifts
in a category cofibered in groupoids is invertible, and the inverse again lies over the
identity. -/
public noncomputable def liftFiberIsoOfHom
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    liftFiber t₁ ≅ liftFiber t₂ :=
  letI := Deformation.isIso_liftHom hp f
  { hom := CategoryTheory.Functor.Fiber.homMk p A' f.hom
    inv := CategoryTheory.Functor.Fiber.homMk p A' (inv f).hom
    hom_inv_id := Subtype.ext (congrArg (fun q : t₁ ⟶ t₁ => q.hom) (IsIso.hom_inv_id f))
    inv_hom_id := Subtype.ext (congrArg (fun q : t₂ ⟶ t₂ => q.hom) (IsIso.inv_hom_id f)) }

/-- The underlying arrow of `liftFiberIsoOfHom` is the given morphism of lifts. -/
public theorem liftFiberIsoOfHom_hom_val
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    (liftFiberIsoOfHom hp t₁ t₂ f).hom.val = f.hom := rfl

/-- An isomorphism of fibre objects cancels its inverse on underlying arrows. -/
private theorem iso_hom_val_comp_inv_val {u v : p.Fiber A'} (e : u ≅ v) :
    e.hom.val ≫ e.inv.val = 𝟙 u.1 :=
  congrArg (fun k : u ⟶ u => k.val) e.hom_inv_id

/-- An isomorphism of fibre objects is cancelled by its inverse on underlying arrows. -/
private theorem iso_inv_val_comp_hom_val {u v : p.Fiber A'} (e : u ≅ v) :
    e.inv.val ≫ e.hom.val = 𝟙 v.1 :=
  congrArg (fun k : v ⟶ v => k.val) e.inv_hom_id

/-- The morphism of lifts cancels `liftFiberIsoOfHom` on the left. -/
public theorem liftFiberIsoOfHom_hom_comp_inv
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    f.hom ≫ (liftFiberIsoOfHom hp t₁ t₂ f).inv.val = 𝟙 t₁.obj :=
  iso_hom_val_comp_inv_val (liftFiberIsoOfHom hp t₁ t₂ f)

/-- The morphism of lifts cancels `liftFiberIsoOfHom` on the right. -/
public theorem liftFiberIsoOfHom_inv_comp_hom
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    (liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ f.hom = 𝟙 t₂.obj :=
  iso_inv_val_comp_hom_val (liftFiberIsoOfHom hp t₁ t₂ f)

/-- The inverse of `liftFiberIsoOfHom` is a morphism of lifts in the other direction: it
carries the lifting arrow of the target to the lifting arrow of the source. -/
public theorem liftFiberIsoOfHom_inv_fac
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    (liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ t₁.hom = t₂.hom := by
  rw [← f.fac, ← Category.assoc, liftFiberIsoOfHom_inv_comp_hom, Category.id_comp]

/-- Conjugating a fibre automorphism by an isomorphism of fibre objects, read on underlying
arrows. -/
public theorem conjAut_hom_val {u v : p.Fiber A'} (e : u ≅ v) (a : Aut u) :
    (e.conjAut a).hom.val = e.inv.val ≫ a.hom.val ≫ e.hom.val :=
  (congrArg (fun k : v ⟶ v => k.val) (Iso.conjAut_hom e a)).trans rfl

/-- Conjugation by an isomorphism of fibre objects which is compatible with the two lifting
arrows carries relative infinitesimal automorphisms of the one lift to relative infinitesimal
automorphisms of the other. -/
public theorem conjAut_mem_infinitesimalAutomorphisms
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (e : liftFiber t₁ ≅ liftFiber t₂)
    (he : e.hom.val ≫ t₂.hom = t₁.hom) (a : Aut (liftFiber t₁))
    (ha : a ∈ infinitesimalAutomorphisms hp t₁) :
    e.conjAut a ∈ infinitesimalAutomorphisms hp t₂ := by
  have ha' := (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
    hp g t₁.hom t₁.isHomLift a).mp ha
  apply (Deformation.mem_relativeInfinitesimalAutomorphisms_iff
    hp g t₂.hom t₂.isHomLift (e.conjAut a)).2
  simp only [conjAut_hom_val, Category.assoc]
  rw [he, ha', ← he, ← Category.assoc, iso_inv_val_comp_hom_val, Category.id_comp]

/-- **The identification of the two groups of relative infinitesimal automorphisms.** A
morphism of lifts identifies the relative infinitesimal automorphisms of its source with
those of its target, by conjugation. -/
@[stacks 07YB "actions_agree"]
public noncomputable def infinitesimalAutTransport
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂) :
    infinitesimalAutomorphisms hp t₁ ≃* infinitesimalAutomorphisms hp t₂ where
  toFun a := ⟨(liftFiberIsoOfHom hp t₁ t₂ f).conjAut a.1,
    conjAut_mem_infinitesimalAutomorphisms hp t₁ t₂ (liftFiberIsoOfHom hp t₁ t₂ f)
      f.fac a.1 a.2⟩
  invFun b := ⟨(liftFiberIsoOfHom hp t₁ t₂ f).symm.conjAut b.1,
    conjAut_mem_infinitesimalAutomorphisms hp t₂ t₁ (liftFiberIsoOfHom hp t₁ t₂ f).symm
      (liftFiberIsoOfHom_inv_fac hp t₁ t₂ f) b.1 b.2⟩
  left_inv a := by
    apply Subtype.ext
    apply CategoryTheory.Aut.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    change ((liftFiberIsoOfHom hp t₁ t₂ f).symm.conjAut
      ((liftFiberIsoOfHom hp t₁ t₂ f).conjAut a.1)).hom.val = a.1.hom.val
    rw [conjAut_hom_val, conjAut_hom_val, Iso.symm_hom, Iso.symm_inv,
      liftFiberIsoOfHom_hom_val]
    calc f.hom ≫ ((liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ a.1.hom.val ≫ f.hom) ≫
            (liftFiberIsoOfHom hp t₁ t₂ f).inv.val
        = (f.hom ≫ (liftFiberIsoOfHom hp t₁ t₂ f).inv.val) ≫ a.1.hom.val ≫
            (f.hom ≫ (liftFiberIsoOfHom hp t₁ t₂ f).inv.val) := by
          simp only [Category.assoc]
      _ = a.1.hom.val := by rw [liftFiberIsoOfHom_hom_comp_inv]; simp
  right_inv b := by
    apply Subtype.ext
    apply CategoryTheory.Aut.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    change ((liftFiberIsoOfHom hp t₁ t₂ f).conjAut
      ((liftFiberIsoOfHom hp t₁ t₂ f).symm.conjAut b.1)).hom.val = b.1.hom.val
    rw [conjAut_hom_val, conjAut_hom_val, Iso.symm_hom, Iso.symm_inv,
      liftFiberIsoOfHom_hom_val]
    calc (liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫
            (f.hom ≫ b.1.hom.val ≫ (liftFiberIsoOfHom hp t₁ t₂ f).inv.val) ≫ f.hom
        = ((liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ f.hom) ≫ b.1.hom.val ≫
            ((liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ f.hom) := by
          simp only [Category.assoc]
      _ = b.1.hom.val := by rw [liftFiberIsoOfHom_inv_comp_hom]; simp
  map_mul' a b := Subtype.ext ((liftFiberIsoOfHom hp t₁ t₂ f).conjAut.map_mul a.1 b.1)

private theorem infinitesimalAutTransport_hom_val
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x) (f : t₁ ⟶ t₂)
    (a : infinitesimalAutomorphisms hp t₁) :
    (infinitesimalAutTransport hp t₁ t₂ f a).1.hom.val =
      (liftFiberIsoOfHom hp t₁ t₂ f).inv.val ≫ a.1.hom.val ≫ f.hom := by
  rw [show (infinitesimalAutTransport hp t₁ t₂ f a).1 =
    (liftFiberIsoOfHom hp t₁ t₂ f).conjAut a.1 from rfl, conjAut_hom_val,
    liftFiberIsoOfHom_hom_val]

/-- **The two actions agree.** The left action of a relative infinitesimal automorphism of the
source lift on a morphism of lifts is the right action, on the same morphism, of the
corresponding relative infinitesimal automorphism of the target lift. -/
@[stacks 07YB "actions_agree"]
public theorem leftCompositionAction_eq_rightCompositionAction
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a : infinitesimalAutomorphisms hp t₁) (f : t₁ ⟶ t₂) :
    leftCompositionAction hp t₁ t₂ a f =
      rightCompositionAction hp t₁ t₂ f (infinitesimalAutTransport hp t₁ t₂ f a) := by
  apply Deformation.Lift.Hom.ext
  rw [leftCompositionAction_hom, rightCompositionAction_hom, ← map_inv,
    infinitesimalAutTransport_hom_val]
  rw [← Category.assoc, liftFiberIsoOfHom_hom_comp_inv, Category.id_comp]

/-- The left and the right action commute with each other: precomposition and postcomposition
on a morphism of lifts are independent. -/
private theorem leftCompositionAction_rightCompositionAction
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (a : infinitesimalAutomorphisms hp t₁) (f : t₁ ⟶ t₂)
    (b : infinitesimalAutomorphisms hp t₂) :
    leftCompositionAction hp t₁ t₂ a (rightCompositionAction hp t₁ t₂ f b) =
      rightCompositionAction hp t₁ t₂ (leftCompositionAction hp t₁ t₂ a f) b := by
  apply Deformation.Lift.Hom.ext
  simp only [leftCompositionAction_hom, rightCompositionAction_hom, Category.assoc]

/-- **The identifications agree with each other: the two actions agree via them.** When the
relative infinitesimal automorphisms of the source lift commute, the left action of one of
them on a morphism of lifts is the right action, on that same morphism, of the automorphism of
the target lift that corresponds to it along *any* morphism of lifts. -/
public theorem leftCompositionAction_eq_rightCompositionAction_of_comm
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (hcomm : ∀ a b : infinitesimalAutomorphisms hp t₁, a * b = b * a)
    (a : infinitesimalAutomorphisms hp t₁) (f h : t₁ ⟶ t₂) :
    leftCompositionAction hp t₁ t₂ a f =
      rightCompositionAction hp t₁ t₂ f (infinitesimalAutTransport hp t₁ t₂ h a) := by
  obtain ⟨c, hc⟩ : ∃ c : infinitesimalAutomorphisms hp t₁,
      leftCompositionAction hp t₁ t₂ c h = f :=
    ⟨leftOrbitInverse hp t₁ t₂ h f, leftOrbitInverse_apply hp t₁ t₂ h f⟩
  calc leftCompositionAction hp t₁ t₂ a f
      = leftCompositionAction hp t₁ t₂ a (leftCompositionAction hp t₁ t₂ c h) := by rw [hc]
    _ = leftCompositionAction hp t₁ t₂ (a * c) h := (leftComposition_mul hp t₁ t₂ a c h).symm
    _ = leftCompositionAction hp t₁ t₂ (c * a) h := by rw [hcomm a c]
    _ = leftCompositionAction hp t₁ t₂ c (leftCompositionAction hp t₁ t₂ a h) :=
        leftComposition_mul hp t₁ t₂ c a h
    _ = leftCompositionAction hp t₁ t₂ c
          (rightCompositionAction hp t₁ t₂ h (infinitesimalAutTransport hp t₁ t₂ h a)) := by
        rw [leftCompositionAction_eq_rightCompositionAction hp t₁ t₂ a h]
    _ = rightCompositionAction hp t₁ t₂ (leftCompositionAction hp t₁ t₂ c h)
          (infinitesimalAutTransport hp t₁ t₂ h a) :=
        leftCompositionAction_rightCompositionAction hp t₁ t₂ c h _
    _ = rightCompositionAction hp t₁ t₂ f (infinitesimalAutTransport hp t₁ t₂ h a) := by
        rw [hc]

/-- **The identification does not depend on the chosen morphism of lifts.** When the relative
infinitesimal automorphisms of the source lift commute, any two morphisms of lifts induce the
same identification of the two groups. -/
public theorem infinitesimalAutTransport_eq_of_comm
    (hp : Deformation.IsCofiberedInGroupoids p)
    (t₁ t₂ : Deformation.Lift p g x)
    (hcomm : ∀ a b : infinitesimalAutomorphisms hp t₁, a * b = b * a)
    (f h : t₁ ⟶ t₂) :
    infinitesimalAutTransport hp t₁ t₂ f = infinitesimalAutTransport hp t₁ t₂ h := by
  apply MulEquiv.ext
  intro a
  refine (rightComposition_bijective hp t₁ t₂ f).1 ?_
  change rightCompositionAction hp t₁ t₂ f (infinitesimalAutTransport hp t₁ t₂ f a) =
    rightCompositionAction hp t₁ t₂ f (infinitesimalAutTransport hp t₁ t₂ h a)
  rw [← leftCompositionAction_eq_rightCompositionAction hp t₁ t₂ a f,
    ← leftCompositionAction_eq_rightCompositionAction_of_comm hp t₁ t₂ hcomm a f h]

end

end Deformation.Artin
