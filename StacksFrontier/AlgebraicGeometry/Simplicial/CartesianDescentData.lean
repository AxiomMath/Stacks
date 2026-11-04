module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian objects over a simplicial object, and descent data

A cartesian object over a simplicial object `X` in a category with pullbacks is determined by its
object over `X₀` together with an isomorphism between the two pullbacks of that object to `X₁`.
The isomorphism is normalized along the degeneracy and satisfies the usual cocycle condition over
`X₂`. These descent data form a category equivalent to the category of cartesian objects.

The proof turns both the normalization and the cocycle condition into statements about the
*action* of the transition isomorphism on generalized points: a point of `X₁` together with a
point of the object over its first face is carried to a point of the object over its second face.
In that language an object over `X₀` with such an action is exactly a simplicial object over `X`
whose structure squares are cartesian, reconstructed degreewise as the pullback of the object
along the initial-vertex map of each simplex.

## Main definitions

* `Stacks.Simplicial.Descent.DescentDatum`: an object over `X₀`, a transition
  isomorphism over `X₁`, its normalization along the degeneracy, and the cocycle condition
  over `X₂`.
* `Stacks.Simplicial.Descent.DescentDatum.Hom`: a morphism of descent data.
* `Stacks.Simplicial.Descent.iteratedPullbackIsoOfCompEq` and
  `Stacks.Simplicial.Descent.iteratedPullbackIsoSelf`: the canonical
  identifications of iterated base changes used to state those two conditions.

## Main results

* `Stacks.Simplicial.Descent.cartesianObjectsOverEquivalenceDescentData`: cartesian
  simplicial objects over a fixed simplicial object are equivalent to descent data.

## Implementation notes

The statement is made in an arbitrary category with pullbacks. Iterated base changes are
identified by the canonical isomorphisms furnished by `CategoryTheory.Over.pullbackComp`; this
records all the canonical identifications implicit in the displayed formulas in the source.

## References

* [Stacks Project, Tag 07TC](https://stacks.math.columbia.edu/tag/07TC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe v u

namespace Stacks.Simplicial.Descent


variable {C : Type u} [Category.{v} C] [HasPullbacks C]

-- The pullback lifting equations are used throughout, in both the plain and the
-- reassociated form; neither is a global `simp` lemma.
attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- The canonical identification of two iterated base changes whose maps to the base agree. -/
noncomputable def iteratedPullbackIsoOfCompEq {A B B' Z : C}
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' : B' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (V : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj V) ≅
      (Over.pullback f').obj ((Over.pullback g').obj V) :=
  (Over.pullbackComp f g).symm.app V ≪≫
    eqToIso (congrArg (fun k ↦ (Over.pullback k).obj V) h) ≪≫
    (Over.pullbackComp f' g').app V

/-- The canonical identification of the base change along a split composite with the original
object. -/
noncomputable def iteratedPullbackIsoSelf {A Z : C} (f : A ⟶ Z) (s : Z ⟶ A)
    (h : s ≫ f = 𝟙 Z) (V : Over Z) :
    (Over.pullback s).obj ((Over.pullback f).obj V) ≅ V :=
  (Over.pullbackComp s f).symm.app V ≪≫
    eqToIso (congrArg (fun k ↦ (Over.pullback k).obj V) h) ≪≫
    (Over.pullbackId).app V

/-- Descent data on the zero-simplices of a simplicial object.  The equation `unit` is
`(s⁰₀)* φ = 1`, and `cocycle` is `(d²₁)* φ = (d²₂)* φ` followed by
`(d²₀)* φ`, with the canonical base-change identifications inserted. -/
structure DescentDatum (X : SimplicialObject C) where
  /-- The object over `X₀`. -/
  V : Over (X.obj (Opposite.op (SimplexCategory.mk 0)))
  /-- The transition isomorphism over `X₁`. -/
  iso : (Over.pullback (X.δ (1 : Fin 2))).obj V ≅
    (Over.pullback (X.δ (0 : Fin 2))).obj V
  /-- Pullback of the transition isomorphism along the degeneracy is the identity. -/
  unit :
    (Over.pullback (X.σ (0 : Fin 1))).map iso.hom ≫
        (iteratedPullbackIsoSelf (X.δ (0 : Fin 2)) (X.σ (0 : Fin 1))
          (X.δ_comp_σ_self (i := (0 : Fin 1))) V).hom =
      (iteratedPullbackIsoSelf (X.δ (1 : Fin 2)) (X.σ (0 : Fin 1))
        (X.δ_comp_σ_succ (i := (0 : Fin 1))) V).hom
  /-- The transition isomorphism satisfies the cocycle condition over `X₂`. -/
  cocycle :
    (iteratedPullbackIsoOfCompEq (X.δ (2 : Fin 3)) (X.δ (1 : Fin 2))
          (X.δ (1 : Fin 3)) (X.δ (1 : Fin 2))
          (X.δ_comp_δ_self (i := (1 : Fin 2))).symm V).hom ≫
        (Over.pullback (X.δ (1 : Fin 3))).map iso.hom =
      (Over.pullback (X.δ (2 : Fin 3))).map iso.hom ≫
        (iteratedPullbackIsoOfCompEq (X.δ (2 : Fin 3)) (X.δ (0 : Fin 2))
          (X.δ (0 : Fin 3)) (X.δ (1 : Fin 2))
          (X.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by simp)) V).hom ≫
        (Over.pullback (X.δ (0 : Fin 3))).map iso.hom ≫
        (iteratedPullbackIsoOfCompEq (X.δ (0 : Fin 3)) (X.δ (0 : Fin 2))
          (X.δ (1 : Fin 3)) (X.δ (0 : Fin 2))
          (X.δ_comp_δ_self (i := (0 : Fin 2))) V).hom

namespace DescentDatum

/-- A morphism of descent data is a morphism over `X₀` compatible with the transition
isomorphisms. -/
structure Hom {X : SimplicialObject C} (D E : DescentDatum X) where
  /-- The underlying morphism over `X₀`. -/
  hom : D.V ⟶ E.V
  comm :
    (Over.pullback (X.δ (1 : Fin 2))).map hom ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map hom := by aesop_cat

/-- Two morphisms of descent data are equal when their underlying morphisms over `X₀` are. -/
@[ext]
lemma Hom.ext {X : SimplicialObject C} {D E : DescentDatum X} (f g : Hom D E)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  simp_all

/-- Descent data over a simplicial object form a category, with composition that of the
underlying morphisms over `X₀`. -/
instance (X : SimplicialObject C) : Category (DescentDatum X) where
  Hom := Hom
  id D := ⟨𝟙 D.V, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp _ := Hom.ext _ _ (by simp)
  comp_id _ := Hom.ext _ _ (by simp)
  assoc _ _ _ := Hom.ext _ _ (by simp)

end DescentDatum


/-- The first projection of the base change along a composite, through the inverse of
`Over.pullbackComp`, is the composite of the two first projections. -/
lemma pullbackComp_inv_fst {A B Z : C} (f : A ⟶ B) (g : B ⟶ Z)
    (V : Over Z) :
    ((Over.pullbackComp f g).inv.app V).left ≫ pullback.fst V.hom (f ≫ g) =
      pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g := by
  simp [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app]

/-- The underlying morphism of `Over.pullbackId` is the first projection of the base change along
the identity. -/
lemma pullbackId_hom_left {Z : C} (V : Over Z) :
    ((Over.pullbackId).hom.app V).left = pullback.fst V.hom (𝟙 Z) := by
  simp [Over.pullbackId, conjugateIsoEquiv]

/-- Transporting a base change along an equality of maps commutes with the first projections. -/
lemma eqToHom_pullback_fst {A Z : C} {f g : A ⟶ Z} (h : f = g)
    (V : Over Z) :
    (eqToHom (congrArg (fun k ↦ (Over.pullback k).obj V) h)).left ≫
        pullback.fst V.hom g = pullback.fst V.hom f := by
  subst g
  simp

/-- The identification `iteratedPullbackIsoOfCompEq` is compatible with the composite first
projections of the two iterated base changes to `V`. -/
lemma iteratedPullbackIsoOfCompEq_fst {A B B' Z : C}
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' : B' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (V : Over Z) :
    (iteratedPullbackIsoOfCompEq f g f' g' h V).hom.left ≫
        pullback.fst ((Over.pullback g').obj V).hom f' ≫ pullback.fst V.hom g' =
      pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g := by
  have hh := pullbackComp_inv_fst f' g' V
  have hh' : ((Over.pullbackComp f' g').hom.app V).left ≫
      pullback.fst ((Over.pullback g').obj V).hom f' ≫ pullback.fst V.hom g' =
      pullback.fst V.hom (f' ≫ g') := by
    rw [← hh]
    simp [← Over.comp_left, ← Category.assoc]
  simp only [iteratedPullbackIsoOfCompEq, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Over.comp_left, Category.assoc, eqToIso.hom]
  rw [hh', eqToHom_pullback_fst h V, pullbackComp_inv_fst]

/-- The identification `iteratedPullbackIsoSelf` is the composite of the two first projections. -/
lemma iteratedPullbackIsoSelf_left {A Z : C} (f : A ⟶ Z) (s : Z ⟶ A)
    (h : s ≫ f = 𝟙 Z) (V : Over Z) :
    (iteratedPullbackIsoSelf f s h V).hom.left =
      pullback.fst ((Over.pullback f).obj V).hom s ≫ pullback.fst V.hom f := by
  simp only [iteratedPullbackIsoSelf, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Over.comp_left,
    pullbackId_hom_left, eqToIso.hom]
  rw [eqToHom_pullback_fst h V, pullbackComp_inv_fst]

/-- The action of a morphism `φ : f^* V ⟶ g^* V` over `A` on generalized points: a point `t` of
`A` together with a point `v` of `V` over `f ∘ t` is sent to the point of `V` obtained by
applying `φ` to the pair and projecting to `V`. -/
noncomputable def action {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    {T : C} (t : T ⟶ A) (v : T ⟶ V.left) (h : v ≫ V.hom = t ≫ f) :
    T ⟶ V.left :=
  pullback.lift v t h ≫ φ.left ≫ pullback.fst V.hom g

/-- The image of a point under `action φ` lies over `g ∘ t`. -/
lemma action_base {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    {T : C} (t : T ⟶ A) (v : T ⟶ V.left) (h : v ≫ V.hom = t ≫ f) :
    action φ t v h ≫ V.hom = t ≫ g := by
  simp only [action, Category.assoc, pullback.condition]
  rw [← Category.assoc φ.left, show φ.left ≫ pullback.snd V.hom g =
    pullback.snd V.hom f from Over.w φ]
  simp

/-- The action of `φ` commutes with precomposition of the points. -/
lemma action_precomp {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    {S T : C} (a : S ⟶ T) (t : T ⟶ A) (v : T ⟶ V.left)
    (h : v ≫ V.hom = t ≫ f) :
    action φ (a ≫ t) (a ≫ v) (by simpa [Category.assoc] using congrArg (a ≫ ·) h) =
      a ≫ action φ t v h := by
  have hl : pullback.lift (a ≫ v) (a ≫ t)
      (by simpa [Category.assoc] using congrArg (a ≫ ·) h) = a ≫ pullback.lift v t h := by
    apply pullback.hom_ext <;> simp
  exact (congrArg (· ≫ φ.left ≫ pullback.fst V.hom g) hl).trans (by simp [action])

/-- The action depends on the point of the base and the point of the object over it, but not on
the proof that the two are compatible. -/
lemma action_congr {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    {T : C} {t t' : T ⟶ A} {v v' : T ⟶ V.left}
    (h : v ≫ V.hom = t ≫ f) (h' : v' ≫ V.hom = t' ≫ f)
    (ht : t = t') (hvv : v = v') :
    action φ t v h = action φ t' v' h' := by
  subst ht
  subst hvv
  rfl

/-- The point of `g^* V` determined by the image of `(t, v)` under `action φ` is the image of the
point `(v, t)` of `f^* V` under `φ`. -/
lemma action_lift {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    {T : C} (t : T ⟶ A) (v : T ⟶ V.left) (h : v ≫ V.hom = t ≫ f) :
    pullback.lift (action φ t v h) t (action_base φ t v h) =
      pullback.lift v t h ≫ φ.left := by
  apply pullback.hom_ext
  · simp [action]
  · simp only [pullback.lift_snd, Category.assoc]
    rw [show φ.left ≫ pullback.snd V.hom g = pullback.snd V.hom f from Over.w φ]
    simp

/-- The action of the inverse of an isomorphism `φ` undoes the action of `φ`. -/
lemma action_inv {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ≅ (Over.pullback g).obj V)
    {T : C} (t : T ⟶ A) (v : T ⟶ V.left) (h : v ≫ V.hom = t ≫ f) :
    action φ.inv t (action φ.hom t v h) (action_base φ.hom t v h) = v := by
  change pullback.lift (action φ.hom t v h) t _ ≫ φ.inv.left ≫
    pullback.fst V.hom f = v
  rw [action_lift]
  have hφ : φ.hom.left ≫ φ.inv.left = 𝟙 _ := congrArg CommaMorphism.left φ.hom_inv_id
  simp only [Category.assoc]
  rw [← Category.assoc φ.hom.left, hφ]
  simp

/-- The base change of `φ` along `b : A ⟶ B`, composed with the projections to `V`, acts on a
point by the action of `φ` on its image in `B`. -/
lemma action_pullback {A B Z : C} {f g : B ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V) (b : A ⟶ B)
    {T : C} (q : T ⟶ ((Over.pullback b).obj ((Over.pullback f).obj V)).left) :
    q ≫ ((Over.pullback b).map φ).left ≫
        pullback.fst ((Over.pullback g).obj V).hom b ≫ pullback.fst V.hom g =
      action φ (q ≫ pullback.snd ((Over.pullback f).obj V).hom b ≫ b)
        (q ≫ pullback.fst ((Over.pullback f).obj V).hom b ≫ pullback.fst V.hom f)
        (by simp [pullback.condition, pullback.condition_assoc, Category.assoc]) := by
  have hl : pullback.lift
      (q ≫ pullback.fst ((Over.pullback f).obj V).hom b ≫ pullback.fst V.hom f)
      (q ≫ pullback.snd ((Over.pullback f).obj V).hom b ≫ b)
      (by simp [pullback.condition, pullback.condition_assoc, Category.assoc]) =
      q ≫ pullback.fst ((Over.pullback f).obj V).hom b := by
    apply pullback.hom_ext
    · simp
    · simp [Category.assoc, pullback.condition]
  calc
    _ = (q ≫ pullback.fst ((Over.pullback f).obj V).hom b) ≫
        φ.left ≫ pullback.fst V.hom g := by simp [Over.pullback_map_left]
    _ = _ := (congrArg (· ≫ φ.left ≫ pullback.fst V.hom g) hl).symm

/-- The normalization of `φ` along a common section `s` of `f` and `g` holds if and only if the
action of `φ` fixes every point lying over the image of `s`. -/
lemma unit_iff_action {A Z : C} (f g : A ⟶ Z) (s : Z ⟶ A)
    (hf : s ≫ f = 𝟙 Z) (hg : s ≫ g = 𝟙 Z) (V : Over Z)
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V) :
    (Over.pullback s).map φ ≫ (iteratedPullbackIsoSelf g s hg V).hom =
        (iteratedPullbackIsoSelf f s hf V).hom ↔
      ∀ (T : C) (t : T ⟶ Z) (v : T ⟶ V.left) (h : v ≫ V.hom = t),
        action φ (t ≫ s) v (by simpa [Category.assoc, hf] using h) = v := by
  constructor
  · intro H T t v h
    let q : T ⟶ ((Over.pullback s).obj ((Over.pullback f).obj V)).left :=
      pullback.lift (pullback.lift v (t ≫ s) (by simpa [Category.assoc, hf] using h))
        t (by simp)
    have H' := congrArg (fun k ↦ q ≫ k.left) H
    simp only [Over.comp_left, iteratedPullbackIsoSelf_left] at H'
    rw [action_pullback] at H'
    simpa [q] using H'
  · intro H
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, iteratedPullbackIsoSelf_left]
    have H' := H _ (pullback.snd ((Over.pullback f).obj V).hom s)
      (pullback.fst ((Over.pullback f).obj V).hom s ≫ pullback.fst V.hom f)
      (by simp [Category.assoc, pullback.condition, pullback.condition_assoc, hf])
    have Hq := action_pullback φ s (q := 𝟙 _)
    simp only [Category.id_comp] at Hq
    exact Hq.trans H'

/-- Two points of an iterated base change are equal when their composite first projections and
their second projections agree. -/
lemma iterated_hom_ext {A B Z T : C} (f : A ⟶ B) (g : B ⟶ Z)
    (V : Over Z) (q r : T ⟶ ((Over.pullback f).obj ((Over.pullback g).obj V)).left)
    (h₁ : q ≫ pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g =
      r ≫ pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g)
    (h₂ : q ≫ pullback.snd ((Over.pullback g).obj V).hom f =
      r ≫ pullback.snd ((Over.pullback g).obj V).hom f) : q = r := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h₁
    · change (q ≫ pullback.fst ((Over.pullback g).obj V).hom f) ≫
        ((Over.pullback g).obj V).hom =
        (r ≫ pullback.fst ((Over.pullback g).obj V).hom f) ≫ ((Over.pullback g).obj V).hom
      simpa only [Category.assoc, pullback.condition, pullback.condition_assoc] using
        congrArg (· ≫ f) h₂
  · exact h₂

/-- The identification `iteratedPullbackIsoOfCompEq` commutes with the second projections. -/
@[reassoc] lemma comparison_snd {A B B' Z : C}
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' : B' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (V : Over Z) :
    (iteratedPullbackIsoOfCompEq f g f' g' h V).hom.left ≫
        pullback.snd ((Over.pullback g').obj V).hom f' =
      pullback.snd ((Over.pullback g).obj V).hom f :=
  Over.w _

/-- The base change of `φ` along `f'`, precomposed with `iteratedPullbackIsoOfCompEq`, acts on a
point of the iterated base change by the action of `φ` on its image. -/
lemma comparison_action {A B B' Z T : C}
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A ⟶ B') (g' k : B' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (V : Over Z)
    (φ : (Over.pullback g').obj V ⟶ (Over.pullback k).obj V)
    (q : T ⟶ ((Over.pullback f).obj ((Over.pullback g).obj V)).left) :
    q ≫ (iteratedPullbackIsoOfCompEq f g f' g' h V).hom.left ≫
        ((Over.pullback f').map φ).left ≫
        pullback.fst ((Over.pullback k).obj V).hom f' ≫ pullback.fst V.hom k =
      action φ (q ≫ pullback.snd ((Over.pullback g).obj V).hom f ≫ f')
        (q ≫ pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g)
        (by simp [pullback.condition, pullback.condition_assoc, Category.assoc, ← h]) := by
  have H := action_pullback φ f'
    (q := q ≫ (iteratedPullbackIsoOfCompEq f g f' g' h V).hom.left)
  simpa only [Category.assoc, comparison_snd_assoc, iteratedPullbackIsoOfCompEq_fst] using H

/-- The cocycle condition for `φ` over a triple of maps `a`, `b`, `c` holds if and only if, on
points, acting along `b` equals acting along `a` and then along `c`. -/
lemma cocycle_iff_action {A B Z : C} (f g : A ⟶ Z) (a b c : B ⟶ A)
    (hab : a ≫ f = b ≫ f) (hac : a ≫ g = c ≫ f) (hcb : c ≫ g = b ≫ g)
    (V : Over Z) (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V) :
    (iteratedPullbackIsoOfCompEq a f b f hab V).hom ≫ (Over.pullback b).map φ =
      (Over.pullback a).map φ ≫ (iteratedPullbackIsoOfCompEq a g c f hac V).hom ≫
        (Over.pullback c).map φ ≫ (iteratedPullbackIsoOfCompEq c g b g hcb V).hom ↔
      ∀ (T : C) (t : T ⟶ B) (v : T ⟶ V.left) (h : v ≫ V.hom = t ≫ a ≫ f),
        action φ (t ≫ b) v (by simpa [Category.assoc, ← hab] using h) =
          action φ (t ≫ c) (action φ (t ≫ a) v (by simpa [Category.assoc] using h))
            (by simpa [Category.assoc, ← hac] using (action_base φ (t ≫ a) v
              (by simpa [Category.assoc] using h))) := by
  let L := (iteratedPullbackIsoOfCompEq a f b f hab V).hom ≫ (Over.pullback b).map φ
  let R := (Over.pullback a).map φ ≫ (iteratedPullbackIsoOfCompEq a g c f hac V).hom ≫
    (Over.pullback c).map φ ≫ (iteratedPullbackIsoOfCompEq c g b g hcb V).hom
  have evalL {T : C} (q : T ⟶ ((Over.pullback a).obj ((Over.pullback f).obj V)).left) :
      q ≫ L.left ≫ pullback.fst ((Over.pullback g).obj V).hom b ≫ pullback.fst V.hom g =
        action φ (q ≫ pullback.snd ((Over.pullback f).obj V).hom a ≫ b)
          (q ≫ pullback.fst ((Over.pullback f).obj V).hom a ≫ pullback.fst V.hom f)
          (by simp [Category.assoc, pullback.condition, pullback.condition_assoc, ← hab]) := by
    simpa only [L, Over.comp_left, Category.assoc] using
      comparison_action a f b f g hab V φ q
  have evalR {T : C} (q : T ⟶ ((Over.pullback a).obj ((Over.pullback f).obj V)).left) :
      q ≫ R.left ≫ pullback.fst ((Over.pullback g).obj V).hom b ≫ pullback.fst V.hom g =
        action φ (q ≫ pullback.snd ((Over.pullback f).obj V).hom a ≫ c)
          (action φ (q ≫ pullback.snd ((Over.pullback f).obj V).hom a ≫ a)
            (q ≫ pullback.fst ((Over.pullback f).obj V).hom a ≫ pullback.fst V.hom f)
            (by simp [Category.assoc, pullback.condition, pullback.condition_assoc]))
          (by simpa [Category.assoc, ← hac] using (action_base φ
            (q ≫ pullback.snd ((Over.pullback f).obj V).hom a ≫ a)
            (q ≫ pullback.fst ((Over.pullback f).obj V).hom a ≫ pullback.fst V.hom f)
            (by simp [Category.assoc, pullback.condition, pullback.condition_assoc]))) := by
    have H := comparison_action a g c f g hac V φ (q ≫ ((Over.pullback a).map φ).left)
    have hw : ((Over.pullback a).map φ).left ≫
        pullback.snd ((Over.pullback g).obj V).hom a =
        pullback.snd ((Over.pullback f).obj V).hom a := Over.w _
    simp only [Category.assoc] at H
    conv at H => rhs; simp only [reassoc_of% hw, action_pullback]
    simpa only [R, Over.comp_left, Category.assoc, iteratedPullbackIsoOfCompEq_fst] using H
  constructor
  · intro H T t v h
    let q : T ⟶ ((Over.pullback a).obj ((Over.pullback f).obj V)).left :=
      pullback.lift (pullback.lift v (t ≫ a) (by simpa [Category.assoc] using h)) t (by simp)
    have H' : q ≫ L.left ≫ pullback.fst ((Over.pullback g).obj V).hom b ≫
        pullback.fst V.hom g = q ≫ R.left ≫
        pullback.fst ((Over.pullback g).obj V).hom b ≫ pullback.fst V.hom g := by
      rw [show L = R from H]
    rw [evalL, evalR] at H'
    simpa [q] using H'
  · intro H
    apply Over.OverMorphism.ext
    apply iterated_hom_ext b g V
    · have H' := H _ (pullback.snd ((Over.pullback f).obj V).hom a)
        (pullback.fst ((Over.pullback f).obj V).hom a ≫ pullback.fst V.hom f)
        (by simp [Category.assoc, pullback.condition, pullback.condition_assoc])
      have HL := evalL (𝟙 _)
      have HR := evalR (𝟙 _)
      simp only [Category.id_comp] at HL HR
      exact HL.trans (H'.trans HR.symm)
    · exact (Over.w L).trans (Over.w R).symm

/-- The `i`-th vertex of the standard simplex `n`, as a map from `⦋0⦌`. -/
def vertex {n : SimplexCategory} (i : Fin (n.len + 1)) : ⦋0⦌ ⟶ n :=
  ⦋0⦌.const n i

/-- The edge of the standard simplex `n` from the vertex `i` to the vertex `j`, for `i ≤ j`, as a
map from `⦋1⦌`. -/
def edge {n : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j) : ⦋1⦌ ⟶ n :=
  SimplexCategory.mkOfLe i j h

/-- The image of the vertex `i` under a map of simplices `f` is the vertex `f i`. -/
lemma vertex_comp {n m : SimplexCategory} (i : Fin (n.len + 1)) (f : n ⟶ m) :
    vertex i ≫ f = vertex (f.toOrderHom i) := by
  apply SimplexCategory.Hom.ext_zero_left
  rfl

/-- The image of the edge from `i` to `j` under a map of simplices `f` is the edge from `f i` to
`f j`. -/
lemma edge_comp {n m : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j)
    (f : n ⟶ m) : edge i j h ≫ f =
      edge (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone h) := by
  apply SimplexCategory.Hom.ext_one_left <;> rfl

/-- The source of the edge from `i` to `j` is the vertex `i`. -/
lemma edge_source {n : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j) :
    SimplexCategory.δ (1 : Fin 2) ≫ edge i j h = vertex i := by
  apply SimplexCategory.Hom.ext_zero_left
  rfl

/-- The target of the edge from `i` to `j` is the vertex `j`. -/
lemma edge_target {n : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j) :
    SimplexCategory.δ (0 : Fin 2) ≫ edge i j h = vertex j := by
  apply SimplexCategory.Hom.ext_zero_left
  rfl

/-- The degenerate edge at `i` is the degeneracy followed by the vertex `i`. -/
lemma edge_self {n : SimplexCategory} (i : Fin (n.len + 1)) :
    edge i i le_rfl = SimplexCategory.σ (0 : Fin 1) ≫ vertex i := by
  apply SimplexCategory.Hom.ext_one_left <;> rfl

omit [HasPullbacks C] in
/-- Restricting along the edge from `i` to `j` and then to its source is restricting to the vertex
`i`. -/
lemma map_edge_source (X : SimplicialObject C) {n : SimplexCategory}
    (i j : Fin (n.len + 1)) (h : i ≤ j) :
    X.map (edge i j h).op ≫ X.δ (1 : Fin 2) = X.map (vertex i).op := by
  change X.map (edge i j h).op ≫ X.map (SimplexCategory.δ (1 : Fin 2)).op = _
  rw [← X.map_comp, ← op_comp, edge_source]

omit [HasPullbacks C] in
/-- Restricting along the edge from `i` to `j` and then to its target is restricting to the vertex
`j`. -/
lemma map_edge_target (X : SimplicialObject C) {n : SimplexCategory}
    (i j : Fin (n.len + 1)) (h : i ≤ j) :
    X.map (edge i j h).op ≫ X.δ (0 : Fin 2) = X.map (vertex j).op := by
  change X.map (edge i j h).op ≫ X.map (SimplexCategory.δ (0 : Fin 2)).op = _
  rw [← X.map_comp, ← op_comp, edge_target]

/-- The action of the transition isomorphism of a descent datum along the edge from `i` to `j` of
an `n`-simplex: a point `t` of `Xₙ` and a point `v` of `V` over the vertex `i` of `t` give a
point of `V` over the vertex `j` of `t`. -/
noncomputable def edgeAction {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {T : C} (t : T ⟶ X.obj (Opposite.op n))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) : T ⟶ D.V.left :=
  action D.iso.hom (t ≫ X.map (edge i j hij).op) v
    (by simpa [Category.assoc, map_edge_source] using hv)

/-- The image of the action along the edge from `i` to `j` lies over the vertex `j`. -/
lemma edgeAction_base {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {T : C} (t : T ⟶ X.obj (Opposite.op n))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) :
    edgeAction D t i j hij v hv ≫ D.V.hom = t ≫ X.map (vertex j).op := by
  simpa only [edgeAction, Category.assoc, map_edge_target] using
    action_base D.iso.hom (t ≫ X.map (edge i j hij).op) v
      (by simpa [Category.assoc, map_edge_source] using hv)

/-- The action along a degenerate edge is the identity. -/
lemma edgeAction_self {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {T : C} (t : T ⟶ X.obj (Opposite.op n))
    (i : Fin (n.len + 1)) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) :
    edgeAction D t i i le_rfl v hv = v := by
  have H := (unit_iff_action _ _ _ _ _ _ _).mp D.unit T (t ≫ X.map (vertex i).op) v hv
  simpa [edgeAction, edge_self, op_comp, X.map_comp, Category.assoc,
    SimplicialObject.σ] using H

/-- The action along an edge commutes with precomposition of the points. -/
lemma edgeAction_precomp {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {S T : C} (a : S ⟶ T) (t : T ⟶ X.obj (Opposite.op n))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) :
    edgeAction D (a ≫ t) i j hij (a ≫ v)
      (by simpa [Category.assoc] using congrArg (a ≫ ·) hv) = a ≫ edgeAction D t i j hij v hv := by
  simpa only [edgeAction, Category.assoc] using
    action_precomp D.iso.hom a (t ≫ X.map (edge i j hij).op) v
      (by simpa [Category.assoc, map_edge_source] using hv)

/-- The action along an edge of the restriction of a simplex along `f` is the action along the
image of that edge under `f`. -/
lemma edgeAction_map {X : SimplicialObject C} (D : DescentDatum X)
    {n m : SimplexCategory} (f : n ⟶ m) {T : C} (t : T ⟶ X.obj (Opposite.op m))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = (t ≫ X.map f.op) ≫ X.map (vertex i).op) :
    edgeAction D (t ≫ X.map f.op) i j hij v hv =
      edgeAction D t (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone hij) v
        (by simpa [Category.assoc, ← X.map_comp, ← op_comp, vertex_comp] using hv) := by
  simp only [edgeAction, Category.assoc, ← X.map_comp, ← op_comp, edge_comp]

/-- The action along the edge from `i` to `k` is the action along the edge from `i` to `j` followed
by the action along the edge from `j` to `k`. -/
lemma edgeAction_trans {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {T : C} (t : T ⟶ X.obj (Opposite.op n))
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) :
    edgeAction D t i k (hij.trans hjk) v hv =
      edgeAction D t j k hjk (edgeAction D t i j hij v hv)
        (edgeAction_base D t i j hij v hv) := by
  let τ : ⦋2⦌ ⟶ n := SimplexCategory.mkOfLeComp i j k hij hjk
  have h₂ : SimplexCategory.δ (2 : Fin 3) ≫ τ = edge i j hij := by
    apply SimplexCategory.Hom.ext_one_left <;> rfl
  have h₁ : SimplexCategory.δ (1 : Fin 3) ≫ τ = edge i k (hij.trans hjk) := by
    apply SimplexCategory.Hom.ext_one_left <;> rfl
  have h₀ : SimplexCategory.δ (0 : Fin 3) ≫ τ = edge j k hjk := by
    apply SimplexCategory.Hom.ext_one_left <;> rfl
  have H := (cocycle_iff_action _ _ _ _ _ _ _ _ _ _).mp D.cocycle
    T (t ≫ X.map τ.op) v
    (by simpa [Category.assoc, SimplicialObject.δ, ← X.map_comp, ← op_comp,
      h₂, edge_source] using hv)
  simpa only [edgeAction, Category.assoc, SimplicialObject.δ, ← X.map_comp,
    ← op_comp, h₁, h₂, h₀] using H

/-- The initial vertex of a simplex. -/
abbrev firstVertex (n : SimplexCategoryᵒᵖ) : ⦋0⦌ ⟶ n.unop :=
  vertex (0 : Fin (n.unop.len + 1))

/-- The degree-`n` object of the simplicial object reconstructed from a descent datum: the base
change of `V` along the initial-vertex map `Xₙ ⟶ X₀`. -/
noncomputable abbrev reconstructionObj {X : SimplicialObject C} (D : DescentDatum X)
    (n : SimplexCategoryᵒᵖ) := pullback D.V.hom (X.map (firstVertex n).op)

/-- The projection of the reconstructed degree-`n` object to `Xₙ`. -/
noncomputable abbrev reconstructionBase {X : SimplicialObject C} (D : DescentDatum X)
    (n : SimplexCategoryᵒᵖ) : reconstructionObj D n ⟶ X.obj n :=
  pullback.snd _ _

/-- The projection of the reconstructed degree-`n` object to `V`. -/
noncomputable abbrev reconstructionValue {X : SimplicialObject C} (D : DescentDatum X)
    (n : SimplexCategoryᵒᵖ) : reconstructionObj D n ⟶ D.V.left :=
  pullback.fst _ _

omit [HasPullbacks C] in
/-- Restricting along `f` and then to the vertex `i` is restricting to the vertex `f i`. -/
@[reassoc] lemma map_vertex_comp (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (i : Fin (m.unop.len + 1)) :
    X.map f ≫ X.map (vertex i).op = X.map (vertex (f.unop.toOrderHom i)).op := by
  rw [← X.map_comp]
  congr 1

/-- The action along an edge of the image of a simplex under `X.map f` is the action along the
image of that edge under `f`. -/
lemma edgeAction_map_op {X : SimplicialObject C} (D : DescentDatum X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) {T : C} (t : T ⟶ X.obj n)
    (i j : Fin (m.unop.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = (t ≫ X.map f) ≫ X.map (vertex i).op) :
    edgeAction D (t ≫ X.map f) i j hij v hv =
      edgeAction D t (f.unop.toOrderHom i) (f.unop.toOrderHom j)
        (f.unop.toOrderHom.monotone hij) v
        (by simpa only [Category.assoc, map_vertex_comp] using hv) := by
  have H := edgeAction_map D f.unop t i j hij v
    (by simpa only [Quiver.Hom.op_unop] using hv)
  simpa only [Quiver.Hom.op_unop] using H

/-- The structure map of the reconstructed simplicial object along `f : n ⟶ m`: it acts on the
point of `V` along the edge from the initial vertex to the image of the initial vertex of `m`. -/
noncomputable def reconstructionMap {X : SimplicialObject C} (D : DescentDatum X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) : reconstructionObj D n ⟶ reconstructionObj D m :=
  pullback.lift
    (edgeAction D (reconstructionBase D n) 0 (f.unop.toOrderHom 0) (Fin.zero_le _)
      (reconstructionValue D n) (pullback.condition))
    (reconstructionBase D n ≫ X.map f)
    (by
      rw [Category.assoc, map_vertex_comp]
      exact edgeAction_base D (reconstructionBase D n) 0 (f.unop.toOrderHom 0)
        (Fin.zero_le _) (reconstructionValue D n) pullback.condition)

/-- The reconstructed structure maps lie over the structure maps of `X`. -/
@[reassoc] lemma reconstructionMap_base {X : SimplicialObject C} (D : DescentDatum X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    reconstructionMap D f ≫ reconstructionBase D m = reconstructionBase D n ≫ X.map f := by
  simp [reconstructionMap]

/-- The component in `V` of a reconstructed structure map is the action along the edge from the
initial vertex to the image of the initial vertex. -/
@[reassoc] lemma reconstructionMap_value {X : SimplicialObject C} (D : DescentDatum X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    reconstructionMap D f ≫ reconstructionValue D m =
      edgeAction D (reconstructionBase D n) 0 (f.unop.toOrderHom 0) (Fin.zero_le _)
        (reconstructionValue D n) (pullback.condition) := by
  simp [reconstructionMap]

/-- The reconstructed structure map along the identity is the identity. -/
lemma reconstructionMap_id {X : SimplicialObject C} (D : DescentDatum X)
    (n : SimplexCategoryᵒᵖ) : reconstructionMap D (𝟙 n) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [reconstructionMap_value, Category.id_comp]
    exact edgeAction_self D (reconstructionBase D n) 0 (reconstructionValue D n) pullback.condition
  · simp [reconstructionMap_base]

/-- The reconstructed structure maps are compatible with composition. -/
lemma reconstructionMap_comp {X : SimplicialObject C} (D : DescentDatum X)
    {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) :
    reconstructionMap D (f ≫ g) = reconstructionMap D f ≫ reconstructionMap D g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, reconstructionMap_value]
    rw [← edgeAction_precomp]
    simp only [reconstructionMap_base, reconstructionMap_value]
    rw [edgeAction_map_op]
    exact edgeAction_trans D (reconstructionBase D n) 0 (f.unop.toOrderHom 0)
      (f.unop.toOrderHom (g.unop.toOrderHom 0)) (Fin.zero_le _)
      (f.unop.toOrderHom.monotone (Fin.zero_le _)) (reconstructionValue D n) pullback.condition
  · simp [reconstructionMap_base, reconstructionMap_base_assoc, X.map_comp]

/-- The simplicial object reconstructed from a descent datum. -/
noncomputable def reconstruction {X : SimplicialObject C} (D : DescentDatum X) :
    SimplicialObject C where
  obj := reconstructionObj D
  map := reconstructionMap D
  map_id := reconstructionMap_id D
  map_comp := reconstructionMap_comp D

/-- The projection of the reconstructed simplicial object to `X`. -/
noncomputable def reconstructionProjection {X : SimplicialObject C} (D : DescentDatum X) :
    reconstruction D ⟶ X where
  app := reconstructionBase D
  naturality _ _ f := reconstructionMap_base D f

/-- The action of an isomorphism is injective on points over a fixed point of the base. -/
lemma action_injective {A Z : C} {f g : A ⟶ Z} {V : Over Z}
    (φ : (Over.pullback f).obj V ≅ (Over.pullback g).obj V)
    {T : C} (t : T ⟶ A) (v w : T ⟶ V.left)
    (hv : v ≫ V.hom = t ≫ f) (hw : w ≫ V.hom = t ≫ f)
    (H : action φ.hom t v hv = action φ.hom t w hw) : v = w := by
  have h : pullback.lift v t hv ≫ φ.hom.left = pullback.lift w t hw ≫ φ.hom.left := by
    rw [← action_lift, ← action_lift]
    congr 1
  have hi : IsIso φ.hom.left :=
    ⟨⟨φ.inv.left, congrArg CommaMorphism.left φ.hom_inv_id,
      congrArg CommaMorphism.left φ.inv_hom_id⟩⟩
  have h' := (cancel_mono φ.hom.left).mp h
  simpa using congrArg (· ≫ pullback.fst V.hom f) h'

/-- The structure squares of the reconstructed simplicial object over `X` are pullback squares. -/
lemma reconstruction_equifibered {X : SimplicialObject C} (D : DescentDatum X) :
    (reconstructionProjection D).Equifibered := by
  intro n m f
  apply IsPullback.mk' (reconstructionMap_base D f)
  · intro T q r h₁ h₂
    apply pullback.hom_ext
    · have H := congrArg (· ≫ reconstructionValue D m) h₁
      simp only [Category.assoc, reconstructionMap_value] at H
      rw [← edgeAction_precomp, ← edgeAction_precomp] at H
      simp only [edgeAction, Category.assoc] at H
      simp only [← Category.assoc, h₂] at H
      exact action_injective D.iso _ _ _ _ _ H
    · exact h₂
  · intro T a b h
    let t := b ≫ X.map (edge 0 (f.unop.toOrderHom 0) (Fin.zero_le _)).op
    have ha : (a ≫ reconstructionValue D m) ≫ D.V.hom = t ≫ X.δ (0 : Fin 2) := by
      dsimp [t]
      simp only [Category.assoc, map_edge_target]
      simpa only [Category.assoc, pullback.condition, map_vertex_comp] using
        congrArg (· ≫ X.map (firstVertex m).op) h
    let v := action D.iso.inv t (a ≫ reconstructionValue D m) ha
    have hv : v ≫ D.V.hom = b ≫ X.map (firstVertex n).op := by
      simpa [v, t, Category.assoc, map_edge_source] using
        action_base D.iso.inv t (a ≫ reconstructionValue D m) ha
    refine ⟨pullback.lift v b hv, ?_, by simp⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, reconstructionMap_value]
      rw [← edgeAction_precomp]
      simp only [pullback.lift_snd, pullback.lift_fst]
      exact action_inv D.iso.symm t (a ≫ reconstructionValue D m) ha
    · change (pullback.lift v b hv ≫ reconstructionMap D f) ≫ reconstructionBase D m = _
      rw [Category.assoc, reconstructionMap_base, pullback.lift_snd_assoc]
      exact h.symm

/-- The reconstructed simplicial object, as a cartesian object over `X`. -/
noncomputable def reconstructedCartesian {X : SimplicialObject C} (D : DescentDatum X) :
    ObjectProperty.FullSubcategory (fun Y : Over X ↦ Y.hom.Equifibered) :=
  ⟨Over.mk (reconstructionProjection D), reconstruction_equifibered D⟩

/-- The category of cartesian simplicial objects over `X`: simplicial objects over `X` whose
structure squares are pullback squares. -/
abbrev Cartesian (X : SimplicialObject C) :=
  ObjectProperty.FullSubcategory (fun Y : Over X ↦ Y.hom.Equifibered)

/-- For a cartesian object `Y` over `X`, the identification of `Yₙ` with the base change of `Yₘ`
along `X.map f`. -/
noncomputable def cartesianMapIso {X : SimplicialObject C} (Y : Cartesian X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    Over.mk (Y.1.hom.app n) ≅ (Over.pullback (X.map f)).obj (Over.mk (Y.1.hom.app m)) :=
  Over.isoMk ((Y.2 f).isoIsPullback _ _ (IsPullback.of_hasPullback _ _))
    ((Y.2 f).isoIsPullback_hom_snd _ _ _)

/-- The first projection of `cartesianMapIso` is the structure map of `Y` along `f`. -/
@[reassoc] lemma cartesianMapIso_fst {X : SimplicialObject C} (Y : Cartesian X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (cartesianMapIso Y f).hom.left ≫ pullback.fst (Y.1.hom.app m) (X.map f) =
      Y.1.left.map f := by simp [cartesianMapIso]

/-- The second projection of `cartesianMapIso` is the map `Yₙ ⟶ Xₙ`. -/
@[reassoc] lemma cartesianMapIso_snd {X : SimplicialObject C} (Y : Cartesian X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (cartesianMapIso Y f).hom.left ≫ pullback.snd (Y.1.hom.app m) (X.map f) =
      Y.1.hom.app n := by simp [cartesianMapIso]

/-- The transition isomorphism of a cartesian object over `X`: the two identifications of `Y₁` with
base changes of `Y₀` along the faces `X₁ ⟶ X₀`. -/
noncomputable def cartesianTransition {X : SimplicialObject C} (Y : Cartesian X) :
    (Over.pullback (X.δ (1 : Fin 2))).obj (Over.mk (Y.1.hom.app (Opposite.op ⦋0⦌))) ≅
      (Over.pullback (X.δ (0 : Fin 2))).obj (Over.mk (Y.1.hom.app (Opposite.op ⦋0⦌))) :=
  (cartesianMapIso Y (SimplexCategory.δ (1 : Fin 2)).op).symm ≪≫
    cartesianMapIso Y (SimplexCategory.δ (0 : Fin 2)).op

/-- The transition isomorphism of a cartesian object sends the face `δ 1` of a point `y` of `Y₁`
to its face `δ 0`. -/
lemma cartesian_action {X : SimplicialObject C} (Y : Cartesian X)
    {T : C} (y : T ⟶ Y.1.left.obj (Opposite.op ⦋1⦌)) :
    action (cartesianTransition Y).hom (y ≫ Y.1.hom.app (Opposite.op ⦋1⦌))
      (y ≫ Y.1.left.δ (1 : Fin 2))
      (by simpa only [Category.assoc, SimplicialObject.δ, Over.mk_hom] using
        congrArg (y ≫ ·) (Y.1.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)) =
      y ≫ Y.1.left.δ (0 : Fin 2) := by
  let e := cartesianMapIso Y (SimplexCategory.δ (1 : Fin 2)).op
  have hl : pullback.lift (y ≫ Y.1.left.δ (1 : Fin 2))
      (y ≫ Y.1.hom.app (Opposite.op ⦋1⦌))
      (by simpa only [Category.assoc, SimplicialObject.δ, Over.mk_hom] using
        congrArg (y ≫ ·) (Y.1.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op)) =
        y ≫ e.hom.left := by
    apply pullback.hom_ext <;>
      simp only [e, Category.assoc, Over.mk_hom, SimplicialObject.δ, pullback.lift_fst,
        pullback.lift_snd, cartesianMapIso_fst, cartesianMapIso_snd]
  have hi : e.hom.left ≫ e.inv.left = 𝟙 _ := congrArg CommaMorphism.left e.hom_inv_id
  dsimp only [action, cartesianTransition, Iso.trans_hom, Iso.symm_hom, Over.comp_left]
  change pullback.lift _ _ _ ≫ (e.inv.left ≫
    (cartesianMapIso Y (SimplexCategory.δ (0 : Fin 2)).op).hom.left) ≫ _ = _
  rw [hl]
  simp only [Category.assoc, reassoc_of% hi, Over.mk_hom, SimplicialObject.δ,
    cartesianMapIso_fst]

/-- The descent datum of a cartesian object over `X`: its degree-zero object and its transition
isomorphism. -/
noncomputable def cartesianDatum {X : SimplicialObject C} (Y : Cartesian X) :
    DescentDatum X where
  V := Over.mk (Y.1.hom.app (Opposite.op ⦋0⦌))
  iso := cartesianTransition Y
  unit := by
    apply (unit_iff_action _ _ _ _ _ _ _).mpr
    intro T t v h
    have H := cartesian_action Y (v ≫ Y.1.left.σ (0 : Fin 1))
    have h₀ : (v ≫ Y.1.left.σ (0 : Fin 1)) ≫ Y.1.left.δ (0 : Fin 2) = v := by
      simpa only [Category.assoc, Fin.castSucc_zero] using
        ((congrArg (v ≫ ·) (Y.1.left.δ_comp_σ_self (i := (0 : Fin 1)))).trans (Category.comp_id v))
    have h₁ : (v ≫ Y.1.left.σ (0 : Fin 1)) ≫ Y.1.left.δ (1 : Fin 2) = v := by
      simpa only [Category.assoc, Fin.succ_zero_eq_one] using
        ((congrArg (v ≫ ·) (Y.1.left.δ_comp_σ_succ (i := (0 : Fin 1)))).trans (Category.comp_id v))
    have ht : (v ≫ Y.1.left.σ (0 : Fin 1)) ≫ Y.1.hom.app (Opposite.op ⦋1⦌) =
        t ≫ X.σ (0 : Fin 1) := by
      change (v ≫ Y.1.left.map (SimplexCategory.σ (0 : Fin 1)).op) ≫ _ = _
      rw [Category.assoc, Y.1.hom.naturality, ← Category.assoc]
      exact congrArg (· ≫ X.σ (0 : Fin 1)) h
    simpa only [h₀, h₁, ht] using H
  cocycle := by
    apply (cocycle_iff_action _ _ _ _ _ _ _ _ _ _).mpr
    intro T t v h
    let f := (SimplexCategory.δ (2 : Fin 3)).op ≫ (SimplexCategory.δ (1 : Fin 2)).op
    let y := (Y.2 f).lift v t
      (by simpa only [f, Functor.map_comp, Category.assoc, SimplicialObject.δ, Over.mk_hom]
        using h)
    have hy : y ≫ Y.1.hom.app (Opposite.op ⦋2⦌) = t := (Y.2 f).lift_snd _ _ _
    have hv : y ≫ Y.1.left.δ (2 : Fin 3) ≫ Y.1.left.δ (1 : Fin 2) = v := by
      simpa only [y, f, Functor.map_comp, Category.assoc, SimplicialObject.δ] using
        (Y.2 f).lift_fst v t
          (by simpa only [f, Functor.map_comp, Category.assoc, SimplicialObject.δ, Over.mk_hom]
            using h)
    have hb : y ≫ Y.1.left.δ (1 : Fin 3) ≫ Y.1.left.δ (1 : Fin 2) = v :=
      (congrArg (y ≫ ·) (Y.1.left.δ_comp_δ_self (i := (1 : Fin 2)))).trans hv
    have hc : y ≫ Y.1.left.δ (2 : Fin 3) ≫ Y.1.left.δ (0 : Fin 2) =
        y ≫ Y.1.left.δ (0 : Fin 3) ≫ Y.1.left.δ (1 : Fin 2) :=
      congrArg (y ≫ ·) (Y.1.left.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by simp))
    have hend : y ≫ Y.1.left.δ (0 : Fin 3) ≫ Y.1.left.δ (0 : Fin 2) =
        y ≫ Y.1.left.δ (1 : Fin 3) ≫ Y.1.left.δ (0 : Fin 2) :=
      congrArg (y ≫ ·) (Y.1.left.δ_comp_δ_self (i := (0 : Fin 2)))
    have ht (i : Fin 3) : (y ≫ Y.1.left.δ i) ≫ Y.1.hom.app (Opposite.op ⦋1⦌) = t ≫ X.δ i := by
      change (y ≫ Y.1.left.map (SimplexCategory.δ i).op) ≫ _ = _
      rw [Category.assoc, Y.1.hom.naturality, ← Category.assoc, hy]
      rfl
    have H₂ := cartesian_action Y (y ≫ Y.1.left.δ (2 : Fin 3))
    have H₁ := cartesian_action Y (y ≫ Y.1.left.δ (1 : Fin 3))
    have H₀ := cartesian_action Y (y ≫ Y.1.left.δ (0 : Fin 3))
    simp only [ht, Category.assoc, hv, hb, hc] at H₂ H₁ H₀
    simp only [H₂, H₁, H₀, hend]

/-- A morphism `a` over the base intertwines `φ` and `ψ` if and only if it intertwines their
actions on points. -/
lemma action_compatibility {A Z : C} (f g : A ⟶ Z) {V W : Over Z}
    (φ : (Over.pullback f).obj V ⟶ (Over.pullback g).obj V)
    (ψ : (Over.pullback f).obj W ⟶ (Over.pullback g).obj W) (a : V ⟶ W) :
    (Over.pullback f).map a ≫ ψ = φ ≫ (Over.pullback g).map a ↔
      ∀ (T : C) (t : T ⟶ A) (v : T ⟶ V.left) (hv : v ≫ V.hom = t ≫ f),
        action ψ t (v ≫ a.left) (by simpa [Category.assoc] using hv) =
          action φ t v hv ≫ a.left := by
  constructor
  · intro H T t v hv
    have hl : pullback.lift v t hv ≫ ((Over.pullback f).map a).left =
        pullback.lift (v ≫ a.left) t (by simpa [Category.assoc] using hv) := by
      apply pullback.hom_ext <;> simp [Over.pullback_map_left]
    have H' := congrArg (fun k ↦ pullback.lift v t hv ≫ k.left ≫ pullback.fst W.hom g) H
    simp only [Over.comp_left, Category.assoc] at H'
    rw [← Category.assoc (pullback.lift v t hv), hl] at H'
    simpa only [action, Over.pullback_map_left, Over.homMk_left,
      pullback.lift_fst, Category.assoc] using H'
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [action, Over.pullback_map_left] using
        H _ (pullback.snd V.hom f) (pullback.fst V.hom f) pullback.condition
    · exact (Over.w ((Over.pullback f).map a ≫ ψ)).trans
        (Over.w (φ ≫ (Over.pullback g).map a)).symm

/-- The morphism of descent data induced by a morphism of cartesian objects. -/
noncomputable def cartesianDatumMap {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : Y ⟶ Z) : cartesianDatum Y ⟶ cartesianDatum Z where
  hom := Over.homMk (a.hom.left.app (Opposite.op ⦋0⦌))
    (congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌)) (Over.w a.hom))
  comm := by
    apply (action_compatibility _ _ _ _ _).mpr
    intro T t v hv
    let hp : IsPullback (Y.1.left.δ (1 : Fin 2))
        (Y.1.hom.app (Opposite.op ⦋1⦌)) (Y.1.hom.app (Opposite.op ⦋0⦌))
        (X.δ (1 : Fin 2)) := Y.2 (SimplexCategory.δ (1 : Fin 2)).op
    let y := hp.lift v t hv
    have hy : y ≫ Y.1.hom.app (Opposite.op ⦋1⦌) = t :=
      hp.lift_snd _ _ _
    have hv' : y ≫ Y.1.left.δ (1 : Fin 2) = v :=
      hp.lift_fst _ _ _
    have Hw (n : SimplexCategoryᵒᵖ) : a.hom.left.app n ≫ Z.1.hom.app n = Y.1.hom.app n :=
      congrArg (fun k ↦ k.app n) (Over.w a.hom)
    have H := cartesian_action Z (y ≫ a.hom.left.app (Opposite.op ⦋1⦌))
    have H' := cartesian_action Y y
    simp only [hy, hv'] at H'
    have HN (i : Fin 2) : (y ≫ a.hom.left.app (Opposite.op ⦋1⦌)) ≫ Z.1.left.δ i =
        (y ≫ Y.1.left.δ i) ≫ a.hom.left.app (Opposite.op ⦋0⦌) :=
      (Category.assoc _ _ _).trans ((congrArg (y ≫ ·)
        (a.hom.left.naturality (SimplexCategory.δ i).op).symm).trans (Category.assoc _ _ _).symm)
    have HB : (y ≫ a.hom.left.app (Opposite.op ⦋1⦌)) ≫ Z.1.hom.app (Opposite.op ⦋1⦌) = t := by
      rwa [Category.assoc, Hw]
    simp only [HN, HB, hv'] at H
    simpa only [cartesianDatum, Over.homMk_left, H', Category.assoc] using H

/-- The functor from cartesian objects over `X` to descent data. -/
noncomputable def cartesianToDescent (X : SimplicialObject C) :
    Cartesian X ⥤ DescentDatum X where
  obj := cartesianDatum
  map := cartesianDatumMap
  map_id _ := DescentDatum.Hom.ext _ _ rfl
  map_comp _ _ := DescentDatum.Hom.ext _ _ rfl

/-- The action of the descent datum of a cartesian object along an edge sends the restriction of a
point to the vertex `i` to its restriction to the vertex `j`. -/
lemma cartesian_edgeAction {X : SimplicialObject C} (Y : Cartesian X)
    {n : SimplexCategory} {T : C} (y : T ⟶ Y.1.left.obj (Opposite.op n))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) :
    edgeAction (cartesianDatum Y) (y ≫ Y.1.hom.app (Opposite.op n)) i j hij
      (y ≫ Y.1.left.map (vertex i).op)
      (by simpa only [Category.assoc, cartesianDatum, Over.mk_hom] using
        congrArg (y ≫ ·) (Y.1.hom.naturality (vertex i).op)) =
        y ≫ Y.1.left.map (vertex j).op := by
  have H := cartesian_action Y (y ≫ Y.1.left.map (edge i j hij).op)
  simpa only [edgeAction, cartesianDatum, Category.assoc, Y.1.hom.naturality,
    map_edge_source, map_edge_target] using H

/-- The action along an edge depends on the point of the simplex and the point of the object
over its first vertex, but not on the proof that the two are compatible. -/
lemma edgeAction_congr {X : SimplicialObject C} (D : DescentDatum X)
    {n : SimplexCategory} {T : C} {t t' : T ⟶ X.obj (Opposite.op n)}
    {i j : Fin (n.len + 1)} {hij : i ≤ j} {v v' : T ⟶ D.V.left}
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op)
    (hv' : v' ≫ D.V.hom = t' ≫ X.map (vertex i).op)
    (ht : t = t') (hvv : v = v') :
    edgeAction D t i j hij v hv = edgeAction D t' i j hij v' hv' := by
  subst ht
  subst hvv
  rfl

/-- The edge action of the descent datum of a cartesian object, evaluated on the identity point
of a degree-`n` object. -/
lemma cartesian_edgeAction_id {X : SimplicialObject C} (Y : Cartesian X)
    (n : SimplexCategoryᵒᵖ) (i j : Fin (n.unop.len + 1)) (hij : i ≤ j)
    (hv : Y.1.left.map (vertex i).op ≫ (cartesianDatum Y).V.hom =
      Y.1.hom.app n ≫ X.map (vertex i).op) :
    edgeAction (cartesianDatum Y) (Y.1.hom.app n) i j hij
      (Y.1.left.map (vertex i).op) hv = Y.1.left.map (vertex j).op := by
  have H := cartesian_action Y (Y.1.left.map (edge i j hij).op)
  simpa only [edgeAction, cartesianDatum, Category.assoc, Y.1.hom.naturality,
    map_edge_source, map_edge_target] using H

/-- A morphism of descent data intertwines the actions along an edge. -/
lemma edgeAction_compatibility {X : SimplicialObject C} {D E : DescentDatum X}
    (a : D ⟶ E) {n : SimplexCategory} {T : C} (t : T ⟶ X.obj (Opposite.op n))
    (i j : Fin (n.len + 1)) (hij : i ≤ j) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom = t ≫ X.map (vertex i).op) :
    edgeAction E t i j hij (v ≫ a.hom.left) (by simpa [Category.assoc] using hv) =
      edgeAction D t i j hij v hv ≫ a.hom.left :=
  (action_compatibility _ _ _ _ _).mp a.comm _ _ _ _

/-- The degree-`n` component of the morphism of cartesian objects induced by a morphism of descent
data, defined through the pullback square along the initial vertex. -/
noncomputable def liftDescentMap {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) (n : SimplexCategoryᵒᵖ) :
    Y.1.left.obj n ⟶ Z.1.left.obj n :=
  (Z.2 (firstVertex n).op).lift
    (Y.1.left.map (firstVertex n).op ≫ a.hom.left) (Y.1.hom.app n)
    (by
      have hw : a.hom.left ≫ Z.1.hom.app (Opposite.op ⦋0⦌) =
          Y.1.hom.app (Opposite.op ⦋0⦌) := Over.w a.hom
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => Y.1.left.map (firstVertex n).op ≫ k) hw).trans
          (Y.1.hom.naturality (firstVertex n).op)))

/-- The lifted degree-`n` component lies over `Xₙ`. -/
@[reassoc] lemma liftDescentMap_base {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) (n : SimplexCategoryᵒᵖ) :
    liftDescentMap a n ≫ Z.1.hom.app n = Y.1.hom.app n :=
  (Z.2 (firstVertex n).op).lift_snd _ _ _

/-- The lifted degree-`n` component restricts on the initial vertex to the morphism of descent
data. -/
@[reassoc] lemma liftDescentMap_first {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) (n : SimplexCategoryᵒᵖ) :
    liftDescentMap a n ≫ Z.1.left.map (firstVertex n).op =
      Y.1.left.map (firstVertex n).op ≫ a.hom.left :=
  (Z.2 (firstVertex n).op).lift_fst _ _ _

/-- The lifted degree-`n` component restricts on every vertex to the morphism of descent data. -/
@[reassoc] lemma liftDescentMap_vertex {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    liftDescentMap a n ≫ Z.1.left.map (vertex i).op =
      Y.1.left.map (vertex i).op ≫ a.hom.left := by
  have hY : Y.1.left.map (firstVertex n).op ≫ (cartesianDatum Y).V.hom =
      Y.1.hom.app n ≫ X.map (firstVertex n).op := Y.1.hom.naturality (firstVertex n).op
  have hYa : (Y.1.left.map (firstVertex n).op ≫ a.hom.left) ≫ (cartesianDatum Z).V.hom =
      Y.1.hom.app n ≫ X.map (firstVertex n).op :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => Y.1.left.map (firstVertex n).op ≫ k) (Over.w a.hom)).trans hY)
  have HY := cartesian_edgeAction_id Y n 0 i (Fin.zero_le i) hY
  have H := edgeAction_compatibility a (Y.1.hom.app n) 0 i (Fin.zero_le i)
    (Y.1.left.map (firstVertex n).op) hY
  have HZ := cartesian_edgeAction Z (liftDescentMap a n) 0 i (Fin.zero_le i)
  have HC : edgeAction (cartesianDatum Z) (liftDescentMap a n ≫ Z.1.hom.app n) 0 i
        (Fin.zero_le i) (liftDescentMap a n ≫ Z.1.left.map (firstVertex n).op)
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => liftDescentMap a n ≫ k)
            (Z.1.hom.naturality (firstVertex n).op)).trans
              (Category.assoc _ _ _).symm)) =
      edgeAction (cartesianDatum Z) (Y.1.hom.app n) 0 i (Fin.zero_le i)
        (Y.1.left.map (firstVertex n).op ≫ a.hom.left) hYa :=
    edgeAction_congr _ _ hYa (liftDescentMap_base a n) (liftDescentMap_first a n)
  exact HZ.symm.trans (HC.trans (H.trans (congrArg (· ≫ a.hom.left) HY)))

/-- In degree zero the lifted morphism is the morphism of descent data itself. -/
lemma liftDescentMap_zero {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) :
    liftDescentMap a (Opposite.op ⦋0⦌) = a.hom.left := by
  have hv : (firstVertex (Opposite.op ⦋0⦌)).op = 𝟙 (Opposite.op ⦋0⦌) := by
    have h : firstVertex (Opposite.op ⦋0⦌) = 𝟙 ⦋0⦌ := by
      apply SimplexCategory.Hom.ext_zero_left
      rfl
    rw [h, op_id]
  have h (W : Cartesian X) :
      W.1.left.map (firstVertex (Opposite.op ⦋0⦌)).op = 𝟙 (W.1.left.obj (Opposite.op ⦋0⦌)) := by
    rw [hv, CategoryTheory.Functor.map_id]
  have H := liftDescentMap_first a (Opposite.op ⦋0⦌)
  rw [h, h, Category.comp_id] at H
  exact H.trans (Category.id_comp _)

/-- The morphism of cartesian objects induced by a morphism of descent data. -/
noncomputable def liftDescentHom {X : SimplicialObject C} {Y Z : Cartesian X}
    (a : cartesianDatum Y ⟶ cartesianDatum Z) : Y ⟶ Z :=
  ⟨Over.homMk
    { app := liftDescentMap a
      naturality := by
        intro n m f
        apply (Z.2 (firstVertex m).op).hom_ext
        · simp only [Category.assoc, map_vertex_comp, liftDescentMap_vertex]
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ a.hom.left)
              (map_vertex_comp Y.1.left f (0 : Fin (m.unop.len + 1))))
        · simp only [Category.assoc, liftDescentMap_base, Z.1.hom.naturality,
            liftDescentMap_base_assoc, Y.1.hom.naturality] }
    (by ext n; exact liftDescentMap_base a n)⟩

omit [HasPullbacks C] in
/-- Two morphisms of cartesian objects over `X` are equal when they agree in degree zero. -/
lemma cartesian_hom_ext {X : SimplicialObject C} {Y Z : Cartesian X} (a b : Y ⟶ Z)
    (h : a.hom.left.app (Opposite.op ⦋0⦌) = b.hom.left.app (Opposite.op ⦋0⦌)) : a = b := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  ext n
  apply (Z.2 (firstVertex n).op).hom_ext
  · rw [← a.hom.left.naturality, ← b.hom.left.naturality, h]
  · exact (congrArg (fun k ↦ k.app n) (Over.w a.hom)).trans
      (congrArg (fun k ↦ k.app n) (Over.w b.hom)).symm

/-- The functor from cartesian objects to descent data is fully faithful. -/
noncomputable def cartesianToDescent_fullyFaithful (X : SimplicialObject C) :
    (cartesianToDescent X).FullyFaithful where
  preimage := liftDescentHom
  map_preimage a := DescentDatum.Hom.ext _ _ (Over.OverMorphism.ext (liftDescentMap_zero a))
  preimage_map a := cartesian_hom_ext _ _ (liftDescentMap_zero ((cartesianToDescent X).map a))

/-- An isomorphism of descent data from an isomorphism over `X₀` compatible with the transition
isomorphisms. -/
noncomputable def descentIsoOfIso {X : SimplicialObject C} {D E : DescentDatum X}
    (e : D.V ≅ E.V)
    (h : (Over.pullback (X.δ (1 : Fin 2))).map e.hom ≫ E.iso.hom =
      D.iso.hom ≫ (Over.pullback (X.δ (0 : Fin 2))).map e.hom) : D ≅ E where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    rw [← cancel_mono ((Over.pullback (X.δ (0 : Fin 2))).map e.hom)]
    simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
    rw [← h, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]⟩
  hom_inv_id := DescentDatum.Hom.ext _ _ e.hom_inv_id
  inv_hom_id := DescentDatum.Hom.ext _ _ e.inv_hom_id

/-- The initial vertex of `⦋0⦌` is the identity. -/
lemma firstVertex_zero : firstVertex (Opposite.op ⦋0⦌) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext_zero_left
  rfl

/-- The degree-zero object of the reconstructed cartesian object is isomorphic to `V`. -/
noncomputable def reconstructionZeroIso {X : SimplicialObject C} (D : DescentDatum X) :
    (cartesianDatum (reconstructedCartesian D)).V ≅ D.V := by
  have hv : X.map (firstVertex (Opposite.op ⦋0⦌)).op = 𝟙 _ := by
    rw [firstVertex_zero, op_id, X.map_id]
  have : IsIso (X.map (firstVertex (Opposite.op ⦋0⦌)).op) := by rw [hv]; infer_instance
  have hiso : IsIso (reconstructionValue D (Opposite.op ⦋0⦌)) := by
    have h : IsIso (pullback.fst D.V.hom (X.map (firstVertex (Opposite.op ⦋0⦌)).op)) :=
      inferInstance
    exact h
  exact Over.isoMk (@asIso _ _ _ _ (reconstructionValue D (Opposite.op ⦋0⦌)) hiso)
    (by
      change reconstructionValue D (Opposite.op ⦋0⦌) ≫ D.V.hom =
        reconstructionBase D (Opposite.op ⦋0⦌)
      simpa only [hv, Category.comp_id] using
        (pullback.condition (f := D.V.hom) (g := X.map (firstVertex (Opposite.op ⦋0⦌)).op)))

/-- Over a one-simplex the reconstructed value lies over the first face. -/
lemma reconstruction_condition_one {X : SimplicialObject C} (D : DescentDatum X) :
    reconstructionValue D (Opposite.op ⦋1⦌) ≫ D.V.hom =
      reconstructionBase D (Opposite.op ⦋1⦌) ≫ X.δ (1 : Fin 2) := by
  have he : firstVertex (Opposite.op ⦋1⦌) = SimplexCategory.δ (1 : Fin 2) := by
    apply SimplexCategory.Hom.ext_zero_left
    rfl
  exact pullback.condition.trans (congrArg (reconstructionBase D (Opposite.op ⦋1⦌) ≫ ·)
    (congrArg (fun e ↦ X.map e.op) he))

/-- On the component in `V`, the reconstructed structure map along the face `δ 1` is the
identity, and along the face `δ 0` it is the action of the transition isomorphism. -/
lemma reconstruction_faces {X : SimplicialObject C} (D : DescentDatum X) :
    reconstructionMap D (SimplexCategory.δ (1 : Fin 2)).op ≫
        reconstructionValue D (Opposite.op ⦋0⦌) =
        reconstructionValue D (Opposite.op ⦋1⦌) ∧
    reconstructionMap D (SimplexCategory.δ (0 : Fin 2)).op ≫
        reconstructionValue D (Opposite.op ⦋0⦌) =
      action D.iso.hom (reconstructionBase D (Opposite.op ⦋1⦌))
        (reconstructionValue D (Opposite.op ⦋1⦌)) (reconstruction_condition_one D) := by
  constructor
  · rw [reconstructionMap_value]
    exact edgeAction_self D _ 0 _ _
  · rw [reconstructionMap_value]
    have he : edge (0 : Fin 2) 1 (by decide) = 𝟙 ⦋1⦌ := by
      apply SimplexCategory.Hom.ext_one_left <;> rfl
    change edgeAction D (reconstructionBase D (Opposite.op ⦋1⦌)) 0 1 _
      (reconstructionValue D (Opposite.op ⦋1⦌)) _ = _
    simp only [edgeAction, he, op_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The descent datum of the reconstructed cartesian object is isomorphic to the original descent
datum. -/
noncomputable def reconstructionDatumIso {X : SimplicialObject C} (D : DescentDatum X) :
    cartesianDatum (reconstructedCartesian D) ≅ D := by
  apply descentIsoOfIso (reconstructionZeroIso D)
  apply (action_compatibility _ _ _ _ _).mpr
  intro T t v hv
  let Y := reconstructedCartesian D
  let hp : IsPullback (Y.1.left.δ (1 : Fin 2))
      (Y.1.hom.app (Opposite.op ⦋1⦌)) (Y.1.hom.app (Opposite.op ⦋0⦌))
      (X.δ (1 : Fin 2)) := Y.2 (SimplexCategory.δ (1 : Fin 2)).op
  let y := hp.lift v t hv
  have hy : y ≫ reconstructionBase D (Opposite.op ⦋1⦌) = t := hp.lift_snd _ _ _
  have hyv : y ≫ reconstructionMap D (SimplexCategory.δ (1 : Fin 2)).op = v := hp.lift_fst _ _ _
  have hvy : (y ≫ reconstructionMap D (SimplexCategory.δ (1 : Fin 2)).op) ≫
      (cartesianDatum Y).V.hom =
      (y ≫ reconstructionBase D (Opposite.op ⦋1⦌)) ≫ X.δ (1 : Fin 2) := by
    rwa [hy, hyv]
  have H := cartesian_action Y y
  change action (cartesianTransition Y).hom (y ≫ reconstructionBase D (Opposite.op ⦋1⦌))
    (y ≫ reconstructionMap D (SimplexCategory.δ (1 : Fin 2)).op) hvy =
    y ≫ reconstructionMap D (SimplexCategory.δ (0 : Fin 2)).op at H
  have HY : action (cartesianTransition Y).hom t v hv =
      y ≫ reconstructionMap D (SimplexCategory.δ (0 : Fin 2)).op :=
    (action_congr _ hvy hv hy hyv).symm.trans H
  have hV : v ≫ reconstructionValue D (Opposite.op ⦋0⦌) =
      y ≫ reconstructionValue D (Opposite.op ⦋1⦌) :=
    (congrArg (fun k => k ≫ reconstructionValue D (Opposite.op ⦋0⦌)) hyv).symm.trans
      ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) (reconstruction_faces D).1))
  have hvv0 : (y ≫ reconstructionValue D (Opposite.op ⦋1⦌)) ≫ D.V.hom =
      (y ≫ reconstructionBase D (Opposite.op ⦋1⦌)) ≫ X.δ (1 : Fin 2) :=
    (Category.assoc _ _ _).trans
      ((congrArg (y ≫ ·) (reconstruction_condition_one D)).trans
        (Category.assoc _ _ _).symm)
  have hw : (v ≫ reconstructionValue D (Opposite.op ⦋0⦌)) ≫ D.V.hom =
      t ≫ X.δ (1 : Fin 2) :=
    (congrArg (fun k => k ≫ D.V.hom) hV).trans
      (hvv0.trans (congrArg (fun k => k ≫ X.δ (1 : Fin 2)) hy))
  change action D.iso.hom t (v ≫ reconstructionValue D (Opposite.op ⦋0⦌)) hw =
    action (cartesianTransition Y).hom t v hv ≫ reconstructionValue D (Opposite.op ⦋0⦌)
  calc action D.iso.hom t (v ≫ reconstructionValue D (Opposite.op ⦋0⦌)) hw
      = action D.iso.hom (y ≫ reconstructionBase D (Opposite.op ⦋1⦌))
          (y ≫ reconstructionValue D (Opposite.op ⦋1⦌)) hvv0 :=
        action_congr _ hw hvv0 hy.symm hV
    _ = y ≫ action D.iso.hom (reconstructionBase D (Opposite.op ⦋1⦌))
          (reconstructionValue D (Opposite.op ⦋1⦌)) (reconstruction_condition_one D) :=
        action_precomp _ _ _ _ _
    _ = y ≫ (reconstructionMap D (SimplexCategory.δ (0 : Fin 2)).op ≫
          reconstructionValue D (Opposite.op ⦋0⦌)) :=
        congrArg (y ≫ ·) (reconstruction_faces D).2.symm
    _ = (y ≫ reconstructionMap D (SimplexCategory.δ (0 : Fin 2)).op) ≫
          reconstructionValue D (Opposite.op ⦋0⦌) := (Category.assoc _ _ _).symm
    _ = action (cartesianTransition Y).hom t v hv ≫
          reconstructionValue D (Opposite.op ⦋0⦌) :=
        congrArg (fun k => k ≫ reconstructionValue D (Opposite.op ⦋0⦌)) HY.symm


/-- Cartesian simplicial objects over `X` are equivalent to descent data consisting of an
object over `X₀` and a normalized transition isomorphism satisfying the cocycle condition. -/
@[stacks 07TC]
noncomputable def cartesianObjectsOverEquivalenceDescentData (X : SimplicialObject C) :
    ObjectProperty.FullSubcategory (fun Y : Over X ↦ Y.hom.Equifibered) ≌
      DescentDatum X :=
  by
    let F := cartesianToDescent X
    letI : F.Full := (cartesianToDescent_fullyFaithful X).full
    letI : F.Faithful := (cartesianToDescent_fullyFaithful X).faithful
    letI : F.EssSurj := ⟨fun D ↦ ⟨reconstructedCartesian D, ⟨reconstructionDatumIso D⟩⟩⟩
    letI : F.IsEquivalence := {}
    exact F.asEquivalence

end Stacks.Simplicial.Descent

end
