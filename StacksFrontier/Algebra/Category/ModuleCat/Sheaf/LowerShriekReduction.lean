module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek

/-!
# Exactness of lower shriek along a functor of sites with reductions

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and let `O` be a sheaf of
rings on `D`. Lower shriek `g_! : Mod(g^{-1}O) ⥤ Mod(O)` of Stacks 0797 is a left adjoint, hence
right exact; this file gives a criterion for it to be *left* exact as well, and therefore exact.

The criterion is on the categories `StructuredArrow V u` of pairs `(c, V ⟶ u c)`, which are what
the left Kan extension computing `g_!` is a colimit over: it asks every connected component of
`StructuredArrow V u` to have a terminal object, and asks `O` to send the structure arrow of each
of those terminal objects to an isomorphism. Then the sections of `g_!M` over `V` are the direct
sum, over the components, of the sections of `M` at the terminal objects, and a direct sum of
injective maps of modules is injective.

## Main definitions

* `Stacks.Sites.ReducedLowerShriek.Reduction`: the criterion, as a structure carrying the index
  type of the components, their terminal objects, and the two uniqueness properties.
* `Stacks.Sites.ReducedLowerShriek.extensionObj`: the direct-sum presheaf of modules, which the
  reduction data exhibits as lower shriek on presheaves.
* `Stacks.Sites.ReducedLowerShriek.extensionFunctor` and `.extensionAdjunction`: that
  construction as a functor, left adjoint to restriction along `u`.

## Main results

* `Stacks.Sites.ReducedLowerShriek.extensionFunctor_preservesMonos`: the direct-sum extension
  preserves monomorphisms.
* `Stacks.Sites.ReducedLowerShriek.pullback_preservesMonos`: Mathlib's abstract left adjoint
  `PresheafOfModules.pullback` of restriction along `u` preserves monomorphisms.
* `Stacks.Sites.ReducedLowerShriek.lowerShriek_exact`: **lower shriek of sheaves of modules along
  `u` is exact.**

## Implementation notes

A `Reduction` records, for every object `V` of `D`, a type `idx V` indexing the connected
components of `StructuredArrow V u`, a chosen object `pt t` of each component, an assignment
`red s` of a component to each structured arrow, and an arrow `lift s : pt (red s) ⟶ s`. The two
properties `red_eq` and `hom_ext` say that `pt t` is terminal in its component: an arrow out of
`pt t` pins down the component of its target, and arrows out of `pt t` are unique. Everything the
construction needs is derived from those; in particular `liftBack` produces an arrow
`pt t ⟶ s` from an arrow `s ⟶ pt t` in the opposite direction, which is how the unit and the
naturality squares below are built, and no further axiom on the reduction is required.

The field `isIso_map` is what replaces the base change `M(c) ⊗_{O(u c)} O(V)` appearing in the
general formula for lower shriek by the plain module `M(c)`: the summand indexed by `t` is the
module of sections of `M` at `(pt t).right` with `O.obj (op V)` acting through `Reduction.sc t`,
the inverse of the action of `O` on the structure arrow of `pt t`. The compatibility of these
actions with the restriction maps is `Reduction.sc_naturality`, which is the only computation in
this file that uses the ring structure at all.

The direct sum is taken as a categorical coproduct in `ModuleCat (O.obj X)`, exactly as in
`Stacks.Sites.OverModules.extensionPresheaf`, of which the construction here is the
generalisation from `u = Over.forget U` — where the reduction of `(c, V ⟶ u c)` is
`(V ⟶ U, 𝟙 V)` — to an arbitrary `u` with reductions. Every map out of or into a summand whose
source or target needs a change of the acting ring is defined as a bundled (semi)linear map
rather than by transporting an existing morphism, so that its semilinearity is discharged once,
at definition time.

The module universe is written `max i t` for a free `t`, with `i` the universe of the index
types: a coproduct of modules indexed by a type in `Type i` lies in the module universe only when
that universe dominates `i`, which is what `Stacks.Sites.OverModules.mono_sigmaMap` — the form of
Grothendieck's axiom AB4 used here — asks for.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe i t w a v₁ u₁ v₂ u₂

namespace Stacks.Sites.ReducedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Reduction data** for a functor `u : C ⥤ D` and a presheaf of rings `O` on `D`: a type
`idx V` indexing the connected components of the category `StructuredArrow V u` of pairs
`(c, V ⟶ u c)`, together with a terminal object `pt t` of each component, the assignment `red s`
of its component to every structured arrow, and the arrow `lift s` from the terminal object of
that component to `s`.

Terminality is expressed by `red_eq` — an arrow out of `pt t` has target in the component of
`t` — and `hom_ext` — arrows out of `pt t` are unique. The last field asks `O` not to see the
structure arrow of a terminal object. -/
structure Reduction (u : C ⥤ D) (O : Dᵒᵖ ⥤ RingCat.{w}) where
  /-- The index type of the connected components of `StructuredArrow V u`. -/
  idx : D → Type i
  /-- The chosen terminal object of the component indexed by `t`. -/
  pt : ∀ {V : D}, idx V → StructuredArrow V u
  /-- The component of a structured arrow. -/
  red : ∀ {V : D}, StructuredArrow V u → idx V
  /-- The arrow from the terminal object of the component of `s` to `s`. -/
  lift : ∀ {V : D} (s : StructuredArrow V u), pt (red s) ⟶ s
  /-- An arrow out of `pt t` has target in the component indexed by `t`. -/
  red_eq : ∀ {V : D} {t : idx V} {s : StructuredArrow V u}, (pt t ⟶ s) → red s = t
  /-- Arrows out of `pt t` are unique. -/
  hom_ext : ∀ {V : D} {t : idx V} {s : StructuredArrow V u} (g g' : pt t ⟶ s), g = g'
  /-- `O` sends the structure arrow of a terminal object to an isomorphism. -/
  isIso_map : ∀ {V : D} (t : idx V), IsIso (O.map (pt t).hom.op)

namespace Reduction

variable {u : C ⥤ D} {O : Dᵒᵖ ⥤ RingCat.{w}} (R : Reduction.{i} u O)

/-- The chosen terminal object of a component is in that component. -/
lemma red_pt {V : D} (t : R.idx V) : R.red (R.pt t) = t := R.red_eq (𝟙 _)

/-- An arrow of structured arrows does not change the component. -/
lemma red_eq_red {V : D} {s s' : StructuredArrow V u} (g : s ⟶ s') : R.red s' = R.red s :=
  R.red_eq (R.lift s ≫ g)

/-- The arrow from the terminal object indexed by `t` to a structured arrow in that component. -/
noncomputable def liftTo {V : D} {t : R.idx V} (s : StructuredArrow V u) (h : R.red s = t) :
    R.pt t ⟶ s := by
  subst h; exact R.lift s

/-- An arrow `s ⟶ R.pt t` places `s` in the component of `t`, so it is matched by an arrow in
the other direction. -/
noncomputable def liftBack {V : D} {t : R.idx V} {s : StructuredArrow V u} (g : s ⟶ R.pt t) :
    R.pt t ⟶ s :=
  R.liftTo s ((R.red_eq_red g).symm.trans (R.red_pt t))

/-- The ring map transporting sections of `O` over `V` to sections over the image of the terminal
object of the component indexed by `t`: the inverse of the action of `O` on the structure arrow
of that terminal object. -/
noncomputable def sc {V : D} (t : R.idx V) :
    O.obj (op V) ⟶ O.obj (op (u.obj (R.pt t).right)) :=
  @inv _ _ _ _ (O.map (R.pt t).hom.op) (R.isIso_map t)

/-- `Reduction.sc t` is a right inverse of the action of `O` on the structure arrow of the
terminal object indexed by `t`. -/
lemma sc_comp {V : D} (t : R.idx V) : R.sc t ≫ O.map (R.pt t).hom.op = 𝟙 _ :=
  @IsIso.inv_hom_id _ _ _ _ _ (R.isIso_map t)

/-- `Reduction.sc t` is a left inverse of the action of `O` on the structure arrow of the
terminal object indexed by `t`. -/
lemma comp_sc {V : D} (t : R.idx V) : O.map (R.pt t).hom.op ≫ R.sc t = 𝟙 _ :=
  @IsIso.hom_inv_id _ _ _ _ _ (R.isIso_map t)

/-- Applying the action of `O` on the structure arrow to `Reduction.sc t r` recovers `r`. -/
lemma sc_comp_apply {V : D} (t : R.idx V) (r : O.obj (op V)) :
    O.map (R.pt t).hom.op (R.sc t r) = r :=
  ConcreteCategory.congr_hom (R.sc_comp t) r

/-- The transporting ring maps are compatible with restriction: this is the semilinearity that
makes the direct sum below a presheaf of `O`-modules. -/
lemma sc_naturality {V V' : D} (f : V' ⟶ V) {t : R.idx V} {t' : R.idx V'}
    (g : R.pt t' ⟶ StructuredArrow.mk (f ≫ (R.pt t).hom)) :
    R.sc t ≫ O.map (u.map g.right).op = O.map f.op ≫ R.sc t' := by
  have := R.isIso_map t'
  have hw : (R.pt t').hom ≫ u.map g.right = f ≫ (R.pt t).hom := StructuredArrow.w g
  have key : O.map (u.map g.right).op ≫ O.map (R.pt t').hom.op =
      O.map (R.pt t).hom.op ≫ O.map f.op := by
    rw [← O.map_comp, ← O.map_comp]
    exact congrArg O.map (congrArg Quiver.Hom.op hw)
  refine (cancel_mono (O.map (R.pt t').hom.op)).1 ?_
  simp only [Category.assoc, key, reassoc_of% (R.sc_comp t), R.sc_comp t', Category.comp_id]

/-- `Reduction.sc_naturality`, evaluated at a section `r`. -/
lemma sc_naturality_apply {V V' : D} (f : V' ⟶ V) {t : R.idx V} {t' : R.idx V'}
    (g : R.pt t' ⟶ StructuredArrow.mk (f ≫ (R.pt t).hom)) (r : O.obj (op V)) :
    O.map (u.map g.right).op (R.sc t r) = R.sc t' (O.map f.op r) :=
  ConcreteCategory.congr_hom (R.sc_naturality f g) r

end Reduction

section Extension

variable {u : C ⥤ D} {O : Dᵒᵖ ⥤ RingCat.{w}} (R : Reduction.{i} u O)
  (M : PresheafOfModules.{max i t} (u.op ⋙ O))

/-- The family of modules whose direct sum is the value at `X` of the extension: the summand
indexed by a component `s` is the module of sections of `M` at the terminal object of `s`, with
`O.obj X` acting through `Reduction.sc`. -/
noncomputable abbrev summands (X : Dᵒᵖ) : R.idx X.unop → ModuleCat.{max i t, w} (O.obj X) :=
  fun s => (ModuleCat.restrictScalars (R.sc s).hom).obj (M.obj (op (R.pt s).right))

/-- The transport of a section of `M` along an arrow of structured arrows, as a map of
summands. -/
noncomputable def transport {X Y : Dᵒᵖ} (f : X ⟶ Y) {s : R.idx X.unop} {s' : R.idx Y.unop}
    (g : R.pt s' ⟶ StructuredArrow.mk (f.unop ≫ (R.pt s).hom)) :
    summands R M X s ⟶ (ModuleCat.restrictScalars (O.map f).hom).obj (summands R M Y s') :=
  ModuleCat.semilinearMapAddEquiv (O.map f).hom (summands R M X s) (summands R M Y s')
    { toFun := fun x => M.map g.right.op x
      map_add' := fun x y => map_add (M.map g.right.op).hom x y
      map_smul' := fun r x =>
        (M.map_smul g.right.op (R.sc s r) x).trans
          (congrArg (fun z => z • M.map g.right.op x) (R.sc_naturality_apply f.unop g r)) }

/-- The restriction maps of the extension. -/
noncomputable def restrictionMap {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    (∐ summands R M X) ⟶ (ModuleCat.restrictScalars (O.map f).hom).obj (∐ summands R M Y) :=
  Sigma.desc fun s =>
    transport R M f (R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))) ≫
      (ModuleCat.restrictScalars (O.map f).hom).map
        (Sigma.ι (summands R M Y) (R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))))

/-- The restriction map on a single summand, with the target component and the arrow witnessing
it supplied separately so that nothing has to be transported at the use site. -/
lemma restrictionMap_ι_apply {X Y : Dᵒᵖ} (f : X ⟶ Y) (s : R.idx X.unop) (s' : R.idx Y.unop)
    (g : R.pt s' ⟶ StructuredArrow.mk (f.unop ≫ (R.pt s).hom))
    (x : M.obj (op (R.pt s).right)) :
    restrictionMap R M f (Sigma.ι (summands R M X) s x) =
      Sigma.ι (summands R M Y) s' (M.map g.right.op x) := by
  obtain rfl : R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)) = s' := R.red_eq g
  obtain rfl : R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)) = g := R.hom_ext _ _
  exact ConcreteCategory.congr_hom
    (Sigma.ι_desc (f := summands R M X)
      (fun s => transport R M f (R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))) ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (Sigma.ι (summands R M Y)
            (R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))))) s) x

/-- Restriction of a presheaf of modules along the opposite of an identity. -/
private lemma map_op_id_apply {E : Type u₁} [Category.{v₁} E] {O' : Eᵒᵖ ⥤ RingCat.{w}}
    (N : PresheafOfModules.{a} O') {A : E} (x : N.obj (op A)) :
    N.map (𝟙 A).op x = x := by
  rw [op_id, N.map_id]
  rfl

/-- Applying two restriction maps in a row is the restriction along any equal composite. -/
private lemma map_map_eq_apply {E : Type u₁} [Category.{v₁} E] {O' : Eᵒᵖ ⥤ RingCat.{w}}
    (N : PresheafOfModules.{a} O') {A B B' : Eᵒᵖ} (f : A ⟶ B) (g : B ⟶ B') {h : A ⟶ B'}
    (e : f ≫ g = h) (x : N.obj A) : N.map g (N.map f x) = N.map h x := by
  subst e
  exact (N.map_comp_apply f g x).symm

/-- The restriction map of the extension along a composite, on a single summand. -/
private lemma restrictionMap_comp_apply {X Y Z : Dᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : R.idx X.unop) (s₁ : R.idx Y.unop) (s₂ : R.idx Z.unop)
    (g₁ : R.pt s₁ ⟶ StructuredArrow.mk (f.unop ≫ (R.pt s).hom))
    (g₂ : R.pt s₂ ⟶ StructuredArrow.mk (g.unop ≫ (R.pt s₁).hom))
    (x : M.obj (op (R.pt s).right)) :
    restrictionMap R M (f ≫ g) (Sigma.ι (summands R M X) s x) =
      restrictionMap R M g (restrictionMap R M f (Sigma.ι (summands R M X) s x)) := by
  have h₁ : (R.pt s₁).hom ≫ u.map g₁.right = f.unop ≫ (R.pt s).hom := StructuredArrow.w g₁
  have h₂ : (R.pt s₂).hom ≫ u.map g₂.right = g.unop ≫ (R.pt s₁).hom := StructuredArrow.w g₂
  have hcomp : (R.pt s₂).hom ≫ u.map (g₂.right ≫ g₁.right) =
      (f ≫ g).unop ≫ (R.pt s).hom := by
    rw [u.map_comp, ← Category.assoc, h₂, Category.assoc, h₁]
    simp
  refine (restrictionMap_ι_apply R M (f ≫ g) s s₂ (StructuredArrow.homMk _ hcomp) x).trans ?_
  refine (congrArg (fun z => Sigma.ι (summands R M Z) s₂ z)
    (M.map_comp_apply g₁.right.op g₂.right.op x)).trans ?_
  refine ((restrictionMap_ι_apply R M g s₁ s₂ g₂ (M.map g₁.right.op x)).symm).trans ?_
  exact congrArg (fun z => restrictionMap R M g z)
    (restrictionMap_ι_apply R M f s s₁ g₁ x).symm

/-- The presheaf of `O`-modules whose sections over `X` are the direct sum, over the components
of `StructuredArrow X.unop u`, of the sections of `M` at the terminal objects. -/
noncomputable def extensionObj : PresheafOfModules.{max i t} O where
  obj X := ∐ summands R M X
  map f := restrictionMap R M f
  map_id X := by
    apply Sigma.hom_ext
    intro s
    ext x
    refine (restrictionMap_ι_apply R M (𝟙 X) s s
      (StructuredArrow.homMk (𝟙 (R.pt s).right) (by simp)) x).trans ?_
    exact congrArg (fun z => Sigma.ι (summands R M X) s z) (map_op_id_apply M x)
  map_comp {X Y Z} f g := by
    apply Sigma.hom_ext
    intro s
    ext x
    exact restrictionMap_comp_apply R M f g s _ _ (R.lift _) (R.lift _) x

/-- The component of `StructuredArrow (u.obj A) u` containing the identity. -/
noncomputable def unitIdx (A : Cᵒᵖ) : R.idx (u.obj A.unop) :=
  R.red (StructuredArrow.mk (𝟙 (u.obj A.unop)))

/-- The arrow out of the terminal object of that component. -/
noncomputable def unitLift (A : Cᵒᵖ) :
    R.pt (unitIdx R A) ⟶ StructuredArrow.mk (𝟙 (u.obj A.unop)) :=
  R.lift (StructuredArrow.mk (𝟙 (u.obj A.unop)))

/-- The structure arrow of the terminal object composed with `u` applied to `unitLift R A` is
the identity of `u.obj A.unop`. -/
lemma unitLift_w (A : Cᵒᵖ) :
    (R.pt (unitIdx R A)).hom ≫ u.map (unitLift R A).right = 𝟙 (u.obj A.unop) :=
  StructuredArrow.w (unitLift R A)

/-- At the component of an identity structured arrow the transporting ring map is the action of
`O` on the arrow of the reduction. -/
lemma sc_unitIdx (A : Cᵒᵖ) :
    R.sc (unitIdx R A) = O.map (u.map (unitLift R A).right).op := by
  have := R.isIso_map (unitIdx R A)
  refine (cancel_mono (O.map (R.pt (unitIdx R A)).hom.op)).1 ?_
  rw [R.sc_comp, ← O.map_comp, ← op_comp, unitLift_w R A]
  simp

/-- The unit on sections: a section of `M` over `A` lands in the summand of the component of the
identity structured arrow at `u.obj A`, transported along the arrow of the reduction. -/
noncomputable def unitApp (A : Cᵒᵖ) :
    M.obj A ⟶ summands R M (op (u.obj A.unop)) (unitIdx R A) :=
  ModuleCat.homEquiv.symm
    { toFun := fun x => M.map (unitLift R A).right.op x
      map_add' := fun x y => map_add (M.map (unitLift R A).right.op).hom x y
      map_smul' := fun r x => by
        refine (M.map_smul (unitLift R A).right.op r x).trans ?_
        exact congrArg (fun z => z • M.map (unitLift R A).right.op x)
          (ConcreteCategory.congr_hom (sc_unitIdx R A).symm r) }

/-- The unit of the adjunction, as a morphism of presheaves of modules. -/
noncomputable def extensionUnit :
    M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj (extensionObj R M) where
  app A := unitApp R M A ≫ Sigma.ι (summands R M (op (u.obj A.unop))) (unitIdx R A)
  naturality {A B} f := by
    ext x
    change Sigma.ι (summands R M (op (u.obj B.unop))) (unitIdx R B)
        (M.map (unitLift R B).right.op (M.map f x)) =
      restrictionMap R M ((u.map f.unop).op)
        (Sigma.ι (summands R M (op (u.obj A.unop))) (unitIdx R A)
          (M.map (unitLift R A).right.op x))
    have hwA : (R.pt (unitIdx R A)).hom ≫ u.map (unitLift R A).right = 𝟙 _ := unitLift_w R A
    have hwB : (R.pt (unitIdx R B)).hom ≫ u.map (unitLift R B).right = 𝟙 _ := unitLift_w R B
    have h₁ : StructuredArrow.mk (u.map f.unop ≫ (R.pt (unitIdx R A)).hom) ⟶
        StructuredArrow.mk (u.map f.unop) :=
      StructuredArrow.homMk (unitLift R A).right
        (show (u.map f.unop ≫ (R.pt (unitIdx R A)).hom) ≫ u.map (unitLift R A).right =
          u.map f.unop by rw [Category.assoc, hwA, Category.comp_id])
    have h₂ : StructuredArrow.mk (𝟙 (u.obj B.unop)) ⟶ StructuredArrow.mk (u.map f.unop) :=
      StructuredArrow.homMk f.unop
        (show 𝟙 (u.obj B.unop) ≫ u.map f.unop = u.map f.unop from Category.id_comp _)
    have hred : R.red (StructuredArrow.mk (u.map f.unop ≫ (R.pt (unitIdx R A)).hom)) =
        unitIdx R B :=
      (R.red_eq_red h₁).symm.trans (R.red_eq (R.lift _ ≫ h₂))
    have key : (R.liftTo _ hred).right ≫ (unitLift R A).right =
        (unitLift R B).right ≫ f.unop := by
      have hwg : (R.pt (unitIdx R B)).hom ≫ u.map (R.liftTo _ hred).right =
          u.map f.unop ≫ (R.pt (unitIdx R A)).hom := StructuredArrow.w (R.liftTo _ hred)
      have e₁ : (R.pt (unitIdx R B)).hom ≫
          u.map ((R.liftTo _ hred).right ≫ (unitLift R A).right) = u.map f.unop := by
        rw [u.map_comp, ← Category.assoc, hwg, Category.assoc, hwA, Category.comp_id]
      have e₂ : (R.pt (unitIdx R B)).hom ≫
          u.map ((unitLift R B).right ≫ f.unop) = u.map f.unop := by
        rw [u.map_comp, ← Category.assoc, hwB, Category.id_comp]
      exact congrArg CommaMorphism.right
        (R.hom_ext (t := unitIdx R B) (s := StructuredArrow.mk (u.map f.unop))
          (StructuredArrow.homMk _ e₁) (StructuredArrow.homMk _ e₂))
    refine Eq.symm ?_
    refine (restrictionMap_ι_apply R M ((u.map f.unop).op) (unitIdx R A) (unitIdx R B)
      (R.liftTo _ hred) (M.map (unitLift R A).right.op x)).trans ?_
    refine congrArg
      (fun z => Sigma.ι (summands R M (op (u.obj B.unop))) (unitIdx R B) z) ?_
    refine (M.map_comp_apply (unitLift R A).right.op (R.liftTo _ hred).right.op x).symm.trans ?_
    have hop : (unitLift R A).right.op ≫ (R.liftTo _ hred).right.op =
        f ≫ (unitLift R B).right.op := congrArg Quiver.Hom.op key
    exact (M.congr_map_apply hop x).trans (M.map_comp_apply f (unitLift R B).right.op x)

/-- The map `M ⟶ u^* N` determined by a map `extensionObj M ⟶ N`. -/
noncomputable def homForward {N : PresheafOfModules.{max i t} O} (α : extensionObj R M ⟶ N) :
    M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N :=
  extensionUnit R M ≫ (PresheafOfModules.pushforward₀.{max i t} u O).map α

/-- The component at a summand of the map out of the direct sum determined by
`α : M ⟶ u^* N`. -/
noncomputable def descComponent {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) (X : Dᵒᵖ)
    (s : R.idx X.unop) : summands R M X s ⟶ N.obj X :=
  ModuleCat.homEquiv.symm
    { toFun := fun x => N.map (R.pt s).hom.op (α.app (op (R.pt s).right) x)
      map_add' := fun x y =>
        (congrArg (fun z => N.map (R.pt s).hom.op z)
            (map_add (α.app (op (R.pt s).right)).hom x y)).trans
          (map_add (N.map (R.pt s).hom.op).hom _ _)
      map_smul' := fun r x =>
        (congrArg (fun z => N.map (R.pt s).hom.op z)
            (map_smul (α.app (op (R.pt s).right)).hom (R.sc s r) x)).trans
          ((N.map_smul (R.pt s).hom.op (R.sc s r) (α.app (op (R.pt s).right) x)).trans
            (congrArg (fun z => z • N.map (R.pt s).hom.op (α.app (op (R.pt s).right) x))
              (R.sc_comp_apply s r))) }

/-- `descComponent R M α X s` sends `x` to the restriction along the structure arrow of
`α.app _ x`. -/
lemma descComponent_apply {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) (X : Dᵒᵖ)
    (s : R.idx X.unop) (x : M.obj (op (R.pt s).right)) :
    descComponent R M α X s x = N.map (R.pt s).hom.op (α.app (op (R.pt s).right) x) := rfl

/-- The naturality square of the maps out of the summands. -/
lemma transport_comp_descComponent {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) {X Y : Dᵒᵖ} (f : X ⟶ Y)
    (s : R.idx X.unop) (s' : R.idx Y.unop)
    (g : R.pt s' ⟶ StructuredArrow.mk (f.unop ≫ (R.pt s).hom)) :
    transport R M f g ≫
        (ModuleCat.restrictScalars (O.map f).hom).map (descComponent R M α Y s') =
      descComponent R M α X s ≫ N.map f := by
  ext x
  have hα : α.app (op (R.pt s').right) (M.map g.right.op x) =
      N.map (u.map g.right).op (α.app (op (R.pt s).right) x) :=
    ConcreteCategory.congr_hom (α.naturality g.right.op) x
  show N.map (R.pt s').hom.op (α.app (op (R.pt s').right) (M.map g.right.op x)) =
    N.map f (N.map (R.pt s).hom.op (α.app (op (R.pt s).right) x))
  refine (congrArg (fun z => N.map (R.pt s').hom.op z) hα).trans ?_
  have hop : (u.map g.right).op ≫ (R.pt s').hom.op = (R.pt s).hom.op ≫ f :=
    congrArg Quiver.Hom.op (StructuredArrow.w g)
  exact (map_map_eq_apply N _ _ hop _).trans
    (N.map_comp_apply (R.pt s).hom.op f (α.app (op (R.pt s).right) x))

/-- The value on a summand of the map out of the direct sum. -/
lemma desc_ι_apply {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) (X : Dᵒᵖ)
    (s : R.idx X.unop) (y : M.obj (op (R.pt s).right)) :
    Sigma.desc (descComponent R M α X) (Sigma.ι (summands R M X) s y) =
      descComponent R M α X s y :=
  ConcreteCategory.congr_hom (Sigma.ι_desc (descComponent R M α X) s) y

/-- The map `extensionObj M ⟶ N` determined by a map `M ⟶ u^* N`. -/
noncomputable def homBackward {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) :
    extensionObj R M ⟶ N where
  app X := Sigma.desc (descComponent R M α X)
  naturality {X Y} f := by
    apply Sigma.hom_ext
    intro s
    ext x
    change Sigma.desc (descComponent R M α Y)
        (restrictionMap R M f (Sigma.ι (summands R M X) s x)) =
      N.map f (Sigma.desc (descComponent R M α X) (Sigma.ι (summands R M X) s x))
    refine (congrArg (fun z => Sigma.desc (descComponent R M α Y) z)
      (restrictionMap_ι_apply R M f s (R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)))
        (R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))) x)).trans ?_
    refine (desc_ι_apply R M α Y (R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)))
      (M.map (R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom))).right.op x)).trans ?_
    refine (ConcreteCategory.congr_hom (transport_comp_descComponent R M α f s
      (R.red (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)))
      (R.lift (StructuredArrow.mk (f.unop ≫ (R.pt s).hom)))) x).trans ?_
    exact congrArg (fun z => N.map f z) (desc_ι_apply R M α X s x).symm

/-- On the summand indexed by `s`, `homBackward R M α` is `descComponent R M α X s`. -/
lemma ι_comp_homBackward {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) (X : Dᵒᵖ)
    (s : R.idx X.unop) :
    Sigma.ι (summands R M X) s ≫ (homBackward R M α).app X = descComponent R M α X s :=
  Sigma.ι_desc _ _

/-- On the summand indexed by `s`, the map determined by the adjunct `homForward R M β` agrees
with `β`. -/
lemma descComponent_homForward {N : PresheafOfModules.{max i t} O}
    (β : extensionObj R M ⟶ N) (X : Dᵒᵖ) (s : R.idx X.unop)
    (x : M.obj (op (R.pt s).right)) :
    descComponent R M (homForward R M β) X s x = β.app X (Sigma.ι (summands R M X) s x) := by
  have hl := unitLift_w R (op (R.pt s).right)
  let hback : StructuredArrow.mk ((R.pt s).hom ≫
        (R.pt (unitIdx R (op (R.pt s).right))).hom) ⟶ R.pt s :=
    StructuredArrow.homMk (unitLift R (op (R.pt s).right)).right
      (show ((R.pt s).hom ≫ (R.pt (unitIdx R (op (R.pt s).right))).hom) ≫
        u.map (unitLift R (op (R.pt s).right)).right = (R.pt s).hom by
        rw [Category.assoc, hl, Category.comp_id])
  have hid : (R.liftBack hback).right ≫ (unitLift R (op (R.pt s).right)).right =
      𝟙 (R.pt s).right :=
    congrArg CommaMorphism.right (R.hom_ext (R.liftBack hback ≫ hback) (𝟙 _))
  have hβ : β.app X (restrictionMap R M ((R.pt s).hom.op)
        (Sigma.ι (summands R M (op (u.obj (R.pt s).right))) (unitIdx R (op (R.pt s).right))
          (M.map (unitLift R (op (R.pt s).right)).right.op x))) =
      N.map (R.pt s).hom.op (β.app (op (u.obj (R.pt s).right))
        (Sigma.ι (summands R M (op (u.obj (R.pt s).right))) (unitIdx R (op (R.pt s).right))
          (M.map (unitLift R (op (R.pt s).right)).right.op x))) :=
    ConcreteCategory.congr_hom (β.naturality ((R.pt s).hom.op)) _
  refine (descComponent_apply R M (homForward R M β) X s x).trans ?_
  refine hβ.symm.trans ?_
  refine congrArg (fun z => β.app X z) ?_
  refine (restrictionMap_ι_apply R M ((R.pt s).hom.op) (unitIdx R (op (R.pt s).right)) s
    (R.liftBack hback) (M.map (unitLift R (op (R.pt s).right)).right.op x)).trans ?_
  refine congrArg (fun z => Sigma.ι (summands R M X) s z) ?_
  have hop : (unitLift R (op (R.pt s).right)).right.op ≫ (R.liftBack hback).right.op =
      (𝟙 (R.pt s).right).op := congrArg Quiver.Hom.op hid
  exact (map_map_eq_apply M _ _ hop x).trans (map_op_id_apply M x)

/-- The map determined by the adjunct of `α`, at the summand of an identity structured arrow,
is `α` itself. -/
lemma descComponent_unitApp {N : PresheafOfModules.{max i t} O}
    (α : M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) (A : Cᵒᵖ) (x : M.obj A) :
    descComponent R M α (op (u.obj A.unop)) (unitIdx R A)
        (M.map (unitLift R A).right.op x) = α.app A x := by
  have hα : α.app (op (R.pt (unitIdx R A)).right) (M.map (unitLift R A).right.op x) =
      N.map (u.map (unitLift R A).right).op (α.app A x) :=
    ConcreteCategory.congr_hom (α.naturality (unitLift R A).right.op) x
  refine (descComponent_apply R M α (op (u.obj A.unop)) (unitIdx R A) _).trans ?_
  refine (congrArg (fun z => N.map (R.pt (unitIdx R A)).hom.op z) hα).trans ?_
  have hop : (u.map (unitLift R A).right).op ≫ (R.pt (unitIdx R A)).hom.op =
      (𝟙 (u.obj A.unop)).op := congrArg Quiver.Hom.op (unitLift_w R A)
  exact (map_map_eq_apply N _ _ hop _).trans (map_op_id_apply N _)

/-- The extension is left adjoint to restriction along `u`, in hom-set form. -/
noncomputable def homEquiv (N : PresheafOfModules.{max i t} O) :
    (extensionObj R M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.pushforward₀.{max i t} u O).obj N) where
  toFun := homForward R M
  invFun := homBackward R M
  left_inv β := by
    apply PresheafOfModules.hom_ext
    intro X
    apply Sigma.hom_ext
    intro s
    ext x
    exact (ConcreteCategory.congr_hom (ι_comp_homBackward R M (homForward R M β) X s) x).trans
      (descComponent_homForward R M β X s x)
  right_inv α := by
    apply PresheafOfModules.hom_ext
    intro A
    ext x
    exact (ConcreteCategory.congr_hom
        (ι_comp_homBackward R M α (op (u.obj A.unop)) (unitIdx R A))
        (M.map (unitLift R A).right.op x)).trans (descComponent_unitApp R M α A x)

/-- `homEquiv` is natural in the target presheaf of modules. -/
lemma homEquiv_naturality (N N' : PresheafOfModules.{max i t} O) (g : N ⟶ N')
    (h : extensionObj R M ⟶ N) :
    homEquiv R M N' (h ≫ g) =
      homEquiv R M N h ≫ (PresheafOfModules.pushforward₀.{max i t} u O).map g := by
  show extensionUnit R M ≫ (PresheafOfModules.pushforward₀.{max i t} u O).map (h ≫ g) =
    (extensionUnit R M ≫ (PresheafOfModules.pushforward₀.{max i t} u O).map h) ≫
      (PresheafOfModules.pushforward₀.{max i t} u O).map g
  rw [Functor.map_comp, Category.assoc]

end Extension

section Functor

variable {u : C ⥤ D} {O : Dᵒᵖ ⥤ RingCat.{w}} (R : Reduction.{i} u O)

/-- The extension of presheaves of modules along `u`, as a functor. -/
noncomputable def extensionFunctor :
    PresheafOfModules.{max i t} (u.op ⋙ O) ⥤ PresheafOfModules.{max i t} O :=
  Adjunction.leftAdjointOfEquiv (G := PresheafOfModules.pushforward₀.{max i t} u O)
    (F_obj := fun M => extensionObj R M) (e := fun M N => homEquiv R M N)
    (fun M N N' g h => homEquiv_naturality R M N N' g h)

/-- The extension along `u` is left adjoint to restriction along `u`. -/
noncomputable def extensionAdjunction :
    extensionFunctor R ⊣ PresheafOfModules.pushforward₀.{max i t} u O :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- On the summand indexed by `s`, the extension of a morphism is that morphism at the terminal
object of `s`, followed by the inclusion of the corresponding summand. -/
lemma ι_comp_extensionFunctor_map_app {M M' : PresheafOfModules.{max i t} (u.op ⋙ O)}
    (φ : M ⟶ M') (X : Dᵒᵖ) (s : R.idx X.unop) :
    Sigma.ι (summands R M X) s ≫ ((extensionFunctor R).map φ).app X =
      (ModuleCat.restrictScalars (R.sc s).hom).map (φ.app (op (R.pt s).right)) ≫
        Sigma.ι (summands R M' X) s := by
  refine (ι_comp_homBackward R M
    (φ ≫ homForward R M' (𝟙 (extensionObj R M'))) X s).trans ?_
  ext x
  exact descComponent_homForward R M' (𝟙 (extensionObj R M')) X s
    (φ.app (op (R.pt s).right) x)

/-- On sections over `X`, the extension of a morphism is the coproduct of its components at the
terminal objects of the components of `StructuredArrow X.unop u`. -/
lemma extensionFunctor_map_app_eq {M M' : PresheafOfModules.{max i t} (u.op ⋙ O)}
    (φ : M ⟶ M') (X : Dᵒᵖ) :
    ((extensionFunctor R).map φ).app X =
      Limits.Sigma.map (f := summands R M X) (g := summands R M' X)
        (fun s => (ModuleCat.restrictScalars (R.sc s).hom).map
          (φ.app (op (R.pt s).right))) := by
  apply Sigma.hom_ext
  intro s
  exact (ι_comp_extensionFunctor_map_app R φ X s).trans
    (Limits.Sigma.ι_map (f := summands R M X) (g := summands R M' X)
      (fun s => (ModuleCat.restrictScalars (R.sc s).hom).map
        (φ.app (op (R.pt s).right))) s).symm

/-- **The extension preserves monomorphisms**: a monomorphism of presheaves of modules is
injective on sections, and a coproduct of injective maps of modules is injective. -/
lemma extensionFunctor_preservesMonos :
    (extensionFunctor R : PresheafOfModules.{max i t} (u.op ⋙ O) ⥤
      PresheafOfModules.{max i t} O).PreservesMonomorphisms where
  preserves {M M'} φ hφ := by
    apply PresheafOfModules.mono_of_injective
    intro X
    have hmono : Mono (Limits.Sigma.map (f := summands R M X) (g := summands R M' X)
        (fun s => (ModuleCat.restrictScalars (R.sc s).hom).map
          (φ.app (op (R.pt s).right)))) :=
      Stacks.Sites.OverModules.mono_sigmaMap
        (fun s => (ModuleCat.restrictScalars (R.sc s).hom).map
          (φ.app (op (R.pt s).right)))
        (fun s => (ModuleCat.mono_iff_injective
          ((ModuleCat.restrictScalars (R.sc s).hom).map
            (φ.app (op (R.pt s).right)))).2
          (PresheafOfModules.injective_of_mono φ (op (R.pt s).right)))
    exact (ModuleCat.mono_iff_injective _).1 (extensionFunctor_map_app_eq R φ X ▸ hmono)

variable [(PresheafOfModules.pushforward.{max i t} (F := u) (R := O)
  (𝟙 (u.op ⋙ O))).IsRightAdjoint]

include R in
/-- **Mathlib's abstract left adjoint of restriction preserves monomorphisms**: two left
adjoints of one functor are isomorphic, and the direct-sum model does. -/
lemma pullback_preservesMonos :
    (PresheafOfModules.pullback.{max i t} (F := u) (R := O)
      (𝟙 (u.op ⋙ O))).PreservesMonomorphisms := by
  have hadj : PresheafOfModules.pullback.{max i t} (F := u) (R := O) (S := u.op ⋙ O)
      (𝟙 (u.op ⋙ O)) ⊣ PresheafOfModules.pushforward₀.{max i t} u O :=
    PresheafOfModules.pullbackPushforwardAdjunction (𝟙 (u.op ⋙ O))
  have h : (extensionFunctor R : PresheafOfModules.{max i t} (u.op ⋙ O) ⥤
      PresheafOfModules.{max i t} O).PreservesMonomorphisms :=
    extensionFunctor_preservesMonos R
  exact (Functor.PreservesMonomorphisms.iso_iff
    (Adjunction.leftAdjointUniq hadj (extensionAdjunction R))).2 h

end Functor

section Sheaf

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] [u.IsCocontinuous J K] (O : Sheaf K RingCat.{w})

/-- Restriction of sheaves of modules along `u` is additive: it reindexes the sections and
restricts scalars along an identity, neither of which changes the underlying additive maps. -/
lemma inverseImage_additive :
    (Stacks.SheafOfModules.inverseImage.{a} J K u O).Additive where
  map_add := by intros; ext _ _; rfl

variable [UnivLE.{w, max i t}] [UnivLE.{v₁, max i t}] [UnivLE.{v₂, max i t}]
  [UnivLE.{u₁, max i t}]
  [HasSheafify J AddCommGrpCat.{max i t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max i t}]
  [HasSheafify K AddCommGrpCat.{max i t}] [K.WEqualsLocallyBijective AddCommGrpCat.{max i t}]

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **Lower shriek of sheaves of modules along `u` preserves monomorphisms.** It is
"forget, extend as presheaves, sheafify", and each of the three steps preserves monomorphisms,
the middle one by `Stacks.Sites.ReducedLowerShriek.pullback_preservesMonos`. -/
lemma lowerShriek_preservesMonos (R : Reduction.{i} u O.obj) :
    (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O).PreservesMonomorphisms := by
  have hra : (PresheafOfModules.pushforward.{max i t} (F := u) (R := O.obj)
      (𝟙 (u.op ⋙ O.obj))).IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward.{max i t}
      (Stacks.SheafOfModules.structureMap J K u O).hom).IsRightAdjoint
  have hpre : (PresheafOfModules.pullback.{max i t}
      (Stacks.SheafOfModules.structureMap J K u O).hom).PreservesMonomorphisms :=
    @pullback_preservesMonos.{i, t, w, v₁, u₁, v₂, u₂} C _ D _ u O.obj R hra
  have hcomp : (_root_.SheafOfModules.forget.{max i t}
        (Stacks.SheafOfModules.inverseImageRing J K u O) ⋙
      PresheafOfModules.pullback.{max i t}
        (Stacks.SheafOfModules.structureMap J K u O).hom ⋙
      PresheafOfModules.sheafification.{max i t} (R₀ := O.obj)
        (𝟙 O.obj)).PreservesMonomorphisms := inferInstance
  exact hcomp

/-- **Lower shriek of sheaves of modules along a functor of sites with reductions is exact.**
Right exactness is formal, lower shriek being a left adjoint; left exactness is the direct-sum
formula for the extension of presheaves of modules, which the reduction data supplies, together
with Grothendieck's axiom AB4 for modules. An additive functor that preserves monomorphisms and
cokernels preserves homology, hence finite limits. -/
theorem lowerShriek_exact (R : Reduction.{i} u O.obj) :
    exactFunctor
      (_root_.SheafOfModules.{max i t} (Stacks.SheafOfModules.inverseImageRing J K u O))
      (_root_.SheafOfModules.{max i t} O)
      (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O) := by
  have hadj := Stacks.SheafOfModules.lowerShriekAdjunction.{max i t} J K u O
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · have hinv : (Stacks.SheafOfModules.inverseImage.{max i t} J K u O).Additive :=
      inverseImage_additive J K u O
    have : (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O).Additive :=
      hadj.left_adjoint_additive
    have : (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O).PreservesMonomorphisms :=
      lowerShriek_preservesMonos.{i, t, w, v₁, u₁, v₂, u₂} J K u O R
    have : PreservesColimits (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O) :=
      hadj.leftAdjoint_preservesColimits
    have := Functor.preservesHomology_of_preservesMonos_and_cokernels
      (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O)
    exact Functor.preservesFiniteLimits_of_preservesHomology _
  · have : PreservesColimitsOfSize.{0, 0}
        (Stacks.SheafOfModules.lowerShriek.{max i t} J K u O) :=
      hadj.leftAdjoint_preservesColimits
    exact PreservesColimitsOfSize.preservesFiniteColimits _

end Sheaf

end Stacks.Sites.ReducedLowerShriek

end
