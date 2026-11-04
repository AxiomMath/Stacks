module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Fibres
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# Splittings of a choice of pullbacks

Stacks 02XX says that a fibred category `p : 𝒳 ⥤ 𝒮` is split (Stacks 02XW, i.e. isomorphic over `𝒮`
to the category attached to a presheaf of categories `F : 𝒮ᵒᵖ ⥤ Cat`) if and only if for some
choice of pullbacks (Stacks 02XN) the pullback functors satisfy `(f ∘ g)^* = g^* ∘ f^*`. This file
introduces the condition on a choice of pullbacks that this refers to, in the two readings
discussed below, and proves the biconditional for the condition it actually needs.

## Main definitions

* `CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp`, the source's literal condition
  `(f ∘ g)^* = g^* ∘ f^*`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting`, that condition together with the unit law
  `𝟙^* = 𝟭`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage`, the condition Stacks 02XX actually
  needs: the two canonical comparisons of Stacks 02XN are *identities*, so that the chosen
  cartesian lifts, and not merely the pullback functors they induce, are strictly compatible with
  identities and composition;
* `CategoryTheory.Functor.ChoiceOfPullbacks.transport`, a choice of pullbacks carried along a
  strict isomorphism over `𝒮`;
* `CategoryTheory.presheafOfCategoriesCleavage`, the canonical choice of pullbacks of `𝒮_F`.

## Main results

* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting.compatibleWithComp`: a splitting satisfies
  the source's literal condition;
* `CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp.pullbackFunctor_id_comp_self`: the
  literal condition makes `𝟙^*` idempotent, which together with
  `CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorIdIso` is everything it says about
  `𝟙^*`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp.isSplitting_iff`: given the
  source's literal condition, the unit law is equivalent to `𝟙^*` fixing the objects of the fibres,
  so that is precisely what the source's condition fails to control;
* `CategoryTheory.Functor.eq_id_of_isoId_of_comp_self`, the general fact behind that: an idempotent
  endofunctor isomorphic to the identity and fixing every object is the identity;
* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting.presheafOfCategories`: the presheaf of
  categories `F : 𝒮ᵒᵖ ⥤ Cat` a splitting defines, with `F U` the fibre over `U` and `F f` the
  pullback functor along `f`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.isoOver` and
  `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.isSplitFibered`: a fibred category
  admitting a split cleavage is isomorphic over `𝒮` to `𝒮_F`, hence split in the sense of
  Stacks 02XW. The mutually inverse comparison functors are
  `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.toGrothendieck` and
  `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.fromGrothendieck`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.isSplitCleavage_of_map`: a choice of pullbacks is a
  split cleavage as soon as its chosen objects and chosen lifts are strictly unital and
  associative, the two canonical comparisons then being identities automatically;
* `CategoryTheory.isSplitCleavage_presheafOfCategoriesCleavage`: `𝒮_F` carries a split cleavage,
  namely the one whose chosen lifts are the pairs `(f, 𝟙)`;
* `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.transport`: a split cleavage is carried
  along a strict isomorphism over `𝒮`;
* `CategoryTheory.Functor.isSplitFibered_iff_exists_isSplitCleavage`: **Stacks 02XX**, in the
  corrected form discussed below; this is the declaration carrying the tag.

The counterexample separating the two readings is
`CategoryTheory.SplittingCounterexample.compatibleWithComp_not_isSplitting`, in
`StacksFrontier/CategoryTheory/FiberedCategory/SplittingCounterexample.lean`.

## The deviation from the source, and why it is necessary

The source defines a splitting by the single clause `(f ∘ g)^* = g^* ∘ f^*`. That clause is not
enough for the use Stacks 02XX makes of it, and the definition below therefore *also* requires the
unit law `𝟙^* = 𝟭`. Precisely:

* taking `f = g = 𝟙 U`, the literal clause says only that `𝟙^*` is an idempotent endofunctor of the
  fibre (`CompatibleWithComp.pullbackFunctor_id_comp_self`), and every choice of pullbacks already
  has `𝟙^*` naturally isomorphic to `𝟭` (`pullbackFunctorIdIso`), whatever it satisfies;
* an idempotent endofunctor naturally isomorphic to the identity need not *be* the identity, and
  this really happens for a choice of pullbacks satisfying the literal clause:
  `CategoryTheory.SplittingCounterexample.compatibleWithComp_not_isSplitting` exhibits a fibred
  category over the one-morphism base category, where the literal clause has `f = g = 𝟙` as its
  only instance, together with a choice of pullbacks satisfying it for which `𝟙^*` is not `𝟭`;
* without the unit law there is no functor `F : 𝒮ᵒᵖ ⥤ Cat` to be had: the assignment `U ↦ 𝒳_U`,
  `f ↦ f^*` has `F.map_comp` given by the literal clause, but its `F.map_id` field *is* the unit
  law, as `IsSplitting.presheafOfCategories` makes visible. Since Stacks 02XX is a statement about
  being isomorphic over `𝒮` to the category of such an `F`, the literal clause cannot characterise
  it.

Both readings are named, so that the deviation stays visible and checkable rather than becoming
folklore: `CompatibleWithComp` is the source's clause verbatim, `IsSplitting` is the strengthening
the mathematics requires, and the two are separated by an explicit counterexample. The gap between
them is measured exactly by `CompatibleWithComp.isSplitting_iff`: given the source's clause, the
unit law holds if and only if `𝟙^*` fixes the objects of the fibres. So the clause does determine
`𝟙^*` on morphisms; all it fails to determine is where `𝟙^*` sends an object, and the
counterexample is a choice of pullbacks that sends them all to one object.

## Stacks 02XX itself

Stacks 02XX is proved here, and tagged, in the *corrected* form
`CategoryTheory.Functor.isSplitFibered_iff_exists_isSplitCleavage`:

`p.IsSplitFibered ↔ ∃ c : p.ChoiceOfPullbacks, c.IsSplitCleavage`.

The biconditional the source states is false, for both readings of its own condition, and both are
refuted in `StacksFrontier/CategoryTheory/FiberedCategory/SplittingCounterexample.lean`:
`CategoryTheory.SplittingCounterexample.compatibleWithComp_not_isSplitting` for the literal clause
`(f ∘ g)^* = g^* ∘ f^*`, which does not even give the unit law, and
`CategoryTheory.SplitCleavageCounterexample.isSplitting_not_isSplitFibered` for that clause
together with the unit law, which holds for a fibred category that is not split. So no condition on
the pullback *functors* can characterise splitness, and the tag sits on the statement whose
condition constrains the chosen cartesian *lifts*, as described above.

The two directions are: `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.isSplitFibered`,
a choice of pullbacks satisfying `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage` makes
`𝒳` isomorphic over `𝒮` to `CategoryTheory.presheafOfCategories`, hence split; and for the
converse, a split cleavage extracted from a splitness witness, namely the canonical split cleavage
`CategoryTheory.presheafOfCategoriesCleavage` of `𝒮_F`
(`CategoryTheory.isSplitCleavage_presheafOfCategoriesCleavage`) transported along the isomorphism
over `𝒮` (`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.transport`).
-/

@[expose] public section

namespace CategoryTheory.Functor.ChoiceOfPullbacks

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}
  (c : p.ChoiceOfPullbacks)

/-- The condition on a choice of pullbacks that Stacks 02XX states literally: the pullback functors
are compatible with composition on the nose, `(f ∘ g)^* = g^* ∘ f^*`. See the module docstring:
this is strictly weaker than `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting`, which is the
condition Stacks 02XX needs. -/
def CompatibleWithComp : Prop :=
  ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U),
    c.pullbackFunctor (g ≫ f) = c.pullbackFunctor f ⋙ c.pullbackFunctor g

/-- A *splitting*: a choice of pullbacks whose pullback functors are compatible with composition
and with identities on the nose. The unit law is not in the source; see the module docstring for
why it is needed and for the counterexample showing it does not follow from the source's clause. -/
def IsSplitting : Prop :=
  (∀ U : 𝒮, c.pullbackFunctor (𝟙 U) = 𝟭 (p.Fiber U)) ∧ c.CompatibleWithComp

variable {c}

/-- A splitting satisfies the unit law `𝟙^* = 𝟭`. -/
lemma IsSplitting.pullbackFunctor_id (h : c.IsSplitting) (U : 𝒮) :
    c.pullbackFunctor (𝟙 U) = 𝟭 (p.Fiber U) := h.1 U

/-- A splitting satisfies the source's literal condition `(f ∘ g)^* = g^* ∘ f^*`. -/
lemma IsSplitting.compatibleWithComp (h : c.IsSplitting) : c.CompatibleWithComp := h.2

/-- The source's literal condition forces `𝟙^*` to be idempotent, and — since `𝟙 U ≫ 𝟙 U = 𝟙 U` is
its only instance at a single object — that is all it forces there. Compare
`CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorIdIso`, which says that `𝟙^*` is naturally
isomorphic to `𝟭` for *every* choice of pullbacks. -/
lemma CompatibleWithComp.pullbackFunctor_id_comp_self (h : c.CompatibleWithComp) (U : 𝒮) :
    c.pullbackFunctor (𝟙 U) ⋙ c.pullbackFunctor (𝟙 U) = c.pullbackFunctor (𝟙 U) := by
  simpa using (h (𝟙 U) (𝟙 U)).symm

/-- An idempotent endofunctor of a category which is isomorphic to the identity functor *and* fixes
every object is the identity functor.

Both hypotheses are needed. Every choice of pullbacks has `𝟙^*` isomorphic to `𝟭`
(`CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctorIdIso`) and the source's condition in
Stacks 02XX makes it idempotent
(`CategoryTheory.Functor.ChoiceOfPullbacks.CompatibleWithComp.pullbackFunctor_id_comp_self`); what
can fail is only that it fixes the objects, and then the conclusion fails too. -/
lemma _root_.CategoryTheory.Functor.eq_id_of_isoId_of_comp_self {C : Type u₁} [Category.{v₁} C]
    {E : C ⥤ C} (θ : E ≅ 𝟭 C) (hobj : ∀ x, E.obj x = x) (hEE : E ⋙ E = E) : E = 𝟭 C := by
  -- The isomorphism `θ` expresses `E` on morphisms.
  have key : ∀ {y y' : C} (β : y ⟶ y'), E.map β = θ.hom.app y ≫ β ≫ θ.inv.app y' := by
    intro y y' β
    have h1 : E.map β ≫ θ.hom.app y' = θ.hom.app y ≫ β := θ.hom.naturality β
    rw [← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  -- `θ` at two equal objects, compared across the equality.
  have happ : ∀ {y y' : C} (e : y = y'),
      θ.hom.app y = eqToHom (congrArg E.obj e) ≫ θ.hom.app y' ≫ eqToHom e.symm := by
    intro y y' e; subst e; simp
  have hinv : ∀ {y y' : C} (e : y = y'),
      θ.inv.app y = eqToHom e ≫ θ.inv.app y' ≫ eqToHom (congrArg E.obj e).symm := by
    intro y y' e; subst e; simp
  refine Functor.ext hobj fun x x' α => ?_
  -- Idempotence, read on `α`, with the object identifications supplied by `hobj`.
  have hI : E.map (E.map α) = eqToHom (congrArg E.obj (hobj x)) ≫ E.map α ≫
      eqToHom (congrArg E.obj (hobj x')).symm := Functor.congr_hom hEE α
  rw [key (E.map α), happ (hobj x), hinv (hobj x')] at hI
  simp only [← Category.assoc] at hI
  replace hI := (cancel_mono (eqToHom (congrArg E.obj (hobj x')).symm)).1 hI
  simp only [Category.assoc] at hI
  replace hI := (cancel_epi (eqToHom (congrArg E.obj (hobj x)))).1 hI
  -- Expand the remaining `E.map α` by `key` and cancel `θ` on both sides.
  rw [key α] at hI
  simp only [Category.assoc] at hI
  replace hI := (cancel_epi (θ.hom.app x)).1 hI
  simp only [← Category.assoc] at hI
  replace hI := (cancel_mono (θ.inv.app x')).1 hI
  rw [key α]
  conv_rhs => rw [← hI]
  simp

/-- Given the source's condition, the unit law is *equivalent* to `𝟙^*` fixing the objects of the
fibres. So the counterexample in
`StacksFrontier/CategoryTheory/FiberedCategory/SplittingCounterexample.lean` is the only kind
there is: what the source's clause leaves undetermined about `𝟙^*` is exactly where it sends an
object, and once that is fixed
the clause pins down the rest. -/
lemma CompatibleWithComp.isSplitting_iff (h : c.CompatibleWithComp) :
    c.IsSplitting ↔ ∀ (U : 𝒮) (x : p.Fiber U), c.obj (𝟙 U) x = x :=
  ⟨fun hs U x => Functor.congr_obj (hs.pullbackFunctor_id U) x, fun hobj =>
    ⟨fun U => Functor.eq_id_of_isoId_of_comp_self (c.pullbackFunctorIdIso U) (hobj U)
      (h.pullbackFunctor_id_comp_self U), h⟩⟩

/-- The presheaf of categories determined by a splitting: `U ↦ 𝒳_U` on objects and `f ↦ f^*` on
morphisms. The `map_comp` field is the source's literal condition and the `map_id` field is the
unit law, which is why Stacks 02XX needs the latter as well. -/
noncomputable def IsSplitting.presheafOfCategories (h : c.IsSplitting) :
    𝒮ᵒᵖ ⥤ Cat.{v₂, u₂} where
  obj U := Cat.of (p.Fiber U.unop)
  map f := (c.pullbackFunctor f.unop).toCatHom
  map_id U := Cat.ext (by simpa using h.pullbackFunctor_id U.unop)
  map_comp f g := Cat.ext (by simpa using h.compatibleWithComp g.unop f.unop)

end CategoryTheory.Functor.ChoiceOfPullbacks

/-! ### The correct repair: a split cleavage

The unit law of `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitting` is still not enough for
Stacks 02XX: see `CategoryTheory.SplitCleavageCounterexample.isSplitting_not_isSplitFibered` in
`StacksFrontier/CategoryTheory/FiberedCategory/SplittingCounterexample.lean`, a fibred category
with a choice of pullbacks satisfying both the unit law and the composition law for pullback
*functors* which is not split. Both `CompatibleWithComp` and `IsSplitting` constrain only the
pullback functors, whereas splitness constrains the chosen cartesian *lifts*: for a genuine
functor `F : 𝒮ᵒᵖ ⥤ Cat` the lift `(f, id_{f^* x})` of Stacks 02XV satisfies `𝟙^*`-unitality and
lift-level associativity on the nose, and that is strictly more than the induced functors
record. The condition below asks exactly this, by requiring the two canonical comparisons of
Stacks 02XN to be identities.
-/

namespace CategoryTheory.Functor.ChoiceOfPullbacks

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒮}

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion
  IsSplitting.presheafOfCategories

variable (c : p.ChoiceOfPullbacks)

/-- A *split cleavage*: a choice of pullbacks whose canonical comparisons `𝟙^* ≅ 𝟭` and
`(f ∘ g)^* ≅ g^* ∘ f^*` are equalities *as isomorphisms*, i.e. whose chosen cartesian lifts, and
not merely the pullback functors they induce, are compatible with identities and composition. -/
structure IsSplitCleavage : Prop where
  /-- The unit law for pullback functors. -/
  pullbackFunctor_id : ∀ U : 𝒮, c.pullbackFunctor (𝟙 U) = 𝟭 (p.Fiber U)
  /-- The canonical comparison `𝟙^* ≅ 𝟭` is the identity. -/
  pullbackFunctorIdIso_eq :
    ∀ U : 𝒮, c.pullbackFunctorIdIso U = eqToIso (pullbackFunctor_id U)
  /-- The composition law for pullback functors. -/
  pullbackFunctor_comp : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U),
    c.pullbackFunctor (g ≫ f) = c.pullbackFunctor f ⋙ c.pullbackFunctor g
  /-- The canonical comparison `(f ∘ g)^* ≅ g^* ∘ f^*` is the identity. -/
  pullbackFunctorCompIso_eq : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U),
    c.pullbackFunctorCompIso g f = eqToIso (pullbackFunctor_comp g f)

variable {c}

/-- A split cleavage is in particular a splitting. -/
lemma IsSplitCleavage.isSplitting (h : c.IsSplitCleavage) : c.IsSplitting :=
  ⟨h.pullbackFunctor_id, fun g f => h.pullbackFunctor_comp g f⟩

/-- A split cleavage pulls an object of the fibre over `U` back along `𝟙 U` to itself. -/
lemma IsSplitCleavage.obj_id (h : c.IsSplitCleavage) (U : 𝒮) (x : p.Fiber U) :
    c.obj (𝟙 U) x = x :=
  Functor.congr_obj (h.pullbackFunctor_id U) x

/-- For a split cleavage the canonical isomorphism `c.obj (𝟙 U) x ≅ x` is the `eqToHom` of
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_id`. -/
lemma IsSplitCleavage.objIdIso_hom (h : c.IsSplitCleavage) {U : 𝒮} (x : p.Fiber U) :
    (c.objIdIso x).hom = eqToHom (h.obj_id U x) := by
  have := congrArg (fun e : c.pullbackFunctor (𝟙 U) ≅ 𝟭 (p.Fiber U) => e.hom.app x)
    (h.pullbackFunctorIdIso_eq U)
  simpa [pullbackFunctorIdIso] using this

/-- For a split cleavage the chosen cartesian lift of `𝟙 U` at `x` is the identity of `x`, written
as the `eqToHom` transporting along
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_id`. -/
lemma IsSplitCleavage.map_id (h : c.IsSplitCleavage) {U : 𝒮} (x : p.Fiber U) :
    c.map (𝟙 U) x = eqToHom (congrArg Fiber.fiberInclusion.obj (h.obj_id U x)) := by
  rw [← fiberInclusion_map_objIdIso_hom, h.objIdIso_hom, eqToHom_map]

/-- A split cleavage pulls back along a composite `g ≫ f` by pulling back along `f` and then
along `g`, on the nose. -/
lemma IsSplitCleavage.obj_comp (h : c.IsSplitCleavage) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (x : p.Fiber U) : c.obj (g ≫ f) x = c.obj g (c.obj f x) :=
  Functor.congr_obj (h.pullbackFunctor_comp g f) x

/-- For a split cleavage the canonical isomorphism `c.obj (g ≫ f) x ≅ c.obj g (c.obj f x)` is the
`eqToHom` of `CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_comp`. -/
lemma IsSplitCleavage.objCompIso_hom (h : c.IsSplitCleavage) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (x : p.Fiber U) : (c.objCompIso g f x).hom = eqToHom (h.obj_comp g f x) := by
  have := congrArg
    (fun e : c.pullbackFunctor (g ≫ f) ≅ c.pullbackFunctor f ⋙ c.pullbackFunctor g => e.hom.app x)
    (h.pullbackFunctorCompIso_eq g f)
  simpa [pullbackFunctorCompIso] using this

/-- For a split cleavage the chosen cartesian lift of a composite `g ≫ f` is the composite of the
chosen lifts of `g` and of `f`, up to the `eqToHom` transporting along
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_comp`. -/
lemma IsSplitCleavage.map_comp (h : c.IsSplitCleavage) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (x : p.Fiber U) : c.map (g ≫ f) x =
      eqToHom (congrArg Fiber.fiberInclusion.obj (h.obj_comp g f x)) ≫
        c.map g (c.obj f x) ≫ c.map f x := by
  rw [← objCompIso_hom_fac, h.objCompIso_hom, eqToHom_map]

/-- The four identities of
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_id`,
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.map_id`,
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.obj_comp` and
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.map_comp` characterise a split cleavage:
a choice of pullbacks is one as soon as its chosen objects and chosen lifts are strictly unital and
associative. Both canonical comparisons of Stacks 02XN are then identities automatically, because
each is the unique factorisation of one cartesian lift through another. -/
lemma isSplitCleavage_of_map
    (hobj_id : ∀ (U : 𝒮) (x : p.Fiber U), c.obj (𝟙 U) x = x)
    (hmap_id : ∀ (U : 𝒮) (x : p.Fiber U),
      c.map (𝟙 U) x = eqToHom (congrArg Fiber.fiberInclusion.obj (hobj_id U x)))
    (hobj_comp : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U),
      c.obj (g ≫ f) x = c.obj g (c.obj f x))
    (hmap_comp : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U),
      c.map (g ≫ f) x = eqToHom (congrArg Fiber.fiberInclusion.obj (hobj_comp g f x)) ≫
        c.map g (c.obj f x) ≫ c.map f x) :
    c.IsSplitCleavage := by
  have hid : ∀ (U : 𝒮) (x : p.Fiber U), (c.objIdIso x).hom = eqToHom (hobj_id U x) := fun U x =>
    Fiber.hom_ext (by rw [fiberInclusion_map_objIdIso_hom, hmap_id, eqToHom_map])
  have hcomp : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U),
      (c.objCompIso g f x).hom = eqToHom (hobj_comp g f x) := by
    intro W V U g f x
    refine fiber_hom_ext_of_cartesian (g ≫ f) (c.map g (c.obj f x) ≫ c.map f x) inferInstance
      _ _ ?_
    rw [objCompIso_hom_fac, eqToHom_map, ← hmap_comp]
  exact
    { pullbackFunctor_id := fun U =>
        Functor.ext_of_iso (c.pullbackFunctorIdIso U) (hobj_id U)
          fun x => by simp [pullbackFunctorIdIso, hid]
      pullbackFunctorIdIso_eq := fun U => by
        ext x; simp [pullbackFunctorIdIso, hid, eqToHom_app]
      pullbackFunctor_comp := fun g f =>
        Functor.ext_of_iso (c.pullbackFunctorCompIso g f) (hobj_comp g f)
          fun x => by simp [pullbackFunctorCompIso, hcomp]
      pullbackFunctorCompIso_eq := fun g f => by
        ext x; simp [pullbackFunctorCompIso, hcomp, eqToHom_app] }

/-- The chosen lift at equal objects of the fibre. -/
lemma map_congr_obj {V U : 𝒮} (f : V ⟶ U) {x x' : p.Fiber U} (e : x = x') :
    c.map f x = eqToHom (congrArg Fiber.fiberInclusion.obj (congrArg (c.obj f) e)) ≫
      c.map f x' ≫ eqToHom (congrArg Fiber.fiberInclusion.obj e.symm) := by
  subst e; simp

section Comparison

variable (c)

/-- The vertical morphism `x ⟶ p(ψ)^* y` that a morphism `ψ : x ⟶ y` of `𝒳` induces. -/
noncomputable def splitHom {x y : 𝒳} (ψ : x ⟶ y) :
    Fiber.mk (rfl : p.obj x = p.obj x) ⟶ c.obj (p.map ψ) (Fiber.mk (rfl : p.obj y = p.obj y)) :=
  ⟨IsStronglyCartesian.map p (p.map ψ) (c.map (p.map ψ) (Fiber.mk rfl))
    (Category.id_comp (p.map ψ)).symm ψ, inferInstance⟩

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.splitHom` factors `ψ` through the chosen cartesian
lift of `p ψ`. -/
@[reassoc (attr := simp)]
lemma splitHom_fac {x y : 𝒳} (ψ : x ⟶ y) :
    Fiber.fiberInclusion.map (c.splitHom ψ) ≫ c.map (p.map ψ) (Fiber.mk (rfl : p.obj y = p.obj y))
      = ψ :=
  IsStronglyCartesian.fac p (p.map ψ) (c.map (p.map ψ) (Fiber.mk rfl))
    (Category.id_comp (p.map ψ)).symm ψ

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.splitHom` is the unique vertical morphism factoring
`ψ` through the chosen cartesian lift of `p ψ`. -/
lemma splitHom_uniq {x y : 𝒳} (ψ : x ⟶ y)
    (β : Fiber.mk (rfl : p.obj x = p.obj x) ⟶ c.obj (p.map ψ) (Fiber.mk (rfl : p.obj y = p.obj y)))
    (hβ : Fiber.fiberInclusion.map β ≫ c.map (p.map ψ) (Fiber.mk (rfl : p.obj y = p.obj y)) = ψ) :
    β = c.splitHom ψ :=
  Fiber.hom_ext (IsStronglyCartesian.map_uniq p (p.map ψ) (c.map (p.map ψ) (Fiber.mk rfl))
    (Category.id_comp (p.map ψ)).symm ψ (Fiber.fiberInclusion.map β) hβ)

variable {c}

/-- The chosen lift along a morphism that happens to be an identity. -/
lemma IsSplitCleavage.eqToHom_comp_map_id (h : c.IsSplitCleavage) {x : 𝒳}
    {f : p.obj x ⟶ p.obj x} (hf : f = 𝟙 (p.obj x))
    (e : Fiber.mk (rfl : p.obj x = p.obj x) = c.obj f (Fiber.mk rfl)) :
    Fiber.fiberInclusion.map (eqToHom e) ≫ c.map f (Fiber.mk rfl) = 𝟙 x := by
  subst hf
  rw [eqToHom_map, h.map_id]
  simp

/-- The chosen lift along a morphism that happens to be a composite. -/
lemma IsSplitCleavage.eqToHom_comp_map_comp (h : c.IsSplitCleavage) {W V U : 𝒮}
    {x : p.Fiber U} {k : W ⟶ U} (g : W ⟶ V) (f : V ⟶ U) (hk : k = g ≫ f)
    (e : c.obj g (c.obj f x) = c.obj k x) :
    Fiber.fiberInclusion.map (eqToHom e) ≫ c.map k x = c.map g (c.obj f x) ≫ c.map f x := by
  subst hk
  rw [eqToHom_map, h.map_comp g f]
  simp

/-- The factorisation characterising the fibre component of the comparison functor on a
composite. -/
lemma IsSplitCleavage.splitHom_comp_fac (h : c.IsSplitCleavage) {x y z : 𝒳} (ψ : x ⟶ y) (χ : y ⟶ z)
    (e : c.obj (p.map ψ) (c.obj (p.map χ) (Fiber.mk (rfl : p.obj z = p.obj z)))
        = c.obj (p.map (ψ ≫ χ)) (Fiber.mk rfl)) :
    Fiber.fiberInclusion.map (c.splitHom ψ ≫ c.homMap (p.map ψ) (c.splitHom χ) ≫ eqToHom e)
        ≫ c.map (p.map (ψ ≫ χ)) (Fiber.mk rfl) = ψ ≫ χ := by
  rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, h.eqToHom_comp_map_comp (p.map ψ) (p.map χ) (p.map_comp ψ χ),
    homMap_fac_assoc, splitHom_fac, splitHom_fac_assoc]

/-- The comparison functor `𝒳 ⥤ 𝒮_F` attached to a split cleavage. -/
noncomputable def IsSplitCleavage.toGrothendieck (h : c.IsSplitCleavage) :
    𝒳 ⥤ ∫ᶜ h.isSplitting.presheafOfCategories.toPseudofunctor' where
  obj x := ⟨p.obj x, Fiber.mk rfl⟩
  map ψ := { base := p.map ψ, fiber := c.splitHom ψ }
  map_id x := by
    refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
    simp only [CoGrothendieck.categoryStruct_id_fiber, Functor.toPseudofunctor'_mapId,
      eqToIso.inv, Cat.eqToHom_app, eqToHom_trans]
    refine (c.splitHom_uniq (𝟙 x) _ ?_).symm
    exact h.eqToHom_comp_map_id (p.map_id x) _
  map_comp {x y z} ψ χ := by
    refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
    simp only [CoGrothendieck.categoryStruct_comp_fiber, Functor.toPseudofunctor'_mapComp,
      eqToIso.inv, Cat.eqToHom_app, eqToHom_trans, Category.assoc]
    refine (c.splitHom_uniq (ψ ≫ χ) _ ?_).symm
    exact h.splitHom_comp_fac ψ χ _

/-- Chosen lift along an identity, at an arbitrary object of the fibre. -/
lemma IsSplitCleavage.eqToHom_comp_map_id' (h : c.IsSplitCleavage) {U : 𝒮} (x : p.Fiber U)
    (e : x = c.obj (𝟙 U) x) :
    Fiber.fiberInclusion.map (eqToHom e) ≫ c.map (𝟙 U) x =
      𝟙 (Fiber.fiberInclusion.obj x) := by
  rw [eqToHom_map, h.map_id]; simp

/-- The factorisation characterising the composite of two morphisms of `𝒮_F`. -/
lemma IsSplitCleavage.fiber_comp_fac (h : c.IsSplitCleavage) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    {x : p.Fiber W} {y : p.Fiber V} {z : p.Fiber U} (β : x ⟶ c.obj g y) (γ : y ⟶ c.obj f z)
    (e : c.obj g (c.obj f z) = c.obj (g ≫ f) z) :
    Fiber.fiberInclusion.map (β ≫ c.homMap g γ ≫ eqToHom e) ≫ c.map (g ≫ f) z =
      (Fiber.fiberInclusion.map β ≫ c.map g y) ≫ Fiber.fiberInclusion.map γ ≫ c.map f z := by
  rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, h.eqToHom_comp_map_comp g f rfl, homMap_fac_assoc, Category.assoc]

/-- Transport of a chosen lift along an equality of base morphisms. -/
lemma eqToHom_comp_map_of_base_eq {V U : 𝒮} {x : p.Fiber U} {f f' : V ⟶ U} (hf : f = f')
    (e : c.obj f x = c.obj f' x) :
    Fiber.fiberInclusion.map (eqToHom e) ≫ c.map f' x = c.map f x := by
  subst hf
  rw [show e = rfl from rfl, eqToHom_refl, Fiber.fiberInclusion.map_id, Category.id_comp]

/-- `CategoryTheory.Functor.ChoiceOfPullbacks.eqToHom_comp_map_of_base_eq`, precomposed. -/
lemma comp_eqToHom_comp_map {V U : 𝒮} {y : p.Fiber U} {f f' : V ⟶ U} (hf : f = f') {z : 𝒳}
    (β : z ⟶ Fiber.fiberInclusion.obj (c.obj f y)) (e : c.obj f y = c.obj f' y) :
    β ≫ Fiber.fiberInclusion.map (eqToHom e) ≫ c.map f' y = β ≫ c.map f y := by
  rw [c.eqToHom_comp_map_of_base_eq hf]

/-- The comparison functor `𝒮_F ⥤ 𝒳` attached to a split cleavage. -/
noncomputable def IsSplitCleavage.fromGrothendieck (h : c.IsSplitCleavage) :
    (∫ᶜ h.isSplitting.presheafOfCategories.toPseudofunctor') ⥤ 𝒳 where
  obj X := (X.fiber : p.Fiber X.base).1
  map {_ Y} u := Fiber.fiberInclusion.map u.fiber ≫ c.map u.base Y.fiber
  map_id X := by
    simp only [CoGrothendieck.categoryStruct_id_base, CoGrothendieck.categoryStruct_id_fiber,
      Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]
    exact h.eqToHom_comp_map_id' X.fiber _
  map_comp {_ _ Z} u v := by
    simp only [CoGrothendieck.categoryStruct_comp_base, CoGrothendieck.categoryStruct_comp_fiber,
      Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
    exact h.fiber_comp_fac u.base v.base u.fiber v.fiber _

/-- The comparison functors of a split cleavage compose to the identity of `𝒳`. -/
lemma IsSplitCleavage.toGrothendieck_comp_fromGrothendieck (h : c.IsSplitCleavage) :
    h.toGrothendieck ⋙ h.fromGrothendieck = 𝟭 𝒳 :=
  Functor.ext (fun _ => rfl) fun _ _ _ => by simp [fromGrothendieck, toGrothendieck]

/-- A chosen lift precomposed with a vertical morphism lies over its base morphism. -/
private lemma isHomLift_fiberInclusion_map_comp_map {V U : 𝒮} (f : V ⟶ U) {x : p.Fiber V}
    {y : p.Fiber U} (β : x ⟶ c.obj f y) :
    p.IsHomLift f (Fiber.fiberInclusion.map β ≫ c.map f y) := by
  have hl : p.IsHomLift (𝟙 V ≫ f) (Fiber.fiberInclusion.map β ≫ c.map f y) := inferInstance
  rwa [Category.id_comp] at hl

/-- The comparison functors of a split cleavage compose to the identity of `𝒮_F`. -/
lemma IsSplitCleavage.fromGrothendieck_comp_toGrothendieck (h : c.IsSplitCleavage) :
    h.fromGrothendieck ⋙ h.toGrothendieck = 𝟭 _ := by
  refine Functor.hext (fun X => ?_) fun X Y u => ?_
  · obtain ⟨U, y⟩ := X
    obtain ⟨a, ha⟩ := y
    have ha' : p.obj a = U := ha
    subst ha'
    rfl
  · obtain ⟨U, y⟩ := X
    obtain ⟨a, ha⟩ := y
    have ha' : p.obj a = U := ha
    subst ha'
    obtain ⟨V, z⟩ := Y
    obtain ⟨b, hb⟩ := z
    have hb' : p.obj b = V := hb
    subst hb'
    refine heq_of_eq ?_
    have hlift : p.IsHomLift u.base (h.fromGrothendieck.map u) :=
      isHomLift_fiberInclusion_map_comp_map u.base u.fiber
    have hbase : p.map (h.fromGrothendieck.map u) = u.base :=
      (IsHomLift.eq_of_isHomLift p u.base _).symm
    refine CoGrothendieck.Hom.ext _ _ hbase ?_
    refine (c.splitHom_uniq _ _ ?_).symm
    simp only [Functor.id_map, Fiber.fiberInclusion.map_comp, Category.assoc]
    exact c.comp_eqToHom_comp_map hbase.symm _ _

/-- The image under `fromGrothendieck` of a morphism of `𝒮_F` lies over its base component. -/
lemma IsSplitCleavage.isHomLift_fromGrothendieck_map (h : c.IsSplitCleavage)
    {X Y : ∫ᶜ h.isSplitting.presheafOfCategories.toPseudofunctor'} (u : X ⟶ Y) :
    p.IsHomLift u.base (h.fromGrothendieck.map u) :=
  isHomLift_fiberInclusion_map_comp_map u.base u.fiber

/-- `toGrothendieck` is strictly a functor over `𝒮`. -/
lemma IsSplitCleavage.toGrothendieck_comp_forget (h : c.IsSplitCleavage) :
    h.toGrothendieck ⋙ CoGrothendieck.forget _ = p := rfl

/-- `fromGrothendieck` is strictly a functor over `𝒮`. -/
lemma IsSplitCleavage.fromGrothendieck_comp_p (h : c.IsSplitCleavage) :
    h.fromGrothendieck ⋙ p = CoGrothendieck.forget _ :=
  Functor.ext (fun X => X.fiber.2) fun X Y u => by
    have := h.isHomLift_fromGrothendieck_map u
    exact IsHomLift.fac' p u.base (h.fromGrothendieck.map u)

/-- `𝒳` is isomorphic over `𝒮` to `𝒮_F` for the presheaf of categories a split cleavage
defines. -/
lemma IsSplitCleavage.isoOver (h : c.IsSplitCleavage) :
    (BasedCategory.ofFunctor p).IsoOver
      (presheafOfCategories h.isSplitting.presheafOfCategories) :=
  ⟨⟨h.toGrothendieck, h.toGrothendieck_comp_forget⟩,
    ⟨h.fromGrothendieck, h.fromGrothendieck_comp_p⟩,
    h.toGrothendieck_comp_fromGrothendieck, h.fromGrothendieck_comp_toGrothendieck⟩

/-- A fibred category admitting a split cleavage is split (Stacks 02XW). -/
lemma IsSplitCleavage.isSplitFibered (h : c.IsSplitCleavage) : p.IsSplitFibered :=
  ⟨c.isFibered, h.isSplitting.presheafOfCategories, h.isoOver⟩

end Comparison

end CategoryTheory.Functor.ChoiceOfPullbacks

/-! ### Transport of a cleavage along an isomorphism over `𝒮`

A pair of mutually strictly inverse functors over `𝒮` identifies the fibres of the two structure
functors on the nose, and therefore carries a choice of pullbacks from one side to the other. This
is what makes the converse of
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage.isSplitFibered` available: it suffices to
exhibit a split cleavage on `𝒮_F`, and to transport it along the isomorphism over `𝒮` that
splitness provides.
-/

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃}
  [Category.{v₃} 𝒴] {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} {G : 𝒳 ⥤ 𝒴} {H : 𝒴 ⥤ 𝒳}

set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- A functor with a strict left inverse is faithful. -/
lemma faithful_of_comp_eq_id (hHG : H ⋙ G = 𝟭 𝒴) : H.Faithful where
  map_injective {Y Y'} u u' h := by
    have h₁ := Functor.congr_hom hHG u
    have h₂ := Functor.congr_hom hHG u'
    simp only [Functor.comp_map, Functor.id_map] at h₁ h₂
    rw [h] at h₁
    exact (cancel_mono _).1 ((cancel_epi _).1 (h₁.symm.trans h₂))

/-- A functor with a strict two-sided inverse is full. -/
lemma full_of_comp_eq_id (hGH : G ⋙ H = 𝟭 𝒳) (hHG : H ⋙ G = 𝟭 𝒴) : H.Full where
  map_surjective {Y Y'} ψ :=
    ⟨eqToHom (Functor.congr_obj hHG Y).symm ≫ G.map ψ ≫ eqToHom (Functor.congr_obj hHG Y'), by
      rw [H.map_comp, H.map_comp, eqToHom_map, eqToHom_map, ← Functor.comp_map,
        Functor.congr_hom hGH]
      simp⟩

/-- An `eqToHom` of the total category lies over an identity of the base. -/
lemma isHomLift_id_eqToHom (p : 𝒳 ⥤ 𝒮) {a b : 𝒳} (e : a = b) :
    p.IsHomLift (𝟙 (p.obj b)) (eqToHom e) := by
  subst e; simp

/-- Strong cartesianness does not see a post-composition of the base morphism with an `eqToHom`. -/
lemma isStronglyCartesian_of_comp_eqToHom {V U U' : 𝒮} {f : V ⟶ U} (e : U = U') {a b : 𝒳}
    {φ : a ⟶ b} (h : p.IsStronglyCartesian (f ≫ eqToHom e) φ) : p.IsStronglyCartesian f φ := by
  subst e; simpa using h

namespace ChoiceOfPullbacks

/-- A choice of pullbacks transported along a strict isomorphism over `𝒮`: the chosen lift of `f`
at `x` is the image under `H` of the chosen lift of `f` at `G x`, corrected by the identification
`H (G x) = x`. -/
noncomputable def transport (hG : G ⋙ q = p) (hH : H ⋙ p = q) (hGH : G ⋙ H = 𝟭 𝒳)
    (hHG : H ⋙ G = 𝟭 𝒴) (d : q.ChoiceOfPullbacks) : p.ChoiceOfPullbacks where
  obj {V U} f x := (fiberMap q p H hH V).obj (d.obj f ((fiberMap p q G hG U).obj x))
  map {_ U} f x :=
    H.map (d.map f ((fiberMap p q G hG U).obj x)) ≫ eqToHom (Functor.congr_obj hGH x.1)
  isStronglyCartesian {V U} f x := by
    have hfull : H.Full := full_of_comp_eq_id hGH hHG
    have hfaithful : H.Faithful := faithful_of_comp_eq_id hHG
    have hsurj : ∀ a : 𝒳, ∃ (Y : 𝒴) (e : H.obj Y ≅ a), p.IsHomLift (𝟙 (p.obj a)) e.hom :=
      fun a => ⟨G.obj a, eqToIso (Functor.congr_obj hGH a),
        isHomLift_id_eqToHom p (Functor.congr_obj hGH a)⟩
    have hdcart : (H ⋙ p).IsStronglyCartesian f (d.map f ((fiberMap p q G hG U).obj x)) := by
      rw [hH]; exact d.isStronglyCartesian f _
    have hHcart : p.IsStronglyCartesian f (H.map (d.map f ((fiberMap p q G hG U).obj x))) :=
      isStronglyCartesian_map H hsurj f _
    have hlift : p.IsHomLift (𝟙 U) (eqToHom (Functor.congr_obj hGH x.1)) :=
      IsHomLift.of_fac' p _ _ ((congrArg p.obj (Functor.congr_obj hGH x.1)).trans x.2) x.2
        (by simp [eqToHom_map])
    have hiso : p.IsStronglyCartesian (𝟙 U) (eqToHom (Functor.congr_obj hGH x.1)) :=
      IsStronglyCartesian.of_isIso p (𝟙 U) _
    have hcomp : p.IsStronglyCartesian (f ≫ 𝟙 U)
        (H.map (d.map f ((fiberMap p q G hG U).obj x)) ≫
          eqToHom (Functor.congr_obj hGH x.1)) := inferInstance
    simpa using hcomp

/-- The chosen pullback of the transported choice of pullbacks, in terms of the given one. -/
@[simp]
lemma transport_obj (hG : G ⋙ q = p) (hH : H ⋙ p = q) (hGH : G ⋙ H = 𝟭 𝒳) (hHG : H ⋙ G = 𝟭 𝒴)
    (d : q.ChoiceOfPullbacks) {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) :
    (transport hG hH hGH hHG d).obj f x =
      (fiberMap q p H hH V).obj (d.obj f ((fiberMap p q G hG U).obj x)) := rfl

/-- The chosen cartesian lift of the transported choice of pullbacks, in terms of the given one. -/
@[simp]
lemma transport_map (hG : G ⋙ q = p) (hH : H ⋙ p = q) (hGH : G ⋙ H = 𝟭 𝒳) (hHG : H ⋙ G = 𝟭 𝒴)
    (d : q.ChoiceOfPullbacks) {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U) :
    (transport hG hH hGH hHG d).map f x =
      H.map (d.map f ((fiberMap p q G hG U).obj x)) ≫ eqToHom (Functor.congr_obj hGH x.1) := rfl

/-- **The transport of a split cleavage along a strict isomorphism over `𝒮` is a split cleavage.**
Both identities of objects come from the identifications `H (G x) = x` and `G (H y) = y`, and both
identities of chosen lifts are then the images under `H` of the corresponding identities for the
given cleavage. -/
lemma IsSplitCleavage.transport (hG : G ⋙ q = p) (hH : H ⋙ p = q) (hGH : G ⋙ H = 𝟭 𝒳)
    (hHG : H ⋙ G = 𝟭 𝒴) {d : q.ChoiceOfPullbacks} (hd : d.IsSplitCleavage) :
    (ChoiceOfPullbacks.transport hG hH hGH hHG d).IsSplitCleavage := by
  have hobj_id : ∀ (U : 𝒮) (x : p.Fiber U),
      (ChoiceOfPullbacks.transport hG hH hGH hHG d).obj (𝟙 U) x = x := fun U x =>
    (transport_obj hG hH hGH hHG d (𝟙 U) x).trans
      ((congrArg (fiberMap q p H hH U).obj (hd.obj_id U _)).trans
        (Subtype.ext (Functor.congr_obj hGH x.1)))
  have hobj_comp : ∀ {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : p.Fiber U),
      (ChoiceOfPullbacks.transport hG hH hGH hHG d).obj (g ≫ f) x =
        (ChoiceOfPullbacks.transport hG hH hGH hHG d).obj g
          ((ChoiceOfPullbacks.transport hG hH hGH hHG d).obj f x) := by
    intro W V U g f x
    rw [transport_obj, transport_obj, transport_obj]
    refine congrArg (fiberMap q p H hH W).obj ?_
    rw [hd.obj_comp g f]
    exact congrArg (d.obj g) (Subtype.ext (Functor.congr_obj hHG _)).symm
  refine isSplitCleavage_of_map hobj_id (fun U x => ?_) hobj_comp (fun g f x => ?_)
  · rw [transport_map, hd.map_id]
    simp [eqToHom_map]
  · rw [transport_map, transport_map, transport_map, hd.map_comp g f,
      d.map_congr_obj g (show (fiberMap p q G hG _).obj
        ((ChoiceOfPullbacks.transport hG hH hGH hHG d).obj f x) =
          d.obj f ((fiberMap p q G hG _).obj x) from Subtype.ext (Functor.congr_obj hHG _))]
    simp [eqToHom_map]

end ChoiceOfPullbacks

end CategoryTheory.Functor

/-! ### The canonical split cleavage of `𝒮_F`

The category `𝒮_F` of Stacks 02XV has an evident choice of pullbacks: the chosen lift of `f` at
`(U, z)` is the pair `(f, 𝟙)`, i.e. Mathlib's
`CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift`.
Because `F` is an honest functor into `Cat`, all the pseudofunctoriality constraints of
`F.toPseudofunctor'` are `eqToIso`s, and this choice is a split cleavage.
-/

namespace CategoryTheory

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- The `eqToHom` of `∫ᶜ F` between two objects with one and the same base component: its base
component is an identity and its fibre component is the `eqToHom` of the fibre components,
corrected by the unit constraint of `F`. -/
lemma Pseudofunctor.CoGrothendieck.eqToHom_mk
    {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}} {U : 𝒮} {z z' : F.obj ⟨op U⟩}
    (hz : z = z') (e : (⟨U, z⟩ : ∫ᶜ F) = ⟨U, z'⟩) :
    eqToHom e = ⟨𝟙 U, eqToHom hz ≫ (F.mapId ⟨op U⟩).inv.toNatTrans.app z'⟩ := by
  subst hz
  obtain rfl : e = rfl := rfl
  simp only [eqToHom_refl, Category.id_comp]
  exact CoGrothendieck.Hom.ext _ _ rfl (by simp)

variable (F : 𝒮ᵒᵖ ⥤ Cat.{v₂, u₂})

/-- A presheaf of categories is strictly unital: it fixes the objects of its values along an
identity of the base. -/
lemma Functor.toPseudofunctor'_map_obj_of_eq_id {U : 𝒮} {u : U ⟶ U} (hu : u = 𝟙 U)
    (w : F.obj (op U)) : (F.toPseudofunctor'.map u.op.toLoc).toFunctor.obj w = w := by
  subst hu
  show (F.map (𝟙 (op U))).toFunctor.obj w = w
  simp

/-- A presheaf of categories is strictly compatible with composition on objects: this is the
`map_comp` of the functor `F`, which is why `𝒮_F` is split and a mere pseudofunctor's Grothendieck
construction need not be. -/
lemma Functor.toPseudofunctor'_map_obj_of_eq_comp {W V U : 𝒮} {u : W ⟶ U} {g : W ⟶ V} {f : V ⟶ U}
    (hu : u = g ≫ f) (w : F.obj (op U)) :
    (F.toPseudofunctor'.map u.op.toLoc).toFunctor.obj w =
      (F.toPseudofunctor'.map g.op.toLoc).toFunctor.obj
        ((F.toPseudofunctor'.map f.op.toLoc).toFunctor.obj w) := by
  subst hu
  show (F.map (f.op ≫ g.op)).toFunctor.obj w =
    (F.map g.op).toFunctor.obj ((F.map f.op).toFunctor.obj w)
  rw [F.map_comp]
  rfl

/-- The domain of the cartesian lift of `𝒮_F` along an `eqToHom` is the object itself: transporting
an object of `F(U')` along an equality `U = U'` of the base changes nothing. -/
lemma Pseudofunctor.CoGrothendieck.mk_eq_mk_of_map_eq_eqToHom {U U' : 𝒮} (e : U = U')
    {u : U ⟶ U'} (hu : u = eqToHom e) (w : F.obj (op U')) :
    (⟨U, (F.toPseudofunctor'.map u.op.toLoc).toFunctor.obj w⟩ : ∫ᶜ F.toPseudofunctor')
      = ⟨U', w⟩ := by
  subst hu; subst e
  exact congrArg (fun v => (⟨U, v⟩ : ∫ᶜ F.toPseudofunctor'))
    (Functor.toPseudofunctor'_map_obj_of_eq_id F (by simp) w)

/-- The cartesian lift of `𝒮_F` along an `eqToHom` *is* the corresponding `eqToHom`. -/
lemma Pseudofunctor.CoGrothendieck.cartesianLift_eq_eqToHom {U U' : 𝒮} (e : U = U')
    {u : U ⟶ U'} (hu : u = eqToHom e) (w : F.toPseudofunctor'.obj ⟨op U'⟩)
    (e' : (⟨U, (F.toPseudofunctor'.map u.op.toLoc).toFunctor.obj w⟩ : ∫ᶜ F.toPseudofunctor')
      = ⟨U', w⟩) :
    cartesianLift w u = eqToHom e' := by
  subst hu
  subst e
  rw [CoGrothendieck.eqToHom_mk
    (Functor.toPseudofunctor'_map_obj_of_eq_id F (u := eqToHom (rfl : U = U)) (by simp) w) e']
  refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
  simp [Functor.toPseudofunctor'_mapId]

/-- The cartesian lift of `𝒮_F` along a composite is, on the nose, the `eqToHom` identifying the
two chosen domains followed by the two cartesian lifts. -/
lemma Pseudofunctor.CoGrothendieck.cartesianLift_eq_eqToHom_comp {W V U : 𝒮} {u : W ⟶ U}
    {g : W ⟶ V} {f : V ⟶ U} (hu : u = g ≫ f) (w : F.toPseudofunctor'.obj ⟨op U⟩)
    (e' : (⟨W, (F.toPseudofunctor'.map u.op.toLoc).toFunctor.obj w⟩ : ∫ᶜ F.toPseudofunctor')
      = ⟨W, (F.toPseudofunctor'.map g.op.toLoc).toFunctor.obj
          ((F.toPseudofunctor'.map f.op.toLoc).toFunctor.obj w)⟩) :
    cartesianLift w u =
      eqToHom e' ≫ cartesianLift ((F.toPseudofunctor'.map f.op.toLoc).toFunctor.obj w) g ≫
        cartesianLift w f := by
  subst hu
  rw [CoGrothendieck.eqToHom_mk (Functor.toPseudofunctor'_map_obj_of_eq_comp F rfl w) e']
  refine CoGrothendieck.Hom.ext _ _ (by simp) ?_
  simp [Functor.toPseudofunctor'_mapId, Functor.toPseudofunctor'_mapComp, eqToHom_map]

/-- The canonical choice of pullbacks of the category `𝒮_F` of Stacks 02XV attached to a presheaf
of categories `F`: the chosen pullback of `(U, z)` along `f : V ⟶ U` is `(V, F(f)(z))`, and the
chosen cartesian lift is `(f, 𝟙)`. -/
noncomputable def presheafOfCategoriesCleavage :
    (CoGrothendieck.forget F.toPseudofunctor').ChoiceOfPullbacks where
  obj f y := ⟨domainCartesianLift y.1.fiber (f ≫ eqToHom y.2.symm), rfl⟩
  map f y := cartesianLift y.1.fiber (f ≫ eqToHom y.2.symm)
  isStronglyCartesian _f y :=
    Functor.isStronglyCartesian_of_comp_eqToHom y.2.symm
      (isStronglyCartesian_homCartesianLift y.1.fiber _)

/-- The chosen pullback of `𝒮_F` along an identity is the object itself. -/
lemma presheafOfCategoriesCleavage_obj_id (U : 𝒮)
    (y : (CoGrothendieck.forget F.toPseudofunctor').Fiber U) :
    (presheafOfCategoriesCleavage F).obj (𝟙 U) y = y :=
  Subtype.ext (CoGrothendieck.mk_eq_mk_of_map_eq_eqToHom F y.2.symm (by simp) y.1.fiber)

/-- The chosen cartesian lift of `𝒮_F` along an identity is the identity. -/
lemma presheafOfCategoriesCleavage_map_id (U : 𝒮)
    (y : (CoGrothendieck.forget F.toPseudofunctor').Fiber U) :
    (presheafOfCategoriesCleavage F).map (𝟙 U) y =
      eqToHom (congrArg Functor.Fiber.fiberInclusion.obj
        (presheafOfCategoriesCleavage_obj_id F U y)) :=
  CoGrothendieck.cartesianLift_eq_eqToHom F y.2.symm (by simp) y.1.fiber _

/-- The chosen pullbacks of `𝒮_F` are strictly compatible with composition. -/
lemma presheafOfCategoriesCleavage_obj_comp {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (y : (CoGrothendieck.forget F.toPseudofunctor').Fiber U) :
    (presheafOfCategoriesCleavage F).obj (g ≫ f) y =
      (presheafOfCategoriesCleavage F).obj g ((presheafOfCategoriesCleavage F).obj f y) := by
  have hV : eqToHom ((presheafOfCategoriesCleavage F).obj f y).2.symm = 𝟙 V := rfl
  exact Subtype.ext (congrArg (fun v => (⟨W, v⟩ : ∫ᶜ F.toPseudofunctor'))
    (Functor.toPseudofunctor'_map_obj_of_eq_comp F (by rw [hV]; simp) y.1.fiber))

/-- The chosen cartesian lifts of `𝒮_F` are strictly compatible with composition. -/
lemma presheafOfCategoriesCleavage_map_comp {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U)
    (y : (CoGrothendieck.forget F.toPseudofunctor').Fiber U) :
    (presheafOfCategoriesCleavage F).map (g ≫ f) y =
      eqToHom (congrArg Functor.Fiber.fiberInclusion.obj
          (presheafOfCategoriesCleavage_obj_comp F g f y)) ≫
        (presheafOfCategoriesCleavage F).map g ((presheafOfCategoriesCleavage F).obj f y) ≫
        (presheafOfCategoriesCleavage F).map f y := by
  have hV : eqToHom ((presheafOfCategoriesCleavage F).obj f y).2.symm = 𝟙 V := rfl
  exact CoGrothendieck.cartesianLift_eq_eqToHom_comp F (by rw [hV]; simp) y.1.fiber _

/-- **The canonical choice of pullbacks of `𝒮_F` is a split cleavage.** This is the half of
Stacks 02XX that produces a split cleavage out of a splitness witness, before transporting it along
the isomorphism over `𝒮`. -/
lemma isSplitCleavage_presheafOfCategoriesCleavage :
    (presheafOfCategoriesCleavage F).IsSplitCleavage :=
  Functor.ChoiceOfPullbacks.isSplitCleavage_of_map (presheafOfCategoriesCleavage_obj_id F)
    (presheafOfCategoriesCleavage_map_id F) (presheafOfCategoriesCleavage_obj_comp F)
    (presheafOfCategoriesCleavage_map_comp F)

/-! ### Stacks 02XX, corrected -/

variable {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- **Stacks 02XX**, with the source's condition on a choice of pullbacks replaced by
`CategoryTheory.Functor.ChoiceOfPullbacks.IsSplitCleavage`: a fibred category is split
(Stacks 02XW) if and only if some choice of pullbacks (Stacks 02XN) has its two canonical
comparisons of Stacks 02XN equal to identities, i.e. has *chosen cartesian lifts* strictly
compatible with identities and composition.

The source states the condition on the pullback *functors*, as `(f ∘ g)^* = g^* ∘ f^*`, and that
biconditional is false: see the module docstring, and the two counterexamples
`CategoryTheory.SplittingCounterexample.compatibleWithComp_not_isSplitting` and
`CategoryTheory.SplitCleavageCounterexample.isSplitting_not_isSplitFibered` in
`StacksFrontier/CategoryTheory/FiberedCategory/SplittingCounterexample.lean`. -/
@[stacks 02XX]
theorem Functor.isSplitFibered_iff_exists_isSplitCleavage {p : 𝒳 ⥤ 𝒮} :
    p.IsSplitFibered ↔ ∃ c : p.ChoiceOfPullbacks, c.IsSplitCleavage := by
  constructor
  · rintro ⟨-, F, Gf, Hf, hGH, hHG⟩
    exact ⟨_, Functor.ChoiceOfPullbacks.IsSplitCleavage.transport Gf.w Hf.w hGH hHG
      (isSplitCleavage_presheafOfCategoriesCleavage F)⟩
  · rintro ⟨c, hc⟩
    exact hc.isSplitFibered

end CategoryTheory
