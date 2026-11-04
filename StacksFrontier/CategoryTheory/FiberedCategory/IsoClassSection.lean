module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# The presheaf of isomorphism classes of a represented fibred category

Let `C` be a category, let `F` be a presheaf of sets on `C` and let `p : 𝒮 ⥤ C` be a category over
`C` which is equivalent over `C` to the category of elements of `F` (Stacks 02XV applied to
`F ⋙ typeToCat`). Naming a section with an object
(`CategoryTheory.PresheafOfCategories.sectionOfObj`) is constant on isomorphism classes of a
fibre, so it descends to a map out of the presheaf `\overline{𝒮}` of isomorphism classes
(`CategoryTheory.Functor.isoClassPresheaf`, Stacks 04SC); the four basic properties of naming a
section say exactly that this map is a bijection compatible with restriction. So `\overline{𝒮}`
*is* `F`, up to the universe lift that `\overline{𝒮}` carries because an isomorphism class of
objects of `𝒮` lives in the universe of `𝒮` and a section of `F` in the universe of `F`.

This is the form in which a representing presheaf is recognised: a category fibred in groupoids
over the base is handed to us with an abstract equivalence to a category of elements, while the
results about 2-fibre products (Stacks 04SD) and about morphisms (Stacks 04SW) are stated for the
presheaf of isomorphism classes.

## Main definitions

* `CategoryTheory.PresheafOfCategories.isoClassSection`: the section of `F` over `W` named by an
  isomorphism class in the fibre of `p` over `W`.
* `CategoryTheory.PresheafOfCategories.isoClassSectionEquiv`: that map as a bijection.
* `CategoryTheory.PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver`: the resulting
  isomorphism `\overline{𝒮} ≅ F` of presheaves, after the universe lift.

## Main results

* `CategoryTheory.PresheafOfCategories.isoClassSection_map`: naming a section commutes with
  restriction.
* `CategoryTheory.PresheafOfCategories.sectionOfObj_ofEq`: naming a section is unchanged by
  reading the equivalence through an equality of the structure functor of its source.

## Implementation notes

Well-definedness is `CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_fiberIso`,
injectivity is `CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`, surjectivity is
`CategoryTheory.PresheafOfCategories.exists_sectionOfObj` and naturality is
`CategoryTheory.PresheafOfCategories.sectionOfObj_map` applied to the chosen cartesian lift
`CategoryTheory.Functor.IsPreFibered.pullbackMap`, which is the morphism the restriction map of
`CategoryTheory.Functor.isoClassPresheaf` is defined by.

The source of the equivalence is taken in `Type (max a u₁)` for `F` valued in `Type a`, because
the presheaf of isomorphism classes is valued in the universe of that source while `F` is valued
in `Type a`; the two agree exactly when the source's universe absorbs `a`.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 04SC](https://stacks.math.columbia.edu/tag/04SC)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafOfCategories

universe v u a u₁

section

variable {C : Type u} [Category.{v} C] {𝒮 : Type u₁} [Category.{v} 𝒮] {p : 𝒮 ⥤ C}
  {F : Cᵒᵖ ⥤ Type a}
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- Naming a section is unchanged by reading the equivalence through an equality of the structure
functor of its source: `StacksRepresentableCFG.EquivalenceOver.ofEq` is a transport along that
equality, and the two objects of the fibre compared differ only in a proof. -/
lemma sectionOfObj_ofEq {p' : 𝒮 ⥤ C} (h : p = p') (z : 𝒮) {W : C} (hz : p'.obj z = W) :
    sectionOfObj (e.ofEq h) z hz = sectionOfObj e z ((Functor.congr_obj h z).trans hz) := by
  subst h; rfl

/-- The section of `F` over `W` named by an isomorphism class in the fibre of `p` over `W`:
isomorphic objects of one fibre name the same section. -/
def isoClassSection (W : C) :
    _root_.Quotient (isIsomorphicSetoid (p.Fiber W)) → F.obj (op W) := fun c =>
  _root_.Quotient.liftOn c (fun x => sectionOfObj e x.1 x.2)
    (fun _ _ h => sectionOfObj_eq_of_fiberIso e _ _
      ((Functor.isIsomorphicSetoid_r_iff _ _).1 h).some)

/-- The section named by the class of an object is the section named by that object. -/
@[simp] lemma isoClassSection_isoClassMk {W : C} (x : p.Fiber W) :
    isoClassSection e W (Functor.isoClassMk p x) = sectionOfObj e x.1 x.2 :=
  rfl

/-- Two isomorphism classes naming the same section are equal: objects of one fibre naming the
same section are isomorphic in that fibre. -/
lemma isoClassSection_injective (W : C) : Function.Injective (isoClassSection e W) := by
  intro c c' h
  induction c using _root_.Quotient.ind with
  | _ x =>
    induction c' using _root_.Quotient.ind with
    | _ y => exact Functor.isoClassMk_eq_of_iso (fiberIsoOfSectionOfObj_eq e x.2 y.2 h)

/-- Every section of `F` over `W` is named by an isomorphism class in the fibre over `W`. -/
lemma isoClassSection_surjective (W : C) : Function.Surjective (isoClassSection e W) := by
  intro s
  obtain ⟨z, hz, hs⟩ := exists_sectionOfObj e s
  exact ⟨Functor.isoClassMk p (Functor.Fiber.mk hz), hs⟩

/-- **The isomorphism classes of the fibre of `p` over `W` are the sections of `F` over `W`.** -/
noncomputable def isoClassSectionEquiv (W : C) :
    _root_.Quotient (isIsomorphicSetoid (p.Fiber W)) ≃ F.obj (op W) :=
  Equiv.ofBijective _ ⟨isoClassSection_injective e W, isoClassSection_surjective e W⟩

/-- The bijection of `CategoryTheory.PresheafOfCategories.isoClassSectionEquiv` is given by
naming a section. -/
@[simp] lemma isoClassSectionEquiv_apply (W : C)
    (c : _root_.Quotient (isIsomorphicSetoid (p.Fiber W))) :
    isoClassSectionEquiv e W c = isoClassSection e W c :=
  rfl

/-- Naming a section commutes with restriction: the restriction map of the presheaf of
isomorphism classes is induced by a cartesian lift, and an object lying over `f : V ⟶ W` names
the restriction along `f` of the section named by its target. -/
lemma isoClassSection_map [p.IsFibered] {V W : C} (f : V ⟶ W)
    (c : _root_.Quotient (isIsomorphicSetoid (p.Fiber W))) :
    isoClassSection e V (p.isoClassPresheaf.map f.op c) =
      F.map f.op (isoClassSection e W c) := by
  induction c using _root_.Quotient.ind with
  | _ x =>
    exact sectionOfObj_map e x.2 (Functor.pullbackFiber p x f).2 f
      (Functor.IsPreFibered.pullbackMap x.2 f) inferInstance

end

section PresheafIso

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type a} {𝒮 : Type (max a u₁)}
  [Category.{v} 𝒮] {p : 𝒮 ⥤ C} [p.IsFibered]
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **The presheaf of isomorphism classes of a category over `C` equivalent to the category of
elements of `F` is `F`.** The isomorphism carries the class of an object to the section it names;
the universe lift is there because an isomorphism class of objects of `𝒮` lives in the universe
of `𝒮`. -/
noncomputable def isoClassPresheafIsoOfEquivalenceOver :
    p.isoClassPresheaf ≅ F ⋙ uliftFunctor.{max a u₁, a} :=
  NatIso.ofComponents
    (fun W => ((isoClassSectionEquiv e W.unop).trans Equiv.ulift.symm).toIso)
    (by
      intro W V k
      ext c
      exact congrArg ULift.up (isoClassSection_map e k.unop c))

/-- The isomorphism of `CategoryTheory.PresheafOfCategories.isoClassPresheafIsoOfEquivalenceOver`
carries the class of an object to the section that object names. -/
@[simp] lemma isoClassPresheafIsoOfEquivalenceOver_hom_app_isoClassMk {W : C} (x : p.Fiber W) :
    (isoClassPresheafIsoOfEquivalenceOver e).hom.app (op W) (Functor.isoClassMk p x) =
      ULift.up (sectionOfObj e x.1 x.2) :=
  rfl

end PresheafIso

end CategoryTheory.PresheafOfCategories

end
