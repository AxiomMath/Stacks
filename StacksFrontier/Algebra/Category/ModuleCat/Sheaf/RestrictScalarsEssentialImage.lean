module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of restriction of scalars along a locally surjective map

Let `α : R ⟶ R'` be a locally surjective morphism of sheaves of rings on a site `(C, J)` and let
`I ⊆ R` be its sectionwise kernel. This file proves that a sheaf of `R`-modules `G` is in the
essential image of `SheafOfModules.restrictScalars α` exactly when `I` annihilates `G`.

Together with the full faithfulness proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful` this says that
restriction of scalars along `α` is an equivalence of `Mod(R')` onto the full subcategory of
`I`-annihilated `R`-modules. That is the step which the proof of
[Stacks, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3) performs with the words "which is
given to us as we have the multiplication by `O'` which annihilates `I` by assumption and
`i_*O = O'/I`": it is not a numbered lemma in the source, and it is the construction of the
`i_*O`-action on an `I`-annihilated `O'`-module.

## Main definitions

* `Stacks.SheafOfModules.ChangeOfRings.sectionRestrict`: the restriction map of the underlying
  presheaf of abelian groups of a sheaf of modules, with its result type written in the module
  spelling rather than in the restriction-of-scalars spelling.
* `Stacks.SheafOfModules.ChangeOfRings.liftedSMul`: the action of a section of `R'` on a section
  of `G` over the same object, obtained by lifting the scalar locally through `α` and amalgamating.
* `Stacks.SheafOfModules.ChangeOfRings.liftedModule`: the resulting `R'`-module structure on the
  sections of `G`.
* `Stacks.SheafOfModules.ChangeOfRings.liftedSheaf`: the sheaf of `R'`-modules whose underlying
  presheaf of abelian groups is that of `G`.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.isSheafOfTypes_of_isSheaf`: the underlying presheaf of
  types of a sheaf of abelian groups is a sheaf, with no size condition relating the universe of
  the groups to the universes of the site.
* `Stacks.SheafOfModules.ChangeOfRings.map_liftedSMul`: the defining property of the lifted
  action — over any object on which the scalar admits a lift through `α`, the lifted action is the
  original action of that lift.
* `Stacks.SheafOfModules.ChangeOfRings.liftedSMul_app`: the lifted action restricts scalars back
  to the original one, so `liftedSheaf` is a preimage of `G`.
* `Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_of_smul_eq_zero` and
  `Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_iff`: the characterization of the
  essential image.

## Implementation notes

The construction is the source's: a section `a` of `R'` over `X` is, by local surjectivity, in
the image of `α` after restriction along a covering sieve `S` of `X`; over a member `g : Y ⟶ X` of
`S` the action of a lift `b` of `a` on the restriction of `m` does not depend on the choice of
`b`, because two lifts differ by a section of the kernel of `α`, which annihilates `G`; so the
resulting family is compatible and amalgamates to a section of `G` over `X`, which is `a • m`. All
six module axioms, the semilinearity of the restriction maps, and the compatibility with the
original action are then proved by separatedness of `G` over a suitable covering sieve — for the
axioms that involve two scalars, the intersection of the two image sieves.

Two spelling points cost more than the mathematics:

* the restriction map of a presheaf of modules has codomain
  `(ModuleCat.restrictScalars (R.map f)).obj (M.obj Y)`, whose carrier is `M.obj Y` definitionally
  but not syntactically, and which carries two `SMul` instances. Every restriction below therefore
  goes through `sectionRestrict`, a `def` whose *ascribed result type* is `G.val.obj (op Y)`; a
  type ascription on the term would not do, since the elaborator's `inferType` ignores it.

  **A dedup is owed here.** `Stacks.sectionRestrict`
  (`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras`) is the same device for a
  general `PresheafOfModules`, bundled as an `AddMonoidHom`, and it already carries
  `sectionRestrict_id`, `sectionRestrict_comp` and `sectionRestrict_smul`. It is *not* reused
  below only because it is indexed by a morphism of `Cᵒᵖ` while every restriction here is indexed
  by a morphism of `C` coming out of a covering sieve, so each use would carry an `op`/`unop`
  round trip that `rw` does not see through; a dedup pass should generalise the index of
  `Stacks.sectionRestrict` rather than keep two copies.
* the sheaf condition is used in the form `Presieve.IsSheafFor` for the underlying presheaf of
  types. Mathlib's `Presheaf.isSheaf_iff_isSheaf_forget` would force the module universe to be
  `max u' v'`; `isSheafOfTypes_of_isSheaf` instead uses `AddCommGrpCat.coyonedaObjIsoForget`, so
  that the statement is one instance of the definition of a sheaf and no universe is constrained.
  This is the abelian-group analogue of
  `Stacks.NoncommChangeOfRings.Silver.isSheaf_forget_of_isSheaf`.

All four universes are free and independent: the site is `C : Type u'` with `Category.{v'} C`, the
sheaves of rings are `RingCat.{u}`-valued, and the module universe `v` is unconstrained. Nothing
ties them, since the local lifting happens in `R` and `R'` while the amalgamation happens in `G`.

No `@[stacks 08M3]` attribute is carried here. The content of 08M3 is a statement about the direct
image `i_*` along a closed immersion of ringed topoi, whose reverse implication needs this file
*and* a reconstruction of a sheaf of modules from an internal module object on the source topos;
see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage`.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory Opposite

universe v v' u u'

namespace Stacks.SheafOfModules.ChangeOfRings

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- The underlying presheaf of types of a sheaf of abelian groups is a sheaf. Unlike
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` this needs no size condition relating the
universe of the groups to the universes of the site: the forgetful functor of
`AddCommGrpCat.{v}` is corepresented by `ULift ℤ`, so the statement is one instance of the
definition of a sheaf. -/
theorem isSheafOfTypes_of_isSheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (h : Presheaf.IsSheaf J P) :
    Presieve.IsSheaf J (P ⋙ forget AddCommGrpCat.{v}) :=
  Presieve.isSheaf_iso J (Functor.isoWhiskerLeft P AddCommGrpCat.coyonedaObjIsoForget)
    (h (AddCommGrpCat.of (ULift.{v} ℤ)))

/-- "Surjective" in the sense of Stacks — an epimorphism of the underlying sheaves of sets —
implies local surjectivity, which is the hypothesis used below. Epimorphisms of sheaves of types
are locally surjective, and local surjectivity of a morphism of sheaves of rings is local
surjectivity of the underlying morphism of sheaves of sets.

`HasSheafify J (Type u)` is not part of the Stacks hypothesis; it is what Mathlib's
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi` needs in order to factor an epimorphism
through its image sheaf, and it is automatic for a small site. -/
theorem isLocallySurjective_of_epi_forget [J.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify J (Type u)] {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    (h : Epi ((sheafCompose J (forget RingCat.{u})).map α)) : Sheaf.IsLocallySurjective α := by
  rw [Sheaf.IsLocallySurjective, Presheaf.isLocallySurjective_iff_whisker_forget]
  exact (Sheaf.isLocallySurjective_iff_epi _).2 h

section Restriction

variable {R : Sheaf J RingCat.{u}} (G : SheafOfModules.{v} R)

/-- The restriction of a section of a sheaf of modules along a morphism of the site, with its
result type written as a module over the sections of `R` at the target rather than as the
restriction of scalars of that module along `R.map`.

The two types are definitionally equal, but the restriction-of-scalars spelling carries a second
`SMul` instance, so a statement mixing the two spellings elaborates and is then inaccessible to
`rw` and `simp`. This must be a `def` with an ascribed result type: a type ascription on the term
is ignored by `inferType`. -/
noncomputable def sectionRestrict {X : Cᵒᵖ} (m : G.val.obj X) {Y : C} (g : Y ⟶ X.unop) :
    G.val.obj (op Y) :=
  G.val.map g.op m

/-- The restriction map of the underlying presheaf of abelian groups of `G` applied to a section
is `sectionRestrict`. -/
@[simp]
lemma coe_map_sectionRestrict {X : Cᵒᵖ} (m : G.val.obj X) {Y : C} (g : Y ⟶ X.unop) :
    (G.val.presheaf ⋙ forget AddCommGrpCat.{v}).map g.op m = sectionRestrict G m g :=
  rfl

/-- Restricting a section along the identity leaves it unchanged. -/
@[simp]
lemma sectionRestrict_id {X : Cᵒᵖ} (m : G.val.obj X) :
    sectionRestrict G m (𝟙 X.unop) = m :=
  CategoryTheory.congr_fun (G.val.presheaf.map_id X) m

/-- Restricting along `g` and then along `h` is restricting along `h ≫ g`. -/
lemma sectionRestrict_sectionRestrict {X : Cᵒᵖ} (m : G.val.obj X) {Y Z : C} (g : Y ⟶ X.unop)
    (h : Z ⟶ Y) : sectionRestrict G (sectionRestrict G m g) h = sectionRestrict G m (h ≫ g) :=
  (G.val.map_comp_apply g.op h.op m).symm

/-- The restriction of the zero section is zero. -/
@[simp]
lemma sectionRestrict_zero {X : Cᵒᵖ} {Y : C} (g : Y ⟶ X.unop) :
    sectionRestrict G (0 : G.val.obj X) g = 0 :=
  map_zero (G.val.map g.op).hom

/-- Restriction of sections is additive. -/
@[simp]
lemma sectionRestrict_add {X : Cᵒᵖ} (m m' : G.val.obj X) {Y : C} (g : Y ⟶ X.unop) :
    sectionRestrict G (m + m') g = sectionRestrict G m g + sectionRestrict G m' g :=
  map_add (G.val.map g.op).hom m m'

/-- The restriction of `b • m` is the restriction of `b` acting on the restriction of `m`. -/
lemma sectionRestrict_smul {X : Cᵒᵖ} (b : R.obj.obj X) (m : G.val.obj X) {Y : C}
    (g : Y ⟶ X.unop) :
    sectionRestrict G (b • m) g = R.obj.map g.op b • sectionRestrict G m g :=
  G.val.map_smul g.op b m

/-- Separatedness: two sections of a sheaf of modules over `X` that have the same restriction to
every member of a covering sieve of `X` are equal. -/
theorem sections_ext {X : Cᵒᵖ} {S : Sieve X.unop} (hS : S ∈ J X.unop) {t t' : G.val.obj X}
    (h : ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X.unop⦄, S.arrows g →
      sectionRestrict G t g = sectionRestrict G t' g) :
    t = t' :=
  (isSheafOfTypes_of_isSheaf G.val.presheaf G.isSheaf S hS).isSeparatedFor.ext h

end Restriction

section Lift

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R') (G : SheafOfModules.{v} R)
  (hG : ∀ (X : Cᵒᵖ) (a : R.obj.obj X), a ∈ RingHom.ker (α.hom.app X).hom →
    ∀ m : G.val.obj X, a • m = 0)

include hG in
/-- Two sections of `R` with the same image under `α` act in the same way on a sheaf of modules
annihilated by the kernel of `α`: their difference is killed by `α`, hence acts by zero. -/
theorem smul_eq_of_app_eq {X : Cᵒᵖ} {b b' : R.obj.obj X}
    (h : (α.hom.app X).hom b = (α.hom.app X).hom b') (m : G.val.obj X) : b • m = b' • m := by
  have h0 : (b - b') • m = 0 := hG X (b - b') (by simp [RingHom.mem_ker, h]) m
  rw [sub_smul, sub_eq_zero] at h0
  exact h0

/-- The family of local products used to define the lifted action: over a member `g` of the image
sieve of the scalar `a`, the action of a chosen lift of `a` on the restriction of `m`. -/
noncomputable def liftedFamily {X : Cᵒᵖ} (a : R'.obj.obj X) (m : G.val.obj X) :
    Presieve.FamilyOfElements (G.val.presheaf ⋙ forget AddCommGrpCat.{v})
      (Presheaf.imageSieve α.hom a).arrows :=
  fun _ g hg ↦ Presheaf.localPreimage α.hom a g hg • sectionRestrict G m g

include hG in
/-- The family `liftedFamily α G a m` is compatible. -/
lemma liftedFamily_compatible {X : Cᵒᵖ} (a : R'.obj.obj X) (m : G.val.obj X) :
    (liftedFamily α G a m).Compatible := by
  refine (Presieve.compatible_iff_sieveCompatible _).2 (fun Y Z g h hg ↦ ?_)
  have hb : (α.hom.app (op Z)).hom
      (R.obj.map h.op (Presheaf.localPreimage α.hom a g hg)) =
      (α.hom.app (op Z)).hom (Presheaf.localPreimage α.hom a (h ≫ g)
        ((Presheaf.imageSieve α.hom a).downward_closed hg h)) := by
    have h1 := Presheaf.app_localPreimage α.hom a g hg
    have h2 := Presheaf.app_localPreimage α.hom a (h ≫ g)
      ((Presheaf.imageSieve α.hom a).downward_closed hg h)
    have h3 := ConcreteCategory.congr_hom (α.hom.naturality h.op)
      (Presheaf.localPreimage α.hom a g hg)
    simp only [ConcreteCategory.comp_apply] at h3
    rw [h3, h1, h2, op_comp, R'.obj.map_comp, ConcreteCategory.comp_apply]
  change Presheaf.localPreimage α.hom a (h ≫ g) _ • sectionRestrict G m (h ≫ g) =
    sectionRestrict G (Presheaf.localPreimage α.hom a g hg • sectionRestrict G m g) h
  rw [sectionRestrict_smul, sectionRestrict_sectionRestrict]
  exact (smul_eq_of_app_eq α G hG hb _).symm

variable [Sheaf.IsLocallySurjective α]

include hG in
/-- The action of a section of `R'` on a section of `G` over the same object: the amalgamation of
the local products by the lifts of the scalar through `α`.

This is the `i_*O`-action on an `I`-annihilated `O'`-module of the proof of Stacks 08M3. -/
noncomputable def liftedSMul {X : Cᵒᵖ} (a : R'.obj.obj X) (m : G.val.obj X) : G.val.obj X :=
  (isSheafOfTypes_of_isSheaf G.val.presheaf G.isSheaf _
      (Presheaf.imageSieve_mem J α.hom a)).amalgamate
    (liftedFamily α G a m) (liftedFamily_compatible α G hG a m)

/-- **The defining property of the lifted action.** Over any object of the site on which the
scalar `a` admits a lift `b` through `α`, the restriction of `a • m` is `b` times the restriction
of `m`. The right-hand side does not depend on the lift, by `smul_eq_of_app_eq`. -/
theorem map_liftedSMul {X : Cᵒᵖ} (a : R'.obj.obj X) (m : G.val.obj X) {Y : C} (g : Y ⟶ X.unop)
    (b : R.obj.obj (op Y)) (hb : (α.hom.app (op Y)).hom b = (R'.obj.map g.op).hom a) :
    sectionRestrict G (liftedSMul α G hG a m) g = b • sectionRestrict G m g := by
  have hg : (Presheaf.imageSieve α.hom a).arrows g := ⟨b, hb⟩
  have key := (isSheafOfTypes_of_isSheaf G.val.presheaf G.isSheaf _
    (Presheaf.imageSieve_mem J α.hom a)).valid_glue
      (liftedFamily_compatible α G hG a m) g hg
  have h2 : sectionRestrict G (liftedSMul α G hG a m) g =
      Presheaf.localPreimage α.hom a g hg • sectionRestrict G m g := key
  rw [h2]
  refine smul_eq_of_app_eq α G hG ?_ _
  rw [Presheaf.app_localPreimage α.hom a g hg, hb]

/-- The lifted action of a section of the form `α b` is the original action of `b`: take the
identity as the covering and `b` as its own lift. -/
theorem liftedSMul_app {X : Cᵒᵖ} (b : R.obj.obj X) (m : G.val.obj X) :
    liftedSMul α G hG ((α.hom.app X).hom b) m = b • m := by
  have key := map_liftedSMul α G hG ((α.hom.app X).hom b) m (𝟙 X.unop) b (by simp)
  simpa using key

/-- Separatedness over the image sieve of `a`: sections of `G` are equal if their restrictions
agree along every `g` over which `a` admits a lift `b`. -/
private theorem sections_ext_of_lift {X : Cᵒᵖ} (a : R'.obj.obj X) {t t' : G.val.obj X}
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop) (b : R.obj.obj (op Y)),
      (α.hom.app (op Y)).hom b = (R'.obj.map g.op).hom a →
      sectionRestrict G t g = sectionRestrict G t' g) : t = t' :=
  sections_ext G (Presheaf.imageSieve_mem J α.hom a) fun _ g ⟨b, hb⟩ ↦ h g b hb

/-- Separatedness over the intersection of the image sieves of `a` and `a'`. -/
private theorem sections_ext_of_lift₂ {X : Cᵒᵖ} (a a' : R'.obj.obj X) {t t' : G.val.obj X}
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop) (b b' : R.obj.obj (op Y)),
      (α.hom.app (op Y)).hom b = (R'.obj.map g.op).hom a →
      (α.hom.app (op Y)).hom b' = (R'.obj.map g.op).hom a' →
      sectionRestrict G t g = sectionRestrict G t' g) : t = t' :=
  sections_ext G (J.intersection_covering (Presheaf.imageSieve_mem J α.hom a)
    (Presheaf.imageSieve_mem J α.hom a')) fun _ g ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ ↦ h g b b' hb hb'

/-! ### The module axioms for the lifted action

Each is proved by separatedness of `G` over a covering sieve on which every scalar involved
admits a lift through `α`: the image sieve of the scalar, the intersection of the two image
sieves when there are two, and the whole sieve when the scalar is `0` or `1`. -/

/-- The section `1` of `R'` acts as the identity under the lifted action. -/
theorem one_liftedSMul {X : Cᵒᵖ} (m : G.val.obj X) : liftedSMul α G hG 1 m = m := by
  refine sections_ext G (J.top_mem X.unop) (fun Y g _ ↦ ?_)
  rw [map_liftedSMul α G hG _ _ g 1 (by simp), one_smul]

/-- The lifted action of a product is the composite of the lifted actions. -/
theorem mul_liftedSMul {X : Cᵒᵖ} (a a' : R'.obj.obj X) (m : G.val.obj X) :
    liftedSMul α G hG (a * a') m = liftedSMul α G hG a (liftedSMul α G hG a' m) := by
  refine sections_ext_of_lift₂ α G a a' (fun Y g b b' hb hb' ↦ ?_)
  rw [map_liftedSMul α G hG _ _ g (b * b') (by simp [hb, hb']),
    map_liftedSMul α G hG a _ g b hb, map_liftedSMul α G hG a' m g b' hb', mul_smul]

/-- The lifted action of any scalar on the zero section is zero. -/
theorem liftedSMul_zero {X : Cᵒᵖ} (a : R'.obj.obj X) :
    liftedSMul α G hG a (0 : G.val.obj X) = 0 := by
  refine sections_ext_of_lift α G a (fun Y g b hb ↦ ?_)
  rw [map_liftedSMul α G hG a _ g b hb, sectionRestrict_zero, smul_zero]

/-- The lifted action of a scalar is additive in the section. -/
theorem liftedSMul_add {X : Cᵒᵖ} (a : R'.obj.obj X) (m m' : G.val.obj X) :
    liftedSMul α G hG a (m + m') = liftedSMul α G hG a m + liftedSMul α G hG a m' := by
  refine sections_ext_of_lift α G a (fun Y g b hb ↦ ?_)
  rw [map_liftedSMul α G hG a _ g b hb, sectionRestrict_add, sectionRestrict_add,
    map_liftedSMul α G hG a m g b hb, map_liftedSMul α G hG a m' g b hb, smul_add]

/-- The lifted action is additive in the scalar. -/
theorem add_liftedSMul {X : Cᵒᵖ} (a a' : R'.obj.obj X) (m : G.val.obj X) :
    liftedSMul α G hG (a + a') m = liftedSMul α G hG a m + liftedSMul α G hG a' m := by
  refine sections_ext_of_lift₂ α G a a' (fun Y g b b' hb hb' ↦ ?_)
  rw [map_liftedSMul α G hG _ _ g (b + b') (by simp [hb, hb']), sectionRestrict_add,
    map_liftedSMul α G hG a m g b hb, map_liftedSMul α G hG a' m g b' hb', add_smul]

/-- The section `0` of `R'` acts as zero under the lifted action. -/
theorem zero_liftedSMul {X : Cᵒᵖ} (m : G.val.obj X) : liftedSMul α G hG 0 m = 0 := by
  refine sections_ext G (J.top_mem X.unop) (fun Y g _ ↦ ?_)
  rw [map_liftedSMul α G hG _ _ g 0 (by simp), zero_smul, sectionRestrict_zero]

include hG in
/-- The `R'`-module structure on the sections of `G` given by the lifted action. -/
@[instance_reducible]
noncomputable def liftedModule (X : Cᵒᵖ) :
    Module (R'.obj.obj X) (G.val.presheaf.obj X) where
  smul a m := liftedSMul α G hG a m
  one_smul := one_liftedSMul α G hG
  mul_smul := mul_liftedSMul α G hG
  smul_zero := liftedSMul_zero α G hG
  smul_add := liftedSMul_add α G hG
  add_smul := add_liftedSMul α G hG
  zero_smul := zero_liftedSMul α G hG

/-- The semilinearity of the restriction maps of `G` for the lifted action: the restriction of
`a • m` is `(R'.map f a) • (restriction of m)`. Proved by separatedness over the pullback of the
image sieve of `a`. -/
theorem map_smul_liftedSMul ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (a : R'.obj.obj X) (m : G.val.obj X) :
    sectionRestrict G (liftedSMul α G hG a m) f.unop =
      liftedSMul α G hG ((R'.obj.map f).hom a) (sectionRestrict G m f.unop) := by
  refine sections_ext G (J.pullback_stable f.unop (Presheaf.imageSieve_mem J α.hom a))
    (fun Z g hg ↦ ?_)
  obtain ⟨b, hb⟩ := hg
  have hb' : (α.hom.app (op Z)).hom b = (R'.obj.map g.op).hom ((R'.obj.map f).hom a) := by
    rw [hb, op_comp, R'.obj.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [sectionRestrict_sectionRestrict, map_liftedSMul α G hG a m (g ≫ f.unop) b hb,
    map_liftedSMul α G hG _ _ g b hb', sectionRestrict_sectionRestrict]

include hG in
/-- The sheaf of `R'`-modules obtained from an `I`-annihilated sheaf of `R`-modules: the same
underlying presheaf of abelian groups, with the lifted action. -/
noncomputable def liftedSheaf : SheafOfModules.{v} R' where
  val :=
    @PresheafOfModules.ofPresheaf C _ R'.obj G.val.presheaf (liftedModule α G hG)
      (fun _ _ f a m ↦ map_smul_liftedSMul α G hG f a m)
  isSheaf := G.isSheaf

/-- The identity of the underlying presheaf of abelian groups, read as a morphism from the
restriction of scalars of `liftedSheaf` to `G`. The `def` with an ascribed result type is what
pins the two spellings of that presheaf together. -/
noncomputable def liftedPresheafId :
    ((PresheafOfModules.restrictScalars.{v} α.hom).obj (liftedSheaf α G hG).val).presheaf ⟶
      G.val.presheaf :=
  𝟙 _

/-- Restriction of scalars along `α` takes `liftedSheaf` back to `G`: the underlying presheaves of
abelian groups are the same, and the two actions of a section `b` of `R` agree because the lifted
action of `α b` is the action of `b`. -/
noncomputable def restrictScalarsLiftedSheafIso :
    (SheafOfModules.restrictScalars.{v} α).obj (liftedSheaf α G hG) ≅ G where
  hom := ⟨PresheafOfModules.homMk (liftedPresheafId α G hG)
    (fun X b m ↦ liftedSMul_app α G hG b m)⟩
  inv := ⟨PresheafOfModules.homMk (M₂ := (PresheafOfModules.restrictScalars.{v} α.hom).obj
      (liftedSheaf α G hG).val) (liftedPresheafId α G hG)
    (fun X b m ↦ (liftedSMul_app α G hG b m).symm)⟩
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext; rfl

include hG in
/-- **The reverse half of the module-theoretic step of Stacks 08M3.** A sheaf of `R`-modules
annihilated by the sectionwise kernel of a locally surjective `α : R ⟶ R'` is in the essential
image of restriction of scalars along `α`. -/
theorem essImage_restrictScalars_of_smul_eq_zero :
    (SheafOfModules.restrictScalars.{v} α).essImage G :=
  ⟨liftedSheaf α G hG, ⟨restrictScalarsLiftedSheafIso α G hG⟩⟩

end Lift

/-- **The module-theoretic step of Stacks 08M3.** For a locally surjective morphism `α : R ⟶ R'`
of sheaves of rings, a sheaf of `R`-modules is in the essential image of restriction of scalars
along `α` exactly when the sectionwise kernel of `α` annihilates it.

The forward implication needs neither local surjectivity nor the sheaf condition; it is
`Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_restrictScalars` applied to the
identity functor. -/
theorem essImage_restrictScalars_iff {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    [Sheaf.IsLocallySurjective α] (G : SheafOfModules.{v} R) :
    (SheafOfModules.restrictScalars.{v} α).essImage G ↔
      ∀ (X : Cᵒᵖ) (a : R.obj.obj X), a ∈ RingHom.ker (α.hom.app X).hom →
        ∀ m : G.val.obj X, a • m = 0 := by
  refine ⟨fun hGe X a ha m ↦ ?_, fun hG ↦ essImage_restrictScalars_of_smul_eq_zero α G hG⟩
  obtain ⟨M, ⟨e⟩⟩ := hGe
  have key : ∀ x : ((SheafOfModules.restrictScalars.{v} α).obj M).val.obj X, a • x = 0 := by
    intro x
    have h : a • x = (α.hom.app X).hom a • (show M.val.obj X from x) := rfl
    rw [h, RingHom.mem_ker.1 ha, zero_smul]
    rfl
  have hm : (e.hom.val.app X) ((e.inv.val.app X) m) = m := by
    have hid : e.inv.val ≫ e.hom.val = 𝟙 G.val := by
      rw [← SheafOfModules.comp_val, e.inv_hom_id, SheafOfModules.id_val]
    rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, hid, PresheafOfModules.id_app,
      ModuleCat.id_apply]
  rw [← hm, ← _root_.map_smul, key, map_zero]

end Stacks.SheafOfModules.ChangeOfRings

end
