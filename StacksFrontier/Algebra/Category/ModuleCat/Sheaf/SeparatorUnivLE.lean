module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
import all Mathlib.Logic.Small.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separator for sheaves of modules, at independent universes

For a sheaf of rings `R` on a site `C`, the category `SheafOfModules.{v} R` is Grothendieck
abelian as soon as it has a separator and is locally `v`-small: the other two conditions
packaged by `IsGrothendieckAbelian.{v}` — filtered colimits of size `v` and their exactness —
are already available with the universes of the site, of its homs, of the rings and of the
modules mutually independent.  Local smallness is automatic in the single-universe case (the
hom universe is then the module universe) and is *not* automatic here: the homs of
`SheafOfModules.{v} R` live in `max u v` for a site in `Type u`.  This file supplies both
missing conditions.

Every existing separator for sheaves of modules concludes at `SheafOfModules.{max …}`:
Mathlib's instance needs `SmallCategory C` and a single universe, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian` reaches
`SheafOfModules.{max u r t}`.  A conclusion of that shape cannot be instantiated at a
*prescribed* module universe `v`: `max u r t = v` is a universe *equation*, whereas `UnivLE`
is a smallness class and supplies no equation.  This file therefore constructs the separator
at `v` itself.

The free module on a presheaf of types `F` over a presheaf of rings `R` has sections
`F.obj X →₀ R.obj X`, which live in `max t r` for `F : Cᵒᵖ ⥤ Type t` and
`R : Cᵒᵖ ⥤ RingCat.{r}`; this is the step that fixes the module universe in every previous
construction.  Here those sections are replaced by `Shrink.{v} (F.obj X →₀ R.obj X)`, a type
in `Type v` whenever the index and coefficient types are `v`-small — a smallness hypothesis,
which `UnivLE` does supply.  All the algebra is transported along `Shrink.addEquiv`, and the
arithmetic itself is carried out by `Finsupp.mapDomainMapRange` and `Finsupp.lift`, where no
categorical coercion intervenes.

## Main results

* `PresheafOfModules.freeObjShrink`: the free presheaf of modules on a presheaf of types, in
  a module universe independent of the universes of the site, of its homs and of the rings.
* `PresheafOfModules.freeYonedaShrink_isSeparating` and
  `PresheafOfModules.hasSeparator_of_univLE`: a separator for `PresheafOfModules.{v} R`.
* `SheafOfModules.hasSeparator_of_univLE`: a separator for `SheafOfModules.{v} R`.
* `CategoryTheory.locallySmall_functor`, `PresheafOfModules.locallySmall_of_small` and
  `SheafOfModules.locallySmall_of_univLE`: local `v`-smallness of the hom types, the second
  condition that is not automatic once the site leaves the module universe.
* `SheafOfModules.isGrothendieckAbelian_of_univLE`: `SheafOfModules.{v} R` is Grothendieck
  abelian, with the site, hom, ring and module universes independent.
* `SheafOfModules.enoughInjectives_of_univLE`: the resulting enough injectives.

## Implementation notes

The intermediate declarations take the smallness hypotheses they actually use
(`Small.{v} (R.obj X)`, `Small.{v} (F.obj X)`, `LocallySmall.{v} C`, `Small.{v} C`) rather
than `UnivLE`; the final statements are packaged with `UnivLE`, which is the form a consumer
has.

The module universe `v` is not the first universe parameter of these declarations, and it
cannot be made so while the site is introduced by a section variable.  Every occurrence is
therefore pinned by a type ascription rather than by a `.{…}` application, which would bind
the universe of the site instead.

## References

* [Stacks: Grothendieck's AB conditions](https://stacks.math.columbia.edu/tag/079A)
-/

@[expose] public section

universe t v w u r

open CategoryTheory Limits Opposite

/-- A functor category `C ⥤ D` is locally `v`-small as soon as `C` is `v`-small and `D` is
locally `v`-small: a natural transformation is a family of components indexed by the objects
of `C`. -/
@[sga "4 I 1.1.1" "more general"]
theorem CategoryTheory.locallySmall_functor {C : Type u} [Category.{w} C] {D : Type*}
    [Category* D] [Small.{v} C] [LocallySmall.{v} D] : LocallySmall.{v} (C ⥤ D) where
  hom_small F G :=
    small_of_injective (f := fun (α : F ⟶ G) ↦ fun X ↦ α.app X)
      (fun α β h ↦ by ext X; exact congrFun h X)

namespace Shrink

variable {α : Type*} {β : Type*} {γ : Type*} [AddCommGroup α] [AddCommGroup β]
  [AddCommGroup γ] [Small.{v} α] [Small.{v} β] [Small.{v} γ]

/-- An additive map between `v`-small abelian groups, read on the shrunk types. -/
noncomputable def mapAddMonoidHom (f : α →+ β) : Shrink.{v} α →+ Shrink.{v} β :=
  (addEquiv.symm.toAddMonoidHom.comp f).comp addEquiv.toAddMonoidHom

/-- `mapAddMonoidHom f` sends `x` to the shrinking of `f` applied to the unshrinking of `x`. -/
@[simp]
lemma mapAddMonoidHom_apply (f : α →+ β) (x : Shrink.{v} α) :
    mapAddMonoidHom f x = addEquiv.symm (f (addEquiv x)) := rfl

/-- `mapAddMonoidHom` sends the identity to the identity. -/
@[simp]
lemma mapAddMonoidHom_id :
    mapAddMonoidHom (AddMonoidHom.id α) = AddMonoidHom.id (Shrink.{v} α) := by
  ext x
  simp

/-- `mapAddMonoidHom` sends a composite to the composite of the images. -/
lemma mapAddMonoidHom_comp (g : β →+ γ) (f : α →+ β) :
    mapAddMonoidHom (g.comp f) =
      (mapAddMonoidHom g).comp (mapAddMonoidHom (β := β) f) := by
  ext x
  simp

variable {S : Type*} [Semiring S] [Module S α]

/-- Shrinking is compatible with scalar multiplication. -/
lemma addEquiv_smul (c : S) (a : Shrink.{v} α) :
    addEquiv (c • a) = c • addEquiv (α := α) a :=
  (linearEquiv S α).map_smul c a

/-- Unshrinking is compatible with scalar multiplication. -/
lemma addEquiv_symm_smul (c : S) (b : α) :
    (addEquiv (α := α)).symm (c • b) = c • (addEquiv (α := α)).symm b :=
  (linearEquiv S α).symm.map_smul c b

end Shrink

namespace PresheafOfModules

variable {C : Type u} [Category.{w} C] (R : Cᵒᵖ ⥤ RingCat.{r}) [∀ X, Small.{v} (R.obj X)]
  (F : Cᵒᵖ ⥤ Type t) [∀ X, Small.{v} (F.obj X)]

/-- The presheaf of abelian groups sending `X` to the free `R.obj X`-module on `F.obj X`,
shrunk into the module universe `v`.  Unlike `PresheafOfModules.freeAbPresheafU`, whose
sections live in `max r t`, this lands in a prescribed universe `v`, and the universes of the
site and of its homs are unconstrained. -/
noncomputable def freeAbPresheafShrink : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (Shrink.{v} (F.obj X →₀ R.obj X))
  map {X Y} f := AddCommGrpCat.ofHom
    (Shrink.mapAddMonoidHom (Finsupp.mapDomainMapRange (R.map f).hom (F.map f)))
  map_id X := by
    have h : Finsupp.mapDomainMapRange (R.map (𝟙 X)).hom (F.map (𝟙 X)) =
        AddMonoidHom.id (F.obj X →₀ R.obj X) := by
      rw [R.map_id, F.map_id, RingCat.hom_id, types_id]
      exact Finsupp.mapDomainMapRange_id
    apply AddCommGrpCat.hom_ext
    rw [h, Shrink.mapAddMonoidHom_id]
    rfl
  map_comp {X Y Z} f g := by
    have h : Finsupp.mapDomainMapRange (R.map (f ≫ g)).hom (F.map (f ≫ g)) =
        (Finsupp.mapDomainMapRange (R.map g).hom (F.map g)).comp
          (Finsupp.mapDomainMapRange (R.map f).hom (F.map f)) := by
      rw [Finsupp.mapDomainMapRange_comp, R.map_comp, F.map_comp, RingCat.hom_comp, types_comp]
    apply AddCommGrpCat.hom_ext
    rw [h, Shrink.mapAddMonoidHom_comp]
    rfl

/-- The restriction maps of `freeAbPresheafShrink`, read as transports of finitely supported
functions. -/
lemma freeAbPresheafShrink_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : Shrink.{v} (F.obj X →₀ R.obj X)) :
    (freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v}).map f a =
      Shrink.addEquiv.symm
        (Finsupp.mapDomainMapRange (R.map f).hom (F.map f) (Shrink.addEquiv a)) := rfl

/-- The sections of `freeAbPresheafShrink` over `X` are a module over `R.obj X`. -/
noncomputable instance (X : Cᵒᵖ) :
    Module (R.obj X) ((freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v}).obj X) :=
  inferInstanceAs (Module (R.obj X) (Shrink.{v} (F.obj X →₀ R.obj X)))

/-- The restriction maps of `freeAbPresheafShrink` are semilinear. -/
lemma freeAbPresheafShrink_map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (c : R.obj X)
    (a : Shrink.{v} (F.obj X →₀ R.obj X)) :
    (freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v}).map f (c • a) =
      R.map f c • (freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v}).map f a := by
  show Shrink.addEquiv.symm (Finsupp.mapDomainMapRange (R.map f).hom (F.map f)
      (Shrink.addEquiv (c • a))) =
    R.map f c • Shrink.addEquiv.symm (Finsupp.mapDomainMapRange (R.map f).hom (F.map f)
      (Shrink.addEquiv a))
  rw [Shrink.addEquiv_smul, Finsupp.mapDomainMapRange_smul, Shrink.addEquiv_symm_smul]

/-- The free presheaf of modules on a presheaf of types `F`, in a module universe
independent of the universes of the site, of its homs and of the rings. -/
noncomputable def freeObjShrink : PresheafOfModules.{v} R :=
  ofPresheaf (freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (fun {_ _} f c a ↦ freeAbPresheafShrink_map_smul R F f c a)

section Desc

variable {R F} {M : PresheafOfModules.{v} R} (φ : ∀ X, F.obj X → M.obj X)
  (hφ : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (i : F.obj X), φ Y (F.map f i) = M.map f (φ X i))

include hφ in
/-- The morphism of presheaves of abelian groups out of `freeAbPresheafShrink R F` determined
by a natural family of maps `F.obj X → M.obj X`. -/
noncomputable def freeAbDescShrink :
    (freeAbPresheafShrink R F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) ⟶ M.presheaf where
  app X := AddCommGrpCat.ofHom
    ((Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X)).toAddMonoidHom.comp
      Shrink.addEquiv.toAddMonoidHom)
  naturality X Y f := by
    have key : (Finsupp.lift (M.obj Y) (R.obj Y) (F.obj Y) (φ Y)).toAddMonoidHom.comp
          (Finsupp.mapDomainMapRange (R.map f).hom (F.map f)) =
        (M.presheaf.map f).hom.comp
          (Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X)).toAddMonoidHom := by
      apply Finsupp.addHom_ext
      intro i c
      change Finsupp.lift (M.obj Y) (R.obj Y) (F.obj Y) (φ Y)
            (Finsupp.mapDomainMapRange (R.map f).hom (F.map f) (Finsupp.single i c)) =
          M.map f (Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) (Finsupp.single i c))
      rw [Finsupp.mapDomainMapRange_single, Finsupp.lift_apply, Finsupp.lift_apply,
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
        hφ f i, M.map_smul]
      rfl
    apply AddCommGrpCat.hom_ext
    ext x
    have hx := DFunLike.congr_fun key (Shrink.addEquiv x)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe] at hx
    change Finsupp.lift (M.obj Y) (R.obj Y) (F.obj Y) (φ Y)
        (Shrink.addEquiv (Shrink.addEquiv.symm
          (Finsupp.mapDomainMapRange (R.map f).hom (F.map f) (Shrink.addEquiv x)))) = _
    rw [AddEquiv.apply_symm_apply]
    exact hx

include hφ in
/-- The morphism of presheaves of modules out of `freeObjShrink R F` determined by a natural
family of maps `F.obj X → M.obj X`. -/
noncomputable def freeObjDescShrink : (freeObjShrink R F : PresheafOfModules.{v} R) ⟶ M :=
  homMk (freeAbDescShrink φ hφ) (fun X c a ↦
    (congrArg (fun z ↦ Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X) z)
        (Shrink.addEquiv_smul c a)).trans
      (map_smul (Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X)) c _))

include hφ in
/-- The value of `freeObjDescShrink` on a generating section. -/
lemma freeObjDescShrink_app_single (X : Cᵒᵖ) (i : F.obj X) (c : R.obj X) :
    (freeObjDescShrink φ hφ).app X (Shrink.addEquiv.symm (Finsupp.single i c)) =
      c • φ X i := by
  show Finsupp.lift (M.obj X) (R.obj X) (F.obj X) (φ X)
      (Shrink.addEquiv (Shrink.addEquiv.symm (Finsupp.single i c))) = c • φ X i
  rw [AddEquiv.apply_symm_apply, Finsupp.lift_apply, Finsupp.sum_single_index (by simp)]

end Desc

section Separator

variable [LocallySmall.{v} C]

/-- The free presheaf of modules on the Yoneda presheaf at `X`, in the module universe `v`.
This is the generator at `X`; it is available at a prescribed `v` because the site is locally
`v`-small and the rings are `v`-small. -/
noncomputable def freeYonedaShrink (X : C) : PresheafOfModules.{v} R :=
  freeObjShrink R (yoneda.obj X)

/-- **Every section of a presheaf of modules is in the image of a map from a generator.**  The
map sends the tautological generating section over `X` to the given section. -/
lemma exists_freeYonedaShrink_hom {M : PresheafOfModules.{v} R} (X : Cᵒᵖ) (x : M.obj X) :
    ∃ h : (freeObjShrink R (yoneda.obj X.unop) : PresheafOfModules.{v} R) ⟶ M,
      h.app X (Shrink.addEquiv.symm (Finsupp.single (𝟙 X.unop) 1)) = x := by
  have hφ : ∀ ⦃Y Z : Cᵒᵖ⦄ (f : Y ⟶ Z) (g : (yoneda.obj X.unop).obj Y),
      M.restrictₛₗ ((yoneda.obj X.unop).map f g).op x =
        M.map f (M.restrictₛₗ g.op x) := by
    intro Y Z f g
    show M.map ((f.unop ≫ g).op) x = M.map f (M.map g.op x)
    rw [← M.map_comp_apply]
    rfl
  refine ⟨freeObjDescShrink (fun Y g ↦ M.restrictₛₗ g.op x) hφ, ?_⟩
  rw [freeObjDescShrink_app_single, one_smul]
  show M.map (𝟙 X) x = x
  rw [M.map_id]
  simp
  rfl

/-- **The free presheaves of modules on the Yoneda presheaves are a separating family** of
`PresheafOfModules.{v} R`, for any module universe `v` with the rings `v`-small and the site
locally `v`-small. -/
lemma freeYonedaShrink_isSeparating :
    ObjectProperty.IsSeparating
      (.ofObj (freeYonedaShrink R) : ObjectProperty (PresheafOfModules.{v} R)) := by
  intro M N f₁ f₂ h
  ext X x
  obtain ⟨g, hg⟩ := exists_freeYonedaShrink_hom R X x
  have e₂ := congrArg
    (fun (p : (freeObjShrink R (yoneda.obj X.unop) : PresheafOfModules.{v} R) ⟶ N) ↦
      p.app X (Shrink.addEquiv.symm (Finsupp.single (𝟙 X.unop) 1))) (h _ ⟨X.unop⟩ g)
  rw [← hg]
  exact e₂

/-- **Presheaves of modules have a separator**, with the universes of the site, of its homs,
of the rings and of the modules independent: it is the coproduct of the free presheaves of
modules on the Yoneda presheaves, which is indexed by the objects of the site and so exists
once the site is `v`-small. -/
theorem hasSeparator_of_univLE [Small.{v} C] :
    HasSeparator (PresheafOfModules.{v} R) :=
  ⟨_, (freeYonedaShrink_isSeparating R).isSeparator_coproduct⟩

end Separator

omit [∀ X, Small.{v} (R.obj X)] in
/-- Presheaves of modules are locally `v`-small when the site is `v`-small: a morphism is a
family of semilinear maps between modules in `Type v`, indexed by the objects of the site. -/
theorem locallySmall_of_small [Small.{v} C] : LocallySmall.{v} (PresheafOfModules.{v} R) :=
  have : LocallySmall.{v} (Cᵒᵖ ⥤ AddCommGrpCat.{v}) := locallySmall_functor
  locallySmall_of_faithful (toPresheaf R)

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [UnivLE.{w, v}] [UnivLE.{r, v}] [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- Sheaves of modules are locally `v`-small, with the site, hom, ring and module universes
independent, under `UnivLE` between them. -/
theorem locallySmall_of_univLE : LocallySmall.{v} (SheafOfModules.{v} R) :=
  have : LocallySmall.{v} (PresheafOfModules.{v} R.obj) :=
    PresheafOfModules.locallySmall_of_small R.obj
  locallySmall_of_faithful (SheafOfModules.forget R)

/-- **Sheaves of modules have a separator**, with the universes of the site, of its homs, of
the rings and of the modules independent, under `UnivLE` between them: the separator of
presheaves of modules is carried across the sheafification adjunction. -/
theorem hasSeparator_of_univLE : HasSeparator (SheafOfModules.{v} R) :=
  have : HasSeparator (PresheafOfModules.{v} R.obj) :=
    PresheafOfModules.hasSeparator_of_univLE R.obj
  HasSeparator.of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

/-- **Sheaves of modules form a Grothendieck abelian category**, with the universes of the
site, of its homs, of the rings and of the modules independent, under `UnivLE` between them.
Mathlib's `SheafOfModules.instIsGrothendieckAbelian` requires all of them to agree; the
separator is the condition this generalizes, filtered colimits and their exactness being
already available at independent universes. -/
theorem isGrothendieckAbelian_of_univLE :
    IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) where
  locallySmall := locallySmall_of_univLE R
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules R
  hasSeparator := hasSeparator_of_univLE R

/-- **Sheaves of modules have enough injectives**, with the universes of the site, of its
homs, of the rings and of the modules independent, under `UnivLE` between them. -/
theorem enoughInjectives_of_univLE : EnoughInjectives (SheafOfModules.{v} R) :=
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) := isGrothendieckAbelian_of_univLE R
  inferInstance

end SheafOfModules

end
