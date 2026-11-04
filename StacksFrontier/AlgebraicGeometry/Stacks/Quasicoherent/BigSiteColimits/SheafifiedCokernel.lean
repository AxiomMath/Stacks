module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The cokernel of a morphism of sheaves of modules is the sheafification of the presheaf cokernel

Let `a : Q ⟶ P` be a morphism of sheaves of modules over a sheaf of rings `R` on a site, and let
`b : P ⟶ N` exhibit `N` as a cokernel of `a` *in sheaves of modules*.  Taking the cokernel of the
underlying morphism `a.val` of presheaves of modules instead produces a different object, and the
universal property of the sheaf cokernel supplies a comparison `cokernel a.val ⟶ N.val` from it.
This file proves that comparison is the sheafification unit up to isomorphism, and in particular
that it is locally injective: two sections of the presheaf cokernel with the same image in `N`
agree along the arrows of a covering sieve.

The argument uses no cohomology and no base change.  Sheafification of presheaves of modules is
the left adjoint of the forgetful functor to presheaves of modules, and the counit of that
adjunction is an isomorphism, so a sheaf of modules is the sheafification of its own presheaf of
sections.  A left adjoint preserves colimits, so it carries the presheaf cokernel cofork of `a.val`
to a cokernel cofork of its image; the counit carries the sheaf cokernel cofork of `a` to a second
cokernel cofork of the same morphism; and the comparison between the two cocone points of two
colimit coforks is an isomorphism.  Local injectivity of the comparison then follows from local
bijectivity of the sheafification unit, which is what `J.WEqualsLocallyBijective AddCommGrpCat`
provides.

## Main results

* `CategoryTheory.Limits.isIso_of_isColimit_cofork`: a morphism of cocone points of two colimit
  coforks of one parallel pair which is compatible with the projections is an isomorphism.
* `CategoryTheory.Presheaf.exists_mem_forall_map_eq`: a locally injective morphism of presheaves of
  types in the plain form, **two sections with the same image agree along a covering sieve**.
* `PresheafOfModules.isColimit_cokernelCofork_sheafification_val`: **the sheaf cokernel of `a`,
  read through the sheafification counit, is a cokernel of the sheafification of `a.val`.**
* `PresheafOfModules.isIso_sheafification_map_cokernelDesc`: **the sheafification of the comparison
  from the presheaf cokernel to the sheaf cokernel is an isomorphism**, which is the statement that
  the sheaf cokernel is the sheafification of the presheaf cokernel.
* `PresheafOfModules.isLocallyInjective_of_isIso_sheafification_map`: a morphism of presheaves of
  modules whose sheafification is an isomorphism is locally injective.
* `SheafOfModules.isLocallyInjective_toPresheaf_map_cokernelDesc`: **the comparison from the
  presheaf cokernel of a presentation to the sheaf it presents is locally injective.**
* `SheafOfModules.exists_mem_forall_map_eq_of_cokernelDesc_app_eq`: the same, in the plain form
  which asks for a covering sieve along which two sections identified by the comparison agree.

## Implementation notes

The counit of the sheafification adjunction is given a name,
`PresheafOfModules.sheafificationCounit`, with its target spelled as the sheafification of the
presheaf of sections rather than as the value of the composite of the two adjoint functors.  The
two spellings are definitionally equal but not syntactically so, and a goal stated in the second
is not type-correct at the transparency `rewrite` uses, so every rewrite against such a goal fails
with a spurious report that the pattern does not occur.  Naming the morphism fixes one spelling,
and the naturality of the counit is restated for it.

The comparison of coefficient rings at which sheafification is taken is the identity of the
structure sheaf, whose local bijectivity is an instance because it is an isomorphism.

The plain form of local injectivity is stated for presheaves of types, which is the generality of
`CategoryTheory.Presieve.IsSheafFor`, and is obtained from the equalizer sieve of the two sections;
a consumer holding presheaves of modules composes with `CategoryTheory.forget`.

Every universe here is free: the four universes of the morphisms of the site, of its objects, of
the coefficient rings and of the sections are pairwise unrelated in each statement of the file,
with no universe pinned to another and none raised by one.  So a consumer need not reinstantiate
anything, and in particular the universe of the sections of the sheaves of modules is unconstrained
by the site.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r m

namespace CategoryTheory.Limits

/-- **A compatible morphism between the cocone points of two colimit coforks of one parallel pair
is an isomorphism.**  Each colimit describes the other, and the two descriptions are mutually
inverse because a morphism out of a colimit cofork is determined by its composite with the
projection. -/
theorem isIso_of_isColimit_cofork {D : Type u} [Category.{v} D] {X Y : D} {f g : X ⟶ Y}
    {c c' : Cofork f g} (hc : IsColimit c) (hc' : IsColimit c') {φ : c.pt ⟶ c'.pt}
    (hφ : c.π ≫ φ = c'.π) : IsIso φ := by
  have := IsColimit.hom_isIso hc hc' (Cofork.mkHom φ hφ)
  exact (Cocone.forget _).map_isIso (Cofork.mkHom φ hφ)

end CategoryTheory.Limits

namespace CategoryTheory.Presheaf

/-- **Two sections of a presheaf of types with the same image under a locally injective morphism
agree along the arrows of a covering sieve.**  The sieve is the equalizer sieve of the two
sections, whose arrows are by definition those along which they agree.

This is the plain form of `CategoryTheory.Presheaf.IsLocallyInjective` which the sheaf-condition
arguments of a big site consume. -/
theorem exists_mem_forall_map_eq {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ Type w} (θ : F ⟶ G) [IsLocallyInjective J θ] (Z : C) (x y : F.obj (op Z))
    (h : θ.app (op Z) x = θ.app (op Z) y) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (f : V ⟶ Z), S f → F.map f.op x = F.map f.op y := by
  refine ⟨equalizerSieve (F := F) (X := op Z) x y, equalizerSieve_mem J θ x y h,
    fun _ _ hf => ?_⟩
  exact hf

end CategoryTheory.Presheaf

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **A sheaf of modules is the sheafification of its own presheaf of sections**, through the
counit of the sheafification adjunction at the identity comparison of coefficient rings.

The target of the counit is spelled as the sheafification of the presheaf of sections, which is
definitionally but not syntactically the value there of the composite of the two adjoint
functors. -/
noncomputable def sheafificationCounit (M : SheafOfModules.{m} R) :
    (sheafification.{m} (𝟙 R.obj)).obj M.val ⟶ M :=
  (sheafificationAdjunction (𝟙 R.obj)).counit.app M

/-- The comparison `sheafificationCounit M` of a sheaf of modules with the sheafification of its
presheaf of sections is an isomorphism. -/
instance (M : SheafOfModules.{m} R) : IsIso (sheafificationCounit M) :=
  inferInstanceAs (IsIso ((sheafificationAdjunction (𝟙 R.obj)).counit.app M))

/-- The comparison of a sheaf of modules with the sheafification of its presheaf of sections is
natural. -/
lemma sheafificationCounit_naturality {M N : SheafOfModules.{m} R} (f : M ⟶ N) :
    (sheafification.{m} (𝟙 R.obj)).map f.val ≫ sheafificationCounit N =
      sheafificationCounit M ≫ f :=
  (sheafificationAdjunction (𝟙 R.obj)).counit.naturality f

/-- The sheafification unit is locally injective, which is what
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` says about the sheafification of
presheaves of abelian groups: the underlying morphism of presheaves of abelian groups of the unit
is that sheafification unit. -/
instance isLocallyInjective_toPresheaf_map_sheafificationAdjunction_unit_app
    (M : PresheafOfModules.{m} R.obj) :
    Presheaf.IsLocallyInjective J ((toPresheaf R.obj).map
      ((sheafificationAdjunction (𝟙 R.obj)).unit.app M)) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J M.presheaf))

/-- **A cokernel in sheaves of modules, read through the sheafification counit, is a cokernel of
the sheafification of the underlying morphism of presheaves of modules.**

Nothing is preserved here: the two coforks have isomorphic sources and isomorphic targets, by the
counit, and the square commutes by naturality of the counit, so the colimit transports. -/
noncomputable def isColimit_cokernelCofork_sheafification_val
    {Q P N : SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) :
    IsColimit (CokernelCofork.ofπ (sheafificationCounit P ≫ b)
      (by rw [← Category.assoc, sheafificationCounit_naturality a, Category.assoc, hab,
        comp_zero]) :
      Cofork ((sheafification.{m} (𝟙 R.obj)).map a.val) 0) := by
  refine Cofork.isColimitOfIsos _ hN _ (asIso (sheafificationCounit Q)).symm
    (asIso (sheafificationCounit P)).symm (Iso.refl N) ?_ ?_ ?_
  · dsimp only [Iso.symm_hom, asIso_inv]
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← sheafificationCounit_naturality a,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · dsimp only [Iso.symm_hom, asIso_inv]
    rw [comp_zero, zero_comp]
  · simp

/-- **The sheaf cokernel of a morphism of sheaves of modules is the sheafification of the presheaf
cokernel of the underlying morphism of presheaves of modules.**

Stated as the comparison from the presheaf cokernel to the sheaf cokernel becoming an isomorphism
after sheafification.  Sheafification is a left adjoint, so it carries the presheaf cokernel cofork
to a cokernel cofork of the sheafification of `a.val`;
`PresheafOfModules.isColimit_cokernelCofork_sheafification_val` is a second one with the same
parallel pair; and the comparison, composed with the counit, is compatible with the two
projections, hence is an isomorphism, from which the comparison itself is one. -/
theorem isIso_sheafification_map_cokernelDesc
    {Q P N : SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (hab' : a.val ≫ b.val = 0) :
    IsIso ((sheafification.{m} (𝟙 R.obj)).map (cokernel.desc a.val b.val hab')) := by
  have key : IsIso ((sheafification.{m} (𝟙 R.obj)).map (cokernel.desc a.val b.val hab') ≫
      sheafificationCounit N) := by
    refine isIso_of_isColimit_cofork
      (isColimitOfHasCokernelOfPreservesColimit (sheafification.{m} (𝟙 R.obj)) a.val)
      (isColimit_cokernelCofork_sheafification_val a b hab hN) ?_
    have h : (sheafification.{m} (𝟙 R.obj)).map (cokernel.π a.val) ≫
        (sheafification.{m} (𝟙 R.obj)).map (cokernel.desc a.val b.val hab') =
        (sheafification.{m} (𝟙 R.obj)).map b.val := by
      rw [← Functor.map_comp, cokernel.π_desc]
    rw [Cofork.π_ofπ, Cofork.π_ofπ, ← Category.assoc _ _ (sheafificationCounit N), h]
    exact sheafificationCounit_naturality b
  exact IsIso.of_isIso_comp_right _ (sheafificationCounit N)

/-- **A morphism of presheaves of modules whose sheafification is an isomorphism is locally
injective.**  The naturality square of the sheafification unit factors the morphism, composed with
the locally injective unit at its target, as the locally injective unit at its source followed by
an isomorphism; a composite which is locally injective and whose second factor is so has a locally
injective first factor. -/
theorem isLocallyInjective_of_isIso_sheafification_map
    {M N : PresheafOfModules.{m} R.obj} (u : M ⟶ N)
    (hu : IsIso ((sheafification.{m} (𝟙 R.obj)).map u)) :
    Presheaf.IsLocallyInjective J ((toPresheaf R.obj).map u) := by
  have := hu
  have hnat : u ≫ (sheafificationAdjunction (𝟙 R.obj)).unit.app N =
      (sheafificationAdjunction (𝟙 R.obj)).unit.app M ≫
        (SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).map
          ((sheafification.{m} (𝟙 R.obj)).map u) :=
    (sheafificationAdjunction (𝟙 R.obj)).unit.naturality u
  have hiso : Presheaf.IsLocallyInjective J ((toPresheaf R.obj).map
      ((SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).map
        ((sheafification.{m} (𝟙 R.obj)).map u))) := inferInstance
  rw [← Presheaf.isLocallyInjective_comp_iff J ((toPresheaf R.obj).map u)
      ((toPresheaf R.obj).map ((sheafificationAdjunction (𝟙 R.obj)).unit.app N)),
    ← Functor.map_comp, hnat, Functor.map_comp]
  exact Presheaf.isLocallyInjective_comp J _ _

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {Q P N : SheafOfModules.{m} R}

/-- **The comparison from the presheaf cokernel of a presentation to the sheaf it presents is
locally injective.**

Let `b : P ⟶ N` be a cokernel of `a : Q ⟶ P` in sheaves of modules.  The universal property of the
cokernel of `a.val` in presheaves of modules produces a comparison `cokernel a.val ⟶ N.val`, and
two sections of the presheaf cokernel over an object with the same image in `N` agree along the
arrows of some covering sieve of that object.

This is the separatedness half of the statement that `N` is the sheafification of the presheaf
cokernel; `PresheafOfModules.isIso_sheafification_map_cokernelDesc` is the statement itself.  No
cohomology and no base change enters: the comparison becomes an isomorphism after sheafification,
and the sheafification unit is locally bijective. -/
theorem isLocallyInjective_toPresheaf_map_cokernelDesc
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (hab' : a.val ≫ b.val = 0) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (cokernel.desc a.val b.val hab')) :=
  PresheafOfModules.isLocallyInjective_of_isIso_sheafification_map _
    (PresheafOfModules.isIso_sheafification_map_cokernelDesc a b hab hN hab')

/-- **Two sections of the presheaf cokernel of a presentation with the same image in the sheaf it
presents agree along the arrows of a covering sieve.**

`SheafOfModules.isLocallyInjective_toPresheaf_map_cokernelDesc` in the plain form which the
sheaf-condition arguments consume, for the presheaf of types of sections of the presheaf
cokernel. -/
theorem exists_mem_forall_map_eq_of_cokernelDesc_app_eq
    (a : Q ⟶ P) (b : P ⟶ N) (hab : a ≫ b = 0)
    (hN : IsColimit (CokernelCofork.ofπ b hab)) (hab' : a.val ≫ b.val = 0) (Z : C)
    (x y : ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}).obj (op Z))
    (h : (Functor.whiskerRight
          ((PresheafOfModules.toPresheaf R.obj).map (cokernel.desc a.val b.val hab'))
          (CategoryTheory.forget AddCommGrpCat.{m})).app (op Z) x =
        (Functor.whiskerRight
          ((PresheafOfModules.toPresheaf R.obj).map (cokernel.desc a.val b.val hab'))
          (CategoryTheory.forget AddCommGrpCat.{m})).app (op Z) y) :
    ∃ S : Sieve Z, S ∈ J Z ∧ ∀ ⦃V : C⦄ (f : V ⟶ Z), S f →
      ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}).map f.op x =
        ((cokernel a.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}).map f.op y := by
  have := isLocallyInjective_toPresheaf_map_cokernelDesc a b hab hN hab'
  exact Presheaf.exists_mem_forall_map_eq J (Functor.whiskerRight
    ((PresheafOfModules.toPresheaf R.obj).map (cokernel.desc a.val b.val hab'))
    (CategoryTheory.forget AddCommGrpCat.{m})) Z x y h

end SheafOfModules

end
