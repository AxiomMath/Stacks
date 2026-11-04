module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian

/-!
# Functors induced on the homotopy categories of differential graded modules

Let `R` and `R'` be sheaves of rings on sites, let `B` be a sheaf of differential graded
`R`-algebras and let `A'` be a sheaf of differential graded `R'`-algebras. A functor
`F : Mod(B, d) ⟶ Mod(A', d)` which carries homotopic morphisms to homotopic morphisms descends
uniquely to a functor `K(Mod(B, d)) ⟶ K(Mod(A', d))` of homotopy categories, compatibly with
the two quotient functors. The descent is functorial: it takes the identity to the identity and
a composite to the composite, which is the mechanism behind every transitivity statement for
such induced functors.

This is the step "the functor extends to a functor of differential graded categories and hence
induces a functor on the homotopy categories" that the derived pullback of a sheaf of
differential graded modules is built from. The construction of the functor in question,
`M ↦ f^*M ⊗_𝒜 𝒩` for a morphism of ringed topoi `f` and a differential graded
`(𝒜, 𝒜')`-bimodule `𝒩`, is a separate matter and is not available here; see the
implementation notes.

Along the way two elementary facts about homotopies are recorded: subtraction of morphisms of
differential graded modules is degreewise, and a homotopy only depends on the *difference* of
the two morphisms it connects, so that `f` and `g` are homotopic exactly when `f - g` is
null-homotopic.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Homotopy.ofDiffEq` transports a homotopy between two
  morphisms to a homotopy between any other two morphisms with the same degreewise difference.
* `SheafOfModules.DifferentialGradedModule.PreservesHomotopic` is the property of a functor of
  differential graded modules that it carries homotopic morphisms to homotopic morphisms.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.descend` is the functor induced on
  the homotopy categories by such a functor.

## Main results

* `SheafOfModules.DifferentialGradedModule.sub_f`: subtraction of morphisms of differential
  graded modules is degreewise.
* `SheafOfModules.DifferentialGradedModule.homotopic_sub_zero_iff`: two morphisms are homotopic
  exactly when their difference is null-homotopic.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_comp_descend`,
  `...descend_obj` and `...descend_map`: the descended functor is compatible with the quotient
  functors, on objects and on morphisms.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.eq_descend`: it is the unique such
  functor.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.descend_id` and
  `...descend_comp`: descent takes the identity functor to the identity functor and a composite
  to the composite of the descents.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.isIso_quotient_map_of_homotopyInverse`:
  a morphism admitting a homotopy inverse becomes an isomorphism in the homotopy category.

## Implementation notes

The source and the target of the functor are allowed to live over *different* sheaves of rings
on *different* sites, with all their universes independent. This is what the intended
application needs: the derived pullback of
[Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE) takes differential graded modules
over a sheaf of differential graded algebras `ℬ` on one ringed topos to differential graded
modules over a sheaf of differential graded algebras `𝒜'` on another.

Nothing in this file carries a `@[stacks]` attribute, and in particular nothing here claims Tag
0FTE, Tag 0FTI or Tag 0FTJ. Those three tags are statements about the *specific* functor
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩`, about the derived category `D(𝒜, d)` and about the derived tensor
product `- ⊗^𝐋_𝒜 𝒩`, and the objects they speak of do not yet exist in this development: there
is no tensor product of a right differential graded module with a differential graded bimodule
over a sheaf of differential graded algebras (Tag 0FRS), hence no pullback `f^*` of a sheaf of
differential graded modules (Tag 0FRU, which is defined as
`f^*ℳ = f^{-1}ℳ ⊗_{f^{-1}ℬ} 𝒜`), no triangulated structure on the homotopy category (Tag
0FS7), no good differential graded modules and no derived category (Tags 0FS9 and 0FT5). What
*is* proved here is the homotopy-category descent those tags all rest on, stated for an
arbitrary homotopy-preserving functor; it is strictly weaker than any of them, so attaching
their tags to it would misreport what has been established.

The descent itself is `CategoryTheory.Quotient.lift` applied to the homotopy congruence of
`SheafOfModules.DifferentialGradedModule.homotopic_congruence`, so the compatibility with the
quotient functors on objects and on morphisms holds by definition and needs no transport along
an equality of objects. Exactness of the descended functor is not addressed, since the homotopy
category of sheaf differential graded modules has no triangulated structure here yet; the
ingredients for one are the axioms (A), (B) and (C) of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAxiomA.lean` and its two
companions.

`Homotopy.ofDiffEq` is what makes `homotopic_sub_zero_iff` a two-line proof: the `app` and
`map_mul` fields of a homotopy do not mention the two morphisms at all, and the `comm` field
mentions only their degreewise difference, so changing the pair of morphisms without changing
that difference reuses the homotopy verbatim.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
* [Stacks Project, Tag 0FS1](https://stacks.math.columbia.edu/tag/0FS1)
-/

@[expose] public section

open CategoryTheory

universe t a m v u t' a' m' v' u' t'' a'' m'' v'' u''

namespace SheafOfModules

namespace DifferentialGradedModule

section SingleSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- Subtraction of morphisms of differential graded modules is degreewise. -/
@[simp]
theorem sub_f {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) (n : ℤ) :
    (f - g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n - g.toHomologicalComplex.f n := by
  rw [sub_eq_add_neg, add_f, neg_f, ← sub_eq_add_neg]

/-- A homotopy depends on the two morphisms it connects only through their degreewise
difference: the degree `-1` map and its compatibility with the action of the algebra do not
mention them, and the homotopy equation mentions only the difference. So a homotopy between `f`
and `g` is also a homotopy between any `f'` and `g'` with the same difference. -/
def Homotopy.ofDiffEq {M N : DifferentialGradedModule.{t, a, m} A} {f g f' g' : M ⟶ N}
    (h : Homotopy f g)
    (e : ∀ n : ℤ, f'.toHomologicalComplex.f n - g'.toHomologicalComplex.f n =
      f.toHomologicalComplex.f n - g.toHomologicalComplex.f n) :
    Homotopy f' g' where
  app := h.app
  map_mul := h.map_mul
  comm n := (e n).trans (h.comm n)

/-- Two morphisms of differential graded modules are homotopic exactly when their difference is
null-homotopic. -/
theorem homotopic_sub_zero_iff {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) :
    Homotopic (f - g) 0 ↔ Homotopic f g :=
  by constructor <;> rintro ⟨h⟩ <;> exact ⟨h.ofDiffEq fun n => by simp⟩

namespace HomotopyCategory

/-- A morphism of differential graded modules which admits a homotopy inverse becomes an
isomorphism in the homotopy category. -/
theorem isIso_quotient_map_of_homotopyInverse {M N : DifferentialGradedModule.{t, a, m} A}
    (f : M ⟶ N) (g : N ⟶ M) (h₁ : Homotopic (f ≫ g) (𝟙 M)) (h₂ : Homotopic (g ≫ f) (𝟙 N)) :
    IsIso ((quotient A).map f) :=
  ⟨(quotient A).map g,
    by rw [← Functor.map_comp, (quotient_map_eq_iff _ _).2 h₁, (quotient A).map_id],
    by rw [← Functor.map_comp, (quotient_map_eq_iff _ _).2 h₂, (quotient A).map_id]⟩

end HomotopyCategory

end SingleSite

section Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t''}}
  {B : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t', a'} R'}
  {A'' : DifferentialGradedAlgebra.{t'', a''} R''}

/-- A functor of right differential graded modules *preserves homotopy* when it carries
homotopic morphisms to homotopic morphisms. This is what a functor extending to the differential
graded categories does, and it is exactly what is needed for the functor to descend to the
homotopy categories. -/
def PreservesHomotopic
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A') :
    Prop :=
  ∀ {M N : DifferentialGradedModule.{t, a, m} B} (f g : M ⟶ N),
    Homotopic f g → Homotopic (F.map f) (F.map g)

/-- The identity functor preserves homotopy. -/
theorem PreservesHomotopic.id :
    PreservesHomotopic (𝟭 (DifferentialGradedModule.{t, a, m} B)) :=
  fun _ _ h => h

/-- A composite of functors preserving homotopy preserves homotopy. -/
theorem PreservesHomotopic.comp
    {F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A'}
    {G : DifferentialGradedModule.{t', a', m'} A' ⥤ DifferentialGradedModule.{t'', a'', m''} A''}
    (hF : PreservesHomotopic F) (hG : PreservesHomotopic G) :
    PreservesHomotopic (F ⋙ G) :=
  fun f g h => hG _ _ (hF f g h)

namespace HomotopyCategory

/-- The functor induced on the homotopy categories by a functor of right differential graded
modules which preserves homotopy. -/
def descend
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F) :
    HomotopyCategory.{t, a, m} B ⥤ HomotopyCategory.{t', a', m'} A' :=
  CategoryTheory.Quotient.lift _ (F ⋙ quotient A')
    fun _ _ f g h => (quotient_map_eq_iff (F.map f) (F.map g)).2 (hF f g h)

/-- The descended functor factors the original one through the two quotient functors. -/
theorem quotient_comp_descend
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F) :
    quotient B ⋙ descend F hF = F ⋙ quotient A' :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- On an object of the homotopy category represented by a differential graded module, the
descended functor is the original functor. -/
@[simp]
theorem descend_obj
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F) (M : DifferentialGradedModule.{t, a, m} B) :
    (descend F hF).obj ((quotient B).obj M) = (quotient A').obj (F.obj M) :=
  rfl

/-- On a homotopy class represented by a morphism of differential graded modules, the descended
functor is the original functor. -/
@[simp]
theorem descend_map
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F) {M N : DifferentialGradedModule.{t, a, m} B} (f : M ⟶ N) :
    (descend F hF).map ((quotient B).map f) = (quotient A').map (F.map f) :=
  rfl

/-- The descended functor is the only functor of homotopy categories factoring the original one
through the two quotient functors. -/
theorem eq_descend
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F)
    (Φ : HomotopyCategory.{t, a, m} B ⥤ HomotopyCategory.{t', a', m'} A')
    (hΦ : quotient B ⋙ Φ = F ⋙ quotient A') :
    Φ = descend F hF :=
  CategoryTheory.Quotient.lift_unique _ _ _ Φ hΦ

/-- The identity functor descends to the identity functor. -/
theorem descend_id :
    descend (𝟭 (DifferentialGradedModule.{t, a, m} B)) PreservesHomotopic.id = 𝟭 _ :=
  (eq_descend _ _ _ rfl).symm

/-- Descent to the homotopy categories is compatible with composition. -/
theorem descend_comp
    (F : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A')
    (hF : PreservesHomotopic F)
    (G : DifferentialGradedModule.{t', a', m'} A' ⥤ DifferentialGradedModule.{t'', a'', m''} A'')
    (hG : PreservesHomotopic G) :
    descend (F ⋙ G) (hF.comp hG) = descend F hF ⋙ descend G hG :=
  (eq_descend _ _ _ (by
    rw [← Functor.assoc, quotient_comp_descend, Functor.assoc, quotient_comp_descend,
      Functor.assoc])).symm

/-- A natural isomorphism between functors of right differential graded modules which both carry
homotopic morphisms to homotopic morphisms descends to a natural isomorphism between the induced
functors of homotopy categories. -/
noncomputable def descendNatIso
    {F G : DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t', a', m'} A'}
    (hF : PreservesHomotopic F) (hG : PreservesHomotopic G) (e : F ≅ G) :
    descend F hF ≅ descend G hG :=
  CategoryTheory.Quotient.natIsoLift _
    (eqToIso (quotient_comp_descend F hF) ≪≫ Functor.isoWhiskerRight e (quotient A') ≪≫
      eqToIso (quotient_comp_descend G hG).symm)

end HomotopyCategory

end Descent

end DifferentialGradedModule

end SheafOfModules

end
