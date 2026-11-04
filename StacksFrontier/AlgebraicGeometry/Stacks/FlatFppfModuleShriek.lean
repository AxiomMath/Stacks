module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules
public import Mathlib.CategoryTheory.Adjunction.Lifting.Left
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Lower shriek for modules on the flat-fppf site (Stacks 0789, part (2), first assertion)

Let `𝒳` be an algebraic stack over `S` and let
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the morphism of ringed topoi of
**Stacks 0788** (2)(f). The first assertion of **Stacks 0789** part (2) is that pullback of
sheaves of modules along `g` admits a left adjoint

`g_! : Mod(𝒳_{flat,fppf}, 𝒪_{𝒳_{flat,fppf}}) ⟶ Mod(𝒳_{fppf}, 𝒪_𝒳)`.

That is `AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_modulePullback`, with `g_!` itself
and its defining adjunction named below.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.moduleShriek`: the functor `g_!` on sheaves of modules,
  the left adjoint supplied by the result below. It is the module-valued companion of
  `AlgebraicGeometry.Stack.FlatFppf.setsShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.abelianShriek` of **Stacks 0788** (2)(c), (2)(d).
* `AlgebraicGeometry.Stack.FlatFppf.moduleShriekAdjunction`: its defining adjunction
  `g_! ⊣ g^*`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_modulePullback`: **Stacks 0789**,
  part (2), first assertion — pullback of sheaves of modules along the flat-fppf morphism of
  ringed topoi admits a left adjoint.
* `AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_moduleRestriction`: the same assertion read
  at restriction of sheaves of modules along the inclusion of the flat objects, which is the
  form the proof is carried out in.
* `AlgebraicGeometry.presheafModulePushforward_isRightAdjoint_of_essentiallySmall`: the
  general input — pushforward of presheaves of modules along a functor out of an essentially
  small category admits a left adjoint.

## Implementation notes

### Why the general lemma is needed, and what it replaces

Mathlib builds the left adjoint of `SheafOfModules.pushforward` out of the presheaf-level left
adjoint by sheafifying (`CategoryTheory.SheafOfModules.PullbackConstruction.adjunction`), so the
whole content is the presheaf-level statement plus the two sheafification hypotheses
`HasWeakSheafify` and `WEqualsLocallyBijective` on the target site. Both sheafification
hypotheses are already available for this site, as
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_addCommGrpCat`,
`AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_addCommGrpCat` and
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_associatedTopology_ab`; only the last of the four,
local bijectivity on the ambient fppf site, is added here, and it is one application of
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`.

The presheaf-level statement is the one thing genuinely absent. `StacksTag03D2` has it, but only
for sites that are literally `SmallCategory`; the flat-fppf site is a `Type (u+1)` with morphisms
in `Type u` and is *essentially* small, not small, so that form does not apply. The lemma here is
therefore stated for an essentially small source category, which is the generality this site
needs — and the generality in which it is a statement about presheaves of modules and nothing
else. It is a candidate generalisation of `StacksTag03D2.presheafPushforward_isRightAdjoint`.

### The route

Essential smallness of the source makes the comma categories `CostructuredArrow F.op Y`
essentially small, so the pointwise left Kan extension of a presheaf of types along `F.op`
exists; restriction of presheaves of types therefore has a left adjoint. Composing with the
free/forget adjunction for presheaves of modules makes pushforward a right adjoint *after*
forgetting to presheaves of types, and the free functor's counit is a regular epimorphism, so
`CategoryTheory.isRightAdjoint_triangle_lift` lifts the adjoint through the forgetful functor.

### The two spellings of `g^*`

The source's `g^*` is the pullback of sheaves of modules of **Stacks 03D6** part (2), which is
`Stacks.Sheaves.RingedToposModules.pullbackModules` applied to
`AlgebraicGeometry.Stack.FlatFppf.ringedToposModulesHom`. The proof is carried out at
restriction of modules along the inclusion of the flat objects and transported along
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`, which is **Stacks 0788**, `flat_ringed`,
clause (c): the identification of the two. Both forms are recorded, because the restriction form
is the one a sheaf-theoretic argument wants and the pullback form is the one the source states.

As in `StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules`, the sheafification facts are
`theorem`s made local instances rather than global ones, so the statements here carry those
proofs in their own terms. That is the established shape for this layer, and the reason the two
results below are in the same file as the attribute block.

## References

* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry

universe u u₁ u₂ w

/-- Pushforward of presheaves of modules along a functor whose source is essentially small
admits a left adjoint.

The coefficient universe is that of the sections, and the source category is essentially small
in it; neither category need be small. This is the generality the flat-fppf site of an algebraic
stack needs: it is a `Type (u+1)` with morphisms in `Type u`.

For sites that are literally small the statement is
`StacksTag03D2.presheafPushforward_isRightAdjoint`. -/
theorem presheafModulePushforward_isRightAdjoint_of_essentiallySmall
    {C : Type u₁} [Category.{u} C] {D : Type u₂} [Category.{u} D]
    [EssentiallySmall.{u} C] {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}}
    {T : Cᵒᵖ ⥤ RingCat.{u}} (φ : T ⟶ F.op ⋙ R) :
    (PresheafOfModules.pushforward.{u} φ).IsRightAdjoint := by
  have h : ∀ M, RegularEpi ((PresheafOfModules.freeAdjunction T).counit.app M) :=
    fun M => regularEpiOfEpi _
  have _ : ∀ P : Cᵒᵖ ⥤ Type u, F.op.HasPointwiseLeftKanExtension P := fun P Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u} (CostructuredArrow F.op Y) (Type u)
    infer_instance
  have _ := (F.op.lanAdjunction (Type u)).isRightAdjoint
  have _ := (PresheafOfModules.freeAdjunction R).isRightAdjoint
  have : (PresheafOfModules.pushforward.{u} φ ⋙ PresheafOfModules.toPresheaf T ⋙
      (Functor.whiskeringRight _ _ _).obj (forget Ab)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso (Iso.refl
      ((PresheafOfModules.toPresheaf R ⋙
        (Functor.whiskeringRight _ _ _).obj (forget Ab)) ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj F.op))
  exact isRightAdjoint_triangle_lift _ (PresheafOfModules.freeAdjunction T) h

namespace Stack.FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- On the fppf site of an algebraic stack, the sheafification equivalences for
`AddCommGrpCat.{u}`-valued presheaves are the local bijections. As for
`AlgebraicGeometry.Stack.FlatFppf.hasSheafify_associatedTopology_ab`, this is not the
size-matched statement and it holds because the site is essentially small. -/
theorem wEqualsLocallyBijective_fppfTopology_addCommGrpCat :
    (fppfTopology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

attribute [local instance] isContinuous_inclusion_topology
  hasSheafify_addCommGrpCat wEqualsLocallyBijective_addCommGrpCat
  hasSheafify_associatedTopology_ab wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-- Restriction of sheaves of modules along the inclusion of the flat objects admits a left
adjoint. This is **Stacks 0789** part (2), first assertion, read through **Stacks 0788**,
`flat_ringed`, clause (c), which identifies that restriction with the pullback of modules along
the flat-fppf morphism of ringed topoi. -/
theorem isRightAdjoint_moduleRestriction :
    (moduleRestriction B S hS 𝒳).IsRightAdjoint := by
  unfold moduleRestriction
  refine Adjunction.isRightAdjoint
    (@SheafOfModules.PullbackConstruction.adjunction _ _ _ _ _ _ _ _ _ _ _
      (presheafModulePushforward_isRightAdjoint_of_essentiallySmall _) _ _)

/-- **Stacks 0789**, part (2), first assertion: pullback of sheaves of modules along the
flat-fppf morphism of ringed topoi `g` admits a left adjoint `g_!`.

Registered as an instance, because the functor `g_!` and its adjunction are then the canonical
choices it supplies. -/
@[stacks 0789 "flat_module_shriek"]
instance isRightAdjoint_modulePullback :
    (RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
      (ringedToposModulesHom B S hS 𝒳)).IsRightAdjoint :=
  have := isRightAdjoint_moduleRestriction B S hS 𝒳
  Functor.isRightAdjoint_of_iso (modulePullbackIso B S hS 𝒳).symm

/-- The lower-shriek functor `g_!` on sheaves of modules for the flat-fppf site: the left
adjoint of module pullback supplied by
`AlgebraicGeometry.Stack.FlatFppf.isRightAdjoint_modulePullback`. -/
noncomputable def moduleShriek :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (ringedTopos B S hS 𝒳).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u} (fppfRingedTopos B S hS 𝒳).O) :=
  (RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1}
    (ringedToposModulesHom B S hS 𝒳)).leftAdjoint

/-- The defining adjunction `g_! ⊣ g^*` of module-valued lower shriek for the flat-fppf
site. -/
noncomputable def moduleShriekAdjunction :
    moduleShriek B S hS 𝒳 ⊣
      RingedToposHom.pullbackModules.{u, u, u, u + 1, u, u + 1} (ringedToposModulesHom B S hS 𝒳) :=
  Adjunction.ofIsRightAdjoint _

end Stack.FlatFppf

end AlgebraicGeometry

end
