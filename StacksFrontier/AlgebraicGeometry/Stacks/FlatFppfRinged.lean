module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Flat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# The flat-fppf morphism of ringed topoi (Stacks 0788, `flat_ringed`)

Let `𝒳` be an algebraic stack over `S`. **Stacks 0788** (2)(f) asserts that the morphism of topoi
`g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` of **Stacks 0788** (2)(a) is a *flat morphism of ringed
topoi* once the flat-fppf site is given the restriction of the fppf structure sheaf: that is,
`g⁻¹𝒪_𝒳 = 𝒪_{𝒳_{flat,fppf}}`, that the resulting morphism of ringed topoi is flat, and that
pullback of modules along it is restriction of modules.

The first two of those three are proved here, the third in
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules`. The reason the identification of
the inverse image
with the restriction is available at all — rather than merely up to sheafification — is that the
inclusion of the flat objects is *cocontinuous* as well as continuous (**Stacks 0788** (2)), so
the inverse image of `g` is restriction along the inclusion **on the nose**: that is how
`AlgebraicGeometry.Stack.FlatFppf.toposMorphism` is built. Transporting the commutative ring
operations through a geometric inverse image which is restriction leaves the underlying sheaf of
sets untouched, which is
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`; so `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{flat,fppf}}` is that
comparison, and it is the identity on sections. Flatness of the morphism of ringed topoi then
follows because its inverse-image structure map is that very isomorphism, and an isomorphism of
sheaves of commutative rings is a flat morphism.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.structureSheaf`: **Stacks 0788**, `flat_ringed` — the
  structure sheaf of the flat-fppf site, the restriction of the fppf structure sheaf of
  **Stacks 06TV** along the inclusion of the flat objects.
* `AlgebraicGeometry.Stack.FlatFppf.fppfRingedTopos` and
  `AlgebraicGeometry.Stack.FlatFppf.ringedTopos`: the two ringed topoi of **Stacks 0788** (2)(f).
* `AlgebraicGeometry.Stack.FlatFppf.toposMorphismOnRings`: the morphism of topoi of
  **Stacks 0788** (2)(a), read at the universe of the sections of the structure sheaf.
* `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism`: **Stacks 0788**, `flat_ringed` — the
  morphism of ringed topoi.
* `AlgebraicGeometry.Stack.FlatFppf.moduleRestriction`: **Stacks 0788**, `flat_ringed` —
  restriction of sheaves of modules along the inclusion of the flat objects, over the two
  structure sheaves.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.structureSheafIso`: **Stacks 0788**, `flat_ringed` —
  `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{flat,fppf}}`.
* `AlgebraicGeometry.Stack.FlatFppf.structureSheafIso_apply`: that comparison is the identity on
  sections, so it is not an arbitrary automorphism of the restricted structure sheaf.
* `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism_isFlat`: **Stacks 0788**,
  `flat_ringed` — the morphism of ringed topoi is flat, in the sense of **Stacks 04JB**.
* `AlgebraicGeometry.hasSheafCompose_forget_ringCat` and
  `AlgebraicGeometry.hasSheafCompose_forget_commRingCat`: on any site, and for any universe of
  sections, the forgetful functors of rings and of commutative rings preserve the sheaf
  condition.

## Implementation notes

### Where the third assertion is

The third assertion of **Stacks 0788** (2)(f), that *pullback of sheaves of modules along `g` is
restriction of sheaves of modules*, is
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`, in
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules`. It is kept in a separate module
because the pullback of sheaves of modules sheafifies a tensor product and so asks for
sheafification hypotheses on the flat-fppf site that nothing in this file needs.
`AlgebraicGeometry.Stack.FlatFppf.moduleRestriction` is the restriction functor that assertion
compares the pullback with, and it carries the tag for the same reason
`AlgebraicGeometry.Stack.FlatFppf.structureSheaf` does: it is the object the clause is about.

### The essential smallness of the flat-fppf site, and where it comes from

Every statement of **Stacks 0788** (2)(f) is about the topos of sheaves of sets *at the universe
of the sections of the structure sheaf*, which for `AlgebraicGeometry.Stack.structureSheaf` is one
universe below the objects of the site. The morphism of topoi at that universe needs the right Kan
extension along the inclusion to exist pointwise, and that is exactly a smallness condition on the
site: the declarations from `AlgebraicGeometry.Stack.FlatFppf.toposMorphismOnRings` onwards need
`CategoryTheory.EssentiallySmall.{u} (AlgebraicGeometry.Stack.FlatFppf B S hS 𝒳)`.

It is supplied, not assumed, so those statements are unconditional. It is exactly the condition
`StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite` was written to account for, and the
two declarations of that file reduce it to its inputs: composing
`AlgebraicGeometry.Stack.essentiallySmall_fullSubsite` with
`AlgebraicGeometry.Stack.essentiallySmall_obj` discharges it from essential smallness of the
size-bounded category of schemes — which is
`AlgebraicGeometry.BigFppfSite.essentiallySmall_schemes` of
`StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties`, registered as an instance in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness` — together with essential
smallness of each fibre `𝒳(U)` of the stack, which is a descent statement about its smooth
presentation and is
`AlgebraicGeometry.Stack.essentiallySmall_fiber_algebraicStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness`. That composition is registered
there as the instance
`AlgebraicGeometry.Stack.essentiallySmall_flatFppf_algebraicStack`, which instance search finds at
each use site below. `AlgebraicGeometry.Stack.FlatFppf.structureSheaf`, the two ringed topoi and
`AlgebraicGeometry.Stack.FlatFppf.moduleRestriction` do not need it at all.

### Which topology, and why nothing here is conditional on the choice

The flat-fppf site carries two descriptions of its topology, and they are *equal*
(`AlgebraicGeometry.Stack.FlatFppf.inclusionTopology_eq_topology`). The statements below use
`AlgebraicGeometry.Stack.FlatFppf.topology`, the one generated by the inherited *chosen* covering
families, since that is the topology **Stacks 0787** puts on the flat-fppf site. Both continuity
and cocontinuity of the inclusion are available there —
`AlgebraicGeometry.Stack.FlatFppf.isContinuous_inclusion_topology` and
`AlgebraicGeometry.Stack.FlatFppf.isCocontinuous_inclusion_topology` — so no choice is being
hedged and no third topology is introduced.

### The two sheaf-condition witnesses

`AlgebraicGeometry.RingedTopos` and `AlgebraicGeometry.RingedToposHom` ask that composing with
`CategoryTheory.forget RingCat`, with `CategoryTheory.forget₂ CommRingCat RingCat` and — for
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` — with
`CategoryTheory.forget CommRingCat` preserves the sheaf condition. Here the site lives one
universe above the sections, so none of the three is an instance by Mathlib's size-matched
route. All three hold on any site and for any universe of sections: `forget₂ CommRingCat RingCat`
and `forget CommRingCat` preserve limits of every size, and `forget RingCat` is corepresentable,
by the free ring on one generator
(`AlgebraicGeometry.Stack.ringForgetIsoCoyoneda`), hence preserves every limit it can. They are
stated as theorems and made local instances, following
`Stacks.hasSheafCompose_forget₂_commRingCat`, which records why a global instance would be
harmful.

## References

* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry

universe u v w

/-- On any site, and for any universe of sections, the sheaf condition for `RingCat`-valued
presheaves is preserved by `CategoryTheory.forget RingCat`. No size hypothesis relating the site
to the universe of sections is needed: that functor is corepresentable.

This is a `theorem` rather than an `instance`, for the reason recorded in
`Stacks.hasSheafCompose_forget₂_commRingCat`. -/
theorem hasSheafCompose_forget_ringCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget RingCat.{w}) :=
  let := Functor.IsCorepresentable.mk' Stack.ringForgetIsoCoyoneda.{w}
  inferInstance

/-- On any site, and for any universe of sections, the sheaf condition for `CommRingCat`-valued
presheaves is preserved by `CategoryTheory.forget CommRingCat`, which preserves limits of every
size.

This is a `theorem` rather than an `instance`, for the reason recorded in
`Stacks.hasSheafCompose_forget₂_commRingCat`. -/
theorem hasSheafCompose_forget_commRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget CommRingCat.{w}) :=
  hasSheafCompose_of_preservesLimitsOfSize J

namespace Stack.FlatFppf

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The fppf topology on the objects of an algebraic stack: the topology of **Stacks 06TP**
inherited from the chosen fppf covering families of the big site. -/
noncomputable abbrev fppfTopology : GrothendieckTopology 𝒳.val.val.obj :=
  associatedTopology B S hS 𝒳.val.val.p B.topology

/-- The structure sheaf of the fppf site of an algebraic stack: **Stacks 06TV** at the fppf
topology. -/
noncomputable abbrev ambientStructureSheaf : Sheaf (fppfTopology B S hS 𝒳) CommRingCat.{u} :=
  Stack.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl

/-- **Stacks 0788**, `flat_ringed`. The structure sheaf of the flat-fppf site of an algebraic
stack: the restriction, along the inclusion of the flat objects, of the structure sheaf of its
fppf site. The rings of sections are unchanged — they are those of the fppf structure sheaf at
the flat objects. -/
@[stacks 0788 "the structure sheaf of the flat-fppf site"]
noncomputable def structureSheaf : Sheaf (topology B S hS 𝒳) CommRingCat.{u} :=
  haveI := isContinuous_inclusion_topology B S hS 𝒳
  ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous CommRingCat.{u}
    (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)).obj (ambientStructureSheaf B S hS 𝒳)

/-- The fppf ringed topos of an algebraic stack: its fppf site with the structure sheaf of
**Stacks 06TV**. -/
noncomputable abbrev fppfRingedTopos : RingedTopos.{u, u + 1, u} where
  C := 𝒳.val.val.obj
  J := fppfTopology B S hS 𝒳
  O := ambientStructureSheaf B S hS 𝒳

/-- The flat-fppf ringed topos of an algebraic stack: its flat-fppf site with the restricted
structure sheaf. -/
noncomputable abbrev ringedTopos : RingedTopos.{u, u + 1, u} where
  C := FlatFppf B S hS 𝒳
  J := topology B S hS 𝒳
  O := structureSheaf B S hS 𝒳

/-- **The morphism of topoi `g` of Stacks 0788 (2)(a), at the universe of the sections of the
structure sheaf.** This is the same morphism of topoi as
`AlgebraicGeometry.Stack.FlatFppf.toposMorphismTopology` — inverse image restriction along the
inclusion of the flat objects, pushforward its cocontinuous right adjoint — read at `Type u`
rather than at `Type (u + 1)`, which is where the structure sheaves of **Stacks 06TV** live. At
that universe the pointwise right Kan extension along the inclusion has to be supplied, and that
is what the essential smallness of the flat-fppf site provides. -/
noncomputable def toposMorphismOnRings :
    MorphismOfTopoi (ringedTopos B S hS 𝒳).Topos (fppfRingedTopos B S hS 𝒳).Topos := by
  haveI := isContinuous_inclusion_topology B S hS 𝒳
  haveI := isCocontinuous_inclusion_topology B S hS 𝒳
  haveI : ∀ F : (FlatFppf B S hS 𝒳)ᵒᵖ ⥤ Type u,
      (objectProperty B S hS 𝒳).ι.op.HasPointwiseRightKanExtension F := fun F Y => by
    have := hasLimitsOfShape_of_essentiallySmall.{u}
      (StructuredArrow Y (objectProperty B S hS 𝒳).ι.op) (Type u)
    infer_instance
  exact
    { pushforward := (objectProperty B S hS 𝒳).ι.sheafPushforwardCocontinuous (Type u) _ _
      inverseImage := (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous (Type u) _ _
      adj := (objectProperty B S hS 𝒳).ι.sheafAdjunctionCocontinuous (Type u) _ _
      preservesFiniteLimits := ⟨fun I _ _ =>
        have : PreservesLimitsOfShape I
            ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous (Type u)
                (topology B S hS 𝒳) (fppfTopology B S hS 𝒳) ⋙
              sheafToPresheaf (topology B S hS 𝒳) (Type u)) :=
          preservesLimitsOfShape_of_natIso
            ((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuousCompSheafToPresheafIso
              (Type u) _ _).symm
        preservesLimitsOfShape_of_reflects_of_preserves _
          (sheafToPresheaf (topology B S hS 𝒳) (Type u))⟩ }

/-- **Stacks 0788**, `flat_ringed`: `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{flat,fppf}}`. The inverse image of the fppf
structure sheaf along the morphism of topoi of **Stacks 0788** (2)(a) is the structure sheaf of
the flat-fppf site.

The inverse image of `g` on sheaves of sets *is* restriction along the inclusion of the flat
objects, so this is the comparison of the transported commutative ring operations with those of
the restricted sheaf, and that comparison is the identity on sections
(`AlgebraicGeometry.Stack.FlatFppf.structureSheafIso_apply`). -/
@[stacks 0788 "the structure sheaf is the restriction of the big one"]
noncomputable def structureSheafIso :
    (inverseImageCommRingFunctor (toposMorphismOnRings B S hS 𝒳)).obj
        (fppfRingedTopos B S hS 𝒳).O ≅ (ringedTopos B S hS 𝒳).O :=
  haveI := isContinuous_inclusion_topology B S hS 𝒳
  restrictionCommRingIso (topology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (objectProperty B S hS 𝒳).ι (ambientStructureSheaf B S hS 𝒳)

/-- **Stacks 0788**, `flat_ringed`. The identification `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{flat,fppf}}` is the
identity on sections over a flat object. This pins it: it is not an arbitrary automorphism of the
restricted structure sheaf. -/
@[stacks 0788 "that identification, on sections"]
theorem structureSheafIso_apply (U : (FlatFppf B S hS 𝒳)ᵒᵖ)
    (a : ((inverseImageCommRingFunctor (toposMorphismOnRings B S hS 𝒳)).obj
      (fppfRingedTopos B S hS 𝒳).O).obj.obj U) :
    (structureSheafIso B S hS 𝒳).hom.hom.app U a = a := rfl

/-- **Stacks 0788**, `flat_ringed`. The morphism of ringed topoi
`(g, g♯) : (Sh(𝒳_{flat,fppf}), 𝒪_{𝒳_{flat,fppf}}) ⟶ (Sh(𝒳_{fppf}), 𝒪_𝒳)` of **Stacks 01D3**
part (2), whose structure map is the adjoint of the identification
`AlgebraicGeometry.Stack.FlatFppf.structureSheafIso`. -/
@[stacks 0788 "the induced morphism of ringed topoi"]
noncomputable def ringedToposMorphism :
    RingedToposHom (ringedTopos B S hS 𝒳) (fppfRingedTopos B S hS 𝒳) where
  toToposHom := toposMorphismOnRings B S hS 𝒳
  fSharp := (commRingImageAdjunction (toposMorphismOnRings B S hS 𝒳)).homEquiv
    (fppfRingedTopos B S hS 𝒳).O (ringedTopos B S hS 𝒳).O (structureSheafIso B S hS 𝒳).hom

/-- The inverse-image form of the structure map of the flat-fppf morphism of ringed topoi is the
identification `g⁻¹𝒪_𝒳 ≅ 𝒪_{𝒳_{flat,fppf}}` itself, the direct-image form having been defined as
its adjoint. -/
theorem ringedToposMorphism_fSharpInverseImage :
    (ringedToposMorphism B S hS 𝒳).fSharpInverseImage = (structureSheafIso B S hS 𝒳).hom :=
  Equiv.symm_apply_apply _ _

/-- **Stacks 0788**, `flat_ringed`. The flat-fppf morphism of ringed topoi is flat, in the sense
of **Stacks 04JB**: its inverse-image structure map is an isomorphism, by
`AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism_fSharpInverseImage`, and an isomorphism of
sheaves of commutative rings is a flat morphism. -/
@[stacks 0788 "that morphism of ringed topoi is flat"]
theorem ringedToposMorphism_isFlat : (ringedToposMorphism B S hS 𝒳).IsFlat := by
  let : IsIso (ringedToposMorphism B S hS 𝒳).fSharpInverseImage := by
    rw [ringedToposMorphism_fSharpInverseImage]
    exact Iso.isIso_hom _
  let : HasWeakSheafify (topology B S hS 𝒳) AddCommGrpCat.{u + 1} := by
    have : HasSheafify (topology B S hS 𝒳) AddCommGrpCat.{u + 1} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
    infer_instance
  let : (topology B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  exact AlgebraicGeometry.SheafOfModules.isFlatMap_of_isIso
    ((AlgebraicGeometry.SheafOfModules.sheafULift.{u, u + 1, u} (topology B S hS 𝒳)).map
      (ringedToposMorphism B S hS 𝒳).fSharpInverseImage)

/-- **Stacks 0788**, `flat_ringed`. Restriction of sheaves of modules along the inclusion of the
flat objects, over the fppf structure sheaf and its restriction. The scalar comparison is the
identity, because the structure sheaf of the flat-fppf site is the restriction of the fppf one
with its original rings of sections.

This is the functor that the third assertion of **Stacks 0788** (2)(f) identifies pullback of
modules along `AlgebraicGeometry.Stack.FlatFppf.ringedToposMorphism` with; the identification is
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`, in
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules`. -/
@[stacks 0788 "restriction of modules along it"]
noncomputable def moduleRestriction :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
          (ambientStructureSheaf B S hS 𝒳)) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
          (structureSheaf B S hS 𝒳)) :=
  haveI := isContinuous_inclusion_topology B S hS 𝒳
  SheafOfModules.pushforward (F := (objectProperty B S hS 𝒳).ι) (𝟙 _)

end Stack.FlatFppf

end AlgebraicGeometry

end
