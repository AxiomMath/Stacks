module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiRealFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffinesZariskiExists
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctorUnconditional

/-!
# The sections description of `𝓕ᵃ` on the small Zariski site

[Stacks, Tag 03DU] (4) defines the associated module `𝓕ᵃ` of a quasi-coherent `𝒪_S`-module **by
its sections**: over an object `f : T → S` of the small site its sections are `Γ(T, f^*𝓕)`.  On
the small Zariski site that sheaf is
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections`.  What the development calls
`AlgebraicGeometry.SmallZariski.associatedModule` is a different construction: the pullback of
sheaves of modules along the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)` of
[Stacks, Remark 03FH].  **This file identifies the two**, which is the content of
[Stacks, Remark 03FH] (1) at `τ = Zariski` and the one thing the Zariski column of this cluster
was missing: the big sites have the identification in
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` and the small étale site in
`AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`, and before this file the tree held
two unconnected Zariski readings of `𝓕ᵃ`, with [Stacks, Tag 0GN7] registered on one and
[Stacks, Tag 03DU] (4) on the other.

## The route, and why it is not the étale one

At `τ = étale` the identification is [Stacks, Tag 070S] (2): the pullback is the étale
sheafification of the sections presheaf, and the sheafification is then stripped because the
presheaf is already a sheaf.  At `τ = Zariski` no sheafification argument is needed, because the
morphism of ringed sites is an *equivalence* of ringed sites: by
`AlgebraicGeometry.SmallZariski.isEquivalence_restrictModule` the restriction
`AlgebraicGeometry.SmallZariski.restrictModule` is an equivalence, so it is fully faithful, and
an isomorphism of its values is an isomorphism of its arguments.  Hence the identification
follows from

* `AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso`, `𝓕 ≅ f_*f^*𝓕`, which the tree
  already had, and
* `AlgebraicGeometry.SmallZariski.sectionsUnitIso`, `𝓕 ≅ f_*(𝓕ᵃ)` for the **sections-defined**
  `𝓕ᵃ`, which is what this file builds.

That second isomorphism is where the work is.  Its abelian-group half is already in the tree —
`AlgebraicGeometry.smallZariskiSectionsUnit` and
`AlgebraicGeometry.isIso_smallZariskiSectionsUnit`, over the explicitly-constructed comparison
functor `AlgebraicGeometry.opensToSmallZariski` — but the pullback is taken along
`AlgebraicGeometry.SmallZariski.opensToSmallZariski`, the *inverse of the equivalence of sites*
of [Stacks, Tag 020X], which picks its object over an open `V` by `Classical.choice`; and an
isomorphism of abelian sheaves does not upgrade to one of sheaves of modules.  What is needed is
the **semilinear** statement over `AlgebraicGeometry.SmallZariski.structureMap`, and therefore a
computation of the component of that map at an open of `S`.  Unlike the étale `structureMap`,
whose component is literally `(Scheme.Opens.topIso U).inv`, the Zariski one is the inverse of a
`RingCat` sheaf isomorphism assembled from the counit of
`AlgebraicGeometry.smallZariskiSheafEquivWith` and
`AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`, and no lemma computed it.
`AlgebraicGeometry.SmallZariski.structureMap_hom_app` is that computation: the component at `V`
is `g.appLE V ⊤`, where `g` is the structure morphism of the chosen object over `V`.  With it,
semilinearity of pulling sections back is `AlgebraicGeometry.pullbackSectionHom_smul` exactly as
at `τ = étale`.

Two further Zariski-only points, both caused by the chosen object being opaque:

* the component of the unit is `AlgebraicGeometry.pullbackSectionHom` along an arbitrary open
  immersion with open image `V`, not along `V.ι`, so
  `AlgebraicGeometry.isIso_pullbackSectionHom_ι` does not apply directly;
  `AlgebraicGeometry.isIso_pullbackSectionHom_of_opensRange_eq` transports it along the
  isomorphism of `Over S` between the two;
* all that is ever used about the chosen object is that its open image *equals* `V`, which is
  `AlgebraicGeometry.smallZariskiToOpens_opensToSmallZariski_obj`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.sectionsUnit` and
  `AlgebraicGeometry.SmallZariski.sectionsUnitIso`: pulling a section of `𝓕` over an open `V` of
  `S` back to the object of `S_Zar` chosen over `V`, as a semilinear isomorphism
  `𝓕 ≅ f_*(𝓕ᵃ)` onto the restriction of the sections-defined `𝓕ᵃ`.
* `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`: **[Stacks, Remark 03FH] (1) at
  `τ = Zariski`** — the pullback-defined `𝓕ᵃ` and the sections-defined `𝓕ᵃ` agree.
* `AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`: the same as an
  isomorphism of *functors* on `QCoh(𝒪_S)`.
* `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedSheafFunctor`: **[Stacks, Tag 0GN7] at
  `τ = Zariski` for the sections-defined functor.**

## Main results

* `AlgebraicGeometry.SmallZariski.structureMap_hom_app`: the component of the structure-sheaf
  comparison of the small Zariski site at an open `V` of `S` is the action on sections of the
  structure morphism of the object chosen over `V`.
* `AlgebraicGeometry.isIso_pullbackSectionHom_of_opensRange_eq`: pulling a section of a module
  back along an open immersion is bijective on the open image of that immersion.
* `AlgebraicGeometry.SmallZariski.associatedPresheaf_map_opensToSmallZariski`: the restriction
  map of the presheaf of [Stacks, Tag 03DS] along the image of an arrow of opens of `S` in the
  small Zariski site is the pullback map on sections of that arrow's image.
* `AlgebraicGeometry.SmallZariski.sectionsUnitApp_naturality`.
* `AlgebraicGeometry.SmallZariski.isIso_sectionsUnit`.

## Implementation notes

`AlgebraicGeometry.SmallZariski.commStructureIso_hom_app` is stated at the `CommRingCat`-valued
lifting `AlgebraicGeometry.smallZariskiCommStructureIso` rather than at
`AlgebraicGeometry.SmallZariski.structureMap` itself, because `Scheme.Hom.appLE` is a
`CommRingCat` morphism; `AlgebraicGeometry.whiskerRight_smallZariskiCommStructureIso_hom`, which
is `rfl`, carries it to the `RingCat` statement.  Its proof may not `rw` the counit component
into `AlgebraicGeometry.openImmersion_ΓIsoTop_inv` directly: the codomain of the counit component
is `(e.op.inverse ⋙ e.op.functor).obj (op V)` where the `appLE` is typed at
`op ((smallZariskiOpenImmersion ...).opensRange)`, and the two are equal only up to unfolding
that `rw`'s motive check does not perform.  The counit component is therefore replaced by the
unique arrow of the poset of opens first, which is `Subsingleton.elim`.

`AlgebraicGeometry.SmallZariski.sectionsUnit` is stated as a morphism of *presheaves* of modules,
as its étale counterpart `AlgebraicGeometry.SmallEtale.sectionsUnit` is, and
`AlgebraicGeometry.SmallZariski.sectionsUnitHom` is the sheaf-level morphism with that `val`;
the two objects it connects have the same underlying presheaf of modules by `rfl`, restriction of
a sheaf of modules being restriction of its sections.

Naturality of `AlgebraicGeometry.SmallZariski.sectionsUnit` in the open is the one place where
the opacity of the chosen object is felt, and it is why that naturality is a statement of its
own, `AlgebraicGeometry.SmallZariski.sectionsUnitApp_naturality`, proved as a chain of named
steps rather than left to a single definitional comparison.  Asking the elaborator to identify
the restriction map of the pushed-forward sections-defined `𝓕ᵃ` with the pullback map on
sections *at the chosen object* makes it unfold the `Classical.choice` of
`AlgebraicGeometry.SmallZariski.opensToSmallZariski` on both sides.  Two reformulations remove
that work, and both are the same discipline: never state an identification at the chosen object
when it can be stated at a parameter.

* `AlgebraicGeometry.SmallZariski.opensPushforward_map_apply` pins the comparison functor and
  the two presheaves of rings in its *statement*, so that applying it is a substitution.
  Mathlib's `CategoryTheory.PresheafOfModules.pushforward_obj_map_apply` says the same thing
  with the comparison functor implicit, and recovering that functor from the type of the
  structure comparison is what costs: it is reached only through
  `CategoryTheory.Functor.sheafPushforwardContinuous`, and solving for it unfolds the chosen
  object.
* `AlgebraicGeometry.SmallZariski.associatedPresheaf_map_opensToSmallZariski` is an equation of
  *morphisms* of abelian groups, with no element applied and no module structure to reconcile.
  The element is applied afterwards by `congrArg`, by which point the two sides of the equation
  are already the same term.

Nothing in that proof is a search; what it costs is definitional unfolding alone.

The naturality of the unit in the module is proved against
`AlgebraicGeometry.SmallZariski.associatedSheafFunctor`, whose action on morphisms is the pullback
of the morphism read on global sections by `rfl`; the component statement is then
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`.

## References

* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Pulling sections back along an open immersion -/

/-- The whole of the source of an open immersion lies over any open containing its image. -/
public theorem top_le_preimage_of_opensRange_le {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] {U : Y.Opens} (h : g.opensRange ≤ U) : (⊤ : X.Opens) ≤ g ⁻¹ᵁ U :=
  fun x _ => h ⟨x, rfl⟩

/-- **Pulling a section of a module back along an open immersion is bijective on its open
image.**  For an open immersion `g : T ⟶ S` with open image `V`, the map
`Γ(F, V) ⟶ Γ(g^*F, ⊤)` of `AlgebraicGeometry.pullbackSectionHom` is an isomorphism, for any
`𝒪_S`-module `F`.

This is `AlgebraicGeometry.isIso_pullbackSectionHom_ι`, which is the case `g = V.ι`, transported
along the isomorphism of `Over S` from `g` to `V.ι` supplied by
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`: the restriction map of the presheaf of
[Stacks, Tag 03DS] along that isomorphism is an isomorphism, and by
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` it carries the one pullback of
sections to the other. -/
public theorem isIso_pullbackSectionHom_of_opensRange_eq {S T : Scheme.{u}} (F : S.Modules)
    (g : T ⟶ S) [IsOpenImmersion g] (V : S.Opens) (hV : g.opensRange = V) :
    IsIso (pullbackSectionHom g F V ⊤ (top_le_preimage_of_opensRange_le g hV.le)) := by
  have hrange : Set.range g.base = Set.range V.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, hV, Scheme.Opens.opensRange_ι]
  let e : Over.mk g ≅ Over.mk V.ι :=
    Over.isoMk (IsOpenImmersion.isoOfRangeEq g V.ι hrange)
      (IsOpenImmersion.isoOfRangeEq_hom_fac g V.ι hrange)
  have hcomp :
      pullbackSectionHom (Over.mk V.ι).hom F V ⊤ (@Scheme.Opens.top_le_ι_preimage S V V le_rfl) ≫
          pullbackSectionsMap F e.hom =
        pullbackSectionHom g F V ⊤ (top_le_preimage_of_opensRange_le g hV.le) := by
    ext c
    exact pullbackSectionsMap_pullbackSectionHom F e.hom V
      (@Scheme.Opens.top_le_ι_preimage S V V le_rfl)
      (top_le_preimage_of_opensRange_le g hV.le) c
  have h1 : IsIso (pullbackSectionHom (Over.mk V.ι).hom F V ⊤
      (@Scheme.Opens.top_le_ι_preimage S V V le_rfl)) :=
    isIso_pullbackSectionHom_ι F V
  have h2 : IsIso (pullbackSectionsMap F e.hom) := by
    have : IsIso (pullbackSectionsMap F e.hom.op.unop) := by
      rw [← (quasiCoherentPresheafConstruction S F).map_objIso e.hom.op]
      infer_instance
    exact this
  rw [← hcomp]
  infer_instance

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The object of the site chosen over an open -/

/-- The structure morphism of the object of the small Zariski site of `S` chosen over an open `V`
of `S` by `AlgebraicGeometry.SmallZariski.opensToSmallZariski`.  It is an open immersion with
open image `V`, and that is all that is known about it. -/
public noncomputable abbrev chosenObjHom (V : S.Opens) :
    (SmallZariski.toScheme B S hS).obj
      ((SmallZariski.opensToSmallZariski B S hS).obj V) ⟶ S :=
  smallZariskiOpenImmersion B S hS ((SmallZariski.opensToSmallZariski B S hS).obj V)

/-- **The open image of the object chosen over `V` is `V`.**
`AlgebraicGeometry.smallZariskiToOpens_opensToSmallZariski_obj`, read at the structure morphism
of that object. -/
public theorem opensRange_chosenObjHom (V : S.Opens) : (chosenObjHom B S hS V).opensRange = V :=
  smallZariskiToOpens_opensToSmallZariski_obj B S hS V

/-- The whole of the object chosen over `V` lies over any open of `S` containing `V`. -/
public theorem top_le_chosenObjHom_preimage {V U : S.Opens} (h : V ≤ U) :
    (⊤ : ((SmallZariski.toScheme B S hS).obj
      ((SmallZariski.opensToSmallZariski B S hS).obj V)).Opens) ≤
      (chosenObjHom B S hS V) ⁻¹ᵁ U :=
  top_le_preimage_of_opensRange_le _ ((opensRange_chosenObjHom B S hS V).le.trans h)

/-! ### The component of the structure-sheaf comparison -/

/-- **The structure-sheaf comparison of the small Zariski site, on sections over an open `V` of
`S`**, in `CommRingCat`: it is the action on sections of the structure morphism of the object
chosen over `V`, from `V` to the whole of that object.

`AlgebraicGeometry.smallZariskiCommStructureIso` is the counit of the equivalence of sites of
[Stacks, Tag 020X] followed by `AlgebraicGeometry.IsOpenImmersion.ΓIsoTop`.  The counit component
is an arrow of the poset of opens of `S`, hence the unique one from `V` to the open image of the
chosen object, which is `V` again by
`AlgebraicGeometry.SmallZariski.opensRange_chosenObjHom`; and `ΓIsoTop` is an `appLE` by
`AlgebraicGeometry.openImmersion_ΓIsoTop_inv`.  Composing the two restriction maps is
`AlgebraicGeometry.Scheme.Hom.map_appLE`. -/
public theorem commStructureIso_hom_app (V : S.Opens) :
    (smallZariskiCommStructureIso B S hS).hom.app (op V) =
      (chosenObjHom B S hS V).appLE V ⊤ (top_le_chosenObjHom_preimage B S hS le_rfl) := by
  have hle : (chosenObjHom B S hS V).opensRange ≤ V := (opensRange_chosenObjHom B S hS V).le
  have key : (smallZariskiCommStructureIso B S hS).hom.app (op V) =
      S.presheaf.map (homOfLE hle).op ≫
        (IsOpenImmersion.ΓIsoTop (chosenObjHom B S hS V)).inv :=
    congrArg (fun (k : Γ(S, V) ⟶ Γ(S, (chosenObjHom B S hS V).opensRange)) =>
        k ≫ (IsOpenImmersion.ΓIsoTop (chosenObjHom B S hS V)).inv)
      (congrArg S.presheaf.map (Subsingleton.elim _ _))
  rw [key, openImmersion_ΓIsoTop_inv, Scheme.Hom.map_appLE]

/-- **The structure-sheaf comparison of the small Zariski site, on sections over an open `V` of
`S`.**  `AlgebraicGeometry.SmallZariski.commStructureIso_hom_app` in `RingCat`, which is where
`AlgebraicGeometry.SmallZariski.structureMap` lives; the two are the same map by
`AlgebraicGeometry.whiskerRight_smallZariskiCommStructureIso_hom`.

This is the lemma that makes pulling sections back semilinear over the comparison, and it is the
small Zariski counterpart of `AlgebraicGeometry.SmallEtale.structureMap_hom_app`, where the
component is `(Scheme.Opens.topIso U).inv` on the nose. -/
public theorem structureMap_hom_app (V : (S.Opens)ᵒᵖ) :
    (structureMap B S hS).hom.app V =
      (forget₂ CommRingCat RingCat.{u}).map
        ((chosenObjHom B S hS V.unop).appLE V.unop ⊤
          (top_le_chosenObjHom_preimage B S hS le_rfl)) := by
  rw [← commStructureIso_hom_app]
  exact (NatTrans.congr_app
    (whiskerRight_smallZariskiCommStructureIso_hom B S hS) V).symm

/-! ### Pulling sections back, semilinearly -/

section

variable (F : S.Modules) [F.IsQuasicoherent]

/-- Pulling a section of `𝓕` over an open `V` of `S` back to the object of the small Zariski site
chosen over `V`, as a map of modules of sections.  It is semilinear over the structure-sheaf
comparison by `AlgebraicGeometry.pullbackSectionHom_smul` together with
`AlgebraicGeometry.SmallZariski.structureMap_hom_app`. -/
public noncomputable def sectionsUnitApp (V : (S.Opens)ᵒᵖ) :
    ((SheafOfModules.forget S.ringCatSheaf).obj F).obj V ⟶
      ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (associatedModuleOfSections B S hS F).val).obj V :=
  ModuleCat.homEquiv.symm {
    toFun := fun a =>
      pullbackSectionHom (chosenObjHom B S hS V.unop) F V.unop ⊤
        (top_le_chosenObjHom_preimage B S hS le_rfl) a
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      refine (pullbackSectionHom_smul (chosenObjHom B S hS V.unop) F V.unop ⊤
        (top_le_chosenObjHom_preimage B S hS le_rfl) r a).trans ?_
      have h2 : ConcreteCategory.hom ((chosenObjHom B S hS V.unop).appLE V.unop ⊤
          (top_le_chosenObjHom_preimage B S hS le_rfl)) r
          = ConcreteCategory.hom ((structureMap B S hS).hom.app V) r := by
        rw [structureMap_hom_app]
        rfl
      exact congrArg (fun s => s • pullbackSectionHom (chosenObjHom B S hS V.unop) F V.unop ⊤
        (top_le_chosenObjHom_preimage B S hS le_rfl) a) h2 }

/-- The value of `AlgebraicGeometry.SmallZariski.sectionsUnitApp` on a section is its pullback to
the object chosen over the open. -/
@[simp]
public theorem sectionsUnitApp_apply (V : (S.Opens)ᵒᵖ)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj V) :
    sectionsUnitApp B S hS F V a =
      pullbackSectionHom (chosenObjHom B S hS V.unop) F V.unop ⊤
        (top_le_chosenObjHom_preimage B S hS le_rfl) a :=
  rfl

/-- **The restriction maps of a pushforward of presheaves of modules along a comparison of the
opens of `S` with the small Zariski site**, on a section: the restriction map of the pushforward
along `ψ` is the restriction map of the module along the image of the arrow under the comparison
functor.

This is `CategoryTheory.PresheafOfModules.pushforward_obj_map_apply` with the comparison functor
`uu` and the two presheaves of rings written into the statement instead of left implicit.  That
is the whole point of the restatement: in Mathlib's form they are recovered by unifying the type
of `ψ` with `_ ⟶ uu.op ⋙ _`, and at `ψ = (structureMap B S hS).hom` the comparison functor is
visible only after `CategoryTheory.Functor.sheafPushforwardContinuous` is unfolded, which makes
the elaborator unfold the `Classical.choice` of
`AlgebraicGeometry.SmallZariski.opensToSmallZariski` as well.  Here nothing is solved for: the
statement is instantiated. -/
public theorem opensPushforward_map_apply
    (uu : S.Opens ⥤ SmallZariski B S hS)
    (ψ : S.ringCatSheaf.obj ⟶ uu.op ⋙ (structureSheaf B S hS).obj)
    (M : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    {U V : (S.Opens)ᵒᵖ} (h : U ⟶ V)
    (m : ((PresheafOfModules.pushforward.{u} ψ).obj M).obj U) :
    (((PresheafOfModules.pushforward.{u} ψ).obj M).map h) m =
      M.map (uu.map h.unop).op m :=
  rfl

/-- **The restriction maps of the presheaf of [Stacks, Tag 03DS] over the small Zariski site, at
the image of an arrow of opens of `S`.**  It is the pullback map on sections of the morphism of
schemes over `S` that the arrow induces between the chosen objects.

`Stacks.Sites.associatedPresheaf_map_eq` at the arrow `(opensToSmallZariski ...).map h.unop`.
The statement is an equation of morphisms of abelian groups and is deliberately not applied to a
section: the sections of the two sides over the chosen object are the same type only after the
`Classical.choice` of `AlgebraicGeometry.SmallZariski.opensToSmallZariski` is unfolded, whereas
with no element present the two sides are the same term.  A consumer applies the equation to a
section afterwards, with `congrArg`. -/
public theorem associatedPresheaf_map_opensToSmallZariski {U V : (S.Opens)ᵒᵖ} (h : U ⟶ V) :
    (Stacks.Sites.associatedPresheaf S F (SmallZariski.inclusion B S hS ⋙
        Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)).map
        ((SmallZariski.opensToSmallZariski B S hS).map h.unop).op =
      pullbackSectionsMap F ((SmallZariski.inclusion B S hS ⋙
        Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).map
          ((SmallZariski.opensToSmallZariski B S hS).map h.unop)) :=
  Stacks.Sites.associatedPresheaf_map_eq S F
    (SmallZariski.inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
    ((SmallZariski.opensToSmallZariski B S hS).map h.unop).op

/-- **Pulling sections back to the chosen objects is natural in the open.**  The naturality
square of `AlgebraicGeometry.SmallZariski.sectionsUnit`, which is where the opacity of the
chosen object has to be worked around.

On a section the two sides are read off in named steps.  Restricting the section before pulling
it back changes nothing, which is `AlgebraicGeometry.pullbackSectionHom_map`; the restriction map
of the pushforward of the sections-defined `𝓕ᵃ` is the restriction map of `𝓕ᵃ` along the image
of the arrow, which is `AlgebraicGeometry.SmallZariski.opensPushforward_map_apply`; that
restriction map is the one of the underlying abelian presheaf, which is
`CategoryTheory.PresheafOfModules.presheaf_map_apply_coe`, and the underlying abelian presheaf is
the presheaf of [Stacks, Tag 03DS], whose restriction maps are pullback maps on sections by
`AlgebraicGeometry.SmallZariski.associatedPresheaf_map_opensToSmallZariski`; and finally the
presheaf of [Stacks, Tag 03DS] carries pullbacks of sections to pullbacks of sections, which is
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`. -/
public theorem sectionsUnitApp_naturality {U V : (S.Opens)ᵒᵖ} (h : U ⟶ V) :
    ((SheafOfModules.forget S.ringCatSheaf).obj F).map h ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (S.ringCatSheaf.obj.map h))).map
          (sectionsUnitApp B S hS F V) =
      sectionsUnitApp B S hS F U ≫
        ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
          (associatedModuleOfSections B S hS F).val).map h := by
  ext a
  have hUV : V.unop ≤ U.unop := leOfHom h.unop
  refine Eq.trans (pullbackSectionHom_map (chosenObjHom B S hS V.unop) F U.unop V.unop hUV ⊤
    (top_le_chosenObjHom_preimage B S hS le_rfl)
    (top_le_chosenObjHom_preimage B S hS hUV) a) ?_
  refine Eq.trans ?_ (ModuleCat.comp_apply (sectionsUnitApp B S hS F U)
    (((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
      (associatedModuleOfSections B S hS F).val).map h) a).symm
  refine Eq.trans ?_ (opensPushforward_map_apply B S hS (opensToSmallZariski B S hS)
    (structureMap B S hS).hom (associatedModuleOfSections B S hS F).val h
    (sectionsUnitApp B S hS F U a)).symm
  refine Eq.trans ?_ (congrArg
    (fun z => ((associatedModuleOfSections B S hS F).val.map
      ((opensToSmallZariski B S hS).map h.unop).op) z)
    (sectionsUnitApp_apply B S hS F U a)).symm
  refine Eq.trans ?_ (PresheafOfModules.presheaf_map_apply_coe
    (associatedModuleOfSections B S hS F).val
    ((SmallZariski.opensToSmallZariski B S hS).map h.unop).op
    (pullbackSectionHom (chosenObjHom B S hS U.unop) F U.unop ⊤
      (top_le_chosenObjHom_preimage B S hS (V := U.unop) (U := U.unop) le_rfl) a))
  refine Eq.trans ?_ (congrArg
    (fun k => k (pullbackSectionHom (chosenObjHom B S hS U.unop) F U.unop ⊤
      (top_le_chosenObjHom_preimage B S hS (V := U.unop) (U := U.unop) le_rfl) a))
    (associatedPresheaf_map_opensToSmallZariski B S hS F h)).symm
  exact (pullbackSectionsMap_pullbackSectionHom F ((SmallZariski.inclusion B S hS ⋙
      Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).map
        ((SmallZariski.opensToSmallZariski B S hS).map h.unop))
      U.unop (top_le_chosenObjHom_preimage B S hS (V := U.unop) (U := U.unop) le_rfl)
      (top_le_chosenObjHom_preimage B S hS (V := V.unop) (U := U.unop) hUV) a).symm

/-- **Pulling sections back, as a morphism out of `𝓕`.**  A section of `𝓕` over an open `V` of
`S` pulls back to a section of `g^*𝓕` over all of the object of the small Zariski site chosen
over `V`, naturally in `V`: a morphism from `𝓕` to the restriction, along the morphism of ringed
sites of [Stacks, Remark 03FH], of the sections-defined `𝓕ᵃ` of [Stacks, Tag 03DU] (4).

Naturality is `AlgebraicGeometry.SmallZariski.sectionsUnitApp_naturality`. -/
public noncomputable def sectionsUnit :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (associatedModuleOfSections B S hS F).val where
  app V := sectionsUnitApp B S hS F V
  naturality h := sectionsUnitApp_naturality B S hS F h

/-- **Pulling sections back to the objects of the small Zariski site is an isomorphism.**  Each
component is the map of `AlgebraicGeometry.isIso_pullbackSectionHom_of_opensRange_eq` at the
structure morphism of the chosen object, whose open image is the open it was chosen over. -/
public theorem isIso_sectionsUnit : IsIso (sectionsUnit B S hS F) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf S.ringCatSheaf.obj),
    NatTrans.isIso_iff_isIso_app]
  exact fun V => isIso_pullbackSectionHom_of_opensRange_eq F (chosenObjHom B S hS V.unop) V.unop
    (opensRange_chosenObjHom B S hS V.unop)

/-- `AlgebraicGeometry.SmallZariski.sectionsUnit` as a morphism of sheaves of modules
`𝓕 ⟶ f_*(𝓕ᵃ)`, onto the restriction of the sections-defined `𝓕ᵃ` along the morphism of ringed
sites of [Stacks, Remark 03FH].  The underlying presheaf of modules of the target is the one
`sectionsUnit` lands in by `rfl`. -/
public noncomputable def sectionsUnitHom :
    F ⟶ (restrictModule B S hS).obj (associatedModuleOfSections B S hS F) :=
  ⟨sectionsUnit B S hS F⟩

/-- `AlgebraicGeometry.SmallZariski.sectionsUnitHom` is an isomorphism:
`AlgebraicGeometry.SmallZariski.isIso_sectionsUnit` carried across the fully faithful forgetful
functor to presheaves of modules. -/
public theorem isIso_sectionsUnitHom : IsIso (sectionsUnitHom B S hS F) := by
  have : IsIso ((SheafOfModules.forget S.ringCatSheaf).map (sectionsUnitHom B S hS F)) :=
    isIso_sectionsUnit B S hS F
  exact (SheafOfModules.fullyFaithfulForget S.ringCatSheaf).isIso_of_isIso_map
    (sectionsUnitHom B S hS F)

/-- **`𝓕 ≅ f_*(𝓕ᵃ)` for the sections-defined `𝓕ᵃ` of [Stacks, Tag 03DU] (4) at `τ = Zariski`**:
restricting it along the morphism of ringed sites of [Stacks, Remark 03FH] returns `𝓕`, the
isomorphism being "pull the section back to the object chosen over the open". -/
public noncomputable def sectionsUnitIso :
    F ≅ (restrictModule B S hS).obj (associatedModuleOfSections B S hS F) :=
  @asIso _ _ _ _ _ (isIso_sectionsUnitHom B S hS F)

/-- **The two constructions of `𝓕ᵃ` on the small Zariski site agree**: the pullback of `𝓕` along
the morphism of ringed sites `(S_Zar, 𝒪) → (S_Zar, 𝒪_S)`,
`AlgebraicGeometry.SmallZariski.associatedModule`, is the sheaf
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections` whose sections over an object
`f : T → S` of `S_Zar` are `Γ(T, f^*𝓕)`.

This is the content of [Stacks, Remark 03FH] (1) on the small Zariski site: [Stacks, Tag 03DU]
(4) defines `𝓕ᵃ` by its sections, and the remark observes that it is the pullback along
`id_{small, Zar, Zar}`.  At `τ = Zariski` that morphism of ringed sites is an equivalence, so
`AlgebraicGeometry.SmallZariski.restrictModule` is fully faithful and the identification follows
from the two isomorphisms `𝓕 ≅ f_*f^*𝓕`
(`AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso`) and `𝓕 ≅ f_*(𝓕ᵃ)`
(`AlgebraicGeometry.SmallZariski.sectionsUnitIso`); no sheafification argument is needed, where
`τ = étale` needs [Stacks, Tag 070S] (2).

**This carries [Stacks, Remark 03FH] (1) at `τ = Zariski` for the second of the two morphisms
that clause offers**, `id_{small, Zar, Zar} : (S_Zar, 𝒪) → (S_Zar, 𝒪_S)`.  Its `τ = étale`
counterpart is `AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`, and the first
morphism of the clause, `id_{τ, Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪)`, is carried at all five `τ`
by `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`.

The quasi-coherence hypothesis is not an added hypothesis of 03FH: the construction `𝓕 ↦ 𝓕ᵃ`
whose two descriptions the remark identifies is [Stacks, Tag 03DU] (4), which is stated for a
quasi-coherent `𝒪_S`-module. -/
@[stacks 03FH "part (1), for the morphism id_{small, Zariski, Zar} : (S_Zar, 𝒪) → (S_Zar, 𝒪_S)"]
public noncomputable def associatedModuleIsoOfSections :
    (associatedModule B S hS).obj F ≅ associatedModuleOfSections B S hS F :=
  (Functor.FullyFaithful.ofFullyFaithful (restrictModule B S hS)).preimageIso
    (((restrictAssociatedModuleIso B S hS).app F).symm ≪≫ sectionsUnitIso B S hS F)

end

/-! ### The identification is natural, and 0GN7 for the sections-defined functor -/

/-- **Pulling sections back is natural in the module.**  For a morphism `φ : 𝓕 ⟶ 𝓖` of
quasi-coherent `𝒪_S`-modules, `AlgebraicGeometry.SmallZariski.sectionsUnitHom` commutes with `φ`
and with the morphism `𝓕ᵃ ⟶ 𝓖ᵃ` of
`AlgebraicGeometry.SmallZariski.associatedSheafFunctor`, which on sections over an object of the
site is the pullback of `φ` read on global sections.  On components this is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`. -/
public theorem sectionsUnitHom_naturality
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map φ ≫
        @sectionsUnitHom B S hS G.obj G.property =
      @sectionsUnitHom B S hS F.obj F.property ≫
        (restrictModuleOfSheaf B S hS).map ((associatedSheafFunctor B S hS).map φ) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.Hom.ext ?_)
  ext V a
  exact (Scheme.Modules.pullbackSection_naturality (chosenObjHom B S hS V.unop) φ.hom V.unop ⊤
    (top_le_chosenObjHom_preimage B S hS le_rfl) a).symm

/-- **`𝓕 ≅ f_*(𝓕ᵃ)` naturally in `𝓕`**, for the sections-defined functor `𝓕 ↦ 𝓕ᵃ` of
[Stacks, Tag 03DU] (4) at `τ = Zariski`: the inclusion of the quasi-coherent `𝒪_S`-modules is
isomorphic to `𝓕 ↦ f_*(𝓕ᵃ)`. -/
public noncomputable def restrictAssociatedSheafFunctorIso :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ≅
      associatedSheafFunctor B S hS ⋙ restrictModuleOfSheaf B S hS :=
  NatIso.ofComponents (fun F => @sectionsUnitIso B S hS F.obj F.property)
    (fun φ => sectionsUnitHom_naturality B S hS φ)

/-- **`f_*f^*𝓕 ≅ 𝓕` naturally in `𝓕`** on the quasi-coherent modules:
`AlgebraicGeometry.SmallZariski.restrictAssociatedModuleIso` whiskered with the inclusion of the
quasi-coherent `𝒪_S`-modules. -/
public noncomputable def associatedModuleQcohCompRestrictIso :
    associatedModuleQcoh B S hS ⋙ restrictModuleOfSheaf B S hS ≅
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
  Functor.isoWhiskerLeft ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι)
      (restrictAssociatedModuleIso B S hS).symm ≪≫
    Functor.rightUnitor ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι)

/-- **The two constructions of `𝓕 ↦ 𝓕ᵃ` on the small Zariski site agree as functors on
`QCoh(𝒪_S)`**: `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections` is natural in `𝓕`.

Both composites with `AlgebraicGeometry.SmallZariski.restrictModuleOfSheaf` are the inclusion of
the quasi-coherent modules, by
`AlgebraicGeometry.SmallZariski.associatedModuleQcohCompRestrictIso` and
`AlgebraicGeometry.SmallZariski.restrictAssociatedSheafFunctorIso`, and that restriction is fully
faithful, being an equivalence; `CategoryTheory.Functor.fullyFaithfulCancelRight` cancels it. -/
public noncomputable def associatedModuleQcohIsoAssociatedSheafFunctor :
    associatedModuleQcoh B S hS ≅ associatedSheafFunctor B S hS :=
  Functor.fullyFaithfulCancelRight (restrictModuleOfSheaf B S hS)
    (associatedModuleQcohCompRestrictIso B S hS ≪≫ restrictAssociatedSheafFunctorIso B S hS)

/-- **[Stacks, Tag 0GN7] for the small site at `τ = Zariski`, for the functor the source
defines**: the assignment `𝓕 ↦ 𝓕ᵃ` of [Stacks, Tag 03DU] (4) — the sheaf of `𝒪`-modules on
`S_Zar` whose sections over `f : T → S` are `Γ(T, f^*𝓕)`,
`AlgebraicGeometry.SmallZariski.associatedSheafFunctor` — is fully faithful on the quasi-coherent
`𝒪_S`-modules.

`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh` is the same statement for the
*pullback*-defined functor of [Stacks, Remark 03FH]; this is it read through
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`, which identifies
the two.  Both are 0GN7 at `τ = Zariski`, and the source's own statement is about the sections
description, so the clause is only about the object the source names once this form exists.

0GN7 spells the target `QCoh(S_Zar, 𝒪)` where this is `Mod(S_Zar, 𝒪)`; that is the same
statement for the reason recorded on
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh`, full faithfulness into a
category being full faithfulness into any full subcategory containing the image, and the image
landing in `QCoh(S_Zar, 𝒪)` by [Stacks, Tag 03DV] (2).

**This is also clause (1) of [Stacks, Tag 06VE] at `τ = Zariski` for the sections-defined
functor**, that clause being the same assertion of full faithfulness; its second functor has
target `Mod(S_τ, 𝒪)`, which is the target here with nothing to read through.  The two attributes
sit together for the same reason they do on
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh` for the pullback-defined
functor. -/
@[stacks 0GN7 "small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor, whose value at 𝓕 is \
SmallZariski.associatedModuleOfSections.  The same clause for the pullback-defined functor of \
Remark 03FH is fullyFaithfulAssociatedModuleQcoh; the two functors are identified by \
associatedModuleQcohIsoAssociatedSheafFunctor",
  stacks 06VE "part (1), small site at τ = Zariski, for the SECTIONS-defined functor 𝓕 ↦ 𝓕ᵃ of \
Definition 03DU (4) — SmallZariski.associatedSheafFunctor, whose target Mod(S_Zar, 𝒪) is the \
target 06VE spells for its second functor.  The same clause for the pullback-defined functor of \
Remark 03FH is fullyFaithfulAssociatedModuleQcoh"]
public noncomputable def fullyFaithfulAssociatedSheafFunctor :
    (associatedSheafFunctor B S hS).FullyFaithful := by
  haveI := Functor.Full.of_iso (associatedModuleQcohIsoAssociatedSheafFunctor B S hS)
  haveI := Functor.Faithful.of_iso (associatedModuleQcohIsoAssociatedSheafFunctor B S hS)
  exact .ofFullyFaithful _

end SmallZariski

end AlgebraicGeometry

end
