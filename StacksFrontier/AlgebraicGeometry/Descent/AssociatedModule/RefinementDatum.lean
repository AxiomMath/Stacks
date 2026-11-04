module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithfulUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality

/-!
# The descent datum of Stacks 03DX (1) on the fpqc refinement alone

`AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement` carries the gluing step of
Stacks 03DX (1) with *two* families of objects of `(Sch/S)_fppf`: a family `X` covering the final
object, on whose members the local associated-module data of Stacks 03DV live, and a refinement
`Y` of it whose structure morphisms are already an fpqc covering family of the scheme `S`.  Both
are there because the local data arrive on `X` while descent for quasi-coherent sheaves is
stated for `Y`.

**One family suffices.**  The local datum of Stacks 03DX (1) transports along a morphism of the
big fppf site — `AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_refinement` — so the
data on `X` may be moved to `Y` before anything else happens, after which `X` is never mentioned
again.  What is left, `AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum`, is the same
step for a *single* family which covers the final object and is fpqc downstairs, and
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff_datumOfRefinement` shows that
nothing was gained or lost.

The file also writes down the transition isomorphisms that such a datum is made of.  Over an
object `Z` of `(Sch/S)_fppf` mapping into two members of the family, the two local isomorphisms
give `(g₁^*𝓕₁)^a ≅ 𝒢|_{(Sch/Z)_fppf} ≅ (g₂^*𝓕₂)^a`, and Stacks 0GN7 — fully faithful with no
hypothesis — descends that to an isomorphism `g₁^*𝓕₁ ≅ g₂^*𝓕₂` of quasi-coherent modules on the
scheme of `Z`.  These isomorphisms satisfy the identity and composition laws of a descent datum.
Compatibility with further pullback is not proved in this file; it is the pseudonaturality of the
comparison of Stacks 03DV — see the implementation notes.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum`: **the gluing step of
  Stacks 03DX (1) with the refinement already carried out** — out of local associated-module
  data on a family which covers the final object of `(Sch/S)_fppf` and whose structure morphisms
  are an fpqc covering family of `S`, an fpqc covering family of `S` and a quasi-coherent descent
  datum for it whose effectivity exhibits `𝒢` as an associated module.
* `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`: the comparison isomorphism
  `(g^*𝓕)^a ≅ 𝒢|_{(Sch/X')_fppf}` along a morphism `g` of the big fppf site.
* `AlgebraicGeometry.BigFppfOver.transitionIso`: **the transition isomorphism of a descent datum
  for Stacks 03DX (1)**, over an object mapping into two members of the family.

## Main results

* `AlgebraicGeometry.BigFppfOver.hom_ext_of_associatedModule_map`: the faithfulness half of
  Stacks 0GN7 on morphisms of quasi-coherent modules rather than of the full subcategory of
  them.
* `AlgebraicGeometry.BigFppfOver.associatedModule_map_transitionIso`: the defining property of
  the transition isomorphism — its associated module is the composite of the two comparisons.
* `AlgebraicGeometry.BigFppfOver.transitionIso_self` and
  `AlgebraicGeometry.BigFppfOver.transitionIso_trans`: the identity and composition laws of the
  transition isomorphisms — `CategoryTheory.Pseudofunctor.DescentData.hom_self` and
  `CategoryTheory.Pseudofunctor.DescentData.hom_comp` for them.
* `AlgebraicGeometry.BigFppfOver.associatedModuleDatumOfRefinement_of_refinedDatum`: the
  one-family form implies the two-family form, the local data being transported along the
  refinement by `AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_refinement`.
* `AlgebraicGeometry.BigFppfOver.refinedDatum_of_associatedModuleGlueDescentDatum`,
  `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff_datumOfRefinement`: the
  converses, hence the equivalence — the one-family form is **not** a strengthening.

## Implementation notes

Nothing here carries a `stacks` attribute.  `AssociatedModuleRefinedDatum` is *stated* here and
proved elsewhere — `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean` —
and Stacks 03DX (1) quantifies over five topologies while everything here is the big fppf site.

The index universe is `u + 1`, as in
`AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement`: the covering families of the
final object of `(Sch/S)_fppf` are indexed by the objects of that site, which form a
`Type (u + 1)`.

The conclusion keeps the fpqc covering family of `S` existentially quantified rather than
pinning it to `AlgebraicGeometry.BigFppfOver.objHypercover` of the given family, even though
that is the family the intended proof uses.  Pinning it would make the statement *stronger* than
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` and the converse below would
fail: a descent datum on a prescribed family cannot be produced from one on an unknown family
without already knowing the conclusion, which is what the datum is for.

`AlgebraicGeometry.BigFppfOver.transitionIso` is stated between the pullbacks along
`AlgebraicGeometry.BigFppfOver.objHom` of `CategoryTheory.Over.mk gᵢ.left`, which are modules on
the scheme of `CategoryTheory.Over.mk gᵢ.left` read as an object over the scheme of `Tᵢ`,
whereas `AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` forms its associated
module on the scheme of `Z`.  Those schemes are the same definitionally and not merely up to
isomorphism — the underlying scheme of a morphism's source in `(Sch/S)_fppf` is the underlying
scheme of that source — and that is what lets the two comparisons at `g₁` and at `g₂` be
composed with no transport at all.

**The fourth field of the descent datum.**  A `CategoryTheory.Pseudofunctor.DescentData` for
`AlgebraicGeometry.modulePullbackPseudofunctor` has four fields.  Three of them are supplied by
`AlgebraicGeometry.BigFppfOver.transitionIso`, `…transitionIso_self` and `…transitionIso_trans`.
The fourth, `CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` — equivalently the cocycle
condition of `CategoryTheory.Pseudofunctor.DescentData'` over triple fibre products — is a
different kind of statement: it asks that
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` be compatible with *composition*
in the big fppf site, that is, that the comparison of Stacks 03DV be a *pseudonatural*
transformation and not merely a family of isomorphisms indexed by the morphisms of the site.  It
is not available by unfolding: `ObjectFunctoriality.lean` supplies the components
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` and
`AlgebraicGeometry.BigFppfOver.objRestrictComp` but no coherence between them, and both are
assembled from `CategoryTheory.Adjunction.leftAdjointUniq`.  It is the theorem
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsCocycle.lean:420`),
proved with no hypothesis.

The datum is presented through `CategoryTheory.Pseudofunctor.DescentData'`, on chosen fibre
products, rather than through `CategoryTheory.Pseudofunctor.DescentData` directly, and not only
for convenience: the transition morphisms of the latter are indexed by *every*
scheme mapping to two members of the family, whereas `𝒢` can only be restricted to a scheme
which is an object of the big fppf site.  The fibre products of objects of the site are again
objects of the site — `AlgebraicGeometry.BigFppfOver.memberProd` is such a fibre product — which
is what lets the transitions above, indexed by objects of `AlgebraicGeometry.BigFppfOver`, serve
the fibre-product presentation that
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlueDescentDatumViaUnprimed.lean`
assembles.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison isomorphism along a morphism of the big site -/

/-- **The comparison isomorphism that a descent datum for Stacks 03DX (1) is assembled from.**
Let the restriction of `𝒢` to the big fppf site of the scheme `X` of an object `T` of
`(Sch/S)_fppf` be the associated module of an `𝒪_X`-module `𝓕`, by the isomorphism `e`.  Then
for every `g : T' ⟶ T` the restriction of `𝒢` to the big fppf site of the scheme `X'` of `T'`
is the associated module of the pullback of `𝓕` along `g`:

    `(g^*𝓕)^a ≅ 𝒢|_{(Sch/X')_fppf}`.

This is the isomorphism whose existence
`AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_hom` asserts, named: it is
Stacks 03DV functorial in the object,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, followed by the restriction
of `e` and the functoriality of restriction,
`AlgebraicGeometry.BigFppfOver.objRestrictComp`.  Naming it is what lets the transition
isomorphisms of a descent datum be written down: over an object mapping into two members of a
covering family, two such isomorphisms share their target and so compose to an isomorphism of
associated modules, which Stacks 0GN7 descends to the schemes. -/
public noncomputable def localAssociatedModuleComparison
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (F : (objScheme B S hS T).Modules)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    (associatedModule B (objScheme B S hS T') (contains_objScheme B S hS T')).obj
        ((Scheme.Modules.pullback (objHom B (objScheme B S hS T)
          (contains_objScheme B S hS T) (Over.mk g.left))).obj F) ≅
      (objRestrict B S hS T').obj G :=
  (associatedModuleObjRestrictNatIso B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left)).app F ≪≫
    (objRestrict B (objScheme B S hS T) (contains_objScheme B S hS T)
      (Over.mk g.left)).mapIso e ≪≫
    (objRestrictComp B S hS g).app G

/-! ### The transition isomorphisms of the datum -/

/-- **The transition isomorphism of a descent datum for Stacks 03DX (1).**  Let `Z` be an object
of `(Sch/S)_fppf` with morphisms `g₁ : Z ⟶ T₁` and `g₂ : Z ⟶ T₂` into two members of a covering
family on each of which the restriction of `𝒢` is an associated module, by `e₁` and `e₂`.  Then
the pullbacks of the two quasi-coherent modules downstairs are isomorphic on the scheme of `Z`:

    `g₁^*𝓕₁ ≅ g₂^*𝓕₂`.

This is the first paragraph of the source's proof after the local step.  Both pullbacks have
associated module `𝒢|_{(Sch/Z)_fppf}`, by
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison`, so the composite of the one
comparison with the inverse of the other is an isomorphism of associated modules; Stacks 0GN7 at
the scheme of `Z` — fully faithful with no hypothesis,
`AlgebraicGeometry.BigFppfOver.fullyFaithfulAssociatedModuleQcoh'` — has it as the image of a
unique isomorphism downstairs, and that is the transition.  The pullbacks are quasi-coherent by
Stacks 01BG. -/
public noncomputable def transitionIso
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (Scheme.Modules.pullback (objHom B (objScheme B S hS T₁)
          (contains_objScheme B S hS T₁) (Over.mk g₁.left))).obj F₁ ≅
      (Scheme.Modules.pullback (objHom B (objScheme B S hS T₂)
        (contains_objScheme B S hS T₂) (Over.mk g₂.left))).obj F₂ :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (objScheme B S hS Z).ringCatSheaf)).mapIso
    ((fullyFaithfulAssociatedModuleQcoh' B (objScheme B S hS Z)
        (contains_objScheme B S hS Z)).preimageIso
      (X := ⟨_, Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁⟩)
      (Y := ⟨_, Stacks.Modules.isQuasicoherent_pullback _ F₂ hF₂⟩)
      (localAssociatedModuleComparison B S hS G g₁ F₁ e₁ ≪≫
        (localAssociatedModuleComparison B S hS G g₂ F₂ e₂).symm))

/-- **Morphisms of quasi-coherent modules on a scheme of the site are determined by their
associated modules**, the faithfulness half of Stacks 0GN7 read on morphisms of modules rather
than of the full subcategory of quasi-coherent ones.  The inclusion of that subcategory is fully
faithful, so a morphism of quasi-coherent modules is a morphism of the subcategory in exactly
one way. -/
public theorem hom_ext_of_associatedModule_map (T : Scheme.{u}) (hT : B.Contains T)
    {M N : T.Modules} (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) {a b : M ⟶ N}
    (h : (associatedModule B T hT).map a = (associatedModule B T hT).map b) : a = b :=
  congrArg InducedCategory.Hom.hom ((fullyFaithfulAssociatedModuleQcoh' B T hT).map_injective
    (f := ObjectProperty.homMk (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) a)
    (g := ObjectProperty.homMk (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) b) h)

/-- **The transition isomorphism is characterized by its associated module**: applying
`𝓕 ↦ 𝓕^a` on the scheme of `Z` to it returns the composite of the two comparisons of
`AlgebraicGeometry.BigFppfOver.localAssociatedModuleComparison` it was descended from.  This is
the defining property of the transition, and the identity and composition laws below are read
off it. -/
public theorem associatedModule_map_transitionIso
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ Z : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G) :
    (associatedModule B (objScheme B S hS Z) (contains_objScheme B S hS Z)).map
        (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom =
      (localAssociatedModuleComparison B S hS G g₁ F₁ e₁).hom ≫
        (localAssociatedModuleComparison B S hS G g₂ F₂ e₂).inv :=
  (fullyFaithfulAssociatedModuleQcoh' B (objScheme B S hS Z)
    (contains_objScheme B S hS Z)).map_preimage _

/-- **The transition isomorphism of a member with itself is the identity**, which is
`CategoryTheory.Pseudofunctor.DescentData.hom_self` for
`AlgebraicGeometry.BigFppfOver.transitionIso`.  Its associated module is the composite of a
comparison with its own inverse, hence the identity, and Stacks 0GN7 is faithful. -/
public theorem transitionIso_self
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T Z : BigFppfOver B S hS} (g : Z ⟶ T)
    {F : (objScheme B S hS T).Modules} (hF : F.IsQuasicoherent)
    (e : (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T)).obj F ≅
      (objRestrict B S hS T).obj G) :
    (transitionIso B S hS G g g hF e hF e).hom = 𝟙 _ := by
  refine hom_ext_of_associatedModule_map B _ (contains_objScheme B S hS Z)
    (Stacks.Modules.isQuasicoherent_pullback _ F hF)
    (Stacks.Modules.isQuasicoherent_pullback _ F hF) ?_
  rw [associatedModule_map_transitionIso]
  simp

/-- **The transition isomorphisms compose**, which is
`CategoryTheory.Pseudofunctor.DescentData.hom_comp` for
`AlgebraicGeometry.BigFppfOver.transitionIso`: over one object mapping into three members of the
family, the transition from the first member to the second followed by the transition from the
second to the third is the transition from the first to the third.  The three comparisons share
their target, so their associated modules telescope, and Stacks 0GN7 is faithful. -/
public theorem transitionIso_trans
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {T₁ T₂ T₃ Z : BigFppfOver B S hS}
    (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂) (g₃ : Z ⟶ T₃)
    {F₁ : (objScheme B S hS T₁).Modules} (hF₁ : F₁.IsQuasicoherent)
    (e₁ : (associatedModule B (objScheme B S hS T₁) (contains_objScheme B S hS T₁)).obj F₁ ≅
      (objRestrict B S hS T₁).obj G)
    {F₂ : (objScheme B S hS T₂).Modules} (hF₂ : F₂.IsQuasicoherent)
    (e₂ : (associatedModule B (objScheme B S hS T₂) (contains_objScheme B S hS T₂)).obj F₂ ≅
      (objRestrict B S hS T₂).obj G)
    {F₃ : (objScheme B S hS T₃).Modules} (hF₃ : F₃.IsQuasicoherent)
    (e₃ : (associatedModule B (objScheme B S hS T₃) (contains_objScheme B S hS T₃)).obj F₃ ≅
      (objRestrict B S hS T₃).obj G) :
    (transitionIso B S hS G g₁ g₂ hF₁ e₁ hF₂ e₂).hom ≫
        (transitionIso B S hS G g₂ g₃ hF₂ e₂ hF₃ e₃).hom =
      (transitionIso B S hS G g₁ g₃ hF₁ e₁ hF₃ e₃).hom := by
  refine hom_ext_of_associatedModule_map B _ (contains_objScheme B S hS Z)
    (Stacks.Modules.isQuasicoherent_pullback _ F₁ hF₁)
    (Stacks.Modules.isQuasicoherent_pullback _ F₃ hF₃) ?_
  rw [Functor.map_comp, associatedModule_map_transitionIso,
    associatedModule_map_transitionIso, associatedModule_map_transitionIso]
  simp

/-! ### The gluing step on a single, already fpqc, covering family -/

/-- **The gluing step of Stacks 03DX (1) with the refinement already carried out.**  Out of a
sheaf of modules `𝒢` on `(Sch/S)_fppf` and a *single* family `Y` of objects of `(Sch/S)_fppf`
which covers the final object, whose structure morphisms `Y j ⟶ S` are an fpqc covering family
of the scheme `S`, and the restriction of `𝒢` to the big fppf site of the scheme of each of
whose members is an associated module, it produces an fpqc covering family of `S` and a
quasi-coherent descent datum for it whose effectivity — the effectivity half of Stacks 023T —
exhibits `𝒢` as an associated module.

Compared with `AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement` the family on
which the local data are carried and the family which is fpqc downstairs have been identified;
`AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_refinement` is what identifies them,
and `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff_datumOfRefinement` shows
that this is an equivalent hypothesis and not a stronger one. -/
public abbrev AssociatedModuleRefinedDatum : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (J : Type (u + 1))
      (Y : J → BigFppfOver B S hS), (topology B S hS).CoversTop Y →
      (objHypercover B S hS Y).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
      (∀ j, HasLocalAssociatedModule B S hS G (Y j)) →
    ∃ (𝒰 : PreZeroHypercover.{u + 1} S) (_ : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
      (D : QuasicoherentDescentData 𝒰.f), D.IsEffective →
        (associatedModuleQcoh B S hS).essImage G

/-- **One family suffices: the one-family form implies the two-family form.**  The local
associated-module data that `AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement`
carries on the family `X` covering the final object are transported to the refinement `Y` by
`AlgebraicGeometry.BigFppfOver.hasLocalAssociatedModule_of_refinement`, which is unconditional;
after that the family `X` is not mentioned again. -/
public theorem associatedModuleDatumOfRefinement_of_refinedDatum
    (h : AssociatedModuleRefinedDatum B S hS) :
    AssociatedModuleDatumOfRefinement B S hS := fun G _ _X _hX hF J Y hY hfpqc hre =>
  h G J Y hY hfpqc fun j => hasLocalAssociatedModule_of_refinement B S hS G hF hre j

/-- **The one-family form is implied by the descent datum of Stacks 03DX (1)**, so assuming it
is not a strengthening.  The family `Y` is handed to
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` as its covering family of the
final object — its being fpqc downstairs is simply not used there — and the compatible family of
local isomorphisms that comes back is assembled into a global one by the Stacks 03EM step
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd`, which is
unconditional. -/
public theorem refinedDatum_of_associatedModuleGlueDescentDatum
    (h : AssociatedModuleGlueDescentDatum B S hS) :
    AssociatedModuleRefinedDatum B S hS := by
  intro G J Y hY _hfpqc hlocal
  obtain ⟨𝒰, h𝒰, D, hD⟩ := h G J Y hY hlocal
  refine ⟨𝒰, h𝒰, D, fun heff => ?_⟩
  obtain ⟨𝓕, h𝓕, e, he⟩ := hD heff
  exact essImage_associatedModuleQcoh_of_forall_memberProd B S hS G Y hY 𝓕 h𝓕 e he

/-- **The one-family form and the descent datum of Stacks 03DX (1) are equivalent.**  Carrying
out the refinement is therefore not part of what the appeal to Stacks 023T supplies: what is
left is exactly the construction of a quasi-coherent descent datum out of the local
associated-module data, now on one family instead of two. -/
public theorem associatedModuleRefinedDatum_iff :
    AssociatedModuleRefinedDatum B S hS ↔ AssociatedModuleGlueDescentDatum B S hS :=
  ⟨fun h => associatedModuleGlueDescentDatum_of_datumOfRefinement B S hS
      (associatedModuleDatumOfRefinement_of_refinedDatum B S hS h),
    refinedDatum_of_associatedModuleGlueDescentDatum B S hS⟩

/-- **The one-family form and the two-family form are equivalent**, so nothing was smuggled in
by identifying the family on which the local data are carried with the fpqc refinement.  This is
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff` read through
`AlgebraicGeometry.BigFppfOver.associatedModuleDatumOfRefinement_iff`. -/
public theorem associatedModuleRefinedDatum_iff_datumOfRefinement :
    AssociatedModuleRefinedDatum B S hS ↔ AssociatedModuleDatumOfRefinement B S hS :=
  (associatedModuleRefinedDatum_iff B S hS).trans
    (associatedModuleDatumOfRefinement_iff B S hS).symm

end AlgebraicGeometry.BigFppfOver

end
