module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# The local step of Stacks 03DX (1) at an arbitrary member of a covering family

The essential-surjectivity half of Stacks 03DX (1) begins like this: a quasi-coherent
`𝒪`-module `𝒢` on `(Sch/S)_fppf` has, by Stacks 03DL (6) read through Stacks 03DN, a covering
family `{X_i}` of the final object on whose members the restriction `𝒢|_{(Sch/S)_fppf/X_i}` has a
global presentation; and then "we claim that this implies that `𝒢|_{(Sch/X_i)_τ}` is `𝓕_i^a` for
some quasi-coherent sheaf `𝓕_i` on `X_i`".

**That claim is proved here, unconditionally, for an arbitrary object `T` of the big fppf
category over `S`.**  Three pieces meet:

* the localization `(Sch/S)_fppf / T` *is* the big fppf site of the scheme `X` of `T`, as a
  ringed site — the equivalence of categories is Mathlib's
  `CategoryTheory.Over.iteratedSliceEquiv` and the comparison of structure sheaves is the
  identity, `AlgebraicGeometry.BigFppfOver.reindexRing_objEquiv` below being a `rfl`;
* a global presentation on a site with a final object is a `SheafOfModules.Presentation`,
  `AlgebraicGeometry.BigFppfOver.nonempty_presentation_of_hasGlobalPresentation`, with no size
  hypothesis on the site;
* the local step at a `SheafOfModules.Presentation`,
  `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_presentation`.

The restriction functor that carries `𝒢` to a module on the big fppf site of `X` is
`AlgebraicGeometry.BigFppfOver.objRestrict`: restrict to the localization at `T` and then
reindex along the equivalence of sites.

With the local step discharged, the residue of
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal` is *purely* the gluing part of
the source's proof — full faithfulness of `𝓕 ↦ 𝓕^a` turning the canonical isomorphisms of `𝒢`
into a descent datum on the `𝓕_i`, the effectivity of descent for quasi-coherent sheaves
(Stacks 023T) gluing it to a quasi-coherent `𝓕` on `S`, and the sheaf property of `SheafHom`
(Stacks 03EM) assembling the local isomorphisms.  That residue is named
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohGlue`, and it no longer mentions
presentations of any kind.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objEquiv`: the equivalence of sites between the big fppf site
  of the scheme of `T` and the localization of the big fppf site of `S` at `T`.
* `AlgebraicGeometry.BigFppfOver.objRestrict`: restriction of a module on `(Sch/S)_fppf` to the
  big fppf site of the scheme of `T`.
* `AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohGlue`: **the gluing step of
  Stacks 03DX (1)** as a hypothesis — a module on `(Sch/S)_fppf` whose restriction to each
  member of some covering family of the final object is the associated module of a
  quasi-coherent sheaf on that member is itself an `𝓕^a`.  This is the appeal to Stacks 023T and
  Stacks 03EM and nothing else.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_objRestrict` and
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModule_objRestrict`: **the local step of
  Stacks 03DX (1) at an arbitrary object of the big fppf category over `S`**, unconditionally.
* `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohLocal_of_glue` and
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_glue`: the
  globalization step of Stacks 03DX (1), and hence its essential surjectivity, over the gluing
  step alone.
* `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohGlue_iff`: the gluing step is
  *equivalent* to Stacks 03DX (1)'s essential surjectivity, so the reduction neither loses nor
  smuggles in content.

## Implementation notes

Nothing here carries a `stacks` attribute: everything that would be a clause of Stacks 03DX is
still conditional on the gluing step, and a hypothesis is part of a citation.

`AlgebraicGeometry.BigFppfOver.objRestrict` is spelled with
`SheafOfModules.pushforward (𝟙 (Stacks.SheafOfModules.reindexRing …))` rather than with
`Stacks.SheafOfModules.reindexEquivalence`, even though the two are the same functor: that is
the exact shape in which `Stacks.SheafOfModules.hasGlobalPresentation_reindex` states its
conclusion, so the transport of a global presentation needs no bridging isomorphism.

The two continuity instances are restatements of Mathlib's instances for
`CategoryTheory.Over.iteratedSliceForward` and `CategoryTheory.Over.iteratedSliceBackward` at
`AlgebraicGeometry.BigFppfOver.topology`; instance search does not see them through
`CategoryTheory.Equivalence.symm`, which is why they are named.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- **Stacks 06WI for the identity fibration.**  The big fppf category of the scheme `X` of an
object `T` of the big fppf category over `S` is the localization of the latter at `T`.  This is
Mathlib's `CategoryTheory.Over.iteratedSliceEquiv`, read in the direction in which the big site
of `X` is the source. -/
public noncomputable abbrev objEquiv :
    BigFppfOver B (objScheme B S hS T) (contains_objScheme B S hS T) ≌ Over T :=
  (Over.iteratedSliceEquiv T).symm

/-- Passing from the big fppf site of the scheme of `T` to the localization at `T` is
continuous. -/
public instance isContinuous_objEquiv_functor :
    (objEquiv B S hS T).functor.IsContinuous
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((topology B S hS).over T) :=
  isContinuous_iteratedSliceBackward B S hS T

/-- Passing from the localization at `T` to the big fppf site of the scheme of `T` is
continuous. -/
public instance isContinuous_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsContinuous ((topology B S hS).over T)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  inferInstanceAs ((Over.iteratedSliceForward T).IsContinuous
    ((B.topology.over (B.obj hS)).over T) (B.topology.over T.left))

/-- Passing from the big fppf site of the scheme of `T` to the localization at `T` is
cocontinuous. -/
public instance isCocontinuous_objEquiv_functor :
    (objEquiv B S hS T).functor.IsCocontinuous
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((topology B S hS).over T) :=
  inferInstanceAs ((Over.iteratedSliceBackward T).IsCocontinuous (B.topology.over T.left)
    ((B.topology.over (B.obj hS)).over T))

/-- Passing from the localization at `T` to the big fppf site of the scheme of `T` is
cocontinuous. -/
public instance isCocontinuous_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsCocontinuous ((topology B S hS).over T)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  inferInstanceAs ((Over.iteratedSliceForward T).IsCocontinuous
    ((B.topology.over (B.obj hS)).over T) (B.topology.over T.left))

/-- **The two topologies correspond under the equivalence of Stacks 06WI.**  A sieve of the
localization of the big fppf site of `S` at `T` is covering exactly when its image in the big
fppf site of the scheme of `T` is, both functors being cocontinuous. -/
public instance isDenseSubsite_objEquiv_inverse :
    (objEquiv B S hS T).inverse.IsDenseSubsite ((topology B S hS).over T)
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (objEquiv B S hS T)

/-- **The equivalence of Stacks 06WI is an equivalence of *ringed* sites, on the nose.**  The
structure sheaf of the localization of the big fppf site of `S` at `T`, transported along
`AlgebraicGeometry.BigFppfOver.objEquiv`, *is* the structure sheaf of the big fppf site of the
scheme of `T`: both send an object to the global functions on its underlying scheme, and
`CategoryTheory.Over.iteratedSliceBackward_forget_forget` is an equality of functors. -/
public theorem reindexRing_objEquiv :
    Stacks.SheafOfModules.reindexRing
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
        (objEquiv B S hS T) ((structureSheaf B S hS).over T) =
      structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T) :=
  rfl

/-- Reindexing a module on the localization of the big fppf site of `S` at `T` along
`AlgebraicGeometry.BigFppfOver.objEquiv` — a module on the big fppf site of the scheme of `T`.
It is an equivalence of categories, being the functor of
`Stacks.SheafOfModules.reindexEquivalence`. -/
public noncomputable abbrev objRestrictFunctor :
    SheafOfModules.{u} ((structureSheaf B S hS).over T) ⥤
      SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  SheafOfModules.pushforward.{u}
    (𝟙 (Stacks.SheafOfModules.reindexRing
      (topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      (objEquiv B S hS T) ((structureSheaf B S hS).over T)))

/-- **The restriction `𝒢 ↦ 𝒢|_{(Sch/X)_fppf}` of the source's proof of Stacks 03DX (1).**
Restrict a module on `(Sch/S)_fppf` to the localization at `T` and read the result on the big
fppf site of the scheme `X` of `T`, which is the same ringed site by
`AlgebraicGeometry.BigFppfOver.reindexRing_objEquiv`. -/
public noncomputable abbrev objRestrict :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T ⋙ objRestrictFunctor B S hS T

/-- A global presentation of the restriction of `𝒢` to the localization at `T` is a global
presentation of its restriction to the big fppf site of the scheme of `T`: the two sites agree,
and a global presentation is carried along an equivalence of ringed sites by
`Stacks.SheafOfModules.hasGlobalPresentation_reindex`. -/
public theorem hasGlobalPresentation_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over T).HasGlobalPresentation) :
    ((objRestrict B S hS T).obj G).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_reindex (objEquiv B S hS T)
    ((structureSheaf B S hS).over T) (G.over T) h

/-- **Stacks 03DX (1), essential surjectivity, local step, at an arbitrary object of the big
fppf category over `S`**, unconditionally.  If the restriction of `𝒢` to the localization at `T`
has a global presentation, then its restriction to the big fppf site of the scheme `X` of `T` is
the associated module `𝓕^a` of a quasi-coherent `𝒪_X`-module `𝓕`.

This is the sentence "we claim that this implies that `𝒢|_{(Sch/S_i)_τ}` is `𝓕_i^a` for some
quasi-coherent sheaf `𝓕_i` on `S_i`" of the source's proof.  The global presentation becomes a
`SheafOfModules.Presentation` because the big fppf site of `X` has a final object, and the local
step at a presentation is then unconditional. -/
public theorem exists_isQuasicoherent_iso_associatedModule_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over T).HasGlobalPresentation) :
    ∃ F : (objScheme B S hS T).Modules, F.IsQuasicoherent ∧
      Nonempty ((associatedModule B (objScheme B S hS T)
        (contains_objScheme B S hS T)).obj F ≅ (objRestrict B S hS T).obj G) :=
  exists_isQuasicoherent_iso_associatedModule_of_presentation B _ _
    (nonempty_presentation_of_hasGlobalPresentation B _ _
      (hasGlobalPresentation_objRestrict B S hS T h)).some

/-- **Stacks 03DX (1), essential surjectivity, local step, at an arbitrary object**, in the form
of a membership in the essential image of the functor
`QCoh(𝒪_X) ⥤ Mod((Sch/X)_fppf, 𝒪)` of Stacks 06VE. -/
public theorem essImage_associatedModule_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over T).HasGlobalPresentation) :
    (associatedModuleQcoh B (objScheme B S hS T)
      (contains_objScheme B S hS T)).essImage ((objRestrict B S hS T).obj G) := by
  obtain ⟨F, hF, e⟩ := exists_isQuasicoherent_iso_associatedModule_objRestrict B S hS T h
  exact ⟨⟨F, hF⟩, e⟩

/-- **The gluing step of Stacks 03DX (1) for `τ = fppf`**, as a hypothesis: a sheaf of modules
on `(Sch/S)_fppf` whose restriction to the big fppf site of the scheme of each member of some
covering family of the final object is the associated module of a quasi-coherent sheaf there is
itself the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`.

This is `AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal` with the *local* step
discharged: the hypothesis supplies the modules `𝓕_i` downstairs, so what is left is exactly the
part of the source's proof that is not local — full faithfulness of `𝓕 ↦ 𝓕^a` (Stacks 0GN7)
turning the canonical isomorphisms of `𝒢` over `X_i ×_S X_j` into a descent datum on the `𝓕_i`,
the effectivity of descent for quasi-coherent sheaves (Stacks 023T) gluing that datum to a
quasi-coherent `𝓕` on `S`, and the sheaf property of `SheafHom(𝓕^a, 𝒢)` (Stacks 03EM)
assembling the local isomorphisms into a global one.  No presentation of any kind occurs in the
statement. -/
public abbrev EssImageAssociatedModuleQcohGlue : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (I : Type (u + 1))
      (X : I → BigFppfOver B S hS), (topology B S hS).CoversTop X →
      (∀ i, ∃ F : (objScheme B S hS (X i)).Modules, F.IsQuasicoherent ∧
        Nonempty ((associatedModule B (objScheme B S hS (X i))
          (contains_objScheme B S hS (X i))).obj F ≅ (objRestrict B S hS (X i)).obj G)) →
    (associatedModuleQcoh B S hS).essImage G

/-- **The globalization step of Stacks 03DX (1) follows from the gluing step alone.**  The
global presentations that
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal` carries on the members of the
covering family are turned into quasi-coherent sheaves downstairs by
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_objRestrict`, which
is unconditional; nothing else about them is used. -/
public theorem essImageAssociatedModuleQcohLocal_of_glue
    (h : EssImageAssociatedModuleQcohGlue B S hS) :
    EssImageAssociatedModuleQcohLocal B S hS := fun G I X hX hP =>
  h G I X hX fun i => exists_isQuasicoherent_iso_associatedModule_objRestrict B S hS (X i) (hP i)

/-- **Stacks 03DX (1), essential surjectivity, for `τ = fppf`, over the gluing step.**  Every
quasi-coherent `𝒪`-module on the big fppf site of `S` is isomorphic to `𝓕^a` for a
quasi-coherent `𝒪_S`-module `𝓕`.

This is the sole surviving hypothesis of
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite'` and of the Stacks
0GNC, 0GNE and 03DX statements that rest on it, now reduced to the appeal to Stacks 023T and
Stacks 03EM with the first paragraph of the source's proof discharged. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_glue
    (h : EssImageAssociatedModuleQcohGlue B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule B S hS
    (essImageAssociatedModuleQcohLocal_of_glue B S hS h)

/-- The gluing step is *implied* by the conclusion it is used for, so it is not a
strengthening of Stacks 03DX (1)'s essential surjectivity.  A module whose restriction to each
member of a covering family of the final object is an associated module there is quasi-coherent
on each of those members, by the quasi-coherence of associated modules, hence quasi-coherent by
Stacks 03DN — and then the conclusion applies to it. -/
public theorem essImageAssociatedModuleQcohGlue_of_quasicoherentIsEssImage
    (h : QuasicoherentIsEssImageAssociatedModule B S hS) :
    EssImageAssociatedModuleQcohGlue B S hS := by
  intro G I X hX hF
  refine h G ?_
  change G.IsQuasicoherentOnSite
  rw [Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite G]
  refine ⟨I, X, hX, fun i => ?_⟩
  obtain ⟨F, hF', ⟨e⟩⟩ := hF i
  have hqc : ((objRestrict B S hS (X i)).obj G).IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso e
      (associatedModuleIsQuasicoherent B _ _ ⟨F, hF'⟩)
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex (objEquiv B S hS (X i))
    ((structureSheaf B S hS).over (X i)) (G.over (X i)) hqc

/-- **The gluing step and Stacks 03DX (1)'s essential surjectivity are equivalent.**  The
hypothesis named here is therefore exactly the content that the appeal to Stacks 023T and
Stacks 03EM supplies, with the local step of the source's proof already discharged. -/
public theorem essImageAssociatedModuleQcohGlue_iff :
    EssImageAssociatedModuleQcohGlue B S hS ↔
      QuasicoherentIsEssImageAssociatedModule B S hS :=
  ⟨quasicoherentIsEssImageAssociatedModule_of_glue B S hS,
    essImageAssociatedModuleQcohGlue_of_quasicoherentIsEssImage B S hS⟩

end BigFppfOver

end AlgebraicGeometry

end
