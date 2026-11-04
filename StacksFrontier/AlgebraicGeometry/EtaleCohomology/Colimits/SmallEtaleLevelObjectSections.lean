module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocyclePresentation
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.AbelianObjectSectionsOfColimitOfFiniteSites

/-!
# The object-level inputs of Stacks 09YQ in degree zero, at the levels of Stacks 0EYL

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` — the
degree-zero step of [Stacks, Tag 09YQ] over an object that neither the levels of
[Stacks, Tag 0EYL] nor their colimit site contain — takes two inputs about the system: that every
section of the colimit sheaf over the image of an object of a level comes from a section at some
level below (`hsurjObj`), and that two sections of a level with the same image agree after a
transition (`hsep`).

This file supplies both for a system of abelian étale sheaves presented on **Mathlib's** small
étale sites, in the inverse-image vocabulary in which [Stacks, Tag 09YQ] states its hypothesis.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelSection_eq_of_pullbackPresentation`
  — **`hsurjObj` at the étale system.**
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelCocycleMap_eq_of_pullbackPresentation`
  — **`hsep` at the étale system.**

## How the crossing goes, and what it does not assume

The chain is the one `haff` uses, and no step of it is a hypothesis.
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` reads the system on the levels
as direct-image transition data satisfying the cocycle law — the notion [Stacks, Tag 0EZL]
imposes, with **no identity law** —
`...isColimitPresentation_levelCocycleSystem` presents it there, and
`Stacks.WeakSites.ColimitSiteCohomology.exists_level_section_eq_of_cocycleIsColimitPresentation`
and `...exists_cocycleMap_eq_of_cocycleIsColimitPresentation` read the two clauses off that
presentation. Those two in turn split the identity arrows' idempotents and read a filtered colimit
of abelian groups; the module docstring of
`StacksFrontier/CategoryTheory/Sites/InverseSystem/AbelianObjectSectionsOfColimitOfFiniteSites.lean`
says how.

**No identity law is assumed anywhere in the chain, and that is what makes these usable for a
faithful registration of the tag.** An `Stacks.EtaleCohomology.EtaleSheafSystem` has fields `obj`,
`map` and `map_comp` only, which is exactly the datum of [Stacks, Tag 0EZL]; the splitting of the
idempotents happens inside the proof and is invisible in the statements, whose sections are those
of the system itself.

**The site of the colimit is the raised small affine étale site of `X`, written through
`Stacks.EtaleCohomology.AffineEtaleModel.precoverage`**, which is the spelling the presentation of
the crossing carries. It is the same precoverage as
`Stacks.EtaleCohomology.AffineLimitCohomology.limitSitePrecoverage`, definitionally and not by a
lemma, so the four site inputs of [Stacks, Tag 09YP] that
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/AffineEtaleCohomologyColimit.lean` proves
for the latter — `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`,
`toLimitSmall_hom_eventually_eq` and `mem_limitSitePrecoverage_iff` — are supplied to it as they
stand.

## What is still owed for the degree-zero statement of Tag 09YQ

These two clauses are what the one-hypercover step takes *about the system*; with the cocycle law
`cocycleMap_app_comp` and the leg compatibility `cocycleLeg_app_eq_of_isCompatible` of the same
file, applied to `levelCocycleSystem` and to `levelPullbackLeg` below, all four of its inputs
about the system are available. Three things are still owed, all geometric and none of them in
this file.

**The one-hypercover datum**, which
`Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum` produces: for an object
`V₀` of Mathlib's size-bounded small étale site of a level whose scheme is quasi-compact and
quasi-separated, a finite family of objects of that level which is a one-hypercover of the base
change of `V₀` at every level below and at the limit. It is stated for the ambient sites
`AlgebraicGeometry.SmallEtale B · ·` and the crossings
`...limitToSmallEtale`, `...QcSeparatedColimit.levelToSmallEtale`, which are exactly the `w₀` and
`wn` the one-hypercover step quantifies over, so it is used as it stands at abelian coefficients.

**The restriction isomorphisms `e₀` and `en` of that step are `CategoryTheory.Iso.refl`.** With `w₀ := limitToSmallEtale D c B hX` and
`G' := (AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX AddCommGrpCat).obj 𝓕`,
the presheaf `w₀ᵒᵖ ⋙ G'` *is* the presheaf of
`(AffineEtaleModel.modelRestrict B c.pt hX).obj ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)`
— the sheaf of the level presentation — because
`AffineEtaleModel.toModel` followed by `CategoryTheory.AsSmall.down` is `limitToSmallEtale`
followed by `AlgebraicGeometry.SmallEtale.toEtaleSite` on the nose. At a level the same holds with
`wn n := levelToSmallEtale D c B hD hX hc n` and
`Hs n := (etaleSiteRestriction B (X_n) _ AddCommGrpCat).obj (F.obj (levelIndex n))`, by
`...levelEtaleRestrictAb_obj` and `levelEtaleSite`. So the abelian counterpart of
`Stacks.EtaleCohomology.AffineLimitCohomology.raisedSheaf` and of
`Stacks.EtaleCohomology.QcSeparatedColimit.levelRaisedSheaf` is not a construction to be made:
both isomorphisms are the identity.

**The pinning is what remains.** The one-hypercover step quantifies over the restriction map `ρ`
from the sections of `F_n` over the base change `V_n` to the sections of `𝓕` over the base change
`V_X`, and pins it by its effect on the objects of the datum (`hρ`): the restriction to the image
of `W₀ k` of `ρ(t)` is the leg `ι_n` applied to the restriction of `t`. A consumer that wants the
conclusion for a *particular* geometric map has to prove that map satisfies `hρ` — for the
degree-zero statement `H0` that map is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection`, and for the
surjectivity `hqc` of
`Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` it is
`Stacks.EtaleCohomology.opensSectionsLeg`. That comparison — between the transpose of a leg read
on sections over an object and the level leg `levelPullbackLeg` read on the objects of the datum —
is not available in the library, and it is the whole of what those two statements still need.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex)

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]
  (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
  (ι : ∀ i : Iᵒᵖ,
    (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)

/-- The legs of the level presentation of a family of maps out of the inverse images: the
transposed family, read on the levels. This is the `ι` of
`...isColimitPresentation_levelCocycleSystem`, named so that the two statements below mention it
without writing the transpose out. -/
abbrev levelPullbackLeg (n : (sys D c B hD hX hc).I) :
    ((levelCocycleSystem D c B hD hX hc F).obj n).obj ⟶
      (toLimitSmall D c B hD hX hc n).op ⋙
        ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj :=
  levelCocycleLeg D c B hD hX hc F 𝓕
    (fun m => Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc m)) n

variable
  (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
  (hιc : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)

include B hD hX hc hpres hιc in
/-- **The object-level surjectivity input of [Stacks, Tag 09YQ] in degree zero, at the levels of
[Stacks, Tag 0EYL].** Let `(X_i)` be an inverse system of schemes over a nonempty directed index
with affine transition morphisms, all objects of a big étale site `B`, let `X` be the vertex of a
limit cone, let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i` in
the sense of [Stacks, Tag 0EZL], and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be a compatible family exhibiting
`𝓕 = colim_i f_i^{-1}F_i`. Then every section of `𝓕` over the image in the raised small affine
étale site of `X` of an object `Y` of a level `n` is the image, under the leg at some level `m`
below `n`, of a section of `F_m` over the transition image of `Y`.

This is the hypothesis `hsurjObj` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` at the étale
system. No identity law on the system is assumed; the module docstring says why the chain does not
need one. -/
theorem exists_levelSection_eq_of_pullbackPresentation (n : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C n)
    (z : ToType (((AffineEtaleModel.modelRestrict B c.pt hX).obj
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj.obj
        (op ((toLimitSmall D c B hD hX hc n).obj Y)))) :
    ∃ (m : (sys D c B hD hX hc).I) (a : m ⟶ n)
      (s : ToType (((levelCocycleSystem D c B hD hX hc F).obj m).obj.obj
        (op (((sys D c B hD hX hc).u a).obj Y)))),
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj.map
          (eqToHom (congrArg op (Functor.congr_obj
            (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((levelPullbackLeg D c B hD hX hc F 𝓕 ι m).app
          (op (((sys D c B hD hX hc).u a).obj Y)) s) = z :=
  Stacks.WeakSites.ColimitSiteCohomology.exists_level_section_eq_of_cocycleIsColimitPresentation
    (levelCocycleSystem D c B hD hX hc F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (AffineEtaleModel.precoverage B c.pt hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) _ _
    (isColimitPresentation_levelCocycleSystem D c B hD hX hc F 𝓕 ι hpres hιc) n Y z

include B hD hX hc hpres hιc in
/-- **The object-level separatedness input of [Stacks, Tag 09YQ] in degree zero, at the levels of
[Stacks, Tag 0EYL].** In the situation of
`exists_levelSection_eq_of_pullbackPresentation`, two sections of `F_m` over the transition image
of an object of a level, which have the same image under the leg, are carried to the same section
by the transition along some further arrow.

This is the hypothesis `hsep` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` at the étale
system. -/
theorem exists_levelCocycleMap_eq_of_pullbackPresentation (n : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C n) (m : (sys D c B hD hX hc).I) (a : m ⟶ n)
    (s s' : ToType (((levelCocycleSystem D c B hD hX hc F).obj m).obj.obj
      (op (((sys D c B hD hX hc).u a).obj Y))))
    (hs : (levelPullbackLeg D c B hD hX hc F 𝓕 ι m).app
        (op (((sys D c B hD hX hc).u a).obj Y)) s =
      (levelPullbackLeg D c B hD hX hc F 𝓕 ι m).app
        (op (((sys D c B hD hX hc).u a).obj Y)) s') :
    ∃ (p : (sys D c B hD hX hc).I) (b : p ⟶ m),
      ((levelCocycleSystem D c B hD hX hc F).map b).app
          (op (((sys D c B hD hX hc).u a).obj Y)) s =
        ((levelCocycleSystem D c B hD hX hc F).map b).app
          (op (((sys D c B hD hX hc).u a).obj Y)) s' :=
  Stacks.WeakSites.ColimitSiteCohomology.exists_cocycleMap_eq_of_cocycleIsColimitPresentation
    (levelCocycleSystem D c B hD hX hc F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (AffineEtaleModel.precoverage B c.pt hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) _ _
    (isColimitPresentation_levelCocycleSystem D c B hD hX hc F 𝓕 ι hpres hιc) n Y m a s s' hs

end Stacks.EtaleCohomology.AffineLimitCohomology

end
