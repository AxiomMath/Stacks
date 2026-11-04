module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitObjectSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology

/-!
# The second geometric hypothesis of Stacks 09YQ, over the quasi-compact opens of the stages

`Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` reduces the
degree-zero gluing condition `hsub` of
`SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`
to ONE surjectivity statement, `hqc`: for a quasi-compact open `V` of a stage `X_i` and a section
of the colimit sheaf `𝓕` over its preimage `f_i^{-1}V` in the limit, there is a stage `X_j` above
`X_i` and a section of `F_j` over the pullback of `V` whose image under
`Stacks.EtaleCohomology.opensSectionsLeg` is that section. This file discharges `hqc` and hence
`hsub`.

The input is
`Stacks.EtaleCohomology.AffineLimitCohomology.exists_objectSectionsLeg_eq`, the degree-zero
statement of [Stacks, Tag 09YQ] over an *étale object* of a stage whose structure morphism is a
monomorphism. A quasi-compact open of a stage is such an object by
`Stacks.EtaleCohomology.opensEtaleObj`; what remains is the identification of its base changes
with the preimage opens, and the index bookkeeping, both of which are carried out here. No new
mathematics enters: the one-hypercover step, its three level-side inputs and the surjectivity it
yields are all proved.

## Main results

* `Stacks.EtaleCohomology.opensSectionsLeg_apply_eq_of_iso` — **the leg on sections over an open
  subscheme, read through isomorphisms.** For `k : T ⟶ S`, an open `W` of `S` and an object `Zn`
  of the small étale site of `S` identified with the object `W` is there, the leg
  `Stacks.EtaleCohomology.opensSectionsLeg` over `W` is the transpose
  `Stacks.EtaleCohomology.etaleTransposeSection` of `ι` over `Zn`, transported along any
  morphisms into the base change of `Zn` whose composites agree. The coherence is free: both
  composites land in `(smallEtaleBaseChange k).obj Zn`, whose structure morphism is a
  monomorphism, so `Stacks.EtaleCohomology.etale_hom_ext_of_mono` identifies them.
* `Stacks.EtaleCohomology.AffineLimitCohomology.toLimitBaseChangeOpensIso` and
  `transitionBaseChangeOpensIso` — **the base change of the object of an open of a stage is the
  object of the preimage open**, at the limit and at a lower stage.
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_opensSectionsLeg_eq_of_level` — the
  surjectivity over a quasi-compact open of a stage, indexed by the levels of [Stacks, Tag 0EYL].
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_opensSectionsLeg_eq_of_isCompact` —
  **`hqc`**, the same statement indexed by `Iᵒᵖ`.
* `Stacks.EtaleCohomology.AffineLimitCohomology.sectionsDifference_of_levelSectionsColimit` —
  **`hsub` for the colimit sheaf of [Stacks, Tag 09YQ]**, and
  `sectionsDifference_of_pullbackPresentation`, the same at a colimit presentation.
* `Stacks.EtaleCohomology.opensToEtaleTopIso` and
  `opensSectionsLeg_top_eq_etaleSectionsRestriction` — the object of the open `⊤` is the whole
  scheme as an object of its own small étale site, and the leg on sections over `⊤` is the leg on
  **global** sections.
* `AffineLimitCohomology.exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit`
  — **the surjectivity half of the degree-zero statement `H0` on global sections**: every global
  section of the colimit sheaf comes from a stage.

## How the two identifications go

Both isomorphisms are one composition of existing comparisons. The object of an open `V'` of a
scheme `S` of the big étale site is `Stacks.EtaleCohomology.opensEtaleObj`, and its image in
Mathlib's small étale site is the object that open is there, on the nose
(`toEtaleSite_opensEtaleObj`). Base change in the size-bounded site of [Stacks, Tag 021B]
commutes with the embedding by
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`, and the base change of the object of an
open is the object of its preimage by
`Stacks.EtaleCohomology.opensToEtaleBaseChangeIso`. Composing the two gives the base change of
the object of `V'` as the object of the preimage of `V'`, at the limit along the projection of the
cone and at a lower stage along the transition.

## The index bookkeeping, and why it is not an identity

The levels of [Stacks, Tag 0EYL] are indexed by `(sys …).I`, which
`Stacks.EtaleCohomology.affineEtaleSiteColimit` equips with an *equivalence* to `Iᵒᵖ` rather than
an equality — the site system is `@[no_expose]`, so `levelIndex i` does not reduce to `i`. Going
from an index `i : Iᵒᵖ` to a level therefore produces the level
`indexEquiv.inverse.obj i` together with an isomorphism `levelIndex (indexEquiv.inverse.obj i) ≅ i`
in `Iᵒᵖ`, and the open of the stage the argument runs over is the pullback of `V` along it. This
costs nothing — `Stacks.EtaleCohomology.conePi_preimage_map_preimage` says the preimage in the
limit is unchanged, and `QuasiCompact.isCompact_preimage` keeps the open quasi-compact, the
transitions being affine — but it is a genuine transport and not an identity.

## What is assumed

Beyond the standing hypotheses of [Stacks, Tag 09YQ] — a nonempty directed index, affine
transition morphisms, all stages and the limit objects of a big étale site, a limit cone — the
statements here assume exactly that each stage is quasi-separated
(`[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`), which is the hypothesis of the tag itself, and
nothing else. Quasi-compactness of the object the one-hypercover is taken over comes from the
open, not from the stage; the `Mono` obligation of the one-hypercover comparison is discharged by
`Stacks.EtaleCohomology.mono_hom_opensEtaleObj`, an open immersion being a monomorphism; and
`IsAffineHom (c.π.app _)`, which `exists_oneHypercoverOf_datum` asks for as an instance, is
supplied inside from `hc` by
`Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection`. No identity law on the
system of [Stacks, Tag 0EZL] is used or available.

## What the degree-zero statement owed, and where the rest of it is

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_iff` splits the
hypothesis `H0` into two clauses on global sections: the surjectivity of the legs, which is
`exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit` above, and the **separatedness** —
a global section of `F_i` whose leg vanishes is killed by a transition
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleSectionsTransition` to some further stage.

The second clause is **not** proved here, and it is not the same kind of bookkeeping as the first.
The separatedness half of the one-hypercover step
(`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, second
conjunct, named by `DatumIsColimit`) concludes only that the two sections *agree on the objects
`W₀ k` of the covering datum* after a transition to a later level, whereas the sheaf condition
which turns such an agreement into an equality of sections over the whole base change — the field
`isLevelDatum` of `Stacks.EtaleCohomology.QcSeparatedColimit.OneHypercoverDatum` — can only consume
the other order, *transition and then restrict*.

**Both are proved**, in two modules downstream of this one.
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap_app_apply`
(`Colimits/SmallEtaleLevelTransitionPinning.lean`) is the pinning lemma for the transition — the
counterpart for `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap` of what
`levelPullbackLeg_app_apply` is for the leg — and it interchanges the two orders; it is the
naturality of `levelDirTransition` in the object of the stage's étale site, which
`levelCocycleMap_app` factors the level transition through.
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_of_isLimit`
(`Colimits/SmallEtaleColimitGlobalSeparated.lean`) is `H0` itself: it supplies the first clause
from this file and the second from that interchange together with `isLevelDatum`, at the open `⊤`
of a stage, and it carries no hypothesis beyond [Stacks, Tag 09YQ]'s own.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v u

namespace Stacks.EtaleCohomology

/-- **Restricting a section along an isomorphism of a site and then along its inverse returns the
section**, for a presheaf of abelian groups.

`CategoryTheory.PresheafOfCategories.map_op_hom_map_op_inv` is the statement for a presheaf of
*sets* whose values live in the morphism universe of the site; neither the coefficients nor the
universes are those of an abelian sheaf on the small étale site of a scheme, whose values are one
universe above the morphisms. Stated over a variable category because, at the concrete presheaf
and the concrete isomorphism, `simp` does not close it: the section it is applied to is given in
the `Stacks.EtaleCohomology.OpensAcyclicity.opensSections` spelling of the group of sections,
which is only definitionally the presheaf's value, and the rewrite does not fire through it. -/
theorem presheafMap_op_hom_inv_apply {A : Type*} [Category* A] (P : Aᵒᵖ ⥤ AddCommGrpCat.{w})
    {X Y : A} (e : X ≅ Y) (x : ToType (P.obj (op X))) :
    P.map e.hom.op (P.map e.inv.op x) = x := by
  simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
    P.map_id, ConcreteCategory.id_apply]

/-! ### The leg on sections over an open, read through isomorphisms -/

section Bridge

variable {T S : Scheme.{u}} (k : T ⟶ S)
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **The leg of an inverse image on sections over an open subscheme, compared with its transpose
over an étale object identified with that open.** Let `k : T ⟶ S` be a morphism of schemes,
`ι : k^{-1}G ⟶ 𝒢` a map of abelian sheaves on Mathlib's small étale sites, `W` an open subscheme
of `S` and `βn` an identification of an object `Zn` of the small étale site of `S` with the object
of `W` there. Let `βX`, `δ` and `ε` be morphisms with `βX ≫ δ = ε`, where `βX` goes out of the
object of `k^{-1}W` in the small étale site of `T`, and let `y` be a section of `𝒢` whose
restriction along `δ` is the transpose
`Stacks.EtaleCohomology.etaleTransposeSection` of `ι` at `Zn` applied to `t`, restricted along
`γ`. Then `Stacks.EtaleCohomology.opensSectionsLeg` over `W`, applied to `t` read over `W`
through `βn`, is `y` restricted along `ε`.

**The coherence is free.** `opensSectionsLeg` is the transpose over the object of `W` followed by
the identification `Stacks.EtaleCohomology.opensToEtaleBaseChangeIso` of `k^{-1}W` with a base
change (`opensSectionsLeg_eq_etaleTransposeSection`), and the transpose is natural in the object
(`etaleTransposeSection_naturality`); so both sides are the transpose at `Zn` restricted along a
morphism `k^{-1}W ⟶ (smallEtaleBaseChange k).obj Zn`, and any two such morphisms agree by
`Stacks.EtaleCohomology.etale_hom_ext_of_mono`, the structure morphism of the target being a
monomorphism — which is the hypothesis `hmono`, and holds whenever `Zn` has monomorphic structure
morphism, monomorphisms being stable under base change. -/
theorem opensSectionsLeg_apply_eq_of_iso
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    (W : S.Opens) {Zn : S.Etale} (βn : Zn ≅ (opensToEtale S).obj W)
    {ZX A : T.Etale} (γ : ZX ⟶ (smallEtaleBaseChange k).obj Zn)
    (hmono : Mono ((smallEtaleBaseChange k).obj Zn).hom)
    (βX : (opensToEtale T).obj (k ⁻¹ᵁ W) ⟶ ZX) (δ : ZX ⟶ A)
    (ε : (opensToEtale T).obj (k ⁻¹ᵁ W) ⟶ A) (hε : βX ≫ δ = ε)
    (t : ToType (G.obj.obj (op Zn))) (y : ToType (𝒢.obj.obj (op A)))
    (hy : 𝒢.obj.map γ.op (etaleTransposeSection.{u + 1, u} k ι Zn t) =
      𝒢.obj.map δ.op y) :
    opensSectionsLeg k ι W (G.obj.map βn.inv.op t) = 𝒢.obj.map ε.op y := by
  have heq : (opensToEtaleBaseChangeIso k W).hom ≫ (smallEtaleBaseChange k).map βn.inv
      = βX ≫ γ := etale_hom_ext_of_mono hmono _ _
  have e1 := ConcreteCategory.congr_hom
    (opensSectionsLeg_eq_etaleTransposeSection k ι W) (G.obj.map βn.inv.op t)
  have e2 := ConcreteCategory.congr_hom
    (etaleTransposeSection_naturality.{u + 1, u} k ι βn.inv) t
  simp only [ConcreteCategory.comp_apply] at e1 e2
  refine e1.trans ?_
  refine (congrArg (𝒢.obj.map (opensToEtaleBaseChangeIso k W).hom.op) e2).trans ?_
  have h3 : 𝒢.obj.map (opensToEtaleBaseChangeIso k W).hom.op
        (𝒢.obj.map ((smallEtaleBaseChange k).map βn.inv).op
          (etaleTransposeSection.{u + 1, u} k ι Zn t)) =
      𝒢.obj.map βX.op (𝒢.obj.map γ.op (etaleTransposeSection.{u + 1, u} k ι Zn t)) := by
    simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp, ← op_comp, heq]
  refine h3.trans ((congrArg (𝒢.obj.map βX.op) hy).trans ?_)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hε]

end Bridge

/-! ### The leg on sections over the whole scheme -/

section Top

variable (S : Scheme.{u})

/-- **The object of the open subscheme `⊤` is the whole scheme as an object of its own small étale
site.** Both are terminal objects — `AlgebraicGeometry.isTerminal_opensToEtale_top` and
`Stacks.EtaleCohomology.etaleMkIdIsTerminal` — so the identification is
`CategoryTheory.Limits.IsTerminal.uniqueUpToIso` and carries no information. -/
def opensToEtaleTopIso : (opensToEtale S).obj ⊤ ≅ Scheme.Etale.mk (𝟙 S) :=
  (AlgebraicGeometry.isTerminal_opensToEtale_top S).uniqueUpToIso (etaleMkIdIsTerminal S)

variable {T : Scheme.{u}} (k : T ⟶ S)

/-- The structure morphism of the base change of the terminal object of the small étale site of
`S` is a monomorphism, that of the terminal object being the identity and monomorphisms being
stable under base change. This is the hypothesis `hmono` of
`Stacks.EtaleCohomology.opensSectionsLeg_apply_eq_of_iso` at the terminal object, the counterpart
of `Stacks.EtaleCohomology.mono_hom_smallEtaleBaseChange_opensToEtale` for an open. -/
theorem mono_hom_smallEtaleBaseChange_etaleMkId :
    Mono ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 S))).hom :=
  MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms Scheme.{u})
    (IsPullback.of_hasPullback (Scheme.Etale.mk (𝟙 S)).hom k)
    (show Mono (𝟙 S) from inferInstance)

variable {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {𝒢 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **The leg of an inverse image on sections over the open `⊤` is its leg on global sections.**
For `k : T ⟶ S` and `ι : k^{-1}G ⟶ 𝒢`, the composite
`Stacks.EtaleCohomology.etaleSectionsRestriction` followed by `ι` over the terminal object — which
is `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection` of
[Stacks, Tag 09YQ] in degree zero — is `Stacks.EtaleCohomology.opensSectionsLeg` over `⊤`, read
through the identifications `opensToEtaleTopIso` of the object of `⊤` with the terminal object at
both ends.

This is `Stacks.EtaleCohomology.opensSectionsLeg_apply_eq_of_iso` at the terminal object, whose
hypothesis `hy` is
`Stacks.EtaleCohomology.etaleSectionsRestriction_comp_eq`: the leg on global sections *is* the
transpose over the terminal object followed by restriction along the unique morphism from the
terminal object upstairs. Every coherence is again free, the base change of the terminal object
having monomorphic structure morphism
(`mono_hom_smallEtaleBaseChange_etaleMkId`), and the three morphisms into terminal objects that
appear are identified by terminality alone. -/
theorem opensSectionsLeg_top_eq_etaleSectionsRestriction
    (ι : (etaleAbelianInverseImage.{u, u + 1} k).obj G ⟶ 𝒢)
    (t : ToType (G.obj.obj (op (Scheme.Etale.mk (𝟙 S))))) :
    opensSectionsLeg k ι ⊤ (G.obj.map (opensToEtaleTopIso S).hom.op t) =
      𝒢.obj.map (opensToEtaleTopIso T).hom.op
        (ι.hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (etaleSectionsRestriction.{u, u + 1} k G t)) := by
  have hsr := ConcreteCategory.congr_hom (etaleSectionsRestriction_comp_eq k ι) t
  simp only [ConcreteCategory.comp_apply] at hsr
  have hδθ : (etaleMkIdIsTerminal T).from
        ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 S))) ≫
      (isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).from (Scheme.Etale.mk (𝟙 T)) =
      𝟙 ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 S))) :=
    (isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).hom_ext _ _
  refine opensSectionsLeg_apply_eq_of_iso k ι ⊤ (opensToEtaleTopIso S).symm
    (𝟙 ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 S))))
    (mono_hom_smallEtaleBaseChange_etaleMkId S k)
    ((isTerminalSmallEtaleBaseChangeEtaleMkId.{u} k).from _)
    ((etaleMkIdIsTerminal T).from _) _
    ((etaleMkIdIsTerminal T).hom_ext _ _) t _ ?_
  refine Eq.trans ?_ (congrArg (𝒢.obj.map ((etaleMkIdIsTerminal T).from
    ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 S)))).op) hsr).symm
  simp only [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp, ← op_comp, hδθ]

end Top

namespace AffineLimitCohomology

open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex toLimitBaseChangeEtaleObj
  transitionBaseChangeEtaleObj toLimitBigHom transitionBigHom transitionScheme)
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi transportLeg)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The base changes of the object of an open of a stage -/

/-- **The base change to the limit of the object of an open `V'` of a stage is the object of the
preimage of `V'` in the limit.** Base change in the size-bounded small étale site of
[Stacks, Tag 021B] commutes with the embedding into Mathlib's small étale site by
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`, and the base change of the object of an
open subscheme is the object of its preimage by
`Stacks.EtaleCohomology.opensToEtaleBaseChangeIso`; the object of `V'` embeds as the object `V'`
is in Mathlib's site on the nose (`Stacks.EtaleCohomology.toEtaleSite_opensEtaleObj`), so this is
the composition of the two. -/
def toLimitBaseChangeOpensIso {i : (sys D c B hD hX hc).I}
    (V' : (D.obj (levelIndex D c B hD hX hc i)).Opens) :
    (SmallEtale.toEtaleSite B c.pt hX).obj
        (toLimitBaseChangeEtaleObj D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i)) (hD _) V')) ≅
      (opensToEtale c.pt).obj (conePi c (levelIndex D c B hD hX hc i) ⁻¹ᵁ V') :=
  (SmallEtale.toEtaleSiteBaseChangeIso B (toLimitBigHom D c B hD hX hc i)).app
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i)) (hD _) V') ≪≫
    (opensToEtaleBaseChangeIso (conePi c (levelIndex D c B hD hX hc i)) V').symm

/-- **The base change along a transition of the object of an open `V'` of a stage is the object of
the preimage of `V'` at the lower stage.** The stage counterpart of
`toLimitBaseChangeOpensIso`, with the projection of the cone replaced by the transition morphism;
the two factors are the same two comparisons. -/
def transitionBaseChangeOpensIso {i : (sys D c B hD hX hc).I}
    (V' : (D.obj (levelIndex D c B hD hX hc i)).Opens)
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    (SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i)) (hD _) V') a) ≅
      (opensToEtale (D.obj (levelIndex D c B hD hX hc n))).obj
        (transitionScheme D c B hD hX hc a ⁻¹ᵁ V') :=
  (SmallEtale.toEtaleSiteBaseChangeIso B (transitionBigHom D c B hD hX hc a)).app
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i)) (hD _) V') ≪≫
    (opensToEtaleBaseChangeIso (transitionScheme D c B hD hX hc a) V').symm

/-! ### The surjectivity over a quasi-compact open of a stage -/

section Descent

variable (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
  (ιe : ∀ i : Iᵒᵖ,
    (Stacks.EtaleCohomology.etaleAbelianInverseImage.{max u v, max u v + 1}
      (conePi c i)).obj (F.obj i) ⟶ 𝓕)

/-- **[Stacks, Tag 09YQ] in degree zero over a quasi-compact open of a stage, indexed by the
levels of [Stacks, Tag 0EYL]: every section of the colimit sheaf over the preimage of the open
comes from a stage.** Let `(X_i)` be an inverse system of schemes over a nonempty directed index
with affine transition morphisms, all objects of a big étale site `B`, let `X` be the vertex of a
limit cone, let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i` in
the sense of [Stacks, Tag 0EZL] and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be legs whose level cocycle data
is presented on the limit (`EtaleLevelSectionsColimit`). Let `V'` be a **quasi-compact** open of a
quasi-separated stage `X_{i₀}`. Then every section of `𝓕` over `f_{i₀}^{-1}V'` is the image under
`Stacks.EtaleCohomology.opensSectionsLeg` of a section of some `F_n` over the pullback of `V'` to
`X_n`.

This is `exists_objectSectionsLeg_eq` at the étale object
`Stacks.EtaleCohomology.opensEtaleObj` of `V'`, whose structure morphism is a monomorphism and
whose underlying scheme is quasi-compact and quasi-separated, with its two base changes identified
with the preimage opens by `toLimitBaseChangeOpensIso` and `transitionBaseChangeOpensIso` and the
two maps on sections compared by
`Stacks.EtaleCohomology.opensSectionsLeg_apply_eq_of_iso`. Nothing is added: the one-hypercover
datum is produced by
`Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum` from the
quasi-compactness and quasi-separatedness of the open alone, the affineness of the projection of
the cone coming from `hc`. -/
theorem exists_opensSectionsLeg_eq_of_level
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (i₀ : (sys D c B hD hX hc).I)
    [QuasiSeparatedSpace (D.obj (levelIndex D c B hD hX hc i₀))]
    (V' : (D.obj (levelIndex D c B hD hX hc i₀)).Opens)
    (hV' : IsCompact (V' : Set (D.obj (levelIndex D c B hD hX hc i₀))))
    (τ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)
      (conePi c (levelIndex D c B hD hX hc i₀) ⁻¹ᵁ V'))) :
    ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
      (σ : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict
          (D.obj (levelIndex D c B hD hX hc n))).obj
          (F.obj (levelIndex D c B hD hX hc n)))
        (transitionScheme D c B hD hX hc a ⁻¹ᵁ V'))),
      opensSectionsLeg (conePi c (levelIndex D c B hD hX hc n))
          (ιe (levelIndex D c B hD hX hc n))
          (transitionScheme D c B hD hX hc a ⁻¹ᵁ V') σ =
        OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)
          (conePi_preimage_map_preimage c
            ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) V').le τ := by
  have : IsAffineHom (c.π.app (levelIndex D c B hD hX hc i₀)) :=
    Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection D c hc _
  have := compactSpace_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V' hV'
  have := quasiSeparatedSpace_opensEtaleObj B
    (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V'
  obtain ⟨E⟩ := Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum
    D c B hD hX hc i₀ (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V')
  obtain ⟨n, a, t, hts⟩ := exists_objectSectionsLeg_eq D c B hD hX hc F 𝓕 ιe h
    (mono_hom_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V') E
    (𝓕.obj.map (toLimitBaseChangeOpensIso D c B hD hX hc V').hom.op τ)
  refine ⟨n, a, (F.obj (levelIndex D c B hD hX hc n)).obj.map
    (transitionBaseChangeOpensIso D c B hD hX hc V' a).inv.op t, ?_⟩
  have hε : ((opensToEtale c.pt).map (homOfLE (conePi_preimage_map_preimage c
          ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) V').le) ≫
        (toLimitBaseChangeOpensIso D c B hD hX hc V').inv) ≫
      (toLimitBaseChangeOpensIso D c B hD hX hc V').hom =
      (opensToEtale c.pt).map (homOfLE (conePi_preimage_map_preimage c
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) V').le) := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact opensSectionsLeg_apply_eq_of_iso (conePi c (levelIndex D c B hD hX hc n))
    (ιe (levelIndex D c B hD hX hc n))
    (transitionScheme D c B hD hX hc a ⁻¹ᵁ V')
    (transitionBaseChangeOpensIso D c B hD hX hc V' a)
    (toLimitBaseChangeEtaleObjIso D c B hD hX hc
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V') a).hom
    (mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj D c B hD hX hc
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V')
      (mono_hom_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) V') a)
    _ (toLimitBaseChangeOpensIso D c B hD hX hc V').hom _ hε t τ hts

/-- **The surjectivity hypothesis `hqc` of
`Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` for the colimit sheaf
of [Stacks, Tag 09YQ].** `exists_opensSectionsLeg_eq_of_level` reindexed from the levels of
[Stacks, Tag 0EYL] to `Iᵒᵖ`. -/
theorem exists_opensSectionsLeg_eq_of_isCompact [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (i : Iᵒᵖ) (V : (D.obj i).Opens) (hV : IsCompact (V : Set (D.obj i)))
    (τ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) (conePi c i ⁻¹ᵁ V))) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F.obj j)) (D.map a ⁻¹ᵁ V))),
      opensSectionsLeg (conePi c j) (ιe j) (D.map a ⁻¹ᵁ V) σ =
        OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)
          (conePi_preimage_map_preimage c a V).le τ := by
  set i₀ := (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i
  set hi : levelIndex D c B hD hX hc i₀ ⟶ i :=
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
  obtain ⟨n, a, σ₀, hσ₀⟩ := exists_opensSectionsLeg_eq_of_level D c B hD hX hc F 𝓕 ιe h i₀
    (D.map hi ⁻¹ᵁ V) (QuasiCompact.isCompact_preimage (f := D.map hi) _ V.2 hV)
    (OpensAcyclicity.opensSectionsRestrict
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) (conePi_preimage_map_preimage c hi V).le τ)
  have hWeq : (D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a ≫ hi) ⁻¹ᵁ V
      : (D.obj (levelIndex D c B hD hX hc n)).Opens) =
      transitionScheme D c B hD hX hc a ⁻¹ᵁ (D.map hi ⁻¹ᵁ V) := by
    rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_preimage]
  refine ⟨levelIndex D c B hD hX hc n,
    (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a ≫ hi,
    OpensAcyclicity.opensSectionsRestrict _ hWeq.le σ₀, ?_⟩
  rw [← opensSectionsLeg_restrict (conePi c (levelIndex D c B hD hX hc n))
      (ιe (levelIndex D c B hD hX hc n)) hWeq.le σ₀, hσ₀,
    OpensAcyclicity.opensSectionsRestrict_restrict,
    OpensAcyclicity.opensSectionsRestrict_restrict]

/-- **The second geometric hypothesis `hsub` of [Stacks, Tag 09YQ] for the colimit sheaf.** Let
`(X_i)` be an inverse system of schemes over a nonempty directed index with affine transition
morphisms, all objects of a big étale site `B` and all quasi-separated, let `X` be the vertex of a
limit cone, quasi-separated, let `F` be a system of abelian sheaves on Mathlib's small étale sites
of the `X_i` in the sense of [Stacks, Tag 0EZL] with every `F_i` **injective**, and let
`ι_i : f_i^{-1}F_i ⟶ 𝓕` be legs whose level cocycle data is presented on the limit. Then for every
quasi-compact open `U` and affine open `V` of `X`, every section of `𝓕` over `U ⊓ V` is the
difference of a section over `U` and a section over `V`.

This is `Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` with its
hypothesis `hqc` supplied by `exists_opensSectionsLeg_eq_of_isCompact`, and nothing else. -/
theorem sectionsDifference_of_levelSectionsColimit
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [QuasiSeparatedSpace c.pt]
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (hF : ∀ i : Iᵒᵖ, Injective (F.obj i))
    (U V : (c.pt).Opens) (hU : IsCompact (U : Set c.pt)) (hV : IsAffineOpen V) :
    OpensAcyclicity.SectionsDifference
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) U V :=
  Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg.{v, u}
    hc 𝓕 F.obj hF ιe
    (fun i W hW τ =>
      exists_opensSectionsLeg_eq_of_isCompact D c B hD hX hc F 𝓕 ιe h i W hW τ) U V hU hV

/-! ### The surjectivity half of the degree-zero statement, on global sections -/

/-- **[Stacks, Tag 09YQ] in degree zero on global sections, the surjectivity half: every global
section of the colimit sheaf comes from a stage.** Let `(X_i)` be an inverse system of schemes
over a nonempty directed index with affine transition morphisms, all objects of a big étale site
`B` and all quasi-compact and quasi-separated, let `X` be the vertex of a limit cone, let `F` be a
system of abelian sheaves on Mathlib's small étale sites of the `X_i` in the sense of
[Stacks, Tag 0EZL] and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be legs whose level cocycle data is presented
on the limit. Then every section of `𝓕` over the terminal object of the small étale site of `X` is
the image of a section of some `F_i` over the terminal object of the small étale site of `X_i`
under the pullback map on global sections followed by `ι_i`.

That composite is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection`, so this is the
first of the two clauses
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_iff` splits the
degree-zero hypothesis `H0` of
`SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`
into. The second clause — a global section at a stage killed by its leg is killed by a transition
— is **not** proved here but in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitGlobalSeparated.lean`,
which assembles the two into `H0`; see the implementation notes.

The proof is `exists_opensSectionsLeg_eq_of_isCompact` at the open `⊤` of any stage, which is
quasi-compact exactly because the stage is, with the leg on sections over `⊤` identified with the
leg on global sections by `opensSectionsLeg_top_eq_etaleSectionsRestriction`. Nothing further
about the presentation is used. -/
theorem exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (y : ToType (𝓕.obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))))) :
    ∃ (i : Iᵒᵖ) (s : ToType ((F.obj i).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i)))))),
      (ιe i).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
        (etaleSectionsRestriction.{max u v, max u v + 1} (conePi c i) (F.obj i) s) = y := by
  obtain ⟨j, a, σ, hσ⟩ := exists_opensSectionsLeg_eq_of_isCompact D c B hD hX hc F 𝓕 ιe h
    (op (Classical.arbitrary I)) ⊤ isCompact_univ
    (𝓕.obj.map (opensToEtaleTopIso c.pt).hom.op y)
  have hcollapse : ∀ (U : (c.pt).Opens) (hU : U ≤ U)
      (z : ToType (OpensAcyclicity.opensSections
        ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) U)),
      OpensAcyclicity.opensSectionsRestrict
        ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) hU z = z := fun U hU z => by
    rw [OpensAcyclicity.opensSectionsRestrict_self]
    rfl
  have hσ' : opensSectionsLeg (conePi c j) (ιe j) (D.map a ⁻¹ᵁ (⊤ : (D.obj _).Opens)) σ =
      𝓕.obj.map (opensToEtaleTopIso c.pt).hom.op y := hσ.trans (hcollapse _ _ _)
  refine ⟨j, (F.obj j).obj.map (opensToEtaleTopIso (D.obj j)).inv.op σ, ?_⟩
  have hkey := (opensSectionsLeg_top_eq_etaleSectionsRestriction _ (conePi c j) (ιe j)
    ((F.obj j).obj.map (opensToEtaleTopIso (D.obj j)).inv.op σ)).symm.trans
    ((congrArg (opensSectionsLeg (conePi c j) (ιe j) (⊤ : (D.obj j).Opens))
      (presheafMap_op_hom_inv_apply (F.obj j).obj (opensToEtaleTopIso (D.obj j)) σ)).trans hσ')
  have hinv : ∀ w : ToType (𝓕.obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))),
      𝓕.obj.map (opensToEtaleTopIso c.pt).inv.op
        (𝓕.obj.map (opensToEtaleTopIso c.pt).hom.op w) = w :=
    fun w => presheafMap_op_hom_inv_apply 𝓕.obj (opensToEtaleTopIso c.pt).symm w
  exact (hinv _).symm.trans
    ((congrArg (𝓕.obj.map (opensToEtaleTopIso c.pt).inv.op) hkey).trans (hinv y))

/-! ### The two hypotheses at a colimit presentation -/

include B hD hX hc in
/-- `exists_opensSectionsLeg_eq_of_isCompact` with its hypothesis supplied by
`levelSectionsColimit_of_pullbackPresentation`, so that the telescope is that of
`QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation`:
a colimit presentation of `𝓕` as `colim_i f_i^{-1}F_i` and the compatibility of the legs with the
transitions, the two halves
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_iff` splits the
presentation predicate of [Stacks, Tag 09YQ] into. -/
theorem exists_opensSectionsLeg_eq_of_pullbackPresentation
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F
      (transportLeg F 𝓕 ιe))
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫
          transportLeg F 𝓕 ιe i = transportLeg F 𝓕 ιe j)
    (i : Iᵒᵖ) (V : (D.obj i).Opens) (hV : IsCompact (V : Set (D.obj i)))
    (τ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) (conePi c i ⁻¹ᵁ V))) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i) (σ : ToType (OpensAcyclicity.opensSections
      ((MayerVietoris.mayerVietorisRestrict (D.obj j)).obj (F.obj j)) (D.map a ⁻¹ᵁ V))),
      opensSectionsLeg (conePi c j) (ιe j) (D.map a ⁻¹ᵁ V) σ =
        OpensAcyclicity.opensSectionsRestrict
          ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)
          (conePi_preimage_map_preimage c a V).le τ :=
  exists_opensSectionsLeg_eq_of_isCompact D c B hD hX hc F 𝓕 ιe
    (levelSectionsColimit_of_pullbackPresentation D c B hD hX hc F 𝓕
      (transportLeg F 𝓕 ιe) hpres hι) i V hV τ

include B hD hX hc in
/-- **`hsub` for [Stacks, Tag 09YQ] at a colimit presentation.**
`sectionsDifference_of_levelSectionsColimit` with its hypothesis supplied by
`levelSectionsColimit_of_pullbackPresentation`; the telescope is that of
`QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation`,
extended only by the quasi-separatedness of the stages, which is a hypothesis of
[Stacks, Tag 09YQ] itself. -/
theorem sectionsDifference_of_pullbackPresentation
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [QuasiSeparatedSpace c.pt]
    (hF : ∀ i : Iᵒᵖ, Injective (F.obj i))
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F
      (transportLeg F 𝓕 ιe))
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫
          transportLeg F 𝓕 ιe i = transportLeg F 𝓕 ιe j)
    (U V : (c.pt).Opens) (hU : IsCompact (U : Set c.pt)) (hV : IsAffineOpen V) :
    OpensAcyclicity.SectionsDifference
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) U V :=
  sectionsDifference_of_levelSectionsColimit D c B hD hX hc F 𝓕 ιe
    (levelSectionsColimit_of_pullbackPresentation D c B hD hX hc F 𝓕
      (transportLeg F 𝓕 ιe) hpres hι) hF U V hU hV

end Descent

end AffineLimitCohomology

end Stacks.EtaleCohomology

end
