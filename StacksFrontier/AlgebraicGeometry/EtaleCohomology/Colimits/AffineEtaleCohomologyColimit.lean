module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineSiteFinalObject
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-! # Cohomology of the small affine etale site of a limit of affine schemes (Stacks 09YQ)

Let `I` be a directed set, let `(X_i)` be an inverse system of schemes over `I` with affine
transition morphisms and let `X = lim X_i`. Stacks 0EYL exhibits the small affine etale site of
`X` as the colimit of the small affine etale sites of the `X_i` in the sense of Stacks 09YL, and
Stacks 09YP computes the cohomology of a colimit of abelian sheaves on a colimit of sites. This
file joins the two, for `X_i` affine.

Stacks 09YP is stated for a `C` that is a *small category in the universe of the levels*, whereas
`AlgebraicGeometry.SmallAffineEtale B X hX` is a `Type (max u v + 1)` with morphisms in
`Type (max u v)`, only essentially small. The site is therefore raised through
`CategoryTheory.AsSmall`, which is an honest equivalence and definitionally a retract, and the
five inputs of Stacks 09YP — the cocone identity, the descent of objects, the descent of
morphisms, the eventual equality of morphisms and the description of the coverings — are
re-derived across that equivalence from Stacks 0EYL. The etale precoverage is transported, not
re-invented: `limitSitePrecoverage` is `Precoverage.comap AsSmall.down` of
`AlgebraicGeometry.SmallAffineEtale.precoverage`, so the topology of the conclusion is the etale
topology of `X`.

## Main results

* `mem_limitSitePrecoverage_iff`: the coverings of the raised site are exactly the images of the
  finite coverings of the levels — the description `hK` that Stacks 09YP asks for (Stacks 0EYL).
* `toLimitSmall_transition`, `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`,
  `toLimitSmall_hom_eventually_eq`: the remaining four inputs of Stacks 09YP for the raised site.
* `isTerminal_of_isIso_structMap` and `isIso_structMap_of_isTerminal`: an object of the small
  affine etale site of an affine `S` is terminal exactly when its structure morphism to `S` is an
  isomorphism.
* `levelTerminal`, `levelTerminal_isTerminal`: when the `X_i` are affine, `X_i` is itself an
  object of its own small affine etale site, and it is the terminal one.
* `transitionImage_isoLevelTerminal` and `toLimitImage_isoLimitTerminal`: **Stacks 09YQ, the
  identification of the objects the cohomology is taken over.** The transition images of `X_i`
  are the `X_j`, and its image in the site of the limit is `X`; so the cocone below is a cocone
  of the groups `H^p(X_j, F_j)` with vertex `H^p(X, F)`.
* `etaleCohomologyColimit_isColimit_of_affine`: **Stacks 09YQ in the affine case.**
* `colimitSheaf`, `colimitSheafLegs`, `isColimitPresentation_colimitSheaf`: **the colimit
  `colim_i f_i^{-1} F_i`, constructed** — the left Kan extension of the system along the functors
  to the site of the limit, its unit, and the universal property.
* `etaleCohomologyColimit_isColimit_of_affine_colimitSheaf`: Stacks 09YQ in the affine case with
  that colimit sheaf, its legs, its universal property and the cohomology cocone constructed
  rather than assumed.

## Implementation notes

The abelian sheaf system `F` is a hypothesis, as in Stacks 09YP and as in the source. The sheaf
`𝒢` presenting its colimit, the legs `ι` and the presentation `hcolim` are *not*: `colimitSheaf`
builds them from the five inputs this file supplies, and
`etaleCohomologyColimit_isColimit_of_affine_colimitSheaf` is the colimit statement with them
substituted. `etaleCohomologyColimit_isColimit_of_affine` keeps them as hypotheses, being the
form Stacks 09YP is stated in.

The two identifications of the cohomology-carrying objects are proved, not assumed. Both run off
the pullback squares that Stacks 0EYL supplies: `transition_isPullback` and `toLimit_isPullback`
make the structure morphism of the image of `X_i` the base change of the structure morphism of
`X_i / X_i`, which is an isomorphism, and the base change of an isomorphism is an isomorphism
(`CategoryTheory.IsPullback.isIso_snd_of_isIso`); terminality then follows from
`isTerminal_of_isIso_structMap`, whose proof uses that the small affine etale site is a full
subcategory of a full subcategory of a slice of a full subcategory of schemes, so that each of
those four steps reflects isomorphisms. `AlgebraicGeometry.Scheme.isAffine_of_isLimit` supplies
the affineness of `X` itself, so it is not a hypothesis.

The cohomology is the right-derived `sheafSections` of Stacks 09YP on the small affine etale site,
not the library's mainstream etale cohomology of a scheme; the comparison across Stacks 04HR
(`AlgebraicGeometry.SmallAffineEtale.inclusion_isDenseSubsite` together with Mathlib's
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`) is not performed in this file, and the clause
strings of the tags say so. It is performed downstream, for the site of the limit, by
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.rightDerivedSectionsRaisedFinalIsoEtaleCohomology`:
the raise `CategoryTheory.AsSmall` is itself a dense subsite inclusion
(`CategoryTheory.AsSmall.isDenseSubsite_up`), so the cohomology of `limitSite` is the cohomology of
the unraised small affine etale site, which Stacks 04HR turns into the etale cohomology of the
scheme.
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/AffineLimitEtaleCohomology.lean` carries
that out at both ends of the colimit of this file, the levels included.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

/-! ### Terminal objects of a small affine etale site -/

section Site

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the small affine etale site of `S`. -/
abbrev structMap (W : AlgebraicGeometry.SmallAffineEtale B S hS) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj W ⟶ S :=
  B.inclusion.map W.obj.obj.hom

/-- Morphisms of the small affine etale site are morphisms over `S`. -/
lemma toScheme_map_comp_structMap {W W' : AlgebraicGeometry.SmallAffineEtale B S hS}
    (t : W ⟶ W') :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map t ≫ structMap B S hS W' =
      structMap B S hS W := by
  let tOver := (AlgebraicGeometry.SmallEtale.inclusion B S hS).map
    ((AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).map t)
  have hmap : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map t =
      B.inclusion.map tOver.left := rfl
  rw [hmap, ← B.inclusion.map_comp]
  exact congrArg B.inclusion.map (Over.w tOver)

/-- The structure morphism of the final object `S / S` is the identity of `S`. -/
lemma structMap_final [IsAffine S] :
    structMap B S hS (AlgebraicGeometry.SmallAffineEtale.final B S hS) = 𝟙 S := by
  show B.inclusion.map (𝟙 (B.obj S hS)) = 𝟙 S
  exact B.inclusion.map_id _

/-- A morphism of the small affine etale site whose underlying morphism of schemes is an
isomorphism is itself an isomorphism: the site is a full subcategory of a full subcategory of a
slice of a full subcategory of schemes, and each of those four steps reflects isomorphisms. -/
lemma isIso_of_isIso_toScheme_map {W W' : AlgebraicGeometry.SmallAffineEtale B S hS}
    (t : W ⟶ W') (h : IsIso ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map t)) :
    IsIso t :=
  isIso_of_reflects_iso t ((AlgebraicGeometry.SmallAffineEtale.inclusion B S hS) ⋙
    (AlgebraicGeometry.SmallEtale.inclusion B S hS) ⋙ Over.forget (B.obj S hS) ⋙ B.inclusion)

/-- The structure morphism of the final object is an isomorphism. -/
lemma isIso_structMap_final [IsAffine S] :
    IsIso (structMap B S hS (AlgebraicGeometry.SmallAffineEtale.final B S hS)) := by
  rw [structMap_final]
  exact IsIso.id S

/-- **An object of the small affine etale site of an affine `S` whose structure morphism is an
isomorphism is terminal.** The canonical morphism to `S / S`, followed by the structure morphism
of `S / S`, is the structure morphism of the object; so when the latter is an isomorphism so is
that canonical morphism, and the object is isomorphic to the final one. -/
def isTerminal_of_isIso_structMap [IsAffine S]
    (W : AlgebraicGeometry.SmallAffineEtale B S hS) (h : IsIso (structMap B S hS W)) :
    IsTerminal W := by
  haveI := isIso_structMap_final B S hS
  haveI : IsIso ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map
        ((AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS).from W) ≫
      structMap B S hS (AlgebraicGeometry.SmallAffineEtale.final B S hS)) := by
    rw [toScheme_map_comp_structMap]
    exact h
  haveI := IsIso.of_isIso_comp_right ((AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).map
    ((AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS).from W))
    (structMap B S hS (AlgebraicGeometry.SmallAffineEtale.final B S hS))
  have := isIso_of_isIso_toScheme_map B S hS
    ((AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS).from W) this
  exact (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS).ofIso
    (asIso ((AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS).from W)).symm

/-- **The structure morphism of a terminal object of the small affine etale site of an affine `S`
is an isomorphism.** The converse of `isTerminal_of_isIso_structMap`. -/
lemma isIso_structMap_of_isTerminal [IsAffine S]
    (W : AlgebraicGeometry.SmallAffineEtale B S hS) (hW : IsTerminal W) :
    IsIso (structMap B S hS W) := by
  have := isIso_structMap_final B S hS
  rw [← toScheme_map_comp_structMap B S hS
    (hW.uniqueUpToIso (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B S hS)).hom]
  infer_instance

end Site

/-! ### Images of presieves -/

/-- The image of a presieve under a composite functor. -/
theorem presieve_map_comp {A : Type*} [Category* A] {E₁ : Type*} [Category* E₁]
    {E₂ : Type*} [Category* E₂] (F : A ⥤ E₁) (G : E₁ ⥤ E₂) {X : A} (S : Presieve X) :
    S.map (F ⋙ G) = (S.map F).map G := by
  refine le_antisymm ?_ ?_
  · rintro W f ⟨h⟩
    exact Presieve.map_map (Presieve.map_map h)
  · rintro W f ⟨⟨h⟩⟩
    exact Presieve.map_map h

/-- Pushing a presieve of `AsSmall A` down and back up returns it: `AsSmall.up` and
`AsSmall.down` are inverse to one another on the nose. -/
theorem presieve_map_down_up {A : Type*} [Category* A] {X : AsSmall.{w} A}
    (R : Presieve X) : (R.map AsSmall.down).map AsSmall.up = R := by
  refine le_antisymm ?_ ?_
  · rintro W f ⟨⟨h⟩⟩
    exact h
  · intro W f hf
    exact Presieve.map_map (Presieve.map_map hf)

/-- Terminality transports through `AsSmall.up`. -/
def isTerminal_asSmallUp {A : Type*} [Category* A] {Z : A} (h : IsTerminal Z) :
    IsTerminal ((AsSmall.up : A ⥤ AsSmall.{w} A).obj Z) :=
  IsTerminal.ofUniqueHom (fun W => AsSmall.up.map (h.from (AsSmall.down.obj W)))
    fun _ _ => ULift.ext (h.hom_ext _ _)

/-- Terminality transports back along an equivalence. -/
def isTerminal_of_functorObj {A : Type*} [Category* A] {E₁ : Type*} [Category* E₁] (e : A ≌ E₁)
    {Z : A} (h : IsTerminal (e.functor.obj Z)) : IsTerminal Z :=
  (h.isTerminalObj e.inverse).ofIso (e.unitIso.app Z).symm

/-! ### The small affine etale site of the limit, raised to the universe of the levels -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The small affine etale site of the limit `X = lim X_i`, with its morphism universe raised so
that it is a small category in the universe of the levels of the system of Stacks 0EYL. -/
abbrev limitSite := AsSmall.{max u v + 1} (AlgebraicGeometry.SmallAffineEtale B c.pt hX)

/-- The canonical system of Stacks 0EYL. -/
abbrev sys := (affineEtaleSiteColimit D c B hD hX hc).system

/-- The canonical functors from the levels to the raised site of the limit. -/
abbrev toLimitSmall (i : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C i ⥤ limitSite D c B hX :=
  (affineEtaleSiteColimit D c B hD hX hc).toLimit i ⋙ AsSmall.up

/-- The etale precoverage of the limit, read on the raised site. It is the etale precoverage of
`AlgebraicGeometry.SmallAffineEtale`, transported along the equivalence, not a new collection. -/
def limitSitePrecoverage : Precoverage (limitSite D c B hX) :=
  (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX).comap AsSmall.down

/-- **The cocone identity of Stacks 09YL**, on the raised site: the functors to the limit are
compatible with the transition functors of the system. -/
theorem toLimitSmall_transition {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    (sys D c B hD hX hc).u a ⋙ toLimitSmall D c B hD hX hc i =
      toLimitSmall D c B hD hX hc j :=
  (Functor.assoc _ _ _).symm.trans
    (congrArg (fun F => F ⋙ AsSmall.up)
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a))

/-- **Stacks 0EYL, objects**, on the raised site: every affine etale object over the limit
descends to a finite stage. -/
theorem toLimitSmall_obj_descends (Z : limitSite D c B hX) :
    ∃ (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i),
      (toLimitSmall D c B hD hX hc i).obj Y = Z := by
  obtain ⟨i, Y, h⟩ := affineEtaleSiteColimit_obj_descends D c B hD hX hc (AsSmall.down.obj Z)
  exact ⟨i, Y, ULift.ext h⟩

/-- **Stacks 0EYL, morphisms**, on the raised site: every morphism between objects descended from
one stage descends after increasing the stage. -/
theorem toLimitSmall_hom_descends
    (i : (sys D c B hD hX hc).I) (Y Z : (sys D c B hD hX hc).C i)
    (f : (toLimitSmall D c B hD hX hc i).obj Y ⟶ (toLimitSmall D c B hD hX hc i).obj Z) :
    ∃ (j : (sys D c B hD hX hc).I) (a : j ⟶ i)
      (g : ((sys D c B hD hX hc).u a).obj Y ⟶ ((sys D c B hD hX hc).u a).obj Z),
      (toLimitSmall D c B hD hX hc j).map g =
        eqToHom (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) Y) ≫ f ≫
          eqToHom (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) Z).symm := by
  obtain ⟨j, a, g, hg⟩ :=
    affineEtaleSiteColimit_hom_descends D c B hD hX hc i Y Z (ULift.down f)
  refine ⟨j, a, g, ULift.ext ?_⟩
  simp only [down_comp, eqToHom_down]
  exact hg

/-- **Stacks 0EYL, faithfulness**, on the raised site: two morphisms that agree over the limit
agree after increasing the stage. -/
theorem toLimitSmall_hom_eventually_eq
    (i : (sys D c B hD hX hc).I) (X Y : (sys D c B hD hX hc).C i) (g₁ g₂ : X ⟶ Y)
    (h : (toLimitSmall D c B hD hX hc i).map g₁ = (toLimitSmall D c B hD hX hc i).map g₂) :
    ∃ (j : (sys D c B hD hX hc).I) (a : j ⟶ i),
      ((sys D c B hD hX hc).u a).map g₁ = ((sys D c B hD hX hc).u a).map g₂ :=
  affineEtaleSiteColimit_hom_eventually_eq D c B hD hX hc i X Y g₁ g₂ (congrArg ULift.down h)

/-- Pushing a presieve of a level to the raised site and then down to the small affine etale site
of the limit is the same as pushing it straight down. -/
theorem map_toLimitSmall_down (i : (sys D c B hD hX hc).I)
    {Y : (sys D c B hD hX hc).C i} (S : Presieve Y) :
    (S.map (toLimitSmall D c B hD hX hc i)).map AsSmall.down =
      S.map ((affineEtaleSiteColimit D c B hD hX hc).toLimit i) :=
  (presieve_map_comp _ _ S).symm

/-- **Stacks 0EYL, coverings**, on the raised site: the etale coverings of the limit are exactly
the images of the finite coverings of the levels. This is the description `hK` of the coverings
that Stacks 09YP asks for, and it is what makes the topology of the conclusion the etale
topology. -/
theorem mem_limitSitePrecoverage_iff (Z : limitSite D c B hX) (R : Presieve Z) :
    R ∈ limitSitePrecoverage D c B hX Z ↔
      ∃ (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i)
        (h : (toLimitSmall D c B hD hX hc i).obj Y = Z) (S : Presieve Y),
        S ∈ ((sys D c B hD hX hc).J i).toPrecoverage Y ∧
          S ∈ Precoverage.finite ((sys D c B hD hX hc).C i) Y ∧
          R = h ▸ S.map (toLimitSmall D c B hD hX hc i) := by
  obtain ⟨Z⟩ := Z
  have hcomap :
      R ∈ limitSitePrecoverage D c B hX ⟨Z⟩ ↔
        R.map AsSmall.down ∈ AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX Z :=
    Iff.rfl
  refine hcomap.trans
    ((affineEtaleSiteColimit_mem_precoverage_iff D c B hD hX hc Z
      (R.map AsSmall.down)).trans ?_)
  constructor
  · rintro ⟨i, Y, h0, S, hS, hfin, heq⟩
    subst h0
    have heq' : R.map AsSmall.down =
        S.map ((affineEtaleSiteColimit D c B hD hX hc).toLimit i) := heq
    refine ⟨i, Y, rfl, S, hS, hfin, ?_⟩
    exact ((presieve_map_down_up R).symm.trans
      (congrArg (Presieve.map AsSmall.up) heq')).trans (presieve_map_comp _ _ S).symm
  · rintro ⟨i, Y, h, S, hS, hfin, heq⟩
    have h0 : ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y = Z :=
      congrArg ULift.down h
    subst h0
    have heq' : R = S.map (toLimitSmall D c B hD hX hc i) := heq
    refine ⟨i, Y, rfl, S, hS, hfin, ?_⟩
    rw [heq']
    exact map_toLimitSmall_down D c B hD hX hc i S

/-! ### The colimit of the inverse images, constructed

The sheaf `𝒢 = colim_i f_i^{-1} F_i` on the site of the limit, its legs and the universal
property, for a system `F` of abelian sheaves on the sites of the levels. Nothing here is a
hypothesis: the five inputs of Stacks 09YP that this file supplies are exactly what the
construction of Stacks 09YN needs.
-/

section ColimitSheaf

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
  (sys D c B hD hX hc))

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **The colimit `colim_i f_i^{-1} F_i`, constructed rather than assumed.** For a system `F` of
abelian sheaves on the small affine etale sites of the levels, the left Kan extension of the
system along the functors to the site of the limit; it is a sheaf by Stacks 09YN. -/
def colimitSheaf : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1} :=
  systemColimitSheaf.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc) F

open Stacks.WeakSites.ColimitSiteCohomology in
/-- The legs `F_j ⟶ f_j^{-1} 𝒢` of the colimit of `colimitSheaf`: the unit of the left Kan
extension, read at the level `j`. -/
def colimitSheafLegs (j : (sys D c B hD hX hc).I) :
    (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ (colimitSheaf D c B hD hX hc F).obj :=
  systemKanUnit.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) F j

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **`colimitSheaf` presents the colimit of the inverse images.** Its legs are compatible with
the transitions and every compatible family factors uniquely through them, a left Kan extension
having exactly that universal property. This is the datum `hcolim` of Stacks 09YP, proved. -/
theorem isColimitPresentation_colimitSheaf :
    IsColimitPresentation.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) F (colimitSheaf D c B hD hX hc F)
      (colimitSheafLegs D c B hD hX hc F) :=
  systemColimitSheaf_isColimitPresentation.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc) F

end ColimitSheaf

/-! ### The affine case: the schemes of the system are objects of their own sites -/

section Affine

variable [∀ i : Iᵒᵖ, IsAffine (D.obj i)]

/-- **`X_i` itself, as an object of its level site.** For an affine `X_i` the identity
`X_i → X_i` is an affine etale object over `X_i`, so `X_i` is an object of its own small affine
etale site; this is `AlgebraicGeometry.SmallAffineEtale.final` read at the level of the system
through the equivalence of Stacks 0EYL. It is here that the affine hypothesis on the `X_i` is
used. -/
def levelTerminal (i : (sys D c B hD hX hc).I) : (sys D c B hD hX hc).C i :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).inverse.obj
    (AlgebraicGeometry.SmallAffineEtale.final B
      (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
      (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i)))

/-- `levelTerminal i` is the terminal object of the level site: it is `X_i / X_i`, carried along
the equivalence of Stacks 0EYL, and an equivalence preserves terminal objects. -/
def levelTerminal_isTerminal (i : (sys D c B hD hX hc).I) :
    IsTerminal (levelTerminal D c B hD hX hc i) :=
  (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B
      (D.obj ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))
      (hD ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i))).isTerminalObj
    ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).inverse

/-- `X` itself, as an object of the raised site of the limit. The limit of a system of affine
schemes is affine (`AlgebraicGeometry.Scheme.isAffine_of_isLimit`), so this needs no hypothesis
beyond the affineness of the `X_i`. -/
def limitTerminal : limitSite D c B hX :=
  letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  AsSmall.up.obj (AlgebraicGeometry.SmallAffineEtale.final B c.pt hX)

/-- `X` is terminal in the raised site of the limit. -/
def limitTerminal_isTerminal : IsTerminal (limitTerminal D c B hX hc) :=
  letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  isTerminal_asSmallUp (AlgebraicGeometry.SmallAffineEtale.finalIsTerminal B c.pt hX)

/-- The structure morphism of a terminal object of a level is an isomorphism. -/
lemma isIso_structureMorphism_of_isTerminal
    (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i) (hY : IsTerminal Y) :
    IsIso (affineEtaleStructureMorphism D B hD
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i)
      (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y)) :=
  isIso_structMap_of_isTerminal B _ _ _
    (hY.isTerminalObj ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor)

/-- **The transition functors of the system carry the terminal object to the terminal object.**
By `transition_isPullback` the structure morphism of the transition image is the base change of
the structure morphism of `Y`, which is an isomorphism when `Y` is terminal; the base change of
an isomorphism is an isomorphism, and an object with invertible structure morphism is
terminal. -/
def transitionImage_isTerminal {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j) (hY : IsTerminal Y) :
    IsTerminal (((sys D c B hD hX hc).u a).obj Y) :=
  isTerminal_of_functorObj ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i)
    (isTerminal_of_isIso_structMap B _ _ _
      (((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isIso_snd_of_isIso
        (isIso_structureMorphism_of_isTerminal D c B hD hX hc j Y hY)))

/-- **The functors to the limit carry the terminal object to the terminal object.** Same argument
as `transitionImage_isTerminal`, run off `toLimit_isPullback`. -/
def toLimitImage_isTerminal (i : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C i) (hY : IsTerminal Y) :
    IsTerminal ((toLimitSmall D c B hD hX hc i).obj Y) :=
  letI : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  isTerminal_asSmallUp (isTerminal_of_isIso_structMap B c.pt hX _
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y).isIso_snd_of_isIso
      (isIso_structureMorphism_of_isTerminal D c B hD hX hc i Y hY)))

/-- **Stacks 09YQ, the diagram values.** The transition image of `X_i` at a level `j` below `i`
is `X_j`: the value of the cohomology diagram at `a : j ⟶ i` is the cohomology of `F_j` over the
terminal object of the site of `X_j`, that is over `X_j` itself. -/
@[stacks 09YQ "the affine case: the transition image of the terminal object `X_i` is the terminal \
object `X_j`, so the value of the cohomology diagram at `a : j ⟶ i` is the cohomology over `X_j`"]
def transitionImage_isoLevelTerminal {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    ((sys D c B hD hX hc).u a).obj (levelTerminal D c B hD hX hc i) ≅
      levelTerminal D c B hD hX hc j :=
  IsTerminal.uniqueUpToIso
    (transitionImage_isTerminal D c B hD hX hc a (levelTerminal D c B hD hX hc i)
      (levelTerminal_isTerminal D c B hD hX hc i))
    (levelTerminal_isTerminal D c B hD hX hc j)

/-- **Stacks 09YQ, the cocone vertex.** The image of `X_i` in the site of the limit is `X`: the
vertex of the cohomology cocone is the cohomology of `𝒢` over the terminal object of the site of
`X`, that is over `X` itself. -/
@[stacks 09YQ "the affine case: the image of the terminal object `X_i` in the site of the limit \
is the terminal object `X`, so the vertex of the cohomology cocone is the cohomology over `X`"]
def toLimitImage_isoLimitTerminal (i : (sys D c B hD hX hc).I) :
    (toLimitSmall D c B hD hX hc i).obj (levelTerminal D c B hD hX hc i) ≅
      limitTerminal D c B hX hc :=
  IsTerminal.uniqueUpToIso
    (toLimitImage_isTerminal D c B hD hX hc i (levelTerminal D c B hD hX hc i)
      (levelTerminal_isTerminal D c B hD hX hc i))
    (limitTerminal_isTerminal D c B hX hc)

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Stacks 09YQ, the affine case.** Let `I` be a directed set, let `(X_i)` be an inverse system
of *affine* schemes over `I` with affine transition morphisms, and let `X = lim X_i`. Let `F` be a
system of abelian sheaves on the small affine etale sites of the `X_i`, let `𝒢` on the small
affine etale site of `X` present the colimit `colim f_i^{-1} F_i`, and let `p` be a degree. Then
`H^p(X, 𝒢)` is the filtered colimit, over the arrows `a : j ⟶ i`, of the groups `H^p(X_j, F_j)`:
the canonical cocone is a colimit cocone.

The base object is `levelTerminal i`, which is `X_i` (`levelTerminal_isTerminal`); its image in
the site of the limit is `X` (`toLimitImage_isoLimitTerminal`) and its transition image at a
level `j` is `X_j` (`transitionImage_isoLevelTerminal`), so the vertex and the values of the
diagram are the cohomology groups of the schemes of the system.

This is Stacks 09YP, applied to the colimit of sites of Stacks 0EYL through
`mem_limitSitePrecoverage_iff` and the three descent clauses above. -/
@[stacks 09YQ "the affine case: the schemes `X_i` of the system are affine, so that `X_i` is \
itself an object of its own small affine etale site and is the terminal one; the sites are the \
small AFFINE etale sites and the cohomology of THIS statement is the right-derived \
`sheafSections` of Stacks 09YP on them. The comparison across Stacks 04HR that turns those \
groups into the library's mainstream etale cohomology of a scheme is \
`Stacks.EtaleCohomology.AffineLimitCohomology.limitCohomologyFunctorIsoEtaleCohomology` at the \
limit and `...levelTerminalCohomologyIsoEtaleCohomology` at a level", no_expose]
def etaleCohomologyColimit_isColimit_of_affine
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (i : (sys D c B hD hX hc).I) (p : ℕ)
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i
      (levelTerminal D c B hD hX hc i) p) :
    IsColimit E.cocone :=
  isColimitCohomologyCocone.{v, v, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc)
    F 𝒢 ι hcolim i (levelTerminal D c B hD hX hc i) p E

section ColimitSheafAffine

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
  (sys D c B hD hX hc)) (i : (sys D c B hD hX hc).I) (p : ℕ)

open Stacks.WeakSites.ColimitSiteCohomology in
/-- The canonical cohomology cocone at the constructed colimit sheaf, over `X_i`: the diagram of
the groups `H^p(X_j, F_j)` together with its cocone at `H^p(X, colim_i f_i^{-1} F_i)`. -/
def cohomologyCoconeOfColimitSheaf :
    CohomologyCocone.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) F (colimitSheaf D c B hD hX hc F)
      (colimitSheafLegs D c B hD hX hc F) i (levelTerminal D c B hD hX hc i) p :=
  cohomologyCocone.{v, v, max u v + 1} (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc) (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX) (mem_limitSitePrecoverage_iff D c B hD hX hc) F
    (colimitSheaf D c B hD hX hc F) (colimitSheafLegs D c B hD hX hc F)
    (isColimitPresentation_colimitSheaf D c B hD hX hc F) i
    (levelTerminal D c B hD hX hc i) p

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Stacks 09YQ in the affine case, with the colimit sheaf constructed.** Let `(X_i)` be an
inverse system of affine schemes with affine transitions, `X = lim X_i`, and let `F` be a system
of abelian sheaves on their small affine etale sites. Then

`H^p(X, colim_i f_i^{-1} F_i) = colim_i H^p(X_i, F_i)`.

This is `etaleCohomologyColimit_isColimit_of_affine` with the sheaf presenting the colimit, its
legs and its universal property no longer hypotheses but the constructions `colimitSheaf`,
`colimitSheafLegs` and `isColimitPresentation_colimitSheaf`. -/
@[stacks 09YQ "the affine case with the colimit sheaf CONSTRUCTED: the sheaf `𝒢` presenting \
`colim f_i^{-1} F_i` on the site of the limit, its legs and its universal property are the \
left Kan extension of the system and are no longer hypotheses. The system `F` itself is still \
given, and the cohomology of THIS statement is the right-derived `sheafSections` of Stacks 09YP \
on the small AFFINE etale sites; \
`AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine_etaleVertex` is the same \
colimit with its vertex the library's mainstream etale cohomology of the limit.",
  no_expose]
def etaleCohomologyColimit_isColimit_of_affine_colimitSheaf
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1} (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (limitSitePrecoverage D c B hX) F (colimitSheaf D c B hD hX hc F)
      (colimitSheafLegs D c B hD hX hc F) i (levelTerminal D c B hD hX hc i) p :=
      cohomologyCoconeOfColimitSheaf D c B hD hX hc F i p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_isColimit_of_affine D c B hD hX hc F (colimitSheaf D c B hD hX hc F)
    (colimitSheafLegs D c B hD hX hc F) (isColimitPresentation_colimitSheaf D c B hD hX hc F)
    i p E

end ColimitSheafAffine

end Affine

end Stacks.EtaleCohomology.AffineLimitCohomology

end
