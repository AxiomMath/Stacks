module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The two inverse images of abelian étale sheaves, reconciled over a limit cone

This library carries two inverse images of abelian sheaves on the small étale sites along a
morphism of schemes. `Stacks.EtaleCohomology.smallEtalePullbackAb` — equivalently
`Stacks.EtaleCohomology.systemPullback`, which `Stacks.EtaleCohomology.EtaleSheafSystem` types
its transition maps in — is the abstract left adjoint of the direct image.
`Stacks.EtaleCohomology.etaleAbelianInverseImage` is the same functor constructed as a left Kan
extension followed by sheafification, and it is the one `CategoryTheory.Sheaf.H`, and hence
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem`, is built from. They are
isomorphic and not equal, and that is the only thing separating the presentation hypothesis
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` of [Stacks, Tag 09YQ]
from `Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, the
hypothesis `h0EYN` of [Stacks, Tag 0DV2]: both are statements about abelian sheaves on
Mathlib's small étale sites at the coefficients `AddCommGrpCat.{u + 1}`, so no site crossing and
no change of coefficients is involved.

This file reconciles the two over a limit cone.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb` — the comparison of
  the two inverse images, for an arbitrary morphism of schemes: uniqueness of a left adjoint.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.transportLeg` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.untransportLeg` — a family of legs
  `f_i^{-1}F_i ⟶ H` read in the other vocabulary, in each direction.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePullbackCompPi` —
  `Stacks.EtaleCohomology.conePullbackComp` with its projections written through
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi` (see the implementation notes).
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneDirectImageLeg` — the counit
  `f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕` of [Stacks, Tag 0EYN], read as a leg out of the constructed inverse
  image, which is the vocabulary `IsColimitPresentation` and `PresentedSystem` ask for.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePullbackComp_inv_comp` — **the comparison
  of the two comparisons.** Along the factorisation `f_j = f_i ≫ f_{ji}` of a projection of the
  cone through a transition of the index, the inverse image is compared with the composite of the
  inverse images in two ways: `Stacks.EtaleCohomology.conePullbackComp` for the abstract inverse
  image and `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` for the
  constructed one. The two agree, once the two inverse images are compared at each of the three
  morphisms involved. `conePullbackComp_inv_app_comp` is the same statement at a sheaf.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.transportLeg_comp_iff` — factoring through
  the legs is the same condition in the two vocabularies.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.diagramMap_crossing_comp` — the two spellings
  of the diagram map `f_j^{-1}F_j ⟶ f_i^{-1}F_i` of a system agree.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_iff` — consequently a
  family of legs is compatible with the transitions of the system in one vocabulary exactly when
  its transport is in the other.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_coneDirectImageLeg` —
  **the counits of the projections are a compatible family for the system of direct images**, in
  the vocabulary `IsColimitPresentation` and `PresentedSystem` require. This is the cocone half of
  [Stacks, Tag 0EYN], proved as `Stacks.EtaleCohomology.coneDirectImageCounit_cocone`, crossed
  over; so at that system the whole remaining content of the presentation predicate is its
  universal property, which is [Stacks, Tag 0EYN]'s colimit half.

## Implementation notes

The content is `conePullbackComp_inv_comp`, and it is not a new coherence. Both comparisons are
induced by one and the same comparison of *direct* images — direct image is restriction along the
base-change functor, with no left adjoint and no sheafification in it, so the two developments
spell it with the same term, and `Stacks.EtaleCohomology.coneDirectImageCompAb` is that term —
and `CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker` is exactly the hexagon saying
that a comparison of two *systems* of left adjoints is compatible with composition. That lemma
was written for this shape of problem; this is its first consumer.

**The `conePi` rule, for the comparison and not the projection.**
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean` records
that `c.π.app i` must be written `conePi c i`, its source `((Functor.const Iᵒᵖ).obj c.pt).obj i`
being `c.pt` definitionally but not at the transparency typeclass inference uses. The same rule
applies to every construction whose type mentions `c.π.app i`, and in particular to
`Stacks.EtaleCohomology.conePullbackComp`: its source is
`systemPullback a ⋙ smallEtalePullbackAb (c.π.app i)`, whose target category is
`Sheaf (((Functor.const Iᵒᵖ).obj c.pt).smallEtaleTopology) _`, so a composite of one of its
components with a map written in the `c.pt` spelling is well-typed only up to unfolding. The
*statement* of such a composite elaborates, because elaboration unifies; `rw` does not, because
it must build a motive, and it reports that it did not find a pattern which the printed goal
appears to contain. `conePullbackCompPi` is `conePullbackComp` in the `conePi` spelling — its
body is `conePullbackComp c a` and nothing else changes — and with it every composite below lives
in one category.

**Reassociation.** `diagramMap_crossing_comp` rewrites inside a right-associated five-fold
composite, where a two-factor equation is not a subterm; `reassoc_of%` supplies the reassociated
form of each step, which is what makes the chase go through. For the same reason the epimorphism
cancelled in `isCompatibleFamily_iff` is named rather than left to unification, which there costs
more than the whole rest of the file.

**What is not here**, stated precisely, because the obvious reading of it is wrong. The colimit
half of [Stacks, Tag 0EYN] — that the counits exhibit `𝓕 = colim_i f_i^{-1}f_{i, *}𝓕` — IS proved
in this repository for abelian sheaves, as
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToEtaleSite`
(`Colimits/SmallEtaleLimitColimitMainstreamSite.lean`), which gives
`InverseSystemOfFiniteSites.RestrictionIsColimit'` on `(c.pt).smallEtaleTopology` at
`AddCommGrpCat`, for an arbitrary abelian sheaf on the limit's small étale site; its set-valued
companion `restrictionIsColimit_limitToSmallEtale`
(`Colimits/SmallEtaleLimitColimitSheaf.lean`) is the registered part (2) of that tag.

What is NOT here is the coherence that translates that `RestrictionIsColimit'` form into the
counit form, namely the compatibility of `Stacks.EtaleCohomology.coneDirectImageCompAb` with the
reindexings of `RestrictionIsColimit'`. That coherence, and not the colimit half, is the
hypothesis `h0EYN` of [Stacks, Tag 0DV2], and by
`isCompatibleFamily_coneDirectImageLeg` it is also what the presentation predicate of
[Stacks, Tag 09YQ] asks at the canonical concrete system — so discharging it once discharges both.
Note that 09YQ does not depend on that route: its presentation at an arbitrary system is proved
as `isColimitPresentation_levelCocycleSystem`
(`Colimits/SmallEtaleLevelCocyclePresentation.lean`).

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

/-! ### The comparison of the two inverse images -/

/-- **The comparison of the two inverse images of abelian étale sheaves** along a morphism of
schemes: `Stacks.EtaleCohomology.smallEtalePullbackAb`, the abstract left adjoint of the direct
image, and `Stacks.EtaleCohomology.etaleAbelianInverseImage`, its construction as a left Kan
extension followed by sheafification. It is uniqueness of a left adjoint. -/
def inverseImageIsoPullbackAb {X Y : Scheme.{u}} (f : Y ⟶ X)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}] :
    smallEtalePullbackAb f ≅ etaleAbelianInverseImage.{u, u + 1} f :=
  Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb f)
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f)

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- The comparison named in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean` is this
one, at a transition morphism. -/
theorem systemPullbackIsoInverseImage_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullbackIsoInverseImage D a = inverseImageIsoPullbackAb (D.map a) :=
  rfl

/-- The inverse of the comparison of two left adjoints is the comparison the other way. -/
private theorem leftAdjointUniq_inv_eq_hom {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    (Adjunction.leftAdjointUniq adj₁ adj₂).inv = (Adjunction.leftAdjointUniq adj₂ adj₁).hom :=
  NatTrans.ext (funext fun x => Adjunction.leftAdjointUniq_inv_app _ _ x)

/-- **The two comparisons of inverse images along the factorisation `f_j = f_i ≫ f_{ji}` of a
projection of the cone agree**, after the two inverse images are compared at each of the three
morphisms. Both are induced by the same comparison
`Stacks.EtaleCohomology.coneDirectImageCompAb` of direct images, so this is the hexagon
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker`. -/
theorem conePullbackComp_inv_comp (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] {i j : Iᵒᵖ} (a : i ⟶ j) :
    (conePullbackComp c a).inv ≫
        Functor.whiskerRight (inverseImageIsoPullbackAb (D.map a)).hom
            (smallEtalePullbackAb (conePi c i)) ≫
          Functor.whiskerLeft (etaleAbelianInverseImage.{u, u + 1} (D.map a))
            (inverseImageIsoPullbackAb (conePi c i)).hom =
      (inverseImageIsoPullbackAb (conePi c j)).hom ≫ (coneInverseImageComp a).hom := by
  have hhex := Adjunction.leftAdjointUniq_hom_comp_whisker
    (smallEtaleAdjunctionAb (D.map a))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))
    (smallEtaleAdjunctionAb (conePi c i))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i))
    (smallEtaleAdjunctionAb (conePi c j))
    (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a)).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i))).ofNatIsoRight
      (coneDirectImageCompAb c a))
    (coneDirectImageCompAb c a) rfl
  have h₁ : Adjunction.leftAdjointUniq
      (((smallEtaleAdjunctionAb (D.map a)).comp
          (smallEtaleAdjunctionAb (conePi c i))).ofNatIsoRight (coneDirectImageCompAb c a))
      (smallEtaleAdjunctionAb (conePi c j)) = conePullbackComp c a :=
    Adjunction.leftAdjointUniq_ofNatIsoRight_comp _ _ _ _
  have h₂ : Adjunction.leftAdjointUniq
      (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a)).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i))).ofNatIsoRight
        (coneDirectImageCompAb c a))
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c j)) =
      (coneInverseImageComp a).symm :=
    Adjunction.leftAdjointUniq_ofNatIsoRight_comp _ _ _ _
  have h₃ := Adjunction.leftAdjointUniq_trans
    (smallEtaleAdjunctionAb (conePi c j))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c j))
    (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a)).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i))).ofNatIsoRight
      (coneDirectImageCompAb c a))
  have hR : (inverseImageIsoPullbackAb (conePi c j)).hom ≫ (coneInverseImageComp a).hom =
      (Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb (conePi c j))
        (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a)).comp
            (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (conePi c i))).ofNatIsoRight
          (coneDirectImageCompAb c a))).hom := by
    rw [← h₃]
    exact congrArg (fun t => (inverseImageIsoPullbackAb (conePi c j)).hom ≫ t)
      ((congrArg Iso.inv h₂).symm.trans (leftAdjointUniq_inv_eq_hom _ _))
  rw [← h₁]
  refine Eq.trans (congrArg (· ≫ _) (leftAdjointUniq_inv_eq_hom _ _)) ?_
  rw [hR]
  exact hhex

/-- `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePullbackComp_inv_comp` at a sheaf. -/
theorem conePullbackComp_inv_app_comp (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] {i j : Iᵒᵖ} (a : i ⟶ j)
    (G : Sheaf (smallEtaleTopology (D.obj j)) AddCommGrpCat.{u + 1}) :
    (conePullbackComp c a).inv.app G ≫
        (smallEtalePullbackAb (conePi c i)).map
            ((inverseImageIsoPullbackAb (D.map a)).hom.app G) ≫
          (inverseImageIsoPullbackAb (conePi c i)).hom.app
            ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj G) =
      (inverseImageIsoPullbackAb (conePi c j)).hom.app G ≫
        (coneInverseImageComp a).hom.app G :=
  NatTrans.congr_app (conePullbackComp_inv_comp c a) G

/-- **`Stacks.EtaleCohomology.conePullbackComp` with its functors written through
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePi`.** The body is `conePullbackComp`
itself; what changes is the spelling of the projections, and with them of the categories the
comparison's components live in.

This is the `conePi` device of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean` applied
to the comparison rather than to the projection, and it is needed for the same reason. The source
of `conePullbackComp c a` is `systemPullback a ⋙ smallEtalePullbackAb (c.π.app i)`, whose target
category is `Sheaf (((Functor.const Iᵒᵖ).obj c.pt).smallEtaleTopology) _`; that is `c.pt`'s
category definitionally but not syntactically, so a composite of one of its components with a map
in the `c.pt` spelling is well-typed only up to unfolding, and `rw` — which must build a motive —
fails on it. With this spelling every composite below lives in one category. -/
def conePullbackCompPi (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullback D AddCommGrpCat.{u + 1} a ⋙ smallEtalePullbackAb (conePi c i) ≅
      smallEtalePullbackAb (conePi c j) :=
  conePullbackComp c a

/-- `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePullbackComp_inv_app_comp` in the
`conePi` spelling. -/
theorem conePullbackCompPi_inv_app_comp (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] {i j : Iᵒᵖ} (a : i ⟶ j)
    (G : Sheaf (smallEtaleTopology (D.obj j)) AddCommGrpCat.{u + 1}) :
    (conePullbackCompPi c a).inv.app G ≫
        (smallEtalePullbackAb (conePi c i)).map
            ((inverseImageIsoPullbackAb (D.map a)).hom.app G) ≫
          (inverseImageIsoPullbackAb (conePi c i)).hom.app
            ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj G) =
      (inverseImageIsoPullbackAb (conePi c j)).hom.app G ≫
        (coneInverseImageComp a).hom.app G :=
  conePullbackComp_inv_app_comp c a G

/-! ### Reading the legs of a presentation in either vocabulary -/

variable {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-- `Stacks.EtaleCohomology.systemTransitionMap` written through
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`: it is the
transition map of the system itself, read through the comparison of the two inverse images. -/
theorem systemTransitionMap_eq (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    systemTransitionMap F a =
      (inverseImageIsoPullbackAb (D.map a)).inv.app (F.obj j) ≫ F.map a :=
  rfl

/-- A family of maps out of the constructed inverse images, read as a family of maps out of the
abstract ones. -/
def transportLeg (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H)
    (i : Iᵒᵖ) : (smallEtalePullbackAb (conePi c i)).obj (F.obj i) ⟶ H :=
  (inverseImageIsoPullbackAb (conePi c i)).hom.app (F.obj i) ≫ τ i

/-- A family of maps out of the abstract inverse images, read as a family of maps out of the
constructed ones — the direction `PresentedSystem` needs. -/
def untransportLeg (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (conePi c i)).obj (F.obj i) ⟶ H) (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H :=
  (inverseImageIsoPullbackAb (conePi c i)).inv.app (F.obj i) ≫ τ i

omit [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] in
/-- The two readings are inverse to one another. -/
@[simp]
theorem transportLeg_untransportLeg (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (conePi c i)).obj (F.obj i) ⟶ H) (i : Iᵒᵖ) :
    transportLeg F H (untransportLeg F H τ) i = τ i := by
  rw [transportLeg, untransportLeg, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

omit [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] in
/-- **Factoring through the legs is the same condition in the two vocabularies.** -/
theorem transportLeg_comp_iff (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {𝒢 H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢)
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H)
    (χ : 𝒢 ⟶ H) (i : Iᵒᵖ) :
    ι i ≫ χ = τ i ↔ transportLeg F 𝒢 ι i ≫ χ = transportLeg F H τ i := by
  rw [transportLeg, transportLeg, Category.assoc]
  exact (cancel_epi ((inverseImageIsoPullbackAb (conePi c i)).hom.app (F.obj i))).symm

/-- **The diagram map `f_j^{-1}F_j ⟶ f_i^{-1}F_i` of a system in the two vocabularies**, with a
further map appended. On the left the diagram map is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` followed by the inverse
image of `Stacks.EtaleCohomology.systemTransitionMap`; on the right it is
`Stacks.EtaleCohomology.conePullbackComp` followed by the abstract inverse image of the
transition `F.map a` itself. The appended map is what makes the statement applicable inside a
right-associated composite.

The proof is `conePullbackComp_inv_app_comp`, the naturality of the comparison of the two inverse
images used twice, and the cancellation of that comparison against its own inverse. -/
theorem diagramMap_crossing_comp (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) {T : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (t : (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ T) :
    (inverseImageIsoPullbackAb (conePi c j)).hom.app (F.obj j) ≫
        (coneInverseImageComp a).hom.app (F.obj j) ≫
          (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a) ≫ t =
      (conePullbackCompPi c a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (conePi c i)).map (F.map a) ≫
          (inverseImageIsoPullbackAb (conePi c i)).hom.app (F.obj i) ≫ t := by
  have hid : (smallEtalePullbackAb (conePi c i)).map
          ((inverseImageIsoPullbackAb (D.map a)).hom.app (F.obj j)) ≫
        (smallEtalePullbackAb (conePi c i)).map
            ((inverseImageIsoPullbackAb (D.map a)).inv.app (F.obj j)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  rw [systemTransitionMap_eq, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% conePullbackCompPi_inv_app_comp c a (F.obj j),
    reassoc_of% ((inverseImageIsoPullbackAb (conePi c i)).hom.naturality
      ((inverseImageIsoPullbackAb (D.map a)).inv.app (F.obj j))).symm,
    reassoc_of% ((inverseImageIsoPullbackAb (conePi c i)).hom.naturality (F.map a)).symm,
    reassoc_of% hid]

/-- **The two compatibility conditions on a family of legs agree.** A family `τ` is compatible
with the transitions of the system in the vocabulary of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` exactly when its transport
is compatible in the vocabulary of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, whose
compatibility clause is the right-hand side here (written with `conePi` in place of the
definitionally equal `Cone.π.app`). -/
theorem isCompatibleFamily_iff (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H) :
    IsCompatibleFamily F H τ ↔
      ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
        (conePullbackCompPi c a).inv.app (F.obj j) ≫
            (smallEtalePullbackAb (conePi c i)).map (F.map a) ≫ transportLeg F H τ i =
          transportLeg F H τ j := by
  have key : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      ((conePullbackCompPi c a).inv.app (F.obj j) ≫
            (smallEtalePullbackAb (conePi c i)).map (F.map a) ≫ transportLeg F H τ i =
          transportLeg F H τ j) ↔
        ((coneInverseImageComp a).hom.app (F.obj j) ≫
            (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a) ≫
              τ i = τ j) := by
    intro i j a
    rw [transportLeg, transportLeg, ← diagramMap_crossing_comp F a (τ i)]
    exact cancel_epi ((inverseImageIsoPullbackAb (conePi c j)).hom.app (F.obj j))
  exact ⟨fun h _ _ a => (key a).mpr (h a), fun h _ _ a => (key a).mp (h a)⟩

/-! ### The system of direct images of [Stacks, Tag 0EYN] -/

/-- The counit `ι_i : f_i^{-1}f_{i, *}𝓕 ⟶ 𝓕` of [Stacks, Tag 0EYN], as a leg out of the
constructed inverse image — the vocabulary
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation` and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` ask for. -/
def coneDirectImageLeg (𝓕 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj
        ((directImageSystem D AddCommGrpCat.{u + 1} c 𝓕).obj i) ⟶ 𝓕 :=
  untransportLeg (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕
    (coneDirectImageCounit c 𝓕) i

omit [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}] in
/-- Read back in the abstract vocabulary, `coneDirectImageLeg` is the counit it was built from. -/
@[simp]
theorem transportLeg_coneDirectImageLeg
    (𝓕 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) (i : Iᵒᵖ) :
    transportLeg (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕 (coneDirectImageLeg 𝓕) i =
      coneDirectImageCounit c 𝓕 i :=
  transportLeg_untransportLeg _ _ _ i

/-- **The counits of the projections form a family compatible with the transitions of the system
of direct images**, in the vocabulary of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`. This is the cocone half
of [Stacks, Tag 0EYN], proved as
`Stacks.EtaleCohomology.coneDirectImageCounit_cocone`, read through the comparison of the two
inverse images.

Consequently the whole content of the presentation hypothesis `P` of `PresentedSystem` at this
system is its universal property, which is the colimit half of [Stacks, Tag 0EYN] — the
hypothesis `h0EYN` of [Stacks, Tag 0DV2]. -/
theorem isCompatibleFamily_coneDirectImageLeg
    (𝓕 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) :
    IsCompatibleFamily (directImageSystem D AddCommGrpCat.{u + 1} c 𝓕) 𝓕
      (coneDirectImageLeg 𝓕) := by
  rw [isCompatibleFamily_iff]
  intro i j a
  rw [transportLeg_coneDirectImageLeg, transportLeg_coneDirectImageLeg]
  exact coneDirectImageCounit_cocone c 𝓕 a

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
