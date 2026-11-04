module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraUnitCounitFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal

/-!
# The first assertion of Stacks 08AI for an affine morphism to an affine scheme

Let `f : Y ⟶ schemeSpace V` be an affine morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`, whose target is the algebraic space represented by an object
`V` of the site with **affine** underlying scheme, and let `𝒜 = f_*𝒪_Y`.  The first assertion of
Stacks 08AI — direct image is an equivalence from the quasi-coherent `𝒪_Y`-modules onto the
quasi-coherent `𝒜`-modules — is proved here for that `f`:
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_affineSchemeTarget`.

`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_schemeTarget_of_presentations` already
reduced the assertion, for an affine morphism with representable target, to two hypotheses: that
every quasi-coherent `𝒜`-module and every quasi-coherent `𝒪_Y`-module admits a
`SheafOfModules.Presentation`, that is, is the cokernel of a map of free modules *globally* and
not merely on a covering.  This file discharges both, and that is where affineness of `V` enters.

## Main results

* `AlgebraicGeometry.Space.hasGlobalPresentation_of_over_isTerminal`: **on the small étale site
  of a presheaf, a global presentation on the slice at a terminal object is a global
  presentation.**  The converse direction is `Stacks.SheafOfModules.hasGlobalPresentation_over`.
* `AlgebraicGeometry.Space.isTerminal_isoChart`: a presheaf isomorphic to a representable one has
  a terminal object in its small étale site, namely the isomorphism itself regarded as a chart.
* `AlgebraicGeometry.Space.nonempty_presentation_directImageAlgebra_of_isAffine` and
  `AlgebraicGeometry.Space.nonempty_presentation_of_isAffineHom_of_isAffine`: the two hypotheses
  of `...affineDirectImageEquivalence_of_schemeTarget_of_presentations`, discharged.
* `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_affineSchemeTarget`: **the first
  sentence of Stacks 08AI for an affine morphism whose target is represented by an affine
  scheme**, with no hypothesis beyond those.

## Implementation notes

### Why the target is a representable space with affine underlying scheme

Two separate restrictions are in force.

*The target is representable* because the only colimit input this tree has for direct image along
an affine morphism of algebraic spaces is
`AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`, which asks for it;
preservation of a colimit is not a local property of the base, so no chartwise glueing removes
that hypothesis.

*The underlying scheme of the target is affine* because the two discharged hypotheses are **false
without it**, not because a proof is missing.  A quasi-coherent module on a non-affine base need
not be globally a cokernel of free modules: on the projective line over a field, `𝒪(-1)` has no
global sections at all, so it is not even a quotient of a free module, while it is quasi-coherent
and is its own direct image along the identity.  So this is the largest case the shape of
`...affineDirectImageEquivalence_of_schemeTarget_of_presentations` can cover, and it is exactly
the case the chartwise reduction
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_over_affineCharts` consumes: that
reduction tests the unit and the counit on the slice at one **affine** étale chart of the target
at a time, and an étale chart of an algebraic space is representable by construction.

`AlgebraicGeometry.Space.isTerminal_isoChart` and
`AlgebraicGeometry.Space.hasGlobalPresentation_of_over_isTerminal` are between them the bridge
from `AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra` to a
`SheafOfModules.Presentation`.

### The two discharges run over different categories

The `𝒜`-module hypothesis and the `𝒪_Y`-module hypothesis are over different sites and different
sheaves of rings, so they are discharged by different routes, sharing only the descent along a
terminal object.

Over `𝒜`, on the small étale site of `schemeSpace V`, the terminal object is the identity chart
`AlgebraicGeometry.Space.idChart` and the global presentation on the slice at it is
`AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra`, which is
stated for an arbitrary affine chart and needs nothing beyond affineness of `f`.

Over `𝒪_Y` the site is the small étale site of `Y`, which is not given as representable; what
makes it so is that `Y` is affine over an affine scheme, so
`AlgebraicGeometry.Space.exists_representing_over_of_isAffineHom` — relative Tag 03JH at
Mathlib's `AlgebraicGeometry.IsAffineHom` — represents it by an object `W` of the site whose
projection to `V` is an affine morphism of schemes, hence with `W` affine by
`AlgebraicGeometry.isAffine_of_isAffineHom`.  The representing isomorphism is only an
isomorphism, not an equality, so the terminal object of the small étale site of `Y` is the
isomorphism read as a chart rather than an identity chart; that is the one place
`AlgebraicGeometry.Space.isTerminal_isoChart` is needed in the generality in which it is stated.
The global presentation on the slice there is Stacks 03DX for the small étale ringed site,
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine`.

### The descent along a terminal object

`AlgebraicGeometry.Space.hasGlobalPresentation_of_over_isTerminal` is the transport
`Stacks.SheafOfModules.hasGlobalPresentation_map` along the pushforward of modules under the
inverse of `CategoryTheory.Over.equivalenceOfIsTerminal`, which is an equivalence of sites — a
dense subsite in both directions by
`CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget` — carrying the sheaf of rings
`R.over T` back to `R` and the restricted module back to the module, both on the nose; so the
structure map of the transport is the identity and no comparison isomorphism has to be built.
The transport is `Stacks.SheafOfModules.reindexEquivalence`, which is also where the colimit
preservation that moves the presentation comes from: its functor is a left adjoint.  The
statement is for the small étale site of a presheaf
rather than for an arbitrary site only because the universes then agree without a `max`: the
objects of the site and of its slices both lie in `Type (u + 1)`, which is what
`...hasGlobalPresentation_map` asks of the two sites it compares.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart given by an isomorphism with a representable presheaf -/

section IsoChart

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}

/-- **An isomorphism from a representable presheaf, read as an object of the small étale site.**
An isomorphism of presheaves is an étale chart by
`AlgebraicGeometry.Space.presheaf_etale_of_iso`, so an isomorphism `yoneda.obj T ≅ F` is an
étale chart of `F` with underlying object `T`. -/
def isoChart (e : yoneda.obj T ≅ F) : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk e.hom, presheaf_etale_of_iso B S hS e⟩

/-- The object of the big fppf site underlying `AlgebraicGeometry.Space.isoChart` is the
representing object. -/
theorem toOver_obj_isoChart (e : yoneda.obj T ≅ F) :
    (SmallEtale.toOver B S hS F).obj (isoChart B S hS e) = T := rfl

/-- **A presheaf isomorphic to a representable one has a terminal object in its small étale
site**, namely the isomorphism read as a chart.

This is `AlgebraicGeometry.Space.isTerminal_idChart` with the identity replaced by an
isomorphism: a chart `V.hom : yoneda.obj V.left ⟶ F` factors through `e` in exactly one way,
because `e` is invertible and `yoneda` is fully faithful, so the factorization is `yoneda` of a
unique morphism `V.left ⟶ T` of the site. -/
def isTerminal_isoChart (e : yoneda.obj T ≅ F) : IsTerminal (isoChart B S hS e) := by
  have hmap (V : SmallEtale B S hS F) (g : V.obj.left ⟶ T) :
      yoneda.map g ≫ (isoChart B S hS e).obj.hom = V.obj.hom ↔
        g = yonedaEquiv (V.obj.hom ≫ e.inv) := by
    have hyy : yoneda.map (yonedaEquiv (V.obj.hom ≫ e.inv)) = V.obj.hom ≫ e.inv :=
      yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
    rw [show (isoChart B S hS e).obj.hom = e.hom from rfl]
    exact ⟨fun h => by
      rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id, yonedaEquiv_yoneda_map],
      fun h => by rw [h, hyy, Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  refine IsTerminal.ofUniqueHom
    (fun V => ObjectProperty.homMk
      (CostructuredArrow.homMk (yonedaEquiv (V.obj.hom ≫ e.inv)) ((hmap V _).2 rfl)))
    fun V m => ?_
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  exact (hmap V m.hom.left).1 (CostructuredArrow.w m.hom)

end IsoChart

/-! ### A global presentation on the slice at a terminal object -/

/-- **A global presentation on the slice at a terminal object is a global presentation.**  For an
arbitrary sheaf of rings `R` on the small étale site of a presheaf `F` and a terminal object `T`
of that site, a sheaf of `R`-modules whose restriction to the slice at `T` has a global
presentation has one itself.

The slice at a terminal object is the site again — the forgetful functor is a dense subsite in
both directions, `CategoryTheory.GrothendieckTopology.isDenseSubsite_overForget` — and the
equivalence carries `R.over T` to `R` and `M.over T` to `M` on the nose, so the cokernel diagram
travels by `Stacks.SheafOfModules.hasGlobalPresentation_map` with identities for both structure
maps.  The converse direction, which assumes nothing of the object, is
`Stacks.SheafOfModules.hasGlobalPresentation_over`. -/
theorem hasGlobalPresentation_of_over_isTerminal
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    {T : SmallEtale B S hS F} (hT : IsTerminal T) (M : SheafOfModules.{u} R)
    (h : (M.over T).HasGlobalPresentation) : M.HasGlobalPresentation := by
  have _hds' : ((Over.equivalenceOfIsTerminal hT).symm).inverse.IsDenseSubsite
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F) :=
    GrothendieckTopology.isDenseSubsite_overForget (SmallEtale.topology B S hS F) hT
  have _hc : ((Over.equivalenceOfIsTerminal hT).symm).inverse.IsContinuous
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F) :=
    inferInstanceAs ((Over.forget T).IsContinuous
      ((SmallEtale.topology B S hS F).over T) (SmallEtale.topology B S hS F))
  let E : SmallEtale B S hS F ≌ Over T := (Over.equivalenceOfIsTerminal hT).symm
  let φ : R ⟶ Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS F) E (R.over T) :=
    𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS F) E (R.over T))
  let F₀ := SheafOfModules.pushforward.{u} φ
  let FF := SheafOfModules.pushforward.{u + 1} φ
  have hFadj : FF.IsLeftAdjoint :=
    (Stacks.SheafOfModules.reindexEquivalence.{u, u + 1}
      (J' := SmallEtale.topology B S hS F) E (R.over T)).isLeftAdjoint_functor
  have hFzero : FF.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have step : (F₀.obj (M.over T)).HasGlobalPresentation :=
    Stacks.SheafOfModules.hasGlobalPresentation_map (F₀ := F₀) (F := FF) _
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ
        (SheafOfModules.unit (R.over T)))
      (Stacks.SheafOfModules.pushforwardUliftIso.{u + 1, u, u, u, u + 1} φ (M.over T)) h
  have key : F₀.obj (M.over T) ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) fun _ _ _ => by ext; rfl)
  exact SheafOfModules.HasGlobalPresentation.of_iso key step

/-! ### The two presentation hypotheses, discharged -/

variable {Y : AlgebraicSpaces B S hS}

/-- A module whose restriction to the slice at a terminal object has a global presentation admits
a `SheafOfModules.Presentation`. -/
private theorem nonempty_presentation_of_over_isTerminal
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (R : Sheaf (SmallEtale.topology B S hS F) RingCat.{u})
    {T : SmallEtale B S hS F} (hT : IsTerminal T) (M : SheafOfModules.{u} R)
    (h : (M.over T).HasGlobalPresentation) : Nonempty M.Presentation :=
  (hasGlobalPresentation_of_over_isTerminal B S hS R hT M h).nonempty_presentation_of_isTerminal hT

/-- **A quasi-coherent `𝒜`-module on a representable space with affine underlying scheme admits a
`SheafOfModules.Presentation`**, for `𝒜 = f_*𝒪_Y` along an affine morphism
`f : Y ⟶ schemeSpace V`.

`AlgebraicGeometry.Space.hasGlobalPresentation_over_affine_chart_directImageAlgebra` presents the
module on the slice at any affine étale chart of the target; the identity chart of
`schemeSpace V` is such a chart when the underlying scheme of `V` is affine, and it is terminal
by `AlgebraicGeometry.Space.isTerminal_idChart`, so
`AlgebraicGeometry.Space.hasGlobalPresentation_of_over_isTerminal` makes the presentation global
and `SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_isTerminal` shrinks its index
types to the universe of the sections. -/
theorem nonempty_presentation_directImageAlgebra_of_isAffine (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) : Nonempty G.Presentation :=
  nonempty_presentation_of_over_isTerminal B S hS _ (isTerminal_idChart B S hS V) G
    (hasGlobalPresentation_over_affine_chart_directImageAlgebra B S hS f hf G hG
      (idChart B S hS V) hV)

/-- **A quasi-coherent `𝒪_Y`-module admits a `SheafOfModules.Presentation` when `Y` is affine over
an affine scheme.**

An algebraic space affine over a representable presheaf is representable,
`AlgebraicGeometry.Space.exists_representing_over_of_isAffineHom`, by an object whose projection
to `V` is an affine morphism of schemes; so when the underlying scheme of `V` is affine that
object is affine too.  The representing isomorphism, read as a chart by
`AlgebraicGeometry.Space.isoChart`, is then a terminal object of the small étale site of `Y` with
affine underlying scheme, and the rest is Stacks 03DX for the small étale ringed site,
`AlgebraicGeometry.Space.hasGlobalPresentation_over_of_isAffine`, carried over the terminal
object. -/
theorem nonempty_presentation_of_isAffineHom_of_isAffine (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite) :
    Nonempty M.Presentation := by
  obtain ⟨W, e, P, -, hP⟩ :=
    exists_representing_over_of_isAffineHom B S hS Y.2 f.hom hf
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map P) := hP
  have hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map P)
  exact nonempty_presentation_of_over_isTerminal B S hS _ (isTerminal_isoChart B S hS e.symm) M
    (hasGlobalPresentation_over_of_isAffine B S hS Y M hM (isoChart B S hS e.symm) hW)

/-! ### The first sentence of Stacks 08AI for an affine target -/

/-- **The first assertion of Stacks 08AI for an affine morphism whose target is represented by an
affine scheme.**  For `f : Y ⟶ schemeSpace V` affine with the underlying scheme of `V` affine,
direct image `ℱ ↦ f_*ℱ` is an equivalence from the quasi-coherent `𝒪_Y`-modules onto the
quasi-coherent `𝒜`-modules, `𝒜 = f_*𝒪_Y`.  By
`AlgebraicGeometry.Space.quasicoherentDirectImage_comp_ι` the functor asserted to be an
equivalence is the direct image of Stacks 03D1 itself.

This is `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_schemeTarget_of_presentations`
with both of its presentation hypotheses discharged, by
`AlgebraicGeometry.Space.nonempty_presentation_directImageAlgebra_of_isAffine` and
`AlgebraicGeometry.Space.nonempty_presentation_of_isAffineHom_of_isAffine`.

The tag is stated for an affine morphism to an arbitrary algebraic space `X`; this is its case
`X = schemeSpace V` with `V` affine.  Representability of the target is what the only colimit
input available here,
`AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`, asks for, and
preservation of a colimit is not local on the base, so no chartwise glueing removes it.
Affineness of the underlying scheme is not a missing proof: the two discharged hypotheses are
false without it — on the projective line `𝒪(-1)` is quasi-coherent with no global sections, so
it is not a quotient of a free module — and it is precisely the case that the chartwise reduction
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_over_affineCharts` consumes.  The
general case is `AlgebraicGeometry.Space.isEquivalence_affineQuasicoherentDirectImage`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineDirectImageEquivalence.lean`), which reduces to the
present one chart by chart. -/
theorem affineDirectImageEquivalence_of_affineSchemeTarget (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom) :
    AffineDirectImageEquivalence B S hS f :=
  affineDirectImageEquivalence_of_schemeTarget_of_presentations B S hS V f hf
    (nonempty_presentation_directImageAlgebra_of_isAffine B S hS V hV f hf)
    (nonempty_presentation_of_isAffineHom_of_isAffine B S hS V hV f hf)

end AlgebraicGeometry.Space

end
