module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ChangeOfBigSites
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfRepresentable

/-!
# Enlarging the big fppf site of an algebraic space

A big fppf site contained in a larger one of the same kind induces, after localizing at a
scheme `S` of the smaller site, an inverse-image functor on sheaves of sets. That functor
carries the sheaf represented by an object of the smaller site to the sheaf represented by the
same object of the larger one, and it carries algebraic spaces over `S` to algebraic spaces
over `S`.

## Main definitions

* `CategoryTheory.sheafifyYonedaIso` identifies the sheafification of the Yoneda embedding of a
  subcanonical site with the Yoneda embedding into sheaves.
* `CategoryTheory.pullbackYonedaIso` is the resulting comparison for the inverse image along a
  continuous functor: `h_U ↦ h_{i(U)}`, naturally in `U`.
* `CategoryTheory.coequalizerIsoOfNatIso` transports a coequalizer of two parallel arrows along
  such a comparison.

## Main results

* `AlgebraicGeometry.hasSheafify_bigFppfOver` — sheaves of sets on the big fppf site of `S`
  admit sheafification, with no hypothesis.
* `AlgebraicGeometry.inclusionOver_sheafPushforwardContinuous_isRightAdjoint` — the direct image
  along the localized inclusion of big fppf sites has a left adjoint on set-valued sheaves,
  which is the inverse image of the statement.
* `AlgebraicGeometry.isAlgebraicSpace_sheafPullback_of_descent` — that inverse image carries an
  algebraic space over `S` to an algebraic space over `S`.

## Implementation notes

The first assertion of Stacks 03FP is the general theorem for continuous functors of sites,
`sheafPullback_sheafify_yoneda_natIso`, applied to the localized inclusion; representable
sheaves are expressed as sheafified Yoneda presheaves, so that no choice of a subcanonical
structure enters the statement. The right-adjoint assertion supplies the inverse image on
`Type u`-valued sheaves, which Mathlib's sheaf-pullback construction provides once both
localized sites are essentially small.

The second assertion presents the algebraic space as the coequalizer of the kernel pair of an
étale atlas (Stacks 0262), transports that coequalizer along the comparison above, and
identifies the result with the quotient sheaf of the transported étale equivalence relation,
which is an algebraic space by Stacks 02WW. The quotient theorem is available in this library
only relative to effective descent along the covering sieves of the site at the monomorphisms
locally of finite type, so that hypothesis is carried here as an explicit argument.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

/-- For a subcanonical Grothendieck topology, sheafifying the Yoneda embedding of the site
gives the Yoneda embedding into sheaves: the counit of the sheafification adjunction is an
isomorphism at every representable sheaf. -/
@[sga "4 II 4.4.0" "partial"]
def sheafifyYonedaIso {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [J.Subcanonical] [HasWeakSheafify J (Type v₁)] :
    yoneda ⋙ presheafToSheaf J (Type v₁) ≅ J.yoneda :=
  NatIso.ofComponents (fun X =>
    asIso ((sheafificationAdjunction J (Type v₁)).counit.app (J.yoneda.obj X)))
    (fun f => (sheafificationAdjunction J (Type v₁)).counit.naturality (J.yoneda.map f))

/-- **Stacks 03FP, part (1), for an arbitrary morphism of sites.** The inverse image along a
continuous functor `i` between subcanonical sites carries the sheaf represented by `U` to the
sheaf represented by `i(U)`, naturally in `U`. -/
def pullbackYonedaIso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D]
    (i : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [i.IsContinuous J K] [J.Subcanonical] [K.Subcanonical]
    [HasWeakSheafify J (Type v₁)] [HasWeakSheafify K (Type v₁)]
    [(i.sheafPushforwardContinuous (Type v₁) J K).IsRightAdjoint] :
    J.yoneda ⋙ i.sheafPullback (Type v₁) J K ≅ i ⋙ K.yoneda :=
  Functor.isoWhiskerRight (sheafifyYonedaIso J).symm _ ≪≫
    (sheafPullback_sheafify_yoneda_natIso i J K).some ≪≫
    Functor.isoWhiskerLeft i (sheafifyYonedaIso K)

/-- Transport a coequalizer along a natural isomorphism. If `q : Y(U) ⟶ F` is the coequalizer
of `Y(s)` and `Y(t)`, if `q' : Z(U) ⟶ G` is the coequalizer of `Z(s)` and `Z(t)`, if
`e : Y ⋙ L ≅ Z`, and if `L` preserves the first coequalizer, then `L(F) ≅ G`. -/
def coequalizerIsoOfNatIso {C : Type u₁} [Category.{v₁} C] {A : Type*} {B : Type*}
    [Category A] [Category B] (Y : C ⥤ A) (Z : C ⥤ B) (L : A ⥤ B) (e : Y ⋙ L ≅ Z)
    {R U : C} (s t : R ⟶ U) {F : A} {G : B}
    (q : Y.obj U ⟶ F) (wq : Y.map s ≫ q = Y.map t ≫ q)
    (q' : Z.obj U ⟶ G) (wq' : Z.map s ≫ q' = Z.map t ≫ q')
    (hq : IsColimit (Cofork.ofπ q wq)) (hq' : IsColimit (Cofork.ofπ q' wq'))
    [PreservesColimit (parallelPair (Y.map s) (Y.map t)) L] :
    L.obj F ≅ G := by
  let c : Cofork (Z.map s) (Z.map t) := Cofork.ofπ ((e.app U).inv ≫ L.map q) (by
    have hs := e.inv.naturality s
    have ht := e.inv.naturality t
    dsimp at hs ht
    change Z.map s ≫ e.inv.app U ≫ L.map q = Z.map t ≫ e.inv.app U ≫ L.map q
    rw [← Category.assoc, hs, ← Category.assoc, ht]
    simp only [Category.assoc, ← L.map_comp, wq])
  have hc : IsColimit c := Cofork.isColimitOfIsos
    (Cofork.ofπ (L.map q) (by simp only [← L.map_comp, wq]))
    (isColimitCoforkMapOfIsColimit L wq hq) c
    (e.app R) (e.app U) (Iso.refl _) (e.hom.naturality s).symm
    (e.hom.naturality t).symm (by simp [c])
  exact hc.coconePointUniqueUpToIso hq'

/-- A locally surjective map of presheaves whose target is isomorphic to a representable one
stays locally surjective when read through the Yoneda preimage of the composite.

This is `CategoryTheory.Functor.map_preimage` in the form in which a client holding a map
produced by `CategoryTheory.Functor.preimage` needs it; stating it separately keeps the rewrite
out of a term whose type is only definitionally correct. -/
theorem Presheaf.isLocallySurjective_yoneda_map_preimage_comp_iso {C : Type u₁}
    [Category.{v₁} C] (J : GrothendieckTopology C) {X Y : C} {F : Cᵒᵖ ⥤ Type v₁}
    (φ : yoneda.obj X ⟶ F) (hφ : Presheaf.IsLocallySurjective J φ) (e : F ≅ yoneda.obj Y) :
    Presheaf.IsLocallySurjective J (yoneda.map (yoneda.preimage (φ ≫ e.hom))) := by
  have := hφ
  rw [yoneda.map_preimage]
  infer_instance

/-- Pasting a commuting square of representable presheaves over a presheaf with a factorization
of one of its legs: from `h_{wU} ≫ f = h_{wV} ≫ q` and `w ≫ wV = t` one gets
`h_{w ≫ wU} ≫ f = h_t ≫ q`. -/
theorem yoneda_map_comp_fac {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v₁}
    {U V W T : C} {f : yoneda.obj U ⟶ F} {q : yoneda.obj V ⟶ F} {wU : W ⟶ U} {wV : W ⟶ V}
    (hW : yoneda.map wU ≫ f = yoneda.map wV ≫ q) {w : T ⟶ W} {t : T ⟶ V}
    (hwt : w ≫ wV = t) : yoneda.map (w ≫ wU) ≫ f = yoneda.map t ≫ q := by
  rw [yoneda.map_comp, Category.assoc, hW, ← Category.assoc, ← yoneda.map_comp, hwt]

end CategoryTheory

namespace AlgebraicGeometry

open Space Stacks.Groupoids

/-- Sheaves of sets on the big fppf site of a scheme `S` of a big fppf site admit
sheafification: the site is essentially small. -/
alias hasSheafify_bigFppfOver := bigFppfOver_hasSheafify

/-- The localized big fppf site of a scheme is essentially small. -/
theorem essentiallySmall_overTopologySite (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
  essentiallySmall_bigFppfOver B S hS

/-- Sheaves of sets on a localized big fppf site admit sheafification. -/
theorem hasSheafify_overTopology (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (overTopology .fppf B S hS) (Type u) :=
  hasSheafify_bigFppfOver B S hS

/-- The localized big fppf site is subcanonical: the sheaf represented by an object of the site
is a sheaf because it is an algebraic space. -/
theorem subcanonical_overTopology (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (overTopology .fppf B S hS).Subcanonical :=
  .of_isSheaf_yoneda_obj _ fun X =>
    (isSheaf_iff_isSheaf_of_type _ _).mp (isAlgebraicSpace_yoneda B S hS X).isSheaf

/-- **Stacks 03FP, the inverse image.** The direct image along the inclusion of a localized big
fppf site into the localization of a big fppf site containing it has a left adjoint on
set-valued sheaves. That left adjoint is the inverse image `f⁻¹` of the source. -/
theorem inclusionOver_sheafPushforwardContinuous_isRightAdjoint (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B) := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (siteCategory (τ := .fppf) B') := essentiallySmall_schemeBelow _
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B S hS)) :=
    essentiallySmall_bigFppfOver B S hS
  let : EssentiallySmall.{u} (Over (base (τ := .fppf) B' S (largerContains h hS))) :=
    essentiallySmall_bigFppfOver B' S (largerContains h hS)
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S (largerContains h hS)
  let : ∀ P : (Over (base (τ := .fppf) B S hS))ᵒᵖ ⥤ Type u,
      i.op.HasPointwiseLeftKanExtension P := by
    intro P X
    let : HasColimitsOfShape (CostructuredArrow i.op X) (Type u) :=
      hasColimitsOfShape_of_essentiallySmall.{u} _ _
    infer_instance
  infer_instance

/-- **Stacks 03FP, part (2)**, relative to effective descent along the covering sieves of the
larger site at the monomorphisms locally of finite type.

Enlarging the big fppf site preserves algebraic spaces over the base scheme: the inverse image
of an algebraic space over `S` on the smaller localized site is an algebraic space over `S` on
the larger one.

The descent hypothesis is the one carried by the quotient theorem
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_relation_of_diagDescent`, which is the
only input of the Stacks proof that this library does not yet have unconditionally; the statement
of Stacks 03FP itself has no such hypothesis. -/
theorem isAlgebraicSpace_sheafPullback_of_descent (B B' : BigFppfSite.{u})
    (h : IsContained (τ := .fppf) B B') (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B' S (largerContains h hS)
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    IsAlgebraicSpace B' S (largerContains h hS)
      ((i.sheafPullback (Type u) J K).obj ⟨F, hF.isSheaf⟩).obj := by
  let hS' : B'.Contains S := largerContains h hS
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S hS'
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S hS'
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    inferInstanceAs (HasSheafify J (Type u))
  let : HasSheafify (BigFppfOver.topology B' S hS') (Type u) :=
    inferInstanceAs (HasSheafify K (Type u))
  let : J.Subcanonical := subcanonical_overTopology B S hS
  let : K.Subcanonical := subcanonical_overTopology B' S hS'
  obtain ⟨U, q, hqs, hqe⟩ := hF.exists_atlas
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  have hs : Etale ((Over.post B.inclusion).map s).left :=
    hqe.property q (yoneda.map t) s hR.flip
  have ht : Etale ((Over.post B.inclusion).map t).left :=
    hqe.property q (yoneda.map s) t hR
  let : IsEtaleEquivalenceRelation (relation B S hS t s) := {
    isEquivalenceRelation := by
      simpa only [relation, PreRelation.target, PreRelation.source, prod.lift_fst, prod.lift_snd]
        using isEquivalenceRelation_of_isPullback B S hS q s t hR
    etale_source := by
      simpa only [relation, PreRelation.source, prod.lift_snd] using ht
    etale_target := by
      simpa only [relation, PreRelation.target, prod.lift_fst] using hs }
  let : IsEtaleEquivalenceRelation (relation B' S hS' (i.map t) (i.map s)) :=
    inferInstanceAs (IsEtaleEquivalenceRelation (relation B S hS t s))
  let Q := quotientSheaf K (Over.post B'.inclusion) (relation B' S hS' (i.map t) (i.map s))
  have hQ : IsAlgebraicSpace B' S hS' Q.obj :=
    isAlgebraicSpace_quotientSheaf_relation_of_diagDescent B' S hS' (i.map t) (i.map s) hdesc
  let q' : yoneda.obj (i.obj U) ⟶ Q.obj := quotientMap B' S hS' (i.map t) (i.map s)
  have hrep : yoneda.relativelyRepresentable q' :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B' S hS' (i.map t) (i.map s) hQ
  have hR' : IsPullback (yoneda.map (i.map s)) (yoneda.map (i.map t)) q' q' :=
    quotientMap_isPullback B' S hS' (i.map t) (i.map s)
  obtain ⟨_, _, ⟨hq⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS q s t hR hF hqs hqe
  obtain ⟨_, _, ⟨hq'⟩⟩ := isCoequalizer_of_surjectiveEtale B' S hS' q' (i.map s) (i.map t) hR' hQ
    (quotientMap_surjective B' S hS' (i.map t) (i.map s) hrep)
    (quotientMap_etale B' S hS' (i.map t) (i.map s) hrep)
  let : PreservesColimits (i.sheafPullback (Type u) J K) :=
    (i.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  let e := coequalizerIsoOfNatIso J.yoneda (i ⋙ K.yoneda) (i.sheafPullback (Type u) J K)
    (pullbackYonedaIso i J K) s t
    (show J.yoneda.obj U ⟶ (⟨F, hF.isSheaf⟩ : Sheaf J (Type u)) from ⟨q⟩)
    (by apply Sheaf.hom_ext; exact hR.w)
    (show (i ⋙ K.yoneda).obj U ⟶ Q from ⟨q'⟩)
    (by apply Sheaf.hom_ext; exact hR'.w) hq hq'
  exact isAlgebraicSpace_of_iso B' S hS' ((sheafToPresheaf K (Type u)).mapIso e) hQ

end AlgebraicGeometry

end
