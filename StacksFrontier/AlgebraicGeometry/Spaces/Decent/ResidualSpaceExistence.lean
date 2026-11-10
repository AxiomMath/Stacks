module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Existence of the residual space at a point (Stacks 06QZ)

Every point `x` of an algebraic space `X` over `S` is the image of a monomorphism `Z ⟶ X` with
`Z` a reduced, locally Noetherian algebraic space whose point set is a singleton: a *residual
space* of `X` at `x` in the sense of **Stacks 06R0**.

## Main results

* `AlgebraicGeometry.Space.exists_isResidualSpaceAt`: **Stacks 06QZ**, the existence half.

## Implementation notes

The construction is the one of the source. Choose an étale presentation `U/R` of `X`
(**Stacks 0263**), which `AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace` assembles
from a chosen atlas and its kernel pair. Let `U'` be the disjoint union of the spectra of the
residue fields at the points of `U` lying over `x`; the map `U' ⟶ U` is a monomorphism
(**Stacks 01J9**), and `U'` lies in the chosen big fppf site because its size is at most
`2 ^ (size of U)`, which is below the site's cutoff since that cutoff is a strong limit. Let
`R'` be the restriction of `R` along `U' ⟶ U`, formed as a fibre product inside the site.

The point of the proof is that `R' ⟶ U'` is étale even though `U' ⟶ U` is only a
monomorphism: each leg of `R'` factors as a monomorphism followed by a base change of the
corresponding étale leg of `R`, and a monomorphism into a scheme étale over a disjoint union
of spectra of fields is étale after composing, by **Stacks 03DP** and **Stacks 03PC**. So
`R'` is an étale equivalence relation on `U'` and `Z = U'/R'` is an algebraic space
(**Stacks 02WW**). Being a restriction, `Z ⟶ U/R = X` is a monomorphism (**Stacks 045Z** and
**Stacks 02VH**), so it is injective on points (**Stacks 06RV**); since every point of `U'`
lies over `x`, the point set of `Z` is the singleton `{x}`. Reducedness and local
Noetherianity are read off the atlas `U'`, which is a disjoint union of spectra of fields.

Two pieces of general category theory are proved here for want of a home: transport of an
internal equivalence relation along an isomorphism of its relation object
(`AlgebraicGeometry.Space.isEquivalenceRelation_of_iso`), and injectivity of the map of
quotient sheaves attached to a cartesian restriction square
(`AlgebraicGeometry.Space.mono_quotientSheafMap_of_isPullback`). The latter is Stacks 045Z
stated for a relation that is *exhibited* as a restriction by a cartesian square rather than
one that is literally the pullback, which is what the construction produces: the relation
`R'` is built inside the site, and its image in the slice over `S` is only isomorphic to the
pullback there.

Uniqueness of the residual space, the other half of Stacks 06QZ, is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceUniqueness`, which assembles the two
halves into the full statement.

## References

* [Stacks Project, Tag 01J9](https://stacks.math.columbia.edu/tag/01J9)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03DP](https://stacks.math.columbia.edu/tag/03DP)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 06QZ](https://stacks.math.columbia.edu/tag/06QZ)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **Stacks 03DP and 03PC combined.** A monomorphism into a scheme étale over a field,
followed by that étale morphism, is again étale.

By Stacks 03PC the étale scheme is a disjoint union of spectra of finite separable field
extensions, and by Stacks 03DP a monomorphism into such a disjoint union is a sub-disjoint
union of it; the composite is therefore again of that shape. -/
theorem etale_of_mono_of_etale_to_spec_field
    {Y V : Scheme.{u}} {k : Type u} [Field k]
    (m : Y ⟶ V) (e : V ⟶ Spec (.of k)) [Mono m] [Etale e] :
    Etale (m ≫ e) := by
  obtain ⟨I, K, hK, hAlg, hFin, hSep, isoV, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k e).mp inferInstance
  let g : Y ⟶ (∐ fun i : I => Spec (.of (K i))) := m ≫ isoV.hom
  have : Mono g := by
    dsimp [g]
    infer_instance
  obtain ⟨J, isoY, hfac⟩ := exists_iso_coproduct_spec_of_mono K (Y := Y) g
  apply (etale_iff_iso_coproduct_spectra_finite_separable k (m ≫ e)).2
  refine ⟨J, fun j => K j.1, fun j => hK j.1, fun j => hAlg j.1,
    fun j => hFin j.1, fun j => hSep j.1, isoY, ?_⟩
  let fI : (i : I) → Spec (.of (K i)) ⟶ Spec (.of k) :=
    fun i => Spec.map (CommRingCat.ofHom (algebraMap k (K i)))
  let incl : (j : J) → Spec (.of (K j.1)) ⟶ (∐ fun i : I => Spec (.of (K i))) :=
    fun j => Sigma.ι (fun i : I => Spec (.of (K i))) j.1
  have hdesc : (Sigma.desc fun j : J => Spec.map (CommRingCat.ofHom (algebraMap k (K j.1)))) =
      Sigma.desc incl ≫ Sigma.desc fI := by
    apply Sigma.hom_ext
    intro j
    simp [incl, fI]
  calc
    isoY.hom ≫ (Sigma.desc fun j : J =>
        Spec.map (CommRingCat.ofHom (algebraMap k (K j.1)))) =
        (isoY.hom ≫ Sigma.desc incl) ≫ Sigma.desc fI := by
      rw [hdesc, Category.assoc]
    _ = g ≫ Sigma.desc fI := by rw [hfac]
    _ = m ≫ e := by simpa only [g, Category.assoc] using congrArg (fun f => m ≫ f) he

/-- A monomorphism into a scheme étale over a disjoint union of spectra of fields, followed by
that étale morphism, is again étale.

Étaleness is Zariski local on the target, so this follows from
`AlgebraicGeometry.etale_of_mono_of_etale_to_spec_field` on each member of the disjoint union. -/
theorem etale_of_mono_of_etale_to_coproduct_spec_fields
    {I : Type u} (k : I → Type u) [∀ i, Field (k i)]
    {Y V : Scheme.{u}} (m : Y ⟶ V)
    (e : V ⟶ ∐ fun i : I => Spec (.of (k i))) [Mono m] [Etale e] :
    Etale (m ≫ e) := by
  let _ : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  let 𝒰 := sigmaOpenCover (fun i : I => Spec (.of (k i)))
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale.{u}) 𝒰 (f := m ≫ e)).2
  intro i
  let _ : Field (k i) := (inferInstance : (∀ j : I, Field (k j))) i
  let ep := pullback.snd e (𝒰.f i)
  let mp := pullback.snd m (pullback.fst e (𝒰.f i))
  have hmp : Mono mp := by
    dsimp [mp]
    infer_instance
  have hep : Etale ep := by
    dsimp [ep]
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback e (𝒰.f i))
      (show Etale e from inferInstance)
  have hcomp : Etale (mp ≫ ep) :=
    @etale_of_mono_of_etale_to_spec_field _ _ (k i) _ mp ep hmp hep
  let eAssoc := pullbackRightPullbackFstIso e (𝒰.f i) m
  have heq : eAssoc.hom ≫ pullback.snd (m ≫ e) (𝒰.f i) = mp ≫ ep := by
    dsimp [eAssoc, mp, ep]
    rw [pullbackRightPullbackFstIso_hom_snd e (𝒰.f i) m]
  have hlocal : Etale (pullback.snd (m ≫ e) (𝒰.f i)) := by
    have h' : Etale (eAssoc.hom ≫ pullback.snd (m ≫ e) (𝒰.f i)) := heq ▸ hcomp
    let _ : MorphismProperty.RespectsIso (@Etale.{u}) := by
      rw [HasRingHomProperty.eq_affineLocally (@Etale.{u})]
      exact affineLocally_respectsIso RingHom.Etale RingHom.Etale.respectsIso
    simpa [Category.assoc] using MorphismProperty.RespectsIso.precomp (@Etale.{u}) eAssoc.inv
      (eAssoc.hom ≫ pullback.snd (m ≫ e) (𝒰.f i)) h'
  exact hlocal

/-- **Stacks 01J9.** The morphism to `X` from the disjoint union of the spectra of the residue
fields at the points of a subset of `X` is a monomorphism: it is injective and surjective on
stalks. -/
theorem mono_sigmaDesc_fromSpecResidueField (X : Scheme.{u}) (E : Set X) :
    Mono (Sigma.desc (fun y : E ↦ X.fromSpecResidueField y.1)) := by
  let i := Sigma.desc (fun y : E ↦ X.fromSpecResidueField y.1)
  let e := sigmaMk (fun y : E ↦ Spec (.of (X.residueField y.1)) : E → Scheme)
  have hcomponent (y : E) :
      Sigma.ι (fun y : E ↦ Spec (.of (X.residueField y.1))) y ≫ i =
        X.fromSpecResidueField y.1 := Sigma.ι_comp_desc _ _
  have hbase (p : Σ y : E, Spec (.of (X.residueField y.1))) : i (e p) = p.1.1 := by
    obtain ⟨y, a⟩ := p
    rw [sigmaMk_mk]
    change (Sigma.ι (fun y : E ↦ Spec (.of (X.residueField y.1))) y ≫ i) a = y.1
    rw [hcomponent]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfib : ∀ p q : Σ y : E, Spec (.of (X.residueField y.1)),
      (p.1 : X) = (q.1 : X) → p = q := by
    rintro ⟨y, a⟩ ⟨y', b⟩ hval
    obtain rfl : y = y' := Subtype.ext hval
    obtain rfl : a = b := Subsingleton.elim _ _
    rfl
  have hinj : Function.Injective i := by
    intro z z' h
    have hval : (((e.symm z).1 : E) : X) = (((e.symm z').1 : E) : X) := by
      calc (((e.symm z).1 : E) : X) = i (e (e.symm z)) := (hbase _).symm
        _ = i (e (e.symm z')) := by rw [e.apply_symm_apply, h, e.apply_symm_apply]
        _ = (((e.symm z').1 : E) : X) := hbase _
    exact e.symm.injective (hfib _ _ hval)
  have hsurj : SurjectiveOnStalks i := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks)
      (sigmaOpenCover (fun y : E ↦ Spec (.of (X.residueField y.1))))]
    intro y
    change SurjectiveOnStalks
      (Sigma.ι (fun y : E ↦ Spec (.of (X.residueField y.1))) y ≫ i)
    rw [hcomponent y]
    infer_instance
  let _ : SurjectiveOnStalks i := hsurj
  exact SurjectiveOnStalks.mono_of_injective hinj

namespace Space
open Stacks.Groupoids

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

/-- **Stacks 0263.** The presentation of an algebraic space attached to a given surjective étale
atlas `a : yoneda.obj U ⟶ X`: the relation is the kernel pair `U ×_X U`, which exists because the
atlas is relatively representable, and it is an étale equivalence relation by Stacks 0262. -/
noncomputable def presentationOfAtlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Presentation B S hS X hX := by
  classical
  have hrel : MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a := by
    simpa [MorphismProperty.presheaf] using haetale
  let hf : yoneda.relativelyRepresentable a := hrel.1
  let R := hf.pullback a
  let src : R ⟶ U := hf.snd a
  let tgt : R ⟶ U := yoneda.preimage (hf.fst a)
  have hkernel : IsPullback (yoneda.map tgt) (yoneda.map src) a a := by
    simpa [tgt, src] using hf.isPullback a
  have hsrc : PreRelation.source (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map src :=
    prod.lift_snd _ _
  have htgt : PreRelation.target (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map tgt :=
    prod.lift_fst _ _
  exact
    { U := U
      R := R
      target := tgt
      source := src
      isEtaleEquivalenceRelation :=
        { isEquivalenceRelation := by
            rw [htgt, hsrc]
            exact isEquivalenceRelation_of_isPullback B S hS a tgt src hkernel
          etale_source := by
            rw [hsrc]
            exact hrel.2 a (hf.fst a) (hf.snd a) (hf.isPullback a)
          etale_target := by
            rw [htgt]
            exact hrel.2 a (yoneda.map src) tgt (by simpa [tgt, src] using (hf.isPullback a).flip) }
      toSpace := a
      surjective := hasurj
      etale := haetale
      isPullback := hkernel }

/-- **Stacks 0263.** A presentation of an algebraic space, built from a chosen surjective étale
atlas and its kernel pair.

The atlas comes from `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, and the presentation is
`AlgebraicGeometry.Space.presentationOfAtlas` at that atlas. -/
noncomputable def presentationOfIsAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Presentation B S hS X hX :=
  presentationOfAtlas B S hS X hX (Classical.choose hX.exists_atlas)
    (Classical.choose (Classical.choose_spec hX.exists_atlas))
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2


variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The set of points of the presenting scheme lying over `x`. -/
def atlasFibre (P : Presentation B S hS X hX) (x : points B S hS X) :
    Set ((BigFppfOver.toScheme B S hS).obj P.U) :=
  {y | pointsMap B S hS (yoneda.obj P.U) P.toSpace
    ((pointsEquivScheme B S hS P.U).symm y) = x}

/-- The disjoint union of the spectra of the residue fields at the points over `x`. -/
noncomputable def residueCoproduct (P : Presentation B S hS X hX)
    (x : points B S hS X) : Scheme.{u} :=
  ∐ fun y : atlasFibre B S hS P x =>
    Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1))

/-- The canonical morphism from the residue-field coproduct to the presenting scheme. -/
noncomputable def residueCoproductHom (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    residueCoproduct B S hS P x ⟶ (BigFppfOver.toScheme B S hS).obj P.U :=
  Sigma.desc fun y => ((BigFppfOver.toScheme B S hS).obj P.U).fromSpecResidueField y.1

/-- The residue-field coproduct lies in the chosen big fppf site. There are at most `2 ^ size`
points of the presenting scheme, each contributing a spectrum of size at most `size`, so the
coproduct has size at most `2 ^ size`, which is below the site's cutoff because that cutoff is
a strong limit. -/
theorem contains_residueCoproduct (P : Presentation B S hS X hX)
    (x : points B S hS X) : B.Contains (residueCoproduct B S hS P x) := by
  set T := (BigFppfOver.toScheme B S hS).obj P.U with hT
  have hI : Cardinal.mk (atlasFibre B S hS P x) ≤ 2 ^ T.size :=
    (Cardinal.mk_subtype_le _).trans (Scheme.mk_le_two_pow_size T)
  have hsum : (residueCoproduct B S hS P x).size ≤ 2 ^ T.size := by
    refine schemeSize_coproduct_le _ (2 ^ T.size)
      (T.aleph0_le_size.trans (Cardinal.cantor T.size).le) hI fun y => ?_
    exact (Scheme.size_le_of_mono_quasiCompact (T.fromSpecResidueField y.1)).trans
      (Cardinal.cantor T.size).le
  exact hsum.trans_lt (B.cutoff_isStrongPrelimit P.U.left.property)

/-- The residue-field coproduct as an object of the big fppf site over `S`. -/
noncomputable def residueSite (P : Presentation B S hS X hX)
    (x : points B S hS X) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage
    (show B.inclusion.obj (B.obj (contains_residueCoproduct B S hS P x)) ⟶
      B.inclusion.obj P.U.left from residueCoproductHom B S hS P x) ≫ P.U.hom)

/-- The canonical morphism of site objects from the residue-field coproduct to `U`. -/
noncomputable def residueSiteHom (P : Presentation B S hS X hX)
    (x : points B S hS X) : residueSite B S hS P x ⟶ P.U :=
  Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj (B.obj (contains_residueCoproduct B S hS P x)) ⟶
      B.inclusion.obj P.U.left from residueCoproductHom B S hS P x))
    (by apply B.inclusion.map_injective; rfl)

/-- The morphism of site objects underlying the residue-field cover is the cover itself. -/
theorem residueSiteHom_toScheme (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    (BigFppfOver.toScheme B S hS).map (residueSiteHom B S hS P x) =
      residueCoproductHom B S hS P x :=
  B.inclusion.map_preimage _

/-- **Stacks 01J9.** The residue-field cover of the fibre over `x` is a monomorphism. -/
theorem mono_residueSiteHom (P : Presentation B S hS X hX)
    (x : points B S hS X) : Mono (residueSiteHom B S hS P x) := by
  have _ : (BigFppfOver.toScheme B S hS).ReflectsMonomorphisms :=
    Functor.reflectsMonomorphisms_of_faithful _
  have hm : Mono ((BigFppfOver.toScheme B S hS).map (residueSiteHom B S hS P x)) := by
    rw [residueSiteHom_toScheme]
    exact mono_sigmaDesc_fromSpecResidueField _ (atlasFibre B S hS P x)
  exact (inferInstance : (BigFppfOver.toScheme B S hS).ReflectsMonomorphisms).reflects _ hm

/-- The category `BigFppfOver B S hS` has binary products. -/
instance : HasBinaryProducts (BigFppfOver B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- The relation scheme of the restricted presentation: the restriction of `R` along the
residue-field cover of the fibre over `x`. -/
noncomputable def residueRelation (P : Presentation B S hS X hX)
    (x : points B S hS X) : BigFppfOver B S hS :=
  pullback (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
    (prod.lift P.target P.source)

/-- The target projection of the restricted relation. -/
noncomputable def residueRelationTarget (P : Presentation B S hS X hX)
    (x : points B S hS X) : residueRelation B S hS P x ⟶ residueSite B S hS P x :=
  pullback.fst (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
    (prod.lift P.target P.source) ≫ prod.fst

/-- The source projection of the restricted relation. -/
noncomputable def residueRelationSource (P : Presentation B S hS X hX)
    (x : points B S hS X) : residueRelation B S hS P x ⟶ residueSite B S hS P x :=
  pullback.fst (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
    (prod.lift P.target P.source) ≫ prod.snd

/-- The comparison morphism from the restricted relation to the base change of one leg of
the relation along the residue-field cover. -/
noncomputable def residueRelationToLeg (P : Presentation B S hS X hX)
    (x : points B S hS X) (c : P.R ⟶ P.U)
    (π : (P.U ⨯ P.U : BigFppfOver B S hS) ⟶ P.U)
    (π' : (residueSite B S hS P x ⨯ residueSite B S hS P x : BigFppfOver B S hS) ⟶
      residueSite B S hS P x)
    (hπ : prod.lift P.target P.source ≫ π = c)
    (hd : prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x) ≫ π =
      π' ≫ residueSiteHom B S hS P x) :
    residueRelation B S hS P x ⟶ pullback c (residueSiteHom B S hS P x) :=
  pullback.lift
    (pullback.snd (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
      (prod.lift P.target P.source))
    (pullback.fst (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
      (prod.lift P.target P.source) ≫ π')
    (by
      calc pullback.snd (prod.map (residueSiteHom B S hS P x)
              (residueSiteHom B S hS P x)) (prod.lift P.target P.source) ≫ c
          = (pullback.snd (prod.map (residueSiteHom B S hS P x)
              (residueSiteHom B S hS P x)) (prod.lift P.target P.source) ≫
              prod.lift P.target P.source) ≫ π := by rw [← hπ, Category.assoc]
        _ = (pullback.fst (prod.map (residueSiteHom B S hS P x)
              (residueSiteHom B S hS P x)) (prod.lift P.target P.source) ≫
              prod.map (residueSiteHom B S hS P x)
                (residueSiteHom B S hS P x)) ≫ π := by rw [pullback.condition]
        _ = pullback.fst (prod.map (residueSiteHom B S hS P x)
              (residueSiteHom B S hS P x)) (prod.lift P.target P.source) ≫
              (prod.map (residueSiteHom B S hS P x)
                (residueSiteHom B S hS P x) ≫ π) := Category.assoc _ _ _
        _ = (pullback.fst (prod.map (residueSiteHom B S hS P x)
              (residueSiteHom B S hS P x)) (prod.lift P.target P.source) ≫ π') ≫
              residueSiteHom B S hS P x := by rw [hd, Category.assoc])

/-- The comparison morphism composed with the first projection is the projection of the
restricted relation onto the original relation. -/
theorem residueRelationToLeg_fst (P : Presentation B S hS X hX)
    (x : points B S hS X) (c : P.R ⟶ P.U) (π π' hπ hd) :
    residueRelationToLeg B S hS P x c π π' hπ hd ≫ pullback.fst c
        (residueSiteHom B S hS P x) =
      pullback.snd (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
        (prod.lift P.target P.source) :=
  pullback.lift_fst _ _ _

/-- The comparison morphism composed with the second projection is the chosen leg of the
restricted relation. -/
theorem residueRelationToLeg_snd (P : Presentation B S hS X hX)
    (x : points B S hS X) (c : P.R ⟶ P.U) (π π' hπ hd) :
    residueRelationToLeg B S hS P x c π π' hπ hd ≫ pullback.snd c
        (residueSiteHom B S hS P x) =
      pullback.fst (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
        (prod.lift P.target P.source) ≫ π' :=
  pullback.lift_snd _ _ _

/-- The scheme underlying the residue-field cover is the coproduct it was built from. -/
theorem toScheme_residueSite (P : Presentation B S hS X hX) (x : points B S hS X) :
    (BigFppfOver.toScheme B S hS).obj (residueSite B S hS P x) =
      residueCoproduct B S hS P x := rfl

/-- The comparison morphism is a monomorphism: composed with the first projection it is the
projection of the restricted relation onto `R`, which is a base change of the monomorphism
`g × g`. -/
theorem mono_residueRelationToLeg (P : Presentation B S hS X hX)
    (x : points B S hS X) (c : P.R ⟶ P.U) (π π' hπ hd) :
    Mono (residueRelationToLeg B S hS P x c π π' hπ hd) := by
  have hg : Mono (residueSiteHom B S hS P x) := mono_residueSiteHom B S hS P x
  have hmap : Mono (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x)) :=
    inferInstance
  have hsnd : Mono (pullback.snd (prod.map (residueSiteHom B S hS P x)
      (residueSiteHom B S hS P x)) (prod.lift P.target P.source)) :=
    pullback.snd_of_mono
  have _ : Mono (residueRelationToLeg B S hS P x c π π' hπ hd ≫
      pullback.fst c (residueSiteHom B S hS P x)) := by
    rw [residueRelationToLeg_fst]
    exact hsnd
  exact mono_of_mono _ (pullback.fst c (residueSiteHom B S hS P x))

/-- A leg of the relation, based changed along the residue-field cover, stays étale. -/
theorem etale_residueLeg (P : Presentation B S hS X hX) (x : points B S hS X)
    (c : P.R ⟶ P.U) (hc : Etale ((BigFppfOver.toScheme B S hS).map c)) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.snd c (residueSiteHom B S hS P x))) :=
  MorphismProperty.of_isPullback
    (Functor.map_isPullback _ (IsPullback.of_hasPullback c (residueSiteHom B S hS P x))) hc

/-- **The key étaleness statement.** A leg of the restricted relation is étale.

It factors as the comparison monomorphism followed by a base change of the corresponding leg
of the original relation, which is étale; since the target of that base change is the
residue-field cover, a disjoint union of spectra of fields, the composite is étale by
`AlgebraicGeometry.etale_of_mono_of_etale_to_coproduct_spec_fields`. -/
theorem etale_residueRelationLeg (P : Presentation B S hS X hX)
    (x : points B S hS X) (c : P.R ⟶ P.U) (π π' hπ hd)
    (hc : Etale ((BigFppfOver.toScheme B S hS).map c)) :
    Etale ((BigFppfOver.toScheme B S hS).map
      (residueRelationToLeg B S hS P x c π π' hπ hd ≫
        pullback.snd c (residueSiteHom B S hS P x))) := by
  have _ : Mono (residueRelationToLeg B S hS P x c π π' hπ hd) :=
    mono_residueRelationToLeg B S hS P x c π π' hπ hd
  have hm : Mono ((BigFppfOver.toScheme B S hS).map
      (residueRelationToLeg B S hS P x c π π' hπ hd)) := Functor.map_mono _ _
  have _ : Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.snd c (residueSiteHom B S hS P x))) := etale_residueLeg B S hS P x c hc
  have hU : (BigFppfOver.toScheme B S hS).obj (residueSite B S hS P x) =
      ∐ fun y : atlasFibre B S hS P x =>
        Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)) := rfl
  have he : Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.snd c (residueSiteHom B S hS P x)) ≫ eqToHom hU) := inferInstance
  have hcomp := @etale_of_mono_of_etale_to_coproduct_spec_fields
    (atlasFibre B S hS P x)
    (fun y => ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)) _ _ _
    ((BigFppfOver.toScheme B S hS).map (residueRelationToLeg B S hS P x c π π' hπ hd))
    ((BigFppfOver.toScheme B S hS).map
      (pullback.snd c (residueSiteHom B S hS P x)) ≫ eqToHom hU) hm he
  have hback : Etale (((BigFppfOver.toScheme B S hS).map
      (residueRelationToLeg B S hS P x c π π' hπ hd) ≫
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd c (residueSiteHom B S hS P x)) ≫ eqToHom hU)) ≫
      eqToHom hU.symm) := by
    have _ : Etale (eqToHom hU.symm) := inferInstance
    have _ := hcomp
    exact inferInstance
  rw [Functor.map_comp]
  simpa [Category.assoc] using hback

/-- The target projection of a presentation is étale on underlying schemes. -/
theorem etale_presentation_target (P : Presentation B S hS X hX) :
    Etale ((BigFppfOver.toScheme B S hS).map P.target) := by
  have h := P.isEtaleEquivalenceRelation
  have hj : PreRelation.target (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) = (Over.post B.inclusion).map P.target :=
    prod.lift_fst _ _
  have he := h.etale_target
  rw [hj] at he
  exact he

/-- The source projection of a presentation is étale on underlying schemes. -/
theorem etale_presentation_source (P : Presentation B S hS X hX) :
    Etale ((BigFppfOver.toScheme B S hS).map P.source) := by
  have h := P.isEtaleEquivalenceRelation
  have hj : PreRelation.source (prod.lift ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) = (Over.post B.inclusion).map P.source :=
    prod.lift_snd _ _
  have he := h.etale_source
  rw [hj] at he
  exact he

/-- The target projection of the restricted relation is étale. -/
theorem etale_residueRelationTarget (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    Etale ((BigFppfOver.toScheme B S hS).map (residueRelationTarget B S hS P x)) := by
  have h := etale_residueRelationLeg B S hS P x P.target prod.fst prod.fst
    (prod.lift_fst _ _) (prod.map_fst _ _) (etale_presentation_target B S hS P)
  rwa [residueRelationToLeg_snd] at h

/-- The source projection of the restricted relation is étale. -/
theorem etale_residueRelationSource (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    Etale ((BigFppfOver.toScheme B S hS).map (residueRelationSource B S hS P x)) := by
  have h := etale_residueRelationLeg B S hS P x P.source prod.snd prod.snd
    (prod.lift_snd _ _) (prod.map_snd _ _) (etale_presentation_source B S hS P)
  rwa [residueRelationToLeg_snd] at h

/-- A cartesian square exhibiting `j'` as the restriction of `j` along `g` makes the source and
target maps commute with `r` and `g`. -/
private theorem comm_source_target_of_isPullback {T : Scheme.{u}} {R U R' U' : Over T}
    {j : PreRelation R U} {j' : PreRelation R' U'} {r : R' ⟶ R} {g : U' ⟶ U}
    (hpb : IsPullback j' r (prod.map g g) j) :
    r ≫ PreRelation.source j = PreRelation.source j' ≫ g ∧
      r ≫ PreRelation.target j = PreRelation.target j' ≫ g := by
  constructor
  · have hh := congrArg (fun k => k ≫ prod.snd) hpb.w
    simpa only [PreRelation.source, Category.assoc, prod.map_snd] using hh.symm
  · have hh := congrArg (fun k => k ≫ prod.fst) hpb.w
    simpa only [PreRelation.target, Category.assoc, prod.map_fst] using hh.symm

section Transport

variable {C D : Type*} [Category.{u} C] [Category.{u} D]
  [HasBinaryProducts C] [HasBinaryProducts D]

/-- The image of a lift into a binary product, compared with the product of the images, is the
lift of the images. -/
theorem map_lift_comp_prodComparison (G : C ⥤ D) {T A A' : C} (f : T ⟶ A) (f' : T ⟶ A') :
    G.map (prod.lift f f') ≫ prodComparison G A A' = prod.lift (G.map f) (G.map f') := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prodComparison_fst, ← G.map_comp, prod.lift_fst, prod.lift_fst]
  · rw [Category.assoc, prodComparison_snd, ← G.map_comp, prod.lift_snd, prod.lift_snd]

/-- A functor preserving binary products and pullbacks carries the pullback square exhibiting a
restricted relation to the corresponding square for the images. -/
theorem isPullback_map_restriction (G : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan G] [PreservesLimitsOfShape (Discrete WalkingPair) G]
    {R U R' U' : C} (t s : R ⟶ U) (t' s' : R' ⟶ U') (m : U' ⟶ U) (r : R' ⟶ R)
    (h : IsPullback (prod.lift t' s') r (prod.map m m) (prod.lift t s)) :
    IsPullback (prod.lift (G.map t') (G.map s')) (G.map r)
      (prod.map (G.map m) (G.map m)) (prod.lift (G.map t) (G.map s)) :=
  (h.map G).of_iso (Iso.refl _) (asIso (prodComparison G U' U')) (Iso.refl _)
    (asIso (prodComparison G U U))
    (by simpa using map_lift_comp_prodComparison G t' s') (by simp)
    (by simpa using prodComparison_natural G m m)
    (by simpa using map_lift_comp_prodComparison G t s)

omit [HasBinaryProducts C] in
/-- Cancelling an isomorphism inserted between two morphisms that already agree after
composition with `q`. -/
private theorem assoc_inv_hom_comp {W R R' Y : C} (e : R' ≅ R) (a b : W ⟶ R) (q : R ⟶ Y)
    (hq : a ≫ q = b ≫ q) :
    (a ≫ e.inv) ≫ (e.hom ≫ q) = (b ≫ e.inv) ≫ (e.hom ≫ q) := by
  rw [Category.assoc, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id_assoc]
  exact hq

/-- Transport an internal equivalence relation along an isomorphism of its relation object. -/
noncomputable def equivalenceRelationOfIso {R R' Y : C} {p₁ p₂ : R ⟶ Y}
    (h : EquivalenceRelation p₁ p₂) (e : R' ≅ R) :
    EquivalenceRelation (e.hom ≫ p₁) (e.hom ≫ p₂) where
  right_cancellation := by
    intro T a b h₁ h₂
    refine (cancel_mono e.hom).1 (h.right_cancellation (a ≫ e.hom) (b ≫ e.hom) ?_ ?_)
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc] using h₂
  r := h.r ≫ e.inv
  reflexivity₁ := by rw [Category.assoc, Iso.inv_hom_id_assoc]; exact h.reflexivity₁
  reflexivity₂ := by rw [Category.assoc, Iso.inv_hom_id_assoc]; exact h.reflexivity₂
  s := e.hom ≫ h.s ≫ e.inv
  symmetry₁ := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h.symmetry₁]
  symmetry₂ := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h.symmetry₂]
  c := PullbackCone.mk (h.c.fst ≫ e.inv) (h.c.snd ≫ e.inv) (by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    exact h.c.condition)
  isLimit := by
    refine PullbackCone.IsLimit.mk _
      (fun c => PullbackCone.IsLimit.lift h.isLimit (c.fst ≫ e.hom) (c.snd ≫ e.hom) (by
        rw [Category.assoc, Category.assoc]
        simpa only [Category.assoc] using c.condition))
      (fun c => ?_) (fun c => ?_) (fun c m hm₁ hm₂ => ?_)
    · rw [← Category.assoc, PullbackCone.IsLimit.lift_fst, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · rw [← Category.assoc, PullbackCone.IsLimit.lift_snd, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · refine PullbackCone.IsLimit.hom_ext h.isLimit ?_ ?_
      · rw [PullbackCone.IsLimit.lift_fst, ← hm₁, Category.assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
      · rw [PullbackCone.IsLimit.lift_snd, ← hm₂, Category.assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
  t := h.t ≫ e.inv
  transitivity₁ := by
    simp only [PullbackCone.mk_fst]
    exact assoc_inv_hom_comp e h.t h.c.fst p₁ h.transitivity₁
  transitivity₂ := by
    simp only [PullbackCone.mk_snd]
    exact assoc_inv_hom_comp e h.t h.c.snd p₂ h.transitivity₂

omit [HasBinaryProducts C] in
/-- Transport the property of being an internal equivalence relation along an isomorphism of the
relation object. -/
theorem isEquivalenceRelation_of_iso {R R' Y : C} {p₁ p₂ : R ⟶ Y}
    [h : IsEquivalenceRelation p₁ p₂] (e : R' ≅ R) :
    IsEquivalenceRelation (e.hom ≫ p₁) (e.hom ≫ p₂) :=
  ⟨⟨equivalenceRelationOfIso h.nonempty_equivalenceRelation.some e⟩⟩

end Transport

section Assemble

/-- The category `Over S` of schemes over `S` has binary products. -/
instance : HasBinaryProducts (Over S) := hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- Pushing a slice forward along the inclusion of the site into schemes preserves pullbacks. -/
instance postPreservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := B.obj hS) B.inclusion) := by
  have _ : PreservesLimitsOfShape WalkingCospan
      (Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S) := by
    change PreservesLimitsOfShape WalkingCospan
      (Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget (B.inclusion.obj (B.obj hS)))
    rw [Over.post_forget_eq_forget_comp B.inclusion (B.obj hS)]
    exact preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- Pushing a slice forward along the inclusion of the site into schemes preserves the terminal
object, the identity of the base being sent to the identity of its image. -/
instance postPreservesTerminal :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (Over.post (X := B.obj hS) B.inclusion) := by
  have h : IsTerminal ((Over.post (X := B.obj hS) B.inclusion).obj
      (Over.mk (𝟙 (B.obj hS)))) := by
    change IsTerminal (Over.mk (B.inclusion.map (𝟙 (B.obj hS))))
    rw [B.inclusion.map_id]
    exact Over.mkIdTerminal
  have _ : PreservesLimit (Functor.empty.{0} (Over (B.obj hS)))
      (Over.post (X := B.obj hS) B.inclusion) :=
    preservesLimit_of_preserves_limit_cone Over.mkIdTerminal
      ((isLimitMapConeEmptyConeEquiv _ _).symm h)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- Pushing a slice forward along the inclusion of the site into schemes preserves binary
products. -/
instance postPreservesProducts :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (Over.post (X := B.obj hS) B.inclusion) :=
  preservesBinaryProducts_of_preservesTerminal_and_pullbacks _

/-- The restricted relation sits in the cartesian square exhibiting it as the restriction of the
relation of the presentation along the residue-field cover. -/
theorem isPullback_residueRelation (P : Presentation B S hS X hX) (x : points B S hS X) :
    IsPullback (prod.lift (residueRelationTarget B S hS P x)
        (residueRelationSource B S hS P x))
      (pullback.snd (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
        (prod.lift P.target P.source))
      (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
      (prod.lift P.target P.source) := by
  have hpair : prod.lift (residueRelationTarget B S hS P x)
      (residueRelationSource B S hS P x) =
      pullback.fst (prod.map (residueSiteHom B S hS P x) (residueSiteHom B S hS P x))
        (prod.lift P.target P.source) :=
    prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)
  rw [hpair]
  exact IsPullback.of_hasPullback _ _

/-- The restricted relation is étale: this is where the hypothesis that the cover is a
monomorphism from a disjoint union of spectra of fields is used. -/
instance isEtaleEquivalenceRelation_residueRelation (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    IsEtaleEquivalenceRelation (relation B S hS (residueRelationSource B S hS P x)
      (residueRelationTarget B S hS P x)) := by
  set H := Over.post (X := B.obj hS) B.inclusion with hH
  set g := residueSiteHom B S hS P x with hg
  set j : PreRelation (H.obj P.R) (H.obj P.U) := relation B S hS P.source P.target with hj
  have hjdef : j = prod.lift (H.map P.target) (H.map P.source) := rfl
  have hpOver := isPullback_map_restriction H P.target P.source
    (residueRelationTarget B S hS P x) (residueRelationSource B S hS P x) g _
    (isPullback_residueRelation B S hS P x)
  rw [← hjdef] at hpOver
  set e := hpOver.isoPullback with he
  have hefst : e.hom ≫ AlgebraicGeometry.PreRelation.restrict j (H.map g) =
      prod.lift (H.map (residueRelationTarget B S hS P x))
        (H.map (residueRelationSource B S hS P x)) :=
    hpOver.isoPullback_hom_fst
  have htgt : e.hom ≫ PreRelation.target
      (AlgebraicGeometry.PreRelation.restrict j (H.map g)) =
      H.map (residueRelationTarget B S hS P x) := by
    rw [PreRelation.target, ← Category.assoc, hefst, prod.lift_fst]
  have hsrc : e.hom ≫ PreRelation.source
      (AlgebraicGeometry.PreRelation.restrict j (H.map g)) =
      H.map (residueRelationSource B S hS P x) := by
    rw [PreRelation.source, ← Category.assoc, hefst, prod.lift_snd]
  have hequiv : IsEquivalenceRelation
      (H.map (residueRelationTarget B S hS P x))
      (H.map (residueRelationSource B S hS P x)) := by
    rw [← htgt, ← hsrc]
    have _ : IsEquivalenceRelation (PreRelation.target j) (PreRelation.source j) :=
      P.isEtaleEquivalenceRelation.isEquivalenceRelation
    exact isEquivalenceRelation_of_iso e
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [show PreRelation.target (relation B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) =
        H.map (residueRelationTarget B S hS P x) from prod.lift_fst _ _,
      show PreRelation.source (relation B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) =
        H.map (residueRelationSource B S hS P x) from prod.lift_snd _ _]
    exact hequiv
  · rw [show PreRelation.source (relation B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) =
        H.map (residueRelationSource B S hS P x) from prod.lift_snd _ _]
    exact etale_residueRelationSource B S hS P x
  · rw [show PreRelation.target (relation B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) =
        H.map (residueRelationTarget B S hS P x) from prod.lift_fst _ _]
    exact etale_residueRelationTarget B S hS P x

end Assemble

section QuotientMono

variable {T : Scheme.{u}} {C : Type*} [Category.{u} C]
  (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over T)

open AlgebraicGeometry.PreRelation

/-- The quotient-presheaf map attached to an isomorphism of pre-relations over a fixed base
object, in the direction of the isomorphism. -/
private noncomputable def quotientPresheafMapOfIso {R R' U : Over T}
    {j : PreRelation R U} {j' : PreRelation R' U} (e : R' ≅ R) (he : e.hom ≫ j = j') :
    Stacks.Groupoids.quotientPresheaf F j' ⟶ Stacks.Groupoids.quotientPresheaf F j :=
  Stacks.Groupoids.quotientPresheafMap F j' j e.hom (𝟙 U)
    (by rw [PreRelation.source, ← Category.assoc, he, Category.comp_id])
    (by rw [PreRelation.target, ← Category.assoc, he, Category.comp_id])

/-- The map of quotient presheaves induced by a morphism of pre-relations commutes with the
canonical projections. -/
private theorem toQuotientPresheaf_quotientPresheafMap {R U R' U' : Over T}
    (j : PreRelation R U) (j' : PreRelation R' U') (r : R ⟶ R') (f : U ⟶ U') (hs) (ht) :
    Stacks.Groupoids.toQuotientPresheaf F j ≫
        Stacks.Groupoids.quotientPresheafMap F j j' r f hs ht =
      F.op.whiskerLeft (yoneda.map f) ≫ Stacks.Groupoids.toQuotientPresheaf F j' :=
  coequalizer.π_desc _ _

/-- The map of quotient presheaves induced by an isomorphism of pre-relations over a fixed base
object is the identity on the canonical projections. -/
private theorem toQuotientPresheaf_quotientPresheafMapOfIso {R R' U : Over T}
    {j : PreRelation R U} {j' : PreRelation R' U} (e : R' ≅ R) (he : e.hom ≫ j = j') :
    Stacks.Groupoids.toQuotientPresheaf F j' ≫ quotientPresheafMapOfIso F e he =
      Stacks.Groupoids.toQuotientPresheaf F j := by
  rw [quotientPresheafMapOfIso, toQuotientPresheaf_quotientPresheafMap F j' j e.hom (𝟙 U)]
  simp

/-- An isomorphism of pre-relations over a fixed base object induces an isomorphism of quotient
presheaves. -/
private theorem isIso_quotientPresheafMapOfIso {R R' U : Over T}
    {j : PreRelation R U} {j' : PreRelation R' U} (e : R' ≅ R) (he : e.hom ≫ j = j') :
    IsIso (quotientPresheafMapOfIso F e he) := by
  have he' : e.inv ≫ j' = j := by rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨quotientPresheafMapOfIso F e.symm he', ?_, ?_⟩
  · refine coequalizer.hom_ext ?_
    rw [← Category.assoc, toQuotientPresheaf_quotientPresheafMapOfIso F e he,
      toQuotientPresheaf_quotientPresheafMapOfIso F e.symm he']
    exact (Category.comp_id _).symm
  · refine coequalizer.hom_ext ?_
    rw [← Category.assoc, toQuotientPresheaf_quotientPresheafMapOfIso F e.symm he',
      toQuotientPresheaf_quotientPresheafMapOfIso F e he]
    exact (Category.comp_id _).symm

/-- **Stacks 045Z, injectivity, at a restriction square.** If a pre-relation `j'` on `U'`
exhibits the restriction of a pre-equivalence relation `j` on `U` along `g : U' ⟶ U`, in the
sense that the square with sides `j'`, `r`, `g × g` and `j` is cartesian, then the induced map
of quotient sheaves `U'/R' ⟶ U/R` is a monomorphism. -/
@[sga "3 IV 4.4.10" "Monomorphism clause"]
theorem mono_quotientSheafMap_of_isPullback {R U R' U' : Over T}
    (j : PreRelation R U) (j' : PreRelation R' U') (r : R' ⟶ R) (g : U' ⟶ U) (hs) (ht)
    (hpb : IsPullback j' r (prod.map g g) j) (hj : IsPreEquivalenceRelation j) :
    Mono (Stacks.Groupoids.quotientSheafMap J F j' j r g hs ht) := by
  set e := hpb.isoPullback with hedef
  have he : e.hom ≫ AlgebraicGeometry.PreRelation.restrict j g = j' :=
    hpb.isoPullback_hom_fst
  obtain ⟨hsrest, htrest⟩ :=
    comm_source_target_of_isPullback (IsPullback.of_hasPullback (prod.map g g) j)
  have hfac : Stacks.Groupoids.quotientPresheafMap F j' j r g hs ht =
      quotientPresheafMapOfIso F e he ≫
        Stacks.Groupoids.quotientPresheafMap F
          (AlgebraicGeometry.PreRelation.restrict j g) j
          (pullback.snd (prod.map g g) j) g hsrest htrest := by
    refine coequalizer.hom_ext ?_
    rw [toQuotientPresheaf_quotientPresheafMap F j' j r g, ← Category.assoc,
      toQuotientPresheaf_quotientPresheafMapOfIso F e he,
      toQuotientPresheaf_quotientPresheafMap F _ j (pullback.snd (prod.map g g) j) g]
  have _ : IsIso (quotientPresheafMapOfIso F e he) := isIso_quotientPresheafMapOfIso F e he
  have _ : Mono (Stacks.Groupoids.restrictQuotientSheafMap J F j g) :=
    Stacks.Groupoids.restrictQuotientSheafMap_mono J F j g hj
  have hmap : Stacks.Groupoids.quotientSheafMap J F j' j r g hs ht =
      (presheafToSheaf J (Type u)).map (quotientPresheafMapOfIso F e he) ≫
        Stacks.Groupoids.restrictQuotientSheafMap J F j g := by
    change (presheafToSheaf J (Type u)).map
      (Stacks.Groupoids.quotientPresheafMap F j' j r g hs ht) = _
    rw [hfac, Functor.map_comp]
    rfl
  rw [hmap]
  infer_instance

end QuotientMono

section QuotientIso

/-- A fully faithful functor identifies the presheaf represented by an object with the
restriction along it of the presheaf represented by its image. -/
noncomputable def yonedaIsoRestrict {C D : Type*} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) [G.Full] [G.Faithful] (A : C) :
    yoneda.obj A ≅ G.op ⋙ yoneda.obj (G.obj A) :=
  NatIso.ofComponents
    (fun _ => ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv).toIso)
    (by intros; ext; simp)

/-- Naturality of the identification of represented presheaves along a fully faithful functor. -/
theorem yonedaIsoRestrict_naturality {C D : Type*} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) [G.Full] [G.Faithful] {A A' : C} (f : A ⟶ A') :
    yoneda.map f ≫ (yonedaIsoRestrict G A').hom =
      (yonedaIsoRestrict G A).hom ≫ G.op.whiskerLeft (yoneda.map (G.map f)) := by
  ext
  exact G.map_comp _ _

/-- Naturality of the inverse of the identification of represented presheaves along a fully
faithful functor. -/
theorem yonedaIsoRestrict_inv_naturality {C D : Type*} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) [G.Full] [G.Faithful] {A A' : C} (f : A ⟶ A') :
    G.op.whiskerLeft (yoneda.map (G.map f)) ≫ (yonedaIsoRestrict G A').inv =
      (yonedaIsoRestrict G A).inv ≫ yoneda.map f := by
  refine (cancel_epi (yonedaIsoRestrict G A).hom).1 ?_
  rw [← Category.assoc, ← yonedaIsoRestrict_naturality]
  simp

variable {R U : BigFppfOver B S hS}

/-- The identification of represented presheaves is the Yoneda transpose of the identity. -/
theorem yonedaIsoRestrict_hom_eq (A : BigFppfOver B S hS) :
    (yonedaIsoRestrict (Over.post (X := B.obj hS) B.inclusion) A).hom =
      yonedaEquiv.symm (𝟙 ((Over.post (X := B.obj hS) B.inclusion).obj A)) := rfl

/-- The quotient map of Stacks 02WW is the identification of represented presheaves followed by
the canonical projection onto the quotient sheaf. -/
theorem quotientMap_eq (s t : R ⟶ U) :
    quotientMap B S hS s t =
      (yonedaIsoRestrict (Over.post (X := B.obj hS) B.inclusion) U).hom ≫
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) := by
  rw [yonedaIsoRestrict_hom_eq]
  exact (yonedaEquiv_symm_naturality_right U
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)) (𝟙 _)).symm

/-- Two maps out of a quotient sheaf agree as soon as they agree after the canonical
projection. This is `Stacks.Groupoids.quotientSheaf_hom_ext` at the big fppf site of `S`. -/
private theorem quotientSheaf_hom_ext {R' U' : Over S}
    (j : PreRelation R' U')
    {A : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {a b : Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) j ⟶ A}
    (h : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j ≫ a.hom =
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j ≫ b.hom) : a = b :=
  Stacks.Groupoids.quotientSheaf_hom_ext (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) j A a b h

include hX in
/-- **Stacks 02VH.** The quotient sheaf of the kernel-pair relation of a surjective étale
atlas is the algebraic space itself. -/
theorem exists_quotientSheaf_iso (a : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hp : IsPullback (yoneda.map t) (yoneda.map s) a a)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ e : (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj ≅ X,
      quotientMap B S hS s t ≫ e.hom = a := by
  set J := BigFppfOver.topology B S hS with hJ
  set H := Over.post (X := B.obj hS) B.inclusion with hH
  set j := relation B S hS s t with hjdef
  set p := Stacks.Groupoids.toQuotientSheaf J H j with hp'
  set q : yoneda.obj U ⟶ (Stacks.Groupoids.quotientSheaf J H j).obj :=
    (yonedaIsoRestrict H U).hom ≫ p with hq
  set XF : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩ with hXF
  have hjs : PreRelation.source j = H.map s := prod.lift_snd _ _
  have hjt : PreRelation.target j = H.map t := prod.lift_fst _ _
  have hw : Stacks.Groupoids.sourceMap H j ≫ ((yonedaIsoRestrict H U).inv ≫ a) =
      Stacks.Groupoids.targetMap H j ≫ ((yonedaIsoRestrict H U).inv ≫ a) := by
    rw [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, hjs, hjt,
      ← Category.assoc, ← Category.assoc, yonedaIsoRestrict_inv_naturality,
      yonedaIsoRestrict_inv_naturality, Category.assoc, Category.assoc, hp.w]
  set d : Stacks.Groupoids.quotientSheaf J H j ⟶ XF :=
    Stacks.Groupoids.quotientSheafDesc J H j XF ((yonedaIsoRestrict H U).inv ≫ a) hw with hd'
  have hd : p ≫ d.hom = (yonedaIsoRestrict H U).inv ≫ a :=
    Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc J H j XF _ hw
  have hqd : q ≫ d.hom = a := by
    rw [hq, Category.assoc, hd, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hqst : yoneda.map t ≫ q = yoneda.map s ≫ q := by
    have hst : H.op.whiskerLeft (yoneda.map (H.map t)) ≫ p =
        H.op.whiskerLeft (yoneda.map (H.map s)) ≫ p := by
      have h0 := (Stacks.Groupoids.sourceMap_toQuotientSheaf J H j).symm
      rwa [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap, hjs, hjt] at h0
    calc yoneda.map t ≫ q
        = (yoneda.map t ≫ (yonedaIsoRestrict H U).hom) ≫ p := by
          rw [hq, Category.assoc]
      _ = ((yonedaIsoRestrict H R).hom ≫
            H.op.whiskerLeft (yoneda.map (H.map t))) ≫ p := by
          rw [yonedaIsoRestrict_naturality]
      _ = (yonedaIsoRestrict H R).hom ≫
            (H.op.whiskerLeft (yoneda.map (H.map t)) ≫ p) := Category.assoc _ _ _
      _ = (yonedaIsoRestrict H R).hom ≫
            (H.op.whiskerLeft (yoneda.map (H.map s)) ≫ p) := by rw [hst]
      _ = ((yonedaIsoRestrict H R).hom ≫
            H.op.whiskerLeft (yoneda.map (H.map s))) ≫ p := (Category.assoc _ _ _).symm
      _ = (yoneda.map s ≫ (yonedaIsoRestrict H U).hom) ≫ p := by
          rw [yonedaIsoRestrict_naturality]
      _ = yoneda.map s ≫ q := by rw [hq, Category.assoc]
  obtain ⟨hR, hU, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS a t s hp hX hsurj hetale
  set UF : Sheaf J (Type u) := ⟨yoneda.obj U, hU⟩ with hUF
  set c : XF ⟶ Stacks.Groupoids.quotientSheaf J H j :=
    Cofork.IsColimit.desc hc (⟨q⟩ : UF ⟶ _) (Sheaf.hom_ext hqst) with hc'
  have hac : a ≫ c.hom = q :=
    congrArg (fun z : UF ⟶ Stacks.Groupoids.quotientSheaf J H j => z.hom)
      (Cofork.IsColimit.π_desc' hc (⟨q⟩ : UF ⟶ _) _)
  have hcd : c ≫ d = 𝟙 XF := by
    refine Cofork.IsColimit.hom_ext hc (Sheaf.hom_ext ?_)
    change a ≫ c.hom ≫ d.hom = a ≫ 𝟙 X
    rw [← Category.assoc, hac, hqd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 (Stacks.Groupoids.quotientSheaf J H j) := by
    refine quotientSheaf_hom_ext B S hS j ?_
    change p ≫ d.hom ≫ c.hom =
      p ≫ (𝟙 (Stacks.Groupoids.quotientSheaf J H j) :
        Stacks.Groupoids.quotientSheaf J H j ⟶
          Stacks.Groupoids.quotientSheaf J H j).hom
    rw [← Category.assoc, hd, Category.assoc, hac, hq, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
    exact (Category.comp_id p).symm
  refine ⟨(sheafToPresheaf J (Type u)).mapIso ⟨d, c, hdc, hcd⟩, ?_⟩
  rw [quotientMap_eq]
  exact hqd

end QuotientIso

section Points

/-- Every point of the residue-field coproduct maps into the fibre of the presenting scheme over
`x`. -/
theorem residueCoproductHom_mem_atlasFibre (P : Presentation B S hS X hX)
    (x : points B S hS X) (z : residueCoproduct B S hS P x) :
    residueCoproductHom B S hS P x z ∈ atlasFibre B S hS P x := by
  obtain ⟨⟨i, w⟩, rfl⟩ := (sigmaMk fun y : atlasFibre B S hS P x =>
    Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1))).surjective z
  rw [sigmaMk_mk]
  change (Sigma.ι _ i ≫ residueCoproductHom B S hS P x) w ∈ atlasFibre B S hS P x
  rw [residueCoproductHom, Sigma.ι_comp_desc]
  rw [Scheme.fromSpecResidueField_apply]
  exact i.2

/-- Every point of the residue-field cover maps to `x` in the algebraic space. -/
theorem pointsMap_residueSiteHom_eq (P : Presentation B S hS X hX)
    (x : points B S hS X) (w : points B S hS (yoneda.obj (residueSite B S hS P x))) :
    pointsMap B S hS (yoneda.obj P.U) P.toSpace
      (pointsMap B S hS (yoneda.obj (residueSite B S hS P x))
        (yoneda.map (residueSiteHom B S hS P x)) w) = x := by
  set v := pointsMap B S hS (yoneda.obj (residueSite B S hS P x))
    (yoneda.map (residueSiteHom B S hS P x)) w with hv
  have hsp : pointsToScheme B S hS P.U v =
      residueCoproductHom B S hS P x (pointsToScheme B S hS
        (residueSite B S hS P x) w) := by
    rw [hv, pointsToScheme_pointsMap, residueSiteHom_toScheme]
    rfl
  have hmem : pointsToScheme B S hS P.U v ∈ atlasFibre B S hS P x := by
    rw [hsp]
    exact residueCoproductHom_mem_atlasFibre B S hS P x _
  have hback : (pointsEquivScheme B S hS P.U).symm
      (pointsToScheme B S hS P.U v) = v :=
    (pointsEquivScheme B S hS P.U).symm_apply_apply v
  rw [← hback]
  exact hmem

/-- The fibre of the presenting scheme over `x` is nonempty, the atlas being surjective on
points. -/
theorem nonempty_atlasFibre (P : Presentation B S hS X hX) (x : points B S hS X) :
    Nonempty (atlasFibre B S hS P x) := by
  obtain ⟨w, hw⟩ := P.pointsMap_surjective x
  refine ⟨⟨pointsToScheme B S hS P.U w, ?_⟩⟩
  change pointsMap B S hS (yoneda.obj P.U) P.toSpace
    ((pointsEquivScheme B S hS P.U).symm (pointsToScheme B S hS P.U w)) = x
  rw [show (pointsEquivScheme B S hS P.U).symm (pointsToScheme B S hS P.U w) = w from
    (pointsEquivScheme B S hS P.U).symm_apply_apply w]
  exact hw

/-- The residue-field cover of the fibre over `x` is nonempty. -/
theorem nonempty_residueSite (P : Presentation B S hS X hX) (x : points B S hS X) :
    Nonempty ((BigFppfOver.toScheme B S hS).obj (residueSite B S hS P x)) := by
  obtain ⟨y⟩ := nonempty_atlasFibre B S hS P x
  exact ⟨Sigma.ι (fun y : atlasFibre B S hS P x =>
    Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1))) y
      (IsLocalRing.closedPoint ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1))⟩

/-- The residue-field cover is reduced, being a disjoint union of spectra of fields. -/
theorem isReduced_residueSite (P : Presentation B S hS X hX) (x : points B S hS X) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj (residueSite B S hS P x)) := by
  change IsReduced (∐ fun y : atlasFibre B S hS P x =>
    Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)))
  rw [IsReduced.iff_of_openCover _ (sigmaOpenCover _)]
  intro y
  change IsReduced (Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)))
  infer_instance

/-- The residue-field cover is locally Noetherian, being a disjoint union of spectra of fields. -/
theorem isLocallyNoetherian_residueSite (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (residueSite B S hS P x)) := by
  change IsLocallyNoetherian (∐ fun y : atlasFibre B S hS P x =>
    Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)))
  rw [isLocallyNoetherian_iff_openCover (sigmaOpenCover _)]
  intro y
  change IsLocallyNoetherian
    (Spec (.of ↥(((BigFppfOver.toScheme B S hS).obj P.U).residueField y.1)))
  infer_instance

end Points

section Main

/-- The residual space at `x`: the quotient of the residue-field cover of the fibre over `x`
by the restricted relation. -/
noncomputable abbrev residualSpaceAt (P : Presentation B S hS X hX)
    (x : points B S hS X) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
    (relation B S hS (residueRelationSource B S hS P x)
      (residueRelationTarget B S hS P x))).obj

include hX in
/-- **Stacks 02VH.** The quotient of the residue-field cover by the restricted relation maps
monomorphically to the algebraic space, compatibly with the quotient map.

The restricted relation is the restriction of the relation of the presentation along the
residue-field cover, so the induced map of quotient sheaves is injective by Stacks 045Z; the
quotient of the presentation is the algebraic space itself by Stacks 02VH. -/
theorem exists_mono_to_space (P : Presentation B S hS X hX) (x : points B S hS X) :
    ∃ d : residualSpaceAt B S hS P x ⟶ X, Mono d ∧
      quotientMap B S hS (residueRelationSource B S hS P x)
          (residueRelationTarget B S hS P x) ≫ d =
        yoneda.map (residueSiteHom B S hS P x) ≫ P.toSpace := by
  set J := BigFppfOver.topology B S hS with hJ
  set H := Over.post (X := B.obj hS) B.inclusion with hH
  set g := residueSiteHom B S hS P x with hg
  set t' := residueRelationTarget B S hS P x with ht'
  set s' := residueRelationSource B S hS P x with hs'
  set j : PreRelation (H.obj P.R) (H.obj P.U) := relation B S hS P.source P.target with hjd
  set j' : PreRelation (H.obj (residueRelation B S hS P x)) (H.obj (residueSite B S hS P x)) :=
    relation B S hS s' t' with hj'd
  set r : residueRelation B S hS P x ⟶ P.R :=
    pullback.snd (prod.map g g) (prod.lift P.target P.source) with hr
  have hpb : IsPullback j' (H.map r) (prod.map (H.map g) (H.map g)) j :=
    isPullback_map_restriction H P.target P.source t' s' g r
      (isPullback_residueRelation B S hS P x)
  obtain ⟨hs, ht⟩ := comm_source_target_of_isPullback hpb
  have hjpre : IsPreEquivalenceRelation j := by
    have hequiv : IsEquivalenceRelation (PreRelation.target j) (PreRelation.source j) :=
      P.isEtaleEquivalenceRelation.isEquivalenceRelation
    rw [isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation] at hequiv
    exact hequiv.2
  set m := Stacks.Groupoids.quotientSheafMap J H j' j (H.map r) (H.map g) hs ht with hm
  have hmono : Mono m := mono_quotientSheafMap_of_isPullback J H j j' (H.map r) (H.map g)
    hs ht hpb hjpre
  have hmh : Mono m.hom := inferInstance
  obtain ⟨e, he⟩ := exists_quotientSheaf_iso (hX := hX) B S hS P.toSpace P.source P.target
    P.isPullback P.surjective P.etale
  have hsmall : quotientMap B S hS s' t' ≫ m.hom =
      yoneda.map g ≫ quotientMap B S hS P.source P.target :=
    calc quotientMap B S hS s' t' ≫ m.hom
        = ((yonedaIsoRestrict H (residueSite B S hS P x)).hom ≫
            Stacks.Groupoids.toQuotientSheaf J H j') ≫ m.hom := by
          rw [quotientMap_eq]
      _ = (yonedaIsoRestrict H (residueSite B S hS P x)).hom ≫
            (Stacks.Groupoids.toQuotientSheaf J H j' ≫ m.hom) := Category.assoc _ _ _
      _ = (yonedaIsoRestrict H (residueSite B S hS P x)).hom ≫
            (H.op.whiskerLeft (yoneda.map (H.map g)) ≫
              Stacks.Groupoids.toQuotientSheaf J H j) := by
          rw [hm, Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap]
      _ = ((yonedaIsoRestrict H (residueSite B S hS P x)).hom ≫
            H.op.whiskerLeft (yoneda.map (H.map g))) ≫
              Stacks.Groupoids.toQuotientSheaf J H j := (Category.assoc _ _ _).symm
      _ = (yoneda.map g ≫ (yonedaIsoRestrict H P.U).hom) ≫
            Stacks.Groupoids.toQuotientSheaf J H j := by
          rw [yonedaIsoRestrict_naturality]
      _ = yoneda.map g ≫ quotientMap B S hS P.source P.target := by
          rw [quotientMap_eq, Category.assoc]
  have hem : Mono e.hom := IsIso.mono_of_iso e.hom
  have hdmono : Mono (m.hom ≫ e.hom) := @mono_comp _ _ _ _ _ m.hom hmh e.hom hem
  refine ⟨m.hom ≫ e.hom, hdmono, ?_⟩
  calc quotientMap B S hS s' t' ≫ (m.hom ≫ e.hom)
      = (quotientMap B S hS s' t' ≫ m.hom) ≫ e.hom := (Category.assoc _ _ _).symm
    _ = (yoneda.map g ≫ quotientMap B S hS P.source P.target) ≫ e.hom := by rw [hsmall]
    _ = yoneda.map g ≫ (quotientMap B S hS P.source P.target ≫ e.hom) :=
        Category.assoc _ _ _
    _ = yoneda.map g ≫ P.toSpace := by rw [he]

include hX in
/-- **Stacks 06QZ, existence**, in the form given by a chosen presentation. -/
theorem exists_isResidualSpaceAt_of_presentation (P : Presentation B S hS X hX)
    (x : points B S hS X) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : Z ⟶ X), IsResidualSpaceAt B S hS X x f := by
  have hZalg : IsAlgebraicSpace B S hS (residualSpaceAt B S hS P x) :=
    isAlgebraicSpace_quotient_unconditional B S hS (residueRelationSource B S hS P x)
      (residueRelationTarget B S hS P x)
  have hqsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (quotientMap B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) :=
    quotientMap_surjective_unconditional B S hS (residueRelationSource B S hS P x)
      (residueRelationTarget B S hS P x)
  have hqetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (quotientMap B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) :=
    quotientMap_etale_unconditional B S hS (residueRelationSource B S hS P x)
      (residueRelationTarget B S hS P x)
  obtain ⟨d, hdmono, hqd⟩ := exists_mono_to_space B S hS P x
  have hqpoints : Function.Surjective (pointsMap B S hS
      (yoneda.obj (residueSite B S hS P x))
      (quotientMap B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x))) :=
    (surjective_iff_surjective_pointsMap B S hS (residualSpaceAt B S hS P x) hZalg
      (residueSite B S hS P x) _).mp hqsurj
  have hall : ∀ z : points B S hS (residualSpaceAt B S hS P x),
      pointsMap B S hS (residualSpaceAt B S hS P x) d z = x := by
    intro z
    obtain ⟨w, rfl⟩ := hqpoints z
    have h := pointsMap_comp_apply B S hS
      (quotientMap B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x)) d w
    rw [hqd] at h
    rw [← h, pointsMap_comp_apply]
    exact pointsMap_residueSiteHom_eq B S hS P x w
  refine ⟨residualSpaceAt B S hS P x, d, hZalg, hdmono,
    ⟨residueSite B S hS P x, _, hqsurj, hqetale, isReduced_residueSite B S hS P x⟩,
    ⟨residueSite B S hS P x, _, hqsurj, hqetale,
      isLocallyNoetherian_residueSite B S hS P x⟩, ?_, ?_, hall⟩
  · obtain ⟨z⟩ := nonempty_residueSite B S hS P x
    exact ⟨pointsMap B S hS (yoneda.obj (residueSite B S hS P x))
      (quotientMap B S hS (residueRelationSource B S hS P x)
        (residueRelationTarget B S hS P x))
      ((pointsEquivScheme B S hS (residueSite B S hS P x)).symm z)⟩
  · exact ⟨fun z₁ z₂ => pointsMap_injective_of_mono B S hS d
      ((hall z₁).trans (hall z₂).symm)⟩

/-- **Stacks 06QZ, existence.** Every point of an algebraic space carries a residual space:
a monomorphism from a reduced, locally Noetherian algebraic space with exactly one point,
whose image on points is that point. -/
@[stacks 06QZ "existence"]
theorem exists_isResidualSpaceAt (hXalg : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : Z ⟶ X),
      IsResidualSpaceAt B S hS X x f :=
  exists_isResidualSpaceAt_of_presentation B S hS
    (presentationOfIsAlgebraicSpace B S hS X hXalg) x

end Main

end Space

end AlgebraicGeometry

end
