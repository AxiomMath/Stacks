module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteCoproductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeDescentAlongAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentationQuotients
public import StacksFrontier.Topology.Algebra.AdicTopology.DescentNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactFiniteRefinement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteFormalAtlas

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer`

A representable étale morphism of fppf sheaves is representable flat; for a surjective flat
morphism of affine formal algebraic spaces representable by algebraic spaces, every presenting
ring of the target is related to every presenting ring of the source by a continuous taut
homomorphism with faithfully flat maps on quotients by open ideals; and Stacks 0AKX holds for the
countably indexed and classical, weakly adic, adic\* and Noetherian properties. A primed name `X'`
is a variant of the declaration `X` of `StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasTautFaithfullyFlatPresentation'`: every presenting ring of
  the target of a surjective flat morphism of affine formal algebraic spaces representable by
  algebraic spaces is related to every presenting ring of the source by a continuous taut
  homomorphism with faithfully flat maps on quotients by open ideals.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRepresentableEtale.isRepresentableFlat`: a representable
  étale morphism of fppf sheaves is representable flat.
* `AlgebraicGeometry.FormalSpace.hasTautFaithfullyFlatPresentation`:
  `HasTautFaithfullyFlatPresentation'` holds.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleRefinementWithProperty`: the refinement step of
  Stacks 0AKX for a property which descends along representable étale morphisms and is stable
  under finite disjoint unions.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty'`:
  Stacks 0AKX for such a property which moreover transfers along surjective flat morphisms.
* `AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic_unconditional`
  and its variants for the countably indexed and classical, adic\* and Noetherian properties:
  Stacks 0AKX for these properties.

## References

* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable étale morphism of fppf sheaves is representable flat. -/
theorem IsRepresentableEtale.isRepresentableFlat {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsRepresentableEtale B S hS f) : IsRepresentableFlat B S hS f :=
  ⟨hf.1, hasPropertyULift_flat_of_isEtale B S hS f.hom hf.1 hf.2⟩

/-- For every surjective flat morphism of affine formal algebraic spaces over `S` representable
by algebraic spaces, every presenting ring `C` of the source and every presenting ring `A` of the
target are related by a continuous taut homomorphism `A → C` all of whose maps on quotients by
open ideals are faithfully flat.

It differs from `AlgebraicGeometry.FormalSpace.HasTautFaithfullyFlatPresentation`, which asks
for one presenting ring of the target with such a homomorphism, in quantifying over every
presenting ring of the target. -/
def HasTautFaithfullyFlatPresentation' : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y),
    IsAffineFormalAlgebraicSpace B S hS X → IsAffineFormalAlgebraicSpace B S hS Y →
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom →
    IsSurjective B S hS f → IsRepresentableFlat B S hS f →
    ∀ (C : Type u) (_ : CommRing C) (_ : TopologicalSpace C) (_ : IsTopologicalRing C)
      (_ : IsLinearTopology C C), IsPresentingRing B S hS C X →
    ∀ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A), IsPresentingRing B S hS A Y →
    ∃ φ : A →+* C, Continuous φ ∧ RingHom.IsTaut φ ∧ HasFaithfullyFlatQuotients φ

/-- `AlgebraicGeometry.FormalSpace.HasTautFaithfullyFlatPresentation'` holds: for a surjective
flat morphism of affine formal algebraic spaces representable by algebraic spaces, any presenting
rings of the target and of the source are related by a continuous taut homomorphism with
faithfully flat maps on quotients by open ideals. -/
theorem hasTautFaithfullyFlatPresentation : HasTautFaithfullyFlatPresentation' B S hS := by
  rintro X Y f - hY - hsurj hflat C _ _ _ _ hC A _ _ _ _ hA
  exact exists_taut_faithfullyFlatQuotients_of_surjective_flat B S hS f hY hsurj hflat hC hA

/-- The target of a surjective flat morphism representable by algebraic spaces with countably
indexed source is countably indexed and McQuillan, and has a presenting ring. -/
private theorem isCountablyIndexed_and_isPresentingRing_target {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsurj : IsSurjective B S hS f) (hflat : IsRepresentableFlat B S hS f)
    (hXc : IsCountablyIndexed B S hS X) :
    IsCountablyIndexed B S hS Y ∧ HasSomeSurjectivePresentation B S hS Y ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A Y := by
  have hYc : IsCountablyIndexed B S hS Y :=
    (isCountablyIndexed_iff_of_surjective_flat' B S hS f hX hY hf hsurj hflat).1 hXc
  exact ⟨hYc, isPresentingRing_of_isCountablyIndexed B S hS hY hYc⟩

/-- **The refinement step of Stacks 0AKX.** Let `P` be a property of fppf sheaves which descends
along a representable étale morphism of affine formal algebraic spaces (`hPetale`) and is stable
under finite disjoint unions of affine formal algebraic spaces (`hPsigma`). If `X` has a jointly
surjective family of representable étale morphisms from affine formal algebraic spaces with `P`,
then every affine formal algebraic space `Y` representable étale over `X` receives a morphism
from an affine formal algebraic space with `P` which is representable by algebraic spaces,
surjective, flat and locally of finite type. -/
theorem hasAffineEtaleRefinementWithProperty (P : FppfSheaf B S hS → Prop)
    (hPetale : ∀ {V Z : FppfSheaf B S hS} (v : V ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS V → IsAffineFormalAlgebraicSpace B S hS Z →
      IsRepresentableEtale B S hS v → P Z → P V)
    (hPsigma : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ (K : Type (u + 1)) (Z : K → FppfSheaf B S hS), Finite K →
        (∀ k, IsAffineFormalAlgebraicSpace B S hS (Z k)) → (∀ k, P (Z k)) → P (∐ Z)) :
    HasAffineEtaleRefinementWithProperty B S hS P := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro X I Xi fi hXiaff hXiet hXisurj hXiP Y g hY hg
  have hsndet : ∀ i, IsRepresentableEtale B S hS (pullback.snd (fi i) g) := fun i ↦
    isRepresentableEtale_pullback_snd B S hS (fi i) g (hXiet i)
  have hfstet : ∀ i, IsRepresentableEtale B S hS (pullback.fst (fi i) g) := fun i ↦
    isRepresentableEtale_of_isPullback B S hS (IsPullback.of_hasPullback (fi i) g).flip hg
  have hTi : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (fi i) g) := fun i ↦
    isFormalAlgebraicSpace_of_isRepresentableEtale B S hS (pullback.snd (fi i) g)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hY) (hsndet i)
  choose M V v hVaff hVet hVsurj using fun i ↦ (hTi i).2
  have hwet : ∀ n : Σ i, M i,
      IsRepresentableEtale B S hS (v n.1 n.2 ≫ pullback.snd (fi n.1) g) := fun n ↦
    IsRepresentableEtale.comp B S hS (hVet n.1 n.2) (hsndet n.1)
  have hwsurj : Sheaf.IsLocallySurjective
      (Sigma.desc fun n : Σ i, M i ↦ v n.1 n.2 ≫ pullback.snd (fi n.1) g) :=
    Sheaf.isLocallySurjective_sigmaDesc_comp (fun i ↦ pullback.snd (fi i) g) v
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd g fi hXisurj) hVsurj
  obtain ⟨T, Yred, iY, hTcompact, ⟨eT⟩, hiY⟩ :=
    exists_isReduction_uliftYoneda_of_isAffineFormalAlgebraicSpace B S hS Y hY
  obtain ⟨t, ht⟩ := exists_finite_jointly_surjective_of_isQuasiCompactSpaceULift B S hS hiY
    (Space.isQuasiCompactSpaceULift_of_iso B S hS eT
      (Space.isQuasiCompactSpaceULift_uliftYoneda B S hS T hTcompact)) hwet hwsurj
  have hZaff : ∀ n : {n : Σ i, M i // n ∈ t},
      IsAffineFormalAlgebraicSpace B S hS (V n.1.1 n.1.2) := fun n ↦ hVaff n.1.1 n.1.2
  have hdescet : IsRepresentableEtale B S hS
      (Sigma.desc fun n : {n : Σ i, M i // n ∈ t} ↦
        v n.1.1 n.1.2 ≫ pullback.snd (fi n.1.1) g) :=
    coproductsRepresentableEtale' B S hS {n : Σ i, M i // n ∈ t}
      (fun n ↦ V n.1.1 n.1.2) Y (fun n ↦ v n.1.1 n.1.2 ≫ pullback.snd (fi n.1.1) g)
      inferInstance fun n ↦ hwet n.1
  refine ⟨∐ fun n : {n : Σ i, M i // n ∈ t} ↦ V n.1.1 n.1.2,
    Sigma.desc fun n : {n : Σ i, M i // n ∈ t} ↦ v n.1.1 n.1.2 ≫ pullback.snd (fi n.1.1) g,
    finiteCoproductsAffineFormal' B S hS _ _ inferInstance hZaff,
    hPsigma _ _ inferInstance hZaff (fun n ↦ hPetale (v n.1.1 n.1.2 ≫ pullback.fst (fi n.1.1) g)
      (hZaff n) (hXiaff n.1.1)
      (IsRepresentableEtale.comp B S hS (hVet n.1.1 n.1.2) (hfstet n.1.1)) (hXiP n.1.1)),
    hdescet.1, fun p ↦ ?_, IsRepresentableEtale.isRepresentableFlat B S hS hdescet,
    IsRepresentableEtale.isLocallyOfFiniteType B S hS hdescet⟩
  obtain ⟨n, hnt, y, hy⟩ := ht p
  refine ⟨Space.pointsMapULift.{u + 1} B S hS (V n.1 n.2).obj
    (Sigma.ι (fun n : {n : Σ i, M i // n ∈ t} ↦ V n.1.1 n.1.2) ⟨n, hnt⟩).hom y, ?_⟩
  refine (Space.pointsMapULift_comp_apply B S hS
    (Sigma.ι (fun n : {n : Σ i, M i // n ∈ t} ↦ V n.1.1 n.1.2) ⟨n, hnt⟩).hom
    (Sigma.desc fun n : {n : Σ i, M i // n ∈ t} ↦
      v n.1.1 n.1.2 ≫ pullback.snd (fi n.1.1) g).hom y).symm.trans ?_
  refine Eq.trans (congrArg (Space.pointsMapULift B S hS _ · y) ?_) hy
  rw [← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_comp_desc]

/-- Let `X` be a formal algebraic space over `S` and let `P` be a property of
affine formal algebraic spaces which descends along a morphism representable by algebraic
spaces and étale, is stable under finite disjoint unions, and transfers in both directions
along a surjective flat morphism representable by algebraic spaces and locally of finite type.
Then every affine formal algebraic space representable étale over `X` satisfies `P` if and
only if `X` admits an atlas as in Definition 0AIM all of whose members satisfy `P`. -/
theorem hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty'
    (X : FppfSheaf B S hS) (P : FppfSheaf B S hS → Prop)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hPetale : ∀ {V Z : FppfSheaf B S hS} (v : V ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS V → IsAffineFormalAlgebraicSpace B S hS Z →
      IsRepresentableEtale B S hS v → P Z → P V)
    (hPsigma : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ (K : Type (u + 1)) (Z : K → FppfSheaf B S hS), Finite K →
        (∀ k, IsAffineFormalAlgebraicSpace B S hS (Z k)) → (∀ k, P (Z k)) → P (∐ Z))
    (htransfer : ∀ {W Z : FppfSheaf B S hS} (w : W ⟶ Z),
      IsAffineFormalAlgebraicSpace B S hS W → IsAffineFormalAlgebraicSpace B S hS Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS w.hom →
      IsSurjective B S hS w → IsRepresentableFlat B S hS w →
      IsLocallyOfFiniteType B S hS w → (P W ↔ P Z)) :
    HasAffineEtaleChartProperty B S hS X P ↔
      HasAffineEtaleAtlasWithProperty B S hS X P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, Xi, fi, hXiaff, hXiet, hXisurj⟩ := hX
  refine ⟨fun h ↦ ⟨I, Xi, fi, hXiaff, hXiet, hXisurj,
    fun i ↦ h (Xi i) (fi i) (hXiaff i) (hXiet i)⟩, fun h ↦ ?_⟩
  obtain ⟨J, Zj, gj, hZjaff, hZjet, hZjsurj, hZjP⟩ := h
  intro Y g hY hg
  obtain ⟨W, w, hWaff, hWP, hwrep, hwsurj, hwflat, hwft⟩ :=
    hasAffineEtaleRefinementWithProperty B S hS P hPetale hPsigma J Zj gj hZjaff hZjet
      hZjsurj hZjP Y g hY hg
  exact (htransfer w hWaff hY hwrep hwsurj hwflat hwft).1 hWP

/-- Every affine formal algebraic space representable étale over a formal algebraic space `X` is
countably indexed and classical if and only if `X` admits an atlas as in Definition 0AIM all of
whose members are. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2) for the countably indexed and \
classical property of Stacks 0AIJ and Stacks 0AID, unconditionally. The three conditions on \
the property asked for by `hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty` \
above are, in order, clause (2) of Stacks 0AKQ \
(`isCountablyIndexedAndClassical_of_isRepresentable'`), the passage to a finite disjoint union \
(`isCountablyIndexed_sigma'` and `isClassical_sigma`), and Stacks 0GXR \
(`isCountablyIndexedAndClassical_iff_of_isSurjective_of_isRepresentableFlat`)"]
theorem hasAffineEtaleChartProperty_iff_atlas_isCountablyIndexedAndClassical_unconditional
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasAffineEtaleChartProperty B S hS X
        (fun Y ↦ IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y) ↔
      HasAffineEtaleAtlasWithProperty B S hS X
        (fun Y ↦ IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y) :=
  hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty' B S hS X _ hX
    (fun {_ _} v hV hZ hv hZc ↦
      isCountablyIndexedAndClassical_of_isRepresentable' B S hS v hV hZ hv.1 hZc)
    (fun _ Z hfin _ hZc ↦ have := hfin;
      ⟨isCountablyIndexed_sigma' B S hS Z fun k ↦ (hZc k).1,
        isClassical_sigma B S hS Z fun k ↦ (hZc k).2⟩)
    (fun {_ _} w hW hZ hw hsurj hflat _ ↦
      isCountablyIndexedAndClassical_iff_of_isSurjective_of_isRepresentableFlat
        B S hS w hW hZ hw hsurj hflat)

/-- Every affine formal algebraic space representable étale over a formal algebraic space `X` is
weakly adic if and only if `X` admits an atlas as in Definition 0AIM all of whose members are. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2) for the weakly adic property of \
Stacks 0AID, unconditionally. The three conditions on the property asked for by \
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty` above are, in order, clause \
(3) of Stacks 0AKQ (`isWeaklyAdic_of_isRepresentable'`), the passage to a finite disjoint union \
(`isWeaklyAdic_sigma'`), and Stacks 0GXS (`isWeaklyAdic_iff_of_surjective_flat'`)"]
theorem hasAffineEtaleChartProperty_iff_atlas_isWeaklyAdic_unconditional
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasAffineEtaleChartProperty B S hS X (IsWeaklyAdic B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsWeaklyAdic B S hS) :=
  hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty' B S hS X
    (IsWeaklyAdic B S hS) hX
    (fun {_ _} v hV hZ hv hZc ↦ isWeaklyAdic_of_isRepresentable' B S hS v hV hZ hv.1 hZc)
    (fun _ Z hfin _ hZc ↦ have := hfin; isWeaklyAdic_sigma' B S hS Z hZc)
    (fun {_ _} w hW hZ hw hsurj hflat _ ↦
      isWeaklyAdic_iff_of_surjective_flat' B S hS w hW hZ hw hsurj hflat)

/-- Every affine formal algebraic space representable étale over a formal algebraic space `X` is
adic\* if and only if `X` admits an atlas as in Definition 0AIM all of whose members are. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2) for the adic* property of \
Stacks 0AID, unconditionally. The three conditions on the property asked for by \
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty` above are, in order, clause \
(4) of Stacks 0AKQ (`isAdicStar_of_isRepresentable'`), the passage to a finite disjoint union \
(`isAdicStar_sigma'`), and Stacks 0AKT (`isAdicStar_iff_of_surjective_flat'`)"]
theorem hasAffineEtaleChartProperty_iff_atlas_isAdicStar_unconditional
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasAffineEtaleChartProperty B S hS X (IsAdicStar B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsAdicStar B S hS) :=
  hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty' B S hS X
    (IsAdicStar B S hS) hX
    (fun {_ _} v hV hZ hv hZc ↦ isAdicStar_of_isRepresentable' B S hS v hV hZ hv.1 hZc)
    (fun _ Z hfin _ hZc ↦ have := hfin; isAdicStar_sigma' B S hS Z hZc)
    (fun {_ _} w hW hZ hw hsurj hflat _ ↦
      isAdicStar_iff_of_surjective_flat' B S hS w hW hZ hw hsurj hflat)

/-- Every affine formal algebraic space representable étale over a formal algebraic space `X` is
Noetherian if and only if `X` admits an atlas as in Definition 0AIM all of whose members are. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2) for the Noetherian property of \
Stacks 0AID, unconditionally. The three conditions on the property asked for by \
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty` above are, in order, clause \
(5) of Stacks 0AKQ (`isNoetherian_of_isRepresentable'`, which for this property also uses that \
a representable étale morphism is locally of finite type), the passage to a finite disjoint \
union (`isNoetherian_sigma'`), and Stacks 0AKW \
(`isNoetherian_iff_of_isSurjective_of_isRepresentableFlat`)"]
theorem hasAffineEtaleChartProperty_iff_atlas_isNoetherian_unconditional
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasAffineEtaleChartProperty B S hS X (IsNoetherian B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsNoetherian B S hS) :=
  hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty' B S hS X
    (IsNoetherian B S hS) hX
    (fun {_ _} v hV hZ hv hZc ↦ isNoetherian_of_isRepresentable' B S hS v hV hZ hv.1
      (IsRepresentableEtale.isLocallyOfFiniteType B S hS hv) hZc)
    (fun _ Z hfin _ hZc ↦ have := hfin; isNoetherian_sigma' B S hS Z hZc)
    (fun {_ _} w hW hZ hw hsurj hflat hft ↦
      isNoetherian_iff_of_isSurjective_of_isRepresentableFlat B S hS w hW hZ hw hsurj hflat hft)

end AlgebraicGeometry.FormalSpace

end
