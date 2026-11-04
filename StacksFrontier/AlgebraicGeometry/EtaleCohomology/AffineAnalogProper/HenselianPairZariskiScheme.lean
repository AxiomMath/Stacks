module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairZariskiSections

/-!
# Global sections of a Zariski sheaf along a closed immersion of a henselian pair

Restriction of global sections of a Zariski sheaf along a morphism of schemes `f : Y ⟶ X` is the
component at the largest open of the unit of the inverse-image/direct-image adjunction. It is
recorded in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed` as
`Stacks.EtaleCohomology.zariskiGlobalSectionsMap`, for coefficients one universe above the
schemes; `Stacks.EtaleCohomology.zariskiGlobalSectionsMapAt` is the same map for coefficients in
an arbitrary universe, which is what lets it be compared with the topological statement of
[Stacks, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG), whose coefficients are sheaves of
sets in the universe of the space.

Two things are proved. First, for a morphism of schemes whose map on underlying spaces is a
topological embedding, bijectivity of the restriction map on the Zariski site follows from
bijectivity of the purely topological restriction map `Stacks.globalSectionsRestriction` to the
image: the two maps are units of inverse-image/direct-image adjunctions taken along two
continuous maps which differ by a homeomorphism. Second, the two Zariski hypotheses (1) and (2)
of [Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) for the closed immersion
`Spec (A ⧸ I) ⟶ Spec A` attached to a henselian pair `(A, I)`, with no hypothesis that `A` is
local: restriction along that closed immersion, and along its base change by an arbitrary finite
morphism `Y ⟶ Spec A`, is bijective on global sections of every sheaf of sets on the Zariski
site.

## Main definitions

* `Stacks.EtaleCohomology.zariskiGlobalSectionsMapAt` — restriction of global sections of a
  Zariski sheaf along a morphism of schemes, with coefficients in an arbitrary universe.

## Main results

* `Stacks.EtaleCohomology.zariskiGlobalSectionsMapAt_eq` — at the coefficient universe of
  `Stacks.EtaleCohomology.zariskiGlobalSectionsMap` the two maps are the same map.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_of_globalSectionsRestriction` —
  the bridge from the topological restriction map to the restriction map on the Zariski site of a
  scheme, for a morphism which is a topological embedding on underlying spaces.
* `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_quotient_of_henselianPair` and
  `Stacks.EtaleCohomology.bijective_zariskiGlobalSectionsMapAt_pullback_of_henselianPair` — the
  two Zariski hypotheses of Tag 09ZF for a henselian pair.

## Implementation notes

The bridge is a comparison of two adjunction units. A continuous map which is a topological
embedding factors as a homeomorphism onto its image followed by the inclusion of that image; the
unit of a composite adjunction is the first unit followed by the direct image of the second
(`CategoryTheory.Adjunction.comp_unit_app`), and it agrees with the unit of the adjunction for the
composite map up to the canonical isomorphism of the two left adjoints
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`). Along an isomorphism of spaces the
unit is invertible, because the inverse image is then a left adjoint of the same functor as the
direct image along the inverse map, and that direct image is fully faithful since the inverse map
is inducing (`ClosedImmersionSheaves.sheafPushforwardFullyFaithful`).

For the base change of `Spec (A ⧸ I) ⟶ Spec A` along a finite morphism `f : Y ⟶ Spec A` the
scheme `Y` is affine, so `AlgebraicGeometry.Scheme.isoSpec` makes its space homeomorphic to the
spectrum of `B = Γ(Y, ⊤)`, a finite — hence integral — `A`-algebra. The image of the base change
is the preimage of `V(I)`, which that homeomorphism carries to `V(IB)`, and bijectivity of
restriction to the latter is
`Stacks.bijective_globalSectionsRestriction_zeroLocus_map_of_henselianPair`. Rather than
transporting sheaves along the homeomorphism, it is fed to the same comparison of adjunction
units as the embedding itself: being an isomorphism of spaces, restriction along it is bijective
for every sheaf of sets.

No Stacks attribute is placed on anything below: these statements are hypotheses (1) and (2) of
Tag 09ZF, not its conclusion. That conclusion is
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImageComparison_of_zariskiBijective`
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.FiniteSurjectiveDescent`,
and the conclusion of Tag 09ZH is
`Stacks.EtaleCohomology.isIso_globalSectionsComparison_quotient_of_henselianPair` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.HenselianPairEtaleSections`,
which is the former applied to the two results proved here.

## References

* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)
* [Stacks Project, Tag 09ZH](https://stacks.math.columbia.edu/tag/09ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe u v t

namespace Stacks.EtaleCohomology

/-- Restriction of global sections along a morphism of schemes, for a sheaf of sets with values
in an arbitrary universe: the component at the largest open of the unit of the sheaf
pullback/pushforward adjunction for the Zariski sites.

This is `Stacks.EtaleCohomology.zariskiGlobalSectionsMap` with the coefficient universe left
free; the typeclass hypothesis is what makes the inverse image exist, and it is automatic for
`Type t` whenever sheafification is (in particular at `t = u` and at `t = max (u + 1) v`). -/
public def zariskiGlobalSectionsMapAt {Y X : Scheme.{u}} (f : Y ⟶ X)
    [((Opens.map f.base).sheafPushforwardContinuous (Type t)
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Y.carrier)).IsRightAdjoint]
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type t)) :
    F.obj.obj (op ⊤) →
      (((Opens.map f.base).sheafPullback (Type t)
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Y.carrier)).obj F).obj.obj (op ⊤) :=
  (((Opens.map f.base).sheafAdjunctionContinuous (Type t)
    (Opens.grothendieckTopology X.carrier)
    (Opens.grothendieckTopology Y.carrier)).unit.app F).hom.app (op ⊤)

/-- At the coefficient universe `max (u + 1) v` the restriction map of
`Stacks.EtaleCohomology.zariskiGlobalSectionsMapAt` is the map
`Stacks.EtaleCohomology.zariskiGlobalSectionsMap`. -/
public theorem zariskiGlobalSectionsMapAt_eq {Y X : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type (max (u + 1) v))) :
    zariskiGlobalSectionsMapAt.{u, max (u + 1) v} f F = zariskiGlobalSectionsMap.{u, v} f F :=
  rfl

section Bridge

open TopCat _root_.Stacks.Topology

/-- Restriction of global sections of a sheaf of sets along a continuous map of topological
spaces: the component at the largest open of the unit of the inverse-image/direct-image
adjunction of the two Zariski sites. -/
private def topGlobalSectionsMap {W X : TopCat.{u}} (g : W ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u)) :
    F.obj.obj (op ⊤) →
      (((Opens.map g).sheafPullback (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology W)).obj F).obj.obj (op ⊤) :=
  (((Opens.map g).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology W)).unit.app F).hom.app (op ⊤)

/-- Along an isomorphism of topological spaces the unit of the inverse-image/direct-image
adjunction on sheaves of sets is an isomorphism: the inverse image is a left adjoint of the same
functor as the direct image along the inverse map, which is fully faithful because that map is
inducing, and the unit of an adjunction with fully faithful left adjoint is invertible. -/
private theorem isIso_sheafAdjunctionContinuous_unit_of_isIso {W S : TopCat.{u}} (c : W ⟶ S)
    [IsIso c] :
    IsIso ((Opens.map c).sheafAdjunctionContinuous (Type u)
      (Opens.grothendieckTopology S) (Opens.grothendieckTopology W)).unit := by
  have ff : (TopCat.Sheaf.pushforward (Type u) (inv c)).FullyFaithful :=
    ClosedImmersionSheaves.sheafPushforwardFullyFaithful (C := Type u)
      (TopCat.homeoOfIso (asIso c).symm).isInducing
  let adjOpens : Opens.map (inv c) ⊣ Opens.map c :=
    (Opens.mapMapIso (asIso c)).symm.toAdjunction
  let adjSheaf : (Opens.map (inv c)).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology W) (Opens.grothendieckTopology S) ⊣
      (Opens.map c).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology W) :=
    adjOpens.sheafPushforwardContinuous (E := Type u) _ _
  have e : (Opens.map c).sheafPullback (Type u) (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology W) ≅
      (Opens.map (inv c)).sheafPushforwardContinuous (Type u)
        (Opens.grothendieckTopology W) (Opens.grothendieckTopology S) :=
    Adjunction.leftAdjointUniq
      ((Opens.map c).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology W)) adjSheaf
  have : ((Opens.map (inv c)).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology S)).Full := ff.full
  have : ((Opens.map (inv c)).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology S)).Faithful := ff.faithful
  have : ((Opens.map c).sheafPullback (Type u) (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology W)).Full := Functor.Full.of_iso e.symm
  have : ((Opens.map c).sheafPullback (Type u) (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology W)).Faithful := Functor.Faithful.of_iso e.symm
  infer_instance

/-- An isomorphism of sheaves of sets is an isomorphism on sections over every object. -/
theorem isIso_sheafHom_app_of_isIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type u)} (φ : F ⟶ G) [IsIso φ] (U : Cᵒᵖ) : IsIso (φ.hom.app U) := by
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map φ))
  infer_instance

/-- Restriction of global sections along an isomorphism of topological spaces is bijective. -/
private theorem bijective_topGlobalSectionsMap_of_isIso {W S : TopCat.{u}} (c : W ⟶ S) [IsIso c]
    (G : Sheaf (Opens.grothendieckTopology S) (Type u)) :
    Function.Bijective (topGlobalSectionsMap c G) := by
  have := isIso_sheafAdjunctionContinuous_unit_of_isIso c
  exact (isIso_iff_bijective _).mp (isIso_sheafHom_app_of_isIso
    (((Opens.map c).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology W)).unit.app G) (op ⊤))

/-- Restriction of global sections of a sheaf of sets along a composite of continuous maps is
bijective as soon as it is bijective along each factor: the unit of the composite adjunction is
the first unit followed by the direct image of the second, and it agrees with the unit of the
adjunction for the composite up to the isomorphism of the two left adjoints. -/
private theorem bijective_topGlobalSectionsMap_comp {W S X : TopCat.{u}} (a : W ⟶ S) (b : S ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) (Type u))
    (hb : Function.Bijective (topGlobalSectionsMap b F))
    (ha : Function.Bijective (topGlobalSectionsMap a
      (((Opens.map b).sheafPullback (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology S)).obj F))) :
    Function.Bijective (topGlobalSectionsMap (a ≫ b) F) := by
  let adjb := (Opens.map b).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology S)
  let adja := (Opens.map a).sheafAdjunctionContinuous (Type u) (Opens.grothendieckTopology S)
    (Opens.grothendieckTopology W)
  let adjabs := (Opens.map (a ≫ b)).sheafAdjunctionContinuous (Type u)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)
  let adjc : ((Opens.map b).sheafPullback (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology S) ⋙
      (Opens.map a).sheafPullback (Type u) (Opens.grothendieckTopology S)
        (Opens.grothendieckTopology W)) ⊣
      (Opens.map (a ≫ b)).sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology W) := adjb.comp adja
  have hc : Function.Bijective ((adjc.unit.app F).hom.app (op ⊤)) := by
    rw [show adjc.unit.app F = adjb.unit.app F ≫
        ((Opens.map b).sheafPushforwardContinuous (Type u) (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology S)).map
          (adja.unit.app (((Opens.map b).sheafPullback (Type u) (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology S)).obj F)) from Adjunction.comp_unit_app adjb adja F]
    exact ha.comp hb
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adjabs adjc F] at hc
  exact ((isIso_iff_bijective _).mp (isIso_sheafHom_app_of_isIso
    (((Opens.map (a ≫ b)).sheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology W)).map
        ((Adjunction.leftAdjointUniq adjabs adjc).hom.app F)) (op ⊤))).of_comp_iff' _ |>.mp hc

/-- **Restriction of global sections along a topological embedding.** If restriction of global
sections of a sheaf of sets to the range of an embedding `g` is bijective, then so is the
restriction map along `g` itself: `g` factors as a homeomorphism onto its range followed by the
inclusion of that range. -/
private theorem bijective_topGlobalSectionsMap_of_isEmbedding {W X : TopCat.{u}} (g : W ⟶ X)
    (hg : Topology.IsEmbedding (ConcreteCategory.hom g))
    (F : Sheaf (Opens.grothendieckTopology X) (Type u))
    (h : Function.Bijective
      (Stacks.globalSectionsRestriction (Set.range (ConcreteCategory.hom g)) F)) :
    Function.Bijective (topGlobalSectionsMap g F) := by
  set Z : Set X := Set.range (ConcreteCategory.hom g)
  let c : W ≅ TopCat.of Z := TopCat.isoOfHomeo hg.toHomeomorph
  have hfac : g = c.hom ≫ Stacks.subsetInclusion X Z := by
    ext w
    rfl
  rw [hfac]
  exact bijective_topGlobalSectionsMap_comp _ _ F h
    (bijective_topGlobalSectionsMap_of_isIso _ _)

end Bridge

/-- **Hypotheses (1) and (2) of Tag 09ZF, reduced to the topological statement of Tag 09ZG.** Let
`i : Z ⟶ X` be a morphism of schemes whose map on underlying spaces is a topological embedding.
If restriction of global sections to the image of `i` is bijective for a sheaf of sets on the
space of `X`, then restriction along `i` is bijective on global sections of that sheaf viewed on
the Zariski site of `X`.

The two maps differ only in the continuous map they are taken along — `i` on underlying spaces
versus the inclusion of its image — and those differ by a homeomorphism. -/
public theorem bijective_zariskiGlobalSectionsMapAt_of_globalSectionsRestriction
    {X Z : Scheme.{u}} (i : Z ⟶ X) (hi : Topology.IsEmbedding i.base)
    (F : Sheaf (Opens.grothendieckTopology X.carrier) (Type u))
    (h : Function.Bijective (Stacks.globalSectionsRestriction (Set.range i.base) F)) :
    Function.Bijective (zariskiGlobalSectionsMapAt i F) :=
  bijective_topGlobalSectionsMap_of_isEmbedding i.base hi F h

/-- The map `Spec (A ⧸ I) ⟶ Spec A` is a closed immersion. -/
private theorem isClosedImmersion_specMap_quotientMk {A : Type u} [CommRing A] (I : Ideal A) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **Hypothesis (1) of Tag 09ZF for a henselian pair.** For a henselian pair `(A, I)`,
restriction of global sections along the closed immersion `Spec (A ⧸ I) ⟶ Spec A` is bijective
for every sheaf of sets on the Zariski site of `Spec A`. The base ring is not assumed local.

The image of that closed immersion is the closed subset `V(I)`, and bijectivity of restriction to
it is `Stacks.bijective_globalSectionsRestriction_range_comap_of_henselianPair`. -/
public theorem bijective_zariskiGlobalSectionsMapAt_quotient_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (F : Sheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A)).carrier) (Type u)) :
    Function.Bijective (zariskiGlobalSectionsMapAt
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F) := by
  have := isClosedImmersion_specMap_quotientMk I
  exact bijective_zariskiGlobalSectionsMapAt_of_globalSectionsRestriction _
    (Scheme.Hom.isClosedEmbedding _).isEmbedding F <|
    Stacks.bijective_globalSectionsRestriction_range_comap_of_henselianPair I hI F

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A` has image the zero locus `V(I)`. -/
theorem range_specMap_ofHom_quotientMk_base {A : Type u} [CommRing A] (I : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- A morphism from an affine scheme `Y` to `Spec R` is `Y ≅ Spec Γ(Y, ⊤)` followed by the
spectrum of the induced map `R ⟶ Γ(Y, ⊤)`. -/
theorem isoSpec_hom_comp_specMap_ΓSpecIso_inv_comp_appTop {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom,
    Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- For an affine scheme `Y` over `Spec A`, the image in `Spec Γ(Y, ⊤)` of the base change of
`Spec (A ⧸ I) ⟶ Spec A` is the preimage of `V(I)` under the induced map on spectra. -/
theorem range_pullbackFst_specQuotient_comp_isoSpec_hom_base {A : Type u} [CommRing A]
    (I : Ideal A) {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec (CommRingCat.of A)) :
    Set.range (ConcreteCategory.hom
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base ≫
        Y.isoSpec.hom.base)) =
      PrimeSpectrum.comap ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set A) := by
  let α : CommRingCat.of A ⟶ Γ(Y, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop
  have hbase : ∀ y : Y.carrier, f.base y = PrimeSpectrum.comap α.hom (Y.isoSpec.hom.base y) := by
    intro y
    rw [← isoSpec_hom_comp_specMap_ΓSpecIso_inv_comp_appTop f]
    rfl
  have hmemq : ∀ y : Y.carrier,
      y ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).base ↔
      f.base y ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
    intro y
    rw [Scheme.Pullback.range_fst, range_specMap_ofHom_quotientMk_base]
    exact Iff.rfl
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨w, rfl⟩
    have h₁ := (hmemq _).mp ⟨w, rfl⟩
    rwa [hbase] at h₁
  · intro p hp
    obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso Y.isoSpec.hom.base).2 p
    obtain ⟨w, hw⟩ := (hmemq y).mpr (by rwa [hbase y, hy])
    refine ⟨w, ?_⟩
    rw [← hy, ← hw]
    rfl

/-- **Hypothesis (2) of Tag 09ZF for a henselian pair.** For a henselian pair `(A, I)` and a
finite morphism `f : Y ⟶ Spec A`, restriction of global sections along the base change of
`Spec (A ⧸ I) ⟶ Spec A` by `f` is bijective for every sheaf of sets on the Zariski site of `Y`.
The base ring is not assumed local.

Being finite over an affine base, `Y` is the spectrum of the integral `A`-algebra `Γ(Y, ⊤)`, and
the image of the base change corresponds to the closed subset cut out by the extended ideal;
bijectivity of restriction to that subset is
`Stacks.bijective_globalSectionsRestriction_zeroLocus_map_of_henselianPair`. -/
public theorem bijective_zariskiGlobalSectionsMapAt_pullback_of_henselianPair
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A)) [IsFinite f]
    (F : Sheaf (Opens.grothendieckTopology Y.carrier) (Type u)) :
    Function.Bijective (zariskiGlobalSectionsMapAt
      (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) F) := by
  have := isClosedImmersion_specMap_quotientMk I
  have : IsAffine Y := isAffine_of_isAffineHom f
  let : Algebra A Γ(Y, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom.toAlgebra
  have : Algebra.IsIntegral A Γ(Y, ⊤) :=
    ⟨RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2)
      (Scheme.Hom.finite_appTop f).to_isIntegral⟩
  have hZeq := range_pullbackFst_specQuotient_comp_isoSpec_hom_base I f
  set i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hfac : (pullback.fst f i).base =
      ((pullback.fst f i).base ≫ Y.isoSpec.hom.base) ≫ Y.isoSpec.inv.base := by
    rw [Category.assoc, ← Scheme.Hom.comp_base, Iso.hom_inv_id, Scheme.Hom.id_base,
      Category.comp_id]
  show Function.Bijective (topGlobalSectionsMap (pullback.fst f i).base F)
  rw [hfac]
  refine bijective_topGlobalSectionsMap_comp _ _ F (bijective_topGlobalSectionsMap_of_isIso _ F)
    (bijective_topGlobalSectionsMap_of_isEmbedding _ ?_ _ ?_)
  · exact (TopCat.homeoOfIso (asIso Y.isoSpec.hom.base)).isEmbedding.comp
      (Scheme.Hom.isClosedEmbedding (pullback.fst f i)).isEmbedding
  · rw [hZeq]
    exact Stacks.bijective_globalSectionsRestriction_zeroLocus_map_of_henselianPair I hI _

end Stacks.EtaleCohomology

end
