module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.ZariskisMainTheorem

/-!
# Factoring a quasi-finite morphism of affine schemes through a finite one

A quasi-finite morphism between affine schemes is an open immersion followed by a finite
morphism of affine schemes. This is the geometric form of Zariski's Main Theorem in commutative
algebra: the finite intermediate algebra is the one produced by Tag 00QB, whose spectrum receives
the source as an open subscheme.

The passage from the algebra to the geometry is a criterion for a morphism of affine schemes to
be an open immersion. The conditions supplied by Tag 00QB are that the induced map of spectra be
an open topological embedding and that the localizations at the basic opens inside its image be
isomorphisms; together they say exactly that the morphism is an isomorphism onto an open
subscheme, which is checked here one basic open at a time.

## Main results

* `AlgebraicGeometry.isOpenImmersion_SpecMap_of_forall_exists_awayMap_bijective`: a morphism of
  affine schemes is an open immersion as soon as it is injective on points and every point of
  the source has a basic open neighbourhood, cut out by a function on the target, over which the
  morphism becomes an isomorphism.
* `AlgebraicGeometry.isOpenImmersion_SpecMap_of_isOpenEmbedding_comap` is the same criterion in
  the form in which Tag 00QB verifies it.
* `AlgebraicGeometry.isOpenImmersion_specMap_of_isOpen_range_comap` drops the injectivity: an
  open *range* together with the away-map isomorphisms already force an open immersion.
* `AlgebraicGeometry.exists_isOpenImmersion_isFinite_factorization` is Tag 03GU: a quasi-finite
  morphism of affine schemes factors as an open immersion followed by a finite morphism with
  affine source.

## Implementation notes

Quasi-finiteness of a morphism is represented by the typeclasses
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.LocallyQuasiFinite` and
`AlgebraicGeometry.QuasiCompact`; the last is not assumed, since it is automatic for an affine
source.

The open-immersion criterion is proved from
`AlgebraicGeometry.IsOpenImmersion.of_forall_source_exists`:
the chosen local piece of the source is the basic open `D(φ a)`, which is the spectrum of a
localization away from an element and hence an open subscheme, and its composite to the target
is the spectrum of the away map `A_a ⟶ B_{φ a}`, which the hypothesis makes an isomorphism. No
stalk computation is needed, and the only comparison of ring maps used is
`IsLocalization.map_comp`.

`AlgebraicGeometry.isOpenImmersion_specMap_of_isOpen_range_comap` instead uses the Zariski
locality of `AlgebraicGeometry.IsOpenImmersion` on the target, in the form
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`: the range is covered by the
basic opens it contains, and over each of those the restriction of `Spec φ` is the spectrum of
an away map (`AlgebraicGeometry.SpecMapRestrictBasicOpenIso`), hence an isomorphism. Only basic
opens *inside* the range are used, so neither a cover of the whole target nor injectivity on
points is needed.

## References

* [Stacks Project, Tag 03GU](https://stacks.math.columbia.edu/tag/03GU)
* [Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB)
* [Stacks Project, Tag 01TJ](https://stacks.math.columbia.edu/tag/01TJ)
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry

/-- The ring map `A_a ⟶ B_{φ a}` between localizations is an isomorphism if it is bijective. -/
private theorem isIso_ofHom_awayMap {A B : Type u} [CommRing A] [CommRing B] {φ : A →+* B}
    {a : A} (h : Function.Bijective (Localization.awayMap φ a)) :
    IsIso (CommRingCat.ofHom (Localization.awayMap φ a)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 h

/-- A morphism of affine schemes `Spec B ⟶ Spec A` is an open immersion provided it is injective
on points and every point `q` of `Spec B` admits `a : A` with `φ a ∉ q` such that the induced map
of localizations `A_a ⟶ B_{φ a}` is bijective.

This is the criterion through which parts (1) and (2) of
[Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB) produce the open immersion
of [Stacks Project, Tag 03GU](https://stacks.math.columbia.edu/tag/03GU). -/
public theorem isOpenImmersion_SpecMap_of_forall_exists_awayMap_bijective
    {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hinj : Function.Injective (PrimeSpectrum.comap φ.hom))
    (h : ∀ q : PrimeSpectrum B, ∃ a : A, φ.hom a ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap φ.hom a)) :
    IsOpenImmersion (Spec.map φ) := by
  refine IsOpenImmersion.of_forall_source_exists _ (fun x y hxy => hinj hxy) fun q => ?_
  obtain ⟨a, haq, hbij⟩ := h q
  have hring : (Localization.awayMap φ.hom a).comp (algebraMap A (Localization.Away a))
      = (algebraMap B (Localization.Away (φ.hom a))).comp φ.hom := by
    unfold Localization.awayMap IsLocalization.Away.map
    exact IsLocalization.map_comp _
  have hcat : φ ≫ CommRingCat.ofHom (algebraMap B (Localization.Away (φ.hom a)))
      = CommRingCat.ofHom (algebraMap A (Localization.Away a)) ≫
        CommRingCat.ofHom (Localization.awayMap φ.hom a) :=
    CommRingCat.hom_ext (by simpa using hring.symm)
  refine ⟨Spec (.of (Localization.Away (φ.hom a))),
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ.hom a)))), inferInstance,
    ?_, ?_⟩
  · change q ∈ (Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away (φ.hom a))))).opensRange
    rw [Scheme.Hom.opensRange_localizationAway]
    exact haq
  · have : IsIso (CommRingCat.ofHom (Localization.awayMap φ.hom a)) :=
      (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
    rw [← Spec.map_comp, hcat, Spec.map_comp]
    infer_instance

/-- A morphism of affine schemes `Spec B ⟶ Spec A` is an open immersion provided the induced map
of spectra is an open topological embedding and, for every `a : A` whose basic open lies inside
the image, the induced map of localizations `A_a ⟶ B_{φ a}` is bijective.

These are the two conclusions of parts (1) and (2) of
[Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB). -/
public theorem isOpenImmersion_SpecMap_of_isOpenEmbedding_comap
    {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hemb : IsOpenEmbedding (PrimeSpectrum.comap φ.hom))
    (h : ∀ a : A, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))
        ⊆ Set.range (PrimeSpectrum.comap φ.hom) →
      Function.Bijective (Localization.awayMap φ.hom a)) :
    IsOpenImmersion (Spec.map φ) := by
  refine isOpenImmersion_SpecMap_of_forall_exists_awayMap_bijective φ hemb.injective fun q => ?_
  obtain ⟨-, ⟨a, rfl⟩, hmem, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self (f := PrimeSpectrum.comap φ.hom) q) hemb.isOpen_range
  exact ⟨a, hmem, h a hsub⟩

/-- The same criterion with injectivity dropped: the spectrum map of a ring homomorphism `φ` is
an open immersion as soon as the *range* of `Spec φ` is open and `φ` becomes bijective after
localising at every element of the source whose basic open is contained in that range.

The hypotheses are exactly the data produced by part (3) of
[Stacks Project, Tag 00QB](https://stacks.math.columbia.edu/tag/00QB). Injectivity on points is
not needed, because the conclusion is checked Zariski-locally on the target over the basic opens
inside the range (`AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`), where the
restriction of `Spec φ` is the spectrum of an away map. -/
public theorem isOpenImmersion_specMap_of_isOpen_range_comap
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hopen : IsOpen (Set.range (PrimeSpectrum.comap φ)))
    (hbij : ∀ g : A, (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap φ) → Function.Bijective (Localization.awayMap φ g)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  apply IsZariskiLocalAtTarget.of_range_subset_iSup
    (P := @IsOpenImmersion) (f := Spec.map (CommRingCat.ofHom φ))
    (ι := {g : A // (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆
        Set.range (PrimeSpectrum.comap φ)})
    (fun g => PrimeSpectrum.basicOpen g.1) ?_ ?_
  · rintro x ⟨p, rfl⟩
    obtain ⟨_, ⟨g, rfl⟩, hxV, hVsub⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := A))
        (show PrimeSpectrum.comap φ p ∈ (⟨_, hopen⟩ : TopologicalSpace.Opens _) from ⟨p, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hVsub⟩, hxV⟩
  · intro g
    refine (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
      (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom φ) g.1)).mpr ?_
    have := isIso_ofHom_awayMap (hbij g.1 g.2)
    exact IsOpenImmersion.of_isIso _

/-- **Stacks Project, Tag 03GU.** A quasi-finite morphism `f : Y ⟶ X` of affine schemes factors
as `j ≫ π` with `Z` affine, `j : Y ⟶ Z` an open immersion and `π : Z ⟶ X` finite.

Quasi-compactness of `f` is not assumed: it is automatic for an affine source. -/
@[stacks 03GU,
  ega "IV 18.12.13" "affine case",
  ega "IV 8.12.6" "affine case",
  ega "III 4.4.3" "special case", sga "3 VIB 5.6.0" "(ii), special case"]
public theorem exists_isOpenImmersion_isFinite_factorization {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffine X] [IsAffine Y] [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (j : Y ⟶ Z) (π : Z ⟶ X),
      IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f := by
  let _ : Algebra ↑Γ(X, ⊤) ↑Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  have _ : Algebra.FiniteType ↑Γ(X, ⊤) ↑Γ(Y, ⊤) :=
    RingHom.finiteType_algebraMap.mp
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp ‹_›)
  have _ : Algebra.QuasiFinite ↑Γ(X, ⊤) ↑Γ(Y, ⊤) :=
    RingHom.quasiFinite_algebraMap.mp
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite).mp ‹_›)
  obtain ⟨T, -, hfin, hemb, hbij⟩ :=
    quasiFinite_exists_finite_subalgebra (R := ↑Γ(X, ⊤)) (S := ↑Γ(Y, ⊤))
  let ι : CommRingCat.of T ⟶ Γ(Y, ⊤) := CommRingCat.ofHom T.val.toRingHom
  let σ : Γ(X, ⊤) ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap ↑Γ(X, ⊤) T)
  have hστ : σ ≫ ι = f.appTop := by ext x; rfl
  have _ : IsOpenImmersion (Spec.map ι) :=
    isOpenImmersion_SpecMap_of_isOpenEmbedding_comap ι hemb hbij
  have _ : IsFinite (Spec.map σ) :=
    (IsFinite.SpecMap_iff σ).mpr (RingHom.finite_algebraMap.mpr hfin)
  refine ⟨Spec (CommRingCat.of T), inferInstance, Y.isoSpec.hom ≫ Spec.map ι,
    Spec.map σ ≫ X.isoSpec.inv, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, ← Category.assoc (Spec.map ι), ← Spec.map_comp, hστ,
    Scheme.isoSpec_inv_naturality, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end AlgebraicGeometry

end
