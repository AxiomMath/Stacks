module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.Homology.Injectives.Ext.FilteredPageOne
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFilteredComplex

/-!
# Functoriality of the Ext spectral sequence into a filtered complex

Let `A` be a Grothendieck abelian category, let `M` be an object of `D(A)` and let `K^•` be a
filtered complex of `A`.  The spectral sequence of Tag 0G1X is the spectral sequence of the
filtered Hom complex `Hom^•(M^•, J^•)`, `F^pHom^•(M^•, J^•) = Hom^•(M^•, F^pJ^•)`, formed out of a
chosen filtered K-injective resolution `j : K^• ⟶ J^•`.  This file makes that construction
functorial: a morphism of the chosen resolutions induces a morphism of filtered Hom complexes, so
a morphism of spectral sequences, respecting identities and composition; and when the morphism of
resolutions is a quasi-isomorphism on every filtration step, the induced morphism of spectral
sequences is an isomorphism, hence an isomorphism of every page, every differential and every
page-turning isomorphism.

The input is a morphism of the *resolutions*, not of the filtered complexes themselves: the
resolution supplied by Tag 0BKI is chosen, not functorial, so a morphism `K^• ⟶ L^•` of filtered
complexes does not induce one of the chosen resolutions.  Such a comparison is constructed, and
the independence assertion of Tag 0G1Y deduced from it, in
`StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoIndependence`.

## Main definitions

* `Stacks.Injectives.homFiltered`: the Hom complex `Hom^•(P, J^•)` out of a fixed complex `P`,
  filtered by `Hom^•(P, F^pJ^•)`.
* `Stacks.Injectives.homFilteredMap`: its covariant functoriality, by postcomposition.
* `Stacks.Injectives.extIntoFilteredHomComplexIso`: the filtered Hom complex of Tag 0G1X is that
  filtered complex, for the chosen representative of `M` and the chosen resolution.
* `Stacks.Injectives.extIntoFilteredHomComplexMap` and
  `Stacks.Injectives.extSpectralSequenceInto_map`: the morphism of filtered Hom complexes, and of
  Ext spectral sequences, induced by a morphism of the chosen resolutions.

## Main results

* `Stacks.Injectives.quasiIso_homComplexPostcomp`: postcomposition with a quasi-isomorphism
  between K-injective complexes is a quasi-isomorphism of Hom complexes.
* `Stacks.Injectives.extSpectralSequenceInto_map_id` and
  `Stacks.Injectives.extSpectralSequenceInto_map_comp`: functoriality.
* `Stacks.Injectives.extSpectralSequenceInto_map_isIso_of_isIso_firstPage`: a first-page
  isomorphism propagates to the whole spectral sequence.
* `Stacks.Injectives.nonempty_extSpectralSequenceInto_iso_of_quasiIso`: a morphism of the chosen
  resolutions which is a quasi-isomorphism on every filtration step induces an isomorphism of Ext
  spectral sequences.
* `Stacks.Injectives.quasiIso_truncationFiltrationMap_natTrans_app`: a quasi-isomorphism of
  complexes is a quasi-isomorphism on every step of the canonical truncation filtration.

## Implementation notes

The chosen resolution enters only through the filtered complex `J^•`, so the comparison datum is
a morphism of filtered complexes `(extIntoSetup M K).J ⟶ (extIntoSetup M L).J` and nothing more;
in particular it is not required to be compatible with the resolution maps `j`.  What makes the
induced morphism an isomorphism is that it is a quasi-isomorphism on the filtration steps: the
graded pieces of the filtered Hom complex are then compared by
`FilteredComplexSpectralSequence.quasiIso_gr_map`, and the first page by
`FilteredComplexSpectralSequence.isIso_pageHom_one_f`.

The filtered Hom complex of Tag 0G1X is recorded only up to isomorphism over the Hom complexes
named in the setup, by `Stacks.Injectives.FilteredHomComplexRealization`; the comparison with
`Stacks.Injectives.homFiltered` is assembled from those isomorphisms rather than from a
definitional unfolding, so nothing here depends on how the realization is built.

Postcomposition with a quasi-isomorphism between K-injective complexes is a quasi-isomorphism
because it is, on cohomology classes, composition with an isomorphism of the homotopy category:
a quasi-isomorphism between K-injective complexes is a homotopy equivalence.

## References

* [Stacks Project, Tag 0G1Y](https://stacks.math.columbia.edu/tag/0G1Y)
* [Stacks Project, Tag 0G1X](https://stacks.math.columbia.edu/tag/0G1X)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace Stacks.Injectives

section HomComplexPostcomp

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Postcomposition with the identity is the identity morphism of Hom complexes. -/
lemma homComplexPostcomp_id (P X : CochainComplex A ℤ) :
    homComplexPostcomp P (𝟙 X) = 𝟙 (CochainComplex.HomComplex P X) := by
  ext n z
  change CochainComplex.HomComplex.Cochain P X n at z
  exact Cochain.comp_id z

/-- Postcomposition turns composition of morphisms of complexes into composition of morphisms of
Hom complexes. -/
lemma homComplexPostcomp_comp (P : CochainComplex A ℤ) {X Y Z : CochainComplex A ℤ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homComplexPostcomp P f ≫ homComplexPostcomp P g = homComplexPostcomp P (f ≫ g) := by
  ext n z
  rw [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  change CochainComplex.HomComplex.Cochain P X n at z
  show ((z.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g) (add_zero n)) =
    z.comp (Cochain.ofHom (f ≫ g)) (add_zero n)
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc z (Cochain.ofHom f) (Cochain.ofHom g)
    (add_zero n) (zero_add 0) (by omega)

/-- Postcomposition with a monomorphism is a monomorphism of Hom complexes. -/
lemma mono_homComplexPostcomp (P : CochainComplex A ℤ) {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    [Mono f] : Mono (homComplexPostcomp P f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y h
  apply Cochain.ext x y
  intro p q hpq
  have hxy : x.comp (Cochain.ofHom f) (add_zero n) = y.comp (Cochain.ofHom f) (add_zero n) := h
  have h' := congrArg (fun z ↦ z.v p q hpq) hxy
  rw [Cochain.comp_v x (Cochain.ofHom f) (add_zero n) p q q hpq (add_zero q),
    Cochain.comp_v y (Cochain.ofHom f) (add_zero n) p q q hpq (add_zero q)] at h'
  apply (cancel_mono (f.f q)).1
  simpa only [Cochain.ofHom_v] using h'

/-- **Postcomposition on the cohomology of a Hom complex is postcomposition in the homotopy
category.** The map induced on the degree-`n` cohomology of `Hom^•(P, -)` by `g : X ⟶ Y` is
invertible as soon as postcomposition with `g⟦n⟧` on morphisms out of `P` in the homotopy
category is bijective. -/
theorem isIso_homologyMap_homComplexPostcomp (P : CochainComplex A ℤ)
    {X Y : CochainComplex A ℤ} (g : X ⟶ Y) (n : ℤ)
    (h : Function.Bijective
      (fun a : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (X⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧'))) :
    IsIso (HomologicalComplex.homologyMap (homComplexPostcomp P g) n) := by
  have hb : ∀ Z : CochainComplex A ℤ, Function.Bijective
      (CochainComplex.HomComplex.CohomologyClass.toHom :
        CochainComplex.HomComplex.CohomologyClass P Z n → _) := fun Z =>
    CochainComplex.HomComplex.CohomologyClass.toHom_bijective P Z n
  have hcomm : ∀ c : CochainComplex.HomComplex.CohomologyClass P X n,
      CochainComplex.HomComplex.CohomologyClass.toHom (cohomologyClassPostcomp P g n c) =
        CochainComplex.HomComplex.CohomologyClass.toHom c ≫
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧') :=
    fun c => toHom_cohomologyClassPostcomp g n c
  have hbij : Function.Bijective (cohomologyClassPostcomp P g n) := by
    constructor
    · intro c₁ c₂ he
      refine (hb X).injective (h.injective ?_)
      show CochainComplex.HomComplex.CohomologyClass.toHom c₁ ≫ _ =
        CochainComplex.HomComplex.CohomologyClass.toHom c₂ ≫ _
      rw [← hcomm, ← hcomm, he]
    · intro c'
      obtain ⟨a, ha⟩ := h.surjective (CochainComplex.HomComplex.CohomologyClass.toHom c')
      obtain ⟨c, hc⟩ := (hb X).surjective a
      refine ⟨c, (hb Y).injective ?_⟩
      rw [hcomm, hc]
      exact ha
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun z => ?_⟩
  · refine (CochainComplex.HomComplex.homologyAddEquiv P X n).injective (hbij.injective ?_)
    rw [homologyAddEquiv_postcomp P g n x, homologyAddEquiv_postcomp P g n y]
    exact congrArg _ hxy
  · obtain ⟨c, hc⟩ := hbij.surjective (CochainComplex.HomComplex.homologyAddEquiv P Y n z)
    refine ⟨(CochainComplex.HomComplex.homologyAddEquiv P X n).symm c,
      (CochainComplex.HomComplex.homologyAddEquiv P Y n).injective ?_⟩
    rw [← homologyAddEquiv_postcomp P g n, AddEquiv.apply_symm_apply, hc]

/-- A quasi-isomorphism between K-injective complexes becomes an isomorphism in the homotopy
category. -/
lemma isIso_quotient_map_of_quasiIso_of_isKInjective {X Y : CochainComplex A ℤ}
    [X.IsKInjective] [Y.IsKInjective] (g : X ⟶ Y) [QuasiIso g] :
    IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) := by
  have h := (CochainComplex.IsKInjective.quasiIso_iff g).1 inferInstance
  rwa [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at h

/-- **Postcomposition with a quasi-isomorphism between K-injective complexes is a
quasi-isomorphism of Hom complexes.**  For a K-injective target the cohomology of a Hom complex
is a group of morphisms in the homotopy category, and the induced map is composition with an
isomorphism there. -/
lemma quasiIso_homComplexPostcomp (P : CochainComplex A ℤ) {X Y : CochainComplex A ℤ}
    [X.IsKInjective] [Y.IsKInjective] (g : X ⟶ Y) [QuasiIso g] :
    QuasiIso (homComplexPostcomp P g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧')) :=
    isIso_quotient_map_of_quasiIso_of_isKInjective (g⟦n⟧')
  refine isIso_homologyMap_homComplexPostcomp P g n ⟨fun a b hab => ?_, fun b => ?_⟩
  · exact (cancel_mono ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧'))).1 hab
  · exact ⟨b ≫ inv ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧')), by simp⟩

end HomComplexPostcomp

section HomFiltered

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The Hom complex `Hom^•(P, J^•)` out of a fixed complex `P`, filtered by the subcomplexes
`Hom^•(P, F^pJ^•)`. -/
def homFiltered (P : CochainComplex A ℤ) (J : CochainComplex.Filtered A) :
    CochainComplex.Filtered AddCommGrpCat.{v} where
  X := CochainComplex.HomComplex P J.X
  filtration.toMonoOver :=
    { obj := fun i =>
        letI : Mono (homComplexPostcomp P (J.filtration.ι.app i)) :=
          mono_homComplexPostcomp P _
        MonoOver.mk (homComplexPostcomp P (J.filtration.ι.app i))
      map := fun {i j} f => MonoOver.homMk (homComplexPostcomp P (J.filtration.step f)) (by
        change homComplexPostcomp P (J.filtration.step f) ≫
            homComplexPostcomp P (J.filtration.ι.app j) =
          homComplexPostcomp P (J.filtration.ι.app i)
        rw [homComplexPostcomp_comp, J.filtration.step_comp_ι_app])
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }

/-- The underlying complex of `homFiltered P J` is the Hom complex `Hom^•(P, J^•)`. -/
lemma homFiltered_X (P : CochainComplex A ℤ) (J : CochainComplex.Filtered A) :
    (homFiltered P J).X = CochainComplex.HomComplex P J.X :=
  rfl

/-- The `p`-th filtration step of `homFiltered P J` is `Hom^•(P, F^pJ^•)`. -/
lemma homFiltered_filtration_obj (P : CochainComplex A ℤ) (J : CochainComplex.Filtered A)
    (i : ℤᵒᵖ) :
    (homFiltered P J).filtration.obj i = CochainComplex.HomComplex P (J.filtration.obj i) :=
  rfl

/-- Postcomposition by a morphism of filtered complexes, as a morphism of filtered Hom
complexes. -/
def homFilteredMap (P : CochainComplex A ℤ) {J J' : CochainComplex.Filtered A} (g : J ⟶ J') :
    homFiltered P J ⟶ homFiltered P J' :=
  FilteredObject.homMk (homComplexPostcomp P g.hom)
    (fun i => homComplexPostcomp P (g.natTrans.app i)) (fun i => by
      change homComplexPostcomp P (g.natTrans.app i) ≫
          homComplexPostcomp P (J'.filtration.ι.app i) =
        homComplexPostcomp P (J.filtration.ι.app i) ≫ homComplexPostcomp P g.hom
      rw [homComplexPostcomp_comp, homComplexPostcomp_comp, g.comm i])

/-- On the `i`-th filtration step, `homFilteredMap` is postcomposition by the `i`-th component of
the morphism of filtrations. -/
lemma homFilteredMap_natTrans_app (P : CochainComplex A ℤ)
    {J J' : CochainComplex.Filtered A} (g : J ⟶ J') (i : ℤᵒᵖ) :
    (homFilteredMap P g).natTrans.app i = homComplexPostcomp P (g.natTrans.app i) :=
  rfl

/-- Postcomposition by the identity is the identity. -/
lemma homFilteredMap_id (P : CochainComplex A ℤ) (J : CochainComplex.Filtered A) :
    homFilteredMap P (𝟙 J) = 𝟙 (homFiltered P J) :=
  FilteredObject.hom_ext (homComplexPostcomp_id P J.X)

/-- Postcomposition preserves composition. -/
lemma homFilteredMap_comp (P : CochainComplex A ℤ) {J J' J'' : CochainComplex.Filtered A}
    (g : J ⟶ J') (g' : J' ⟶ J'') :
    homFilteredMap P (g ≫ g') = homFilteredMap P g ≫ homFilteredMap P g' := by
  apply FilteredObject.hom_ext
  show homComplexPostcomp P (g.hom ≫ g'.hom) = _
  rw [← homComplexPostcomp_comp]
  rfl

/-- **A filtered quasi-isomorphism of K-injective resolutions is a graded quasi-isomorphism of
filtered Hom complexes.**  If the filtration steps of `J^•` and of `J'^•` are K-injective and `g`
is a quasi-isomorphism on every step, then `Hom^•(P, -)` of `g` is a quasi-isomorphism on every
graded piece. -/
lemma quasiIso_gr_homFilteredMap (P : CochainComplex A ℤ)
    {J J' : CochainComplex.Filtered A} (g : J ⟶ J')
    (hJ : ∀ p : ℤ, (J.filtration.obj (op p)).IsKInjective)
    (hJ' : ∀ p : ℤ, (J'.filtration.obj (op p)).IsKInjective)
    (hg : ∀ p : ℤ, QuasiIso (g.natTrans.app (op p))) (p : ℤ) :
    QuasiIso ((FilteredObject.gr p).map (homFilteredMap P g)) := by
  have key : ∀ r : ℤ, QuasiIso ((homFilteredMap P g).natTrans.app (op r)) := by
    intro r
    have := hJ r
    have := hJ' r
    have := hg r
    rw [homFilteredMap_natTrans_app]
    exact quasiIso_homComplexPostcomp P (g.natTrans.app (op r))
  exact FilteredComplexSpectralSequence.quasiIso_gr_map _ p (key p) (key (p + 1))

end HomFiltered

section ExtInto

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- The filtration steps of the chosen filtered K-injective resolution of Tag 0BKI are
K-injective. -/
lemma isKInjective_extIntoSetup_filtration_obj (M : DerivedCategory A)
    (K : CochainComplex.Filtered A) (p : ℤ) :
    ((extIntoSetup.{w', w} M K).J.filtration.obj (op p)).IsKInjective :=
  (extIntoSetup.{w', w} M K).resolution.2.2.2.2.2.1 p

/-- The filtered Hom complex of Tag 0G1X is the Hom complex out of the chosen representative of
`M`, filtered by the Hom complexes into the steps of the chosen resolution. -/
def extIntoFilteredHomComplexIso (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    extIntoFilteredHomComplex.{w', w} M K ≅
      homFiltered (DerivedCategory.Q.objPreimage M) (extIntoSetup.{w', w} M K).J :=
  FilteredObject.isoMk
    (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).underlyingIso
    (fun i => (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso i.unop)
    (fun i => (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso_hom_comp i.unop)

/-- The morphism of filtered Hom complexes induced by a morphism of the chosen filtered
K-injective resolutions. -/
def extIntoFilteredHomComplexMap (M : DerivedCategory A) {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J) :
    extIntoFilteredHomComplex.{w', w} M K ⟶ extIntoFilteredHomComplex.{w', w} M L :=
  (extIntoFilteredHomComplexIso.{w', w} M K).hom ≫
    homFilteredMap (DerivedCategory.Q.objPreimage M) g ≫
      (extIntoFilteredHomComplexIso.{w', w} M L).inv

/-- The identity of the chosen resolution induces the identity. -/
lemma extIntoFilteredHomComplexMap_id (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    extIntoFilteredHomComplexMap.{w', w} M (𝟙 (extIntoSetup.{w', w} M K).J) =
      𝟙 (extIntoFilteredHomComplex.{w', w} M K) := by
  rw [extIntoFilteredHomComplexMap, homFilteredMap_id, Category.id_comp, Iso.hom_inv_id]

/-- The construction respects composition of morphisms of the chosen resolutions. -/
lemma extIntoFilteredHomComplexMap_comp (M : DerivedCategory A)
    {K L N : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (g' : (extIntoSetup.{w', w} M L).J ⟶ (extIntoSetup.{w', w} M N).J) :
    extIntoFilteredHomComplexMap.{w', w} M (g ≫ g') =
      extIntoFilteredHomComplexMap.{w', w} M g ≫ extIntoFilteredHomComplexMap.{w', w} M g' := by
  rw [extIntoFilteredHomComplexMap, extIntoFilteredHomComplexMap,
    extIntoFilteredHomComplexMap, homFilteredMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- A morphism of the chosen resolutions which is a quasi-isomorphism on every filtration step
induces a quasi-isomorphism on every graded piece of the filtered Hom complexes. -/
lemma quasiIso_gr_extIntoFilteredHomComplexMap (M : DerivedCategory A)
    {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (hg : ∀ p : ℤ, QuasiIso (g.natTrans.app (op p))) (p : ℤ) :
    QuasiIso ((FilteredObject.gr p).map (extIntoFilteredHomComplexMap.{w', w} M g)) := by
  have : QuasiIso ((FilteredObject.gr p).map
      (homFilteredMap (DerivedCategory.Q.objPreimage M) g)) :=
    quasiIso_gr_homFilteredMap _ g (isKInjective_extIntoSetup_filtration_obj.{w', w} M K)
      (isKInjective_extIntoSetup_filtration_obj.{w', w} M L) hg p
  rw [extIntoFilteredHomComplexMap, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The morphism of Ext spectral sequences induced by a morphism of the chosen filtered
K-injective resolutions.  It is the morphism of spectral sequences of the filtered Hom complexes,
so it commutes with every differential and every page-turning isomorphism. -/
def extSpectralSequenceInto_map (M : DerivedCategory A) {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J) :
    (extSpectralSequenceInto.{w', w} M K).1 ⟶ (extSpectralSequenceInto.{w', w} M L).1 :=
  let φ := CochainComplex.Filtered.spectralSequenceFunctor.map
    (extIntoFilteredHomComplexMap.{w', w} M g)
  { hom := fun r hr => φ.hom r (by omega)
    comm := fun r r' pq hrr' hr => φ.comm r r' pq hrr' (by omega) }

/-- The `r`-th page of the induced morphism of Ext spectral sequences is that of the morphism of
spectral sequences of the filtered Hom complexes. -/
private lemma extSpectralSequenceInto_map_hom (M : DerivedCategory A)
    {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J) (r : ℤ) (hr : 1 ≤ r) :
    (extSpectralSequenceInto_map.{w', w} M g).hom r hr =
      (CochainComplex.Filtered.spectralSequenceFunctor.map
        (extIntoFilteredHomComplexMap.{w', w} M g)).hom r (by omega) :=
  rfl

/-- The induced morphism of Ext spectral sequences preserves identities. -/
theorem extSpectralSequenceInto_map_id (M : DerivedCategory A)
    (K : CochainComplex.Filtered A) :
    extSpectralSequenceInto_map.{w', w} M (𝟙 (extIntoSetup.{w', w} M K).J) =
      𝟙 (extSpectralSequenceInto.{w', w} M K).1 := by
  apply SpectralSequence.hom_ext
  intro r hr
  rw [extSpectralSequenceInto_map_hom, extIntoFilteredHomComplexMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- The induced morphism of Ext spectral sequences preserves composition. -/
theorem extSpectralSequenceInto_map_comp (M : DerivedCategory A)
    {K L N : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (g' : (extIntoSetup.{w', w} M L).J ⟶ (extIntoSetup.{w', w} M N).J) :
    extSpectralSequenceInto_map.{w', w} M (g ≫ g') =
      extSpectralSequenceInto_map.{w', w} M g ≫ extSpectralSequenceInto_map.{w', w} M g' := by
  apply SpectralSequence.hom_ext
  intro r hr
  rw [extSpectralSequenceInto_map_hom, extIntoFilteredHomComplexMap_comp,
    CategoryTheory.Functor.map_comp]
  rfl

/-- An isomorphism on the first page of the induced morphism is an isomorphism on every later
page, the compatibility with the page turns being part of `extSpectralSequenceInto_map`. -/
theorem extSpectralSequenceInto_map_isIso_hom_of_isIso_firstPage (M : DerivedCategory A)
    {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (h : IsIso ((extSpectralSequenceInto_map.{w', w} M g).hom 1)) (r : ℤ) (hr : 1 ≤ r) :
    IsIso ((extSpectralSequenceInto_map.{w', w} M g).hom r hr) :=
  SpectralSequence.isIso_hom_of_GE (extSpectralSequenceInto_map.{w', w} M g) 1 r hr h

/-- A first-page isomorphism gives an isomorphism of the entire Ext spectral sequence, including
its differentials and page-turning isomorphisms. -/
theorem extSpectralSequenceInto_map_isIso_of_isIso_firstPage (M : DerivedCategory A)
    {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (h : IsIso ((extSpectralSequenceInto_map.{w', w} M g).hom 1)) :
    IsIso (extSpectralSequenceInto_map.{w', w} M g) := by
  let φ := extSpectralSequenceInto_map.{w', w} M g
  have hφ (r : ℤ) (hr : 1 ≤ r) : IsIso (φ.hom r hr) :=
    extSpectralSequenceInto_map_isIso_hom_of_isIso_firstPage.{w', w} M g h r hr
  let ψ : (extSpectralSequenceInto.{w', w} M L).1 ⟶ (extSpectralSequenceInto.{w', w} M K).1 :=
    { hom := fun r hr => inv (φ.hom r hr)
      comm := by
        intro r r' pq hrr' hr
        have hr' : 1 ≤ r' := by omega
        have := hφ r hr
        have := hφ r' hr'
        apply (cancel_mono ((φ.hom r' hr').f pq)).1
        simp only [Category.assoc, HomologicalComplex.Hom.inv_f_apply, IsIso.inv_hom_id,
          Category.comp_id]
        rw [← φ.comm r r' pq hrr' hr]
        simp only [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          IsIso.inv_hom_id, HomologicalComplex.homologyMap_id, Category.id_comp] }
  refine ⟨⟨ψ, ?_, ?_⟩⟩ <;> refine SpectralSequence.hom_ext fun r hr => ?_ <;>
    have := hφ r hr
  · exact IsIso.hom_inv_id (φ.hom r hr)
  · exact IsIso.inv_hom_id (φ.hom r hr)

/-- **A filtered quasi-isomorphism of the chosen resolutions induces an isomorphism of Ext
spectral sequences.**  If `g` is a quasi-isomorphism on every filtration step then the morphism
it induces on the spectral sequences of Tag 0G1X is an isomorphism, hence an isomorphism of every
page, every differential and every page-turning isomorphism. -/
theorem nonempty_extSpectralSequenceInto_iso_of_quasiIso (M : DerivedCategory A)
    {K L : CochainComplex.Filtered A}
    (g : (extIntoSetup.{w', w} M K).J ⟶ (extIntoSetup.{w', w} M L).J)
    (hg : ∀ p : ℤ, QuasiIso (g.natTrans.app (op p))) :
    Nonempty ((extSpectralSequenceInto.{w', w} M K).1 ≅
      (extSpectralSequenceInto.{w', w} M L).1) := by
  have hfirst : IsIso ((extSpectralSequenceInto_map.{w', w} M g).hom 1
      (show (1 : ℤ) ≤ 1 from le_rfl)) := by
    rw [extSpectralSequenceInto_map_hom]
    exact FilteredComplexSpectralSequence.isIso_filteredSpectralSequenceMap_hom_one
      (extIntoFilteredHomComplexMap.{w', w} M g)
      (quasiIso_gr_extIntoFilteredHomComplexMap.{w', w} M g hg)
  have hmap := extSpectralSequenceInto_map_isIso_of_isIso_firstPage.{w', w} M g hfirst
  rcases hmap.out with ⟨ψ, hgψ, hψg⟩
  exact ⟨⟨extSpectralSequenceInto_map.{w', w} M g, ψ, hgψ, hψg⟩⟩

end ExtInto

section CanonicalTruncation

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

omit [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A] in
/-- A quasi-isomorphism of complexes is a quasi-isomorphism on every step of the canonical
truncation filtration. -/
lemma quasiIso_truncationFiltrationMap_natTrans_app {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    [QuasiIso f] (p : ℤ) :
    QuasiIso ((CochainComplex.truncationFiltrationMap f).natTrans.app (op p)) := by
  show QuasiIso (CochainComplex.truncLEMap f (-p))
  rw [CochainComplex.quasiIso_truncLEMap_iff]
  intro j _
  exact (quasiIso_iff f).1 inferInstance j

end CanonicalTruncation

end Stacks.Injectives

end
