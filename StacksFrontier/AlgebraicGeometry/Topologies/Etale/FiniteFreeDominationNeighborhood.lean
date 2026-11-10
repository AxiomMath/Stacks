module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteFreeDominationAffine

/-!
# A finite locally free morphism locally dominates an étale neighbourhood

This file proves [Stacks, Tag 02LG]: let `s` be a point of a scheme `S` and let `U ⟶ S` be an
étale neighbourhood of `s`. Then there are an affine open `V ∋ s` and a surjective finite locally
free morphism `π : T ⟶ V` such that every point `t` of `T` above `s` has an open neighbourhood
`W ⊆ T` admitting a morphism `W ⟶ U` over `S` which carries `t` to the distinguished point of
the neighbourhood.

The commutative algebra is [Stacks, Tag 00UF],
`Algebra.IsStandardEtale.exists_finite_faithfullyFlat_forall_exists_comp_eq_comap_eq`: for a
standard étale `R`-algebra and a prime `q` of it there is a finite, finitely presented,
faithfully flat `R`-algebra `C` such that every prime `q'` of `C` contracting to the same prime
of `R` as `q` admits a `g' ∉ q'` and an `R`-algebra map to `C_{g'}` pulling `q' C_{g'}` back to
`q`. Combined with Mathlib's `Algebra.IsEtaleAt.exists_isStandardEtale` this gives the same
conclusion for an arbitrary étale algebra, which is the shape the geometric statement needs: the
condition `π t = s` becomes the equality of contractions, and `D(g')` is the neighbourhood `W`.

## Main results

* `Stacks.Topologies.Etale.exists_isFiniteLocallyFree_surjective_locally_lift_etaleNeighborhood`
  is [Stacks, Tag 02LG].

## Implementation notes

The affine open neighbourhood of `s` is an element of `AlgebraicGeometry.Scheme.affineOpens`, and
a point of `T` above `s` is recorded by an equality of points of `V`.

Neither `S` nor the source of the neighbourhood is assumed affine, so the construction runs on an
affine chart: an affine open `A` of `U` containing the distinguished point and lying over an
affine open `V ∋ s`, with `U.toBase.resLE V A` étale between affine schemes. Everything else is
transported along `AlgebraicGeometry.Scheme.isoSpec`, as in the sibling file for Tag 02LH, and
the identification of the basic open `D(g')` of `Spec C` with `Spec C_{g'}` is Mathlib's
`AlgebraicGeometry.basicOpenIsoSpecAway`.

Finite local freeness of `π` is established through
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`
([Stacks, Tag 02KB]), the three conditions being exactly the `Module.Finite`,
`Module.Flat` and `Algebra.FinitePresentation` that Tag 00UF supplies.

## References

* [Stacks Project, Tag 02LG](https://stacks.math.columbia.edu/tag/02LG)
* [Stacks Project, Tag 00UF](https://stacks.math.columbia.edu/tag/00UF)
* [Stacks Project, Tag 00UE](https://stacks.math.columbia.edu/tag/00UE)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace Stacks.Topologies.Etale

/-- The spectrum of a finite, finitely presented, faithfully flat algebra is a surjective finite
locally free cover of the spectrum of the base. -/
private lemma finiteLocallyFree_specMap_of_finite_faithfullyFlat
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [Module.Finite R C] [Algebra.FinitePresentation R C] [Module.FaithfullyFlat R C] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap R C))) ∧
      Stacks.Morphisms.IsFiniteLocallyFree (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
  let f := CommRingCat.ofHom (algebraMap R C)
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff f).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  exact ⟨hsurj,
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (Spec.map f)).2 ⟨(IsFinite.SpecMap_iff f).2 (RingHom.finite_algebraMap.mpr inferInstance),
        hflat, (LocallyOfFinitePresentation.SpecMap_iff f).2
          (RingHom.finitePresentation_algebraMap.mpr inferInstance)⟩⟩

/-- A finite, finitely presented, faithfully flat algebra over the global sections of an affine
scheme gives a surjective finite locally free cover of that scheme. -/
private lemma finiteLocallyFree_cover_of_affine {S : Scheme.{u}} [IsAffine S]
    {C : Type u} [CommRing C] [Algebra Γ(S, ⊤) C]
    [Module.Finite Γ(S, ⊤) C] [Algebra.FinitePresentation Γ(S, ⊤) C]
    [Module.FaithfullyFlat Γ(S, ⊤) C] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv) ∧
      Stacks.Morphisms.IsFiniteLocallyFree
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv) := by
  obtain ⟨hsurj, hflf⟩ :=
    finiteLocallyFree_specMap_of_finite_faithfullyFlat (R := Γ(S, ⊤)) (C := C)
  have := hsurj
  obtain ⟨hfin, hflat, hfp⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)))).1 hflf
  have := hfin
  have := hflat
  have := hfp
  exact ⟨inferInstance,
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv)).2
        ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The map on global sections of an étale morphism of affine schemes is an étale ring map. -/
private lemma etale_appTop_of_affine {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Etale f] : f.appTop.hom.Etale := by
  simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
    (f.etale_appLE (isAffineOpen_top S) (isAffineOpen_top X) (by simp))

/-- An étale neighbourhood admits an affine chart around the distinguished point lying over an
affine open of the base, on which its structure morphism is an étale ring map. -/
private lemma exists_affine_etale_chart {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    ∃ (V : S.affineOpens) (_ : s ∈ V.1) (A : U.scheme.affineOpens) (_ : U.point ∈ A.1)
      (hAV : A.1 ≤ U.toBase ⁻¹ᵁ V.1), (U.toBase.appLE V.1 A.1 hAV).hom.Etale := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hs, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have huV : U.toBase U.point ∈ V := by simpa [U.map_point] using hs
  obtain ⟨-, ⟨A, hA, rfl⟩, hu, hAV⟩ :=
    U.scheme.isBasis_affineOpens.exists_subset_of_mem_open huV
      (V.2.preimage U.toBase.continuous)
  exact ⟨⟨V, hV⟩, hs, ⟨A, hA⟩, hu, hAV, U.toBase.etale_appLE hV hA hAV⟩

/-- **Stacks Project, Tag 00UF, for an arbitrary étale algebra.** Let `B` be an étale
`R`-algebra and `q` a prime of `B`. There is a finite, finitely presented, faithfully flat
`R`-algebra `C` such that every prime `q'` of `C` with the same contraction to `R` as `q` admits
a `g' ∉ q'` and an `R`-algebra map `B → C_{g'}` pulling `q' C_{g'}` back to `q`.

By Stacks Tag 00UE the algebra `B` is standard étale after inverting some `g ∉ q`, and Tag 00UF
applies to that localization. -/
private lemma exists_finite_faithfullyFlat_local_maps
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (q : Ideal B) [q.IsPrime] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Module.Finite R C)
      (_ : Algebra.FinitePresentation R C) (_ : Module.FaithfullyFlat R C),
      ∀ (q' : Ideal C) (_ : q'.IsPrime), q.under R = q'.under R →
        ∃ g' ∉ q', ∃ φ : B →+* Localization.Away g',
          φ.comp (algebraMap R B) =
              (algebraMap C (Localization.Away g')).comp (algebraMap R C) ∧
            (q'.map (algebraMap C (Localization.Away g'))).comap φ = q := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := B) q
  have := hstd
  obtain ⟨C, hC, hRC, hfin, hfp, hff, H⟩ :=
    Algebra.IsStandardEtale.exists_finite_faithfullyFlat_forall_exists_comp_eq_comap_eq
      R (Localization.Away g)
  let := hC
  let := hRC
  have := hfin
  have := hfp
  have := hff
  refine ⟨C, hC, hRC, hfin, hfp, hff, fun q' hq' hqR ↦ ?_⟩
  have := hq'
  have hd : Disjoint (Submonoid.powers g : Set B) (q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg
  have hQ : (q.map (algebraMap B (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ q inferInstance hd
  have hQR : (q.map (algebraMap B (Localization.Away g))).under R = q'.under R := by
    rwa [← Ideal.under_under (A := R) (B := B),
      IsLocalization.under_map_of_isPrime_disjoint (.powers g) _
        (show q.IsPrime from inferInstance) hd]
  obtain ⟨g', hg', hloc⟩ := H _ hQ q' hq' hQR
  obtain ⟨φ, hφ, hqφ⟩ := hloc (Localization.Away g') inferInstance inferInstance inferInstance
  refine ⟨g', hg', φ.comp (algebraMap B (Localization.Away g)), ?_, ?_⟩
  · rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R B (Localization.Away g), hφ]
  · rw [← Ideal.comap_comap, hqφ]
    exact IsLocalization.under_map_of_isPrime_disjoint (.powers g) _
      (show q.IsPrime from inferInstance) hd

/-- The contraction along `f.appTop` of the prime of `Γ(X, ⊤)` at `x` is the prime of `Γ(Y, ⊤)`
at `f x`. -/
private lemma comap_isoSpec_hom_apply {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : X) : (X.isoSpec.hom x).asIdeal.comap f.appTop.hom = (Y.isoSpec.hom (f x)).asIdeal := by
  change (Spec.map f.appTop (X.isoSpec.hom x)).asIdeal = _
  rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply]

/-- Under `basicOpenIsoSpecAway`, a point `t` of `D(g) ⊆ Spec R` corresponds to the prime
`t R_g` of `Spec R_g`. -/
private lemma basicOpenIsoSpecAway_hom_apply_asIdeal {R : CommRingCat.{u}} (g : R)
    (t : Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g)) :
    ((basicOpenIsoSpecAway g).hom t).asIdeal =
      t.1.asIdeal.map (algebraMap R (Localization.Away g)) := by
  have := t.1.isPrime
  have ep : Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))
      ((basicOpenIsoSpecAway g).hom t) = t.1 := by
    rw [← Scheme.Hom.comp_apply, basicOpenIsoSpecAway_hom_SpecMap]
    rfl
  have hd : Disjoint (Submonoid.powers g : Set R) t.1.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr t.2
  exact (IsLocalization.orderEmbedding (.powers g) (Localization.Away g)).injective <|
    (congrArg PrimeSpectrum.asIdeal ep).trans
      (IsLocalization.under_map_of_isPrime_disjoint (.powers g) _ inferInstance hd).symm

/-- A ring map `φ : Γ(X, ⊤) → C_g` compatible with an affine `f : X ⟶ Y` makes the square from
`D(g) ⊆ Spec C` to `Y` commute. -/
private lemma basicOpen_ι_comp_eq {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    {C : Type u} [CommRing C] [Algebra Γ(Y, ⊤) C] (g : C) (φ : Γ(X, ⊤) →+* Localization.Away g)
    (hφ : φ.comp f.appTop.hom =
      (algebraMap C (Localization.Away g)).comp (algebraMap Γ(Y, ⊤) C)) :
    Scheme.Opens.ι (X := Spec (CommRingCat.of C)) (PrimeSpectrum.basicOpen g) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) ≫ Y.isoSpec.inv =
      ((basicOpenIsoSpecAway (R := CommRingCat.of C) g).hom ≫
        Spec.map (CommRingCat.ofHom φ) ≫ X.isoSpec.inv) ≫ f := by
  have hring : f.appTop ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C) ≫
        CommRingCat.ofHom (algebraMap C (Localization.Away g)) :=
    CommRingCat.hom_ext hφ
  have hspec : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map f.appTop =
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away g))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  have hbasic : Scheme.Opens.ι (X := Spec (CommRingCat.of C)) (PrimeSpectrum.basicOpen g) =
      (basicOpenIsoSpecAway (R := CommRingCat.of C) g).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away g))) :=
    (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of C) g).symm
  rw [hbasic]
  simp only [Category.assoc, ← Scheme.isoSpec_inv_naturality f, reassoc_of% hspec]

/-- The point of `D(g) ⊆ Spec C` at `t` maps to `x` under `Spec φ` when `φ` pulls `t C_g` back to
the prime of `x`. -/
private lemma basicOpenIsoSpecAway_comp_apply_eq {X : Scheme.{u}} [IsAffine X] {C : Type u}
    [CommRing C] (g : C) (φ : Γ(X, ⊤) →+* Localization.Away g) (x : X)
    (t : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C)) (PrimeSpectrum.basicOpen g))
    (hφ : (t.1.asIdeal.map (algebraMap C (Localization.Away g))).comap φ =
      (X.isoSpec.hom x).asIdeal) :
    ((basicOpenIsoSpecAway (R := CommRingCat.of C) g).hom ≫
      Spec.map (CommRingCat.ofHom φ) ≫ X.isoSpec.inv) t = x := by
  have h : Spec.map (CommRingCat.ofHom φ) ((basicOpenIsoSpecAway (R := CommRingCat.of C) g).hom t) =
      X.isoSpec.hom x := by
    apply PrimeSpectrum.ext
    change ((basicOpenIsoSpecAway (R := CommRingCat.of C) g).hom t).asIdeal.comap φ = _
    rwa [basicOpenIsoSpecAway_hom_apply_asIdeal]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]
  simp

/-- **Stacks Project, Tag 02LG.** After restricting the base to an affine open neighbourhood of
the point, an étale neighbourhood is locally dominated, at every point above the distinguished
point, by a surjective finite locally free morphism. -/
@[stacks 02LG]
theorem exists_isFiniteLocallyFree_surjective_locally_lift_etaleNeighborhood
    {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s) :
    ∃ (V : S.affineOpens) (hs : s ∈ V.1) (T : Scheme.{u}) (π : T ⟶ V.1)
      (_ : Surjective π) (_ : Stacks.Morphisms.IsFiniteLocallyFree π),
      ∀ (t : T) (_ : π t = ⟨s, hs⟩),
        ∃ (W : T.Opens) (ht : t ∈ W) (h : (W : Scheme.{u}) ⟶ U.scheme),
          W.ι ≫ π ≫ V.1.ι = h ≫ U.toBase ∧ h ⟨t, ht⟩ = U.point := by
  obtain ⟨V, hs, A, hu, hAV, -⟩ := exists_affine_etale_chart U
  let f : (A.1 : Scheme.{u}) ⟶ (V.1 : Scheme.{u}) := U.toBase.resLE V.1 A.1 hAV
  have : Etale f := inferInstance
  let : Algebra Γ(V.1, ⊤) Γ(A.1, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra.Etale Γ(V.1, ⊤) Γ(A.1, ⊤) := (etale_appTop_of_affine f).toAlgebra
  let x : (A.1 : Scheme.{u}) := ⟨U.point, hu⟩
  let y : (V.1 : Scheme.{u}) := ⟨s, hs⟩
  let q : Ideal Γ(A.1, ⊤) := ((A.1 : Scheme.{u}).isoSpec.hom x).asIdeal
  let : q.IsPrime := ((A.1 : Scheme.{u}).isoSpec.hom x).isPrime
  obtain ⟨C, hC, hRC, hfin, hfp, hff, H⟩ :=
    exists_finite_faithfullyFlat_local_maps Γ(V.1, ⊤) Γ(A.1, ⊤) q
  let := hC
  let := hRC
  have := hfin
  have := hfp
  have := hff
  let T : Scheme.{u} := Spec (CommRingCat.of C)
  let π : T ⟶ (V.1 : Scheme.{u}) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(V.1, ⊤) C)) ≫ (V.1 : Scheme.{u}).isoSpec.inv
  obtain ⟨hπsurj, hπflf⟩ := finiteLocallyFree_cover_of_affine (S := V.1) (C := C)
  refine ⟨V, hs, T, π, hπsurj, hπflf, fun t ht ↦ ?_⟩
  let q' : Ideal C := t.asIdeal
  let : q'.IsPrime := t.isPrime
  have hqR : q.under Γ(V.1, ⊤) = q'.under Γ(V.1, ⊤) := by
    refine (comap_isoSpec_hom_apply f x).trans ?_
    change _ = ((Spec.map (CommRingCat.ofHom (algebraMap Γ(V.1, ⊤) C))) t).asIdeal
    congr 1
    calc
      _ = (π ≫ (V.1 : Scheme.{u}).isoSpec.hom) t := by
        rw [Scheme.Hom.comp_apply, ht,
          show f x = y from Subtype.ext (by simp [f, x, y, U.map_point])]
      _ = _ := by
        dsimp only [π]
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨g', hg', φ, hφ, hqφ⟩ := H q' inferInstance hqR
  let W : T.Opens := PrimeSpectrum.basicOpen g'
  have htW : t ∈ W := hg'
  let hA : (W : Scheme.{u}) ⟶ (A.1 : Scheme.{u}) :=
    (basicOpenIsoSpecAway (R := CommRingCat.of C) g').hom ≫
      Spec.map (CommRingCat.ofHom φ) ≫ (A.1 : Scheme.{u}).isoSpec.inv
  refine ⟨W, htW, hA ≫ A.1.ι, ?_, ?_⟩
  · calc W.ι ≫ π ≫ V.1.ι = hA ≫ f ≫ V.1.ι := congrArg (· ≫ V.1.ι) (basicOpen_ι_comp_eq f g' φ hφ)
      _ = hA ≫ A.1.ι ≫ U.toBase := by simp [f, Scheme.Hom.resLE_comp_ι]
      _ = (hA ≫ A.1.ι) ≫ U.toBase := rfl
  · change (A.1.ι) (hA ⟨t, htW⟩) = U.point
    rw [basicOpenIsoSpecAway_comp_apply_eq g' φ x ⟨t, htW⟩ hqφ, Scheme.Opens.ι_apply]

end Stacks.Topologies.Etale

end
