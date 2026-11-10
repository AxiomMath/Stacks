module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.RingTheory.Etale.FiniteFlatCover

/-!
# A surjective étale morphism of affine schemes is dominated by a finite locally free one

This file proves [Stacks, Tag 02LH]: if `f : U ⟶ S` is a surjective étale morphism of affine
schemes, then there are a surjective finite locally free morphism `p : T ⟶ S` and a *finite*
open covering of `T` each of whose members maps to `U` over `S`.

The whole mathematical content sits in commutative algebra and is already available as
[Stacks, Tag 00UG], `Algebra.Etale.exists_finite_faithfullyFlat_forall_exists_comp_eq`: for an
étale, faithfully flat ring map `R → A` there is a finite, finitely presented, faithfully flat
`R`-algebra `S'` such that for every prime `q'` of `S'` there is a `g' ∉ q'` through which
`R → S'_{g'}` factors over `A`. Taking `T = Spec S'` and the basic opens `D(g')` turns that
into the geometric statement; the covering is made finite by quasi-compactness of `T`.

## Main results

* `Stacks.Topologies.Etale.exists_isFiniteLocallyFree_surjective_finite_openCover_lift` is
  [Stacks, Tag 02LH].

## Implementation notes

The affine schemes are not assumed to be literal spectra, so the construction is carried out
on `Spec Γ(S, ⊤)` and `Spec Γ(U, ⊤)` and transported through `AlgebraicGeometry.Scheme.isoSpec`.
The one identity this needs is `AlgebraicGeometry.Scheme.toSpecΓ_naturality`, recorded here as
`Stacks.Topologies.Etale.isoSpec_inv_comp`.

Finite local freeness of the constructed morphism is established through
`Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`
([Stacks, Tag 02KB]) rather than directly from the sheaf-level definition, since the three
conditions it reduces to are exactly `Module.Finite`, `Module.Flat` and
`Algebra.FinitePresentation` of the algebra produced by Tag 00UG.

## References

* [Stacks Project, Tag 02LH](https://stacks.math.columbia.edu/tag/02LH)
* [Stacks Project, Tag 00UG](https://stacks.math.columbia.edu/tag/00UG)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Topologies.Etale

/-- **Stacks Project, Tag 00UG, in covering form.** For an étale, faithfully flat ring map
`R → A` there are a finite, finitely presented, faithfully flat `R`-algebra `S'` and *finitely
many* elements `c i` of `S'` whose basic opens cover `Spec S'`, such that each localization
`S'_{c i}` receives `A` compatibly with the maps from `R`.

This is `Algebra.Etale.exists_finite_faithfullyFlat_forall_exists_comp_eq` together with
quasi-compactness of `Spec S'`. -/
theorem exists_finite_faithfullyFlat_finite_away_cover (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.Etale R A] [Module.FaithfullyFlat R A] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S'),
      Module.Finite R S' ∧ Algebra.FinitePresentation R S' ∧ Module.FaithfullyFlat R S' ∧
        ∃ (ι : Type u) (_ : Finite ι) (c : ι → S'),
          (⋃ i, (PrimeSpectrum.basicOpen (c i) : Set (PrimeSpectrum S'))) = Set.univ ∧
            ∃ ψ : ∀ i, A →+* Localization.Away (c i), ∀ i,
              (ψ i).comp (algebraMap R A) =
                (algebraMap S' (Localization.Away (c i))).comp (algebraMap R S') := by
  classical
  obtain ⟨S', _, _, hfin, hfp, hff, hS'⟩ :=
    Algebra.Etale.exists_finite_faithfullyFlat_forall_exists_comp_eq.{u, u, u} R A
  choose c hc hcB using fun q : PrimeSpectrum S' ↦ hS' q.asIdeal q.isPrime
  choose ψ hψ using fun q : PrimeSpectrum S' ↦
    hcB q (Localization.Away (c q)) inferInstance inferInstance inferInstance
  have hopen : ∀ q : PrimeSpectrum S',
      IsOpen (PrimeSpectrum.basicOpen (c q) : Set (PrimeSpectrum S')) :=
    fun q ↦ (PrimeSpectrum.basicOpen (c q)).2
  have hsub : (Set.univ : Set (PrimeSpectrum S')) ⊆
      ⋃ q, (PrimeSpectrum.basicOpen (c q) : Set (PrimeSpectrum S')) := fun q _ ↦
    Set.mem_iUnion.2 ⟨q, hc q⟩
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover _ hopen hsub
  refine ⟨S', inferInstance, inferInstance, hfin, hfp, hff, {q : PrimeSpectrum S' // q ∈ J},
    inferInstance, fun q ↦ c q.1, Set.eq_univ_of_univ_subset ?_, fun q ↦ ψ q.1, fun q ↦ hψ q.1⟩
  refine hJ.trans (le_of_eq ?_)
  exact (Set.iUnion_subtype (fun q : PrimeSpectrum S' ↦ q ∈ J)
    fun q ↦ (PrimeSpectrum.basicOpen (c q.1) : Set (PrimeSpectrum S'))).symm

/-- Transporting a morphism of affine schemes to the spectra of its global sections. -/
theorem isoSpec_inv_comp {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    X.isoSpec.inv ≫ f = Spec.map f.appTop ≫ Y.isoSpec.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  simpa only [Scheme.isoSpec_hom] using Scheme.toSpecΓ_naturality f

/-- **Stacks Project, Tag 02LH.** A surjective étale morphism of affine schemes is dominated
by a surjective finite locally free morphism whose source has a finite open covering lifting
to the given étale cover. -/
@[stacks 02LH]
theorem exists_isFiniteLocallyFree_surjective_finite_openCover_lift
    {U S : Scheme.{u}} [IsAffine U] [IsAffine S] (f : U ⟶ S) [Etale f] [Surjective f] :
    ∃ (T : Scheme.{u}) (p : T ⟶ S),
      Stacks.Morphisms.IsFiniteLocallyFree p ∧ Surjective p ∧
        ∃ 𝒯 : T.OpenCover.{u}, Finite 𝒯.I₀ ∧
          ∃ g : ∀ i, 𝒯.X i ⟶ U, ∀ i, 𝒯.f i ≫ p = g i ≫ f := by
  classical
  let _ : Algebra ↑Γ(S, ⊤) ↑Γ(U, ⊤) := f.appTop.hom.toAlgebra
  have hetale : Algebra.Etale ↑Γ(S, ⊤) ↑Γ(U, ⊤) :=
    HasRingHomProperty.iff_of_isAffine.mp ‹Etale f›
  have hspec : Spec.map f.appTop = U.isoSpec.inv ≫ f ≫ S.isoSpec.hom := by
    rw [← Category.assoc, isoSpec_inv_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomap : Function.Surjective
      (PrimeSpectrum.comap (algebraMap ↑Γ(S, ⊤) ↑Γ(U, ⊤))) := by
    have : Surjective (Spec.map f.appTop) := by rw [hspec]; infer_instance
    rwa [surjective_iff] at this
  have : Module.FaithfullyFlat ↑Γ(S, ⊤) ↑Γ(U, ⊤) :=
    Module.FaithfullyFlat.of_comap_surjective hcomap
  obtain ⟨S', _, _, hfin, hfp, hff, ι, hι, c, hcov, ψ, hψ⟩ :=
    exists_finite_faithfullyFlat_finite_away_cover ↑Γ(S, ⊤) ↑Γ(U, ⊤)
  refine ⟨Spec (CommRingCat.of S'),
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S')) ≫ S.isoSpec.inv, ?_, ?_, ?_⟩
  · rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S'))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S'))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr hff.toFlat)
    have : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S'))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr hfp)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S'))) := by
      rw [surjective_iff]
      exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    infer_instance
  · have hcovers : ∀ x : ↥(Spec (CommRingCat.of S')), ∃ (i : ι)
        (y : ↥(Spec (CommRingCat.of (Localization.Away (c i))))),
        Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (c i)))) y = x := by
      intro x
      have hx : (x : PrimeSpectrum S') ∈
          ⋃ i, (PrimeSpectrum.basicOpen (c i) : Set (PrimeSpectrum S')) := by
        rw [hcov]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, (PrimeSpectrum.localization_away_comap_range (Localization.Away (c i)) (c i)).ge hi⟩
    refine ⟨Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι
      (fun i ↦ Spec (CommRingCat.of (Localization.Away (c i))))
      (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (c i))))) hcovers,
      hι, fun i ↦ Spec.map (CommRingCat.ofHom (ψ i)) ≫ U.isoSpec.inv, fun i ↦ ?_⟩
    change Spec.map (CommRingCat.ofHom (algebraMap S' (Localization.Away (c i)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, ⊤) S')) ≫ S.isoSpec.inv =
      (Spec.map (CommRingCat.ofHom (ψ i)) ≫ U.isoSpec.inv) ≫ f
    rw [Category.assoc, isoSpec_inv_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.hom_ext (hψ i)).symm

end Stacks.Topologies.Etale

end
