module

public import StacksFrontier.RingTheory.LocalIso.IdentifiesLocalRings
public import Mathlib.RingTheory.LocalIso
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Local isomorphisms and the identification of local rings

A ring map is a *local isomorphism* if, near each prime of its target, it induces an open
immersion on spectra. It *identifies local rings* if the induced map between the localizations
at every prime of the target and at its contraction is an isomorphism. For a local isomorphism
finitely many principal opens cover the target spectrum, and each of the corresponding
localizations is a principal localization of the source as well.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsLocalIsomorphism`: the source's notion of a local isomorphism:
  every prime of the target lies in a principal open `D(g)` such that `Spec(B_g) → Spec(A)` is an
  open immersion of schemes.

## Main results

* `AlgebraicGeometry.ProEtale.isLocalIsomorphism_iff_isLocalIso`: the source's notion agrees with
  Mathlib's `Algebra.IsLocalIso`, where the principal localizations `B_g` are required to be
  principal localizations of `A`.
* `AlgebraicGeometry.ProEtale.exists_fin_localization_away_of_isLocalIsomorphism`: a local
  isomorphism admits a finite cover by principal localizations which are principal localizations
  of the source.
* `AlgebraicGeometry.ProEtale.exists_fin_localization_away`: the same conclusion for
  `Algebra.IsLocalIso`, at arbitrary universes.

## Implementation notes

Mathlib's `Algebra.IsLocalIso` asks for `B_g` to be a localization `A_f`, which is a priori
stronger than the open immersion of the source: the image of `Spec(B_g)` need not be a principal
open of `Spec(A)`. The bridge shrinks `g`: inside the image of `Spec(B_g)` a principal open `D(f)`
around a given point is the isomorphic image of `D(g f)`, so `B_{g f} ≅ A_f` over `A`.

In the finite cover, the equation saying that the chosen elements of the target generate the unit
ideal expresses that their principal opens cover the target spectrum. `IsLocalization.Away`
expresses that the canonical map from the source to each of these localizations is a localization
away from the corresponding source element, hence identifies the two principal localizations as
algebras over the source.

## References

* [Stacks Project, Tag 096E](https://stacks.math.columbia.edu/tag/096E)
* [Stacks Project, Tag 096J](https://stacks.math.columbia.edu/tag/096J)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

universe u v

/-- An algebra satisfying Mathlib's `Algebra.IsLocalIso` admits a finite cover by principal
localizations that are principal localizations of the source. This is the conclusion of
[Stacks, Tag 096J] for Mathlib's notion; the statement for the source's notion of a local
isomorphism is `AlgebraicGeometry.ProEtale.exists_fin_localization_away_of_isLocalIsomorphism`. -/
theorem exists_fin_localization_away
    (A : Type u) (B : Type v) [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Algebra.IsLocalIso A B] :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, IsLocalization.Away (f i) (Localization.Away (g i)) := by
  classical
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top A B)
  let g : Fin t.card → B := fun j => (t.equivFin.symm j).1
  have hspan' : Ideal.span (Set.range g) = ⊤ := by
    change Ideal.span (Set.range ((Subtype.val : t → B) ∘ t.equivFin.symm)) = ⊤
    simpa [Set.range_comp] using hspan
  have hexists (j : Fin t.card) : ∃ f : A, IsLocalization.Away f (Localization.Away (g j)) := by
    let : Algebra.IsStandardOpenImmersion A (Localization.Away (g j)) := ht (by simp [g])
    exact Algebra.IsStandardOpenImmersion.exists_away A (Localization.Away (g j))
  exact ⟨t.card, g, fun j => Classical.choose (hexists j), hspan',
    fun j => Classical.choose_spec (hexists j)⟩

open CategoryTheory

/-- **Stacks 096E (1).** A ring map `A → B` is a *local isomorphism* if for every prime `𝔮` of
`B` there is `g ∈ B`, `g ∉ 𝔮`, such that `A → B_g` induces an open immersion
`Spec(B_g) → Spec(A)`. -/
@[stacks 096E "part (1): local isomorphism, open immersion of spectra of principal localizations"]
def IsLocalIsomorphism (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  ∀ q : Ideal B, q.IsPrime → ∃ g ∉ q,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))))

/-- If `Spec(C) → Spec(A)` is an open immersion, then every prime `𝔮` of `C` avoids the image of
some `f ∈ A` such that `C_f` is a localization of `A` away from `f`. -/
theorem exists_isLocalization_away_of_isOpenImmersion {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (q : Ideal C) [q.IsPrime] :
    ∃ f : A, algebraMap A C f ∉ q ∧
      IsLocalization.Away f (Localization.Away (algebraMap A C f)) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A C))
  have hrange : Set.range φ = Set.range (PrimeSpectrum.comap (algebraMap A C)) := rfl
  let x : PrimeSpectrum C := ⟨q, inferInstance⟩
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self x) (hrange ▸ φ.isOpenEmbedding.isOpen_range)
  have hfq : algebraMap A C f ∉ q := hxf
  refine ⟨f, hfq, ?_⟩
  let L := Localization.Away (algebraMap A C f)
  have hL : Set.range (PrimeSpectrum.comap (algebraMap A L)) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    ext p
    constructor
    · rintro ⟨Q, rfl⟩
      change f ∉ Q.asIdeal.comap (algebraMap A L)
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A C L]
      exact fun hmem => Q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
        (IsLocalization.Away.algebraMap_isUnit (algebraMap A C f)))
    · intro hp
      obtain ⟨P, rfl⟩ := hfU hp
      have hP : P ∈ (PrimeSpectrum.basicOpen (algebraMap A C f) : Set (PrimeSpectrum C)) := hp
      rw [← PrimeSpectrum.localization_away_comap_range L] at hP
      obtain ⟨Q, rfl⟩ := hP
      refine ⟨Q, ?_⟩
      rw [IsScalarTower.algebraMap_eq A C L, PrimeSpectrum.comap_comp_apply]
  have hφL : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A L))) := by
    rw [IsScalarTower.algebraMap_eq A C L, CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let e := IsOpenImmersion.isoOfRangeEq (Spec.map (CommRingCat.ofHom (algebraMap A L)))
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
    (hL.trans (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm)
  let ρ := Spec.preimage e.hom
  let ρ' := Spec.preimage e.inv
  have h₁ : ρ ≫ ρ' = 𝟙 _ := Spec.map_injective (by simp [ρ, ρ'])
  have h₂ : ρ' ≫ ρ = 𝟙 _ := Spec.map_injective (by simp [ρ, ρ'])
  have hcomm : CommRingCat.ofHom (algebraMap A (Localization.Away f)) ≫ ρ =
      CommRingCat.ofHom (algebraMap A L) :=
    Spec.map_injective (by
      rw [Spec.map_comp, Spec.map_preimage]
      exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
  let eRing : Localization.Away f ≃+* L :=
    RingEquiv.ofRingHom ρ.hom ρ'.hom
      (by rw [← CommRingCat.hom_comp, h₂, CommRingCat.hom_id])
      (by rw [← CommRingCat.hom_comp, h₁, CommRingCat.hom_id])
  let eAlg : Localization.Away f ≃ₐ[A] L := AlgEquiv.ofRingEquiv (f := eRing)
    (fun a => congrArg (fun φ => φ.hom a) hcomm)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f) eAlg

/-- If `Spec(C) → Spec(A)` is an open immersion, then `A → C` is a local isomorphism in the sense
of Mathlib's `Algebra.IsLocalIso`. -/
theorem isLocalIso_of_isOpenImmersion {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    Algebra.IsLocalIso A C where
  exists_notMem_isStandardOpenImmersion q _ := by
    obtain ⟨f, hf, hloc⟩ := exists_isLocalization_away_of_isOpenImmersion h q
    exact ⟨_, hf, ⟨f, hloc⟩⟩

/-- The source's notion of a local isomorphism, `IsLocalIsomorphism`, is equivalent to Mathlib's
`Algebra.IsLocalIso`. -/
theorem isLocalIsomorphism_iff_isLocalIso (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : IsLocalIsomorphism A B ↔ Algebra.IsLocalIso A B := by
  constructor
  · intro h
    refine Algebra.IsLocalIso.of_span_eq_top (s := {g : B | IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))))}) ?_
      fun g hg => isLocalIso_of_isOpenImmersion hg
    by_contra hne
    obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgm, hg⟩ := h m hm.isPrime
    exact hgm (hms (Ideal.subset_span hg))
  · intro h q hq
    obtain ⟨g, hgq, hstd⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := A) q
    obtain ⟨r, hr⟩ := hstd.exists_away
    exact ⟨g, hgq, IsOpenImmersion.of_isLocalization r⟩

/-- **Stacks 096J.** Let `A → B` be a local isomorphism. Then there exist `n ≥ 0`,
`g_1, …, g_n ∈ B` and `f_1, …, f_n ∈ A` such that `(g_1, …, g_n) = B` and `A_{f_i} ≅ B_{g_i}`,
the isomorphism being the canonical one: `B_{g_i}` is a localization of `A` away from `f_i`. -/
@[stacks 096J "local isomorphism in the open-immersion form of 096E (1); A_{f_i} ≅ B_{g_i} as \
  A-algebras"]
theorem exists_fin_localization_away_of_isLocalIsomorphism (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] (h : IsLocalIsomorphism A B) :
    ∃ (n : ℕ) (g : Fin n → B) (f : Fin n → A),
      Ideal.span (Set.range g) = ⊤ ∧
        ∀ i, IsLocalization.Away (f i) (Localization.Away (g i)) :=
  haveI := (isLocalIsomorphism_iff_isLocalIso A B).mp h
  exists_fin_localization_away A B

end AlgebraicGeometry.ProEtale

end
