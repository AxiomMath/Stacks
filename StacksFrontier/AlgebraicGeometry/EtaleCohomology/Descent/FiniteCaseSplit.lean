module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Replacing an étale covering of an affine scheme by a single affine one

The finite case of property (B) for the étale topology, [Stacks, Tag 04DQ], is reduced by
`Stacks.EtaleCohomology.HasLocalDecompositionAt.of_etale` to a question about a finite ring
extension `A → B` and an étale covering of `Spec B`. The first step of the argument replaces that
covering by a *single* affine étale surjection `Spec C → Spec B`, obtained by taking the product
of the rings of a finite affine refinement of the covering: a finite product of rings is the ring
of the disjoint union of their spectra.

This file performs that replacement. It is purely a change of presentation of the covering, and
the subordination data — the open immersions of the pieces into the members of the original
covering — is retained, because the decomposition that property (B) asks for must be subordinate
to the original covering.

## Main results

* `Stacks.EtaleCohomology.exists_affine_etaleNeighborhood_finite`: for a finite `f`, an affine
  étale neighbourhood of a point of the base over which the fibre product is affine and
  module-finite.
* `Stacks.EtaleCohomology.exists_finite_etale_refinement_hom`: an étale covering of an affine
  scheme `Spec B` admits a finite refinement by affine schemes `Spec (C k)`, with each `C k` étale
  over `B` and each piece mapping to a member of the covering by an open immersion.
* `Stacks.EtaleCohomology.surjective_comap_pi`: if a family of algebras jointly hits every prime
  of the base, then the product algebra is surjective on spectra.
* `Stacks.EtaleCohomology.isOpen_range_comap_pi`: the spectrum map of a finite product of étale
  algebras has open image.
* `Stacks.EtaleCohomology.etaleNeighborhoodSpec`: an étale algebra with a prime over a point is an
  étale neighbourhood of that point of the spectrum of the base.
* `Stacks.EtaleCohomology.sigmaSpecIsoOfAlgEquiv`: a product decomposition of a ring is a
  disjoint-union decomposition of its spectrum.
* `Stacks.EtaleCohomology.pullbackBaseChangeMap_eq`: the comparison morphism of a further base
  change is a projection of a pasted fibre product.
* `Stacks.EtaleCohomology.pullbackBaseChangeSpecIso`: **a further base change of an affine
  situation is the spectrum of a tensor product**, together with
  `Stacks.EtaleCohomology.pullbackBaseChangeSpecIso_hom_comp_pullbackBaseChangeMap` and
  `Stacks.EtaleCohomology.pullbackBaseChangeSpecIso_hom_comp_snd`, which say that under this
  identification the comparison morphism is `b ↦ b ⊗ 1` and the projection to the new base is
  `a ↦ 1 ⊗ a`.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The affine situation the finite case of property (B) reduces to.** For a finite `f : X ⟶ Y`,
an étale `g : V ⟶ Y` and a point `v` of `V` there is an *affine* étale neighbourhood `V₀` of `v`
over which the fibre product `X ×ₗᵧ V₀` is affine and its ring is module-finite over the ring of
`V₀`.

Affineness of the fibre product is not an assumption but a consequence: `X ×ₗᵧ V₀ ⟶ V₀` is the
base change of the finite morphism `f`, hence finite, hence affine over the affine `V₀`. Combined
with `Stacks.EtaleCohomology.HasLocalDecompositionAt.of_etale`, which allows the local
decomposition to be sought after any étale base change of `V`, this is the first step of
[Stacks, Tag 04DQ]: it turns the question into one about a finite ring extension. -/
theorem exists_affine_etaleNeighborhood_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {V : Scheme.{u}} (g : V ⟶ Y) [Etale g] (v : V) :
    ∃ (N : EtaleNeighborhood V v) (_ : IsAffine N.scheme)
      (_ : IsAffine (pullback f (N.toBase ≫ g))),
      (pullback.snd f (N.toBase ≫ g)).appTop.hom.Finite := by
  obtain ⟨N, hN⟩ := exists_affine_etale_neighborhood v
  have hfin : IsFinite (pullback.snd f (N.toBase ≫ g)) := inferInstance
  have haff : IsAffine (pullback f (N.toBase ≫ g)) :=
    isAffine_of_isAffineHom (pullback.snd f (N.toBase ≫ g))
  refine ⟨N, hN, haff, ?_⟩
  exact IsFinite.finite_app (pullback.snd f (N.toBase ≫ g)) ⊤ (isAffineOpen_top N.scheme)

/-- **A finite affine étale refinement of an étale covering of an affine scheme, in ring form.**
Let `B` be a ring and let `U` be an étale covering of `Spec B`. There are finitely many ring maps
`φ k : B ⟶ C k`, each étale, whose spectra jointly cover `Spec B` and each of which factors as an
open immersion into a member `U.X (idx k)` of the covering over `Spec B`.

This is `Stacks.EtaleCohomology.exists_finite_affine_etale_refinement` with the pieces of the
refinement read as rings: a morphism of affine schemes is the spectrum of a unique ring map, by
full faithfulness of `Spec`. Taking the product of the `C k` over the (finite) index set then
replaces the covering by a single affine étale surjection, which is what the finite case of
property (B), [Stacks, Tag 04DQ], works with. -/
theorem exists_finite_etale_refinement_hom {B : CommRingCat.{u}}
    (U : (Spec B).Cover.{u} Scheme.etalePrecoverage) :
    ∃ (K : Type u) (_ : Finite K) (C : K → CommRingCat.{u}) (φ : ∀ k, B ⟶ C k)
      (idx : K → U.I₀) (ρ : ∀ k, Spec (C k) ⟶ U.X (idx k)),
      (∀ k, (φ k).hom.Etale) ∧
      (∀ k, IsOpenImmersion (ρ k)) ∧
      (∀ k, ρ k ≫ U.f (idx k) = Spec.map (φ k)) ∧
      ∀ p : PrimeSpectrum B, ∃ k, p ∈ Set.range (PrimeSpectrum.comap (φ k).hom) := by
  obtain ⟨𝒲, hfin, r, hopen⟩ := exists_finite_affine_etale_refinement U
  refine ⟨𝒲.I₀, hfin, 𝒲.X, fun k => Spec.preimage (𝒲.f k), r.s₀, r.h₀, ?_, hopen, ?_, ?_⟩
  · intro k
    have hEt : Etale (Spec.map (Spec.preimage (𝒲.f k))) := by
      rw [Spec.map_preimage]
      exact 𝒲.map_prop k
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hEt
  · intro k
    exact (r.w₀ k).trans (Spec.map_preimage (𝒲.f k)).symm
  · intro p
    obtain ⟨x, hx⟩ := 𝒲.covers p
    refine ⟨𝒲.idx p, x, ?_⟩
    exact (congrArg (fun m : Spec (𝒲.X (𝒲.idx p)) ⟶ Spec B => m.base x)
      (Spec.map_preimage (𝒲.f (𝒲.idx p)))).trans hx

variable {B : Type u} [CommRing B] {K : Type u} (C : K → Type u) [∀ k, CommRing (C k)]
  [∀ k, Algebra B (C k)]

/-- Evaluating the product algebra at one index is the structure map of that factor. -/
theorem evalRingHom_comp_algebraMap_pi (k : K) :
    (Pi.evalRingHom C k).comp (algebraMap B (∀ k, C k)) = algebraMap B (C k) := rfl

/-- The spectrum of a factor of a product algebra maps into the spectrum of the product. -/
theorem range_comap_subset_range_comap_pi (k : K) :
    Set.range (PrimeSpectrum.comap (algebraMap B (C k))) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap B (∀ k, C k))) := by
  intro p hp
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom C k) q, ?_⟩
  exact (PrimeSpectrum.comap_comp_apply (algebraMap B (∀ k, C k))
    (Pi.evalRingHom C k) q).symm.trans hq

/-- **A jointly surjective family of algebras has surjective product.** If every prime of `B` is
in the image of the spectrum of some `C k`, then `Spec (∀ k, C k) → Spec B` is surjective.

The spectrum of a product of rings contains the spectra of all the factors — it is their disjoint
union when the index set is finite — so joint surjectivity of a family is surjectivity of its
product. -/
theorem surjective_comap_pi
    (h : ∀ p : PrimeSpectrum B, ∃ k, p ∈ Set.range (PrimeSpectrum.comap (algebraMap B (C k)))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (∀ k, C k))) := by
  intro p
  obtain ⟨k, hk⟩ := h p
  exact range_comap_subset_range_comap_pi C k hk

/-- **The spectrum of a finite product of étale algebras has open image.** This is the hypothesis
of `Stacks.EtaleCohomology.exists_notMem_basicOpen_subset_range_comap`, which shrinks the base
until the étale covering becomes surjective. -/
theorem isOpen_range_comap_pi [Finite K] [∀ k, Algebra.Etale B (C k)] :
    IsOpen (Set.range (PrimeSpectrum.comap (algebraMap B (∀ k, C k)))) :=
  (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
    (R := B) (S := ∀ k, C k)).isOpen_range

section SpecTranslation

/-- A ring isomorphism, read in `CommRingCat`, is an isomorphism. -/
theorem isIso_ofHom_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (ε : R ≃+* S) :
    IsIso (CommRingCat.ofHom ε.toRingHom) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr ε.bijective

/-- **An étale algebra with a prime over a point is an étale neighbourhood of that point.** For an
étale `A`-algebra `A'` and a prime `p'` of `A'` lying over a prime `p` of `A`, the scheme `Spec A'`
with the point `p'` is an étale neighbourhood of `p` in `Spec A`.

This is the scheme-theoretic reading of the étale localisation of the base produced by the étale
local structure theorem [Stacks, Tag 00UL], and so of the neighbourhood over which the finite case
of property (B), [Stacks, Tag 04DQ], produces its decomposition. -/
noncomputable def etaleNeighborhoodSpec {A : Type u} [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] [Algebra.Etale A A'] (p : Ideal A) [p.IsPrime] (p' : Ideal A') [p'.IsPrime]
    [p'.LiesOver p] :
    EtaleNeighborhood (Spec (CommRingCat.of A)) (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A) where
  scheme := Spec (CommRingCat.of A')
  point := ⟨p', ‹p'.IsPrime›⟩
  toBase := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  etale_toBase :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.mpr inferInstance)
  map_point := PrimeSpectrum.ext (p'.over_def p).symm

/-- The structure morphism of `etaleNeighborhoodSpec` is the spectrum of the structure map. -/
theorem etaleNeighborhoodSpec_toBase {A : Type u} [CommRing A] (A' : Type u) [CommRing A']
    [Algebra A A'] [Algebra.Etale A A'] (p : Ideal A) [p.IsPrime] (p' : Ideal A') [p'.IsPrime]
    [p'.LiesOver p] :
    (etaleNeighborhoodSpec A' p p').toBase = Spec.map (CommRingCat.ofHom (algebraMap A A')) := rfl

/-- **A product decomposition of a ring is a disjoint-union decomposition of its spectrum.** An
isomorphism `R ≃ₐ[A] ∀ l, F l` onto a product over a finite index type gives an isomorphism from
the coproduct of the `Spec (F l)` to `Spec R`.

This is the scheme-theoretic reading of the decomposition produced by a complete orthogonal family
of idempotents, hence of the clopen decomposition of the fibre product that the finite case of
property (B), [Stacks, Tag 04DQ], asks for. The isomorphism `sigmaSpec` of a finite product of
rings is Mathlib's; the content here is only the composition with the given decomposition. -/
noncomputable def sigmaSpecIsoOfAlgEquiv {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    {L : Type u} [Finite L] (F : L → Type u) [∀ l, CommRing (F l)] [∀ l, Algebra A (F l)]
    (ε : R ≃ₐ[A] (∀ l, F l)) :
    (∐ fun l => Spec (CommRingCat.of (F l))) ≅ Spec (CommRingCat.of R) :=
  have : IsIso (CommRingCat.ofHom ε.toRingEquiv.toRingHom) :=
    isIso_ofHom_ringEquiv ε.toRingEquiv
  (asIso (sigmaSpec fun l => CommRingCat.of (F l))).trans
    (asIso (Spec.map (CommRingCat.ofHom ε.toRingEquiv.toRingHom)))

/-- The piece with index `l` of `sigmaSpecIsoOfAlgEquiv` maps to `Spec R` by the spectrum of the
`l`-th component of the decomposition. -/
theorem sigmaSpecIsoOfAlgEquiv_ι {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]
    {L : Type u} [Finite L] (F : L → Type u) [∀ l, CommRing (F l)] [∀ l, Algebra A (F l)]
    (ε : R ≃ₐ[A] (∀ l, F l)) (l : L) :
    Sigma.ι _ l ≫ (sigmaSpecIsoOfAlgEquiv F ε).hom =
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun l => F l) l).comp
        ε.toRingEquiv.toRingHom)) := by
  have h : (sigmaSpecIsoOfAlgEquiv F ε).hom =
      sigmaSpec (fun l => CommRingCat.of (F l)) ≫
        Spec.map (CommRingCat.ofHom ε.toRingEquiv.toRingHom) := rfl
  rw [h, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  rfl

section FurtherBaseChange

open TensorProduct

/-- **The comparison morphism of a further base change is a projection of a pasted pullback.**
`pullbackBaseChangeMap f g n` is, under the pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, the first projection of
`(X ×ₗᵧ V) ×ᵥ W ⟶ X ×ₗᵧ V`.

Both morphisms satisfy the two equations `pullbackBaseChangeMap_fst` and
`pullbackBaseChangeMap_snd`, which determine a morphism into a fibre product. Reading the
comparison morphism this way is what lets the further base change be computed when everything in
sight is affine: `X ×ₗᵧ W` becomes a fibre product of *two* affine schemes over an affine base,
hence the spectrum of a tensor product. -/
theorem pullbackBaseChangeMap_eq {X Y V W : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (n : W ⟶ V) :
    pullbackBaseChangeMap f g n =
      (pullbackLeftPullbackSndIso f g n).inv ≫ pullback.fst (pullback.snd f g) n := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackBaseChangeMap_fst, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  · rw [pullbackBaseChangeMap_snd, Category.assoc]
    exact (pullbackLeftPullbackSndIso_inv_fst_snd f g n).symm

/-- **A further base change of an affine situation is the spectrum of a tensor product.** Let
`f : X ⟶ Y` and `g : V ⟶ Y`, let `V` be identified with `Spec A` and the fibre product `X ×ₗᵧ V`
with `Spec B` in such a way that the projection `X ×ₗᵧ V ⟶ V` becomes `Spec` of the structure map
`A → B`, and let `n : Spec A'' ⟶ V` be `Spec` of a ring map `A → A''`. Then the further base change
`X ×ₗᵧ Spec A''` is `Spec (B ⊗[A] A'')`.

The fibre product over `V` of `X ×ₗᵧ V ⟶ V` and `n` is the fibre product of `X ⟶ Y` and
`n ≫ g` by `CategoryTheory.Limits.pullbackLeftPullbackSndIso`, and under the two identifications it
is the fibre product of two affine schemes over an affine base, which is
`AlgebraicGeometry.pullbackSpecIso`.

This is the identification the finite case of property (B), [Stacks, Tag 04DQ], needs: the étale
neighbourhood of the base produced by the étale local structure theorem [Stacks, Tag 00UL] is
`Spec A''` for an étale `A`-algebra `A''`, and the decomposition of the fibre product over it is a
decomposition of the ring `B ⊗[A] A''`. -/
@[ega "I 3.3.13" "more general"]
noncomputable def pullbackBaseChangeSpecIso {X Y V : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    {A B A'' : Type u} [CommRing A] [CommRing B] [CommRing A''] [Algebra A B] [Algebra A A'']
    (eV : Spec (CommRingCat.of A) ≅ V) (eP : Spec (CommRingCat.of B) ≅ pullback f g)
    (n : Spec (CommRingCat.of A'') ⟶ V)
    (hP : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eV.hom =
      eP.hom ≫ pullback.snd f g)
    (hn : Spec.map (CommRingCat.ofHom (algebraMap A A'')) ≫ eV.hom = n) :
    Spec (CommRingCat.of (B ⊗[A] A'')) ≅ pullback f (n ≫ g) :=
  (pullbackSpecIso A B A'').symm.trans
    ((asIso (pullback.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))
          (Spec.map (CommRingCat.ofHom (algebraMap A A''))) (pullback.snd f g) n
          eP.hom (𝟙 _) eV.hom hP (by rw [hn, Category.id_comp]))).trans
      (pullbackLeftPullbackSndIso f g n))

/-- The identification `pullbackBaseChangeSpecIso` is compatible with the comparison morphism
`pullbackBaseChangeMap`: on rings the comparison morphism is `b ↦ b ⊗ 1`. -/
theorem pullbackBaseChangeSpecIso_hom_comp_pullbackBaseChangeMap {X Y V : Scheme.{u}} (f : X ⟶ Y)
    (g : V ⟶ Y) {A B A'' : Type u} [CommRing A] [CommRing B] [CommRing A''] [Algebra A B]
    [Algebra A A''] (eV : Spec (CommRingCat.of A) ≅ V) (eP : Spec (CommRingCat.of B) ≅ pullback f g)
    (n : Spec (CommRingCat.of A'') ⟶ V)
    (hP : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eV.hom =
      eP.hom ≫ pullback.snd f g)
    (hn : Spec.map (CommRingCat.ofHom (algebraMap A A'')) ≫ eV.hom = n) :
    (pullbackBaseChangeSpecIso f g eV eP n hP hn).hom ≫ pullbackBaseChangeMap f g n =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A''))) ≫ eP.hom := by
  rw [pullbackBaseChangeMap_eq]
  simp only [pullbackBaseChangeSpecIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, pullback.lift_fst, pullback.map]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]

/-- The identification `pullbackBaseChangeSpecIso` carries the projection to the new base to `Spec`
of the ring map `a ↦ 1 ⊗ a`. -/
theorem pullbackBaseChangeSpecIso_hom_comp_snd {X Y V : Scheme.{u}} (f : X ⟶ Y)
    (g : V ⟶ Y) {A B A'' : Type u} [CommRing A] [CommRing B] [CommRing A''] [Algebra A B]
    [Algebra A A''] (eV : Spec (CommRingCat.of A) ≅ V) (eP : Spec (CommRingCat.of B) ≅ pullback f g)
    (n : Spec (CommRingCat.of A'') ⟶ V)
    (hP : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eV.hom =
      eP.hom ≫ pullback.snd f g)
    (hn : Spec.map (CommRingCat.ofHom (algebraMap A A'')) ≫ eV.hom = n) :
    (pullbackBaseChangeSpecIso f g eV eP n hP hn).hom ≫ pullback.snd f (n ≫ g) =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := A'')))) := by
  simp only [pullbackBaseChangeSpecIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd, pullback.map, Category.comp_id]
  exact pullbackSpecIso_inv_snd A B A''

end FurtherBaseChange

end SpecTranslation

end Stacks.EtaleCohomology

end

