module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrivialize

/-!
# Assembling the finite case of property (B) from its ring-theoretic form

The finite case of property (B) for the étale topology, [Stacks, Tag 04DQ], is a statement about
schemes whose content is a statement about rings: over an affine étale neighbourhood of a point of
the base the fibre product of a finite morphism is affine, and the decomposition that property (B)
asks for is a product decomposition of its ring, each factor being an algebra over one member of
the given covering.

This file performs the translation. It isolates that ring-theoretic content as
`Stacks.EtaleCohomology.HasFiniteCaseDecomposition` and proves that *everything else* in the
finite case — the reduction to an affine base, the replacement of the covering by a finite affine
one, the identification of the further base change as the spectrum of a tensor product, the
reading of a product decomposition as a disjoint union of spectra, and the regrouping of the
pieces under the indices of the original covering — follows from it. The finite case
[Stacks, Tag 04DQ] and, through
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite`, the integral case
[Stacks, Tag 04DR] are therefore reduced to a single ring-theoretic statement.

## Main definitions

* `Stacks.EtaleCohomology.HasFiniteCaseDecomposition` is the ring-theoretic statement: for a
  module-finite `A → B` and a finite family of étale `B`-algebras `C k` jointly covering
  `Spec B`, and a prime `p` of `A`, there is an étale `A`-algebra `A₁` with a prime over `p` such
  that `B ⊗[A] A₁` is a finite product of rings, each of which is an algebra over one of the
  `C k` compatibly with `B`.

## Main results

* `Stacks.EtaleCohomology.exists_finite_etale_refinement_of_iso`: an étale covering of a scheme
  identified with `Spec B` admits a finite refinement by spectra of étale `B`-algebras, each
  piece mapping to a member of the covering.
* `Stacks.EtaleCohomology.hasLocalDecompositionAt_of_algEquivPi`: a product decomposition of
  `B ⊗[A] A₁` whose factors map to members of the covering *is* the local decomposition of
  `Stacks.EtaleCohomology.HasLocalDecompositionAt`.
* `Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition` and
  `Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_hasFiniteCaseDecomposition`: property
  (B) for a finite, respectively an integral, morphism, assuming
  `HasFiniteCaseDecomposition`.

## References

* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open TensorProduct

/-- `Spec` of an algebra map is étale exactly when the algebra is étale. -/
private theorem etale_spec_map_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔ Algebra.Etale R S :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).trans RingHom.etale_algebraMap

/-- **The local decomposition read off from a product decomposition of a ring.** Suppose the base
`V` is identified with `Spec A` and the fibre product `X ×ₗᵧ V` with `Spec B` in such a way that
the projection becomes `Spec` of the structure map `A → B`, let `A₁` be an étale `A`-algebra with
a prime `p₁` whose point of `Spec A₁` is carried to the given point `v`, and suppose
`B ⊗[A] A₁` decomposes as a finite product `∏ l, F l` of `B`-algebras, the `l`-th factor coming
with a morphism `Spec (F l) ⟶ U.X (idx l)` to a member of the covering which is compatible with
the structure map `B → F l`. Then the local decomposition `HasLocalDecompositionAt` holds at `v`.

This is the whole scheme-theoretic content of the finite case of property (B),
[Stacks, Tag 04DQ]: `Spec A₁` is the étale neighbourhood of `v`, the fibre product over it is
`Spec (B ⊗[A] A₁)` by `Stacks.EtaleCohomology.pullbackBaseChangeSpecIso`, the product
decomposition is the disjoint-union decomposition by
`Stacks.EtaleCohomology.sigmaSpecIsoOfAlgEquiv`, the comparison morphism is `b ↦ b ⊗ 1` by
`Stacks.EtaleCohomology.pullbackBaseChangeSpecIso_hom_comp_pullbackBaseChangeMap`, and the pieces
are regrouped under the indices of the covering by
`Stacks.EtaleCohomology.HasLocalDecompositionAt.of_refinement`. The `B`-linearity of the
decomposition is what makes the pieces subordinate to the covering: it identifies the structure
map of the `l`-th factor with the `l`-th component of the decomposition. -/
theorem hasLocalDecompositionAt_of_algEquivPi {X Y V : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y)
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V)
    {A B A₁ : Type u} [CommRing A] [CommRing B] [CommRing A₁]
    [Algebra A B] [Algebra A A₁] [Algebra.Etale A A₁]
    (eV : Spec (CommRingCat.of A) ≅ V) (eP : Spec (CommRingCat.of B) ≅ pullback f g)
    (hP : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eV.hom = eP.hom ≫ pullback.snd f g)
    (n : Spec (CommRingCat.of A₁) ⟶ V)
    (hn : Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ eV.hom = n)
    (p₁ : Ideal A₁) [p₁.IsPrime] (hv : n.base ⟨p₁, ‹p₁.IsPrime›⟩ = v)
    {L : Type u} [Finite L] (F : L → Type u) [∀ l, CommRing (F l)] [∀ l, Algebra B (F l)]
    (ε : (B ⊗[A] A₁) ≃ₐ[B] (∀ l, F l))
    (idx : L → U.I₀) (α : ∀ l, Spec (CommRingCat.of (F l)) ⟶ U.X (idx l))
    (hα : ∀ l, α l ≫ U.f (idx l) =
      Spec.map (CommRingCat.ofHom (algebraMap B (F l))) ≫ eP.hom) :
    HasLocalDecompositionAt f g U v := by
  have hEt : Etale n := by
    rw [← hn]
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) :=
      etale_spec_map_algebraMap_iff.2 inferInstance
    infer_instance
  have hcomp : ∀ l : L, (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := A₁))) ≫
      CommRingCat.ofHom ((Pi.evalRingHom (fun l => F l) l).comp ε.toRingEquiv.toRingHom) =
      CommRingCat.ofHom (algebraMap B (F l)) := by
    intro l
    ext b
    change (Pi.evalRingHom (fun l => F l) l) (ε (b ⊗ₜ[A] (1 : A₁))) = algebraMap B (F l) b
    have hb : (b ⊗ₜ[A] (1 : A₁)) = algebraMap B (B ⊗[A] A₁) b := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [hb, AlgEquiv.commutes]
    rfl
  have key : ∀ l, α l ≫ U.f (idx l) = Sigma.ι (fun l => Spec (CommRingCat.of (F l))) l ≫
      ((sigmaSpecIsoOfAlgEquiv (A := B) F ε).trans
        (pullbackBaseChangeSpecIso f g eV eP n hP hn)).hom ≫ pullbackBaseChangeMap f g n := by
    intro l
    rw [hα l, Iso.trans_hom, Category.assoc, ← Category.assoc (Sigma.ι _ l),
      sigmaSpecIsoOfAlgEquiv_ι, pullbackBaseChangeSpecIso_hom_comp_pullbackBaseChangeMap,
      ← Category.assoc, ← Spec.map_comp, hcomp l]
  exact HasLocalDecompositionAt.of_refinement f g U v
    { scheme := Spec (CommRingCat.of A₁)
      point := ⟨p₁, ‹p₁.IsPrime›⟩
      toBase := n
      map_point := hv }
    (pullbackBaseChangeMap f g n)
    (pullbackBaseChangeMap_fst f g n) (pullbackBaseChangeMap_snd f g n)
    (fun l => Spec (CommRingCat.of (F l))) idx
    ((sigmaSpecIsoOfAlgEquiv (A := B) F ε).trans
      (pullbackBaseChangeSpecIso f g eV eP n hP hn)) α key

/-- **A finite affine étale refinement of a covering of an affine scheme, in ring form.** Let
`P` be a scheme identified with `Spec B` by an isomorphism `eP`, and let `U` be an étale covering
of `P`. There are finitely many étale `B`-algebras `C k` whose spectra jointly cover `Spec B` and
each of which maps to a member `U.X (idx k)` of the covering compatibly with the structure map
`B → C k`.

This is `Stacks.EtaleCohomology.exists_finite_etale_refinement_hom` with the affine scheme
presented by an isomorphism rather than literally as a `Spec`, and with the pieces read as
`Type`-valued algebras rather than as objects of `CommRingCat`: that is the form in which the
finite case of property (B), [Stacks, Tag 04DQ], meets it, because the fibre product
`X ×ₗᵧ V₀` there is affine but not literally the spectrum of a ring. The subordination data is
retained, since the decomposition property (B) asks for must be subordinate to the covering one
started with. -/
theorem exists_finite_etale_refinement_of_iso {P : Scheme.{u}} {B : Type u} [CommRing B]
    (eP : Spec (CommRingCat.of B) ≅ P) (U : P.Cover.{u} Scheme.etalePrecoverage) :
    ∃ (K : Type u) (_ : Finite K) (C : K → Type u) (_ : ∀ k, CommRing (C k))
      (_ : ∀ k, Algebra B (C k)) (_ : ∀ k, Algebra.Etale B (C k))
      (idx : K → U.I₀) (ρ : ∀ k, Spec (CommRingCat.of (C k)) ⟶ U.X (idx k)),
      (∀ k, ρ k ≫ U.f (idx k) =
        Spec.map (CommRingCat.ofHom (algebraMap B (C k))) ≫ eP.hom) ∧
      ∀ q : PrimeSpectrum B, ∃ k, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (C k))) := by
  have : IsAffine P := IsAffine.of_isIso eP.inv
  obtain ⟨𝒲, hfin, r, hopen⟩ := exists_finite_affine_etale_refinement U
  let : ∀ k, Algebra B ↥(𝒲.X k) :=
    fun k => (Spec.preimage (𝒲.f k ≫ eP.inv)).hom.toAlgebra
  have hmap' : ∀ k, Spec.map (CommRingCat.ofHom (algebraMap B ↥(𝒲.X k))) =
      𝒲.f k ≫ eP.inv := by
    intro k
    change Spec.map (Spec.preimage (𝒲.f k ≫ eP.inv)) = 𝒲.f k ≫ eP.inv
    rw [Spec.map_preimage]
  have hmap : ∀ k, 𝒲.f k =
      Spec.map (CommRingCat.ofHom (algebraMap B ↥(𝒲.X k))) ≫ eP.hom := by
    intro k
    rw [hmap' k, Category.assoc, eP.inv_hom_id, Category.comp_id]
  refine ⟨𝒲.I₀, hfin, fun k => ↥(𝒲.X k), fun k => inferInstance, fun k => inferInstance,
    fun k => ?_, r.s₀, r.h₀, fun k => (r.w₀ k).trans (hmap k), fun q => ?_⟩
  · have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap B ↥(𝒲.X k)))) := by
      rw [hmap' k]
      have h₀ : Etale (𝒲.f k) := 𝒲.map_prop k
      infer_instance
    exact etale_spec_map_algebraMap_iff.1 hEt
  · obtain ⟨x, hx⟩ := 𝒲.covers (eP.hom.base q)
    refine ⟨𝒲.idx (eP.hom.base q), x, ?_⟩
    change (Spec.map (CommRingCat.ofHom
      (algebraMap B ↥(𝒲.X (𝒲.idx (eP.hom.base q)))))).base x = q
    rw [hmap' (𝒲.idx (eP.hom.base q))]
    change eP.inv.base ((𝒲.f (𝒲.idx (eP.hom.base q))).base x) = q
    rw [hx]
    exact Scheme.hom_inv_apply eP q

/-- **The ring-theoretic content of the finite case of property (B), [Stacks, Tag 04DQ].** Let
`A → B` be module-finite, let `C : K → Type u` be a finite family of étale `B`-algebras whose
spectra jointly cover `Spec B`, and let `p` be a prime of `A`. The statement asks for an étale
`A`-algebra `A₁` with a prime `p₁` over `p` such that the base change `B ⊗[A] A₁` is a *finite
product* of rings, each factor `F l` being an algebra over one member `C (κ l)` of the family
compatibly with `B`.

In the geometric reading `Spec B` is the fibre product of a finite morphism with an affine étale
base, the `C k` are a finite affine étale refinement of the given covering of it, `Spec A₁` is
the étale neighbourhood of the base that property (B) produces, and the factors `F l` are the
clopen pieces of the decomposition, the algebra structure over `C (κ l)` being the morphism from
the piece to the member of the covering that makes the decomposition subordinate to it.

`Stacks.EtaleCohomology.hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition` proves that this
statement implies property (B) for every finite morphism, hence — through
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite` — for every integral morphism.
It is the one step of [Stacks, Tag 04DQ] that is not proved in this library; the route to it is
the étale local structure theorem [Stacks, Tag 00UL] in the form
`Stacks.EtaleCohomology.exists_etale_completeOrthogonalIdempotents_tensorBaseChange`, whose
decomposition is trimmed by the shrinking lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseAlgebra` and whose factors are
identified with the factors of the covering side by
`Stacks.EtaleCohomology.exists_notMem_bijective_awayMap_algebraMap_of_etale_pair`. -/
def HasFiniteCaseDecomposition : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type u) [Finite K] (C : K → Type u) [∀ k, CommRing (C k)] [∀ k, Algebra B (C k)]
    [∀ k, Algebra.Etale B (C k)]
    (_ : ∀ q : PrimeSpectrum B, ∃ k, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (C k))))
    (p : Ideal A) [p.IsPrime],
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra A A₁) (_ : Algebra.Etale A A₁)
      (p₁ : Ideal A₁) (_ : p₁.IsPrime) (_ : p₁.LiesOver p)
      (L : Type u) (_ : Finite L) (κ : L → K) (F : L → Type u) (_ : ∀ l, CommRing (F l))
      (_ : ∀ l, Algebra B (F l)) (_ : ∀ l, Algebra (C (κ l)) (F l))
      (_ : ∀ l, IsScalarTower B (C (κ l)) (F l)),
      Nonempty ((B ⊗[A] A₁) ≃ₐ[B] (∀ l, F l))

/-- **The local decomposition for a finite morphism, from the ring-theoretic statement.** Assuming
`Stacks.EtaleCohomology.HasFiniteCaseDecomposition`, every finite morphism has the local
decomposition of `Stacks.EtaleCohomology.HasLocalDecompositionAt` at every point of every étale
base.

This is step (i) of [Stacks, Tag 04DQ] followed by the translation
`Stacks.EtaleCohomology.hasLocalDecompositionAt_of_algEquivPi`. No affineness is assumed: the
point is first replaced by an affine étale neighbourhood `V₀` of it using
`Stacks.EtaleCohomology.HasLocalDecompositionAt.of_etale`, over which the fibre product is affine
because it is finite over `V₀`, and the two affine schemes are then identified with the spectra of
their rings of global sections by `AlgebraicGeometry.Scheme.isoSpec`, the projection becoming
`Spec` of the structure map by `AlgebraicGeometry.Scheme.isoSpec_inv_naturality`. -/
theorem hasLocalDecompositionAt_of_hasFiniteCaseDecomposition
    (hring : HasFiniteCaseDecomposition.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {V : Scheme.{u}} (g : V ⟶ Y) [Etale g]
    (U : (pullback f g).Cover.{u} Scheme.etalePrecoverage) (v : V) :
    HasLocalDecompositionAt f g U v := by
  obtain ⟨N, hNaff, hPaff, hfin⟩ := exists_affine_etaleNeighborhood_finite f g v
  refine HasLocalDecompositionAt.of_etale f g N.toBase (pullbackBaseChangeMap f g N.toBase)
    (pullbackBaseChangeMap_fst f g N.toBase) (pullbackBaseChangeMap_snd f g N.toBase)
    U v N.point N.map_point ?_
  let := (pullback.snd f (N.toBase ≫ g)).appTop.hom.toAlgebra
  have hfinAB : Module.Finite ↥(Γ(N.scheme, ⊤)) ↥(Γ(pullback f (N.toBase ≫ g), ⊤)) := hfin
  obtain ⟨K, hKfin, C, hCring, hCalg, hCetale, idx, ρ, hρ, hcov⟩ :=
    exists_finite_etale_refinement_of_iso (pullback f (N.toBase ≫ g)).isoSpec.symm
      (U.pullback₁ (pullbackBaseChangeMap f g N.toBase))
  have hq : (N.scheme.isoSpec.hom.base N.point).asIdeal.IsPrime :=
    (N.scheme.isoSpec.hom.base N.point).isPrime
  obtain ⟨A₁, hA₁ring, hA₁alg, hA₁et, p₁, hp₁, hp₁over, L, hLfin, κ, F, hFring, hFalgB, hFalgC,
      hFtower, ⟨ε⟩⟩ :=
    hring ↥(Γ(N.scheme, ⊤)) ↥(Γ(pullback f (N.toBase ≫ g), ⊤)) K C hcov
      (N.scheme.isoSpec.hom.base N.point).asIdeal
  have hv : (Spec.map (CommRingCat.ofHom (algebraMap ↥(Γ(N.scheme, ⊤)) A₁)) ≫
      N.scheme.isoSpec.symm.hom).base ⟨p₁, hp₁⟩ = N.point := by
    have h1 : (PrimeSpectrum.comap (algebraMap ↥(Γ(N.scheme, ⊤)) A₁) ⟨p₁, hp₁⟩ :
        PrimeSpectrum ↥(Γ(N.scheme, ⊤))) = N.scheme.isoSpec.hom.base N.point :=
      PrimeSpectrum.ext (hp₁over.over).symm
    change N.scheme.isoSpec.symm.hom.base
      (PrimeSpectrum.comap (algebraMap ↥(Γ(N.scheme, ⊤)) A₁) ⟨p₁, hp₁⟩) = N.point
    rw [h1]
    exact Scheme.hom_inv_apply N.scheme.isoSpec N.point
  refine hasLocalDecompositionAt_of_algEquivPi f (N.toBase ≫ g) _ N.point
    N.scheme.isoSpec.symm (pullback f (N.toBase ≫ g)).isoSpec.symm
    (Scheme.isoSpec_inv_naturality (pullback.snd f (N.toBase ≫ g))) _ rfl p₁ hv F ε
    (fun l => idx (κ l))
    (fun l => Spec.map (CommRingCat.ofHom (algebraMap (C (κ l)) (F l))) ≫ ρ (κ l)) ?_
  intro l
  have hcomp : CommRingCat.ofHom
        (algebraMap ↥(Γ(pullback f (N.toBase ≫ g), ⊤)) (C (κ l))) ≫
      CommRingCat.ofHom (algebraMap (C (κ l)) (F l)) =
      CommRingCat.ofHom (algebraMap ↥(Γ(pullback f (N.toBase ≫ g), ⊤)) (F l)) := by
    ext x
    exact (IsScalarTower.algebraMap_apply ↥(Γ(pullback f (N.toBase ≫ g), ⊤)) (C (κ l)) (F l) x).symm
  rw [Category.assoc, hρ (κ l), ← Category.assoc, ← Spec.map_comp, hcomp]

/-- **Property (B) for a finite morphism, from the ring-theoretic statement.** This is
[Stacks, Tag 04DQ] modulo `Stacks.EtaleCohomology.HasFiniteCaseDecomposition`: property (B) for a
finite morphism follows from the ring-theoretic decomposition statement, by
`Stacks.EtaleCohomology.hasPropertyB_of_hasLocalDecompositionAt`. -/
theorem hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition
    (hring : HasFiniteCaseDecomposition.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    HasPropertyB f := by
  refine hasPropertyB_of_hasLocalDecompositionAt f ?_
  intro V g hg U v
  exact hasLocalDecompositionAt_of_hasFiniteCaseDecomposition hring f g U v

/-- **Property (B) for an integral morphism, from the ring-theoretic statement.** This is
[Stacks, Tag 04DR] modulo `Stacks.EtaleCohomology.HasFiniteCaseDecomposition`: the integral case
is the finite case plus the limit argument of
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom_of_finite`, whose only open argument is the
finite case. -/
theorem hasPropertyB_of_isIntegralHom_of_hasFiniteCaseDecomposition
    (hring : HasFiniteCaseDecomposition.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    HasPropertyB f :=
  hasPropertyB_of_isIntegralHom_of_finite
    (fun _ _ f' hf' =>
      @hasPropertyB_of_isFinite_of_hasFiniteCaseDecomposition hring _ _ f' hf') f

end Stacks.EtaleCohomology

end

