module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksCore.FieldTheory.KrullTopology
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale schemes over a field as continuous Galois sets

For a separable closure `L` of a field `K`, the schemes étale over `K` are equivalent to discrete
sets carrying a continuous action of `Gal(L/K)`. The equivalence sends an étale scheme to its set
of `K`-morphisms from `Spec L`; its inverse sends a continuous Galois set to the coproduct, over
the orbits, of the spectra of the fixed fields of the stabilisers.

## Main definitions

* `AlgebraicGeometry.ContinuousGSet`: Mathlib's category of continuous actions on discrete types.
* `AlgebraicGeometry.ContinuousGSet.ofMulAction`: a set with a continuous action of `G` for the
  discrete topology, as an object of that category.
* `AlgebraicGeometry.ContinuousGSet.homEquiv`: its morphisms are exactly the equivariant maps.
* `AlgebraicGeometry.separableClosureGeometricPoint`: `Spec L` as a scheme over `Spec K`.

## Main results

* `AlgebraicGeometry.etaleEquivalenceContinuousGSet` gives the equivalence and identifies its
  underlying sets, its functoriality, and its Galois action.

## References

* [Stacks Project, Tag 04JJ](https://stacks.math.columbia.edu/tag/04JJ)
* [Stacks Project, Tag 03QR](https://stacks.math.columbia.edu/tag/03QR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry

/-- A map from the spectrum of a field into a coproduct of schemes factors through one summand. -/
private theorem exists_factorization_spec_sigma_ι
    {I : Type u} [Small.{u} I] (Y : I → Scheme.{u})
    (E : Type u) [Field E] (f : Spec (.of E) ⟶ ∐ fun i ↦ Y i) :
    ∃ (i : I) (g : Spec (.of E) ⟶ Y i), f = g ≫ Sigma.ι Y i := by
  classical
  let q := AlgebraicGeometry.sigmaMk Y
  have hcont : Continuous (q.symm ∘ f.base) :=
    q.symm.continuous.comp (Scheme.Hom.continuous f)
  obtain ⟨i, g, _, hg⟩ := Continuous.exists_lift_sigma hcont
  have hrange : Set.range f.base ⊆ Set.range (Sigma.ι Y i).base := by
    rintro x ⟨z, rfl⟩
    refine ⟨g z, ?_⟩
    have hz := congrArg q (congrFun hg z)
    simpa [q, AlgebraicGeometry.sigmaMk_mk] using hz.symm
  exact ⟨i, _, (IsOpenImmersion.lift_fac (Sigma.ι Y i) f hrange).symm⟩

/-- The same factorization, through an isomorphism with a coproduct. -/
private theorem exists_factorization_spec_sigma
    {I : Type u} [Small.{u} I] (Y : I → Scheme.{u})
    (E : Type u) [Field E] {X : Scheme.{u}}
    (e : X ≅ ∐ fun i ↦ Y i) (f : Spec (.of E) ⟶ X) :
    ∃ (i : I) (g : Spec (.of E) ⟶ Y i),
      f = g ≫ Sigma.ι Y i ≫ e.inv := by
  obtain ⟨i, g, h⟩ := exists_factorization_spec_sigma_ι Y E (f ≫ e.hom)
  exact ⟨i, g, by rw [← Category.assoc, ← h]; simp⟩

/-- The summand and the factoring map of such a factorization are unique. -/
private theorem factorization_spec_sigma_unique
    {I : Type u} [Small.{u} I] (Y : I → Scheme.{u})
    (E : Type u) [Field E] (f : Spec (.of E) ⟶ ∐ fun i ↦ Y i)
    {i j : I} {g : Spec (.of E) ⟶ Y i} {h : Spec (.of E) ⟶ Y j}
    (hg : f = g ≫ Sigma.ι Y i) (hh : f = h ≫ Sigma.ι Y j) :
    ∃ e : i = j, g ≫ eqToHom (by rw [e]) = h := by
  classical
  obtain ⟨z⟩ : Nonempty (Spec (.of E)) := inferInstance
  have hcomp : g ≫ Sigma.ι Y i = h ≫ Sigma.ι Y j := hg.symm.trans hh
  have hpoint : (g ≫ Sigma.ι Y i).base z = (h ≫ Sigma.ι Y j).base z :=
    congrArg (fun k : Spec (.of E) ⟶ ∐ fun i ↦ Y i => k.base z) hcomp
  have hleft : (g ≫ Sigma.ι Y i).base z ∈ (Sigma.ι Y i).opensRange := by
    show ∃ y, (Sigma.ι Y i).base y = (g ≫ Sigma.ι Y i).base z
    exact ⟨g.base z, rfl⟩
  have hright : (h ≫ Sigma.ι Y j).base z ∈ (Sigma.ι Y j).opensRange := by
    show ∃ y, (Sigma.ι Y j).base y = (h ≫ Sigma.ι Y j).base z
    exact ⟨h.base z, rfl⟩
  have hij : i = j := by
    by_contra hne
    have hbot := (disjoint_opensRange_sigmaι Y i j hne).le_bot
    have hmem : (g ≫ Sigma.ι Y i).base z ∈
        (Sigma.ι Y i).opensRange ⊓ (Sigma.ι Y j).opensRange :=
      ⟨hleft, hpoint ▸ hright⟩
    simpa using hbot hmem
  refine ⟨hij, ?_⟩
  subst j
  exact (cancel_mono (Sigma.ι Y i)).mp (hg.symm.trans hh)

/-- A geometric point of a scheme étale over a field factors through one of the finite separable
field extensions presenting it. -/
private theorem geometricPoint_factors_through_finite_etale_piece
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale)
    (x : Spec (.of L) ⟶ X.left) :
    ∃ (I : Type u) (Ki : I → Type u) (_hKi : ∀ i, Field (Ki i))
      (_hA : ∀ i, Algebra K (Ki i)) (_hF : ∀ i, Module.Finite K (Ki i))
      (_hS : ∀ i, Algebra.IsSeparable K (Ki i))
      (e : X.left ≅ ∐ fun i ↦ Spec (.of (Ki i)))
      (_he : e.hom ≫ Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap K (Ki i)))) = X.hom)
      (i : I) (g : Spec (.of L) ⟶ Spec (.of (Ki i))),
      x = g ≫ Sigma.ι (fun i ↦ Spec (.of (Ki i))) i ≫ e.inv := by
  obtain ⟨I, Ki, hKi, hA, hF, hS, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K X.hom).mp
      X.prop
  obtain ⟨i, g, hg⟩ := exists_factorization_spec_sigma
    (fun i ↦ Spec (.of (Ki i))) L e x
  exact ⟨I, Ki, hKi, hA, hF, hS, e, he, i, g, hg⟩

/-- Maps from the spectrum of a field into a coproduct of schemes are the disjoint union of the
maps into the summands. -/
private noncomputable def specHomEquivSigma
    {I : Type u} [Small.{u} I] (Y : I → Scheme.{u})
    (E : Type u) [Field E] {X : Scheme.{u}}
    (e : X ≅ ∐ fun i ↦ Y i) :
    (Spec (.of E) ⟶ X) ≃ Σ i, (Spec (.of E) ⟶ Y i) where
  toFun f := by
    let P := exists_factorization_spec_sigma Y E e f
    exact ⟨Classical.choose P, Classical.choose (Classical.choose_spec P)⟩
  invFun p := p.2 ≫ Sigma.ι Y p.1 ≫ e.inv
  left_inv f := by
    dsimp
    exact (Classical.choose_spec (Classical.choose_spec
      (exists_factorization_spec_sigma Y E e f))).symm
  right_inv p := by
    rcases p with ⟨i, g⟩
    let f := g ≫ Sigma.ι Y i ≫ e.inv
    let P := exists_factorization_spec_sigma Y E e f
    let j := Classical.choose P
    let g' := Classical.choose (Classical.choose_spec P)
    have hg' : f = g' ≫ Sigma.ι Y j ≫ e.inv :=
      Classical.choose_spec (Classical.choose_spec P)
    have h₁ : f ≫ e.hom = g ≫ Sigma.ι Y i := by
      dsimp [f]
      simp
    have h₂ : f ≫ e.hom = g' ≫ Sigma.ι Y j := by
      have hh := congrArg (fun k : Spec (.of E) ⟶ X => k ≫ e.hom) hg'
      simpa using hh
    obtain ⟨hij, hcomp⟩ :=
      factorization_spec_sigma_unique Y E (f ≫ e.hom) h₁ h₂
    change (⟨j, g'⟩ : Σ k, (Spec (.of E) ⟶ Y k)) = ⟨i, g⟩
    refine Sigma.ext hij.symm ?_
    exact (heq_comp_eqToHom_iff g g' (by rw [hij])).mp (heq_of_eq hcomp.symm)

/-- The above identification is compatible with precomposition by a map of spectra of fields. -/
private theorem specHomEquivSigma_precomp
    {I : Type u} [Small.{u} I] (Y : I → Scheme.{u})
    (E : Type u) [Field E] {X : Scheme.{u}}
    (e : X ≅ ∐ fun i ↦ Y i) (E' : Type u) [Field E']
    (h : Spec (.of E') ⟶ Spec (.of E)) (f : Spec (.of E) ⟶ X) :
    specHomEquivSigma Y E' e (h ≫ f) =
      ⟨(specHomEquivSigma Y E e f).1,
        h ≫ (specHomEquivSigma Y E e f).2⟩ := by
  classical
  let φ := specHomEquivSigma Y E' e
  let ψ := specHomEquivSigma Y E e
  let p := ψ f
  have hp : ψ.symm p = f := ψ.left_inv f
  let q : Σ i, (Spec (.of E') ⟶ Y i) := ⟨p.1, h ≫ p.2⟩
  have hdom : h ≫ f = φ.symm q := by
    calc
    h ≫ f = h ≫ ψ.symm p := by rw [hp]
    _ = φ.symm q := by
      dsimp [φ, ψ, specHomEquivSigma]
      simp [q, p, Category.assoc]
  show φ (h ≫ f) = q
  calc
    φ (h ≫ f) = φ (φ.symm q) := congrArg φ hdom
    _ = q := φ.apply_symm_apply q

/-- For a finite extension `E` of `K`, the set of Galois elements carrying one embedding of `E` to
another is open in the Krull topology. -/
private theorem isOpen_galois_comp_eq
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Field E] [Algebra K E]
    [FiniteDimensional K E] (f g : E →ₐ[K] L) :
    IsOpen {σ : Gal(L/K) | σ.toAlgHom.comp f = g} := by
  classical
  let b := Module.finBasis K E
  have hEq : {σ : Gal(L/K) | σ.toAlgHom.comp f = g} =
      ⋂ i : Fin (Module.finrank K E), {σ : Gal(L/K) | σ (f (b i)) = g (b i)} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · exact fun h i => congrArg (fun φ : E →ₐ[K] L => φ (b i)) h
    · intro h
      have hb : (σ.toAlgHom.comp f).toLinearMap = g.toLinearMap :=
        b.ext (fun i => h i)
      exact AlgHom.ext fun x => DFunLike.congr_fun hb x
  rw [hEq]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_krullTopology_apply_eq K (f (b i)) (Algebra.IsAlgebraic.isAlgebraic _)

/-- A map of spectra of fields over the base gives a ring map compatible with the structure maps. -/
private theorem comp_spec_homEquiv_algebraMap
    (K L E : Type u) [Field K] [Field L] [Algebra K L] [Field E] [Algebra K E]
    (g : Spec (.of L) ⟶ Spec (.of E))
    (hbase : g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    CommRingCat.ofHom (algebraMap K E) ≫ Spec.homEquiv g =
      CommRingCat.ofHom (algebraMap K L) := by
  have hh := congrArg Spec.preimage hbase
  rw [Spec.homEquiv_apply]
  simpa only [Spec.preimage_comp, Spec.preimage_map] using hh

/-- The stabiliser of a geometric point of the spectrum of a finite extension is open. -/
private theorem isOpen_galois_stabilizer_specMap
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Field E] [Algebra K E]
    [FiniteDimensional K E] (g : Spec (.of L) ⟶ Spec (.of E))
    (hbase : g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    IsOpen {σ : Gal(L/K) |
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g} := by
  classical
  let α : E →ₐ[K] L := AlgHom.mk (Spec.homEquiv g).hom fun k =>
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of L => f k)
      (comp_spec_homEquiv_algebraMap K L E g hbase)
  have hset : {σ : Gal(L/K) |
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g} =
      {σ : Gal(L/K) | σ.toAlgHom.comp α = α} := by
    ext σ
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have hh := congrArg Spec.homEquiv h
      apply AlgHom.ext
      intro x
      have hx := congrArg (fun r : CommRingCat.of E ⟶ CommRingCat.of L => r x) hh
      simpa [Spec.homEquiv_apply, Spec.preimage_comp, Spec.preimage_map,
        CommRingCat.comp_apply, α] using hx
    · intro h
      apply Spec.homEquiv.injective
      apply CommRingCat.hom_ext
      simp only [Spec.homEquiv_apply, Spec.preimage_comp, Spec.preimage_map,
        CommRingCat.hom_comp]
      show (σ.toAlgHom.comp α).toRingHom = α.toRingHom
      exact congrArg AlgHom.toRingHom h
  rw [hset]
  exact isOpen_galois_comp_eq K L E α α

/-- A map of spectra of fields over the base, read as an algebra homomorphism. -/
private noncomputable def specMapOverFieldToAlgHom
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Field E] [Algebra K E] :
    {g : Spec (.of L) ⟶ Spec (.of E) //
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} → (E →ₐ[K] L) := fun g => by
  exact AlgHom.mk (Spec.homEquiv g.1).hom fun k =>
    congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of L => f k)
      (comp_spec_homEquiv_algebraMap K L E g.1 g.2)

/-- An algebra homomorphism, read as a map of spectra of fields over the base. -/
private noncomputable def specMapOverFieldOfAlgHom
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Field E] [Algebra K E] (f : E →ₐ[K] L) :
    {g : Spec (.of L) ⟶ Spec (.of E) //
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} := by
  let g := Spec.homEquiv.symm (CommRingCat.ofHom f.toRingHom)
  refine ⟨g, ?_⟩
  have hcomp : CommRingCat.ofHom (algebraMap K E) ≫
      CommRingCat.ofHom f.toRingHom = CommRingCat.ofHom (algebraMap K L) := by
    apply CommRingCat.hom_ext
    ext k
    exact f.commutes k
  apply Spec.homEquiv.injective
  rw [Spec.homEquiv_apply, Spec.preimage_comp, Spec.preimage_map]
  simpa [g] using hcomp

/-- Maps of spectra of fields over the base correspond to algebra homomorphisms. -/
private noncomputable def specMapOverFieldEquiv
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Field E] [Algebra K E] :
    {g : Spec (.of L) ⟶ Spec (.of E) //
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} ≃ (E →ₐ[K] L) where
  toFun := specMapOverFieldToAlgHom K L E
  invFun := specMapOverFieldOfAlgHom K L E
  left_inv g := by
    apply Subtype.ext
    apply Spec.homEquiv.injective
    simp [specMapOverFieldOfAlgHom, specMapOverFieldToAlgHom, Spec.homEquiv_apply]
  right_inv f := by
    apply AlgHom.ext
    intro x
    simp [specMapOverFieldOfAlgHom, specMapOverFieldToAlgHom, Spec.homEquiv_apply]

/-- A subtype of a sigma type cut out by a predicate on the fibres is the sigma type of the
subtypes. -/
private def sigmaSubtypeDepEquiv
    {I : Type u} (A : I → Type u) (p : ∀ i, A i → Prop) :
    {x : Σ i, A i // p x.1 x.2} ≃ Σ i, {a : A i // p i a} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := by rintro ⟨⟨i, a⟩, h⟩; rfl
  right_inv := by rintro ⟨i, ⟨a, h⟩⟩; rfl

/-- Maps from the geometric point into a coproduct of spectra of extensions, over the base,
correspond to a choice of summand together with an embedding of the corresponding field. -/
private noncomputable def overHomSigmaEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (I : Type u) [Small.{u} I] (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Over.mk (Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))) ≃
      Σ i, (E i →ₐ[K] L) := by
  classical
  let Y : I → Scheme := fun i ↦ Spec (.of (E i))
  let U : Scheme := ∐ fun i ↦ Y i
  let f : U ⟶ Spec (.of K) := Sigma.desc (fun i ↦
    Spec.map (CommRingCat.ofHom (algebraMap K (E i))))
  let φ := specHomEquivSigma Y L (Iso.refl U)
  let η : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Over.mk f) ≃ {g : Spec (.of L) ⟶ U // g ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} := {
    toFun g := ⟨g.left, g.w⟩
    invFun g := Over.homMk g.1 g.2
    left_inv g := by apply Over.OverMorphism.ext; rfl
    right_inv g := by apply Subtype.ext; rfl }
  let q : ∀ i, (Spec (.of L) ⟶ Y i) → Prop := fun i g =>
    g ≫ Spec.map (CommRingCat.ofHom (algebraMap K (E i))) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hprop (g : Spec (.of L) ⟶ U) :
      (g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) ↔
        q (φ g).1 (φ g).2 := by
    let p := φ g
    have hfac : g = p.2 ≫ Sigma.ι Y p.1 := by
      simpa [φ, p, specHomEquivSigma, Y, U] using (φ.left_inv g).symm
    constructor
    · intro h
      rw [hfac] at h
      simpa [q, f, Category.assoc, Sigma.ι_desc, Y, U] using h
    · intro h
      rw [hfac]
      simpa [q, f, Category.assoc, Sigma.ι_desc, Y, U] using h
  exact η.trans ((Equiv.subtypeEquiv φ hprop).trans
    ((sigmaSubtypeDepEquiv (fun i ↦ Spec (.of L) ⟶ Y i) q).trans
      (Equiv.sigmaCongrRight fun i ↦ specMapOverFieldEquiv K L (E i))))

/-- Precomposing the structure map of `Spec L` with the spectrum of a Galois element does not
change it. -/
private theorem spec_map_galois_comp_algebraMap
    (K L : Type u) [Field K] [Field L] [Algebra K L] (σ : Gal(L/K)) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext k
  exact σ.commutes k

/-- The identification with algebra homomorphisms turns the Galois action by precomposition on
spectra into postcomposition on embeddings. -/
private theorem specMapOverFieldEquiv_precomp
    (K L E : Type u) [Field K] [Field L] [Algebra K L]
    [Field E] [Algebra K E] (σ : Gal(L/K))
    (g : {f : Spec (.of L) ⟶ Spec (.of E) //
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))}) :
    specMapOverFieldEquiv K L E
        ⟨Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g.1, by
          rw [Category.assoc, g.2, spec_map_galois_comp_algebraMap]⟩ =
      σ.toAlgHom.comp (specMapOverFieldEquiv K L E g) := by
  apply AlgHom.ext
  intro x
  simp [specMapOverFieldEquiv, specMapOverFieldToAlgHom,
    Spec.homEquiv_apply, Spec.preimage_comp, Spec.preimage_map,
    CommRingCat.hom_comp]

/-- The same compatibility, for the identification with a disjoint union of embeddings. -/
private theorem overHomSigmaEquiv_precomp
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (I : Type u) [Small.{u} I] (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] (σ : Gal(L/K))
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      Over.mk (Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))) :
    overHomSigmaEquiv K L I E
      (Over.homMk (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g.left) (by
        rw [Category.assoc, g.w]
        exact spec_map_galois_comp_algebraMap K L σ)) =
      ⟨(overHomSigmaEquiv K L I E g).1,
        σ.toAlgHom.comp (overHomSigmaEquiv K L I E g).2⟩ := by
  classical
  simp only [overHomSigmaEquiv, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.subtypeEquiv, sigmaSubtypeDepEquiv, Equiv.sigmaCongrRight,
    specHomEquivSigma_precomp, Over.homMk_left]
  apply Sigma.ext
  · rfl
  · let Y : I → Scheme := fun i ↦ Spec (.of (E i))
    let U : Scheme := ∐ fun i ↦ Y i
    let φ := specHomEquivSigma Y L (Iso.refl U)
    let p := φ g.left
    have hfac : g.left = p.2 ≫ Sigma.ι Y p.1 := by
      simpa [p, φ, specHomEquivSigma, Y, U] using (φ.left_inv g.left).symm
    have hpbase : p.2 ≫ Spec.map (CommRingCat.ofHom (algebraMap K (E p.1))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      have h := g.w
      rw [hfac] at h
      simpa [Category.assoc, Sigma.ι_desc, Y, U] using h
    let q : {f : Spec (.of L) ⟶ Spec (.of (E p.1)) //
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (E p.1))) =
          Spec.map (CommRingCat.ofHom (algebraMap K L))} := ⟨p.2, hpbase⟩
    exact heq_of_eq (specMapOverFieldEquiv_precomp K L (E p.1) σ q)

/-- Continuous actions of `G` on sets in an independent universe, regarded
as actions on discrete topological spaces. -/
public abbrev ContinuousGSet (G : Type u) [Group G] [TopologicalSpace G] :=
  let _ : HasForget₂ (Type v) TopCat.{v} :=
    { forget₂ := TopCat.discrete
      forget_comp := rfl }
  DiscreteContAction (Type v) G

/-- The stabiliser of a point of a continuous Galois set is open. -/
@[sga "3 VIIB 2.5" "partial"]
private theorem continuousGSet_stabilizer_open
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (x : S.obj.obj.V) :
    IsOpen {σ : Gal(L/K) | ConcreteCategory.hom (S.obj.obj.ρ σ) x = x} := by
  let : IsGalois K L := inferInstance
  let : HasForget₂ (Type u) TopCat.{u} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  let : TopologicalSpace (S.obj.obj.V) := ⊥
  let : DiscreteTopology (S.obj.obj.V) := ⟨rfl⟩
  have hcont : Continuous (fun p : Gal(L/K) × S.obj.obj.V =>
      ((forget₂ (Type u) TopCat).map (S.obj.obj.ρ p.1)) p.2) :=
    (Action.isContinuous_def (V := Type u) (G := Gal(L/K)) S.obj.obj).mp S.obj.property
  let f : Gal(L/K) → S.obj.obj.V := fun σ => ConcreteCategory.hom (S.obj.obj.ρ σ) x
  have hf : Continuous f := by
    show Continuous (fun σ => ((forget₂ (Type u) TopCat).map (S.obj.obj.ρ σ)) x)
    exact hcont.comp (continuous_id.prodMk continuous_const)
  have hset : {σ : Gal(L/K) | ConcreteCategory.hom (S.obj.obj.ρ σ) x = x} =
      f ⁻¹' {x} := by ext σ; simp [f]
  rw [hset]
  exact (isOpen_discrete {x}).preimage hf

/-- The Galois action on the underlying set of a continuous Galois set. -/
@[instance_reducible]
private def continuousGSetMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) : MulAction (Gal(L/K)) S.obj.obj.V where
  smul σ x := ConcreteCategory.hom (S.obj.obj.ρ σ) x
  one_smul x := by
    change ConcreteCategory.hom (S.obj.obj.ρ 1) x = x
    simp
  mul_smul σ τ x := by
    change ConcreteCategory.hom (S.obj.obj.ρ (σ * τ)) x =
      ConcreteCategory.hom (S.obj.obj.ρ σ)
        (ConcreteCategory.hom (S.obj.obj.ρ τ) x)
    rw [map_mul]
    rfl

/-- The stabiliser of a point of a continuous Galois set is the fixing subgroup of a finite
separable intermediate field. -/
private theorem continuousGSet_stabilizer_fixedField_finite
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (x : S.obj.obj.V) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      Algebra.IsSeparable K E ∧
      {σ : Gal(L/K) | ConcreteCategory.hom (S.obj.obj.ρ σ) x = x} =
        (E.fixingSubgroup : Set (Gal(L/K))) := by
  classical
  let : IsGalois K L := inferInstance
  let : HasForget₂ (Type u) TopCat.{u} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  let : TopologicalSpace (S.obj.obj.V) := ⊥
  let : DiscreteTopology (S.obj.obj.V) := ⟨rfl⟩
  let : MulAction (Gal(L/K)) (S.obj.obj.V) := continuousGSetMulAction K L S
  let H := MulAction.stabilizer (Gal(L/K)) x
  have hopen : IsOpen (H : Set (Gal(L/K))) := continuousGSet_stabilizer_open K L S x
  have hclosed : IsClosed (H : Set (Gal(L/K))) :=
    OpenSubgroup.isClosed ⟨H, hopen⟩
  let Hc : ClosedSubgroup (Gal(L/K)) := ⟨H, hclosed⟩
  let E := IntermediateField.fixedField H
  have hfix : E.fixingSubgroup = H := by
    simpa [E, Hc] using InfiniteGalois.fixingSubgroup_fixedField Hc
  have hEopen : IsOpen (E.fixingSubgroup : Set (Gal(L/K))) := by rwa [hfix]
  have hdim : FiniteDimensional K E :=
    (InfiniteGalois.isOpen_iff_finite E).mp hEopen
  have hsep : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E L
  refine ⟨E, hdim, hsep, ?_⟩
  have hset : {σ : Gal(L/K) | ConcreteCategory.hom (S.obj.obj.ρ σ) x = x} =
      (H : Set (Gal(L/K))) := by
    ext σ
    simp [H, MulAction.mem_stabilizer_iff]
    rfl
  rw [hset, hfix]

/-- The set of orbits of the Galois action on a continuous Galois set. -/
private abbrev continuousGSetOrbitIndex
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) : Type u := by
  letI : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  exact MulAction.orbitRel.Quotient Gal(L/K) S.obj.obj.V

/-- The decomposition of a set with a group action into orbits is equivariant. -/
private theorem selfEquivSigmaOrbits_smul
    (G α : Type u) [Group G] [MulAction G α] (g : G) (x : α) :
    MulAction.selfEquivSigmaOrbits G α (g • x) =
      ⟨(MulAction.selfEquivSigmaOrbits G α x).1,
        g • (MulAction.selfEquivSigmaOrbits G α x).2⟩ := by
  classical
  let D := MulAction.selfEquivSigmaOrbits G α
  have hi : (D (g • x)).1 = (D x).1 := by
    show (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient G α) =
      Quotient.mk'' x
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hOrbit : MulAction.orbit G (Quotient.out (D (g • x)).1) =
      MulAction.orbit G (Quotient.out (D x).1) :=
    congrArg (fun i : MulAction.orbitRel.Quotient G α =>
      MulAction.orbit G (Quotient.out i)) hi
  have hmem : ∀ z : α,
      z ∈ MulAction.orbit G (Quotient.out (D (g • x)).1) ↔
        z ∈ MulAction.orbit G (Quotient.out (D x).1) := by
    intro z
    rw [hOrbit]
  refine Sigma.ext hi ?_
  exact (Subtype.heq_iff_coe_eq hmem).2 rfl

/-- The intermediate field attached to an orbit: the fixed field of the stabiliser of a chosen
representative. -/
private noncomputable def continuousGSetOrbitField
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (i : continuousGSetOrbitIndex K L S) :
    IntermediateField K L := by
  letI : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  exact Classical.choose (continuousGSet_stabilizer_fixedField_finite
    K L S (Quotient.out i))

/-- The field attached to an orbit is finite over the base. -/
private theorem continuousGSetOrbitField_finite
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (i : continuousGSetOrbitIndex K L S) :
    FiniteDimensional K (continuousGSetOrbitField K L S i) := by
  let : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  exact (Classical.choose_spec (continuousGSet_stabilizer_fixedField_finite
    K L S (Quotient.out i))).1

/-- The field attached to an orbit is separable over the base. -/
private theorem continuousGSetOrbitField_separable
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (i : continuousGSetOrbitIndex K L S) :
    Algebra.IsSeparable K (continuousGSetOrbitField K L S i) := by
  let : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  exact (Classical.choose_spec (continuousGSet_stabilizer_fixedField_finite
    K L S (Quotient.out i))).2.1

/-- The stabiliser of the chosen representative of an orbit is the fixing subgroup of the
attached field. -/
private theorem continuousGSetOrbitField_stabilizer
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (i : continuousGSetOrbitIndex K L S) :
    {σ : Gal(L/K) | ConcreteCategory.hom (S.obj.obj.ρ σ) (Quotient.out i) =
        Quotient.out i} =
      (continuousGSetOrbitField K L S i).fixingSubgroup :=
  (Classical.choose_spec (continuousGSet_stabilizer_fixedField_finite
    K L S (Quotient.out i))).2.2

/-- Every embedding of an intermediate field into a separable closure extends to an automorphism
of the closure. -/
private theorem algHom_extends_to_gal
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : IntermediateField K L) (f : E →ₐ[K] L) :
    ∃ σ : Gal(L/K), σ.toAlgHom.domRestrict E = f := by
  let : IsSepClosed L := IsSepClosure.sep_closed K
  have hsep : Algebra.IsSeparable E L := inferInstance
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable
    (K := K) (L := E) (E := L) (M := L) f
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective K L L), hφ⟩

/-- Any two embeddings of a finite separable extension into a separable closure differ by an
automorphism of the closure. -/
private theorem exists_gal_comp_eq_of_finite_separable
    (K L E : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    [Field E] [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    (f g : E →ₐ[K] L) :
    ∃ σ : Gal(L/K), σ.toAlgHom.comp f = g := by
  classical
  let A : IntermediateField K L := f.fieldRange
  let e : E ≃ₐ[K] A := f.equivFieldRange
  let h : A →ₐ[K] L := g.comp e.symm.toAlgHom
  obtain ⟨σ, hσ⟩ := algHom_extends_to_gal K L A h
  refine ⟨σ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun φ : A →ₐ[K] L =>
      φ ⟨f x, f.mem_fieldRange.mpr ⟨x, rfl⟩⟩) hσ
  show σ (f x) = g x
  have he : (⟨f x, f.mem_fieldRange.mpr ⟨x, rfl⟩⟩ : A) = e x := by
    apply Subtype.ext
    rfl
  rw [he] at hx
  simpa [AlgHom.domRestrict, h, e, A] using hx

/-- The image of an embedding is the fixed field of its fixing subgroup. -/
private theorem embeddedAlgHom_range_eq_fixedField_stabilizer
    (K L E : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    [Field E] [Algebra K E] (f : E →ₐ[K] L) :
    f.fieldRange = IntermediateField.fixedField f.fieldRange.fixingSubgroup := by
  let : IsGalois K L := inferInstance
  exact (InfiniteGalois.fixedField_fixingSubgroup f.fieldRange).symm

/-- An equivariant map between the embedding sets of two finite separable extensions is induced by
an embedding of the second extension into the first. -/
private theorem equivariantMap_embeddings_of_finite_separable
    (K L E F : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    [Field E] [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Field F] [Algebra K F] [Module.Finite K F] [Algebra.IsSeparable K F]
    (g : E →ₐ[K] L) (ψ : (E →ₐ[K] L) → (F →ₐ[K] L))
    (hψ : ∀ (σ : Gal(L/K)) (h : E →ₐ[K] L),
      ψ (σ.toAlgHom.comp h) = σ.toAlgHom.comp (ψ h)) :
    ∃ φ : F →ₐ[K] E, ∀ h, ψ h = h.comp φ := by
  classical
  let h₀ := ψ g
  have hstab : g.fieldRange.fixingSubgroup ≤ h₀.fieldRange.fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro z hz
    have hfix : σ.toAlgHom.comp g = g :=
      AlgHom.ext fun x => hσ (g x) (g.mem_fieldRange.mpr ⟨x, rfl⟩)
    have heq := hψ σ g
    rw [hfix] at heq
    have heq' : h₀ = σ.toAlgHom.comp h₀ := by
      simpa [h₀] using heq
    obtain ⟨x, rfl⟩ := h₀.mem_fieldRange.mp hz
    have hz' := congrArg (fun f : F →ₐ[K] L => f x) heq'
    change h₀ x = σ (h₀ x) at hz'
    exact hz'.symm
  have hrange : h₀.fieldRange ≤ g.fieldRange := by
    rw [embeddedAlgHom_range_eq_fixedField_stabilizer K L F h₀,
      embeddedAlgHom_range_eq_fixedField_stabilizer K L E g]
    exact IntermediateField.fixedField_le hstab
  let φ : F →ₐ[K] E := g.equivFieldRange.symm.toAlgHom.comp
    (h₀.codRestrict g.fieldRange.toSubalgebra fun x => hrange
      (h₀.mem_fieldRange.mpr ⟨x, rfl⟩))
  have hφ : g.comp φ = h₀ := by
    apply AlgHom.ext
    intro x
    have hm : h₀ x ∈ g.fieldRange :=
      hrange (h₀.mem_fieldRange.mpr ⟨x, rfl⟩)
    show g (g.equivFieldRange.symm
      ((h₀.codRestrict g.fieldRange.toSubalgebra fun x => hrange
        (h₀.mem_fieldRange.mpr ⟨x, rfl⟩)) x)) = h₀ x
    have hx : g.equivFieldRange.symm
        ((h₀.codRestrict g.fieldRange.toSubalgebra fun x => hrange
          (h₀.mem_fieldRange.mpr ⟨x, rfl⟩)) x) =
          g.equivFieldRange.symm ⟨h₀ x, hm⟩ := by rfl
    rw [hx]
    rw [← AlgHom.equivFieldRange_apply_coe]
    exact congrArg Subtype.val
      (g.equivFieldRange.apply_symm_apply (⟨h₀ x, hm⟩ : g.fieldRange))
  refine ⟨φ, fun h => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_gal_comp_eq_of_finite_separable K L E g h
  calc
    ψ h = ψ (σ.toAlgHom.comp g) := by rw [hσ]
    _ = σ.toAlgHom.comp (ψ g) := hψ σ g
    _ = σ.toAlgHom.comp (g.comp φ) := by rw [hφ]
    _ = h.comp φ := by rw [← hσ]; rfl

/-- A term is heterogeneously equal to its transport along an equality of indices. -/
private theorem heq_cast {ι : Type u} {A : ι → Sort v} {i j : ι}
    (h : i = j) (x : A i) : x ≍ h ▸ x := by
  cases h
  rfl

/-- An equivariant map between disjoint unions of embedding sets sends each summand into a single
summand, by an embedding of fields. -/
private theorem equivariantMap_sigma_embeddings_of_finite_separable
    (K L I J : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : I → Type u) (F : J → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    [∀ j, Field (F j)] [∀ j, Algebra K (F j)] [∀ j, Module.Finite K (F j)]
    [∀ j, Algebra.IsSeparable K (F j)]
    (α : (Σ i, E i →ₐ[K] L) → Σ j, F j →ₐ[K] L)
    (hα : ∀ (σ : Gal(L/K)) (p : Σ i, E i →ₐ[K] L),
      α ⟨p.1, σ.toAlgHom.comp p.2⟩ =
        ⟨(α p).1, σ.toAlgHom.comp (α p).2⟩) (i : I) :
    ∃ (j : J) (φ : F j →ₐ[K] E i),
      ∀ g, α ⟨i, g⟩ = ⟨j, g.comp φ⟩ := by
  classical
  let : IsSepClosed L := IsSepClosure.sep_closed K
  let g₀ : E i →ₐ[K] L := IsSepClosed.lift (K := K) (L := E i) (M := L)
  let j := (α ⟨i, g₀⟩).1
  have hindex (g : E i →ₐ[K] L) : (α ⟨i, g⟩).1 = j := by
    obtain ⟨σ, hσ⟩ := exists_gal_comp_eq_of_finite_separable K L (E i) g₀ g
    simpa [j, hσ] using congrArg Sigma.fst (hα σ ⟨i, g₀⟩)
  let ψ (g : E i →ₐ[K] L) : F j →ₐ[K] L :=
    (hindex g) ▸ (α ⟨i, g⟩).2
  have hpair (g : E i →ₐ[K] L) : α ⟨i, g⟩ = ⟨j, ψ g⟩ := by
    refine Sigma.ext (x := α ⟨i, g⟩) (y := ⟨j, ψ g⟩) (hindex g) ?_
    exact heq_cast (A := fun t : J => F t →ₐ[K] L) (hindex g)
      (α ⟨i, g⟩).2
  have hψ (σ : Gal(L/K)) (g : E i →ₐ[K] L) :
      ψ (σ.toAlgHom.comp g) = σ.toAlgHom.comp (ψ g) := by
    have h := hα σ ⟨i, g⟩
    rw [hpair (σ.toAlgHom.comp g), hpair g] at h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨φ, hφ⟩ := equivariantMap_embeddings_of_finite_separable
    K L (E i) (F j) g₀ ψ hψ
  exact ⟨j, φ, fun g => (hpair g).trans (by rw [hφ g])⟩

/-- An orbit whose stabiliser is the fixing subgroup of `E` is the set of embeddings of `E`. -/
private noncomputable def orbitEquivAlgHom
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {α : Type u} [MulAction (Gal(L/K)) α] (x : α)
    (E : IntermediateField K L)
    (hstab : MulAction.stabilizer (Gal(L/K)) x = E.fixingSubgroup) :
    MulAction.orbit (Gal(L/K)) x ≃ (E →ₐ[K] L) := by
  classical
  let rep : MulAction.orbit (Gal(L/K)) x → Gal(L/K) := fun y =>
    Classical.choose (MulAction.mem_orbit_iff.mp y.property)
  have hrep (y : MulAction.orbit (Gal(L/K)) x) : rep y • x = y.1 :=
    Classical.choose_spec (MulAction.mem_orbit_iff.mp y.property)
  let f : MulAction.orbit (Gal(L/K)) x → (E →ₐ[K] L) := fun y =>
    (rep y).toAlgHom.domRestrict E
  have hrestrict_of_act_eq (σ τ : Gal(L/K)) (hact : σ • x = τ • x) :
      σ.toAlgHom.domRestrict E = τ.toAlgHom.domRestrict E := by
    have hst : (σ⁻¹ * τ) • x = x := by
      calc
        (σ⁻¹ * τ) • x = σ⁻¹ • (τ • x) := by rw [smul_smul]
        _ = σ⁻¹ • (σ • x) := by rw [hact]
        _ = x := inv_smul_smul σ x
    have hfix : σ⁻¹ * τ ∈ E.fixingSubgroup := by
      rwa [← hstab, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hfix
    apply AlgHom.ext
    intro z
    have hz := hfix (z : L) z.2
    have hz' := congrArg (fun w : L => σ w) hz
    change σ ((σ⁻¹ * τ) z) = σ z at hz'
    change σ (z : L) = τ (z : L)
    simpa [AlgEquiv.mul_apply] using hz'.symm
  have hact_of_restrict_eq (σ τ : Gal(L/K))
      (hres : σ.toAlgHom.domRestrict E = τ.toAlgHom.domRestrict E) :
      σ • x = τ • x := by
    have hfix : σ⁻¹ * τ ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hval := congrArg (fun φ : E →ₐ[K] L => φ ⟨z, hz⟩) hres
      have hστ : σ z = τ z := hval
      change σ.symm (τ (z : L)) = z
      rw [← hστ]
      exact σ.symm_apply_apply (z : L)
    have hst : (σ⁻¹ * τ) • x = x := by
      rwa [← MulAction.mem_stabilizer_iff, hstab]
    calc
      σ • x = σ • ((σ⁻¹ * τ) • x) := by rw [hst]
      _ = (σ * (σ⁻¹ * τ)) • x := by rw [smul_smul]
      _ = τ • x := by simp
  have hbij : Function.Bijective f := by
    constructor
    · intro y y' h
      apply Subtype.ext
      have hact := hact_of_restrict_eq (rep y) (rep y') h
      exact (hrep y).symm.trans (hact.trans (hrep y'))
    · intro g
      obtain ⟨σ, hσ⟩ := algHom_extends_to_gal K L E g
      let y : MulAction.orbit (Gal(L/K)) x := ⟨σ • x, ⟨σ, rfl⟩⟩
      exact ⟨y, (hrestrict_of_act_eq (rep y) σ (hrep y)).trans hσ⟩
  exact Equiv.ofBijective f hbij

/-- That identification is equivariant. -/
private theorem orbitEquivAlgHom_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {α : Type u} [MulAction (Gal(L/K)) α] (x : α)
    (E : IntermediateField K L)
    (hstab : MulAction.stabilizer (Gal(L/K)) x = E.fixingSubgroup)
    (σ : Gal(L/K)) (y : MulAction.orbit (Gal(L/K)) x) :
    orbitEquivAlgHom K L x E hstab (σ • y) =
      σ.toAlgHom.comp (orbitEquivAlgHom K L x E hstab y) := by
  classical
  let rep : MulAction.orbit (Gal(L/K)) x → Gal(L/K) := fun z =>
    Classical.choose (MulAction.mem_orbit_iff.mp z.property)
  have hrep (z : MulAction.orbit (Gal(L/K)) x) : rep z • x = z.1 :=
    Classical.choose_spec (MulAction.mem_orbit_iff.mp z.property)
  have hact : rep (σ • y) • x = (σ * rep y) • x := by
    calc
      rep (σ • y) • x = (σ • y).1 := hrep (σ • y)
      _ = σ • y.1 := rfl
      _ = σ • (rep y • x) := by rw [hrep y]
      _ = (σ * rep y) • x := smul_smul _ _ _
  have hres : (rep (σ • y)).toAlgHom.domRestrict E =
      (σ * rep y).toAlgHom.domRestrict E := by
    apply AlgHom.ext
    intro z
    have hst : (rep (σ • y))⁻¹ * (σ * rep y) ∈ E.fixingSubgroup := by
      rw [← hstab, MulAction.mem_stabilizer_iff]
      have := congrArg (fun a : α => (rep (σ • y))⁻¹ • a) hact
      simpa [smul_smul] using this.symm
    rw [IntermediateField.mem_fixingSubgroup_iff] at hst
    have hz := hst (z : L) z.2
    have hz' := congrArg (rep (σ • y)) hz
    change rep (σ • y) (((rep (σ • y))⁻¹ * (σ * rep y)) (z : L)) =
      rep (σ • y) (z : L) at hz'
    show rep (σ • y) (z : L) = σ ((rep y) (z : L))
    simpa [AlgEquiv.mul_apply] using hz'.symm
  show (rep (σ • y)).toAlgHom.domRestrict E =
    σ.toAlgHom.comp ((rep y).toAlgHom.domRestrict E)
  rw [hres]
  apply AlgHom.ext
  intro z
  rfl

/-- The geometric point `Spec L ⟶ Spec K` associated to a field extension
`L/K`. -/
public noncomputable abbrev separableClosureGeometricPoint
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The set of geometric points of an étale scheme over the base, that is, of maps from the
spectrum of the separable closure over the base. -/
private abbrev geometricPointMorphisms (K L : Type u) [Field K] [Field L]
    [Algebra K L] (X : (Spec (.of K)).Etale) :=
  separableClosureGeometricPoint K L ⟶ (Scheme.Etale.forget (Spec (.of K))).obj X

/-- For an étale scheme presented as a coproduct of spectra of finite separable extensions, its
geometric points are the disjoint union of the embedding sets. -/
private noncomputable def geometricPointSigmaEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) (I : Type u) (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : X.left ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = X.hom) :
    geometricPointMorphisms K L X ≃ Σ i, (E i →ₐ[K] L) := by
  let f : (∐ fun i ↦ Spec (.of (E i))) ⟶ Spec (.of K) := Sigma.desc fun i ↦
    Spec.map (CommRingCat.ofHom (algebraMap K (E i)))
  let eOver : (Scheme.Etale.forget (Spec (.of K))).obj X ≅ Over.mk f :=
    Over.isoMk e (by simpa [f] using he)
  let η := overHomSigmaEquiv K L I E
  exact {
    toFun := fun x ↦ η (x ≫ eOver.hom)
    invFun := fun p ↦ η.symm p ≫ eOver.inv
    left_inv := by intro x; simp [η, eOver]
    right_inv := by intro p; simp [η, eOver] }

@[instance_reducible]
private noncomputable def geometricPointMorphismsMulAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) : MulAction (Gal(L/K)) (geometricPointMorphisms K L X) where
  smul σ x := Over.homMk
    (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ x.left)
    (by
      rw [Category.assoc, x.w]
      exact spec_map_galois_comp_algebraMap K L σ)
  one_smul x := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (1 : Gal(L/K)).toAlgHom.toRingHom) ≫ x.left = x.left
    have h : (1 : Gal(L/K)).toAlgHom.toRingHom = RingHom.id L := by ext z; simp
    rw [h]
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 (Spec (.of L)) by simp]
    exact Category.id_comp _
  mul_smul σ τ x := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (σ * τ).toAlgHom.toRingHom) ≫ x.left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ x.left
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1

attribute [local instance] geometricPointMorphismsMulAction

/-- The geometric points of an étale scheme, as an action of the Galois group on a set. -/
private noncomputable def geometricPointAction
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) : Action (Type u) (Gal(L/K)) :=
  Action.ofMulAction (Gal(L/K)) (geometricPointMorphisms K L X)

/-- The Galois action on geometric points is continuous for the discrete topology. -/
private theorem geometricPointAction_continuous
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : (Spec (.of K)).Etale) :
    letI : TopologicalSpace (geometricPointMorphisms K L X) := ⊥
    ContinuousSMul (Gal(L/K)) (geometricPointMorphisms K L X) := by
  let : TopologicalSpace (geometricPointMorphisms K L X) := ⊥
  let : DiscreteTopology (geometricPointMorphisms K L X) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨I, Ki, hKi, hA, hF, hS, e, he, i, g, hx⟩ :=
    geometricPoint_factors_through_finite_etale_piece K L X x.left
  let : Field (Ki i) := hKi i
  let : Algebra K (Ki i) := hA i
  let : Module.Finite K (Ki i) := hF i
  let he' : e.inv ≫ X.hom =
      Sigma.desc (fun j ↦ Spec.map (CommRingCat.ofHom (algebraMap K (Ki j)))) := by
    have h := congrArg (fun f => e.inv ≫ f) he
    simpa [Category.assoc] using h.symm
  have hbase : g ≫ Spec.map (CommRingCat.ofHom (algebraMap K (Ki i))) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    have h := x.w
    rw [hx] at h
    have h' : g ≫ Sigma.ι (fun j ↦ Spec (.of (Ki j))) i ≫
        Sigma.desc (fun j ↦ Spec.map (CommRingCat.ofHom (algebraMap K (Ki j)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [← he']
      simpa [Category.assoc] using h
    simpa using h'
  have hstab : (MulAction.stabilizer (Gal(L/K)) x : Set (Gal(L/K))) =
      {σ : Gal(L/K) |
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g} := by
    ext σ
    show (σ • x = x) ↔ _
    rw [Over.OverMorphism.ext_iff]
    show (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ x.left = x.left) ↔ _
    rw [hx]
    constructor
    · intro h
      have h' : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g ≫
          Sigma.ι (fun j ↦ Spec (.of (Ki j))) i =
          g ≫ Sigma.ι (fun j ↦ Spec (.of (Ki j))) i :=
        (cancel_mono e.inv).mp (by simpa [Category.assoc] using h)
      exact (cancel_mono (Sigma.ι (fun j ↦ Spec (.of (Ki j))) i)).mp h'
    · intro h
      have h' := congrArg (fun f : Spec (.of L) ⟶ Spec (.of (Ki i)) =>
        f ≫ Sigma.ι (fun j ↦ Spec (.of (Ki j))) i ≫ e.inv) h
      simpa [hx, Category.assoc] using h'
  rw [hstab]
  exact isOpen_galois_stabilizer_specMap K L (Ki i) g hbase

/-- The geometric points of an étale scheme, as a continuous Galois set. -/
private noncomputable def geometricPointContinuousGSet
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : (Spec (.of K)).Etale) : ContinuousGSet.{u, u} Gal(L/K) := by
  letI : HasForget₂ (Type u) TopCat.{u} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  letI : TopologicalSpace (geometricPointMorphisms K L X) := ⊥
  letI : DiscreteTopology (geometricPointMorphisms K L X) := ⟨rfl⟩
  exact ⟨⟨geometricPointAction K L X, geometricPointAction_continuous K L X⟩, ⟨rfl⟩⟩

/-- The functor sending an étale scheme over the base to its continuous Galois set of geometric
points. -/
private noncomputable def geometricPointFunctor
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    (Spec (.of K)).Etale ⥤ ContinuousGSet.{u, u} Gal(L/K) where
  obj X := geometricPointContinuousGSet K L X
  map {X Y} f := by
    let f' := (Scheme.Etale.forget (Spec (.of K))).map f
    letI : MulAction (Gal(L/K)) (geometricPointAction K L X).V := by
      change MulAction (Gal(L/K)) (geometricPointMorphisms K L X)
      exact geometricPointMorphismsMulAction K L X
    letI : MulAction (Gal(L/K)) (geometricPointAction K L Y).V := by
      change MulAction (Gal(L/K)) (geometricPointMorphisms K L Y)
      exact geometricPointMorphismsMulAction K L Y
    let h : geometricPointAction K L X ⟶ geometricPointAction K L Y := {
      hom := ↾fun x : geometricPointMorphisms K L X =>
        (Over.homMk (x.left ≫ f'.left) (by
          rw [Category.assoc, f'.w, x.w]) : geometricPointMorphisms K L Y)
      comm := by
        intro σ
        ext x
        apply Over.OverMorphism.ext
        change (σ • x).left ≫ f'.left =
          (σ • (Over.homMk (x.left ≫ f'.left) (by
            rw [Category.assoc, f'.w, x.w]))).left
        change (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ x.left) ≫ f'.left =
          Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ (x.left ≫ f'.left)
        exact Category.assoc _ _ _ }
    exact ObjectProperty.homMk (ObjectProperty.homMk h)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext x
    apply Over.OverMorphism.ext
    change x.left ≫
      ((Scheme.Etale.forget (Spec (.of K))).map (𝟙 X)).left = x.left
    have hm : ((Scheme.Etale.forget (Spec (.of K))).map (𝟙 X)).left = 𝟙 X.left :=
      congrArg Over.Hom.left
        (CategoryTheory.Functor.map_id (Scheme.Etale.forget (Spec (.of K))) X)
    rw [hm]
    exact Category.comp_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext x
    apply Over.OverMorphism.ext
    change x.left ≫
        ((Scheme.Etale.forget (Spec (.of K))).map (f ≫ g)).left =
      (x.left ≫ ((Scheme.Etale.forget (Spec (.of K))).map f).left) ≫
        ((Scheme.Etale.forget (Spec (.of K))).map g).left
    rw [Functor.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The étale scheme attached to a continuous Galois set: the coproduct over its orbits of the
spectra of the fields attached to them. -/
private noncomputable def continuousGSetOrbitEtaleObject
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) : (Spec (.of K)).Etale := by
  classical
  letI : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  let I : Type u := continuousGSetOrbitIndex K L S
  let E : I → IntermediateField K L := continuousGSetOrbitField K L S
  have hdim (i : I) : FiniteDimensional K (E i) := continuousGSetOrbitField_finite K L S i
  have hsep (i : I) : Algebra.IsSeparable K (E i) :=
    continuousGSetOrbitField_separable K L S i
  let F : I → Type u := fun i ↦ (E i : Type u)
  letI (i : I) : Field (F i) := inferInstance
  letI (i : I) : Algebra K (F i) := inferInstance
  letI (i : I) : Module.Finite K (F i) := hdim i
  letI (i : I) : Algebra.IsSeparable K (F i) := hsep i
  let U : Scheme := ∐ fun i : I ↦ Spec (.of (F i))
  let f : U ⟶ Spec (.of K) :=
    Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap K (F i))))
  have hf : Etale f := by
    apply (etale_iff_iso_coproduct_spectra_finite_separable
      K f).2
    refine ⟨I, F, (fun i ↦ inferInstance), (fun i ↦ inferInstance), hdim, hsep,
      Iso.refl U, ?_⟩
    simp [f]
  exact Scheme.Etale.mk f

/-- The underlying set of a continuous Galois set is the set of geometric points of the étale
scheme attached to it. -/
private noncomputable def continuousGSetOrbitPointsEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) :
    S.obj.obj.V ≃ geometricPointMorphisms K L
      (continuousGSetOrbitEtaleObject K L S) := by
  classical
  letI : HasForget₂ (Type u) TopCat :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  letI : TopologicalSpace (S.obj.obj.V) := ⊥
  letI : DiscreteTopology (S.obj.obj.V) := ⟨rfl⟩
  letI : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  let I : Type u := continuousGSetOrbitIndex K L S
  let E : I → IntermediateField K L := continuousGSetOrbitField K L S
  let F : I → Type u := fun i ↦ (E i : Type u)
  letI (i : I) : Field (F i) := inferInstance
  letI (i : I) : Algebra K (F i) := inferInstance
  letI (i : I) : Module.Finite K (F i) := continuousGSetOrbitField_finite K L S i
  letI (i : I) : Algebra.IsSeparable K (F i) := continuousGSetOrbitField_separable K L S i
  let Ψ := overHomSigmaEquiv K L I F
  let θ : S.obj.obj.V ≃ Σ i : I, (F i →ₐ[K] L) :=
    (MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V).trans
      (Equiv.sigmaCongrRight fun i =>
        orbitEquivAlgHom K L (Quotient.out i) (E i) (by
          apply SetLike.ext
          intro σ
          change σ ∈ {τ : Gal(L/K) |
            ConcreteCategory.hom (S.obj.obj.ρ τ) (Quotient.out i) = Quotient.out i} ↔
              σ ∈ (E i).fixingSubgroup
          rw [continuousGSetOrbitField_stabilizer K L S i]
          rfl))
  exact θ.trans Ψ.symm

/-- That identification is equivariant. -/
private theorem continuousGSetOrbitPointsEquiv_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (S : ContinuousGSet.{u, u} Gal(L/K)) (σ : Gal(L/K)) (x : S.obj.obj.V) :
    continuousGSetOrbitPointsEquiv K L S (ConcreteCategory.hom (S.obj.obj.ρ σ) x) =
      σ • continuousGSetOrbitPointsEquiv K L S x := by
  classical
  let : HasForget₂ (Type u) TopCat :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  let : TopologicalSpace (S.obj.obj.V) := ⊥
  let : DiscreteTopology (S.obj.obj.V) := ⟨rfl⟩
  let : MulAction (Gal(L/K)) S.obj.obj.V := continuousGSetMulAction K L S
  let I : Type u := continuousGSetOrbitIndex K L S
  let E : I → IntermediateField K L := continuousGSetOrbitField K L S
  let F : I → Type u := fun i ↦ (E i : Type u)
  let (i : I) : Field (F i) := inferInstance
  let (i : I) : Algebra K (F i) := inferInstance
  let (i : I) : Module.Finite K (F i) := continuousGSetOrbitField_finite K L S i
  let (i : I) : Algebra.IsSeparable K (F i) := continuousGSetOrbitField_separable K L S i
  let Ψ := overHomSigmaEquiv K L I F
  let hstab (i : I) : MulAction.stabilizer (Gal(L/K)) (Quotient.out i) =
      (E i).fixingSubgroup := by
    apply SetLike.ext
    intro τ
    show τ ∈ {γ : Gal(L/K) |
      ConcreteCategory.hom (S.obj.obj.ρ γ) (Quotient.out i) = Quotient.out i} ↔
        τ ∈ (E i).fixingSubgroup
    rw [continuousGSetOrbitField_stabilizer K L S i]
    rfl
  let η := Equiv.sigmaCongrRight (fun i =>
    orbitEquivAlgHom K L (Quotient.out i) (E i) (hstab i))
  let θ : S.obj.obj.V ≃ Σ i : I, (F i →ₐ[K] L) :=
    (MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V).trans η
  have hθ : θ (ConcreteCategory.hom (S.obj.obj.ρ σ) x) =
      ⟨(θ x).1, σ.toAlgHom.comp (θ x).2⟩ := by
    have hsm : ConcreteCategory.hom (S.obj.obj.ρ σ) x = σ • x := rfl
    show η (MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V
        (ConcreteCategory.hom (S.obj.obj.ρ σ) x)) =
      ⟨(η (MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V x)).1,
        σ.toAlgHom.comp (η (MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V x)).2⟩
    rw [hsm, selfEquivSigmaOrbits_smul]
    dsimp [η]
    let D := MulAction.selfEquivSigmaOrbits (Gal(L/K)) S.obj.obj.V
    have h := orbitEquivAlgHom_smul K L (Quotient.out (D x).1) (E (D x).1)
      (hstab (D x).1) σ (D x).2
    show (⟨(D x).1,
        orbitEquivAlgHom K L (Quotient.out (D x).1) (E (D x).1) (hstab (D x).1)
          (σ • (D x).2)⟩ : Σ i : I, (F i →ₐ[K] L)) =
      (⟨(D x).1, σ.toAlgHom.comp
        (orbitEquivAlgHom K L (Quotient.out (D x).1) (E (D x).1)
          (hstab (D x).1) (D x).2)⟩ : Σ i : I, (F i →ₐ[K] L))
    exact congrArg (fun f : F (D x).1 →ₐ[K] L =>
      (⟨(D x).1, f⟩ : Σ i : I, (F i →ₐ[K] L))) h
  let basePoint : Over (Spec (.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let coproductEtale : Over (Spec (.of K)) :=
    Over.mk (Sigma.desc fun i : I =>
      Spec.map (CommRingCat.ofHom (algebraMap K (F i))))
  let act (g : basePoint ⟶ coproductEtale) : basePoint ⟶ coproductEtale :=
    Over.homMk (U := basePoint) (V := coproductEtale)
      (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g.left) (by
      show (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g.left) ≫
          coproductEtale.hom = basePoint.hom
      rw [Category.assoc, g.w]
      exact spec_map_galois_comp_algebraMap K L σ)
  have hΨ (q : Σ i : I, (F i →ₐ[K] L)) :
      Ψ (act (Ψ.symm q)) = ⟨q.1, σ.toAlgHom.comp q.2⟩ := by
    have h := overHomSigmaEquiv_precomp K L I F σ (Ψ.symm q)
    have hq : Ψ (Ψ.symm q) = q := Equiv.apply_symm_apply Ψ q
    rw [hq] at h
    exact h
  have hinv (q : Σ i : I, (F i →ₐ[K] L)) :
      Ψ.symm ⟨q.1, σ.toAlgHom.comp q.2⟩ = act (Ψ.symm q) :=
    Ψ.symm_apply_eq.mpr (hΨ q).symm
  show Ψ.symm (θ (ConcreteCategory.hom (S.obj.obj.ρ σ) x)) = _
  apply Over.OverMorphism.ext
  rw [hθ]
  exact (congrArg Over.Hom.left (hinv (θ x))).trans (by rfl)

/-- The underlying scheme morphism of a geometric point reconstructed from an embedding. -/
private theorem geometricPointSigmaEquiv_symm_left
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) (I : Type u) (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : X.left ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = X.hom)
    (p : Σ i, E i →ₐ[K] L) :
    ((geometricPointSigmaEquiv K L X I E e he).symm p).left =
      Spec.map (CommRingCat.ofHom p.2.toRingHom) ≫
        Sigma.ι (fun i ↦ Spec (.of (E i))) p.1 ≫ e.inv := by
  rfl

/-- Reconstructing a geometric point from an embedding is equivariant. -/
private theorem geometricPointSigmaEquiv_symm_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) (I : Type u) (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : X.left ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = X.hom)
    (σ : Gal(L/K)) (p : Σ i, E i →ₐ[K] L) :
    (geometricPointSigmaEquiv K L X I E e he).symm
      ⟨p.1, σ.toAlgHom.comp p.2⟩ =
      σ • (geometricPointSigmaEquiv K L X I E e he).symm p := by
  apply Over.OverMorphism.ext
  show _ = Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ _
  rw [geometricPointSigmaEquiv_symm_left, geometricPointSigmaEquiv_symm_left]
  show Spec.map (CommRingCat.ofHom (σ.toAlgHom.toRingHom.comp p.2.toRingHom)) ≫ _ = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]
  rfl

/-- The identification of geometric points with embeddings is equivariant. -/
private theorem geometricPointSigmaEquiv_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (X : (Spec (.of K)).Etale) (I : Type u) (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : X.left ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = X.hom)
    (σ : Gal(L/K)) (x : geometricPointMorphisms K L X) :
    geometricPointSigmaEquiv K L X I E e he (σ • x) =
      ⟨(geometricPointSigmaEquiv K L X I E e he x).1,
        σ.toAlgHom.comp (geometricPointSigmaEquiv K L X I E e he x).2⟩ := by
  apply (geometricPointSigmaEquiv K L X I E e he).symm.injective
  rw [Equiv.symm_apply_apply, geometricPointSigmaEquiv_symm_smul,
    Equiv.symm_apply_apply]

/-- The maps induced by the geometric-points functor are equivariant. -/
private theorem geometricPointFunctor_map_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {X Y : (Spec (.of K)).Etale}
    (f : (geometricPointFunctor K L).obj X ⟶ (geometricPointFunctor K L).obj Y)
    (σ : Gal(L/K)) (x : geometricPointMorphisms K L X) :
    f.hom (σ • x) = (geometricPointMorphismsMulAction K L Y).smul σ (f.hom x) :=
  ConcreteCategory.congr_hom (f.hom.hom.comm σ) x

/-- The geometric-points functor is faithful. -/
private theorem geometricPointFunctor_faithful
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    (geometricPointFunctor K L).Faithful := by
  classical
  constructor
  intro X Y f g h
  apply (Scheme.Etale.forget (Spec (.of K))).map_injective
  apply Over.OverMorphism.ext
  obtain ⟨I, E, hfield, halgebra, hfinite, hsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K X.hom).mp
      X.prop
  let := hfield
  let := halgebra
  let := hfinite
  let := hsep
  apply (cancel_epi e.inv).mp
  apply Sigma.hom_ext
  intro i
  let : IsSepClosed L := IsSepClosure.sep_closed K
  let a : E i →ₐ[K] L := IsSepClosed.lift (K := K) (L := E i) (M := L)
  have : Surjective (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
    ⟨Function.surjective_to_subsingleton _⟩
  have : Epi (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
    Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (Spec.map (CommRingCat.ofHom a.toRingHom))).mp
  let x := (geometricPointSigmaEquiv K L X I E e he).symm ⟨i, a⟩
  have hx := congrArg (fun k => (k.hom x).left) h
  change x.left ≫ ((Scheme.Etale.forget (Spec (.of K))).map f).left =
    x.left ≫ ((Scheme.Etale.forget (Spec (.of K))).map g).left at hx
  dsimp only [x] at hx
  rwa [geometricPointSigmaEquiv_symm_left] at hx

/-- The geometric-points functor is full: an equivariant map of geometric points is induced by a
map of schemes. -/
private theorem geometricPointFunctor_full
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    (geometricPointFunctor K L).Full := by
  classical
  constructor
  intro X Y h
  obtain ⟨I, E, hfield, halgebra, hfinite, hsep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K X.hom).mp
      X.prop
  obtain ⟨J, F, hfield', halgebra', hfinite', hsep', e', he'⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K Y.hom).mp
      Y.prop
  let := hfield
  let := halgebra
  let := hfinite
  let := hsep
  let := hfield'
  let := halgebra'
  let := hfinite'
  let := hsep'
  let d := geometricPointSigmaEquiv K L X I E e he
  let d' := geometricPointSigmaEquiv K L Y J F e' he'
  let α (p : Σ i, E i →ₐ[K] L) : Σ j, F j →ₐ[K] L := d' (h.hom (d.symm p))
  have hα (σ : Gal(L/K)) (p : Σ i, E i →ₐ[K] L) :
      α ⟨p.1, σ.toAlgHom.comp p.2⟩ =
        ⟨(α p).1, σ.toAlgHom.comp (α p).2⟩ := by
    dsimp only [α, d, d']
    rw [geometricPointSigmaEquiv_symm_smul, geometricPointFunctor_map_smul]
    exact geometricPointSigmaEquiv_smul K L Y J F e' he' σ (h.hom (d.symm p))
  choose j φ hφ using equivariantMap_sigma_embeddings_of_finite_separable
    K L I J E F α hα
  let m (i : I) : Spec (.of (E i)) ⟶ ∐ fun j ↦ Spec (.of (F j)) :=
    Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫
      Sigma.ι (fun j ↦ Spec (.of (F j))) (j i)
  let f : X.left ⟶ Y.left := e.hom ≫ Sigma.desc m ≫ e'.inv
  have hbase : e'.inv ≫ Y.hom =
      Sigma.desc (fun j ↦ Spec.map (CommRingCat.ofHom (algebraMap K (F j)))) := by
    rw [← he', Iso.inv_hom_id_assoc]
  have hf : f ≫ Y.hom = X.hom := by
    dsimp only [f]
    rw [Category.assoc, Category.assoc, hbase, ← he]
    congr 1
    apply Sigma.hom_ext
    intro i
    simp only [Category.assoc, Sigma.ι_desc, Sigma.ι_desc_assoc, m]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext k
    exact (φ i).commutes k
  let fOver : (Scheme.Etale.forget (Spec (.of K))).obj X ⟶
      (Scheme.Etale.forget (Spec (.of K))).obj Y := Over.homMk f hf
  let fEtale : X ⟶ Y := (Scheme.Etale.forget (Spec (.of K))).preimage fOver
  refine ⟨fEtale, ?_⟩
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  ext x
  obtain ⟨p, rfl⟩ := d.symm.surjective x
  have hp : h.hom (d.symm p) = d'.symm ⟨j p.1, p.2.comp (φ p.1)⟩ :=
    d'.eq_symm_apply.mpr (hφ p.1 p.2)
  show ((geometricPointFunctor K L).map fEtale).hom (d.symm p) = h.hom (d.symm p)
  rw [hp]
  apply Over.OverMorphism.ext
  show (d.symm p).left ≫
      ((Scheme.Etale.forget (Spec (.of K))).map fEtale).left = _
  have hmap : (Scheme.Etale.forget (Spec (.of K))).map fEtale = fOver :=
    Functor.map_preimage _ _
  rw [hmap]
  show (d.symm p).left ≫ f = _
  rw [geometricPointSigmaEquiv_symm_left, geometricPointSigmaEquiv_symm_left]
  dsimp only [f]
  calc
    _ = Spec.map (CommRingCat.ofHom p.2.toRingHom) ≫
          Sigma.ι (fun i ↦ Spec (.of (E i))) p.1 ≫
          (e.inv ≫ e.hom) ≫ Sigma.desc m ≫ e'.inv := by
            simp only [Category.assoc]
            rfl
    _ = _ := by
      simp only [Iso.inv_hom_id, Category.id_comp, m,
        ← Category.assoc, Sigma.ι_desc, AlgHom.toRingHom_eq_coe,
        AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp]

/-- The geometric-points functor is essentially surjective. -/
private theorem geometricPointFunctor_essSurj
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    (geometricPointFunctor K L).EssSurj := by
  constructor
  intro S
  refine ⟨continuousGSetOrbitEtaleObject K L S, ⟨?_⟩⟩
  apply Iso.symm
  apply ObjectProperty.isoMk
  apply ObjectProperty.isoMk
  refine Action.mkIso (continuousGSetOrbitPointsEquiv K L S).toIso ?_
  intro σ
  ext x
  exact continuousGSetOrbitPointsEquiv_smul K L S σ x

/-- The underlying set of the continuous Galois set of an étale scheme is its set of geometric
points. -/
private noncomputable def geometricPointFunctorUnderlyingEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : (Spec (.of K)).Etale) :
    ((geometricPointFunctor K L).obj X).obj.obj.V ≃
      (separableClosureGeometricPoint K L ⟶
        (Scheme.Etale.forget (Spec (.of K))).obj X) := Equiv.refl _

/-- That identification is natural in the étale scheme. -/
private theorem geometricPointFunctorUnderlyingEquiv_natural
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {X Y : (Spec (.of K)).Etale} (f : X ⟶ Y) (x :
      ((geometricPointFunctor K L).obj X).obj.obj.V) :
    geometricPointFunctorUnderlyingEquiv K L Y
        (((geometricPointFunctor K L).map f).hom x) =
      geometricPointFunctorUnderlyingEquiv K L X x ≫
        (Scheme.Etale.forget (Spec (.of K))).map f := by
  rfl

/-- Under that identification the Galois action is precomposition with the spectrum of the
automorphism. -/
private theorem geometricPointFunctorUnderlyingEquiv_action
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : (Spec (.of K)).Etale) (σ : Gal(L/K))
    (x : ((geometricPointFunctor K L).obj X).obj.obj.V) :
    (geometricPointFunctorUnderlyingEquiv K L X
      (ConcreteCategory.hom
        (((geometricPointFunctor K L).obj X).obj.obj.ρ σ) x)).left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (geometricPointFunctorUnderlyingEquiv K L X x).left := by
  rfl

/-- If `L` is a separable closure of `K`, schemes étale over `K` are
equivalent to discrete continuous `Gal(L/K)`-sets. The underlying set of the
image of `X` is naturally the set of morphisms `Spec L ⟶ X` over `Spec K`,
and the action of `σ` is precomposition by `Spec.map σ`. -/
@[stacks 03QR, sga "3 VIIB 2.5" "k a field", sga "4 VIII 2.1" "X_ét ≌ B_π"]
public theorem etaleEquivalenceContinuousGSet
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :
    ∃ E : (Spec (.of K)).Etale ≌ ContinuousGSet.{u, u} Gal(L/K),
      ∃ e : ∀ X,
        (E.functor.obj X).obj.obj.V ≃
          (separableClosureGeometricPoint K L ⟶
            (Scheme.Etale.forget (Spec (.of K))).obj X),
        (∀ {X Y} (f : X ⟶ Y) (x),
          e Y ((E.functor.map f).hom x) =
            e X x ≫ (Scheme.Etale.forget (Spec (.of K))).map f) ∧
        (∀ X (σ : Gal(L/K)) (x),
          (e X (ConcreteCategory.hom ((E.functor.obj X).obj.obj.ρ σ) x)).left =
            Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ (e X x).left) := by
  let : (geometricPointFunctor K L).Faithful := geometricPointFunctor_faithful K L
  let : (geometricPointFunctor K L).Full := geometricPointFunctor_full K L
  let : (geometricPointFunctor K L).EssSurj := geometricPointFunctor_essSurj K L
  let : (geometricPointFunctor K L).IsEquivalence := {}
  exact ⟨(geometricPointFunctor K L).asEquivalence, geometricPointFunctorUnderlyingEquiv K L,
    fun f x => geometricPointFunctorUnderlyingEquiv_natural K L f x,
    fun X σ x => geometricPointFunctorUnderlyingEquiv_action K L X σ x⟩

namespace ContinuousGSet

section

/-- The discrete topology on a type, as the forgetful functor to `TopCat` whose continuity
condition defines a `G`-set. -/
local instance hasForget₂TypeTopCat : HasForget₂ (Type v) TopCat.{v} :=
  { forget₂ := TopCat.discrete
    forget_comp := rfl }

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- A `G`-set, or discrete `G`-set: a set with a left action of `G` which is continuous when the
set is given the discrete topology and `G × X` the product topology. -/
@[stacks 04JJ "G-sets"]
public def ofMulAction (X : Type v) [MulAction G X]
    (h : (Action.ofMulAction G X).IsContinuous) : ContinuousGSet.{u, v} G :=
  ⟨⟨Action.ofMulAction G X, h⟩, ⟨rfl⟩⟩

variable {G}

/-- A morphism of `G`-sets is precisely a `G`-equivariant map of the underlying sets: no
continuity condition is imposed on it. -/
@[stacks 04JJ "morphisms of G-sets"]
public def homEquiv (X Y : ContinuousGSet.{u, v} G) :
    (X ⟶ Y) ≃ {f : X.obj.obj.V → Y.obj.obj.V // ∀ (g : G) (x : X.obj.obj.V),
      f (ConcreteCategory.hom (X.obj.obj.ρ g) x) =
        ConcreteCategory.hom (Y.obj.obj.ρ g) (f x)} where
  toFun f := ⟨ConcreteCategory.hom f.hom.hom.hom,
    fun g x => ConcreteCategory.congr_hom (f.hom.hom.comm g) x⟩
  invFun f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ↾f.1
      comm := fun g => by ext x; exact f.2 g x })
  left_inv _ := rfl
  right_inv _ := rfl

end

end ContinuousGSet

-- The category `G-Sets` of `G`-sets, also called discrete `G`-sets: a set with a left action of
-- `G` which is continuous when the set is discrete and `G × X` carries the product topology, and
-- all `G`-equivariant maps between two such as the morphisms.
add_to_stacks 04JJ "the category G-Sets" AlgebraicGeometry.ContinuousGSet

end AlgebraicGeometry
