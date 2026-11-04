module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.ProfiniteCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverFieldQuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale fundamental group of a field: separable points of étale covers

Let `K` be a field with separable closure `L` and an algebraically closed algebraic extension
`Ω ⊇ L`. A scheme finite étale over `Spec K` is a finite disjoint union of spectra of finite
separable extensions of `K`, so its `L`-points form a finite set on which the absolute Galois
group `Gal(L/K)` acts continuously. Extending an `L`-point along `L → Ω` is a
bijection onto the `Ω`-points.

## Main definitions

* `AlgebraicGeometry.FiniteContinuousGSet` — continuous `G`-sets on a finite discrete set,
  as a full subcategory of `AlgebraicGeometry.ContinuousGSet`.

## Implementation notes

The route to the equivalence is through the Tag 03QR equivalence
`AlgebraicGeometry.etaleEquivalenceContinuousGSet` between *all* schemes étale over `Spec K` and
discrete continuous `Gal(L/K)`-sets. Restricting it to the finite étale covers needs that a
cover is finite exactly when it has finitely many `L`-points
(`finite_iff_finite_separablePoints_of_etale`), which is proved from the decomposition of an
étale scheme over a field supplied by Tag 03PC and the fact that an algebra homomorphism out of
a finite product of fields factors through one factor.

## References

* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete
open scoped CategoryTheory.PreGaloisCategory

universe u v w

namespace AlgebraicGeometry


private theorem exists_algHom_lift_to_separableClosure
    (K L Ω E : Type u) [Field K] [Field L] [Field Ω] [Field E]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra K E] [Algebra.IsSeparable K E] (f : E →ₐ[K] Ω) :
    ∃ g : E →ₐ[K] L, (IsScalarTower.toAlgHom K L Ω).comp g = f := by
  classical
  let M : IntermediateField K Ω := separableClosure K Ω
  have hbot : separableClosure L Ω = ⊥ := by
    let _ : IsSepClosed L := (inferInstance : IsSepClosure K L).sep_closed
    exact (IsSepClosed.separableClosure_eq_bot_iff L Ω).2 inferInstance
  have hmap :
      (separableClosure K L).map (IsScalarTower.toAlgHom K L Ω) = M := by
    simpa [M] using
      (separableClosure.map_eq_of_separableClosure_eq_bot K hbot)
  have htop : separableClosure K L = ⊤ := by
    ext x
    simp only [mem_separableClosure_iff, IntermediateField.mem_top]
    exact ⟨fun _ => trivial, fun _ => Algebra.IsSeparable.isSeparable K x⟩
  let lmap : L →ₐ[K] M :=
    (IsScalarTower.toAlgHom K L Ω).codRestrict M.toSubalgebra (by
      intro x
      rw [← hmap]
      exact (IntermediateField.mem_map (separableClosure K L)).2
        ⟨x, by rw [htop]; exact Set.mem_univ _, rfl⟩)
  have hlmap_surj : Function.Surjective lmap := by
    intro y
    have hy : (y : Ω) ∈ (separableClosure K L).map
        (IsScalarTower.toAlgHom K L Ω) := by rw [hmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := (IntermediateField.mem_map (separableClosure K L)).1 hy
    exact ⟨x, Subtype.ext hxy⟩
  let e : L ≃ₐ[K] M := AlgEquiv.ofBijective lmap
    ⟨fun x y h => (IsScalarTower.toAlgHom K L Ω).injective (congrArg Subtype.val h), hlmap_surj⟩
  let f' : E →ₐ[K] M := f.codRestrict M.toSubalgebra (by
    intro x
    show f x ∈ M
    rw [mem_separableClosure_iff]
    exact IsSeparable.map f f.injective (Algebra.IsSeparable.isSeparable K x))
  refine ⟨e.symm.toAlgHom.comp f', ?_⟩
  ext x
  show (IsScalarTower.toAlgHom K L Ω) (e.symm (f' x)) = f x
  exact congrArg Subtype.val (e.apply_symm_apply (f' x))

/-- The `K`-algebra map `E i →ₐ[K] F` induced by `φ` through `Pi.single i`, given that `φ`
sends the idempotent `Pi.single i 1` to `1`. -/
public def piSingleAlgHom
    (K I : Type u) [Field K] [DecidableEq I]
    (E : I → Type u) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (F : Type u) [Field F] [Algebra K F]
    (φ : (∀ i, E i) →ₐ[K] F) (i : I) (hφ : φ (Pi.single i 1) = 1) :
    E i →ₐ[K] F where
  toFun x := φ (Pi.single i x)
  map_zero' := by simp
  map_one' := hφ
  map_add' x y := by rw [Pi.single_add, map_add]
  map_mul' x y := by rw [Pi.single_mul, map_mul]
  commutes' r := by
    have hs : Pi.single i (algebraMap K (E i) r) =
        algebraMap K (∀ i, E i) r * Pi.single i 1 := by
      ext j
      rcases eq_or_ne j i with rfl | hji
      · simp
      · simp [Pi.single_eq_of_ne hji]
    rw [hs, map_mul, AlgHom.commutes, hφ, mul_one]

private theorem algHom_prod_field_factor
    (K I : Type u) [Field K] [Finite I]
    (E : I → Type u) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (F : Type u) [Field F] [Algebra K F]
    (φ : (∀ i, E i) →ₐ[K] F) :
    ∃ i, ∃ ψ : E i →ₐ[K] F,
      φ = ψ.comp (Pi.evalAlgHom K E i) := by
  classical
  let A := ∀ i, E i
  let p : PrimeSpectrum A := ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hker : Ideal.comap (Pi.evalRingHom E i) q.asIdeal =
      RingHom.ker φ.toRingHom := by
    have h := congrArg PrimeSpectrum.asIdeal hq
    rwa [PrimeSpectrum.comap_asIdeal] at h
  let e : A := Pi.single i (1 : E i)
  have hh : Pi.evalRingHom E i e = 1 := by simp [e]
  have heval : e ∉ Ideal.comap (Pi.evalRingHom E i) q.asIdeal := by
    intro hmem
    have hone : (1 : E i) ∈ q.asIdeal := by
      simpa [hh] using (Ideal.mem_comap.mp hmem)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  have hφe : φ e ≠ 0 := fun h =>
    (hker ▸ heval : e ∉ RingHom.ker φ.toRingHom) (RingHom.mem_ker.mpr h)
  have heidem : e * e = e := by
    show Pi.single i (1 : E i) * Pi.single i 1 = Pi.single i 1
    rw [← Pi.single_mul, mul_one]
  have hφe_one : φ e = 1 :=
    mul_left_cancel₀ hφe (by rw [← map_mul, heidem, mul_one])
  refine ⟨i, piSingleAlgHom K I E F φ i hφe_one, ?_⟩
  apply AlgHom.ext
  intro x
  have hmem : x - Pi.single i (x i) ∈ RingHom.ker φ.toRingHom := by
    rw [← hker, Ideal.mem_comap]
    simp
  have hfx : φ x = φ (Pi.single i (x i)) :=
    sub_eq_zero.mp ((map_sub φ x _).symm.trans (RingHom.mem_ker.mp hmem))
  simpa [piSingleAlgHom] using hfx

private theorem nonempty_algHom_to_separableClosure
    (K L E : Type u) [Field K] [Field L] [Field E]
    [Algebra K L] [IsSepClosure K L] [Algebra K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] :
    Nonempty (E →ₐ[K] L) ∧ Finite (E →ₐ[K] L) := by
  let : IsSepClosed L := (inferInstance : IsSepClosure K L).sep_closed
  exact ⟨⟨IsSepClosed.lift (K := K) (L := E)⟩, inferInstance⟩

/-- The structure map of `Spec (∏ i, E i)` restricts on each summand of `∐ i, Spec (E i)` to the
structure map of `Spec (E i)`. -/
public theorem sigmaSpec_comp_spec_algebraMap
    (K I : Type u) [Field K] (E : I → Type u) [∀ i, Field (E i)] [∀ i, Algebra K (E i)] :
    sigmaSpec (fun i ↦ CommRingCat.of (E i)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, E i))) =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Sigma.ι_desc,
    Spec.map_inj]
  apply ConcreteCategory.ext
  ext x
  rfl

/-- A coproduct decomposition `U ≅ ∐ Spec (E i)` over `K` gives an isomorphism
`U ≅ Spec (∀ i, E i)` over `K`. -/
private theorem exists_iso_spec_pi_of_decomposition
    (K : Type u) [Field K] {U : Scheme.{u}} (f : U ⟶ Spec (.of K))
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f) :
    ∃ e' : U ≅ Spec (.of (∀ i, E i)),
      e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, E i))) = f :=
  ⟨e.trans (asIso (sigmaSpec fun i ↦ CommRingCat.of (E i))), by
    rw [Iso.trans_hom, asIso_hom, Category.assoc, sigmaSpec_comp_spec_algebraMap, he]⟩

private theorem finite_of_finite_index
    (K : Type u) [Field K] {U : Scheme.{u}} (f : U ⟶ Spec (.of K))
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f) : IsFinite f := by
  obtain ⟨e', hf⟩ := exists_iso_spec_pi_of_decomposition K f I E e he
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (∀ i, E i)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  rw [← hf]
  infer_instance

/-- A finite étale `K`-scheme decomposed as a coproduct of spectra of finite field extensions
`E i` of `K` has finitely many summands. -/
theorem finite_index_of_isFinite
    (K : Type u) [Field K] {U : Scheme.{u}} (f : U ⟶ Spec (.of K))
    [Etale f] (I : Type u) (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (_he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f)
    [IsFinite f] : Finite I :=
  have : CompactSpace ↥U :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  finite_index_of_iso_sigma e fun i ↦ (inferInstance : Inhabited (Spec (.of (E i)))).default

private theorem finite_index_of_finite_points
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f]
    (I : Type u) (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f)
    [Finite {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))}] : Finite I := by
  classical
  let p : ∀ i : I, Spec (.of L) ⟶ U := fun i =>
    Spec.map (CommRingCat.ofHom
      (Classical.choice (nonempty_algHom_to_separableClosure K L (E i)).1).toRingHom) ≫
      Sigma.ι (fun i ↦ Spec (.of (E i))) i ≫ e.inv
  have hp (i : I) : p i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    dsimp only [p]
    rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_desc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
    apply ConcreteCategory.ext
    ext x
    exact (Classical.choice (nonempty_algHom_to_separableClosure K L (E i)).1).commutes x
  let q : I → {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))} := fun i => ⟨p i, hp i⟩
  have hq : Function.Injective q := by
    intro i j hij
    have hmaps :
        Spec.map (CommRingCat.ofHom
          (Classical.choice (nonempty_algHom_to_separableClosure K L (E i)).1).toRingHom) ≫
          Sigma.ι (fun i ↦ Spec (.of (E i))) i =
        Spec.map (CommRingCat.ofHom
          (Classical.choice (nonempty_algHom_to_separableClosure K L (E j)).1).toRingHom) ≫
          Sigma.ι (fun i ↦ Spec (.of (E i))) j := by
      have h := congrArg (fun g : Spec (.of L) ⟶ U => g ≫ e.hom)
        (congrArg Subtype.val hij)
      simpa [q, p, Category.assoc] using h
    have hpoints := congrArg (fun g : Spec (.of L) ⟶ _ => g (IsLocalRing.closedPoint L)) hmaps
    exact congrArg Sigma.fst ((sigmaι_eq_iff (fun i ↦ Spec (.of (E i))) i j _ _).mp hpoints)
  exact Finite.of_injective q hq

private theorem finite_of_finite_points
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f]
    (I : Type u) (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f)
    [Finite {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))}] : IsFinite f := by
  have := finite_index_of_finite_points K L f I E e he
  exact finite_of_finite_index K f I E e he

private theorem finite_points_of_finite_index
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K))
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f) :
    Finite {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))} := by
  classical
  obtain ⟨e', hf⟩ := exists_iso_spec_pi_of_decomposition K f I E e he
  let A : Type u := ∀ i, E i
  let g : Spec (.of A) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  have : Module.Free K A := Module.Free.of_divisionRing K A
  have : Finite (A →ₐ[K] L) := Finite.algHom K A L
  let P := {p : Spec (.of L) ⟶ U //
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))}
  let r : P → (CommRingCat.of A ⟶ CommRingCat.of L) := fun p =>
    Spec.homEquiv (p.1 ≫ e'.hom)
  have hr (p : P) :
      CommRingCat.ofHom (algebraMap K A) ≫ r p =
        CommRingCat.ofHom (algebraMap K L) := by
    have hp : (p.1 ≫ e'.hom) ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [Category.assoc, hf]; exact p.2
    rw [← Spec.map_inj]
    simpa [r, g, Spec.homEquiv] using hp
  let q : P → A →ₐ[K] L := fun p =>
    { toRingHom := (r p).hom
      commutes' := fun x =>
        congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of L => φ.hom x) (hr p) }
  have hq : Function.Injective q := fun p p' h => Subtype.ext <| (cancel_mono e'.hom).1 <|
    Spec.homEquiv.injective (CommRingCat.hom_ext (congrArg AlgHom.toRingHom h))
  exact Finite.of_injective q hq

private theorem finite_iff_finite_separablePoints
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f]
    (I : Type u) (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f) :
    IsFinite f ↔ Finite {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))} :=
  ⟨fun _ => have := finite_index_of_isFinite K f I E e he
      finite_points_of_finite_index K L f I E e he,
    fun _ => finite_of_finite_points K L f I E e he⟩

private theorem finite_iff_finite_separablePoints_of_etale
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f] :
    IsFinite f ↔ Finite {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))} := by
  obtain ⟨I, E, hField, hAlg, hFinite, hSep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable K f).mp inferInstance
  let : ∀ i, Field (E i) := hField
  let : ∀ i, Algebra K (E i) := hAlg
  let : ∀ i, Module.Finite K (E i) := hFinite
  let : ∀ i, Algebra.IsSeparable K (E i) := hSep
  exact finite_iff_finite_separablePoints K L f I E e he

/-- Extend an `L`-point of a `K`-scheme `U` to an `Ω`-point along `Spec Ω ⟶ Spec L`. -/
public def extendSeparablePoint
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K))
    (p : {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))}) :
    {g : Spec (.of Ω) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))} := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
  refine ⟨a ≫ p.1, ?_⟩
  calc
    a ≫ p.1 ≫ f = a ≫ (p.1 ≫ f) := by simp
    _ = a ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by rw [p.2]
    _ = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      ext x
      exact (IsScalarTower.algebraMap_apply K L Ω x).symm

/-- For an étale `K`-scheme decomposed as a finite coproduct of spectra of finite field
extensions, extending `L`-points to `Ω`-points is injective. -/
theorem point_extension_injective_with_decomposition
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f]
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (_he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f)
    (p q : {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))})
    (h : extendSeparablePoint K L Ω f p = extendSeparablePoint K L Ω f q) : p = q := by
  classical
  obtain ⟨e', -⟩ := exists_iso_spec_pi_of_decomposition K f I E e _he
  have hmaps : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        (p.1 ≫ e'.hom) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        (q.1 ≫ e'.hom) := by
    have hh := congrArg Subtype.val h
    simpa [extendSeparablePoint, Category.assoc] using
      congrArg (fun g : Spec (.of Ω) ⟶ U => g ≫ e'.hom) hh
  let rp := Spec.homEquiv (p.1 ≫ e'.hom)
  let rq := Spec.homEquiv (q.1 ≫ e'.hom)
  have hr : rp ≫ CommRingCat.ofHom (algebraMap L Ω) =
      rq ≫ CommRingCat.ofHom (algebraMap L Ω) := by
    simpa [rp, rq, Spec.homEquiv, Spec.preimage_comp] using
      congrArg Spec.preimage hmaps
  have hr' : rp = rq := CommRingCat.hom_ext <| RingHom.ext fun a =>
    (IsScalarTower.toAlgHom K L Ω).injective
      (congrArg (fun g : CommRingCat.of (∀ i, E i) ⟶ CommRingCat.of Ω => g.hom a) hr)
  exact Subtype.ext ((cancel_mono e'.hom).1 (Spec.homEquiv.injective hr'))

/-- Every `K`-algebra map from a finite product of finite separable extensions of `K` to `Ω`
factors through the separable closure `L`. -/
public theorem exists_algHom_pi_lift_to_separableClosure
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra.IsSeparable K (E i)]
    (φ : (∀ i, E i) →ₐ[K] Ω) :
    ∃ ψ : (∀ i, E i) →ₐ[K] L, (IsScalarTower.toAlgHom K L Ω).comp ψ = φ := by
  obtain ⟨i, ψΩ, hφΩ⟩ := algHom_prod_field_factor K I E Ω φ
  obtain ⟨ψL, hψL⟩ := exists_algHom_lift_to_separableClosure K L Ω (E i) ψΩ
  refine ⟨ψL.comp (Pi.evalAlgHom K E i), ?_⟩
  rw [← AlgHom.comp_assoc, hψL, hφΩ]

/-- A point of `Spec A` over `K` with values in `Ω` comes from one with values in `L` whenever
every `K`-algebra map `A →ₐ[K] Ω` factors through `L`. -/
public theorem exists_spec_point_lift_of_algHom_lift
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : Type u) [CommRing A] [Algebra K A]
    (hA : ∀ φ : A →ₐ[K] Ω, ∃ ψ : A →ₐ[K] L, (IsScalarTower.toAlgHom K L Ω).comp ψ = φ)
    (x : Spec (.of Ω) ⟶ Spec (.of A))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ y : Spec (.of L) ⟶ Spec (.of A),
      y ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ y = x := by
  let r := Spec.homEquiv x
  have hcomm : CommRingCat.ofHom (algebraMap K A) ≫ r =
      CommRingCat.ofHom (algebraMap K Ω) := by
    have hpre := congrArg Spec.preimage hx
    rw [Spec.preimage_comp, Spec.preimage_map] at hpre
    simpa [r] using hpre
  obtain ⟨φL, hφ⟩ := hA {
    toRingHom := r.hom
    commutes' := fun a =>
      congrArg (fun k : CommRingCat.of K ⟶ CommRingCat.of Ω => k.hom a) hcomm }
  have hKL : CommRingCat.ofHom (algebraMap K A) ≫ CommRingCat.ofHom φL.toRingHom =
      CommRingCat.ofHom (algebraMap K L) :=
    CommRingCat.hom_ext (RingHom.ext φL.commutes)
  have hφring : CommRingCat.ofHom φL.toRingHom ≫
      CommRingCat.ofHom (IsScalarTower.toAlgHom K L Ω).toRingHom = r := by
    rw [← CommRingCat.ofHom_comp]
    exact CommRingCat.hom_ext (RingHom.ext fun a => congrArg (fun b : A →ₐ[K] Ω => b a) hφ)
  refine ⟨Spec.map (CommRingCat.ofHom φL.toRingHom), ?_, ?_⟩
  · rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
  · apply Spec.homEquiv.injective
    simpa [r, Spec.preimage_comp, Spec.preimage_map] using hφring

/-- For an étale `K`-scheme decomposed as a finite coproduct of spectra of finite separable
field extensions, every `Ω`-point is the extension of an `L`-point, when `L` is a separable
closure of `K` and `Ω` an algebraically closed algebraic extension. -/
theorem point_extension_surjective_with_decomposition
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f]
    (I : Type u) (E : I → Type u) [Finite I]
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, Algebra.IsSeparable K (E i)]
    (e : U ≅ ∐ fun i ↦ Spec (.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))) = f)
    (p : {g : Spec (.of Ω) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))}) :
    ∃ q : {g : Spec (.of L) ⟶ U //
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))},
      extendSeparablePoint K L Ω f q = p := by
  classical
  obtain ⟨e', hf⟩ := exists_iso_spec_pi_of_decomposition K f I E e he
  obtain ⟨y, hy, hyx⟩ := exists_spec_point_lift_of_algHom_lift K L Ω (∀ i, E i)
    (exists_algHom_pi_lift_to_separableClosure K L Ω I E) (p.1 ≫ e'.hom)
    (by rw [Category.assoc, hf]; exact p.2)
  refine ⟨⟨y ≫ e'.inv, by rw [Category.assoc, ← hf, Iso.inv_hom_id_assoc]; exact hy⟩,
    Subtype.ext ?_⟩
  rw [← cancel_mono e'.hom]
  simpa [extendSeparablePoint, Category.assoc] using hyx

/-- A continuous `G`-set with finite underlying set, viewed as a continuous action of `G` on a
finite set with the discrete topology. -/
public def discreteActionToFiniteContAction
    {G : Type u} [Group G] [TopologicalSpace G]
    (X : ContinuousGSet G) [Finite X.obj.obj.V] :
    ContAction FintypeCat.{u} G := by
  letI : Fintype X.obj.obj.V := Fintype.ofFinite X.obj.obj.V
  letI : TopologicalSpace X.obj.obj.V := ⊥
  letI : DiscreteTopology X.obj.obj.V := ⟨rfl⟩
  refine ⟨?_, ?_⟩
  · exact {
      V := FintypeCat.of X.obj.obj.V
      ρ := {
        toFun := fun g => FintypeCat.homMk (X.obj.obj.ρ g)
        map_one' := by
          apply FintypeCat.hom_ext
          intro x
          change X.obj.obj.ρ 1 x = x
          exact congrArg (fun f : End X.obj.obj.V => f x) X.obj.obj.ρ.map_one
        map_mul' := by
          intro g h
          apply FintypeCat.hom_ext
          intro x
          change X.obj.obj.ρ (g * h) x =
            X.obj.obj.ρ g (X.obj.obj.ρ h x)
          simp } }
  · let : HasForget₂ (Type u) TopCat :=
      { forget₂ := TopCat.discrete, forget_comp := rfl }
    rw [Action.isContinuous_def]
    exact (Action.isContinuous_def X.obj.obj).mp X.obj.property

/-- Morphisms in `Over S` are the same as morphisms of the underlying schemes commuting with
the structure maps. -/
public def overHomPointEquiv {S : Scheme.{u}} (P Q : Over S) :
    (P ⟶ Q) ≃ {f : P.left ⟶ Q.left // f ≫ Q.hom = P.hom} where
  toFun g := ⟨g.left, g.w⟩
  invFun f := Over.homMk f.1 f.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := Subtype.ext rfl

private theorem finite_etaleActionCarrier
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X))
    {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) [Etale f] (hfinite : IsFinite f) :
    Finite ((E.functor.obj (Scheme.Etale.mk f)).obj.obj.V) :=
  (pointIso _).finite_iff.mpr ((overHomPointEquiv _ _).finite_iff.mpr
    ((finite_iff_finite_separablePoints_of_etale K L f).mp hfinite))

/-- The full subcategory of continuous `G`-sets whose underlying set is finite. -/
public abbrev FiniteContinuousGSet (G : Type u) [Group G] [TopologicalSpace G] :=
  ObjectProperty.FullSubcategory
    (fun X : ContinuousGSet G => Finite X.obj.obj.V)

/-- The functor from finite continuous `G`-sets to continuous actions of `G` on finite sets. -/
public def finiteContinuousGSetFunctor
    {G : Type u} [Group G] [TopologicalSpace G] :
    FiniteContinuousGSet G ⥤ ContAction FintypeCat.{u} G where
  obj X := by
    letI : Finite X.obj.obj.obj.V := X.property
    exact discreteActionToFiniteContAction X.obj
  map {X Y} f := by
    let f₀ := f.hom.hom.hom
    refine ⟨Action.Hom.mk (FintypeCat.homMk f₀.hom) ?_⟩
    intro g
    apply FintypeCat.hom_ext
    intro x
    change ConcreteCategory.hom f₀.hom
        (ConcreteCategory.hom (X.obj.obj.obj.ρ g) x) =
      ConcreteCategory.hom (Y.obj.obj.obj.ρ g)
        (ConcreteCategory.hom f₀.hom x)
    exact ConcreteCategory.congr_hom (f₀.comm g) x
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply FintypeCat.hom_ext
    intro x
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply FintypeCat.hom_ext
    intro x
    rfl

/-- The functor from continuous actions of `G` on finite sets to finite continuous `G`-sets,
giving each finite set the discrete topology. -/
public def finiteActionToFiniteGSet
    {G : Type u} [Group G] [TopologicalSpace G] :
    ContAction FintypeCat.{u} G ⥤ FiniteContinuousGSet G := by
  letI : HasForget₂ (Type u) TopCat.{u} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  have h : ∀ X : ContAction FintypeCat.{u} G,
      ((FintypeCat.incl.mapAction G).obj X.obj).IsContinuous := by
    intro X
    let : TopologicalSpace X.obj.V.obj := ⊥
    let : DiscreteTopology X.obj.V.obj := ⟨rfl⟩
    rw [Action.isContinuous_def]
    have hX := (Action.isContinuous_def X.obj).mp X.property
    convert hX using 1 <;> rfl
  let F := FintypeCat.incl.mapContAction G h
  have hdisc : ∀ X : ContAction FintypeCat.{u} G,
      ContAction.IsDiscrete (V := Type u) (G := G) (F.obj X) := fun _ => ⟨rfl⟩
  let F' : ContAction FintypeCat.{u} G ⥤ ContinuousGSet G :=
    ObjectProperty.lift _ F hdisc
  exact ObjectProperty.lift _ F' fun X => X.obj.V.property

/-- Finite continuous `G`-sets are equivalent to continuous actions of `G` on finite sets. -/
public def finiteContinuousGSetEquivalence
    {G : Type u} [Group G] [TopologicalSpace G] :
    FiniteContinuousGSet G ≌ ContAction FintypeCat.{u} G where
  functor := finiteContinuousGSetFunctor
  inverse := finiteActionToFiniteGSet
  unitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Action.mkIso
      (show X.obj.obj.obj.V ≅
        ((finiteContinuousGSetFunctor ⋙ finiteActionToFiniteGSet).obj X).obj.obj.obj.V
        from Iso.refl _)
      (by intro g; rfl)))))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      rfl)
  counitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Action.mkIso
    (FintypeCat.equivEquivIso
      (show (((finiteActionToFiniteGSet ⋙ finiteContinuousGSetFunctor).obj X).obj.V).obj ≃
        X.obj.V.obj from Equiv.refl _))
    (by intro g; apply FintypeCat.hom_ext; intro x; rfl)))
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply FintypeCat.hom_ext
      intro x
      rfl)
  functor_unitIso_comp := by
    intro X
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply FintypeCat.hom_ext
    intro x
    rfl

/-- The full subcategory of the small étale site of `X` on the objects that are finite
over `X`. -/
public abbrev finiteEtaleObjectsInEtaleSite (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun Y : X.Etale => IsFinite Y.hom)

/-- The functor from finite étale schemes over `X` to the finite objects of the small étale
site of `X`. -/
public def finiteEtaleToEtaleFinite (X : Scheme.{u}) :
    FiniteEtaleOver X ⥤ finiteEtaleObjectsInEtaleSite X :=
  ObjectProperty.lift _
    (MorphismProperty.Over.changeProp (P := finiteEtale) (Q := ⊤)
      (P' := @Etale) (Q' := ⊤) X (by
        intro A B f hf
        exact (MorphismProperty.inf_iff _ _ f).mp hf |>.2) le_rfl)
    (by intro Y; exact Y.prop.1)

/-- The functor from the finite objects of the small étale site of `X` to finite étale schemes
over `X`. -/
public def etaleFiniteToFiniteEtale (X : Scheme.{u}) :
    finiteEtaleObjectsInEtaleSite X ⥤ FiniteEtaleOver X where
  obj Y := MorphismProperty.Over.mk _ Y.1.hom ⟨Y.2, Y.1.prop⟩
  map f := MorphismProperty.Over.homMk f.hom.left f.hom.w
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Finite étale schemes over `X` are equivalent to the finite objects of the small étale site
of `X`. -/
public def finiteEtaleEtaleEquivalence (X : Scheme.{u}) :
    FiniteEtaleOver X ≌ finiteEtaleObjectsInEtaleSite X where
  functor := finiteEtaleToEtaleFinite X
  inverse := etaleFiniteToFiniteEtale X
  unitIso := NatIso.ofComponents (fun Y =>
    MorphismProperty.Over.isoMk (P := finiteEtale) (Q := ⊤)
      (Iso.refl Y.left)) (by intro Y Z f; ext; rfl)
  counitIso := NatIso.ofComponents (fun Y =>
    ObjectProperty.isoMk _ (Iso.refl Y.1)) (by intro Y Z f; ext; rfl)
  functor_unitIso_comp := by intro Y; ext; rfl

private theorem finiteEtale_of_finite_separablePoints
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X))
    (Y : (Spec (.of K)).Etale)
    (hfinite : Finite (E.functor.obj Y).obj.obj.V) : IsFinite Y.hom := by
  let : Etale Y.hom := Y.prop
  exact (finite_iff_finite_separablePoints_of_etale K L Y.hom).mpr
    ((overHomPointEquiv _ _).finite_iff.mp ((pointIso Y).finite_iff.mp hfinite))

/-- The restriction of an equivalence between the small étale site of `Spec K` and continuous
`Gal(L/K)`-sets to the finite objects, landing in finite continuous `Gal(L/K)`-sets. -/
public def finiteEtaleSiteToFiniteGSet
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X)) :
    finiteEtaleObjectsInEtaleSite (Spec (.of K)) ⥤
      FiniteContinuousGSet Gal(L/K) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ E.functor) (by
    intro Y
    exact finite_etaleActionCarrier K L E pointIso Y.1.hom Y.2)

/-- The restriction of the inverse of an equivalence between the small étale site of `Spec K`
and continuous `Gal(L/K)`-sets to finite continuous `Gal(L/K)`-sets, landing in the finite
objects of the étale site. -/
public def finiteGSetToFiniteEtaleSite
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X)) :
    FiniteContinuousGSet Gal(L/K) ⥤
      finiteEtaleObjectsInEtaleSite (Spec (.of K)) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ E.inverse) (by
    intro X
    let α := (E.functor.obj (E.inverse.obj X.1)).obj.obj.V
    let β := X.1.obj.obj.V
    let f : α → β := (E.counitIso.app X.1).hom.hom.hom.hom
    let g : β → α := (E.counitIso.app X.1).inv.hom.hom.hom.hom
    have hfg : Function.LeftInverse g f := by
      intro a
      have h := congrArg (fun k => k.hom.hom.hom.hom)
        (E.counitIso.app X.1).hom_inv_id
      change g (f a) = a
      exact congrArg (fun k => k a) h
    have hgf : Function.RightInverse g f := by
      intro b
      have h := congrArg (fun k => k.hom.hom.hom.hom)
        (E.counitIso.app X.1).inv_hom_id
      change f (g b) = b
      exact congrArg (fun k => k b) h
    let : Finite β := X.2
    have hfinite : Finite α := Finite.of_equiv β ⟨g, f, hgf, hfg⟩
    change IsFinite (E.inverse.obj X.1).hom
    exact finiteEtale_of_finite_separablePoints K L E pointIso
      (E.inverse.obj X.1) hfinite)

end AlgebraicGeometry

end
