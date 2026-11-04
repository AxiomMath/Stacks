module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeSystem
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.SpreadingOut.ColimitSystem
public import StacksFrontier.RingTheory.SpreadingOut.Flat

/-!
# Openness of the relative flat locus

Let `R → S` be a finitely presented map of rings and let `M` be a finitely presented `S`-module.
The set of primes `q` of `S` for which the localization `M_q` is flat over `R` is open in
`Spec(S)`.

## Main results

* `Module.isOpen_setOf_flat_localizedModule_atPrime`: for `R → S` of finite presentation and `M`
  a finitely presented `S`-module, the set of primes `q` of `S` with `M_q` flat over `R` is open.
* `Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing`: the case of a
  Noetherian base and a finite type algebra.
* `Algebra.FiniteTypeSystem.exists_flat_localized_stage`: flatness at a prime descends to a
  finite stage of the directed system of finite type models of `S` over subrings of `R` of finite
  type over `ℤ`.
* `Algebra.FiniteTypeSystem.flat_localized_of_le`,
  `Algebra.FiniteTypeSystem.flat_localized_of_stage`: flatness at a prime ascends along the
  system and to its colimit.

## Implementation notes

The categorical diagrams need a common universe for `R` and `S`; since `S` is of finite type
over `R` it is `R`-isomorphic to a ring in the universe of `R`, which removes the restriction.

## References

* [Stacks Project, Tag 00RC](https://stacks.math.columbia.edu/tag/00RC)
-/

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace OpenFlatLocus

/-- Along a surjection `A → B`, the localization of a `B`-module at a prime `q` is also its
localization, as an `A`-module, at the prime of `A` under `q`. -/
private theorem isLocalizedModule_atPrime_restrictScalars_of_surjective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hs : Function.Surjective (algebraMap A B))
    (X : Type*) [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (q : Ideal B) [q.IsPrime] :
    IsLocalizedModule (q.comap (algebraMap A B)).primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl X).restrictScalars A) := by
  have he : Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl =
      q.primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      obtain ⟨a, rfl⟩ := hs b
      exact ⟨a, hb, rfl⟩
  have : IsLocalizedModule
      (Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl X) := by
    rw [he]
    infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- Along a surjection `A → B`, localizing a `B`-module at a prime `q` or at its preimage in `A`
gives the same flatness condition over a common base `R`. -/
public theorem _root_.Module.flat_localizedModule_atPrime_comap_iff_of_surjective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hs : Function.Surjective (algebraMap A B))
    (X : Type*) [AddCommGroup X] [Module R X] [Module A X] [Module B X]
    [IsScalarTower R A X] [IsScalarTower R B X] [IsScalarTower A B X]
    (q : Ideal B) [q.IsPrime] :
    Module.Flat R (LocalizedModule.AtPrime (q.comap (algebraMap A B)) X) ↔
      Module.Flat R (LocalizedModule.AtPrime q X) := by
  have := isLocalizedModule_atPrime_restrictScalars_of_surjective hs X q
  exact Module.Flat.equiv_iff
    ((IsLocalizedModule.linearEquiv (q.comap (algebraMap A B)).primeCompl
      (LocalizedModule.mkLinearMap _ X)
      ((LocalizedModule.mkLinearMap q.primeCompl X).restrictScalars A)).restrictScalars R)

/-- For a Noetherian ring `R`, a finite type
`R`-algebra `S` and a finite `S`-module `M`, the locus of primes `q` of `S` at which `M_q` is flat
over `R` is open. -/
public theorem _root_.Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : Module (MvPolynomial (Fin n) R) M := Module.compHom M f.toRingHom
  have : IsScalarTower (MvPolynomial (Fin n) R) S M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (MvPolynomial (Fin n) R) M :=
    IsScalarTower.to₁₂₄ R (MvPolynomial (Fin n) R) S M
  have : Module.Finite (MvPolynomial (Fin n) R) S :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) hf
  have : Module.Finite (MvPolynomial (Fin n) R) M := Module.Finite.trans S M
  have := Module.finitePresentation_of_finite (MvPolynomial (Fin n) R) M
  have h := Stacks.Flatness.OpenFlatLocus.isOpen_setOf_flat_localizedModule_atPrime_mvPolynomial
    (R := R) (M := M) (n := n)
  convert h.preimage (PrimeSpectrum.continuous_comap f.toRingHom) using 1
  ext q
  exact (Module.flat_localizedModule_atPrime_comap_iff_of_surjective (R := R) hf M q.asIdeal).symm

/-- A commuting square of ring maps gives equal double preimages of an ideal. -/
private theorem comap_comap_eq_of_comp_eq {A B X Y : CommRingCat.{u}} {φ : A ⟶ B} {σ : B ⟶ Y}
    {ρ : A ⟶ X} {f : X ⟶ Y} (h : φ ≫ σ = ρ ≫ f) (q : Ideal Y) :
    (q.comap f.hom).comap ρ.hom = (q.comap σ.hom).comap φ.hom := by
  rw [Ideal.comap_comap, Ideal.comap_comap, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, h]

/-- A triangle of ring maps gives equal preimages of an ideal. -/
private theorem comap_comap_eq_comap_of_comp_eq {X Y Z : CommRingCat.{u}} {a : X ⟶ Y}
    {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c) (q : Ideal Z) :
    (q.comap b.hom).comap a.hom = q.comap c.hom := by
  rw [Ideal.comap_comap, ← CommRingCat.hom_comp, h]

/-- Transport along a map compatible with the maps to `R` preserves membership in the complement
of the preimage of a prime. -/
private theorem map_mem_primeCompl_comap {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    {u : A →+* B} {gA : A →+* R} {gB : B →+* R} (hu : ∀ x, gB (u x) = gA x) {q : Ideal R}
    [q.IsPrime] {x : A} (hx : gA x ∈ q.primeCompl) : u x ∈ (q.comap gB).primeCompl := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, hu]
  exact hx

/-- An element killed by the leg of a colimit cocone of a directed diagram of rings is killed by
some transition map. -/
private theorem exists_map_eq_zero_of_isColimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I ⥤ CommRingCat.{u}) {T : CommRingCat.{u}}
    {ρ : F ⟶ (Functor.const I).obj T} (hρ : IsColimit (Cocone.mk T ρ)) (i : I) (x : F.obj i)
    (hx : (ρ.app i).hom x = 0) : ∃ (j : I) (h : i ≤ j), (F.map (homOfLE h)).hom x = 0 := by
  obtain ⟨j, a, b, hab⟩ := (IsColimit.eq_iff F hρ).mp
    (show (ρ.app i).hom x = (ρ.app i).hom 0 by simpa using hx)
  refine ⟨j, a.le, ?_⟩
  rw [show homOfLE a.le = a from Subsingleton.elim _ _]
  simpa only [map_zero] using hab

/-- The transition maps of a diagram of rings indexed by a preorder form a directed system. -/
private theorem directedSystem_map_homOfLE {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) :
    DirectedSystem (fun i => ↑(F.obj i)) (fun i j (h : i ≤ j) => ⇑(F.map (homOfLE h)).hom) where
  map_self i x := by simp
  map_map {i j k} h h' x :=
    (ConcreteCategory.congr_hom (F.map_comp (homOfLE h) (homOfLE h')) x).symm

/-- Localizing a directed system of rings at the preimages of a prime `q` of its colimit `R`
gives a system whose colimit is `R_q`: the maps to `R_q` are jointly surjective. -/
private theorem localization_jointly_surjective
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    {R : Type*} [CommRing R] (g : ∀ i, A i →+* R)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)
    (hs : ∀ x, ∃ i y, g i y = x)
    (q : Ideal R) [q.IsPrime]
    (L : I → Type*) [∀ i, CommRing (L i)] [∀ i, Algebra (A i) (L i)]
    [∀ i, IsLocalization (q.comap (g i)).primeCompl (L i)]
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization q.primeCompl T]
    (l : ∀ i, L i →+* T)
    (hl : ∀ i x, l i (algebraMap (A i) (L i) x) = algebraMap R T (g i x)) :
    ∀ x : T, ∃ i y, l i y = x := by
  intro x
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj q.primeCompl x
  obtain ⟨i, a', ha⟩ := hs a
  obtain ⟨j, s', hs'⟩ := hs s
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let a'' := f i k hik a'
  let s'' : (q.comap (g k)).primeCompl :=
    ⟨f j k hjk s', map_mem_primeCompl_comap (hg j k hjk) (by rw [hs']; exact s.property)⟩
  refine ⟨k, IsLocalization.mk' (L k) a'' s'', ?_⟩
  apply (IsLocalization.map_units T s).mul_left_cancel
  calc
    algebraMap R T (s : R) * l k (IsLocalization.mk' (L k) a'' s'') =
        l k (algebraMap (A k) (L k) s'' * IsLocalization.mk' (L k) a'' s'') := by
      rw [map_mul, hl]; congr 1; congr 1; exact ((hg j k hjk s').trans hs').symm
    _ = algebraMap R T a := by rw [IsLocalization.mk'_spec', hl, hg, ha]
    _ = algebraMap R T (s : R) * x := by simpa [mul_comm] using hx.symm

/-- Localizing a directed system of rings at the preimages of a prime `q` of its colimit `R`
gives a system whose colimit is `R_q`: an element dying in `R_q` dies at a later stage. -/
private theorem localization_eventually_zero
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {A : I → Type*} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A (fun i j h => ⇑(f i j h))]
    {R : Type*} [CommRing R] (g : ∀ i, A i →+* R)
    (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)
    (hs : ∀ x, ∃ i y, g i y = x)
    (hz : ∀ i x, g i x = 0 → ∃ (j : I) (h : i ≤ j), f i j h x = 0)
    (q : Ideal R) [q.IsPrime]
    (L : I → Type*) [∀ i, CommRing (L i)] [∀ i, Algebra (A i) (L i)]
    [∀ i, IsLocalization (q.comap (g i)).primeCompl (L i)]
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization q.primeCompl T]
    (l : ∀ i, L i →+* T)
    (hl : ∀ i x, l i (algebraMap (A i) (L i) x) = algebraMap R T (g i x))
    (lf : ∀ i j, i ≤ j → L i →+* L j)
    (hlf : ∀ i j (h : i ≤ j) x,
      lf i j h (algebraMap (A i) (L i) x) = algebraMap (A j) (L j) (f i j h x)) :
    ∀ i x, l i x = 0 → ∃ (j : I) (h : i ≤ j), lf i j h x = 0 := by
  intro i x hx
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj (q.comap (g i)).primeCompl x
  have ha0 : algebraMap R T (g i a) = 0 := by
    rw [← hl, ← ha, map_mul, hx, zero_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl T _).mp ha0
  obtain ⟨j, b, hb⟩ := hs t
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hzero : g k (f j k hjk b * f i k hik a) = 0 := by
    rw [map_mul, hg, hg, hb]
    exact ht
  obtain ⟨m, hkm, hm⟩ := hz k _ hzero
  let him := hik.trans hkm
  let hjm := hjk.trans hkm
  have hmul : f j m hjm b * f i m him a = 0 := by
    simpa only [map_mul, DirectedSystem.map_map' f] using hm
  have hbq : f j m hjm b ∈ (q.comap (g m)).primeCompl :=
    map_mem_primeCompl_comap (hg j m hjm) (by rw [hb]; exact t.property)
  have ham : algebraMap (A m) (L m) (f i m him a) = 0 :=
    (IsLocalization.map_eq_zero_iff (q.comap (g m)).primeCompl (L m) _).mpr
      ⟨⟨_, hbq⟩, hmul⟩
  have hsq : f i m him s ∈ (q.comap (g m)).primeCompl :=
    map_mem_primeCompl_comap (hg i m him) s.property
  refine ⟨m, him, (IsLocalization.map_units (L m) ⟨_, hsq⟩).mul_left_cancel ?_⟩
  rw [mul_zero, ← hlf, ← map_mul, mul_comm, ha, hlf, ham]

section LocalizedDiagram

variable {I : Type u} [Preorder I] {R : Type u} [CommRing R]
  (F : I ⥤ CommRingCat.{u}) (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of R))
  (q : Ideal R) [q.IsPrime]

/-- The localization of a diagram of rings `F` with a cocone to `R` at the preimages of a prime
`q` of `R`. -/
private noncomputable abbrev localizationDiagram : I ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Localization.AtPrime (q.comap (ρ.app i).hom))
  map {i j} h := CommRingCat.ofHom (Localization.localRingHom
    (q.comap (ρ.app i).hom) (q.comap (ρ.app j).hom) (F.map h).hom
    (comap_comap_eq_comap_of_comp_eq (ρ.naturality h) q).symm)
  map_id i := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (q.comap (ρ.app i).hom).primeCompl
    ext a
    simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Localization.localRingHom_to_map, F.map_id]
    rfl
  map_comp {i j k} h h' := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (q.comap (ρ.app i).hom).primeCompl
    ext a
    simp [Localization.localRingHom_to_map, F.map_comp]

/-- The transition maps of `localizationDiagram` extend those of `F`. -/
private theorem localizationDiagram_map_algebraMap {i j : I} (h : i ⟶ j) (x : F.obj i) :
    (localizationDiagram F ρ q).map h (algebraMap (F.obj i)
      (Localization.AtPrime (q.comap (ρ.app i).hom)) x) =
        algebraMap (F.obj j) (Localization.AtPrime (q.comap (ρ.app j).hom)) (F.map h x) := by
  dsimp only [localizationDiagram]
  exact Localization.localRingHom_to_map _ _ _
    (comap_comap_eq_comap_of_comp_eq (ρ.naturality h) q).symm x

/-- The cocone from `localizationDiagram` to `R_q`. -/
private noncomputable abbrev localizationCocone : Cocone (localizationDiagram F ρ q) where
  pt := CommRingCat.of (Localization.AtPrime q)
  ι := {
    app i := CommRingCat.ofHom (Localization.localRingHom _ q (ρ.app i).hom rfl)
    naturality {i j} h := by
      apply CommRingCat.hom_ext
      dsimp only [localizationDiagram, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        Functor.const_obj_map]
      rw [← Localization.localRingHom_comp]
      have he : (ρ.app j).hom.comp (F.map h).hom = (ρ.app i).hom :=
        congrArg CommRingCat.Hom.hom (ρ.naturality h)
      simp only [he]
      rfl }

/-- The legs of `localizationCocone` extend those of the given cocone. -/
private theorem localizationCocone_algebraMap (i : I) (x : F.obj i) :
    (localizationCocone F ρ q).ι.app i (algebraMap (F.obj i)
      (Localization.AtPrime (q.comap (ρ.app i).hom)) x) =
        algebraMap R (Localization.AtPrime q) (ρ.app i x) :=
  Localization.localRingHom_to_map _ _ _ rfl _

/-- Localization commutes with directed colimits: `localizationCocone` is a colimit. -/
private noncomputable def localizationIsColimit [Nonempty I] [IsDirectedOrder I]
    (hρ : IsColimit (Cocone.mk (CommRingCat.of R) ρ)) :
    IsColimit (localizationCocone F ρ q) := by
  let f := fun i j (h : i ≤ j) => (F.map (homOfLE h)).hom
  let g := fun i => (ρ.app i).hom
  have hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x := by
    intro i j h x
    exact ConcreteCategory.congr_hom (ρ.naturality (homOfLE h)) x
  have hs : ∀ x, ∃ i y, g i y = x := Concrete.isColimit_exists_rep F hρ
  have hz : ∀ i x, g i x = 0 → ∃ (j : I) (h : i ≤ j), f i j h x = 0 :=
    exists_map_eq_zero_of_isColimit F hρ
  have : DirectedSystem (fun i => ↑(F.obj i)) (fun i j h => ⇑(f i j h)) :=
    directedSystem_map_homOfLE F
  apply Stacks.SpreadingOut.LocalModuleSystem.isColimitCommRingCatOf
  · exact localization_jointly_surjective f g hg hs q
      (fun i => Localization.AtPrime (q.comap (ρ.app i).hom)) (Localization.AtPrime q)
      (fun i => ((localizationCocone F ρ q).ι.app i).hom)
      (localizationCocone_algebraMap F ρ q)
  · intro i x hx
    obtain ⟨j, h, hj⟩ := localization_eventually_zero f g hg hs hz q
      (fun i => Localization.AtPrime (q.comap (ρ.app i).hom)) (Localization.AtPrime q)
      (fun i => ((localizationCocone F ρ q).ι.app i).hom)
      (localizationCocone_algebraMap F ρ q)
      (fun i j h => ((localizationDiagram F ρ q).map (homOfLE h)).hom)
      (fun i j h x => localizationDiagram_map_algebraMap F ρ q (homOfLE h) x) i x hx
    exact ⟨j, homOfLE h, hj⟩

end LocalizedDiagram

/-- A local ring `T` which is the localization of `R` at a prime and receives a map from an
`R`-algebra `S` is the localization of `S` at the preimage of its maximal ideal, provided ring maps
out of `S` are determined by their restriction to `R`. -/
private theorem isLocalization_atPrime_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [IsLocalRing T]
    [Algebra R T] [Algebra S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization p.primeCompl T] (g : R →+* S)
    (hg : (algebraMap S T).comp g = algebraMap R T)
    (he : Function.Injective (fun f : S →+*
        Localization.AtPrime ((IsLocalRing.maximalIdeal T).comap (algebraMap S T)) =>
      f.comp g)) :
    IsLocalization ((IsLocalRing.maximalIdeal T).comap (algebraMap S T)).primeCompl T := by
  let q := (IsLocalRing.maximalIdeal T).comap (algebraMap S T)
  let L := Localization.AtPrime q
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap S T s) :=
    fun s => IsLocalRing.notMem_maximalIdeal.mp s.property
  let u : L →+* T := IsLocalization.lift hu
  have hv : ∀ r : p.primeCompl, IsUnit (((algebraMap S L).comp g) r) := by
    intro r
    rw [RingHom.comp_apply]
    refine IsLocalization.map_units L (⟨g r, ?_⟩ : q.primeCompl)
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, ← RingHom.comp_apply, hg]
    exact IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units T r)
  let v : T →+* L := IsLocalization.lift hv
  have hu_map (s : S) : u (algebraMap S L s) = algebraMap S T s :=
    IsLocalization.lift_eq _ _
  have hv_map (r : R) : v (algebraMap R T r) = algebraMap S L (g r) :=
    IsLocalization.lift_eq _ _
  have huv : u.comp v = RingHom.id T := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, hv_map, hu_map, RingHom.id_comp]
    exact DFunLike.congr_fun hg r
  have hvu : v.comp u = RingHom.id L := by
    apply IsLocalization.ringHom_ext q.primeCompl
    have h : v.comp (algebraMap S T) = algebraMap S L := by
      apply he
      ext r
      dsimp only
      rw [RingHom.comp_apply, RingHom.comp_apply,
        show algebraMap S T (g r) = algebraMap R T r from DFunLike.congr_fun hg r, hv_map,
        RingHom.comp_apply]
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply, hu_map, RingHom.id_comp]
    exact DFunLike.congr_fun h s
  let e : L ≃ₐ[S] T := {
    __ := u
    invFun := v
    left_inv := fun x => DFunLike.congr_fun hvu x
    right_inv := fun x => DFunLike.congr_fun huv x
    commutes' := hu_map }
  exact IsLocalization.isLocalization_of_algEquiv q.primeCompl e

/-- A tensor product of localizations maps to a localization of the tensor product, which is then
the localization at the preimage of its maximal ideal. -/
private theorem isLocalization_atPrime_tensorProduct
    {C A B C' A' B' D T : Type*}
    [CommRing C] [CommRing A] [CommRing B] [CommRing C'] [CommRing A'] [CommRing B']
    [CommRing D] [CommRing T] [IsLocalRing T]
    [Algebra C A] [Algebra C B] [Algebra C' A'] [Algebra C' B']
    [Algebra A A'] [Algebra B B']
    (U : Submonoid A) (V : Submonoid B) [IsLocalization U A'] [IsLocalization V B']
    (c : C →+* C')
    (hA : (algebraMap A A').comp (algebraMap C A) = (algebraMap C' A').comp c)
    (hB : (algebraMap B B').comp (algebraMap C B) = (algebraMap C' B').comp c)
    (e : D ≃+* A ⊗[C] B)
    [Algebra D T] (p : Ideal D) [p.IsPrime] [IsLocalization p.primeCompl T]
    [Algebra (A' ⊗[C'] B') T]
    (h : (algebraMap (A' ⊗[C'] B') T).comp
        ((Algebra.TensorProduct.mapRingHom c (algebraMap A A') (algebraMap B B') hA hB).comp
          e.toRingHom) = algebraMap D T) :
    IsLocalization
      ((IsLocalRing.maximalIdeal T).comap (algebraMap (A' ⊗[C'] B') T)).primeCompl T := by
  apply isLocalization_atPrime_of_comp p _ h
  intro f₁ f₂ hf
  apply Algebra.TensorProduct.ringHom_ext
  · apply IsLocalization.ringHom_ext U
    ext a
    have hh := DFunLike.congr_fun hf (e.symm (a ⊗ₜ[C] 1))
    simp only [RingHom.comp_apply] at hh
    rw [show e.toRingHom (e.symm (a ⊗ₜ[C] 1)) = a ⊗ₜ[C] 1 from e.apply_symm_apply _] at hh
    simpa only [RingHom.comp_apply,
      Algebra.TensorProduct.mapRingHom_tmul, map_one,
      Algebra.TensorProduct.includeLeftRingHom_apply] using hh
  · apply IsLocalization.ringHom_ext V
    ext b
    have hh := DFunLike.congr_fun hf (e.symm (1 ⊗ₜ[C] b))
    simp only [RingHom.comp_apply] at hh
    rw [show e.toRingHom (e.symm (1 ⊗ₜ[C] b)) = 1 ⊗ₜ[C] b from e.apply_symm_apply _] at hh
    simpa only [RingHom.comp_apply, Algebra.TensorProduct.mapRingHom_tmul, map_one,
      Algebra.TensorProduct.includeRight_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using hh

section TensorDiagram

variable {I : Type u} [Preorder I] {A : Type u} [CommRing A]
  (F : I ⥤ CommRingCat.{u}) [∀ i, Algebra A (F.obj i)]
  (hF : ∀ {i j} (h : i ⟶ j) a,
    (F.map h).hom (algebraMap A (F.obj i) a) = algebraMap A (F.obj j) a)
  (P : Type u) [AddCommGroup P] [Module A P]

/-- A transition map of `F`, as an `A`-algebra map. -/
private def diagramAlgHom {i j : I} (h : i ⟶ j) : F.obj i →ₐ[A] F.obj j :=
  { (F.map h).hom with commutes' := hF h }

omit [Module A P] in
/-- `diagramAlgHom` is the transition map of `F`. -/
private theorem diagramAlgHom_apply {i j : I} (h : i ⟶ j) (x : F.obj i) :
    diagramAlgHom F hF h x = F.map h x := rfl

/-- The diagram of abelian groups `F i ⊗[A] P`. -/
private abbrev tensorModuleDiagram : I ⥤ AddCommGrpCat.{u} where
  obj i := AddCommGrpCat.of (F.obj i ⊗[A] P)
  map h := AddCommGrpCat.ofHom
    ((diagramAlgHom F hF h).toLinearMap.rTensor P).toAddMonoidHom
  map_id i := by
    apply AddCommGrpCat.hom_ext
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p => simp [diagramAlgHom_apply]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_comp {i j k} h h' := by
    apply AddCommGrpCat.hom_ext
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p => simp [diagramAlgHom_apply]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable {T : Type u} [CommRing T] [Algebra A T]
  (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of T))
  (hρA : ∀ i a, (ρ.app i).hom (algebraMap A (F.obj i) a) = algebraMap A T a)

/-- The cocone from `tensorModuleDiagram` to `T ⊗[A] P`. -/
private abbrev tensorModuleCocone : Cocone (tensorModuleDiagram F hF P) where
  pt := AddCommGrpCat.of (T ⊗[A] P)
  ι := {
    app i := AddCommGrpCat.ofHom
      (({ (ρ.app i).hom with commutes' := hρA i } : F.obj i →ₐ[A] T).toLinearMap.rTensor P
        ).toAddMonoidHom
    naturality {i j} h := by
      dsimp only [tensorModuleDiagram]
      apply AddCommGrpCat.hom_ext
      ext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x p =>
        simp [diagramAlgHom_apply]
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy }

/-- Tensor products commute with directed colimits: `tensorModuleCocone` is a colimit. -/
private noncomputable def tensorModuleIsColimit [Nonempty I] [IsDirectedOrder I]
    (hρ : IsColimit (Cocone.mk (CommRingCat.of T) ρ)) :
    IsColimit (tensorModuleCocone F hF P ρ hρA) := by
  letI (i : I) : Algebra (F.obj i) T := (ρ.app i).hom.toAlgebra
  have (i : I) : IsScalarTower A (F.obj i) T :=
    IsScalarTower.of_algebraMap_eq fun a => (hρA i a).symm
  let f := fun i j (h : i ≤ j) => diagramAlgHom F hF (homOfLE h)
  have : DirectedSystem (fun i => ↑(F.obj i)) (fun i j h => ⇑(f i j h)) :=
    directedSystem_map_homOfLE F
  have hg : ∀ i j (h : i ≤ j) x,
      algebraMap (F.obj j) T (f i j h x) = algebraMap (F.obj i) T x := by
    intro i j h x
    exact ConcreteCategory.congr_hom (ρ.naturality (homOfLE h)) x
  have hs : ∀ x : T, ∃ i y, algebraMap (F.obj i) T y = x :=
    Concrete.isColimit_exists_rep F hρ
  have hz : ∀ i x, algebraMap (F.obj i) T x = 0 →
      ∃ (j : I) (h : i ≤ j), f i j h x = 0 :=
    exists_map_eq_zero_of_isColimit F hρ
  have hc := Stacks.ColimitPresentation.FPModules.isModuleColimit f hg hs hz P
  have hcan (i : I) (x : F.obj i ⊗[A] P) :
      Stacks.FinitePresentation.ColimitDescent.canonMod (fun j => IsScalarTower.toAlgHom A (F.obj j)
        T) P i x =
        (tensorModuleCocone F hF P ρ hρA).ι.app i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  have htrans {i j : I} (h : i ≤ j) (x : F.obj i ⊗[A] P) :
      Stacks.FinitePresentation.ColimitDescent.transMod (fun i j h => f i j h) P h x =
        (tensorModuleDiagram F hF P).map (homOfLE h) x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  apply Stacks.SpreadingOut.LocalModuleSystem.isColimitAddCommGrpCatOf
  · intro x
    obtain ⟨i, y, hy⟩ := hc.jointly_surjective x
    exact ⟨i, y, (hcan i y).symm.trans hy⟩
  · intro i x hx
    obtain ⟨j, hij, hj⟩ := hc.exists_eq_of_canonMod_eq i x 0 (by
      rw [hcan, hcan, map_zero]; exact hx)
    refine ⟨j, homOfLE hij, ?_⟩
    rw [← htrans, hj, map_zero]

end TensorDiagram

/-- A map of diagrams, localized at the preimages of a prime and of its preimage. -/
private noncomputable abbrev localizationNatTrans
    {I : Type u} [Preorder I] {R S : Type u} [CommRing R] [CommRing S]
    {F G : I ⥤ CommRingCat.{u}}
    (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of R))
    (σ : G ⟶ (Functor.const I).obj (CommRingCat.of S))
    (φ : F ⟶ G) (f : R →+* S)
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom f)
    (q : Ideal S) [q.IsPrime] :
    localizationDiagram F ρ (q.comap f) ⟶ localizationDiagram G σ q where
  app i := CommRingCat.ofHom (Localization.localRingHom _ _ (φ.app i).hom
    (comap_comap_eq_of_comp_eq (hφ i) q))
  naturality {i j} h := by
    apply CommRingCat.hom_ext
    dsimp only [localizationDiagram, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [← Localization.localRingHom_comp, ← Localization.localRingHom_comp]
    have he := congrArg CommRingCat.Hom.hom (φ.naturality h)
    dsimp only [CommRingCat.hom_comp] at he
    congr 1

/-- Essential finite type over `ℤ` does not depend on the choice of `ℤ`-algebra structure. -/
private theorem essFiniteType_int_of_algebra {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.EssFiniteType ℤ X _ _ i₁) : @Algebra.EssFiniteType ℤ X _ _ i₂ :=
  Subsingleton.elim i₁ i₂ ▸ h

/-- The local ring map induced by an essentially finite type ring map is essentially of finite
type. -/
private theorem essFiniteType_localRingHom
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.EssFiniteType) (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hpq : p = q.comap f) :
    (Localization.localRingHom p q f hpq).EssFiniteType := by
  apply RingHom.EssFiniteType.of_comp (algebraMap A (Localization.AtPrime p))
  have he : (Localization.localRingHom p q f hpq).comp
      (algebraMap A (Localization.AtPrime p)) = (algebraMap B (Localization.AtPrime q)).comp f := by
    ext a
    exact Localization.localRingHom_to_map _ _ _ hpq _
  rw [he]
  exact hf.comp (RingHom.essFiniteType_algebraMap.mpr inferInstance)

section TensorCompatibility

variable {I : Type u} [Preorder I] {A : Type u} [CommRing A]
  (F : I ⥤ CommRingCat.{u}) [∀ i, Algebra A (F.obj i)]
  (hF : ∀ {i j} (h : i ⟶ j) a,
    (F.map h).hom (algebraMap A (F.obj i) a) = algebraMap A (F.obj j) a)
  (P : Type u) [AddCommGroup P] [Module A P]

/-- The transition maps of `tensorModuleDiagram` are semilinear over those of `F`. -/
private theorem tensorModuleDiagram_map_smul {i j : I} (h : i ⟶ j)
    (a : F.obj i) (x : (tensorModuleDiagram F hF P).obj i) :
    (tensorModuleDiagram F hF P).map h (a • x) =
      F.map h a • (tensorModuleDiagram F hF P).map h x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b p => simp [TensorProduct.smul_tmul', diagramAlgHom_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The legs of `tensorModuleCocone` are semilinear over those of the ring cocone. -/
private theorem tensorModuleCocone_smul
    {T : Type u} [CommRing T] [Algebra A T]
    (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of T))
    (hρA : ∀ i a, (ρ.app i).hom (algebraMap A (F.obj i) a) = algebraMap A T a)
    (i : I) (a : F.obj i) (x : (tensorModuleDiagram F hF P).obj i) :
    (tensorModuleCocone F hF P ρ hρA).ι.app i (a • x) =
      HSMul.hSMul (α := T) (β := T ⊗[A] P)
        (Stacks.SpreadingOut.LocalModuleSystem.legHom ρ i a) ((tensorModuleCocone F hF P ρ
            hρA).ι.app i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b p => simp [TensorProduct.smul_tmul', Stacks.SpreadingOut.LocalModuleSystem.legHom]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

end TensorCompatibility

/-- Localizing a pushout square at compatible primes gives a square whose corner is a
localization of the tensor product at a prime. -/
private theorem exists_isLocalization_tensorProduct_of_isPushout
    {A B C D A' B' C' D' : Type*}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [CommRing A'] [CommRing B'] [CommRing C'] [CommRing D'] [IsLocalRing D']
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D] [Algebra.IsPushout A B C D]
    [Algebra A' B'] [Algebra A' C'] [Algebra A' D'] [Algebra B' D'] [Algebra C' D']
    [IsScalarTower A' B' D'] [IsScalarTower A' C' D']
    [Algebra B B'] [Algebra C C'] [Algebra D D']
    (U : Submonoid B) (V : Submonoid C) [IsLocalization U B'] [IsLocalization V C']
    (q : Ideal D) [q.IsPrime] [IsLocalization q.primeCompl D']
    (a : A →+* A')
    (hB : (algebraMap B B').comp (algebraMap A B) = (algebraMap A' B').comp a)
    (hC : (algebraMap C C').comp (algebraMap A C) = (algebraMap A' C').comp a)
    (hBD : (algebraMap B' D').comp (algebraMap B B') =
      (algebraMap D D').comp (algebraMap B D))
    (hCD : (algebraMap C' D').comp (algebraMap C C') =
      (algebraMap D D').comp (algebraMap C D)) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A' B' D')
      (IsScalarTower.toAlgHom A' C' D')).toRingHom.toAlgebra
    ∃ (p : Ideal (B' ⊗[A'] C')) (_ : p.IsPrime), IsLocalization p.primeCompl D' := by
  let := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A' B' D')
    (IsScalarTower.toAlgHom A' C' D')).toRingHom.toAlgebra
  refine ⟨(IsLocalRing.maximalIdeal D').comap (algebraMap (B' ⊗[A'] C') D'),
    inferInstance, ?_⟩
  apply isLocalization_atPrime_tensorProduct U V a hB hC
    (Algebra.IsPushout.equiv A B C D).symm.toRingEquiv q
  ext d
  obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv A B C D).surjective d
  simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgEquiv.symm_toRingEquiv,
    RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, RingEquiv.coe_mk,
    EquivLike.coe_coe, Function.comp_apply, AlgEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b c =>
    rw [Algebra.TensorProduct.mapRingHom_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.IsPushout.equiv_tmul, map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hBD b) (DFunLike.congr_fun hCD c)

/-- The localized systems inherit the pushout condition: if the square of `φ` at `h` is a pushout,
the corresponding localized ring at `j` is a localization of the pushout of the localized square
at a prime. -/
private theorem localizationNatTrans_isLocalization_pushout
    {I : Type u} [Preorder I] {R S : Type u} [CommRing R] [CommRing S]
    {F G : I ⥤ CommRingCat.{u}}
    (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of R))
    (σ : G ⟶ (Functor.const I).obj (CommRingCat.of S))
    (φ : F ⟶ G) (f : R →+* S)
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom f)
    (q : Ideal S) [q.IsPrime] {i j : I} (h : i ⟶ j)
    (hc : IsPushout (φ.app i) (F.map h) (G.map h) (φ.app j)) :
    let locF := localizationDiagram F ρ (q.comap f)
    let locG := localizationDiagram G σ q
    let φL := localizationNatTrans ρ σ φ f hφ q
    letI := (pushout.desc (locG.map h) (φL.app j) (φL.naturality h).symm).hom.toAlgebra
    ∃ (p : Ideal ↑(pushout (φL.app i) (locF.map h))) (_ : p.IsPrime),
      IsLocalization p.primeCompl ↑(locG.obj j) := by
  let locF := localizationDiagram F ρ (q.comap f)
  let locG := localizationDiagram G σ q
  let φL := localizationNatTrans ρ σ φ f hφ q
  let : Algebra (F.obj i) (G.obj i) := (φ.app i).hom.toAlgebra
  let : Algebra (F.obj i) (F.obj j) := (F.map h).hom.toAlgebra
  let : Algebra (G.obj i) (G.obj j) := (G.map h).hom.toAlgebra
  let : Algebra (F.obj j) (G.obj j) := (φ.app j).hom.toAlgebra
  let : Algebra (F.obj i) (G.obj j) := ((G.map h).hom.comp (φ.app i).hom).toAlgebra
  have : IsScalarTower (F.obj i) (G.obj i) (G.obj j) :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (F.obj i) (F.obj j) (G.obj j) :=
    .of_algebraMap_eq fun x => (ConcreteCategory.congr_hom (φ.naturality h) x).symm
  have : Algebra.IsPushout (F.obj i) (G.obj i) (F.obj j) (G.obj j) :=
    CommRingCat.isPushout_iff_isPushout.mp hc
  let : Algebra (locF.obj i) (locG.obj i) := (φL.app i).hom.toAlgebra
  let : Algebra (locF.obj i) (locF.obj j) := (locF.map h).hom.toAlgebra
  let : Algebra (locG.obj i) (locG.obj j) := (locG.map h).hom.toAlgebra
  let : Algebra (locF.obj j) (locG.obj j) := (φL.app j).hom.toAlgebra
  let : Algebra (locF.obj i) (locG.obj j) :=
    ((locG.map h).hom.comp (φL.app i).hom).toAlgebra
  have : IsScalarTower (locF.obj i) (locG.obj i) (locG.obj j) :=
    .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (locF.obj i) (locF.obj j) (locG.obj j) :=
    .of_algebraMap_eq fun x => (ConcreteCategory.congr_hom (φL.naturality h) x).symm
  apply
    Stacks.SpreadingOut.LocalModuleSystem.exists_isLocalization_primeCompl_pushout_of_tensorProduct
    (φL.naturality h).symm
  apply exists_isLocalization_tensorProduct_of_isPushout
    (A := F.obj i) (B := G.obj i) (C := F.obj j) (D := G.obj j)
    (A' := locF.obj i) (B' := locG.obj i) (C' := locF.obj j) (D' := locG.obj j)
    (q.comap (σ.app i).hom).primeCompl
    ((q.comap f).comap (ρ.app j).hom).primeCompl (q.comap (σ.app j).hom)
    (algebraMap (F.obj i) (locF.obj i))
  · ext x
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact (Localization.localRingHom_to_map _ _ _ (comap_comap_eq_of_comp_eq (hφ i) q) x).symm
  · ext x
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact (localizationDiagram_map_algebraMap F ρ (q.comap f) h x).symm
  · ext x
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact localizationDiagram_map_algebraMap G σ q h x
  · ext x
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    exact Localization.localRingHom_to_map _ _ _ (comap_comap_eq_of_comp_eq (hφ j) q) x

/-- **Descent of flatness at a prime along a directed system of finite type stages.** If
`S_q ⊗_C P` is flat over `R`, then `(S_i)_{q_i} ⊗_C P` is flat over `R_i` for some stage `i`. -/
private theorem exists_flat_localized_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {R S C P : Type u} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra C S] [AddCommGroup P] [Module C P] [Module.Finite C P]
    {F G : I ⥤ CommRingCat.{u}} [∀ i, Algebra C (G.obj i)]
    (hG : ∀ {i j} (h : i ⟶ j) c,
      (G.map h).hom (algebraMap C (G.obj i) c) = algebraMap C (G.obj j) c)
    (ρ : F ⟶ (Functor.const I).obj (CommRingCat.of R))
    (σ : G ⟶ (Functor.const I).obj (CommRingCat.of S))
    (hσC : ∀ i c, (σ.app i).hom (algebraMap C (G.obj i) c) = algebraMap C S c)
    (φ : F ⟶ G)
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hρ : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hσ : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    (hFft : ∀ i, Algebra.FiniteType ℤ (F.obj i))
    (hφft : ∀ i, (φ.app i).hom.FiniteType)
    (hc : ∀ {i j} (h : i ⟶ j), IsPushout (φ.app i) (F.map h) (G.map h) (φ.app j))
    (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (Localization.AtPrime q ⊗[C] P)) :
    ∃ i,
      letI : Algebra (F.obj i) (G.obj i) := (φ.app i).hom.toAlgebra
      Module.Flat (F.obj i) (Localization.AtPrime (q.comap (σ.app i).hom) ⊗[C] P) := by
  let p := q.comap (algebraMap R S)
  let locF := localizationDiagram F ρ p
  let locG := localizationDiagram G σ q
  let locφ := localizationNatTrans ρ σ φ (algebraMap R S) hφ q
  let locρ := (localizationCocone F ρ p).ι
  let locσ := (localizationCocone G σ q).ι
  have hlocG : ∀ {i j} (h : i ⟶ j) c,
      (locG.map h).hom (algebraMap C (locG.obj i) c) = algebraMap C (locG.obj j) c := by
    intro i j h c
    rw [IsScalarTower.algebraMap_apply C (G.obj i) (locG.obj i),
      IsScalarTower.algebraMap_apply C (G.obj j) (locG.obj j),
      localizationDiagram_map_algebraMap, hG]
  have hlocσC : ∀ i c, (locσ.app i).hom (algebraMap C (locG.obj i) c) =
      algebraMap C (Localization.AtPrime q) c := by
    intro i c
    rw [IsScalarTower.algebraMap_apply C (G.obj i) (locG.obj i),
      IsScalarTower.algebraMap_apply C S (Localization.AtPrime q),
      localizationCocone_algebraMap, hσC]
  let N := tensorModuleDiagram locG hlocG P
  let ν := (tensorModuleCocone locG hlocG P locσ hlocσC).ι
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) rfl).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun r => (Localization.localRingHom_to_map p q
      (algebraMap R S) rfl r).symm
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q ⊗[C] P) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr hq
  have hlocφ : ∀ i, locφ.app i ≫ locσ.app i =
      locρ.app i ≫ CommRingCat.ofHom
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    intro i
    apply CommRingCat.hom_ext
    dsimp only [locφ, locσ, locρ, localizationNatTrans, localizationCocone,
      CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.algebraMap_toAlgebra]
    rw [← Localization.localRingHom_comp, ← Localization.localRingHom_comp]
    congr 1
    exact congrArg CommRingCat.Hom.hom (hφ i)
  have hlocφft : ∀ i, (locφ.app i).hom.EssFiniteType := by
    intro i
    have hi : (φ.app i).hom.EssFiniteType := by
      let := (φ.app i).hom.toAlgebra
      have : Algebra.FiniteType (F.obj i) (G.obj i) := hφft i
      exact RingHom.essFiniteType_algebraMap.mpr inferInstance
    exact essFiniteType_localRingHom _ hi _ _ (comap_comap_eq_of_comp_eq (hφ i) q)
  obtain ⟨j, _, hj⟩ := Module.Flat.exists_ge_flat_of_isColimit
    (R := Localization.AtPrime p) (S := Localization.AtPrime q)
    (M := Localization.AtPrime q ⊗[C] P) (A := locF) (B := locG) (φ := locφ) (N := N)
    (fun i => inferInstance) (fun {i j} h => tensorModuleDiagram_map_smul locG hlocG P h)
    (localizationIsColimit F ρ p hρ) (localizationIsColimit G σ q hσ)
    (tensorModuleIsColimit locG hlocG P locσ hlocσC (localizationIsColimit G σ q hσ))
    hlocφ (tensorModuleCocone_smul locG hlocG P locσ hlocσC)
    (fun i => inferInstance) (fun i => inferInstance)
    (fun i => by dsimp [locφ, localizationNatTrans]; infer_instance)
    (fun {i j} h => by dsimp [locF, localizationDiagram]; infer_instance)
    (fun i => by
      have := hFft i
      exact essFiniteType_int_of_algebra _ _ (inferInstance :
        Algebra.EssFiniteType ℤ (Localization.AtPrime (p.comap (ρ.app i).hom)))) hlocφft
    (fun i => inferInstance)
    (fun {i j} h =>
      localizationNatTrans_isLocalization_pushout ρ σ φ (algebraMap R S) hφ q h (hc h))
    (fun {i j} h => by
      let : Algebra (locG.obj i) (locG.obj j) := (locG.map h).hom.toAlgebra
      have : IsScalarTower C (locG.obj i) (locG.obj j) :=
        .of_algebraMap_eq fun c => (hlocG h c).symm
      refine @IsBaseChange.of_equiv _ _ _ _ _ _ _ _ _ _ _ _
        (.of_algebraMap_smul fun _ _ => rfl) _
        (TensorProduct.AlgebraTensorModule.cancelBaseChange C (locG.obj i) (locG.obj j)
          (locG.obj j) P) fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, N, diagramAlgHom_apply]
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy])
    (Classical.arbitrary I)
  refine ⟨j, ?_⟩
  let : Algebra (F.obj j) (G.obj j) := (φ.app j).hom.toAlgebra
  let : Algebra (locF.obj j) (locG.obj j) := (locφ.app j).hom.toAlgebra
  have : IsScalarTower (F.obj j) (locF.obj j) (locG.obj j) :=
    .of_algebraMap_eq fun a => (Localization.localRingHom_to_map _ _ (φ.app j).hom
      (comap_comap_eq_of_comp_eq (hφ j) q) a).symm
  have : Module.Flat (locF.obj j) (locG.obj j ⊗[C] P) := hj
  exact Module.Flat.trans (F.obj j) (locF.obj j) (locG.obj j ⊗[C] P)

/-- **Flatness at a prime ascends along base change.** If `S = R ⊗_A B`, `q` is a prime of `S`
and `B_{q ∩ B} ⊗_C P` is flat over `A`, then `S_q ⊗_C P` is flat over `R`. -/
public theorem _root_.Module.flat_localization_atPrime_tensor_of_isPushout
    {A R B S C P : Type*} [CommRing A] [CommRing R] [CommRing B]
    [CommRing S] [CommRing C] [AddCommGroup P] [Module C P]
    [Algebra A R] [Algebra A B] [Algebra A S] [Algebra R S] [Algebra B S]
    [IsScalarTower A R S] [IsScalarTower A B S] [Algebra.IsPushout A R B S]
    [Algebra C B] [Algebra C S] [IsScalarTower C B S]
    (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat A (Localization.AtPrime (q.comap (algebraMap B S)) ⊗[C] P)) :
    Module.Flat R (Localization.AtPrime q ⊗[C] P) := by
  let p := q.comap (algebraMap B S)
  let L := Localization.AtPrime p
  let T := Localization.AtPrime q
  let : Algebra L T := (Localization.localRingHom p q (algebraMap B S) rfl).toAlgebra
  have : IsScalarTower B L T := .of_algebraMap_eq fun b =>
    (Localization.localRingHom_to_map p q (algebraMap B S) rfl b).symm
  have : IsScalarTower C L T := .to₁₃₄ C B L T
  have : Module.Flat R (S ⊗[B] (L ⊗[C] P)) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A R B S (L ⊗[C] P))
  have : Module.Flat R (T ⊗[S] (S ⊗[B] (L ⊗[C] P))) :=
    Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
      (TensorProduct.mk S T (S ⊗[B] (L ⊗[C] P)) 1)
  have : Module.Flat R (T ⊗[B] (L ⊗[C] P)) :=
    Module.Flat.of_linearEquiv
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        B S T T (L ⊗[C] P)).restrictScalars R).symm
  have := IsLocalization.tensorProduct_compatibleSMul p.primeCompl L T (L ⊗[C] P)
  exact Module.Flat.of_linearEquiv
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange C L T T P).symm.trans
      (TensorProduct.equivOfCompatibleSMul B L T T (L ⊗[C] P))).restrictScalars R)

/-- If `M = S ⊗_C P`, then `M_q` is flat over `R` if and only if `S_q ⊗_C P` is. -/
public theorem _root_.Module.flat_localizedModule_atPrime_iff_of_isBaseChange
    {R S C M P : Type*} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra C S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module C M] [IsScalarTower C S M]
    [AddCommGroup P] [Module C P] (f : P →ₗ[C] M) (hf : IsBaseChange S f)
    (q : Ideal S) [q.IsPrime] :
    Module.Flat R (LocalizedModule.AtPrime q M) ↔
      Module.Flat R (Localization.AtPrime q ⊗[C] P) := by
  let T := Localization.AtPrime q
  let e₁ := LocalizedModule.equivTensorProduct q.primeCompl M
  let e₂ := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) hf.equiv.symm
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange C S T T P
  exact Module.Flat.equiv_iff ((e₁.trans e₂ |>.trans e₃).restrictScalars R)

/-- Over a Noetherian stage `A` with `S = R ⊗_A B`, flatness of `B_{q ∩ B} ⊗_C P` over `A`
gives an open neighbourhood of `q` on which `S_{q'} ⊗_C P` is flat over `R`. -/
private theorem exists_open_flat_localized_tensor_of_isPushout
    {A R B S C P : Type*} [CommRing A] [CommRing R] [CommRing B]
    [CommRing S] [CommRing C] [AddCommGroup P] [Module C P] [Module.Finite C P]
    [Algebra A R] [Algebra A B] [Algebra A S] [Algebra R S] [Algebra B S]
    [IsScalarTower A R S] [IsScalarTower A B S] [Algebra.IsPushout A R B S]
    [Algebra C B] [Algebra C S] [IsScalarTower C B S]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (q : PrimeSpectrum S)
    (hq : Module.Flat A
      (Localization.AtPrime (q.asIdeal.comap (algebraMap B S)) ⊗[C] P)) :
    ∃ U : Set (PrimeSpectrum S), q ∈ U ∧ IsOpen U ∧
      ∀ q' ∈ U, Module.Flat R (Localization.AtPrime q'.asIdeal ⊗[C] P) := by
  let U : Set (PrimeSpectrum B) :=
    {p | Module.Flat A (LocalizedModule.AtPrime p.asIdeal (B ⊗[C] P))}
  have hU : IsOpen U := Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing
  have he (p : PrimeSpectrum B) :
      p ∈ U ↔ Module.Flat A (Localization.AtPrime p.asIdeal ⊗[C] P) :=
    Module.flat_localizedModule_atPrime_iff_of_isBaseChange (TensorProduct.mk C B P 1)
      (TensorProduct.isBaseChange C P B) p.asIdeal
  refine ⟨PrimeSpectrum.comap (algebraMap B S) ⁻¹' U,
    (he (PrimeSpectrum.comap (algebraMap B S) q)).mpr hq,
    hU.preimage (PrimeSpectrum.continuous_comap _), ?_⟩
  intro q' hq'
  exact Module.flat_localization_atPrime_tensor_of_isPushout (A := A) (B := B) q'.asIdeal
    ((he (PrimeSpectrum.comap (algebraMap B S) q')).mp hq')

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section RingDiagram
variable {I : Type u} [Preorder I]
  {A : I → Type u} [∀ i, CommRing (A i)]
  (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (fun i j h => ⇑(f i j h))]
  {B : Type u} [CommRing B] (g : ∀ i, A i →+* B)
  (hg : ∀ i j (h : i ≤ j) x, g j (f i j h x) = g i x)

/-- A directed system of rings, as a diagram in `CommRingCat`. -/
private abbrev ringDiagram : I ⥤ CommRingCat.{u} := Stacks.SpreadingOut.LocalModuleSystem.sysFunctor
    A f inferInstance

/-- A compatible family of ring maps out of a directed system, as a cocone. -/
private abbrev ringDiagramCocone : Cocone (ringDiagram f) where
  pt := CommRingCat.of B
  ι := { app i := CommRingCat.ofHom (g i)
         naturality i j h := by ext x; exact hg i j h.le x }

/-- The elementwise criterion for a cocone on a directed system of rings to be a colimit. -/
private noncomputable def ringDiagramIsColimit [Nonempty I] [IsDirectedOrder I]
    (hs : ∀ x, ∃ i y, g i y = x)
    (hz : ∀ i x, g i x = 0 → ∃ (j : I) (h : i ≤ j), f i j h x = 0) :
    IsColimit (ringDiagramCocone f g hg) := by
  apply Stacks.SpreadingOut.LocalModuleSystem.isColimitCommRingCatOf
  · exact hs
  · intro i x hx
    obtain ⟨j, h, hj⟩ := hz i x hx
    exact ⟨j, homOfLE h, hj⟩
end RingDiagram

end OpenFlatLocus

namespace Algebra.FiniteTypeSystem

open OpenFlatLocus

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (R₀ : Subring R) (S₀ P : Type u) [CommRing S₀] [Algebra R₀ S₀] [Algebra S₀ S]
  [IsScalarTower R₀ S₀ S] [AddCommGroup P] [Module S₀ P] [Module.Finite S₀ P]
  [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] [Algebra.IsPushout R₀ R S₀ S]

/-- The base rings `R_λ` as a diagram in `CommRingCat`. -/
private abbrev baseDiagram : Index R₀ ⥤ CommRingCat.{u} :=
  ringDiagram (fun _ _ h => (baseMap R₀ h).toRingHom)

/-- The rings `S_λ` as a diagram in `CommRingCat`. -/
private abbrev ringDiagram' : Index R₀ ⥤ CommRingCat.{u} :=
  ringDiagram (fun _ _ h => (ringMap R₀ S₀ h).toRingHom)

/-- The inclusions `R_λ → R`, as a cocone. -/
private abbrev baseCocone : baseDiagram R₀ ⟶ (Functor.const _).obj (CommRingCat.of R) :=
  (ringDiagramCocone _ (fun i => (baseToRing R₀ i).toRingHom) (fun _ _ _ _ => rfl)).ι

/-- The maps `S_λ → S`, as a cocone. -/
private abbrev ringCocone : ringDiagram' R₀ S₀ ⟶ (Functor.const _).obj (CommRingCat.of S) :=
  (ringDiagramCocone _ (fun i => (ringToRing R₀ S₀ (S := S) i).toRingHom)
    (fun _ _ h x => ring_cocone R₀ S₀ h x)).ι

/-- The structure maps `R_λ → S_λ`, as a natural transformation. -/
private abbrev structureMap : baseDiagram R₀ ⟶ ringDiagram' R₀ S₀ where
  app i := CommRingCat.ofHom (algebraMap (Base R₀ i) (Ring R₀ S₀ i))
  naturality {i j} h := by
    ext x
    exact (ringMap_algebraMap R₀ S₀ h.le x).symm

/-- **Descent of flatness at a prime to a finite stage.** If `M_q ≅ S_q ⊗_{S₀} P` is flat over
`R`, then `(S_λ)_{q_λ} ⊗_{S₀} P` is flat over `R_λ` for some `λ`, where `q_λ` is the prime of
`S_λ` under `q`. -/
public theorem exists_flat_localized_stage (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat R (Localization.AtPrime q ⊗[S₀] P)) :
    ∃ i, Module.Flat (Base R₀ i)
      (Localization.AtPrime (q.comap (algebraMap (Ring R₀ S₀ i) S)) ⊗[S₀] P) := by
  have hρcol : IsColimit (Cocone.mk (CommRingCat.of R) (baseCocone R₀)) :=
    ringDiagramIsColimit _ _ (fun _ _ _ _ => rfl) (base_jointly_surjective R₀)
      (fun i x hx => ⟨i, le_rfl, Subtype.ext hx⟩)
  have hσcol : IsColimit (Cocone.mk (CommRingCat.of S) (ringCocone R₀ S₀)) := by
    refine ringDiagramIsColimit _ _ (fun _ _ h x => ring_cocone R₀ S₀ h x)
      (ring_colimit R₀ S₀).1 fun i x hx => ?_
    obtain ⟨j, h, hj⟩ := (ring_colimit R₀ S₀ (S := S)).2 i x 0 (by simpa using hx)
    exact ⟨j, h, by simpa using hj⟩
  have hφ : ∀ i, (structureMap R₀ S₀).app i ≫ (ringCocone R₀ S₀).app i =
      (baseCocone R₀).app i ≫ CommRingCat.ofHom (algebraMap R S) := by
    intro i
    ext x
    exact (IsScalarTower.algebraMap_apply (Base R₀ i) (Ring R₀ S₀ i) S x).symm
  have hc : ∀ {i j} (h : i ⟶ j), CategoryTheory.IsPushout ((structureMap R₀ S₀).app i)
      ((baseDiagram R₀).map h) ((ringDiagram' R₀ S₀).map h) ((structureMap R₀ S₀).app j) := by
    intro i j h
    have : Fact (i ≤ j) := ⟨h.le⟩
    exact CommRingCat.isPushout_iff_isPushout.mpr (ringMap_isPushout R₀ S₀).symm
  obtain ⟨i, hi⟩ := OpenFlatLocus.exists_flat_localized_stage
    (fun h c => (ringMapOver R₀ S₀ h.le).commutes c)
    (baseCocone R₀) (ringCocone R₀ S₀)
    (fun i c => (IsScalarTower.algebraMap_apply S₀ (Ring R₀ S₀ i) S c).symm)
    (structureMap R₀ S₀) hφ hρcol hσcol (fun _ => inferInstance)
    (fun _ => RingHom.finiteType_algebraMap.mpr inferInstance) hc q hq
  refine ⟨i, ?_⟩
  have h1 : ((ringCocone R₀ S₀).app i).hom = algebraMap (Ring R₀ S₀ i) S := rfl
  have h2 : ((structureMap R₀ S₀).app i).hom.toAlgebra =
      (inferInstance : Algebra (Base R₀ i) (Ring R₀ S₀ i)) := toAlgebra_algebraMap
  rwa [h1, h2] at hi

omit [Module.Finite S₀ P] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀]
  [Algebra.IsPushout R₀ R S₀ S] in
/-- **Flatness at a prime propagates up the system.** If `(S_λ)_{p} ⊗_{S₀} P` is flat over
`R_λ`, where `p` is the prime of `S_λ` under a prime `p'` of `S_μ`, `λ ≤ μ`, then
`(S_μ)_{p'} ⊗_{S₀} P` is flat over `R_μ`. -/
public theorem flat_localized_of_le {i j : Index R₀} (h : i ≤ j) (p : Ideal (Ring R₀ S₀ j))
    [p.IsPrime] (hp : Module.Flat (Base R₀ i)
      (Localization.AtPrime (p.comap (ringMap R₀ S₀ h).toRingHom) ⊗[S₀] P)) :
    Module.Flat (Base R₀ j) (Localization.AtPrime p ⊗[S₀] P) := by
  have : Fact (i ≤ j) := ⟨h⟩
  have := ringMap_isPushout R₀ S₀ (i := i) (j := j)
  exact Module.flat_localization_atPrime_tensor_of_isPushout (A := Base R₀ i)
    (B := Ring R₀ S₀ i) p hp

omit [Module.Finite S₀ P] [Algebra.FiniteType ℤ R₀] [Algebra.FiniteType R₀ S₀] in
/-- Flatness at a stage gives flatness at the limit: if `(S_λ)_{q_λ} ⊗_{S₀} P` is flat over
`R_λ`, then `S_q ⊗_{S₀} P` is flat over `R`. -/
public theorem flat_localized_of_stage (i : Index R₀) (q : Ideal S) [q.IsPrime]
    (hq : Module.Flat (Base R₀ i)
      (Localization.AtPrime (q.comap (algebraMap (Ring R₀ S₀ i) S)) ⊗[S₀] P)) :
    Module.Flat R (Localization.AtPrime q ⊗[S₀] P) := by
  have := ringToRing_isPushout R₀ S₀ (S := S) i
  exact Module.flat_localization_atPrime_tensor_of_isPushout (A := Base R₀ i)
    (B := Ring R₀ S₀ i) q hq

end Algebra.FiniteTypeSystem

namespace OpenFlatLocus

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The relative flat locus is open when `R` and `S` lie in the same universe. -/
private theorem isOpen_setOf_flat_localizedModule_atPrime_sameUniverse
    {R S : Type u} {M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} := by
  obtain ⟨R₀, S₀, P, _, _, _, _, _, _, _, _, f, hR₀, hS₀, hP, hS, hf⟩ :=
    Algebra.exists_subring_finiteType_int_isPushout_isBaseChange (R := R) (S := S) M
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨i, hi⟩ := Algebra.FiniteTypeSystem.exists_flat_localized_stage R₀ S₀ P q.asIdeal
    ((Module.flat_localizedModule_atPrime_iff_of_isBaseChange (R := R) f hf q.asIdeal).mp hq)
  have : IsNoetherianRing (Algebra.FiniteTypeSystem.Base R₀ i) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  have := Algebra.FiniteTypeSystem.ringToRing_isPushout R₀ S₀ (S := S) i
  obtain ⟨U, hqU, hU, hUf⟩ := exists_open_flat_localized_tensor_of_isPushout
    (A := Algebra.FiniteTypeSystem.Base R₀ i) (R := R)
    (B := Algebra.FiniteTypeSystem.Ring R₀ S₀ i) (S := S) (C := S₀) (P := P) q hi
  exact ⟨U, fun q' hq' =>
    (Module.flat_localizedModule_atPrime_iff_of_isBaseChange (R := R) f hf q'.asIdeal).mpr
      (hUf q' hq'),
    hU, hqU⟩

end OpenFlatLocus

open OpenFlatLocus in
/-- For a finitely presented ring map `R → S` and a finitely presented
`S`-module `M`, the locus of primes `q` of `S` at which `M_q` is flat over `R` is open. -/
@[stacks 00RC,
  ega "IV 11.3.1" "U open, affine case",
  sga "1 IV 6.10" "affine case",
  ega "IV 11.1.6" "case C = B", ega "IV 11.3.3" "case C = B"]
public theorem Module.isOpen_setOf_flat_localizedModule_atPrime
    {R : Type*} {S : Type*} {M : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} := by
  have : Small.{u_1} S := Algebra.FiniteType.small (R := R)
  let e : Shrink.{u_1} S ≃ₐ[R] S := Shrink.algEquiv R S
  let : Algebra (Shrink.{u_1} S) S := e.toRingHom.toAlgebra
  have : IsScalarTower R (Shrink.{u_1} S) S := .of_algebraMap_eq fun r => (e.commutes r).symm
  let : Module (Shrink.{u_1} S) M := Module.compHom M e.toRingHom
  have : IsScalarTower (Shrink.{u_1} S) S M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (Shrink.{u_1} S) M := .to₁₂₄ R (Shrink.{u_1} S) S M
  have : Algebra.FinitePresentation R (Shrink.{u_1} S) :=
    Algebra.FinitePresentation.equiv e.symm
  let e' : Shrink.{u_1} S ≃ₐ[Shrink.{u_1} S] S :=
    { __ := e.toRingEquiv, commutes' := fun _ => rfl }
  have : Module.FinitePresentation (Shrink.{u_1} S) S :=
    Module.FinitePresentation.of_equiv e'.toLinearEquiv
  have : Module.FinitePresentation (Shrink.{u_1} S) M :=
    Module.FinitePresentation.trans (Shrink.{u_1} S) M S
  have h := isOpen_setOf_flat_localizedModule_atPrime_sameUniverse (R := R)
    (S := Shrink.{u_1} S) (M := M)
  convert h.preimage (PrimeSpectrum.continuous_comap e.toRingHom) using 1
  ext q
  exact (Module.flat_localizedModule_atPrime_comap_iff_of_surjective (R := R)
    e.surjective M q.asIdeal).symm

/-- **Openness of the relative flat locus gives a flat basic open neighbourhood.** If `M_q` is
flat over `R` at a prime `q` of `S`, then `M_g` is flat over `R` for some `g ∉ q`. -/
public theorem Module.exists_away_flat_of_flat_atPrime
    {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] [Module.FinitePresentation S N]
    (q : PrimeSpectrum S) (hq : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)) :
    ∃ g ∉ q.asIdeal, Module.Flat R (LocalizedModule.Away g N) := by
  have ho := Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := S) (M := N)
  change q ∈ {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)} at hq
  rw [PrimeSpectrum.eq_biUnion_of_isOpen ho] at hq
  obtain ⟨g, hg, hqg⟩ := Set.mem_iUnion₂.mp hq
  exact ⟨g, (PrimeSpectrum.mem_basicOpen g q).mp hqg,
    Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g hg⟩
