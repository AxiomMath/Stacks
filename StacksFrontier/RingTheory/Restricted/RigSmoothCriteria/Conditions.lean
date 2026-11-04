module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.IdealPower
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Restricted.RigSmooth
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Homology
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion

/-!
# Criteria for rig-smoothness: the conditions and Jacobian charts away from a prime

The cohomological, factorization and Jacobian-cover conditions of Stacks 0GAJ, the two-term
bounds of the completed naive cotangent complex, and the prime-local selection of a Jacobian
chart from a cotangent factorization.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Rig.AdicFiniteTypeAlgebra
open Rig.CompletedPolynomialPresentation
open Rig.CompletedNaiveCotangentComplex

universe u v

namespace Rig
open Stacks.Smooth.JacobianCriterion

attribute [local instance] HasDerivedCategory.standard

/- `P.extension.Ring` is definitionally `P.completedPolynomialRing`, but only after unfolding
`CompletedPolynomialPresentation.extension` and `Algebra.Extension.ofSurjective`, both
semireducible. The Jacobian-cover argument below moves between the two spellings -- lifts are
produced by `P.extension.σ` and then fed to `P.toAlgHom` -- so `kabstract` needs the
identification at `implicit` transparency, or else `rw` reports the goal ill-typed and fails to
find its pattern. Likewise `K.cochainComplex` has to be seen as the `HomologicalComplex.double`
it is. This is used instead of `backward.isDefEq.respectTransparency`. -/
attribute [local implicit_reducible] CompletedPolynomialPresentation.extension
  Algebra.Extension.ofSurjective CompletedNaiveCotangentComplex.cochainComplex

/-- The cochain complex of the completed naive cotangent complex is strictly supported between
degrees `-1` and `0`. -/
private lemma completedNaiveCotangent_isStrictlyGE_and_isStrictlyLE
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    ((completedNaiveCotangentComplex B P).cochainComplex.IsStrictlyGE (-1)) ∧
      (completedNaiveCotangentComplex B P).cochainComplex.IsStrictlyLE 0 := by
  have hzero : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((completedNaiveCotangentComplex B P).cochainComplex.X i) := fun i h₁ h₂ =>
    HomologicalComplex.isZero_double_X
      (ModuleCat.ofHom (completedNaiveCotangentComplex B P).liftedDifferential)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) i h₁ h₂
  exact ⟨(CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => hzero i (by omega) (by omega),
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => hzero i (by omega) (by omega)⟩

/-- The derived object represented by the completed naive cotangent complex has cohomology
concentrated in degrees `-1` and `0`. This is the two-term hypothesis of Stacks 0G9K for this
complex. -/
lemma completedNaiveCotangent_homology_vanishes
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) i).obj
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)) := by
  let L := (completedNaiveCotangentComplex B P).cochainComplex
  obtain ⟨hGE, hLE⟩ := completedNaiveCotangent_isStrictlyGE_and_isStrictlyLE B P
  intro i hiNeg hiZero
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{max u v} B.carrier) i).app L)
  let := hGE
  let := hLE
  by_cases hi : i < -1
  · exact (CochainComplex.exactAt_of_isGE L (-1) i hi).isZero_homology
  · have hi' : 0 < i := by omega
    exact (CochainComplex.exactAt_of_isLE L 0 i hi').isZero_homology

/-- The cochain complex of the completed naive cotangent complex is strictly supported between
degrees `-1` and `0`. These are the bracketing instances required to compute its two
cohomology modules as the kernel and the cokernel of its differential, in
`Rig.derivedHnegEquivHneg` and `Rig.derivedHzeroEquivHzero` below. -/
lemma completedNaiveCotangent_strictBounds
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    ((completedNaiveCotangentComplex B P).cochainComplex.IsStrictlyGE (-1)) ∧
      (completedNaiveCotangentComplex B P).cochainComplex.IsStrictlyLE 0 :=
  completedNaiveCotangent_isStrictlyGE_and_isStrictlyLE B P

/-- The scalars which factor through a linear map: `a` lies in this ideal exactly when there
is a retraction `h` with `h ∘ d = a • id`.  Condition (3) of Stacks 0GAJ says that a power of
the ideal of definition lands in this ideal for the differential of the completed naive
cotangent complex, and its being an ideal is what makes that condition checkable on products
of elements. -/
public def cotangentFactorizationIdeal {R : Type*} [CommRing R]
    {D E : Type*} [AddCommGroup D] [Module R D] [AddCommGroup E] [Module R E]
    (d : D →ₗ[R] E) : Ideal R where
  carrier := {a | ∃ h : E →ₗ[R] D, h.comp d = a • LinearMap.id}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨f, hf⟩
    rcases hb with ⟨g, hg⟩
    refine ⟨f + g, ?_⟩
    ext x
    have hf' : f (d x) = a • x := by simpa using LinearMap.congr_fun hf x
    have hg' : g (d x) = b • x := by simpa using LinearMap.congr_fun hg x
    change f (d x) + g (d x) = _
    rw [hf', hg']
    simp [add_smul]
  smul_mem' := by
    intro r a ha
    obtain ⟨f, hf⟩ := ha
    refine ⟨r • f, ?_⟩
    ext x
    have hf' : f (d x) = a • x := by simpa using LinearMap.congr_fun hf x
    change r • f (d x) = (r * a) • x
    rw [hf']
    simp [smul_smul]

private lemma completedNaiveCotangent_conormal_finitePresentation
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    Module.FinitePresentation B.carrier P.extension.Cotangent := by
  let : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
  let : IsNoetherianRing P.extension.Ring := by
    show IsNoetherianRing P.completedPolynomialRing
    infer_instance
  have hker : P.extension.ker.FG := Ideal.fg_of_isNoetherianRing _
  have hfinite : Module.Finite B.carrier P.extension.Cotangent :=
    Algebra.Extension.Cotangent.finite hker
  let : IsNoetherianRing B.carrier :=
    Rig.isNoetherianRing B
  exact Module.finitePresentation_of_finite B.carrier P.extension.Cotangent

/-- The cohomological condition for the completed naive cotangent complex: a power of `IB`
annihilates its degree-minus-one cohomology and its degree-zero cohomology is projective
relative to that power. -/
public def HasCotangentCohomologyCondition {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  let K := DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex
  let Hneg := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).obj K
  let Hzero := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj K
  ∃ c : ℕ,
    (∀ (a : B.carrier), a ∈ B.adicIdeal ^ c → ∀ x : Hneg, a • x = 0) ∧
      Module.IsIProjective B.carrier (B.adicIdeal ^ c) Hzero

/-- Every element of one power of `I` acts on the conormal module through the differential
of the completed naive cotangent complex. -/
public def HasCotangentFactorization {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∃ c : ℕ, ∀ (a : A), a ∈ I ^ c →
    ∃ h : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent,
      h.comp (completedNaiveCotangentComplex B P).differential =
        (algebraMap A B.carrier a) • LinearMap.id

/-- A finite family of Jacobian minors which covers the complement of the ideal of
definition and whose relations generate the presentation ideal modulo its square there. -/
public def HasJacobianCover {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : Prop :=
  ∃ (s : ℕ) (b : Fin s → P.completedPolynomialRing),
    B.adicIdeal ≤
      (Ideal.span (Set.range fun l : Fin s ↦ P.toAlgHom (b l))).radical ∧
      ∀ l : Fin s, ∃ (m : ℕ) (T : Fin m ↪ Fin P.variableCount)
        (f : Fin m → P.ker),
        (P.toAlgHom
          (Matrix.det (fun i j : Fin m ↦
            (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j))) ∣
            P.toAlgHom (b l)) ∧
          (∀ x : P.completedPolynomialRing, x ∈ P.ker →
            b l * x ∈
              Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
                P.ker ^ 2)

/-- A scalar of the presenting ring acts on the conormal module through its image in the
presented algebra. -/
lemma extension_cotangent_ring_smul_eq_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (E : Algebra.Extension R S) (r : E.Ring) (x : E.Cotangent) :
    r • x = (algebraMap E.Ring S r) • x := by
  apply Algebra.Extension.Cotangent.ext
  rw [Algebra.Extension.Cotangent.val_smul', Algebra.Extension.Cotangent.val_smul]
  have hr : E.σ (algebraMap E.Ring S r) - r ∈ E.ker := by
    apply RingHom.mem_ker.mpr
    simp [map_sub, E.algebraMap_σ]
  have hzero := Algebra.Extension.Cotangent.smul_eq_zero_of_mem (P := E)
    (E.σ (algebraMap E.Ring S r) - r) hr x.val
  rw [sub_smul] at hzero
  exact (sub_eq_zero.mp hzero).symm

lemma cotangent_mk_mem_span_of_mem_span
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (E : Algebra.Extension R S) {m : ℕ} (f : Fin m → E.ker) (x : E.Ring)
    (hxker : x ∈ E.ker)
    (hx : x ∈ Ideal.span (Set.range fun j : Fin m => (f j : E.Ring))) :
    Algebra.Extension.Cotangent.mk (P := E) ⟨x, hxker⟩ ∈
      Submodule.span S
        (Set.range fun j : Fin m => Algebra.Extension.Cotangent.mk (P := E) (f j)) := by
  let T := Submodule.span S
    (Set.range fun j : Fin m => Algebra.Extension.Cotangent.mk (P := E) (f j))
  have hspanKer : Ideal.span (Set.range fun j : Fin m => (f j : E.Ring)) ≤ E.ker :=
    Ideal.span_le.mpr (by
      rintro y ⟨j, rfl⟩
      exact (f j).property)
  have hmem : ∀ y : E.Ring,
      y ∈ Ideal.span (Set.range fun j : Fin m => (f j : E.Ring)) →
        ∀ hy : y ∈ E.ker,
          Algebra.Extension.Cotangent.mk (P := E) ⟨y, hy⟩ ∈ T := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, h⟩ := hz
      subst z
      intro hyker
      have hsub : (⟨(f j : E.Ring), hyker⟩ : E.ker) = f j := Subtype.ext rfl
      rw [hsub]
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero =>
      intro hyker
      have hzero : (⟨0, hyker⟩ : E.ker) = 0 := Subtype.ext rfl
      rw [hzero, map_zero]
      exact T.zero_mem
    | add y z hy hz ihy ihz =>
      intro hyzker
      have hyker := hspanKer hy
      have hzker := hspanKer hz
      have hadd : (⟨y + z, hyzker⟩ : E.ker) =
          (⟨y, hyker⟩ : E.ker) + ⟨z, hzker⟩ := Subtype.ext rfl
      rw [hadd, map_add]
      exact T.add_mem (ihy hyker) (ihz hzker)
    | smul c y hy ih =>
      intro hyker
      have hyker' := hspanKer hy
      have hsmul : (⟨c • y, hyker⟩ : E.ker) = c • (⟨y, hyker'⟩ : E.ker) :=
        Subtype.ext rfl
      rw [hsmul, map_smul]
      rw [extension_cotangent_ring_smul_eq_algebraMap]
      exact Submodule.smul_mem T (algebraMap E.Ring S c) (ih hyker')
  exact hmem x hx hxker

private lemma exists_local_basis_minor_of_split
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {n k : ℕ} (f : Fin k → M) (hf : Submodule.span R (Set.range f) = ⊤)
    [Module.FinitePresentation R M] (d : M →ₗ[R] (Fin n → R))
    (q : Ideal R) [q.IsPrime]
    (hsplit : ∃ r : LocalizedModule q.primeCompl (Fin n → R)
        →ₗ[Localization q.primeCompl] LocalizedModule q.primeCompl M,
      r.comp (LocalizedModule.map q.primeCompl d) = LinearMap.id) :
    let T := Localization q.primeCompl
    let Mq := LocalizedModule q.primeCompl M
    let Eq := LocalizedModule q.primeCompl (Fin n → R)
    let _locM : M →ₗ[R] Mq := LocalizedModule.mkLinearMap q.primeCompl M
    let locE : (Fin n → R) →ₗ[R] Eq :=
      LocalizedModule.mkLinearMap q.primeCompl (Fin n → R)
    let bE : Module.Basis (Fin n) T Eq :=
      (Pi.basisFun R (Fin n)).ofIsLocalizedModule T q.primeCompl locE
    ∃ (m : ℕ) (a : Fin m → Fin k)
      (b : Module.Basis (Fin m) (Localization q.primeCompl)
        (LocalizedModule q.primeCompl M)) (e : Fin m ↪ Fin n),
      (∀ i, b i = LocalizedModule.mkLinearMap q.primeCompl M (f (a i))) ∧
        IsUnit ((LinearMap.toMatrix b bE
          (LocalizedModule.map q.primeCompl d)).submatrix e id).det := by
  classical
  let T := Localization q.primeCompl
  let Mq := LocalizedModule q.primeCompl M
  let Eq := LocalizedModule q.primeCompl (Fin n → R)
  let locM : M →ₗ[R] Mq := LocalizedModule.mkLinearMap q.primeCompl M
  let locE : (Fin n → R) →ₗ[R] Eq := LocalizedModule.mkLinearMap q.primeCompl (Fin n → R)
  let dloc : Mq →ₗ[T] Eq := LocalizedModule.map q.primeCompl d
  obtain ⟨r, hr⟩ := hsplit
  let bE : Module.Basis (Fin n) T Eq :=
    (Pi.basisFun R (Fin n)).ofIsLocalizedModule T q.primeCompl locE
  have hspan : Submodule.span T (Set.range (locM ∘ f)) = ⊤ := by
    convert span_eq_top_of_isLocalizedModule T q.primeCompl locM hf using 1
    rw [Set.range_comp]
  have : Module.Projective T Mq := Module.Projective.of_split dloc r hr
  have : Module.Flat T Mq := Module.Flat.of_projective
  let : Module.FinitePresentation T Mq := inferInstance
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat (locM ∘ f) hspan
  let : Finite κ := Module.Finite.finite_basis b
  let ek : κ ≃ Fin (Nat.card κ) := Finite.equivFin κ
  let b' : Module.Basis (Fin (Nat.card κ)) T Mq := b.reindex ek
  let a' : Fin (Nat.card κ) → Fin k := a ∘ ek.symm
  have hb' : ∀ i, b' i = locM (f (a' i)) := by
    intro i
    simpa [b', a'] using hb (ek.symm i)
  let mat : Matrix (Fin n) (Fin (Nat.card κ)) T := LinearMap.toMatrix b' bE dloc
  let inv : Matrix (Fin (Nat.card κ)) (Fin n) T := LinearMap.toMatrix bE b' r
  have hmul : inv * mat = 1 := by
    rw [← LinearMap.toMatrix_comp b' bE b' r dloc, hr, LinearMap.toMatrix_id]
  obtain ⟨e, he⟩ := exists_isUnit_det_submatrix_of_mul_eq_one mat inv hmul
  exact ⟨Nat.card κ, a', b', e, hb', he⟩

private lemma exists_scalar_mul_mem_span_of_localized_span
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {S : Submonoid R} {n : ℕ} (f : Fin n → M)
    (hspan : Submodule.span (Localization S) (Set.range fun i ↦
      LocalizedModule.mkLinearMap S M (f i)) = ⊤) :
    ∃ s : S, ∀ x : M, s.val • x ∈ Submodule.span R (Set.range f) := by
  classical
  let V : Submodule R M := Submodule.span R (Set.range f)
  let Q := M ⧸ V
  let : Module R Q := inferInstance
  let : Module (Localization S) (LocalizedModule S Q) :=
    LocalizedModule.moduleOfIsLocalization
  let locQ : Q →ₗ[R] LocalizedModule S Q := LocalizedModule.mkLinearMap S Q
  let locM : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  let mQ : M →ₗ[R] Q := Submodule.mkQ V
  have hlocV : V.localized' (Localization S) S locM = ⊤ := by
    rw [Submodule.localized'_span]
    rw [← Set.range_comp]
    simpa [Function.comp_def, locM] using hspan
  let e := localizedQuotientEquiv S V
  have hquot : Subsingleton (LocalizedModule S M ⧸ V.localized S) := by
    show Subsingleton (LocalizedModule S M ⧸ V.localized' (Localization S) S locM)
    rw [hlocV]
    infer_instance
  have : Subsingleton (LocalizedModule S Q) := e.subsingleton_congr.mp hquot
  have hfzero : locQ = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
  have hcomp : locQ.comp (LinearMap.id : Q →ₗ[R] Q) = locQ.comp (0 : Q →ₗ[R] Q) := by
    ext x
    simp [hfzero]
  have : Module.Finite R Q := Module.Finite.of_surjective mQ (Submodule.mkQ_surjective V)
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S
    locQ LinearMap.id 0 hcomp
  refine ⟨s, fun x ↦ ?_⟩
  have hzero : s.val • Submodule.mkQ V x = 0 := by
    have h := congrArg (fun g : Q →ₗ[R] Q => g (Submodule.mkQ V x)) hs
    simpa [Q, Submonoid.smul_def] using h
  have hmem : Submodule.mkQ V (s.val • x) = 0 := by
    simpa [map_smul] using hzero
  exact (Submodule.Quotient.mk_eq_zero V).mp hmem

private lemma exists_local_jacobian_minor_of_split
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B)
    (q : Ideal B.carrier) [q.IsPrime]
    {k : ℕ} (f : Fin k → P.ker)
    (hspan : Submodule.span B.carrier
      (Set.range fun j ↦ Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) = ⊤)
    (hsplit : ∃ r : LocalizedModule q.primeCompl
        (Fin P.variableCount → B.carrier) →ₗ[Localization q.primeCompl]
        LocalizedModule q.primeCompl P.extension.Cotangent,
      r.comp (LocalizedModule.map q.primeCompl
        (completedNaiveCotangentComplex B P).differential) = LinearMap.id) :
    ∃ (m : ℕ) (T : Fin m ↪ Fin P.variableCount) (g : Fin m → P.ker),
      IsUnit (algebraMap B.carrier (Localization q.primeCompl)
        (P.toAlgHom (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (T i)
            (g j : P.completedPolynomialRing)))) ∧
        Submodule.span (Localization q.primeCompl)
          (Set.range fun j : Fin m =>
            LocalizedModule.mkLinearMap q.primeCompl P.extension.Cotangent
              (Algebra.Extension.Cotangent.mk (P := P.extension) (g j))) = ⊤ := by
  classical
  let K := completedNaiveCotangentComplex B P
  let D := P.extension.Cotangent
  let E := Fin P.variableCount → B.carrier
  let Tloc := Localization q.primeCompl
  let locD : D →ₗ[B.carrier] LocalizedModule q.primeCompl D :=
    LocalizedModule.mkLinearMap q.primeCompl D
  let locE : E →ₗ[B.carrier] LocalizedModule q.primeCompl E :=
    LocalizedModule.mkLinearMap q.primeCompl E
  let bE : Module.Basis (Fin P.variableCount) Tloc (LocalizedModule q.primeCompl E) :=
    (Pi.basisFun B.carrier (Fin P.variableCount)).ofIsLocalizedModule Tloc q.primeCompl locE
  have hkerEq : P.ker = P.extension.ker := rfl
  let fD : Fin k → D := fun j ↦ Algebra.Extension.Cotangent.mk (P := P.extension)
    (hkerEq ▸ f j)
  let : Module.FinitePresentation B.carrier D :=
    completedNaiveCotangent_conormal_finitePresentation B P
  obtain ⟨m, a, b, e, hb, he⟩ :=
    exists_local_basis_minor_of_split fD hspan K.differential q hsplit
  let g : Fin m → P.ker := fun i ↦ f (a i)
  let dloc : LocalizedModule q.primeCompl D →ₗ[Tloc]
      LocalizedModule q.primeCompl E := LocalizedModule.map q.primeCompl K.differential
  have hentry (i j : Fin m) :
    (LinearMap.toMatrix b bE dloc) (e i) j =
        algebraMap B.carrier Tloc (P.toAlgHom
          (K.partialDeriv (e i) (f (a j) : P.completedPolynomialRing))) := by
    rw [LinearMap.toMatrix_apply]
    rw [hb j]
    show bE.repr (dloc (locD (Algebra.Extension.Cotangent.mk
      (P := P.extension) (hkerEq ▸ f (a j))))) (e i) = _
    rw [show dloc (locD (fD (a j))) = locE (K.differential (fD (a j))) by
      show LocalizedModule.map q.primeCompl K.differential
        (LocalizedModule.mk (fD (a j)) 1) = _
      rw [LocalizedModule.map_mk]
      rfl]
    show ((Pi.basisFun B.carrier (Fin P.variableCount)).ofIsLocalizedModule
      Tloc q.primeCompl locE).repr (locE (K.differential (fD (a j)))) (e i) = _
    rw [Module.Basis.ofIsLocalizedModule_repr_apply]
    show algebraMap B.carrier Tloc
      ((Pi.basisFun B.carrier (Fin P.variableCount)).repr
        (K.differential (Algebra.Extension.Cotangent.mk (P := P.extension)
          (hkerEq ▸ f (a j)))) (e i)) = _
    rw [K.differential_mk]
    simp [Pi.basisFun_repr]
  let jacloc : Matrix (Fin m) (Fin m) Tloc := fun i j ↦
    algebraMap B.carrier Tloc (P.toAlgHom
      (K.partialDeriv (e i) (g j : P.completedPolynomialRing)))
  have hmatrix :
      (LinearMap.toMatrix b bE dloc).submatrix e id =
        jacloc := by
    ext i j
    exact hentry i j
  refine ⟨m, e, g, ?_, ?_⟩
  · have he' : IsUnit jacloc.det := by
      rw [← hmatrix]
      exact he
    let φ : P.completedPolynomialRing →+* Tloc :=
      (algebraMap B.carrier Tloc).comp P.toAlgHom.toRingHom
    let jac : Matrix (Fin m) (Fin m) P.completedPolynomialRing :=
      fun i j ↦ K.partialDeriv (e i) (g j : P.completedPolynomialRing)
    have hmap : φ.mapMatrix jac = jacloc := by
      ext i j
      rfl
    have he'' : IsUnit (φ jac.det) := by
      rw [RingHom.map_det, hmap]
      exact he'
    simpa [φ, Function.comp_def, jac] using he''
  · rw [← b.span_eq]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      show locD (fD (a i)) ∈ _
      rw [← hb i]
      exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      show b i ∈ _
      rw [hb i]
      exact Submodule.subset_span ⟨i, rfl⟩

private lemma cotangent_mem_span_implies_ideal_relation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (E : Algebra.Extension R S) {m : ℕ} (f : Fin m → E.ker)
    (x : E.ker) (hx : Algebra.Extension.Cotangent.mk (P := E) x ∈
      Submodule.span S (Set.range fun j : Fin m =>
        Algebra.Extension.Cotangent.mk (P := E) (f j))) :
    x.val ∈ Ideal.span (Set.range fun j : Fin m => (f j : E.Ring)) + E.ker ^ 2 := by
  let F : Submodule S E.Cotangent := Submodule.span S
    (Set.range fun j : Fin m => Algebra.Extension.Cotangent.mk (P := E) (f j))
  have hspanKer : Ideal.span (Set.range fun j : Fin m => (f j : E.Ring)) ≤ E.ker :=
    Ideal.span_le.mpr (by
      rintro y ⟨j, rfl⟩
      exact (f j).property)
  have hrepr : ∀ z : E.Cotangent, z ∈ F →
      ∃ y : E.ker, y.val ∈ Ideal.span (Set.range fun j : Fin m => (f j : E.Ring)) ∧
        z = Algebra.Extension.Cotangent.mk (P := E) y := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      refine ⟨f j, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, ?_, ?_⟩ <;> simp
    | add z w hz hw ihz ihw =>
      obtain ⟨y, hy, rfl⟩ := ihz
      obtain ⟨y', hy', rfl⟩ := ihw
      refine ⟨y + y', Ideal.add_mem _ hy hy', by simp [map_add]⟩
    | smul a z hz ih =>
      obtain ⟨y, hy, hzy⟩ := ih
      have hya : E.σ a * y.val ∈ E.ker := E.ker.mul_mem_left _ y.property
      refine ⟨⟨E.σ a * y.val, hya⟩, ?_, ?_⟩
      · exact Ideal.mul_mem_left _ _ hy
      · rw [hzy]
        calc
          a • Algebra.Extension.Cotangent.mk (P := E) y =
              algebraMap E.Ring S (E.σ a) • Algebra.Extension.Cotangent.mk (P := E) y := by
                rw [E.algebraMap_σ]
          _ = E.σ a • Algebra.Extension.Cotangent.mk (P := E) y :=
            (extension_cotangent_ring_smul_eq_algebraMap E (E.σ a) _).symm
          _ = Algebra.Extension.Cotangent.mk (P := E) ((E.σ a) • y) := by rw [map_smul]
          _ = Algebra.Extension.Cotangent.mk (P := E) ⟨E.σ a * y.val, hya⟩ := rfl
  obtain ⟨y, hy, hxy⟩ := hrepr _ hx
  have hdiff : x.val - y ∈ E.ker ^ 2 := by
    apply (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem x y).mp
    simpa using hxy
  have hdecomp : x.val = y + (x.val - y) := by ring
  rw [hdecomp]
  exact Submodule.mem_sup.mpr ⟨y, hy, x.val - y, hdiff, rfl⟩

private lemma localizedModuleMap_comp
    {R : Type u} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (S : Submonoid R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    LocalizedModule.map S (g.comp f) =
      (LocalizedModule.map S g).comp (LocalizedModule.map S f) := by
  apply LinearMap.ext
  apply LocalizedModule.induction_on
  intro x s
  simp

/-- Prime-local selection of a Jacobian chart. Given a completed polynomial presentation `P` of
`B` admitting a cotangent factorization and a prime `q` of `B` not containing the adic ideal,
there is an element `b` of the completed polynomial ring with `P.toAlgHom b ∉ q` whose image is
divisible by a minor of the Jacobian matrix of a finite subfamily `f` of the presentation ideal,
and such that `b` multiplies the presentation ideal into the span of `f` plus its square. -/
lemma exists_jacobian_chart_away_prime
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B)
    (hfactor : HasCotangentFactorization B P)
    (q : Ideal B.carrier) [q.IsPrime] (hq : ¬ B.adicIdeal ≤ q) :
    ∃ b : P.completedPolynomialRing, P.toAlgHom b ∉ q ∧
      ∃ (m : ℕ) (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker),
        (P.toAlgHom (Matrix.det fun i j : Fin m ↦
            (completedNaiveCotangentComplex B P).partialDeriv (T i)
              (f j : P.completedPolynomialRing)) ∣
            P.toAlgHom b) ∧
        (∀ x : P.completedPolynomialRing, x ∈ P.ker →
          b * x ∈ Ideal.span (Set.range fun j : Fin m => (f j : P.completedPolynomialRing)) +
            P.ker ^ 2) := by
  classical
  obtain ⟨c, hc⟩ := hfactor
  have hnot : ¬ I ≤ Ideal.comap (algebraMap A B.carrier) q := by
    intro hle
    apply hq
    rw [AdicFiniteTypeAlgebra.adicIdeal, Ideal.map_le_iff_le_comap]
    exact hle
  obtain ⟨a, ha, haneq⟩ := Set.not_subset.mp hnot
  let α : B.carrier := algebraMap A B.carrier (a ^ c)
  have hqp : q.IsPrime := inferInstance
  have hα : α ∉ q := by
    intro h
    apply haneq
    have hpow : (algebraMap A B.carrier a) ^ c ∈ q := by simpa [α, map_pow] using h
    exact hqp.mem_of_pow_mem c hpow
  obtain ⟨h, hh⟩ := hc (a ^ c) (Ideal.pow_mem_pow ha c)
  let S := q.primeCompl
  let Tloc := Localization S
  let sα : S := ⟨α, hα⟩
  let u : IsUnit (algebraMap B.carrier Tloc α) :=
    IsLocalization.map_units Tloc sα
  let e : LocalizedModule S P.extension.Cotangent ≃ₗ[Tloc]
      LocalizedModule S P.extension.Cotangent := LinearEquiv.smulOfUnit u.unit
  have he : (LocalizedModule.map S h).comp
        (LocalizedModule.map S (completedNaiveCotangentComplex B P).differential) =
      e.toLinearMap := by
    rw [← localizedModuleMap_comp S (completedNaiveCotangentComplex B P).differential h]
    change h.comp (completedNaiveCotangentComplex B P).differential = α • LinearMap.id at hh
    rw [hh, map_smul, LocalizedModule.map_id]
    ext x
    show α • x = (u.unit : Tloc) • x
    rw [IsUnit.unit_spec]
    exact (IsScalarTower.algebraMap_smul (R := B.carrier) (A := Tloc) α x).symm
  let r := e.symm.toLinearMap.comp (LocalizedModule.map S h)
  have hsplit : r.comp (LocalizedModule.map S
      (completedNaiveCotangentComplex B P).differential) = LinearMap.id := by
    show e.symm.toLinearMap.comp ((LocalizedModule.map S h).comp
      (LocalizedModule.map S (completedNaiveCotangentComplex B P).differential)) = _
    rw [he]
    ext x
    exact e.symm_apply_apply x
  let : IsNoetherianRing P.completedPolynomialRing := AdicCompletion.isNoetherianRing _
  let : IsNoetherianRing P.extension.Ring := by
    show IsNoetherianRing P.completedPolynomialRing
    infer_instance
  have hkerFG : P.extension.ker.FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨k, f₀, hf₀⟩ := (Submodule.fg_iff_exists_fin_generating_family).mp hkerFG
  have hfker : Ideal.span (Set.range f₀) = P.ker := by
    show Submodule.span P.extension.Ring (Set.range f₀) = P.extension.ker
    exact hf₀
  let f : Fin k → P.ker := fun j => ⟨f₀ j,
    hfker.le (Ideal.subset_span ⟨j, rfl⟩)⟩
  have hspan : Submodule.span B.carrier
      (Set.range fun j => Algebra.Extension.Cotangent.mk (P := P.extension) (f j)) = ⊤ := by
    show Submodule.span B.carrier
      (Set.range fun j => Algebra.Extension.Cotangent.mk (P := P.extension)
        ⟨f₀ j, hfker.le (Ideal.subset_span ⟨j, rfl⟩)⟩) = ⊤
    exact Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
      (P := P.extension) f₀ hfker
  obtain ⟨m, T, g, hdetUnit, hspanLoc⟩ :=
    exists_local_jacobian_minor_of_split B P q f hspan ⟨r, hsplit⟩
  let gD : Fin m → P.extension.Cotangent := fun j =>
    Algebra.Extension.Cotangent.mk (P := P.extension) (g j)
  let : Module.FinitePresentation B.carrier P.extension.Cotangent :=
    completedNaiveCotangent_conormal_finitePresentation B P
  obtain ⟨denom, hdenom⟩ :=
    exists_scalar_mul_mem_span_of_localized_span gD hspanLoc
  let d : P.completedPolynomialRing := Matrix.det fun i j : Fin m ↦
    (completedNaiveCotangentComplex B P).partialDeriv (T i) (g j : P.completedPolynomialRing)
  let detB := P.toAlgHom d
  have hdetNot : detB ∉ q := by
    intro hd
    have hcomp : detB ∈ q.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff Tloc q detB).mp (by
        simpa [detB, d] using hdetUnit)
    exact hcomp hd
  have hprodNot : denom.val * detB ∉ q := by
    intro hmem
    rcases hqp.mul_mem_iff_mem_or_mem.mp hmem with h | h
    · exact denom.property h
    · exact hdetNot h
  have hkerEq : P.ker = P.extension.ker := rfl
  let lift : P.extension.Ring := P.extension.σ denom.val
  let dE : P.extension.Ring := d
  let bE := lift * dE
  let b : P.completedPolynomialRing := bE
  have hbmap : P.toAlgHom b = denom.val * detB := by
    show P.toAlgHom (lift * dE) = _
    rw [map_mul]
    rw [show P.toAlgHom lift = denom.val from P.extension.algebraMap_σ _]
  refine ⟨b, ?_, m, T, g, ?_, ?_⟩
  · rw [hbmap]
    exact hprodNot
  · refine ⟨denom.val, ?_⟩
    rw [hbmap]
    ring
  · intro x hx
    let xE : P.extension.ker := ⟨x, hx⟩
    have hx' : lift * xE.val ∈ P.extension.ker :=
      P.extension.ker.mul_mem_left _ xE.property
    let x' : P.extension.ker := ⟨lift * xE.val, hx'⟩
    have hmk : Algebra.Extension.Cotangent.mk (P := P.extension) x' =
        denom.val • Algebra.Extension.Cotangent.mk (P := P.extension) xE := by
      have hxEq : x' = lift • xE := by ext; rfl
      calc
        _ = lift • Algebra.Extension.Cotangent.mk (P := P.extension) xE := by
          rw [hxEq, map_smul]
        _ = denom.val • Algebra.Extension.Cotangent.mk (P := P.extension) xE := by
          rw [extension_cotangent_ring_smul_eq_algebraMap, P.extension.algebraMap_σ]
    have hspanx : Algebra.Extension.Cotangent.mk (P := P.extension) x' ∈
        Submodule.span B.carrier (Set.range fun j => gD j) := by
      rw [hmk]
      exact hdenom (Algebra.Extension.Cotangent.mk (P := P.extension) xE)
    let gE : Fin m → P.extension.ker := fun j => hkerEq ▸ g j
    have hrel := cotangent_mem_span_implies_ideal_relation P.extension gE x' hspanx
    have hmulE : dE * (lift * xE.val) ∈
        Ideal.span (Set.range fun j => (gE j : P.extension.Ring)) +
          P.extension.ker ^ 2 :=
      (Ideal.span (Set.range fun j : Fin m => (gE j : P.extension.Ring)) +
        P.extension.ker ^ 2).mul_mem_left dE hrel
    have heq : b * x = dE * (lift * xE.val) := by
      show (lift * dE) * xE.val = dE * (lift * xE.val)
      ring
    rw [heq]
    exact hmulE

end Rig

end
