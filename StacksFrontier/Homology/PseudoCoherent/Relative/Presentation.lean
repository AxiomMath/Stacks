module

public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Polynomial

@[expose] public section

/-!
# Independence of the polynomial presentation

Whether a complex of `A`-modules is `m`-pseudo-coherent after restriction of scalars along a
finite polynomial presentation of `A` over `R` does not depend on which presentation is used.
This is what makes the relative notion of Stacks 065I well behaved: quantifying over every
presentation and requiring one are the same condition.

## Main results

* `PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent` (Stacks 065H).

## Implementation notes

Two presentations are compared through a common refinement: adjoining the variables of one to the
other gives a presentation mapping onto both, and tag 065G says that adjoining a variable and
evaluating it at zero leaves `m`-pseudo-coherence unchanged. Tag 064Z moves the property along
the resulting surjections.

Tags 064U, 064Z and 065G are cited from their providers -- the first two are cluster 10's, in
`StacksFrontier/Homology/PseudoCoherent/{Basic,ChangeOfRings}.lean`, and 065G is this cluster's, in
`Relative/Polynomial.lean`.

## References

* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- On derived categories, restriction of scalars along a composite `g.comp f` is isomorphic to
restriction along `g` followed by restriction along `f`. -/
public noncomputable def restrictScalarsDerivedCompIso
    {R : Type u} {S : Type w} {T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (K : DerivedCategory (ModuleCat.{v} T)) :
    (ModuleCat.restrictScalars.{v} (g.comp f)).mapDerivedCategory.obj K ≅
      (ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let F := ModuleCat.restrictScalars.{v} f
  let G := ModuleCat.restrictScalars.{v} g
  let H := ModuleCat.restrictScalars.{v} (g.comp f)
  exact H.mapDerivedCategory.mapIso e.symm ≪≫ H.mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp f g).symm
        (ComplexShape.up ℤ)).symm.app P) ≪≫
    (F.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
    F.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app P).symm ≪≫
    F.mapDerivedCategory.mapIso (G.mapDerivedCategory.mapIso e)

/-- Restriction of scalars along `f : A →+* B` preserves and reflects `m`-pseudo-coherence of
objects of `D(B)` when `B` is a pseudo-coherent `A`-module. -/
private lemma isPseudoCoherentFrom_iff_restrictScalars_of_pseudoCoherent
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (hB : IsModulePseudoCoherent (R := A) ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)))
    (K : DerivedCategory (ModuleCat.{max u v w} B)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{max u v w} f).mapDerivedCategory.obj K) m :=
  by
  let P := DerivedCategory.Q.objPreimage K
  let a : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (isPseudoCoherentFrom_iso_iff a m).symm.trans
    ((pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars f hB P m).1.trans
      (isPseudoCoherentFrom_iso_iff
        (((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app P).symm ≪≫
          (ModuleCat.restrictScalars f).mapDerivedCategory.mapIso a) m))

private lemma isPseudoCoherentFrom_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{max u v} S)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory.obj K) m := by
  let M := (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S S)
  let j := (ModuleCat.restrictScalarsIsoOfEquiv e).toLinearEquiv
  have : Module.Finite R M := Module.Finite.of_surjective j.symm.toLinearMap j.symm.surjective
  have : Module.Free R M := Module.Free.of_equiv j.symm
  exact isPseudoCoherentFrom_iff_restrictScalars_of_pseudoCoherent e.toRingHom
    (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free M) K m

/-- `m`-pseudo-coherence after restriction of scalars along `g.comp f` is the same as after
restriction along `g` and then along `f`. -/
lemma isPseudoCoherentFrom_restrictScalars_comp_iff
    {R : Type u} {S : Type w} {T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (K : DerivedCategory (ModuleCat.{v} T)) (m : ℤ) :
    IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{v} (g.comp f)).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{v} f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{v} g).mapDerivedCategory.obj K)) m :=
  isPseudoCoherentFrom_iso_iff (restrictScalarsDerivedCompIso f g K) m

private lemma isPseudoCoherentFrom_restrictScalars_comp_ringEquiv
    {R S : Type u} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) (K : DerivedCategory (ModuleCat.{max u v} T)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{max u v} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} (f.comp e.toRingHom)).mapDerivedCategory.obj K) m :=
  (isPseudoCoherentFrom_restrictScalars_ringEquiv e _ m).trans
    (isPseudoCoherentFrom_restrictScalars_comp_iff e.toRingHom f K m).symm

private lemma isPseudoCoherentFrom_restrictScalars_polynomial_eval
    {R : Type u} [CommRing R] (x : R)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔ IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{max u v}
        (Polynomial.evalRingHom x)).mapDerivedCategory.obj K) m := by
  let e := (Polynomial.algEquivAevalXAddC x).toRingEquiv
  have h : (Polynomial.evalRingHom (0 : R)).comp e.toRingHom = Polynomial.evalRingHom x := by
    ext <;> simp [e, Polynomial.algEquivAevalXAddC_apply]
  rw [← h]
  exact (isPseudoCoherentFrom_iff_restrictScalars_polynomial_evalZero K m).trans
    (isPseudoCoherentFrom_restrictScalars_comp_ringEquiv e _ K m)

/-- If restriction along `g : S →+* T` preserves `m`-pseudo-coherence, then so does restriction
along `(f.comp g).comp e` for a ring isomorphism `e`, relative to restriction along `f`. -/
private lemma isPseudoCoherentFrom_restrictScalars_comp_comp_ringEquiv
    {R S T : Type u} {U : Type w} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (e : R ≃+* S) (g : S →+* T) (f : T →+* U) (K : DerivedCategory (ModuleCat.{max u v} U)) (m : ℤ)
    (h : ∀ K' : DerivedCategory (ModuleCat.{max u v} T), IsPseudoCoherentFrom K' m ↔
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{max u v} g).mapDerivedCategory.obj K') m) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{max u v} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} ((f.comp g).comp e.toRingHom)).mapDerivedCategory.obj
          K) m :=
  (h _).trans ((isPseudoCoherentFrom_restrictScalars_comp_iff g f K m).symm.trans
    (isPseudoCoherentFrom_restrictScalars_comp_ringEquiv e (f.comp g) K m))

private lemma isPseudoCoherentFrom_restrictScalars_mvPolynomial_eval
    {R : Type u} [CommRing R] (n : ℕ) (x : Fin n → R)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔ IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{max u v} (MvPolynomial.eval x)).mapDerivedCategory.obj K) m := by
  induction n with
  | zero =>
    have h : MvPolynomial.eval x =
        (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom := by
      ext i
      · simpa only [RingHom.comp_apply, MvPolynomial.eval_C, MvPolynomial.algebraMap_eq,
          Algebra.algebraMap_self, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv] using
          ((MvPolynomial.isEmptyAlgEquiv R (Fin 0)).commutes i).symm
      · exact Fin.elim0 i
    rw [h]
    exact isPseudoCoherentFrom_restrictScalars_ringEquiv _ K m
  | succ n ih =>
    let f := MvPolynomial.eval (fun i : Fin n => x i.succ)
    let g := Polynomial.evalRingHom (MvPolynomial.C (x 0) : MvPolynomial (Fin n) R)
    let e := (MvPolynomial.finSuccEquiv R n).toRingEquiv
    have h : MvPolynomial.eval x = (f.comp g).comp e.toRingHom := by
      ext r
      · simp [f, g, e, MvPolynomial.finSuccEquiv_apply]
      · refine Fin.cases ?_ (fun j => ?_) r
        · simp [f, g, e, MvPolynomial.finSuccEquiv_X_zero]
        · simp [f, g, e, MvPolynomial.finSuccEquiv_X_succ]
    rw [h]
    exact (ih (fun i => x i.succ)).trans (isPseudoCoherentFrom_restrictScalars_comp_comp_ringEquiv
      e g f K m (isPseudoCoherentFrom_restrictScalars_polynomial_eval _ · m))

private lemma isPseudoCoherentFrom_polynomialPresentation_iff
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (m : ℤ)
    {n₁ n₂ : ℕ} (α₁ : MvPolynomial (Fin n₁) R →ₐ[R] A)
    (α₂ : MvPolynomial (Fin n₂) R →ₐ[R] A)
    (hα₁ : Function.Surjective α₁) (hα₂ : Function.Surjective α₂) :
    IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} α₁.toRingHom).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} α₂.toRingHom).mapDerivedCategory.obj K) m := by
  classical
  choose f hf using fun j : Fin n₂ => hα₁ (α₂ (MvPolynomial.X j))
  choose g hg using fun i : Fin n₁ => hα₂ (α₁ (MvPolynomial.X i))
  let e₁ := MvPolynomial.sumRingEquiv R (Fin n₂) (Fin n₁)
  let e₂ := (MvPolynomial.renameEquiv R (Equiv.sumComm (Fin n₂) (Fin n₁))).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv R (Fin n₁) (Fin n₂))
  have h : (α₁.toRingHom.comp (MvPolynomial.eval f)).comp e₁.toRingHom =
      (α₂.toRingHom.comp (MvPolynomial.eval g)).comp e₂.toRingHom := by
    ext r
    · simp [e₁, e₂, MvPolynomial.algebraMap_eq]
    · cases r with
      | inl j => simpa [e₁, e₂] using hf j
      | inr i => simpa [e₁, e₂] using (hg i).symm
  have h₁ := isPseudoCoherentFrom_restrictScalars_comp_comp_ringEquiv e₁ _ α₁.toRingHom K m
    (isPseudoCoherentFrom_restrictScalars_mvPolynomial_eval n₂ f · m)
  have h₂ := isPseudoCoherentFrom_restrictScalars_comp_comp_ringEquiv e₂ _ α₂.toRingHom K m
    (isPseudoCoherentFrom_restrictScalars_mvPolynomial_eval n₁ g · m)
  rw [h] at h₁
  exact h₁.trans h₂.symm

private lemma isPseudoCoherent_polynomialPresentation_iff
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat.{max u v} A))
    {n₁ n₂ : ℕ} (α₁ : MvPolynomial (Fin n₁) R →ₐ[R] A)
    (α₂ : MvPolynomial (Fin n₂) R →ₐ[R] A)
    (hα₁ : Function.Surjective α₁) (hα₂ : Function.Surjective α₂) :
    IsPseudoCoherent
        ((ModuleCat.restrictScalars.{max u v} α₁.toRingHom).mapDerivedCategory.obj K) ↔
      IsPseudoCoherent
        ((ModuleCat.restrictScalars.{max u v} α₂.toRingHom).mapDerivedCategory.obj K) := by
  rw [pseudoCoherent_iff_all _, pseudoCoherent_iff_all _]
  exact forall_congr' fun m => isPseudoCoherentFrom_polynomialPresentation_iff K m α₁ α₂ hα₁ hα₂

/-- **Stacks 065H.** For a finite-type `R`-algebra `A`, `m`-pseudo-coherence of an object of
`D(A)` after restriction to a finite polynomial presentation is independent of the presentation.
The same is true of pseudo-coherence. For an object represented by a complex,
`Functor.mapDerivedCategoryFactors` identifies each restricted object below with the localization
of the representing complex after degreewise restriction of scalars. -/
@[stacks 065H]
public theorem isPseudoCoherentFrom_polynomialPresentation_independent
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat.{max u v} A)) (m : ℤ) :
    ((∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        IsPseudoCoherentFrom
          ((ModuleCat.restrictScalars.{max u v} α.toRingHom).mapDerivedCategory.obj K) m) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        IsPseudoCoherentFrom
          ((ModuleCat.restrictScalars.{max u v} α.toRingHom).mapDerivedCategory.obj K) m) ∧
    ((∃ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α ∧
        IsPseudoCoherent
          ((ModuleCat.restrictScalars.{max u v} α.toRingHom).mapDerivedCategory.obj K)) ↔
      ∀ (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective α →
        IsPseudoCoherent
          ((ModuleCat.restrictScalars.{max u v} α.toRingHom).mapDerivedCategory.obj K)) := by
  obtain ⟨n₀, α₀, hα₀⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  refine ⟨⟨?_, fun h => ⟨n₀, α₀, hα₀, h n₀ α₀ hα₀⟩⟩, ?_, fun h => ⟨n₀, α₀, hα₀, h n₀ α₀ hα₀⟩⟩
  · rintro ⟨n, α, hα, hK⟩ n' α' hα'
    exact (isPseudoCoherentFrom_polynomialPresentation_iff K m α α' hα hα').mp hK
  · rintro ⟨n, α, hα, hK⟩ n' α' hα'
    exact (isPseudoCoherent_polynomialPresentation_iff K α α' hα hα').mp hK

/-- One direction of `PseudoCoherence.nonempty_finiteFreeModuleResolution_iff_of_surjective`. The
resolution over `α` makes `M` pseudo-coherent over `R[x₁, …, xₙ]` (Stacks 064T), Stacks 065H
moves that to the presentation `β`, and Stacks 064T turns it back into a resolution. -/
private theorem nonempty_finiteFreeModuleResolution_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module A M] {n n' : ℕ}
    {α : MvPolynomial (Fin n) R →ₐ[R] A} {β : MvPolynomial (Fin n') R →ₐ[R] A}
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    (h : letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
      Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n) R) M)) :
    letI : Module (MvPolynomial (Fin n') R) M := Module.compHom M β.toRingHom
    Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n') R) M) := by
  have : Algebra.FiniteType R A := .of_surjective α hα
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  have hαK : IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj K) := by
    let : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
    exact IsPseudoCoherent.ofIso
      ((modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := MvPolynomial (Fin n) R) M).2.2.2.mpr h)
      (((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of A M)).symm
  have hβK := (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u}
    (R := R) K 0).2.mp ⟨n, α, hα, hαK⟩ n' β hβ
  let : Module (MvPolynomial (Fin n') R) M := Module.compHom M β.toRingHom
  exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    (R := MvPolynomial (Fin n') R) M).2.2.2.mp
    (IsPseudoCoherent.ofIso hβK
      (((ModuleCat.restrictScalars.{u} β.toRingHom).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of A M)))

/-- **Stacks 065H for a module.** Let `A` be an `R`-algebra and `M` an `A`-module. Over two finite
polynomial presentations `α` and `β` of `A`, the module `M` has a resolution by finite free
modules over the one exactly when it has one over the other. The statement mentions no derived
category; the proof reads pseudo-coherence in the model this file fixes. -/
public theorem nonempty_finiteFreeModuleResolution_iff_of_surjective
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : Type u) [AddCommGroup M] [Module A M] {n n' : ℕ}
    {α : MvPolynomial (Fin n) R →ₐ[R] A} {β : MvPolynomial (Fin n') R →ₐ[R] A}
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    (letI : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom;
      Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n) R) M)) ↔
      letI : Module (MvPolynomial (Fin n') R) M := Module.compHom M β.toRingHom
      Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n') R) M) :=
  ⟨nonempty_finiteFreeModuleResolution_of_surjective M hα hβ,
    nonempty_finiteFreeModuleResolution_of_surjective M hβ hα⟩

/-- If `S`, regarded as an `R`-module through `f`, is pseudo-coherent, then an object of the
derived category of `S`-modules is `m`-pseudo-coherent if and only if its restriction of scalars
along `f` is. -/
lemma isPseudoCoherentFrom_iff_restrictScalars
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hS : IsModulePseudoCoherent (R := R)
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (K : DerivedCategory (ModuleCat.{u} S)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K) m :=
  isPseudoCoherentFrom_iff_restrictScalars_of_pseudoCoherent f hS K m

namespace PrincipalResolution

noncomputable section

variable (S : Type u) [CommRing S]

private def term : ℕ → ModuleCat.{u} S
  | 0 => ModuleCat.of S S
  | 1 => ModuleCat.of S S
  | _ + 2 => ModuleCat.of S (Fin 0 → S)

variable (f : S)

private def differential : (n : ℕ) → term S (n + 1) ⟶ term S n
  | 0 => ModuleCat.ofHom (LinearMap.mulLeft S f)
  | _ + 1 => 0

private lemma differential_sq (n : ℕ) :
    differential S f (n + 1) ≫ differential S f n = 0 := by
  cases n <;> exact zero_comp

private def complex : ChainComplex (ModuleCat.{u} S) ℕ :=
  ChainComplex.of (term S) (differential S f) (differential_sq S f)

/-- The quotient `S ⧸ (f)`, regarded as an `S`-module. -/
abbrev quotientModule :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
    (ModuleCat.of (S ⧸ Ideal.span {f}) (S ⧸ Ideal.span {f}))

private def augmentationLinear : S →ₗ[S] quotientModule S f where
  toFun := Ideal.Quotient.mk (Ideal.span {f})
  map_add' := map_add _
  map_smul' a b := map_mul (Ideal.Quotient.mk (Ideal.span {f})) a b

private def augmentation : (complex S f).X 0 ⟶ quotientModule S f :=
  ModuleCat.ofHom (augmentationLinear S f)

private lemma augmentation_condition :
    (complex S f).d 1 0 ≫ augmentation S f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change S at a
  change Ideal.Quotient.mk (Ideal.span {f}) (f * a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (dvd_mul_right f a))

private def pi : complex S f ⟶
    (ChainComplex.single₀ (ModuleCat S)).obj (quotientModule S f) :=
  (ChainComplex.toSingle₀Equiv (complex S f) (quotientModule S f)).symm
    ⟨augmentation S f, augmentation_condition S f⟩

private lemma exactAt_one (hf : ∀ a : S, f * a = 0 → a = 0) :
    (complex S f).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' (complex S f) 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro a ha
  change S at a
  change f * a = 0 at ha
  obtain rfl := hf a ha
  exact ⟨0, rfl⟩

private lemma exactAt_succ_succ (n : ℕ) : (complex S f).ExactAt (n + 2) := by
  rw [HomologicalComplex.exactAt_iff' (complex S f) (n + 3) (n + 2) (n + 1)
    (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  exact fun _ _ => ⟨0, @Subsingleton.elim (Fin 0 → S) inferInstance _ _⟩

private lemma augmentation_exact :
    (ShortComplex.mk ((complex S f).d 1 0) (augmentation S f)
      (augmentation_condition S f)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  change S at a
  change Ideal.Quotient.mk (Ideal.span {f}) a = 0 at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, hb.symm⟩

private lemma augmentation_epi : Epi (augmentation S f) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Ideal.Quotient.mk_surjective (I := Ideal.span {f})

private lemma quasiIsoAt_zero : QuasiIsoAt (pi S f) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ ((complex S f).shape 0 0 (by simp))
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (quotientModule S f) 1 0)
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (quotientModule S f) 0 0)]
  exact ⟨augmentation_exact S f, augmentation_epi S f⟩

private lemma pi_quasiIso (hf : ∀ a : S, f * a = 0 → a = 0) : QuasiIso (pi S f) := by
  rw [quasiIso_iff]
  rintro (_ | n)
  · exact quasiIsoAt_zero S f
  · rw [quasiIsoAt_iff_exactAt' (pi S f) (n + 1)
      (ChainComplex.exactAt_succ_single_obj (quotientModule S f) n)]
    rcases n with _ | n
    · exact exactAt_one S f hf
    · simpa [Nat.add_assoc] using exactAt_succ_succ S f n

private lemma finite_free (n : ℕ) :
    Module.Finite S ((complex S f).X n) ∧ Module.Free S ((complex S f).X n) := by
  rcases n with _ | _ | n
  · exact ⟨inferInstanceAs (Module.Finite S S), inferInstanceAs (Module.Free S S)⟩
  · exact ⟨inferInstanceAs (Module.Finite S S), inferInstanceAs (Module.Free S S)⟩
  · exact ⟨inferInstanceAs (Module.Finite S (Fin 0 → S)),
      inferInstanceAs (Module.Free S (Fin 0 → S))⟩

/-- If `f` is a nonzerodivisor, then `S ⧸ (f)` is a pseudo-coherent `S`-module: the complex
`0 → S → S`, with multiplication by `f` as differential, resolves it by finite free modules. -/
lemma isModulePseudoCoherent (hf : ∀ a : S, f * a = 0 → a = 0) :
    IsModulePseudoCoherent (R := S) (quotientModule S f) :=
  (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
    (quotientModule S f)).2.2.2.mpr ⟨{
      complex := complex S f
      hasHomology := fun _ => inferInstance
      π := pi S f
      quasiIso := pi_quasiIso S f hf
      free := fun n => (finite_free S f n).2
      finite := fun n => (finite_free S f n).1 }⟩

end

end PrincipalResolution

end PseudoCoherence
