module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Dynamics.Newton
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Smooth.Lifting

@[expose] public section

/-!
# Henselian pairs from nilpotent and complete data

An ideal all of whose elements are nilpotent makes a henselian pair, and reduction modulo such an
ideal is an equivalence on étale algebras. The same holds for an adically complete ring, which is
Mathlib's `IsAdicComplete.henselianRing`. Combining the nilpotent case with a limit argument, the
inverse limit of a sequence of rings whose transition maps are surjective with locally nilpotent
kernels is henselian along the kernel of every projection.

## Main definitions

* `etaleBaseChange`: base change of étale algebras along the quotient map `A → A ⧸ I`.

## Main results

* `etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical`: for `I ≤ nilradical A`,
  reduction modulo `I` is an equivalence on étale algebras and `(A, I)` is henselian.
* `henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical`: the inverse limit of a sequence
  of surjections with locally nilpotent kernels is henselian along each projection kernel.

## Implementation notes

The reduction of an `A`-algebra `B` modulo the extended ideal is represented by the canonically
isomorphic base change `(A ⧸ I) ⊗[A] B`, and the category of étale algebras is the full
subcategory of `CommAlgCat` cut out by `CommAlgCat.etale`. Only algebras in the universe of `A`
are needed, since an étale algebra is of finite presentation. Henselianness here is Mathlib's
`HenselianRing`, the Newton-lifting form of the condition.

## References

* [Stacks: Tag 0ALI](https://stacks.math.columbia.edu/tag/0ALI)
* [Stacks: Tag 0ALJ](https://stacks.math.columbia.edu/tag/0ALJ)
* [Stacks: Tag 0CT7](https://stacks.math.columbia.edu/tag/0CT7)
-/

add_to_stacks 0ALJ "An `I`-adically complete ring is henselian at `I`; this is Mathlib's
instance." IsAdicComplete.henselianRing
add_to_sga "3 X 4.0" "Recall 4.0" IsAdicComplete.henselianRing
add_to_ega "IV 18.5.14" "more general" IsAdicComplete.henselianRing
add_to_ega "IV 18.5.16" "more general" IsAdicComplete.henselianRing

open CategoryTheory CategoryTheory.Limits TensorProduct Polynomial
open scoped Ring

universe u

section

/-- Base change of étale algebras along the quotient map `A → A ⧸ I`. On objects this is the
canonical tensor-product model of reduction modulo the extended ideal. -/
@[simps, ega "I 3.7.1" "special case"]
public def etaleBaseChange {A : Type u} [CommRing A] (I : Ideal A) :
    (CommAlgCat.etale.{u} A).FullSubcategory ⥤
      (CommAlgCat.etale.{u} (A ⧸ I)).FullSubcategory where
  obj B := ⟨CommAlgCat.of (A ⧸ I) ((A ⧸ I) ⊗[A] B.obj), by
    let _ : Algebra.Etale A B.obj := B.property
    infer_instance⟩
  map {B C} f := ObjectProperty.homMk <| CommAlgCat.ofHom <|
    Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f.hom.hom

set_option backward.isDefEq.respectTransparency false in
private lemma tensorQuotientAlgEquiv_includeRight
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (b : B) :
    tensorQuotientAlgEquiv A I B (1 ⊗ₜ[A] b) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) b := by
  simp only [tensorQuotientAlgEquiv, AlgEquiv.ofBijective_apply]
  simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul,
    Ideal.Quotient.mkₐ_eq_mk]

private lemma locallyNilpotent_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I ≤ nilradical A) :
    (I.map f).IsLocallyNilpotent := by
  intro y hy
  rw [show I.map f = Ideal.span (f '' (I : Set A)) by
    conv_lhs => rw [← Ideal.span_eq I]
    rw [Ideal.map_span]] at hy
  refine Submodule.span_induction (p := fun z _ => IsNilpotent z) ?_ IsNilpotent.zero
    (fun _ _ _ _ ha hb => Commute.isNilpotent_add (.all _ _) ha hb)
    (fun r a _ ha => ?_) hy
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_nilradical.mp (hI hx)).map f
  · rw [smul_eq_mul]
    exact Commute.isNilpotent_mul_left (.all _ _) ha

private lemma formallyUnramified_ext_of_le_nilradical
    {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra.FinitePresentation R S]
    [Algebra.FormallyUnramified R S]
    (I : Ideal A) (hI : I ≤ nilradical A) (f g : S →ₐ[R] A)
    (h : (Ideal.Quotient.mkₐ R I).comp f = (Ideal.Quotient.mkₐ R I).comp g) : f = g := by
  obtain ⟨n, π, hπ, -⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let d : Fin n → A := fun i => f (π (MvPolynomial.X i)) - g (π (MvPolynomial.X i))
  let J : Ideal A := Ideal.span (Set.range d)
  have hJI : J ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change f (π (MvPolynomial.X i)) - g (π (MvPolynomial.X i)) ∈ I
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    exact sub_eq_zero.mpr (DFunLike.congr_fun h (π (MvPolynomial.X i)))
  have hJnil : IsNilpotent J := isNilpotent_of_fg
    (fun x hx => mem_nilradical.mp (hI hx)) hJI
    (Submodule.fg_span (Set.finite_range d))
  exact Algebra.FormallyUnramified.lift_unique J hJnil f g <| (AlgHom.cancel_right hπ).mp <|
    MvPolynomial.algHom_ext fun i ↦ Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨i, rfl⟩)

private lemma henselianRing_of_le_nilradical {A : Type*} [CommRing A]
    (I : Ideal A) (hI : I ≤ nilradical A) : HenselianRing A I := by
  have hjac : I ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.jacobson_bot]
    exact hI.trans (nilradical_le_jacobson A)
  refine ⟨hjac, fun f _ a₀ hf hdf => ?_⟩
  have hlocal : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hjac
  have hunit : IsUnit (f.derivative.eval a₀) :=
    IsUnit.of_map (Ideal.Quotient.mk I) (f.derivative.eval a₀) hdf
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hI hf)
  have haI : ∀ m, f.newtonMap^[m] a₀ - a₀ ∈ I := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', Polynomial.newtonMap_apply, sub_sub]
      simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      have hev : f.eval (f.newtonMap^[m] a₀) ∈ I := by
        have hsm : f.newtonMap^[m] a₀ ≡ a₀ [SMOD I] := (Ideal.Quotient.eq).2 ih
        have hd : f.eval (f.newtonMap^[m] a₀) - f.eval a₀ ∈ I :=
          (Ideal.Quotient.eq).1 (hsm.eval f)
        exact (sub_add_cancel (f.eval (f.newtonMap^[m] a₀)) (f.eval a₀)) ▸
          I.add_mem hd hf
      rw [show f.newtonMap^[m] a₀ -
        (Ring.inverse (f.derivative.eval (f.newtonMap^[m] a₀)) *
          f.eval (f.newtonMap^[m] a₀) + a₀) =
        (f.newtonMap^[m] a₀ - a₀) -
          Ring.inverse (f.derivative.eval (f.newtonMap^[m] a₀)) *
            f.eval (f.newtonMap^[m] a₀) by ring]
      exact I.sub_mem ih (I.mul_mem_left _ hev)
  refine ⟨f.newtonMap^[n] a₀, ?_, haI n⟩
  change f.eval (f.newtonMap^[n] a₀) = 0
  rw [← zero_dvd_iff, ← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
  exact Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
    (mem_nilradical.mp (hI hf)) hunit n

set_option backward.isDefEq.respectTransparency false in
private lemma etaleBaseChange_faithful {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ nilradical A) : (etaleBaseChange I).Faithful where
  map_injective {B C} f g h := by
    let : Algebra.Etale A B.obj := B.property
    let J : Ideal C.obj := I.map (algebraMap A C.obj)
    have hJ : J ≤ nilradical C.obj := fun x hx =>
      mem_nilradical.mpr (locallyNilpotent_map (algebraMap A C.obj) I hI x hx)
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact formallyUnramified_ext_of_le_nilradical
      (R := A) (S := B.obj) (A := C.obj) J hJ
      f.hom.hom g.hom.hom (by
        apply AlgHom.ext
        intro b
        have hb := congrArg (fun k => k.hom.hom
          ((Algebra.TensorProduct.includeRight : B.obj →ₐ[A] (A ⧸ I) ⊗[A] B.obj) b)) h
        change (Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f.hom.hom)
            (1 ⊗ₜ[A] b) =
          (Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) g.hom.hom)
            (1 ⊗ₜ[A] b) at hb
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at hb
        have hb' := congrArg (tensorQuotientAlgEquiv A I C.obj) hb
        simpa only [tensorQuotientAlgEquiv_includeRight, AlgHom.comp_apply,
          Ideal.Quotient.mkₐ_eq_mk] using hb')

set_option backward.isDefEq.respectTransparency false in
private lemma etaleBaseChange_full {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ nilradical A) : (etaleBaseChange I).Full where
  map_surjective {B C} f := by
    let : Algebra.Etale A B.obj := B.property
    let : Algebra.Etale A C.obj := C.property
    let J : Ideal C.obj := I.map (algebraMap A C.obj)
    let eC := tensorQuotientAlgEquiv A I C.obj
    let φ : (A ⧸ I) ⊗[A] B.obj →ₐ[A ⧸ I] (A ⧸ I) ⊗[A] C.obj := f.hom.hom
    let gbar : B.obj →ₐ[A] C.obj ⧸ J :=
      (((eC.toAlgHom.comp φ).restrictScalars A).comp
        (Algebra.TensorProduct.includeRight : B.obj →ₐ[A] (A ⧸ I) ⊗[A] B.obj))
    have hJ : J.IsLocallyNilpotent := locallyNilpotent_map (algebraMap A C.obj) I hI
    obtain ⟨g, hg⟩ := main_theorem07K4 A B.obj C.obj J hJ gbar
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom g), ?_⟩
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    change Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) g = f.hom.hom
    apply AlgHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x b =>
      have hb := DFunLike.congr_fun hg b
      change Ideal.Quotient.mk J (g b) = gbar b at hb
      have he := congrArg eC.symm hb
      have he' : (1 : A ⧸ I) ⊗ₜ[A] g b = φ (1 ⊗ₜ[A] b) := by
        change eC.symm (Ideal.Quotient.mk J (g b)) =
          eC.symm (eC (φ (1 ⊗ₜ[A] b))) at he
        rwa [← tensorQuotientAlgEquiv_includeRight I (g b), eC.symm_apply_apply,
          eC.symm_apply_apply] at he
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      calc
        x ⊗ₜ[A] g b = x • ((1 : A ⧸ I) ⊗ₜ[A] g b) :=
          TensorProduct.tmul_eq_smul_one_tmul x (g b)
        _ = x • φ (1 ⊗ₜ[A] b) := by rw [he']
        _ = φ (x • (1 ⊗ₜ[A] b)) := (map_smul φ x _).symm
        _ = φ (x ⊗ₜ[A] b) := by
          rw [← TensorProduct.tmul_eq_smul_one_tmul]

private lemma etaleBaseChange_essSurj {A : Type u} [CommRing A] (I : Ideal A) :
    (etaleBaseChange I).EssSurj where
  mem_essImage B := by
    have hss : Algebra.IsStandardSmoothOfRelativeDimension 0 (A ⧸ I) B.obj :=
      Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp B.property
    obtain ⟨ι, σ, _, _, P, hP⟩ := hss.out
    obtain ⟨S, _, _, Q, hQ, ⟨e⟩⟩ := etale_lift_construction A I B.obj ι σ P hP
    let hS : Algebra.Etale A S :=
      Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
        (Q.isStandardSmoothOfRelativeDimension hQ)
    exact ⟨⟨CommAlgCat.of A S, hS⟩,
      ⟨ObjectProperty.isoMk _ (CommAlgCat.isoMk e)⟩⟩

/-- **Stacks 0ALI.** If every element of `I` is nilpotent, reduction modulo `I` induces an
equivalence from étale `A`-algebras to étale `(A ⧸ I)`-algebras, and `(A, I)` is a henselian
pair. -/
@[stacks 0ALI,
  sga "1 IX 1.7" "affine case",
  ega "IV 18.1.2" "affine case",
  sga "1 IX 4.10" "affine, nilpotent ideal"]
theorem etaleBaseChange_isEquivalence_and_henselianRing_of_le_nilradical {A : Type u} [CommRing A]
  (I : Ideal A)
    (hI : I ≤ nilradical A) :
    (etaleBaseChange I).IsEquivalence ∧ HenselianRing A I :=
  ⟨Functor.IsEquivalence.mk (faithful := etaleBaseChange_faithful I hI)
    (full := etaleBaseChange_full I hI) (essSurj := etaleBaseChange_essSurj I),
    henselianRing_of_le_nilradical I hI⟩

end

section

/-- A unit modulo an ideal contained in the nilradical is a unit. -/
public lemma isUnit_of_quotient_of_le_nilradical
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) {x : R}
    (h : IsUnit ((Ideal.Quotient.mk I) x)) : IsUnit x := by
  obtain ⟨y0, hy0⟩ := h.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y0
  have hz : (Ideal.Quotient.mk I) (x * y - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hy0]
    ring
  have hnil : IsNilpotent (x * y - 1) :=
    mem_nilradical.mp (hI ((Ideal.Quotient.eq_zero_iff_mem).mp hz))
  have hu : IsUnit (x * y) := by
    have hh := hnil.isUnit_one_add
    rwa [show (1 : R) + (x * y - 1) = x * y by ring] at hh
  exact isUnit_of_mul_isUnit_left hu

/-- A unit image under a surjection `φ` makes the class modulo `ker φ` a unit. -/
private lemma isUnit_mk_ker_of_isUnit_map
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) {x : R} (hx : IsUnit (φ x)) :
    IsUnit (Ideal.Quotient.mk (RingHom.ker φ) x) := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨z, rfl⟩ := hφ y
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, RingHom.mem_ker, map_sub,
    map_mul, map_one, hy, sub_self]

/-- **Units lift along a surjection whose kernel lies in the nilradical.** If `φ : R →+* S` is
surjective with `ker φ ≤ nilradical R`, then `x : R` is a unit as soon as `φ x` is. -/
public lemma isUnit_of_map_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hk : RingHom.ker φ ≤ nilradical R)
    {x : R} (hx : IsUnit (φ x)) : IsUnit x := by
  exact isUnit_of_quotient_of_le_nilradical (RingHom.ker φ) hk
    (isUnit_mk_ker_of_isUnit_map φ hφ hx)

/-- **A surjection whose kernel lies in the nilradical is a local homomorphism.** The
`IsLocalHom` packaging of `isUnit_of_map_of_surjective_of_ker_le_nilradical`, which is what
consumers taking locality as an instance or as a `ReflectsUnitsObj` hypothesis need.

No local ring is involved: `IsLocalHom` is reflection of units and nothing more. Mathlib's
`IsLocalHom.of_surjective` is a different statement — it assumes `R` local and `S` nontrivial
and says nothing about the kernel. -/
public theorem isLocalHom_of_surjective_of_ker_le_nilradical
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hk : RingHom.ker φ ≤ nilradical R) : IsLocalHom φ :=
  ⟨fun _ hx ↦ isUnit_of_map_of_surjective_of_ker_le_nilradical φ hφ hk hx⟩

/-- **A surjection with square-zero kernel is a local homomorphism.** This is the hypothesis
shape a square-zero extension `𝒜 ⟶ 𝒪` presents — the kernel `𝓘` satisfies `𝓘 ^ 2 = 0`, so each
of its elements is nilpotent with exponent `2` — and it says that a section of `𝒜` is a unit
exactly when its image in `𝒪` is: the forward implication is `IsUnit.map`, and this is the
reflection, which is the content.

Surjectivity cannot be dropped: the inclusion `ℤ → ℚ` has kernel `⊥`, hence square-zero, and
every nonzero integer has invertible image. -/
public theorem isLocalHom_of_surjective_of_forall_sq_eq_zero
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hk : ∀ x ∈ RingHom.ker φ, x ^ 2 = 0) : IsLocalHom φ :=
  isLocalHom_of_surjective_of_ker_le_nilradical φ hφ
    fun x hx ↦ mem_nilradical.mpr ⟨2, hk x hx⟩

private theorem exists_root_lift
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (hk : RingHom.ker φ ≤ nilradical R)
    (f : R[X]) (hf : f.Monic) (x : S) (hx : (f.map φ).IsRoot x)
    (hd : IsUnit ((f.map φ).derivative.eval x)) :
    ∃ y : R, f.IsRoot y ∧ φ y = x ∧ IsUnit (f.derivative.eval y) := by
  let _ : HenselianRing R (RingHom.ker φ) := henselianRing_of_le_nilradical _ hk
  obtain ⟨z, rfl⟩ := hφ x
  have hz : f.eval z ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, ← eval_map_apply, hx.eq_zero]
  have hφD : ∀ u, φ (f.derivative.eval u) = (f.map φ).derivative.eval (φ u) := fun u ↦ by
    rw [derivative_map, eval_map_apply]
  have hq := isUnit_mk_ker_of_isUnit_map φ hφ (x := f.derivative.eval z) (by rwa [hφD])
  obtain ⟨y, hy, hyz⟩ := HenselianRing.is_henselian f hf z hz hq
  have hyz' : φ y = φ z := by
    rw [← sub_eq_zero, ← map_sub]
    exact RingHom.mem_ker.mp hyz
  refine ⟨y, hy, hyz', isUnit_of_quotient_of_le_nilradical _ hk ?_⟩
  rw [show Ideal.Quotient.mk (RingHom.ker φ) (f.derivative.eval y) =
      Ideal.Quotient.mk (RingHom.ker φ) (f.derivative.eval z) from
    Ideal.Quotient.eq.2 (by rw [RingHom.mem_ker, map_sub, hφD, hφD, hyz', sub_self])]
  exact hq

/-- The projections of a cone over `F` commute with the transition maps. -/
private lemma map_π_apply (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F) {i j : ℕ} (h : i ≤ j)
    (x : c.pt) :
    (F.map (homOfLE h).op).hom ((c.π.app (.op j)).hom x) = (c.π.app (.op i)).hom x :=
  congrArg (fun q : c.pt ⟶ F.obj (.op i) => q.hom x) (c.w (homOfLE h).op)

private theorem exists_lift_of_compatible
    (F : Functor ℕᵒᵖ CommRingCat.{u}) (c : Cone F) (hc : IsLimit c)
    (a : ∀ j, F.obj j)
    (ha : ∀ (i j : ℕ) (h : i ≤ j),
      (F.map (homOfLE h).op).hom (a (Opposite.op j)) = a (Opposite.op i)) :
    ∃ x : c.pt, ∀ j, (c.π.app j).hom x = a j := by
  let s : Cone F :=
    { pt := CommRingCat.of (Polynomial c.pt)
      π :=
        { app := fun j ↦ CommRingCat.ofHom (eval₂RingHom (c.π.app j).hom (a j))
          naturality := by
            rintro ⟨i⟩ ⟨j⟩ ⟨h⟩
            ext p
            induction p using Polynomial.induction_on' with
            | add p q hp hq => simp only [map_add, hp, hq]
            | monomial m x =>
              change eval₂ (c.π.app (Opposite.op j)).hom (a (Opposite.op j))
                  (monomial m x) =
                (F.map (Opposite.op h)).hom
                  (eval₂ (c.π.app (Opposite.op i)).hom (a (Opposite.op i))
                    (monomial m x))
              rw [eval₂_monomial, eval₂_monomial, map_mul, map_pow]
              congr 1
              · exact congrArg (fun q ↦ q.hom x) (c.w (Opposite.op h)).symm
              · exact congrArg (· ^ m) (by
                  rw [← homOfLE_leOfHom h]
                  exact (ha _ _ h.le).symm) } }
  refine ⟨(hc.lift s).hom X, fun j ↦ ?_⟩
  have h := congrArg (fun q ↦ q.hom X) (hc.fac s j)
  dsimp [s] at h
  simpa only [eval₂_X] using h

private theorem exists_simple_root_lift_step
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F)
    (hF : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤
          nilradical (F.obj (.op (n + 1))))
    (f : c.pt[X]) (hf : f.Monic) (m : ℕ)
    (x : F.obj (.op m))
    (hx : (f.map (c.π.app (.op m)).hom).IsRoot x)
    (hd : IsUnit ((f.map (c.π.app (.op m)).hom).derivative.eval x)) :
    ∃ y : F.obj (.op (m + 1)),
      (F.map (homOfLE (Nat.le_succ m)).op).hom y = x ∧
      (f.map (c.π.app (.op (m + 1))).hom).IsRoot y ∧
      IsUnit ((f.map (c.π.app (.op (m + 1))).hom).derivative.eval y) := by
  let φ := (F.map (homOfLE (Nat.le_succ m)).op).hom
  have he :
      (f.map (c.π.app (.op (m + 1))).hom).map φ =
        f.map (c.π.app (.op m)).hom := by
    rw [Polynomial.map_map]
    congr 1
    exact congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ m)).op)
  obtain ⟨y, hy, hxy, hdy⟩ := exists_root_lift φ (hF m).1 (hF m).2
    (f.map (c.π.app (.op (m + 1))).hom)
    (hf.map _) x (by simpa only [he] using hx) (by simpa only [he] using hd)
  exact ⟨y, hxy, hy, hdy⟩

private theorem exists_compatible_simple_roots
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F)
    (hF : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤
          nilradical (F.obj (.op (n + 1))))
    (f : c.pt[X]) (hf : f.Monic) (n : ℕ) (a₀ : c.pt)
    (hr : (f.map (c.π.app (.op n)).hom).IsRoot ((c.π.app (.op n)).hom a₀))
    (hu : IsUnit ((f.map (c.π.app (.op n)).hom).derivative.eval
      ((c.π.app (.op n)).hom a₀))) :
    ∃ a : ∀ m : ℕ, F.obj (.op m),
      (∀ m, (F.map (homOfLE (Nat.le_succ m)).op).hom (a (m + 1)) = a m) ∧
      (∀ m, m ≤ n → a m = (c.π.app (.op m)).hom a₀) ∧
      (∀ m, n ≤ m → (f.map (c.π.app (.op m)).hom).IsRoot (a m)) := by
  classical
  let P (m : ℕ) := {x : F.obj (.op m) //
    (m ≤ n → x = (c.π.app (.op m)).hom a₀) ∧
    (n ≤ m → (f.map (c.π.app (.op m)).hom).IsRoot x) ∧
    (n ≤ m → IsUnit ((f.map (c.π.app (.op m)).hom).derivative.eval x))}
  let p₀ : P 0 := by
    refine ⟨(c.π.app (.op 0)).hom a₀, fun _ => rfl, fun hn => ?_, fun hn => ?_⟩
    · obtain rfl : n = 0 := by omega
      exact hr
    · obtain rfl : n = 0 := by omega
      exact hu
  let step (m : ℕ) (p : P m) :
      {q : P (m + 1) //
        (F.map (homOfLE (Nat.le_succ m)).op).hom q.val = p.val} := by
    by_cases h : m + 1 ≤ n
    · refine ⟨⟨(c.π.app (.op (m + 1))).hom a₀, fun _ => rfl, fun hn => ?_, fun hn => ?_⟩, ?_⟩
      · obtain rfl : m + 1 = n := by omega
        exact hr
      · obtain rfl : m + 1 = n := by omega
        exact hu
      · have hm : m ≤ n := by omega
        rw [p.property.1 hm]
        exact map_π_apply F c _ a₀
    · have hm : n ≤ m := by omega
      let e := exists_simple_root_lift_step F c hF f hf m p.val
        (p.property.2.1 hm) (p.property.2.2 hm)
      let y := Classical.choose e
      have he := Classical.choose_spec e
      exact ⟨⟨y, fun _ => by omega, fun _ => he.2.1, fun _ => he.2.2⟩, he.1⟩
  let p : (m : ℕ) → P m := Nat.rec p₀ (fun m x => (step m x).val)
  refine ⟨fun m => (p m).val, ?_, ?_, ?_⟩
  · intro m
    change (F.map (homOfLE (Nat.le_succ m)).op).hom (step m (p m)).val.val =
      (p m).val
    exact (step m (p m)).property
  · intro m hm
    exact (p m).property.1 hm
  · intro m hm
    exact (p m).property.2.1 hm

private theorem compatible_of_adjacent
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (a : ∀ m : ℕ, F.obj (.op m))
    (ha : ∀ m, (F.map (homOfLE (Nat.le_succ m)).op).hom (a (m + 1)) = a m) :
    ∀ (i j : ℕ) (h : i ≤ j),
      (F.map (homOfLE h).op).hom (a j) = a i := by
  intro i j h
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    have he : (homOfLE (Nat.le_succ j)).op ≫ (homOfLE hj).op =
        (homOfLE (Nat.le_trans hj (Nat.le_succ j))).op :=
      Subsingleton.elim _ _
    change (F.map (homOfLE (Nat.le_trans hj (Nat.le_succ j))).op).hom (a (j + 1)) = a i
    rw [← he, Functor.map_comp]
    change (F.map (homOfLE hj).op).hom
      ((F.map (homOfLE (Nat.le_succ j)).op).hom (a (j + 1))) = a i
    rwa [ha j]

private theorem isUnit_of_projection
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F) (hc : IsLimit c)
    (hF : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤
          nilradical (F.obj (.op (n + 1))))
    (n : ℕ) (x : c.pt) (hx : IsUnit ((c.π.app (.op n)).hom x)) : IsUnit x := by
  rw [CommRingCat.Limits.isUnit_iff_forall_isUnit F hc]
  intro j
  obtain ⟨m⟩ := j
  by_cases hmn : m ≤ n
  · rw [← map_π_apply F c hmn x]
    exact hx.map _
  · have hnm : n ≤ m := by omega
    let P (k : ℕ) := IsUnit ((c.π.app (.op (n + k))).hom x)
    have hb : P 0 := by simpa only [P, Nat.add_zero] using hx
    have hs : ∀ k, P k → P (k + 1) := by
      intro k hk
      refine isUnit_of_map_of_surjective_of_ker_le_nilradical _
        (hF (n + k)).1 (hF (n + k)).2 ?_
      exact (map_π_apply F c (Nat.le_succ (n + k)) x).symm ▸ hk
    have ht : ∀ k, P k := Nat.rec hb hs
    have ht' : IsUnit ((c.π.app (.op (n + (m - n)))).hom x) := ht (m - n)
    rwa [Nat.add_sub_of_le hnm] at ht'

/-- **Stacks 0CT7.** Let `A` be the inverse limit of a sequence of commutative rings whose
transition maps are surjective with locally nilpotent kernels. Then the pair consisting of `A`
and the kernel of any limit projection `A → Aₙ` is henselian. -/
@[stacks 0CT7]
theorem henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F) (hc : IsLimit c)
    (hF : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
        RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤
          nilradical (F.obj (.op (n + 1)))) (n : ℕ) :
    HenselianRing c.pt (RingHom.ker (c.π.app (.op n)).hom) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    apply isUnit_of_projection F c hc hF n
    rw [map_add, map_mul, map_one, RingHom.mem_ker.mp hx, zero_mul, zero_add]
    exact isUnit_one
  · intro f hf a₀ hfa hdu
    let πn := (c.π.app (.op n)).hom
    have hr : (f.map πn).IsRoot (πn a₀) := by
      rw [Polynomial.IsRoot.def, eval_map_apply]
      exact RingHom.mem_ker.mp hfa
    have hu : IsUnit ((f.map πn).derivative.eval (πn a₀)) := by
      have h := hdu.map (RingHom.kerLift πn)
      rw [RingHom.kerLift_mk] at h
      simpa only [derivative_map, eval_map_apply] using h
    obtain ⟨a, hadj, hlow, hroot⟩ :=
      exists_compatible_simple_roots F c hF f hf n a₀ hr hu
    obtain ⟨x, hx⟩ := exists_lift_of_compatible F c hc
      (fun j => a (Opposite.unop j)) (compatible_of_adjacent F a hadj)
    refine ⟨x, ?_, ?_⟩
    · rw [Polynomial.IsRoot.def]
      apply Concrete.isLimit_ext F hc
      intro j
      obtain ⟨m⟩ := j
      let k := max n m
      have hk : (c.π.app (.op k)).hom (f.eval x) = 0 := by
        rw [← eval_map_apply, hx (.op k)]
        exact (hroot k (le_max_left n m)).eq_zero
      change (c.π.app (.op m)).hom (f.eval x) =
        (c.π.app (.op m)).hom (0 : c.pt)
      rw [map_zero, ← map_π_apply F c (le_max_right n m), hk, map_zero]
    · rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact (hx (.op n)).trans (hlow n le_rfl)

end

end
