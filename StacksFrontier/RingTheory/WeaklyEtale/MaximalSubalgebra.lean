module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GeometricallyConnected
public import StacksFrontier.RingTheory.Smooth.Lifting
public import StacksFrontier.RingTheory.TensorProduct.Connected
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.Field

@[expose] public section

/-!
# The maximal weakly étale subalgebra

Every algebra over a field contains a greatest weakly étale subalgebra. Over a field, taking
the maximal weakly étale subalgebra is functorial: it commutes with filtered colimits,
reduction, and finite products, and it is compatible with passage to a subalgebra. For a
connected nonzero algebra, its maximal weakly étale subalgebra is a separable algebraic field
extension of the base field. Finally, the maximal weakly étale subalgebra commutes with
extension of the base field.

## Main definitions

No new definitions are introduced.

## Main results

* `exists_greatest_weaklyEtale_subalgebra` (Stacks 0CKS) gives the greatest weakly étale
  subalgebra of an algebra over a field.
* `exists_maximalWeaklyEtaleSubalgebraFunctor` (Stacks 0CKT) packages the maximal weakly étale
  subalgebras into a functor and records its principal structural properties.
* `maximalWeaklyEtaleSubalgebra_baseChange` (Stacks 0CKU) states that scalar extension of the
  maximal weakly étale subalgebra is the maximal weakly étale subalgebra after scalar
  extension.

## Implementation notes

The maximal subalgebra in the source is stated here as a greatest element: the construction
in the source contains every weakly étale subalgebra, and hence establishes this stronger
order-theoretic characterization directly.

The inclusions of the maximal weakly étale subalgebras form a natural transformation to the
identity functor. Thus the induced maps, including their identity and composition laws, are
canonical. Compatibility with subalgebras is expressed elementwise as equality between the
inverse image of the maximal subalgebra and the maximal subalgebra of the source. The colimit
and finite-product assertions are expressed as preservation properties of the functor.

The source's proof of the connected case invokes Tag 0CKR, whose precise conclusion allows the
zero ring as well as a field. Accordingly, the conclusion below retains that necessary zero-ring
alternative; for a nonzero algebra it gives exactly the field conclusion stated in the source.
The final placeholder “add more here” in the source has no mathematical assertion to formalize.

Scalar extension is written in the order `L ⊗[K] B`; symmetry of tensor products identifies
this canonically with the source's `B ⊗[K] L`. Its canonical map into `L ⊗[K] A` is injective,
and maximality is expressed by saying that every weakly étale `L`-subalgebra of the target
consists of elements in its image.

Since the three groups of results use incompatible `open` directives and option settings, each
is kept in its own section: `GreatestSubalgebra`, `MaximalSubalgebraFunctor` and `BaseChange`.

## References

* [The Stacks Project, Tag 0CKS](https://stacks.math.columbia.edu/tag/0CKS)
* [The Stacks Project, Tag 0CKT](https://stacks.math.columbia.edu/tag/0CKT)
* [The Stacks Project, Tag 0CKU](https://stacks.math.columbia.edu/tag/0CKU)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

universe u v w

/-- A quotient of a weakly étale algebra over a field is weakly étale. -/
private lemma weaklyEtale_of_surjective {K B Q : Type*} [Field K] [CommRing B] [Algebra K B]
    [CommRing Q] [Algebra K Q] (hB : Algebra.WeaklyEtale K B) (f : B →ₐ[K] Q)
    (hf : Function.Surjective f) : Algebra.WeaklyEtale K Q :=
  (structure_of_weaklyEtale_over_field K B hB).2.2.2.2.1.2 Q ⟨f, hf⟩

/-- A subalgebra of a weakly étale algebra over a field is weakly étale. -/
private lemma weaklyEtale_subalgebra {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (hB : Algebra.WeaklyEtale K B) (S : Subalgebra K B) : Algebra.WeaklyEtale K S :=
  (structure_of_weaklyEtale_over_field.{_, _, 0} K B hB).2.2.2.2.1.1 S

/-- The range of an algebra map out of a weakly étale algebra over a field is weakly étale. -/
private lemma weaklyEtale_range {K B A : Type*} [Field K] [CommRing B] [Algebra K B]
    [CommRing A] [Algebra K A] (hB : Algebra.WeaklyEtale K B) (f : B →ₐ[K] A) :
    Algebra.WeaklyEtale K f.range :=
  weaklyEtale_of_surjective hB f.rangeRestrict f.rangeRestrict_surjective

/-- An algebra over a field that embeds in a weakly étale algebra is weakly étale. -/
private lemma weaklyEtale_of_injective
    {K R S : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (f : R →ₐ[K] S) (hf : Function.Injective f)
    (hS : Algebra.WeaklyEtale K S) : Algebra.WeaklyEtale K R :=
  weaklyEtale_of_surjective (weaklyEtale_subalgebra hS f.range)
    (AlgEquiv.ofInjective f hf).symm.toAlgHom (AlgEquiv.ofInjective f hf).symm.surjective

/-- The preimage of a weakly étale subalgebra under an injective algebra map is weakly étale. -/
private lemma weaklyEtale_comap
    {K R S : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (D : Subalgebra K S)
    (hD : Algebra.WeaklyEtale K D) (f : R →ₐ[K] S) (hf : Function.Injective f) :
    Algebra.WeaklyEtale K (D.comap f) := by
  let g : D.comap f →ₐ[K] D :=
    (f.comp (D.comap f).val).codRestrict D fun x ↦ x.property
  exact weaklyEtale_of_injective g (fun x y h ↦ Subtype.ext (hf (congrArg Subtype.val h))) hD

section GreatestSubalgebra

open CategoryTheory CategoryTheory.Limits

/-- An algebra over a field has a greatest weakly étale subalgebra. -/
@[stacks 0CKS]
theorem exists_greatest_weaklyEtale_subalgebra
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] :
    ∃ Bmax : Subalgebra K A,
      Algebra.WeaklyEtale K Bmax ∧
        ∀ B : Subalgebra K A, Algebra.WeaklyEtale K B → B ≤ Bmax := by
  let ι := { B : Subalgebra K A // Algebra.WeaklyEtale K B }
  have hbot : Algebra.WeaklyEtale K (⊥ : Subalgebra K A) := by
    simpa using weaklyEtale_range (inferInstance : Algebra.WeaklyEtale K K) (Algebra.ofId K A)
  let : Nonempty ι := ⟨⟨⊥, hbot⟩⟩
  let : IsDirected ι (· ≤ ·) := by
    refine ⟨fun B₁ B₂ ↦ ?_⟩
    let f : TensorProduct K (B₁.1) (B₂.1) →ₐ[K] A :=
      Algebra.TensorProduct.productMap B₁.1.val B₂.1.val
    have ht : Algebra.WeaklyEtale K (TensorProduct K (B₁.1) (B₂.1)) := by
      rcases structure_of_weaklyEtale_over_field K B₁.1 B₁.2 with
        ⟨_, _, _, _, _, ht⟩
      exact ht B₂.1 B₂.2
    refine ⟨⟨f.range, weaklyEtale_range ht f⟩, ?_, ?_⟩
    · intro x hx
      change x ∈ f.range
      rw [← B₁.1.range_val] at hx
      rw [Algebra.TensorProduct.productMap_range]
      exact (le_sup_left : B₁.1.val.range ≤ B₁.1.val.range ⊔ B₂.1.val.range) hx
    · intro x hx
      change x ∈ f.range
      rw [← B₂.1.range_val] at hx
      rw [Algebra.TensorProduct.productMap_range]
      exact (le_sup_right : B₂.1.val.range ≤ B₁.1.val.range ⊔ B₂.1.val.range) hx
  have hdir : Directed (· ≤ ·) (fun i : ι ↦ i.1) := fun i j ↦ directed_of (· ≤ ·) i j
  let F : ι ⥤ CommAlgCat.{v} K :=
    { obj := fun B ↦ CommAlgCat.of K B.1
      map := fun f ↦ CommAlgCat.ofHom (Subalgebra.inclusion f.le)
      map_id := by intros; ext; rfl
      map_comp := by intros; ext; rfl }
  let S : Subalgebra K A := ⨆ i : ι, i.1
  let c : Cocone F :=
    Cocone.mk (CommAlgCat.of K S)
      { app := fun B ↦ CommAlgCat.ofHom (Subalgebra.inclusion (le_iSup (fun i : ι ↦ i.1) B))
        naturality := by intros; ext; rfl }
  have hcompat (s : Cocone F) (i j : ι) (h : i.1 ≤ j.1) :
      (s.ι.app i).hom = (s.ι.app j).hom.comp (Subalgebra.inclusion h) := by
    ext x
    have hn := s.ι.naturality (homOfLE h)
    simpa [F] using DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hn.symm) x
  have hc : IsColimit c := by
    refine IsColimit.mk
      (fun s ↦ CommAlgCat.ofHom <|
        Subalgebra.iSupLift (fun i : ι ↦ i.1) hdir
          (fun i ↦ (s.ι.app i).hom) (hcompat s) S le_rfl) ?_ ?_
    · intro s i
      exact CommAlgCat.hom_ext <| Subalgebra.iSupLift_comp_inclusion
        (K := fun i : ι ↦ i.1) (dir := hdir)
        (hf := hcompat s)
        (i := i) (h := le_iSup (fun i : ι ↦ i.1) i)
    · intro s m hm
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      have hx : (x : A) ∈ ⨆ i : ι, i.1 := x.2
      rw [← SetLike.mem_coe,
        Subalgebra.coe_iSup_of_directed (K := fun i : ι ↦ i.1) hdir] at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      let y : i.1 := ⟨x, hi⟩
      have he := congrArg CommAlgCat.Hom.hom (hm i)
      have hev := DFunLike.congr_fun he y
      change (m.hom x) =
        Subalgebra.iSupLift (fun i : ι ↦ i.1) hdir (fun i ↦ (s.ι.app i).hom)
          (hcompat s) S le_rfl x
      rw [Subalgebra.iSupLift_of_mem (K := fun i : ι ↦ i.1) (i := i) (hx := hi)]
      calc
        m.hom x = m.hom ((c.ι.app i).hom y) := rfl
        _ = (s.ι.app i).hom y := by simpa using hev
  have hS : Algebra.WeaklyEtale K S :=
    (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v} K).2.2
      ι F c hc (fun B ↦ B.2)
  refine ⟨S, hS, ?_⟩
  intro B hB x hx
  let i : ι := ⟨B, hB⟩
  exact le_iSup (fun i : ι ↦ i.1) i hx

end GreatestSubalgebra

section MaximalSubalgebraFunctor

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TensorProduct

private noncomputable def maxSubalgebra (K : Type u) [Field K]
    (A : CommAlgCat.{v} K) : Subalgebra K A :=
  (exists_greatest_weaklyEtale_subalgebra K A).choose

private lemma maxSubalgebra_weaklyEtale (K : Type u) [Field K]
    (A : CommAlgCat.{v} K) : Algebra.WeaklyEtale K (maxSubalgebra K A) :=
  (exists_greatest_weaklyEtale_subalgebra K A).choose_spec.1

private lemma le_maxSubalgebra (K : Type u) [Field K] (A : CommAlgCat.{v} K)
    (S : Subalgebra K A) (hS : Algebra.WeaklyEtale K S) : S ≤ maxSubalgebra K A :=
  (exists_greatest_weaklyEtale_subalgebra K A).choose_spec.2 S hS

private lemma map_mem_maxSubalgebra_of_weaklyEtale (K : Type u) [Field K]
    {S : Type v} [CommRing S] [Algebra K S] (hS : Algebra.WeaklyEtale K S)
    (B : CommAlgCat.{v} K) (g : S →ₐ[K] B) (s : S) : g s ∈ maxSubalgebra K B :=
  le_maxSubalgebra K B g.range (weaklyEtale_range hS g) ⟨s, rfl⟩

private lemma map_mem_maxSubalgebra (K : Type u) [Field K]
    (A B : CommAlgCat.{v} K) (f : A ⟶ B)
    (x : maxSubalgebra K A) : f (x : A) ∈ maxSubalgebra K B :=
  map_mem_maxSubalgebra_of_weaklyEtale K (maxSubalgebra_weaklyEtale K A) B
    (f.hom.comp (maxSubalgebra K A).val) x

private noncomputable def maxMap (K : Type u) [Field K]
    (A B : CommAlgCat.{v} K) (f : A ⟶ B) :
    maxSubalgebra K A →ₐ[K] maxSubalgebra K B :=
  (f.hom.comp (maxSubalgebra K A).val).codRestrict
    (maxSubalgebra K B) (map_mem_maxSubalgebra K A B f)

private noncomputable def maxFunctor (K : Type u) [Field K] :
    CommAlgCat.{v} K ⥤ CommAlgCat.{v} K where
  obj A := CommAlgCat.of K (maxSubalgebra K A)
  map f := CommAlgCat.ofHom (maxMap K _ _ f)
  map_id := by
    intro A
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro A B C f g
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    rfl

private noncomputable def maxInclusion (K : Type u) [Field K] :
    maxFunctor K ⟶ 𝟭 (CommAlgCat.{v} K) where
  app A := CommAlgCat.ofHom (maxSubalgebra K A).val
  naturality := by
    intro A B f
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl

private lemma max_connected (K : Type u) [Field K] (A : CommAlgCat.{v} K)
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Subsingleton A ∨
      (IsField (maxFunctor K |>.obj A) ∧
        Algebra.IsSeparable K (maxFunctor K |>.obj A) ∧
          Algebra.IsAlgebraic K (maxFunctor K |>.obj A)) := by
  have hB : ∀ e : maxSubalgebra K A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    exact (hA (e : A) (by simpa [IsIdempotentElem] using congrArg Subtype.val he)).imp
      Subtype.ext Subtype.ext
  obtain ⟨_, _, _, h, _, _⟩ :=
    structure_of_weaklyEtale_over_field.{u,v,v} K (maxSubalgebra K A)
      (maxSubalgebra_weaklyEtale K A)
  rcases h.1.mpr hB with hzero | hfield
  · left
    have : Subsingleton (maxSubalgebra K A) := hzero
    exact subsingleton_of_zero_eq_one
      (congrArg Subtype.val (Subsingleton.elim (0 : maxSubalgebra K A) 1))
  · exact .inr ⟨hfield, h.2 hfield⟩

/-- Weak étaleness transfers along an isomorphism of algebras: if `A` is weakly étale over the
field `K` and `e : A ≃ₐ[K] B`, then `B` is weakly étale over `K`. -/
lemma Algebra.WeaklyEtale.of_algEquiv (K : Type*) [Field K]
    {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : Algebra.WeaklyEtale K A) (e : A ≃ₐ[K] B) :
    Algebra.WeaklyEtale K B := by
  let m := (Algebra.TensorProduct.congr e e).toAlgHom
  have hm : Function.Bijective m := (Algebra.TensorProduct.congr e e).bijective
  have hcomm :
      (Algebra.TensorProduct.lmul' K (S := B)).comp m =
        e.toAlgHom.comp (Algebra.TensorProduct.lmul' K (S := A)) := by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [m]
    · ext a
      simp [m]
  have hf : (e.toAlgHom.comp (Algebra.TensorProduct.lmul' K (S := A))).Flat :=
    RingHom.Flat.comp (Algebra.WeaklyEtale.flat_lmul' K A) (.of_bijective e.bijective)
  rw [← hcomm] at hf
  exact ⟨inferInstance, (RingHom.Flat.comp_iff_of_bijective_right hm).mp hf⟩

private lemma mem_maxSubalgebra_iff_of_injective (K : Type u) [Field K]
    (A B : CommAlgCat.{v} K) (f : A ⟶ B) (hf : Function.Injective f)
    (x : A) : x ∈ maxSubalgebra K A ↔ f x ∈ maxSubalgebra K B := by
  refine ⟨fun hx ↦ map_mem_maxSubalgebra K A B f ⟨x, hx⟩, fun hx ↦ ?_⟩
  · exact le_maxSubalgebra K A ((maxSubalgebra K B).comap f.hom)
      (weaklyEtale_comap _ (maxSubalgebra_weaklyEtale K B) f.hom hf) hx

private lemma weaklyEtale_of_localizations
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (s : ι → S) (hs : Ideal.span (Set.range s) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra S (T i)] [∀ i, IsScalarTower R S (T i)]
    [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.WeaklyEtale R (T i)] :
    Algebra.WeaklyEtale R S := by
  classical
  let idx : Set.range s → ι := fun r ↦ r.2.choose
  have hidx (r : Set.range s) : s (idx r) = r.1 := r.2.choose_spec
  have hloc : ∀ r : Set.range s, IsLocalization.Away r.1 (T (idx r)) := fun r =>
    hidx r ▸ (inferInstance : IsLocalization.Away (s (idx r)) (T (idx r)))
  refine ⟨?_, ?_⟩
  · exact Module.flat_of_isLocalized_span S S (Set.range s) hs
      (fun r ↦ T (idx r)) (fun r ↦ Algebra.linearMap S (T (idx r)))
      (fun _ ↦ inferInstance)
  · algebraize [(Algebra.TensorProduct.lmul' R (S := S)).toRingHom]
    have : IsScalarTower (S ⊗[R] S) S S := .right
    let alg (r : Set.range s) : Algebra (S ⊗[R] S) (T (idx r)) :=
      ((algebraMap S (T (idx r))).comp (algebraMap (S ⊗[R] S) S)).toAlgebra
    have tower (r : Set.range s) : IsScalarTower (S ⊗[R] S) S (T (idx r)) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have flat_T (r : Set.range s) : Module.Flat (S ⊗[R] S) (T (idx r)) := by
      let i := idx r
      let α : S →ₐ[R] T i := IsScalarTower.toAlgHom R S (T i)
      have hα : α.toRingHom.Flat :=
        RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (T i) (.powers (s i)))
      have hαα : (Algebra.TensorProduct.map α α).toRingHom.Flat :=
        RingHom.Flat.tensorProductMap hα hα
      have hlmul : (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.Flat :=
        Algebra.WeaklyEtale.flat_lmul' R (T i)
      have hcomp : ((Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
          (Algebra.TensorProduct.map α α).toRingHom).Flat :=
        RingHom.Flat.comp hαα hlmul
      have hα_eq : α.toRingHom.comp (Algebra.TensorProduct.lmul' R (S := S)).toRingHom =
          (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
            (Algebra.TensorProduct.map α α).toRingHom := by
        ext x
        all_goals
          simp [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul]
      have heq : algebraMap (S ⊗[R] S) (T i) =
          (Algebra.TensorProduct.lmul' R (S := T i)).toRingHom.comp
            (Algebra.TensorProduct.map α α).toRingHom :=
        hα_eq
      rw [← RingHom.flat_algebraMap_iff, heq]
      exact hcomp
    exact Module.flat_of_isLocalized_span (R := S ⊗[R] S) S S (Set.range s) hs
      (fun r ↦ T (idx r)) (fun r ↦ Algebra.linearMap S (T (idx r))) flat_T

private lemma weaklyEtale_pi {R : Type u} [CommRing R]
    {ι : Type v} [Finite ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Algebra.WeaklyEtale R (B i)] :
    Algebra.WeaklyEtale R (∀ i, B i) := by
  classical
  let (i : ι) : Algebra (∀ j, B j) (B i) := (Pi.evalAlgHom R B i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : ∀ j, B j) (B i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom B i).surjective)
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  exact weaklyEtale_of_localizations _ (Ideal.span_single_eq_top B) (fun i ↦ B i)

private lemma preserves_finite_products (K : Type u) [Field K]
    (J : Type v) [Finite J] :
    PreservesLimitsOfShape (Discrete J) (maxFunctor.{u,v} K) := by
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  let P := ∀ j : J, maxSubalgebra K (F.obj ⟨j⟩)
  have hP : Algebra.WeaklyEtale K P := by
    let (j : J) : Algebra.WeaklyEtale K (maxSubalgebra K (F.obj ⟨j⟩)) :=
      maxSubalgebra_weaklyEtale K (F.obj ⟨j⟩)
    exact weaklyEtale_pi
  let t : Cone F :=
    { pt := CommAlgCat.of K P
      π := Discrete.natTrans (fun j ↦ CommAlgCat.ofHom <|
        (maxSubalgebra K (F.obj j)).val.comp
          (Pi.evalAlgHom K (fun k : J ↦ maxSubalgebra K (F.obj ⟨k⟩)) j.as)) }
  let g : P →ₐ[K] c.pt := (hc.lift t).hom
  let g' : P →ₐ[K] maxSubalgebra K c.pt :=
    g.codRestrict _ (map_mem_maxSubalgebra_of_weaklyEtale K hP c.pt g)
  have hfac (s : Cone (F ⋙ maxFunctor.{u,v} K)) (j : Discrete J) :
      CommAlgCat.ofHom (g'.comp (AlgHom.pi fun k : J ↦ (s.π.app ⟨k⟩).hom)) ≫
        (maxFunctor K).map (c.π.app j) = s.π.app j := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    let h : s.pt →ₐ[K] P := AlgHom.pi (fun k : J ↦ (s.π.app ⟨k⟩).hom)
    change (c.π.app j) (g (h x)) =
      ((maxSubalgebra K (F.obj j)).val) ((s.π.app j) x)
    exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hc.fac t j)) (h x)
  refine IsLimit.mk (fun s ↦ CommAlgCat.ofHom
    (g'.comp (AlgHom.pi fun j : J ↦ (s.π.app ⟨j⟩).hom))) hfac fun s m hm ↦ ?_
  let L : s.pt ⟶ (maxFunctor K).obj c.pt :=
    CommAlgCat.ofHom (g'.comp (AlgHom.pi fun j : J ↦ (s.π.app ⟨j⟩).hom))
  have hproj : m ≫ (maxInclusion K).app c.pt = L ≫ (maxInclusion K).app c.pt := by
    refine hc.hom_ext fun j ↦ CommAlgCat.hom_ext <| AlgHom.ext fun x ↦ ?_
    have hmx := congrArg Subtype.val (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hm j)) x)
    have hLx := congrArg Subtype.val
      (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hfac s j)) x)
    change (c.π.app j) (Subtype.val (m x)) = Subtype.val ((s.π.app j) x) at hmx
    change (c.π.app j) (Subtype.val (L x)) = Subtype.val ((s.π.app j) x) at hLx
    change (c.π.app j) (Subtype.val (m x)) = (c.π.app j) (Subtype.val (L x))
    exact hmx.trans hLx.symm
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hproj) x

private lemma exists_etale_subalgebra_mem (K : Type u) [Field K]
    {B : Type v} [CommRing B] [Algebra K B] [Algebra.WeaklyEtale K B] (x : B) :
    ∃ S : Subalgebra K B, x ∈ S ∧ Algebra.Etale K S :=
  ⟨Algebra.adjoin K {x}, Algebra.self_mem_adjoin_singleton K x,
    (flat_lmul_weaklyEtale_filteredColimitEtale_tfae K B).2
      (Algebra.WeaklyEtale.flat_lmul' K B) _ ⟨{x}, by simp⟩⟩

private lemma reduction_iso (K : Type u) [Field K]
    (A : Type v) [CommRing A] [Algebra K A] :
    IsIso ((maxFunctor K).map
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K (nilradical A)))) := by
  let A₀ : CommAlgCat.{v} K := CommAlgCat.of K A
  let R₀ : CommAlgCat.{v} K := CommAlgCat.of K (A ⧸ nilradical A)
  let q : A₀ →ₐ[K] R₀ := Ideal.Quotient.mkₐ K (nilradical A)
  let f : maxSubalgebra K A₀ →ₐ[K] maxSubalgebra K R₀ :=
    maxMap K A₀ R₀ (CommAlgCat.ofHom q)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hq : q (x : A₀) = q (y : A₀) := congrArg Subtype.val hxy
      have hnil : IsNilpotent ((x - y : maxSubalgebra K A₀) : A₀) := by
        apply (mem_nilradical).mp
        apply (Ideal.Quotient.eq_zero_iff_mem).mp
        change q ((x : A₀) - (y : A₀)) = 0
        rw [map_sub, sub_eq_zero]
        exact hq
      have hnil' : IsNilpotent (x - y : maxSubalgebra K A₀) := by
        obtain ⟨n, hn⟩ := hnil
        refine ⟨n, Subtype.val_injective ?_⟩
        simpa only [Subalgebra.coe_pow, Subalgebra.coe_zero] using hn
      let : IsReduced (maxSubalgebra K A₀) :=
        (structure_of_weaklyEtale_over_field.{u,v,v} K
          (maxSubalgebra K A₀) (maxSubalgebra_weaklyEtale K A₀)).1
      exact sub_eq_zero.mp (IsNilpotent.eq_zero hnil')
    · intro y
      have := maxSubalgebra_weaklyEtale K R₀
      obtain ⟨S, hy, _⟩ := exists_etale_subalgebra_mem K y
      let g : S →ₐ[K] A ⧸ nilradical A :=
        (maxSubalgebra K R₀).val.comp S.val
      have hnil : Ideal.IsLocallyNilpotent (nilradical A) := fun _ ↦ mem_nilradical.mp
      obtain ⟨t, ht⟩ := main_theorem07K4 K S A (nilradical A) hnil g
      let z : maxSubalgebra K A₀ :=
        ⟨t ⟨y, hy⟩, map_mem_maxSubalgebra_of_weaklyEtale K inferInstance A₀ t _⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change q (t ⟨y, hy⟩) = (y : R₀)
      exact DFunLike.congr_fun ht (⟨y, hy⟩ : S)
  change IsIso (CommAlgCat.ofHom f)
  exact (CommAlgCat.isoMk (AlgEquiv.ofBijective f hf)).isIso_hom

variable {K : Type u} [Field K] {J : Type v} [SmallCategory J] [IsFiltered J]
  {F : J ⥤ CommAlgCat.{v} K}

private abbrev colimitAlgebra (c : Cocone (F ⋙ forget₂ _ CommRingCat.{v}))
    (hc : IsColimit c) (j : J) : Algebra K c.pt :=
  (c.ι.app j).hom.comp (algebraMap K (F.obj j)) |>.toAlgebra' <| by
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    simp [← dsimp% c.w hjk, ← dsimp% (c.ι.app k).hom.map_mul, Algebra.commutes']

private def colimitCocone (c : Cocone (F ⋙ forget₂ _ CommRingCat.{v}))
    (hc : IsColimit c) (j : J) : Cocone F where
  pt :=
    letI : Algebra K c.pt := colimitAlgebra c hc j
    CommAlgCat.of K c.pt
  ι.app k := by
    letI : Algebra K c.pt := colimitAlgebra c hc j
    refine CommAlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply _ _

private def isColimitCocone (c : Cocone (F ⋙ forget₂ _ CommRingCat.{v}))
    (hc : IsColimit c) (j : J) : IsColimit (colimitCocone c hc j) where
  desc s := by
    letI : Algebra K c.pt := colimitAlgebra c hc j
    refine CommAlgCat.ofHom { __ := (hc.desc (Functor.mapCocone _ s)).hom, commutes' := ?_ }
    intro r
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j ↦ ?_) _)
    ext
    exact congr($(hm _) _)

private local instance : (forget₂ (CommAlgCat.{v} K) CommRingCat.{v}).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    let i := asIso ((forget₂ (CommAlgCat.{v} K) CommRingCat.{v}).map f)
    let e : X ≃ₐ[K] Y := AlgEquiv.ofBijective f.hom (by
      have hi : Function.Bijective i.hom.hom := by
        change Function.Bijective i.commRingCatIsoToRingEquiv
        exact i.commRingCatIsoToRingEquiv.bijective
      exact hi)
    exact (CommAlgCat.isoMk e).isIso_hom

private noncomputable local instance :
    CreatesColimitsOfShape J (forget₂ (CommAlgCat.{v} K) CommRingCat.{v}) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hc ↦
    ⟨⟨colimitCocone _ hc IsFiltered.nonempty.some, Iso.refl _⟩,
      isColimitCocone _ hc _⟩

private noncomputable local instance : HasColimitsOfShape J (CommAlgCat.{v} K) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (forget₂ _ CommRingCat.{v})

private noncomputable local instance :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{v} K) CommRingCat.{v}) where
  preserves_filtered_colimits _ := inferInstance

private lemma forget_preserves_filtered_colimits :
    PreservesFilteredColimits (forget (CommAlgCat.{v} K)) :=
  Limits.comp_preservesFilteredColimits (forget₂ _ CommRingCat.{v}) (forget CommRingCat.{v})

private lemma exists_stage_fin (F : J ⥤ CommAlgCat.{v} K)
    (c : Cocone F) (hc : IsColimit c) (n : ℕ) (x : Fin n → c.pt) :
    ∃ (j : J) (y : Fin n → F.obj j), ∀ i, c.ι.app j (y i) = x i := by
  let : PreservesFilteredColimits (forget (CommAlgCat.{v} K)) :=
    forget_preserves_filtered_colimits
  induction n with
  | zero =>
      exact ⟨IsFiltered.nonempty.some, Fin.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
      obtain ⟨j₀, _, y₀, hy₀⟩ :=
        Concrete.exists_hom_ι_eq_of_isColimit F hc (x 0) IsFiltered.nonempty.some
      obtain ⟨j₁, y₁, hy₁⟩ := ih (fun i ↦ x i.succ)
      let j := IsFiltered.max j₀ j₁
      let f := IsFiltered.leftToMax j₀ j₁
      let g := IsFiltered.rightToMax j₀ j₁
      let y : Fin (n + 1) → F.obj j := Fin.cons (F.map f y₀) (fun i ↦ F.map g (y₁ i))
      refine ⟨j, y, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · change c.ι.app j (F.map f y₀) = x 0
        rw [← ConcreteCategory.comp_apply, c.w f]
        exact hy₀
      · intro i
        change c.ι.app j (F.map g (y₁ i)) = x i.succ
        rw [← ConcreteCategory.comp_apply, c.w g]
        exact hy₁ i

private lemma exists_stage_kill_fin (F : J ⥤ CommAlgCat.{v} K)
    (c : Cocone F) (hc : IsColimit c) (j : J) (n : ℕ) (x : Fin n → F.obj j)
    (hx : ∀ i, c.ι.app j (x i) = 0) :
    ∃ (k : J) (f : j ⟶ k), ∀ i, F.map f (x i) = 0 := by
  let : PreservesFilteredColimits (forget (CommAlgCat.{v} K)) :=
    forget_preserves_filtered_colimits
  induction n with
  | zero =>
      exact ⟨j, 𝟙 j, fun i ↦ i.elim0⟩
  | succ n ih =>
      obtain ⟨j₀, f₀, hf₀⟩ :=
        (hc.eq_iff' (x 0) (0 : F.obj j)).mp (by simpa only [map_zero] using hx 0)
      obtain ⟨j₁, f₁, hf₁⟩ := ih (fun i ↦ x i.succ) (fun i ↦ hx i.succ)
      let k := IsFiltered.max j₀ j₁
      let g₀ := IsFiltered.leftToMax j₀ j₁
      let g₁ := IsFiltered.rightToMax j₀ j₁
      obtain ⟨l, h, heq⟩ := IsFilteredOrEmpty.cocone_maps (f₀ ≫ g₀) (f₁ ≫ g₁)
      refine ⟨l, (f₀ ≫ g₀) ≫ h, ?_⟩
      intro i
      refine Fin.cases ?_ ?_ i
      · have hf₀' : F.map f₀ (x 0) = 0 := by simpa only [map_zero] using hf₀
        simp only [Functor.map_comp, ConcreteCategory.comp_apply, hf₀', map_zero]
      · intro i
        rw [heq]
        simp only [Functor.map_comp, ConcreteCategory.comp_apply, hf₁ i, map_zero]

private lemma finitePresentation_exists_lift (F : J ⥤ CommAlgCat.{v} K)
    (c : Cocone F) (hc : IsColimit c) {S : Type v} [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] (g : S →ₐ[K] c.pt) :
    ∃ (j : J) (g' : S →ₐ[K] F.obj j), (c.ι.app j).hom.comp g' = g := by
  obtain ⟨n, π, hπ, hker⟩ := Algebra.FinitePresentation.out (R := K) (A := S)
  obtain ⟨j, y, hy⟩ := exists_stage_fin F c hc n (fun i ↦ g (π (MvPolynomial.X i)))
  let ψ : MvPolynomial (Fin n) K →ₐ[K] F.obj j := MvPolynomial.aeval y
  have hcomp : (c.ι.app j).hom.comp ψ = g.comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [ψ] using hy i
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hrvanish (i : Fin m) : c.ι.app j (ψ (r i)) = 0 := by
    have hmem : r i ∈ RingHom.ker π.toRingHom := by
      rw [← hr]
      exact Ideal.subset_span ⟨i, rfl⟩
    have hπr : π (r i) = 0 := hmem
    have h := DFunLike.congr_fun hcomp (r i)
    change c.ι.app j (ψ (r i)) = g (π (r i)) at h
    rwa [hπr, map_zero] at h
  obtain ⟨k, f, hf⟩ := exists_stage_kill_fin F c hc j m (fun i ↦ ψ (r i)) hrvanish
  let ψ' : MvPolynomial (Fin n) K →ₐ[K] F.obj k := (F.map f).hom.comp ψ
  have hkerle : RingHom.ker π.toRingHom ≤ RingHom.ker ψ'.toRingHom := by
    rw [← hr]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change ψ' (r i) = 0
    exact hf i
  let φ : MvPolynomial (Fin n) K ⧸ RingHom.ker π.toRingHom →ₐ[K] F.obj k :=
    Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) ψ' hkerle
  let e : S ≃ₐ[K] MvPolynomial (Fin n) K ⧸ RingHom.ker π.toRingHom :=
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  let g' : S →ₐ[K] F.obj k := φ.comp e.toAlgHom
  refine ⟨k, g', ?_⟩
  apply (AlgHom.cancel_right hπ).mp
  apply AlgHom.ext
  intro p
  have heval : e (π p) = (Ideal.Quotient.mkₐ K (RingHom.ker π.toRingHom)) p :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hπ p
  change c.ι.app k (φ (e (π p))) = g (π p)
  rw [heval]
  change c.ι.app k (ψ' p) = g (π p)
  change c.ι.app k (F.map f (ψ p)) = g (π p)
  rw [← ConcreteCategory.comp_apply, c.w f]
  exact DFunLike.congr_fun hcomp p

private lemma maxSubalgebra_mem_colimit (F : J ⥤ CommAlgCat.{v} K)
    (c : Cocone F) (hc : IsColimit c) (x : maxSubalgebra K c.pt) :
    ∃ (j : J) (y : maxSubalgebra K (F.obj j)),
      c.ι.app j (y : F.obj j) = (x : c.pt) := by
  have := maxSubalgebra_weaklyEtale K c.pt
  obtain ⟨S, hx, _⟩ := exists_etale_subalgebra_mem K x
  let g : S →ₐ[K] c.pt := (maxSubalgebra K c.pt).val.comp S.val
  obtain ⟨j, t, ht⟩ := finitePresentation_exists_lift F c hc g
  let y : maxSubalgebra K (F.obj j) :=
    ⟨t ⟨x, hx⟩, map_mem_maxSubalgebra_of_weaklyEtale K inferInstance (F.obj j) t _⟩
  exact ⟨j, y, DFunLike.congr_fun ht (⟨x, hx⟩ : S)⟩

private lemma maxFunctor_preservesFilteredColimits (K : Type u) [Field K] :
    PreservesFilteredColimits (maxFunctor.{u,v} K) := by
  refine ⟨fun (J : Type v) [SmallCategory J] [IsFiltered J] ↦ ?_⟩
  refine ⟨fun {F} ↦ ?_⟩
  refine ⟨fun {c} hc ↦ ?_⟩
  let D := F ⋙ maxFunctor.{u,v} K
  let d : Cocone D := colimit.cocone D
  let hd : IsColimit d := colimit.isColimit D
  let t : Cocone D := (maxFunctor.{u,v} K).mapCocone c
  let h : d.pt ⟶ t.pt := hd.desc t
  have hh : Function.Bijective h := by
    constructor
    · intro x y hxy
      let : PreservesFilteredColimits (forget (CommAlgCat.{v} K)) :=
        forget_preserves_filtered_colimits
      obtain ⟨i, _, a, ha⟩ :=
        Concrete.exists_hom_ι_eq_of_isColimit D hd x IsFiltered.nonempty.some
      obtain ⟨j, _, b, hb⟩ :=
        Concrete.exists_hom_ι_eq_of_isColimit D hd y IsFiltered.nonempty.some
      change maxSubalgebra K (F.obj i) at a
      change maxSubalgebra K (F.obj j) at b
      have hxy' : h (d.ι.app i a) = h (d.ι.app j b) := by
        rwa [ha, hb]
      have hfa := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hd.fac t i)) a
      have hfb := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hd.fac t j)) b
      have hfa' := congrArg Subtype.val hfa
      have hfb' := congrArg Subtype.val hfb
      have hab : c.ι.app i (a : F.obj i) = c.ι.app j (b : F.obj j) :=
        hfa'.symm.trans (congrArg Subtype.val hxy') |>.trans hfb'
      obtain ⟨k, f, g, hfg⟩ := (hc.eq_iff F).mp hab
      have hfgD : D.map f a = D.map g b := Subtype.ext hfg
      calc
        x = d.ι.app i a := ha.symm
        _ = d.ι.app k (D.map f a) := by
          symm
          exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (d.w f)) a
        _ = d.ι.app k (D.map g b) := congrArg _ hfgD
        _ = d.ι.app j b := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (d.w g)) b
        _ = y := hb
    · intro z
      obtain ⟨j, y, hy⟩ := maxSubalgebra_mem_colimit F c hc z
      refine ⟨d.ι.app j y, ?_⟩
      exact Subtype.ext <| (congrArg Subtype.val
        (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hd.fac t j)) y)).trans hy
  let : IsIso (hd.desc t) := (CommAlgCat.isoMk (AlgEquiv.ofBijective h.hom hh)).isIso_hom
  exact ⟨hd.ofPointIso (t := t)⟩

/-- The maximal weakly étale subalgebra over a field is functorial and commutes with filtered
colimits, reduction, and finite products. It pulls back along injective algebra maps, and over an
algebra without nontrivial idempotents it is either the zero ring or a separable algebraic field
extension. -/
@[stacks 0CKT]
theorem exists_maximalWeaklyEtaleSubalgebraFunctor
    (K : Type u) [Field K] :
    ∃ (Bmax : CommAlgCat.{v} K ⥤ CommAlgCat.{v} K)
      (ι : Bmax ⟶ 𝟭 (CommAlgCat.{v} K)),
      (∀ A, Function.Injective (ι.app A)) ∧
      (∀ A, Algebra.WeaklyEtale K (Bmax.obj A)) ∧
      (∀ (A : CommAlgCat.{v} K) (S : Subalgebra K A),
        Algebra.WeaklyEtale K S →
          ∃ f : CommAlgCat.of K S ⟶ Bmax.obj A,
            f ≫ ι.app A = CommAlgCat.ofHom S.val) ∧
      (∀ (A' A : CommAlgCat.{v} K) (f : A' ⟶ A), Function.Injective f →
        ∀ x : A',
          (∃ b : Bmax.obj A', ι.app A' b = x) ↔
            ∃ b : Bmax.obj A, ι.app A b = f x) ∧
      PreservesFilteredColimits Bmax ∧
      (∀ A : CommAlgCat.{v} K,
        IsIso (Bmax.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ K (nilradical A))))) ∧
      (∀ (J : Type v) [Finite J], PreservesLimitsOfShape (Discrete J) Bmax) ∧
      (∀ A : CommAlgCat.{v} K,
        (∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) →
          Subsingleton A ∨
            (IsField (Bmax.obj A) ∧ Algebra.IsSeparable K (Bmax.obj A) ∧
              Algebra.IsAlgebraic K (Bmax.obj A))) := by
  refine ⟨maxFunctor K, maxInclusion K, fun _ ↦ Subtype.val_injective,
    maxSubalgebra_weaklyEtale K, ?_, ?_, maxFunctor_preservesFilteredColimits K,
    fun A ↦ reduction_iso K A, fun J _ ↦ preserves_finite_products K J, max_connected K⟩
  · intro A S hS
    let f : S →ₐ[K] maxSubalgebra K A :=
      S.val.codRestrict _ (fun x ↦ le_maxSubalgebra K A S hS x.2)
    refine ⟨CommAlgCat.ofHom f, ?_⟩
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  · intro A' A f hf x
    change (∃ b : maxSubalgebra K A', (b : A') = x) ↔
      ∃ b : maxSubalgebra K A, (b : A) = f x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨⟨_, map_mem_maxSubalgebra K A' A f b⟩, rfl⟩
    · rintro ⟨b, hb⟩
      exact ⟨⟨x, (mem_maxSubalgebra_iff_of_injective K A' A f hf x).mpr (hb ▸ b.2)⟩, rfl⟩

end MaximalSubalgebraFunctor

section BaseChange

open TensorProduct

private lemma tensorProduct_map_subalgebra_injective
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [CommRing L] [CommRing A] [Algebra K L] [Algebra K A]
    (B : Subalgebra K A) :
    Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id K L) B.val :
        L ⊗[K] B →ₐ[K] L ⊗[K] A) := by
  change Function.Injective (TensorProduct.map LinearMap.id B.val.toLinearMap)
  exact Module.Flat.lTensor_preserves_injective_linearMap B.val.toLinearMap
    (fun _ _ h ↦ Subtype.ext h)

private lemma tensorProduct_weaklyEtale
    (K : Type u) (L : Type v) (A : Type w)
    [CommRing K] [CommRing L] [CommRing A] [Algebra K L] [Algebra K A]
    (hA : Algebra.WeaklyEtale K A) :
    Algebra.WeaklyEtale L (L ⊗[K] A) := by
  let := hA
  infer_instance

private lemma weaklyEtale_map
    {K R S : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (D : Subalgebra K R)
    (hD : Algebra.WeaklyEtale K D) (f : R →ₐ[K] S) :
    Algebra.WeaklyEtale K (D.map f) :=
  weaklyEtale_of_surjective hD (f.subalgebraMap D) (f.subalgebraMap_surjective D)

private lemma map_mem_of_isGreatest_weaklyEtale
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (D : Subalgebra K R) (hD : Algebra.WeaklyEtale K D)
    (hmax : ∀ C : Subalgebra K R, Algebra.WeaklyEtale K C → C ≤ D)
    (f : R →ₐ[K] R) {x : R} (hx : x ∈ D) : f x ∈ D :=
  hmax (D.map f) (weaklyEtale_map D hD f) ⟨x, hx, rfl⟩

private lemma isIdempotentElem_mem_of_isGreatest_weaklyEtale
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (D : Subalgebra K R)
    (hmax : ∀ C : Subalgebra K R, Algebra.WeaklyEtale K C → C ≤ D)
    {e : R} (he : IsIdempotentElem e) : e ∈ D := by
  let f : (Fin 2 → K) →ₐ[K] R :=
    { toFun := fun x ↦ algebraMap K R (x 0) * e + algebraMap K R (x 1) * (1 - e)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by
        intros
        simp only [Pi.add_apply, map_add]
        ring
      map_mul' := by
        intros
        simp only [Pi.mul_apply, map_mul]
        ring_nf
        simp only [pow_two, he.eq]
        ring
      commutes' := by
        intro r
        change algebraMap K R r * e + algebraMap K R r * (1 - e) = algebraMap K R r
        ring }
  exact hmax f.range (weaklyEtale_range inferInstance f) ⟨![1, 0], by simp [f]⟩

private lemma range_le_of_isGreatest_weaklyEtale
    {K R S : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (hR : Algebra.WeaklyEtale K R)
    (D : Subalgebra K S)
    (hmax : ∀ C : Subalgebra K S, Algebra.WeaklyEtale K C → C ≤ D)
    (f : R →ₐ[K] S) : f.range ≤ D :=
  hmax _ (weaklyEtale_range hR f)

private lemma traceTensor_eq_sum
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [FiniteDimensional K L] [IsGalois K L] (x : L ⊗[K] A) :
    1 ⊗ₜ[K] ((TensorProduct.lid K A) (TensorProduct.map (Algebra.trace K L) LinearMap.id x)) =
      ∑ σ : L ≃ₐ[K] L, Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy, Finset.sum_add_distrib]
  | tmul l a =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms l]
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

private lemma traceTensor_basis_sum
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (x : L ⊗[K] A) :
    ∑ i, b i ⊗ₜ[K] ((TensorProduct.lid K A)
      (TensorProduct.map (Algebra.trace K L) LinearMap.id (b.traceDual i • x))) = x := by
  have hb (l : L) (i : ι) : Algebra.trace K L (b.traceDual i * l) = b.repr l i := by
    conv_rhs => rw [← b.traceDual_traceDual]
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
  | tmul l a =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.lid_tmul, hb]
    simp_rw [← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, b.sum_repr]

private lemma isIdempotentElem_mem_range_tensorProduct_of_isGalois
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [FiniteDimensional K L] [IsGalois K L]
    (B : Subalgebra K A)
    (hBmax : ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B)
    {x : L ⊗[K] A} (hx : IsIdempotentElem x) :
    ∃ y : L ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K L) B.val y = x := by
  classical
  obtain ⟨D, hD, hDmax⟩ := exists_greatest_weaklyEtale_subalgebra K (L ⊗[K] A)
  have hxD : x ∈ D := isIdempotentElem_mem_of_isGreatest_weaklyEtale D hDmax hx
  have hL : Algebra.WeaklyEtale K L := by
    let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    let : Algebra.Etale K L :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    infer_instance
  have hsmul (l : L) {z : L ⊗[K] A} (hz : z ∈ D) : l • z ∈ D := by
    rw [Algebra.smul_def]
    apply D.mul_mem _ hz
    exact range_le_of_isGreatest_weaklyEtale hL D hDmax Algebra.TensorProduct.includeLeft
      ⟨l, rfl⟩
  let t : L ⊗[K] A →ₗ[K] A :=
    (TensorProduct.lid K A).toLinearMap.comp (TensorProduct.map (Algebra.trace K L) LinearMap.id)
  have ht {z : L ⊗[K] A} (hz : z ∈ D) : t z ∈ B := by
    let f : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight
    have hf : Function.Injective f :=
      Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
    apply hBmax (D.comap f) (weaklyEtale_comap D hD f hf)
    change 1 ⊗ₜ[K] t z ∈ D
    change (1 : L) ⊗ₜ[K] ((TensorProduct.lid K A)
      (TensorProduct.map (Algebra.trace K L) LinearMap.id z)) ∈ D
    rw [traceTensor_eq_sum z]
    exact D.sum_mem fun σ _ ↦ map_mem_of_isGreatest_weaklyEtale D hD hDmax
      (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)) hz
  let b := Module.finBasis K L
  refine ⟨∑ i, b i ⊗ₜ[K] ⟨t (b.traceDual i • x), ht (hsmul _ hxD)⟩, ?_⟩
  simpa only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Subalgebra.val_apply, t, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    using traceTensor_basis_sum b x

private lemma tensorProduct_map_val_comm
    {K L E A : Type*} [CommRing K] [CommRing L] [CommRing E] [CommRing A]
    [Algebra K L] [Algebra K E] [Algebra K A] (f : L →ₐ[K] E)
    (B : Subalgebra K A) (x : L ⊗[K] B) :
    Algebra.TensorProduct.map (AlgHom.id K E) B.val
      (Algebra.TensorProduct.map f (AlgHom.id K B) x) =
    Algebra.TensorProduct.map f (AlgHom.id K A)
      (Algebra.TensorProduct.map (AlgHom.id K L) B.val x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

private lemma isIdempotentElem_mem_range_tensorProduct_of_isGalois_infinite
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [IsGalois K L] (B : Subalgebra K A)
    (hBmax : ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B)
    {x : L ⊗[K] A} (hx : IsIdempotentElem x) :
    ∃ y : L ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K L) B.val y = x := by
  classical
  obtain ⟨n, l, a, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let N := FiniteGaloisIntermediateField.adjoin K (Set.range l)
  let l' (i : Fin n) : N := ⟨l i, FiniteGaloisIntermediateField.subset_adjoin K
    (Set.range l) (Set.mem_range_self i)⟩
  let z : N ⊗[K] A := ∑ i, l' i ⊗ₜ[K] a i
  let f : N ⊗[K] A →ₐ[K] L ⊗[K] A :=
    Algebra.TensorProduct.map N.toIntermediateField.val (AlgHom.id K A)
  have hf : Function.Injective f := by
    change Function.Injective (TensorProduct.map N.toIntermediateField.val.toLinearMap LinearMap.id)
    exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id
  have hz : f z = ∑ i, l i ⊗ₜ[K] a i := by simp [f, z, l']
  have hzi : IsIdempotentElem z := by
    apply hf
    simpa only [map_mul, hz] using hx.eq
  obtain ⟨y, hy⟩ := isIdempotentElem_mem_range_tensorProduct_of_isGalois B hBmax hzi
  refine ⟨Algebra.TensorProduct.map N.toIntermediateField.val (AlgHom.id K B) y, ?_⟩
  rw [tensorProduct_map_val_comm, hy]
  exact hz

set_option backward.isDefEq.respectTransparency false in
-- Nested tensor products with restricted scalars require additional instance-search reduction.
private lemma isIdempotentElem_mem_range_tensorProduct_of_isAlgClosed
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [IsAlgClosed L] (B : Subalgebra K A)
    (hBmax : ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B)
    {x : L ⊗[K] A} (hx : IsIdempotentElem x) :
    ∃ y : L ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K L) B.val y = x := by
  let E := separableClosure K L
  let : IsSepClosed E := (inferInstance : IsSepClosure K E).sep_closed
  let : Algebra.IsGeometricallyConnected E L :=
    (Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum E L).mpr inferInstance
  let : CommRing (E ⊗[K] A) := inferInstance
  let : Algebra E (E ⊗[K] A) := inferInstance
  let : Algebra E L := inferInstance
  let e : ((E ⊗[K] A) ⊗[E] L) ≃+* (L ⊗[K] A) :=
    (Algebra.TensorProduct.comm E (E ⊗[K] A) L).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K E L L A).toRingEquiv
  have he (z : E ⊗[K] A) :
      e (algebraMap (E ⊗[K] A) ((E ⊗[K] A) ⊗[E] L) z) =
        Algebra.TensorProduct.map E.val (AlgHom.id K A) z := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      rw [(algebraMap (E ⊗[K] A) ((E ⊗[K] A) ⊗[E] L)).map_add z w,
        e.map_add, hz, hw, map_add]
    | tmul a b =>
      change e ((a ⊗ₜ[K] b) ⊗ₜ[E] (1 : L)) = (a : L) ⊗ₜ[K] b
      simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul]
      simp [Algebra.smul_def]
  have hxi : IsIdempotentElem (e.symm x) := by
    change e.symm x * e.symm x = e.symm x
    rw [← map_mul, hx.eq]
  obtain ⟨z, hz, hzx⟩ :=
    (Algebra.TensorProduct.bijOn_isIdempotentElem_and_bijective_connectedComponentsMap
      E L (E ⊗[K] A)).1.surjOn hxi
  obtain ⟨y, hy⟩ := isIdempotentElem_mem_range_tensorProduct_of_isGalois_infinite B hBmax hz
  refine ⟨Algebra.TensorProduct.map E.val (AlgHom.id K B) y, ?_⟩
  rw [tensorProduct_map_val_comm, hy, ← he, hzx, e.apply_symm_apply]

private lemma range_le_of_isIdempotentElem_mem
    {L R ι : Type*} [Field L] [CommRing R] [Algebra L R] [Finite ι]
    (D : Subalgebra L R) (hD : ∀ e : R, IsIdempotentElem e → e ∈ D)
    (φ : (ι → L) →ₐ[L] R) : φ.range ≤ D := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  rintro _ ⟨x, rfl⟩
  have hφ (i : ι) : φ (Pi.single i 1) ∈ D := by
    apply hD
    change φ (Pi.single i 1) * φ (Pi.single i 1) = φ (Pi.single i 1)
    rw [← map_mul]
    congr 1
    ext j
    by_cases h : j = i <;> simp [h]
  have hs : ∑ i, (x i) • (Pi.single i 1) = x := by
    ext j
    simp [Pi.single_apply]
  rw [← hs, map_sum]
  apply D.sum_mem
  intro i _
  change φ ((x i) • Pi.single i 1) ∈ D
  rw [map_smul]
  exact D.smul_mem (hφ i) _

private lemma weaklyEtale_le_of_isIdempotentElem_mem
    {L R : Type*} [Field L] [CommRing R] [Algebra L R] [IsSepClosed L]
    (D : Subalgebra L R) (hD : ∀ e : R, IsIdempotentElem e → e ∈ D)
    (C : Subalgebra L R) (hC : Algebra.WeaklyEtale L C) : C ≤ D := by
  classical
  intro x hx
  let x' : C := ⟨x, hx⟩
  let S := Algebra.adjoin L ({x'} : Set C)
  have hS : S.FG := ⟨{x'}, by simp [S]⟩
  obtain ⟨ι, hι, F, hF, hLF, e, hsep⟩ :=
    (structure_of_weaklyEtale_over_field.{_, _, 0} L C hC).2.2.1 S hS
  let := hι
  let := hF
  let := hLF
  let (i : ι) : Algebra.IsSeparable L (F i) := (hsep i).2
  let e' : S ≃ₐ[L] (ι → L) := e.trans (AlgEquiv.piCongrRight fun i ↦
    (AlgEquiv.ofBijective (Algebra.ofId L (F i)) (IsSepClosed.algebraMap_bijective L (F i))).symm)
  let φ : (ι → L) →ₐ[L] R := C.val.comp (S.val.comp e'.symm.toAlgHom)
  let z : S := ⟨x', Algebra.subset_adjoin (Set.mem_singleton x')⟩
  exact range_le_of_isIdempotentElem_mem D hD φ ⟨e' z, by simp [φ, z, x']⟩

private lemma weaklyEtale_mem_range_tensorProduct_of_isAlgClosed
    {K L A : Type*} [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    [IsAlgClosed L] (B : Subalgebra K A)
    (hBmax : ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B)
    (C : Subalgebra L (L ⊗[K] A)) (hC : Algebra.WeaklyEtale L C) (x : C) :
    ∃ y : L ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K L) B.val y = x := by
  let f : L ⊗[K] B →ₐ[L] L ⊗[K] A :=
    Algebra.TensorProduct.map (AlgHom.id L L) B.val
  exact weaklyEtale_le_of_isIdempotentElem_mem f.range
    (fun e he ↦ isIdempotentElem_mem_range_tensorProduct_of_isAlgClosed B hBmax he) C hC x.property

private lemma mem_range_tensorProduct_of_map_mem_range
    {K L E A : Type*} [Field K] [Field L] [Field E] [CommRing A]
    [Algebra K L] [Algebra K E] [Algebra K A] (j : L →ₐ[K] E)
    (B : Subalgebra K A) (x : L ⊗[K] A)
    (hx : ∃ y : E ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K E) B.val y =
      Algebra.TensorProduct.map j (AlgHom.id K A) x) :
    ∃ y : L ⊗[K] B, Algebra.TensorProduct.map (AlgHom.id K L) B.val y = x := by
  obtain ⟨p, hp⟩ := j.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr j.injective)
  have hp' (l : L) : p (j l) = l := LinearMap.congr_fun hp l
  let pA : E ⊗[K] A →ₗ[K] L ⊗[K] A := TensorProduct.map p LinearMap.id
  let pB : E ⊗[K] B →ₗ[K] L ⊗[K] B := TensorProduct.map p LinearMap.id
  have hnat (y : E ⊗[K] B) :
      pA (Algebra.TensorProduct.map (AlgHom.id K E) B.val y) =
        Algebra.TensorProduct.map (AlgHom.id K L) B.val (pB y) := by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [pA, pB]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hid (z : L ⊗[K] A) : pA (Algebra.TensorProduct.map j (AlgHom.id K A) z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pA, hp']
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨y, hy⟩ := hx
  exact ⟨pB y, (hnat y).symm.trans ((congrArg pA hy).trans (hid x))⟩

private lemma cancelBaseChange_one_tmul
    {K L E A : Type*} [CommRing K] [CommRing L] [CommRing E] [CommRing A]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E] [Algebra K A]
    (x : L ⊗[K] A) :
    Algebra.TensorProduct.cancelBaseChange K L E E A ((1 : E) ⊗ₜ[L] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L E) (AlgHom.id K A) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul a b => simp [Algebra.smul_def]

/-- Extending the base field carries the maximal weakly étale subalgebra to the maximal
weakly étale subalgebra of the scalar extension. -/
@[stacks 0CKU]
theorem maximalWeaklyEtaleSubalgebra_baseChange
    (K : Type u) (L : Type v) (A : Type w)
    [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]
    (B : Subalgebra K A) (hB : Algebra.WeaklyEtale K B)
    (hBmax : ∀ C : Subalgebra K A, Algebra.WeaklyEtale K C → C ≤ B) :
    let f : L ⊗[K] B →ₐ[K] L ⊗[K] A :=
      Algebra.TensorProduct.map (AlgHom.id K L) B.val
    Function.Injective f ∧
      Algebra.WeaklyEtale L (L ⊗[K] B) ∧
      ∀ C : Subalgebra L (L ⊗[K] A), Algebra.WeaklyEtale L C →
        ∀ x : C, ∃ y : L ⊗[K] B, f y = x := by
  dsimp only
  refine ⟨tensorProduct_map_subalgebra_injective K L A B,
    tensorProduct_weaklyEtale K L B hB, ?_⟩
  intro C hC x
  let E := AlgebraicClosure L
  let g : E ⊗[L] C →ₐ[E] E ⊗[K] A :=
    (Algebra.TensorProduct.cancelBaseChange K L E E A).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id E E) C.val)
  obtain ⟨y, hy⟩ := weaklyEtale_mem_range_tensorProduct_of_isAlgClosed B hBmax g.range
    (weaklyEtale_range (tensorProduct_weaklyEtale L E C hC) g)
    ⟨g ((1 : E) ⊗ₜ[L] x), ⟨(1 : E) ⊗ₜ[L] x, rfl⟩⟩
  apply mem_range_tensorProduct_of_map_mem_range (IsScalarTower.toAlgHom K L E) B x
  refine ⟨y, hy.trans ?_⟩
  change g ((1 : E) ⊗ₜ[L] x) =
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L E) (AlgHom.id K A) x
  simp only [g, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgEquiv.coe_toAlgHom]
  exact cancelBaseChange_one_tmul (x : L ⊗[K] A)

end BaseChange
