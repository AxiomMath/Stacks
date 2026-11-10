module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.RingTheory.Rig.Category.CompletedBaseChange
public import StacksFrontier.RingTheory.Rig.Category.PolynomialPresentation

/-!
# Adic algebra systems and the quotient functor

The category `Rig.AdicAlgebraSystem` of inverse systems of finite type algebras over the
quotients `A ⧸ I ^ n`, the identification of completed base change along `A → A ⧸ 𝔞` with the
quotient functor, and the functor `Rig.adicQuotientFunctor` from `Rig.AdicFiniteTypeAlgebra`.
-/

@[expose] public section

open CategoryTheory

universe u v u₁ u₂

namespace Rig

section

/-- The category of inverse systems `… → B₃ → B₂ → B₁` in which `Bₙ` is a finite
type `A ⧸ I ^ n`-algebra and each transition identifies its target with reduction of its
source modulo `I ^ n`.  The Lean index `n` represents the mathematical index `n + 1`. -/
@[stacks 0AL3]
structure AdicAlgebraSystem (A : Type u) [CommRing A] (I : Ideal A) where
  /-- The rings in the inverse system.  `B n` denotes the displayed ring `B_{n+1}`. -/
  B : ℕ → CommRingCat.{v}
  /-- The algebra structure of `B_{n+1}` over `A ⧸ I^(n+1)`. -/
  algebraMap : ∀ n, A ⧸ I ^ (n + 1) →+* B n
  /-- Each algebra in the system is of finite type over its indicated quotient of `A`. -/
  finiteType : ∀ n, (algebraMap n).FiniteType
  /-- The transition `B_{n+2} → B_{n+1}`. -/
  transition : ∀ n, B (n + 1) →+* B n
  /-- A transition is compatible with the maps from `A`. -/
  transition_comp_algebraMap : ∀ n,
    (transition n).comp ((algebraMap (n + 1)).comp (Ideal.Quotient.mk (I ^ (n + 2)))) =
      (algebraMap n).comp (Ideal.Quotient.mk (I ^ (n + 1)))
  /-- Every transition is onto. -/
  transition_surjective : ∀ n, Function.Surjective (transition n)
  /-- The kernel of `B_{n+2} → B_{n+1}` is `I^(n+1) B_{n+2}`. -/
  transition_ker : ∀ n, RingHom.ker (transition n) =
    (I ^ (n + 1)).map ((algebraMap (n + 1)).comp (Ideal.Quotient.mk (I ^ (n + 2))))

namespace AdicAlgebraSystem

/-- A morphism of adic algebra systems is a levelwise algebra map compatible with the
transition maps. -/
structure Hom {A : Type u} [CommRing A] {I : Ideal A}
    (X Y : AdicAlgebraSystem.{u, v} A I) where
  /-- The map at each level. -/
  app : ∀ n, X.B n →+* Y.B n
  /-- The levelwise maps respect the algebra structures. -/
  commutes_algebraMap : ∀ n, (app n).comp (X.algebraMap n) = Y.algebraMap n
  /-- The levelwise maps commute with transition maps. -/
  naturality : ∀ n, (Y.transition n).comp (app (n + 1)) =
    (app n).comp (X.transition n)

/-- The identity morphism of an adic algebra system. -/
def Hom.id {A : Type u} [CommRing A] {I : Ideal A}
    (X : AdicAlgebraSystem.{u, v} A I) : Hom X X where
  app _ := RingHom.id _
  commutes_algebraMap _ := rfl
  naturality _ := rfl

/-- Composition of morphisms of adic algebra systems. -/
def Hom.comp {A : Type u} [CommRing A] {I : Ideal A}
    {X Y Z : AdicAlgebraSystem.{u, v} A I}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  app n := (g.app n).comp (f.app n)
  commutes_algebraMap n := by rw [RingHom.comp_assoc, f.commutes_algebraMap, g.commutes_algebraMap]
  naturality n := by rw [← RingHom.comp_assoc, g.naturality n, RingHom.comp_assoc,
    f.naturality n, ← RingHom.comp_assoc]

/-- The category structure on inverse systems of finite type quotient algebras. -/
instance {A : Type u} [CommRing A] {I : Ideal A} :
    Category (AdicAlgebraSystem.{u, v} A I) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := by cases f; rw [Hom.mk.injEq]; funext n; ext x; rfl
  comp_id f := by cases f; rw [Hom.mk.injEq]; funext n; ext x; rfl
  assoc f g h := by cases f; cases g; cases h; rw [Hom.mk.injEq]; funext n; ext x; rfl

end AdicAlgebraSystem

end

section

private theorem completion_of_bijective_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map e.toRingHom = J)
    (h : Function.Bijective (AdicCompletion.of I R)) :
    Function.Bijective (AdicCompletion.of J S) := by
  have : IsAdicComplete I R := AdicCompletion.of_bijective_iff.mp h
  have : IsAdicComplete J S := hIJ ▸ (IsAdicComplete.congr_ringEquiv I e).mpr ‹_›
  exact AdicCompletion.of_bijective_iff.mpr ‹_›

private theorem quotient_base_ideal_bounds
    {A : Type u} [CommRing A] {I a : Ideal A} {barI : Ideal (A ⧸ a)}
    {c d : ℕ} (hI : (I ^ c).map (Ideal.Quotient.mk a) ≤ barI)
    (hbarI : barI ^ d ≤ I.map (Ideal.Quotient.mk a))
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    (I.map (algebraMap A (B.carrier ⧸ a.map (algebraMap A B.carrier)))) ^ c ≤
      barI.map (algebraMap (A ⧸ a)
        (B.carrier ⧸ a.map (algebraMap A B.carrier))) ∧
    (barI.map (algebraMap (A ⧸ a)
        (B.carrier ⧸ a.map (algebraMap A B.carrier)))) ^ d ≤
      I.map (algebraMap A (B.carrier ⧸ a.map (algebraMap A B.carrier))) := by
  let S := B.carrier ⧸ a.map (algebraMap A B.carrier)
  have hcomp : (algebraMap (A ⧸ a) S).comp (Ideal.Quotient.mk a) = algebraMap A S := by
    ext x
    simp [S]
  refine ⟨?_, ?_⟩
  · have hm := Ideal.map_mono (f := algebraMap (A ⧸ a) S) hI
    rwa [Ideal.map_map, hcomp, Ideal.map_pow] at hm
  · have hm := Ideal.map_mono (f := algebraMap (A ⧸ a) S) hbarI
    rwa [Ideal.map_map, hcomp, Ideal.map_pow] at hm

private theorem quotientTensorEquiv_natural
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (a : Ideal A) (f : B →ₐ[A] C) :
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C a).toRingHom.comp
        (Ideal.quotientMap (I := a.map (algebraMap A B)) (a.map (algebraMap A C)) f.toRingHom
          (by
            rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
            have hcomp : f.toRingHom.comp (algebraMap A B) = algebraMap A C := by
              ext x
              exact f.commutes x
            rw [hcomp])) =
  (Algebra.TensorProduct.map f (AlgHom.id A (A ⧸ a))).toRingHom.comp
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B a).toRingHom := by
  ext x
  simp [Ideal.quotientMap_mk,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I a : Ideal A) (barI : Ideal (A ⧸ a))
variable {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
variable (hI : (I ^ c).map (Ideal.Quotient.mk a) ≤ barI)
variable (hbarI : barI ^ d ≤ I.map (Ideal.Quotient.mk a))

/-- The quotient of an adically finite type algebra by an ideal from the base is
complete for every ideal defining the induced adic topology. -/
@[stacks 0AL6 "the quotient is complete"]
public theorem quotient_isAdicallyComplete
    (hc : 0 < c) (hd : 0 < d)
    (hI : (I ^ c).map (Ideal.Quotient.mk a) ≤ barI)
    (hbarI : barI ^ d ≤ I.map (Ideal.Quotient.mk a))
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    IsAdicComplete (barI.map (algebraMap (A ⧸ a)
        (B.carrier ⧸ a.map (algebraMap A B.carrier))))
      (B.carrier ⧸ a.map (algebraMap A B.carrier)) := by
  let S := B.carrier ⧸ a.map (algebraMap A B.carrier)
  let J := a.map (algebraMap A B.carrier)
  let qI := I.map (algebraMap A S)
  let qbarI := barI.map (algebraMap (A ⧸ a) S)
  have hbounds := quotient_base_ideal_bounds hI hbarI B
  have hquot := quotient_isAdicFiniteType B J
  let _ : IsAdicComplete qI S := by simpa [qI, S] using hquot.1
  let e := AdicCompletion.ofLinearEquiv qI S
  have he : e.toLinearMap = AdicCompletion.of qI S := rfl
  obtain ⟨e', he'⟩ :=
    agreement_of_completions qI qbarI hc hd hbounds.1 hbounds.2 S
  apply AdicCompletion.of_bijective_iff.mp
  have heq : (e.trans e').toLinearMap = AdicCompletion.of qbarI S := by
    refine LinearMap.ext fun x => ?_
    change (e'.toLinearMap.comp e.toLinearMap) x = AdicCompletion.of qbarI S x
    rw [he]
    exact congrArg (fun f : S →ₗ[S] AdicCompletion qbarI S => f x) he'
  rw [← heq]
  exact (e.trans e').bijective

/-- The canonical map from the tensor-product presentation of the quotient algebra
to its `barI`-adic completion is an isomorphism. -/
@[stacks 0AL6 "completed base change is the quotient"]
public theorem tensor_quotient_completion_bijective
    (hc : 0 < c) (hd : 0 < d)
    (hI : (I ^ c).map (Ideal.Quotient.mk a) ≤ barI)
    (hbarI : barI ^ d ≤ I.map (Ideal.Quotient.mk a))
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    Function.Bijective
      (AdicCompletion.of
        (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
        (baseChangedAlgebra (A₂ := A ⧸ a) B)) := by
  let S := B.carrier ⧸ a.map (algebraMap A B.carrier)
  let K := barI.map (algebraMap (A ⧸ a) S)
  let T := baseChangedAlgebra (A₂ := A ⧸ a) B
  let qEquiv := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B.carrier a
  have hmap : qEquiv.toRingHom.comp (algebraMap (A ⧸ a) S) =
      (Algebra.TensorProduct.includeRight : A ⧸ a →ₐ[A] T).toRingHom := by
    ext y
    change qEquiv (algebraMap B.carrier S (algebraMap A B.carrier y)) =
      1 ⊗ₜ[A] Ideal.Quotient.mk a y
    rw [AlgEquiv.commutes]
    change (algebraMap A B.carrier y) ⊗ₜ[A] 1 =
      1 ⊗ₜ[A] Ideal.Quotient.mk a y
    simpa only [← Ideal.Quotient.algebraMap_eq] using
      (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) y)
  have hideal : K.map qEquiv.toRingHom =
      baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B := by
    rw [Ideal.map_map, hmap]
    rfl
  have hcomplete := quotient_isAdicallyComplete I a barI hc hd hI hbarI B
  have hbijS : Function.Bijective (AdicCompletion.of K S) :=
    AdicCompletion.of_bijective_iff.mpr (by simpa [K, S] using hcomplete)
  exact completion_of_bijective_ringEquiv qEquiv.toRingEquiv K
    (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B) hideal hbijS

/-- Base change to a closed subscheme is the quotient functor. The isomorphism to
completed base change is the canonical completion map, and quotienting a morphism
acts by quotienting its underlying algebra homomorphism. -/
@[stacks 0AL6 "the quotient functor and its natural comparison"]
public theorem quotientBaseChange
    (hc : 0 < c) (hd : 0 < d)
    (hI : (I ^ c).map (Ideal.Quotient.mk a) ≤ barI)
    (hbarI : barI ^ d ≤ I.map (Ideal.Quotient.mk a)) :
    ∃ (Q : AdicFiniteTypeAlgebra.{u, v} A I ⥤
        AdicFiniteTypeAlgebra.{u, max v u} (A ⧸ a) barI),
      ∃ (η : Q ≅
          (completedBaseChange (A₁ := A) (A₂ := A ⧸ a)
            I barI c hc hI (Ideal.fg_of_isNoetherianRing barI)).functor),
        ∃ (e : ∀ B : AdicFiniteTypeAlgebra.{u, v} A I,
            (Q.obj B).carrier ≃+* (B.carrier ⧸ a.map (algebraMap A B.carrier))),
          (∀ (B : AdicFiniteTypeAlgebra.{u, v} A I) (x : B.carrier),
            ((completedBaseChange (A₁ := A) (A₂ := A ⧸ a)
              I barI c hc hI (Ideal.fg_of_isNoetherianRing barI)).completedTensorProductEquiv B)
                (AdicFiniteTypeAlgebra.hom (η.hom.app B)
                  ((e B).symm (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))) =
              AdicCompletion.of
                (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
                (baseChangedAlgebra (A₂ := A ⧸ a) B)
                ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B.carrier a)
                  (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))) ∧
          (∀ {B C : AdicFiniteTypeAlgebra.{u, v} A I} (f : B ⟶ C) (x : B.carrier),
            e C (AdicFiniteTypeAlgebra.hom (Q.map f)
              ((e B).symm (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))) =
              Ideal.Quotient.mk (a.map (algebraMap A C.carrier))
                  (AdicFiniteTypeAlgebra.hom f x)) := by
  let BC := completedBaseChange (A₁ := A) (A₂ := A ⧸ a)
    I barI c hc hI (Ideal.fg_of_isNoetherianRing barI)
  let F := BC.functor
  let α (B : AdicFiniteTypeAlgebra.{u, v} A I) := BC.completedTensorProductEquiv B
  let qEquiv (B : AdicFiniteTypeAlgebra.{u, v} A I) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B.carrier a
  let φ (B : AdicFiniteTypeAlgebra.{u, v} A I) :
      (B.carrier ⧸ a.map (algebraMap A B.carrier)) →+*
        AdicCompletion
          (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
          (baseChangedAlgebra (A₂ := A ⧸ a) B) :=
    (algebraMap
      (baseChangedAlgebra (A₂ := A ⧸ a) B)
      (AdicCompletion
        (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
        (baseChangedAlgebra (A₂ := A ⧸ a) B))).comp (qEquiv B).toRingHom
  let e (B : AdicFiniteTypeAlgebra.{u, v} A I) :=
    (α B).trans ((RingEquiv.ofBijective (φ B)
      (by
        change Function.Bijective (fun x => AdicCompletion.of
          (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
          (baseChangedAlgebra (A₂ := A ⧸ a) B) (qEquiv B x))
        exact Function.Bijective.comp
          (tensor_quotient_completion_bijective I a barI hc hd hI hbarI B)
          (qEquiv B).bijective)).symm)
  have he_symm (B : AdicFiniteTypeAlgebra.{u, v} A I) (x : B.carrier) :
      (e B).symm (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x) =
        (α B).symm (AdicCompletion.of
          (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
          (baseChangedAlgebra (A₂ := A ⧸ a) B)
          (qEquiv B (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))) := by
    simp [e, φ, RingEquiv.ofBijective_apply]
    rfl
  refine ⟨F, Iso.refl F, e, fun B x => ?_, fun {B C} f x => ?_⟩
  · have hId : AdicFiniteTypeAlgebra.hom (𝟙 (F.obj B)) =
        AlgHom.id (A ⧸ a) (F.obj B).carrier := rfl
    change BC.completedTensorProductEquiv B
      (AdicFiniteTypeAlgebra.hom (𝟙 (F.obj B))
        ((e B).symm (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))) =
      AdicCompletion.of
        (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
        (baseChangedAlgebra (A₂ := A ⧸ a) B)
        (qEquiv B (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))
    rw [hId, he_symm]
    exact (α B).apply_symm_apply _
  · apply (e C).symm.injective
    apply (α C).injective
    simp only [RingEquiv.symm_apply_apply]
    rw [he_symm B x, he_symm C (AdicFiniteTypeAlgebra.hom f x)]
    simp only [RingEquiv.apply_symm_apply]
    change BC.completedTensorProductEquiv C
        (AdicFiniteTypeAlgebra.hom (F.map f)
          ((BC.completedTensorProductEquiv B).symm
            (AdicCompletion.of
              (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) B)
              (baseChangedAlgebra (A₂ := A ⧸ a) B)
              (qEquiv B (Ideal.Quotient.mk (a.map (algebraMap A B.carrier)) x))))) =
      AdicCompletion.of
        (baseChangedIdeal (A₂ := A ⧸ a) (I₂ := barI) C)
        (baseChangedAlgebra (A₂ := A ⧸ a) C)
        (qEquiv C (Ideal.Quotient.mk (a.map (algebraMap A C.carrier))
          (AdicFiniteTypeAlgebra.hom f x)))
    rw [BC.map_completedTensorProductEquiv]
    simp [qEquiv]

end

section

private lemma adicSystemHom_ext {A : Type u} [CommRing A] {I : Ideal A}
    {X Y : AdicAlgebraSystem.{u, v} A I}
    {f g : AdicAlgebraSystem.Hom X Y}
    (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private lemma algebraMap_mem_map_pow {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ) {x : A} (hx : x ∈ I ^ n) :
    algebraMap A B x ∈ I.map (algebraMap A B) ^ n := by
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hx

private lemma finiteType_quotient_pow
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (n : ℕ)
    [Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    [IsScalarTower A (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (hred : Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))) :
    (Ideal.Quotient.lift (I ^ (n + 1))
      ((Ideal.Quotient.mk ((I.map (algebraMap A B)) ^ (n + 1))).comp
        (algebraMap A B))
      (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.2
        (algebraMap_mem_map_pow I _ hx))).FiniteType := by
  let J : Ideal B := I.map (algebraMap A B)
  let p : Ideal A := I ^ (n + 1)
  let q : Ideal B := J ^ (n + 1)
  let f : A ⧸ p →+* B ⧸ q :=
    Ideal.Quotient.lift p ((Ideal.Quotient.mk q).comp (algebraMap A B))
      fun _ hx => Ideal.Quotient.eq_zero_iff_mem.2 (algebraMap_mem_map_pow I _ hx)
  let _ : Algebra (A ⧸ p) (B ⧸ q) := f.toAlgebra
  let K : Ideal (A ⧸ p) := I.map (Ideal.Quotient.mk p)
  let L : Ideal (B ⧸ q) := K.map (algebraMap (A ⧸ p) (B ⧸ q))
  have hcompBase : (algebraMap (A ⧸ p) (B ⧸ q)).comp (Ideal.Quotient.mk p) =
      (Ideal.Quotient.mk q).comp (algebraMap A B) := by
    ext a
    change f (Ideal.Quotient.mk p a) = Ideal.Quotient.mk q (algebraMap A B a)
    rw [Ideal.Quotient.lift_mk]
    simp [Ideal.Quotient.mk_comp_algebraMap]
  have hL : L = J.map (Ideal.Quotient.mk q) := by
    change (I.map (Ideal.Quotient.mk p)).map (algebraMap (A ⧸ p) (B ⧸ q)) =
      (I.map (algebraMap A B)).map (Ideal.Quotient.mk q)
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun φ : A →+* B ⧸ q => I.map φ) hcompBase
  have hKL : K ≤ Ideal.comap (algebraMap (A ⧸ p) (B ⧸ q)) L := Ideal.le_comap_map
  let fbar : (A ⧸ p) ⧸ K →+* (B ⧸ q) ⧸ L :=
    Ideal.quotientMap L (algebraMap (A ⧸ p) (B ⧸ q)) hKL
  let _ : Algebra ((A ⧸ p) ⧸ K) ((B ⧸ q) ⧸ L) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have hpI : p ≤ I := Ideal.pow_le_self (by omega)
  have hqJ : q ≤ J := Ideal.pow_le_self (by omega)
  let eA : (A ⧸ p) ⧸ K ≃+* A ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hpI
  let eB : (B ⧸ q) ⧸ L ≃+* B ⧸ J :=
    (Ideal.quotEquivOfEq hL).trans (DoubleQuot.quotQuotEquivQuotOfLE hqJ)
  have hleft (a : A) :
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ q) ⧸ L))
          (Ideal.Quotient.mk K (Ideal.Quotient.mk p a)) =
        Ideal.Quotient.mk L (Ideal.Quotient.mk q (algebraMap A B a)) := by
    calc
      (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ q) ⧸ L))
          (Ideal.Quotient.mk K (Ideal.Quotient.mk p a)) =
        Ideal.Quotient.mk L
          (algebraMap (A ⧸ p) (B ⧸ q) (Ideal.Quotient.mk p a)) := by
            rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      _ = Ideal.Quotient.mk L (Ideal.Quotient.mk q (algebraMap A B a)) := by
        congr 1
  have hright (a : A) :
      (algebraMap (A ⧸ I) (B ⧸ J)) (Ideal.Quotient.mk I a) =
        Ideal.Quotient.mk J (algebraMap A B a) := by
    calc
      (algebraMap (A ⧸ I) (B ⧸ J)) (Ideal.Quotient.mk I a) =
          algebraMap A (B ⧸ J) a := by
        simpa [Ideal.Quotient.algebraMap_eq] using
          (IsScalarTower.algebraMap_apply A (A ⧸ I) (B ⧸ J) a).symm
      _ = Ideal.Quotient.mk J (algebraMap A B a) := by
        rw [← Ideal.Quotient.mk_comp_algebraMap A J]
        rfl
  have hfb : fbar = algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ q) ⧸ L) := rfl
  have heA (a : A) :
      eA.toRingHom (Ideal.Quotient.mk K (Ideal.Quotient.mk p a)) =
        Ideal.Quotient.mk I a := by
    change DoubleQuot.quotQuotEquivQuotOfLE hpI (DoubleQuot.quotQuotMk p I a) =
      Ideal.Quotient.mk I a
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk a hpI
  have heB (a : A) :
      eB.toRingHom (Ideal.Quotient.mk L (Ideal.Quotient.mk q (algebraMap A B a))) =
        Ideal.Quotient.mk J (algebraMap A B a) := by
    change DoubleQuot.quotQuotEquivQuotOfLE hqJ (DoubleQuot.quotQuotMk q J (algebraMap A B a)) = _
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (algebraMap A B a) hqJ
  have hcomp : eB.toRingHom.comp fbar =
      (algebraMap (A ⧸ I) (B ⧸ J)).comp eA.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    simp only [RingHom.comp_apply]
    rw [hfb, hleft a, heB a, heA a, hright a]
  have hfbar : fbar.FiniteType := by
    have hfactor : fbar = eB.symm.toRingHom.comp
        ((algebraMap (A ⧸ I) (B ⧸ J)).comp eA.toRingHom) := by
      apply RingHom.ext
      intro x
      apply eB.injective
      simpa [RingHom.comp_apply] using congrArg (fun k : _ →+* _ => k x) hcomp
    rw [hfactor]
    exact (RingHom.FiniteType.of_surjective _ eB.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr hred).comp
        (RingHom.FiniteType.of_surjective _ eA.surjective))
  have hKnil : IsNilpotent K := by
    refine ⟨n + 1, ?_⟩
    change (I.map (Ideal.Quotient.mk p)) ^ (n + 1) = ⊥
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact finiteType_of_isNilpotent_quotient_finiteType (A ⧸ p) K (B ⧸ q) hKnil (by
    simpa [L, f] using RingHom.finiteType_algebraMap.mp
      (hfbar : (algebraMap ((A ⧸ p) ⧸ K) ((B ⧸ q) ⧸ L)).FiniteType))

/-- The functor which associates to an adically complete algebra `B` its inverse system
of quotients
`B ⧸ (I.map (algebraMap A B)) ^ (n + 1)`.

Its transition maps are the canonical quotient maps, and its action on morphisms is induced
by the underlying `A`-algebra maps. -/
@[stacks 0AJN]
public noncomputable def adicQuotientFunctor (A : Type u) [CommRing A]
    (I : Ideal A) :
    AdicFiniteTypeAlgebra.{u, v} A I ⥤
      AdicAlgebraSystem.{u, v} A I := by
  classical
  let obj : AdicFiniteTypeAlgebra.{u, v} A I ⥤
      AdicAlgebraSystem.{u, v} A I :=
    { obj := fun B =>
        { B := fun n => CommRingCat.of (B.carrier ⧸ B.adicIdeal ^ (n + 1))
          algebraMap := fun n =>
            Ideal.Quotient.lift (I ^ (n + 1))
              ((Ideal.Quotient.mk (B.adicIdeal ^ (n + 1))).comp
                (algebraMap A B.carrier))
              fun _ hx => by exact Ideal.Quotient.eq_zero_iff_mem.2 (algebraMap_mem_map_pow I _ hx)
          finiteType := fun n => by exact finiteType_quotient_pow I n B.finiteTypeReduction
          transition := fun n =>
            Ideal.Quotient.lift (B.adicIdeal ^ (n + 2))
              (Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)))
              fun _ hx =>
                Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_le_pow_right (by omega) hx)
          transition_comp_algebraMap := by
            intro n
            ext x
            rfl
          transition_surjective := fun _ =>
            Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective
          transition_ker := by
            intro n
            ext x
            rw [RingHom.mem_ker]
            rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
            rw [Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem]
            simp only [AdicFiniteTypeAlgebra.adicIdeal,
              ← Ideal.map_pow]
            have hquot :
                ((Ideal.Quotient.lift (I ^ (n + 2))
                    ((Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ (n + 2))).comp
                      (algebraMap A B.carrier))
                    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.2
                      (algebraMap_mem_map_pow I _ ha))).comp
                    (Ideal.Quotient.mk (I ^ (n + 2)))) =
                  (Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ (n + 2))).comp
                    (algebraMap A B.carrier) := by
              ext a
              simp
            rw [hquot, ← Ideal.map_map, Ideal.map_pow,
              Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
            refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
            rintro ⟨y, hy, heq⟩
            have hdiff : x - y ∈ (I.map (algebraMap A B.carrier)) ^ (n + 2) :=
              Ideal.Quotient.eq.1 heq.symm
            rw [show x = y + (x - y) by ring]
            exact Ideal.add_mem _ hy (Ideal.pow_le_pow_right (by omega) hdiff)
        }
      map := fun {X Y} f =>
        { app := fun n =>
            Ideal.Quotient.lift _
                ((Ideal.Quotient.mk _).comp
                  f.hom.hom)
                (by
                  intro x hx
                  exact (Ideal.Quotient.eq_zero_iff_mem).2 (by
                    have hmap :
                        (X.adicIdeal ^ (n + 1)).map f.hom.hom = Y.adicIdeal ^ (n + 1) := by
                      dsimp [AdicFiniteTypeAlgebra.adicIdeal]
                      rw [Ideal.map_pow]
                      change (Ideal.map f.hom.hom.toRingHom
                          (Ideal.map (algebraMap A X.carrier) I)) ^ (n + 1) =
                        (Ideal.map (algebraMap A Y.carrier) I) ^ (n + 1)
                      rw [Ideal.map_map (algebraMap A X.carrier) f.hom.hom.toRingHom]
                      congr 1
                      ext a
                      simp
                    have hmem := Ideal.mem_map_of_mem f.hom.hom hx
                    rwa [hmap] at hmem))
          commutes_algebraMap := by
            intro n
            apply Ideal.Quotient.ringHom_ext
            ext a
            simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]
            exact congrArg (Ideal.Quotient.mk (Y.adicIdeal ^ (n + 1)))
              (f.hom.hom.commutes a)
          naturality := by
            intro n
            ext x
            rfl }
      map_id := by
        intro B
        apply adicSystemHom_ext
        funext n
        apply Ideal.Quotient.ringHom_ext
        ext x
        rfl
      map_comp := by
        intro B C D f g
        apply adicSystemHom_ext
        funext n
        apply Ideal.Quotient.ringHom_ext
        ext x
        change (Ideal.Quotient.mk (D.adicIdeal ^ (n + 1)))
            ((g.hom.hom.comp f.hom.hom) x) =
          (Ideal.Quotient.mk (D.adicIdeal ^ (n + 1)))
            (g.hom.hom (f.hom.hom x))
        rfl }
  exact obj

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The term at level `n` is the quotient by the `(n + 1)`st power of the extended ideal. -/
@[simp] public theorem adicQuotientFunctor_obj_B
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    ((adicQuotientFunctor A I).obj B).B n =
      CommRingCat.of (B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ (n + 1)) := rfl

/-- The structure map at each level is induced by the structure map of the complete algebra. -/
@[simp] public theorem adicQuotientFunctor_obj_algebraMap
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    ((adicQuotientFunctor A I).obj B).algebraMap n =
      Ideal.quotientMap (B.adicIdeal ^ (n + 1)) (algebraMap A B.carrier)
        (by
          apply Ideal.map_le_iff_le_comap.mp
          rw [Ideal.map_pow]) := rfl

/-- On representatives the structure map is the original algebra map followed by quotienting. -/
@[simp] public theorem adicQuotientFunctor_obj_algebraMap_mk
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) (a : A) :
    ((adicQuotientFunctor A I).obj B).algebraMap n (Ideal.Quotient.mk (I ^ (n + 1)) a) =
      Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) (algebraMap A B.carrier a) := rfl

/-- The transition between two successive levels is the canonical quotient map. -/
@[simp] public theorem adicQuotientFunctor_obj_transition
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    ((adicQuotientFunctor A I).obj B).transition n =
      Ideal.Quotient.lift (B.adicIdeal ^ (n + 2))
        (Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)))
        (by
          intro x hx
          exact Ideal.Quotient.eq_zero_iff_mem.mpr
            (Ideal.pow_le_pow_right (by omega) hx)) := rfl

/-- A transition sends the class of an element to its class at the preceding level. -/
@[simp] public theorem adicQuotientFunctor_obj_transition_mk
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) (b : B.carrier) :
    ((adicQuotientFunctor A I).obj B).transition n
        (Ideal.Quotient.mk (B.adicIdeal ^ (n + 2)) b) =
      Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) b := rfl

/-- Each quotient is of finite type over the corresponding quotient of the base ring. -/
public theorem adicQuotientFunctor_obj_finiteType
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    (((adicQuotientFunctor A I).obj B).algebraMap n).FiniteType :=
  ((adicQuotientFunctor A I).obj B).finiteType n

/-- The quotient transitions are surjective. -/
public theorem adicQuotientFunctor_obj_transition_surjective
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    Function.Surjective (((adicQuotientFunctor A I).obj B).transition n) :=
  ((adicQuotientFunctor A I).obj B).transition_surjective n

/-- The transition kernel is the image of the preceding power of the extended ideal. -/
@[simp] public theorem adicQuotientFunctor_obj_transition_ker
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    RingHom.ker (((adicQuotientFunctor A I).obj B).transition n) =
      (B.adicIdeal ^ (n + 1)).map (Ideal.Quotient.mk (B.adicIdeal ^ (n + 2))) := by
  rw [((adicQuotientFunctor A I).obj B).transition_ker n]
  have hcomp :
      (((adicQuotientFunctor A I).obj B).algebraMap (n + 1)).comp
          (Ideal.Quotient.mk (I ^ (n + 2))) =
        (Ideal.Quotient.mk (B.adicIdeal ^ (n + 2))).comp (algebraMap A B.carrier) := by
    ext a
    rfl
  rw [hcomp]
  change (I ^ (n + 1)).map
      ((Ideal.Quotient.mk (B.adicIdeal ^ (n + 2))).comp (algebraMap A B.carrier)) =
    (B.adicIdeal ^ (n + 1)).map (Ideal.Quotient.mk (B.adicIdeal ^ (n + 2)))
  rw [← Ideal.map_map, Ideal.map_pow]

/-- On morphisms the functor takes the quotient map induced by the original algebra map. -/
@[simp] public theorem adicQuotientFunctor_map_app
    {B C : AdicFiniteTypeAlgebra.{u, v} A I} (f : B ⟶ C) (n : ℕ) :
    ((adicQuotientFunctor A I).map f).app n =
      Ideal.quotientMap (I := B.adicIdeal ^ (n + 1))
        (C.adicIdeal ^ (n + 1)) f.hom.hom.toRingHom
        (by
          apply Ideal.map_le_iff_le_comap.mp
          change ((I.map (algebraMap A B.carrier)) ^ (n + 1)).map f.hom.hom.toRingHom ≤ _
          rw [Ideal.map_pow, Ideal.map_map]
          have hcomp : f.hom.hom.toRingHom.comp (algebraMap A B.carrier) =
              algebraMap A C.carrier := by
            ext a
            exact f.hom.hom.commutes a
          rw [hcomp]) := rfl

/-- The induced quotient map sends the class of `b` to the class of its image. -/
@[simp] public theorem adicQuotientFunctor_map_app_mk
    {B C : AdicFiniteTypeAlgebra.{u, v} A I} (f : B ⟶ C) (n : ℕ)
    (b : B.carrier) :
    ((adicQuotientFunctor A I).map f).app n
        (Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) b) =
      Ideal.Quotient.mk (C.adicIdeal ^ (n + 1)) (f.hom.hom b) := rfl

end

end Rig

end
