module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Functors on algebras with a formally étale chart

Let `R` be a commutative ring and `κ` an infinite cardinal. This file sets up the algebraic
counterpart of an algebraic space over an affine scheme `Spec R`: a functor `F` from commutative
`R`-algebras of cardinality below `κ` to sets, together with an *étale chart*, a natural
transformation `Hom_R(C, -) ⟶ F` from the functor corepresented by a smooth `R`-algebra `C`
which is formally étale, that is, which has unique liftings along surjections of algebras with
square-zero kernel.

At a section `x₀` of `F` over `P` which comes from the chart, the chart identifies the sections
of `F` over a square-zero extension `Q` of `P` lying over `x₀` with the `R`-algebra maps `C ⟶ Q`
lying over a fixed one. Since `Hom_R(C, -)` carries fibre products of algebras to fibre products
of sets, so does `F` at such sections: this is the Rim–Schlessinger condition, and it is all the
structure the infinitesimal theory of `F` needs.

## Main definitions

* `Stacks.ChartedFunctor.BoundedAlg` is the category of commutative `R`-algebras of cardinality
  below `κ`.
* `Stacks.ChartedFunctor.corep` is the functor `Hom_R(C, -)` on it.
* `Stacks.ChartedFunctor.EtaleChart` is an étale chart of a functor on it.
* `Stacks.ChartedFunctor.Fib` is the set of sections over an algebra lying over a given section
  over a quotient of it.
* `Stacks.ChartedFunctor.fibreProd` is the fibre product `Q₁ ×_P Q₂` of two algebras over `P`.

## Main results

* `Stacks.ChartedFunctor.EtaleChart.bijective_chartFibMap`: over a square-zero extension, the
  chart identifies the lifts of a chart point with the sections lying over it.
* `Stacks.ChartedFunctor.EtaleChart.bijective_fibreProd`: **the Rim–Schlessinger condition** at
  a chart point, for the fibre product of two square-zero extensions.

## Implementation notes

The cardinality bound stands in for the size cutoff of a big site: the functors this file is
applied to are restrictions of algebraic spaces to spectra of algebras, and only spectra of
algebras of bounded cardinality are objects of the site. All constructions used later (quotients,
subalgebras, products, trivial square-zero extensions, tensor products) stay below an infinite
cardinal, which is the only property of `κ` used.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
-/

@[expose] public section

open CategoryTheory Cardinal Opposite

universe u

namespace Stacks.ChartedFunctor

variable (R : Type u) [CommRing R] (κ : Cardinal.{u})

/-- The category of commutative `R`-algebras of cardinality below `κ`. -/
abbrev BoundedAlg : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun P : CommAlgCat.{u} R => #P < κ

namespace BoundedAlg

variable {R κ}

/-- An `R`-algebra of cardinality below `κ`, as an object of `BoundedAlg R κ`. -/
abbrev of (P : Type u) [CommRing P] [Algebra R P] (hP : #P < κ) : BoundedAlg R κ :=
  ⟨CommAlgCat.of R P, hP⟩

/-- An `R`-algebra map, as a morphism of `BoundedAlg R κ`. -/
abbrev ofHom {P Q : BoundedAlg R κ} (f : P.obj →ₐ[R] Q.obj) : P ⟶ Q :=
  ObjectProperty.homMk (CommAlgCat.ofHom f)

/-- The underlying algebra map of a morphism of `BoundedAlg R κ`. -/
abbrev toAlgHom {P Q : BoundedAlg R κ} (f : P ⟶ Q) : P.obj →ₐ[R] Q.obj := f.hom.hom

/-- The underlying algebra map of `ofHom f` is `f`. -/
@[simp]
lemma toAlgHom_ofHom {P Q : BoundedAlg R κ} (f : P.obj →ₐ[R] Q.obj) :
    toAlgHom (ofHom f) = f := rfl

/-- The underlying algebra map of a composite is the composite of the underlying maps. -/
@[simp]
lemma toAlgHom_comp {P Q W : BoundedAlg R κ} (f : P ⟶ Q) (g : Q ⟶ W) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

/-- The underlying algebra map of the identity morphism is the identity. -/
@[simp]
lemma toAlgHom_id (P : BoundedAlg R κ) : toAlgHom (𝟙 P) = AlgHom.id R P.obj := rfl

/-- The morphism of a composite of algebra maps is the composite of their morphisms. -/
lemma ofHom_comp {P Q W : BoundedAlg R κ} (f : P.obj →ₐ[R] Q.obj) (g : Q.obj →ₐ[R] W.obj) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

/-- A morphism is recovered from its underlying algebra map. -/
@[simp]
lemma ofHom_toAlgHom {P Q : BoundedAlg R κ} (f : P ⟶ Q) : ofHom (toAlgHom f) = f := rfl

/-- The identity algebra map gives the identity morphism. -/
lemma ofHom_id (P : BoundedAlg R κ) : ofHom (AlgHom.id R P.obj) = 𝟙 P := rfl

/-- Two morphisms of `BoundedAlg R κ` with the same underlying algebra map are equal. -/
lemma hom_ext {P Q : BoundedAlg R κ} {f g : P ⟶ Q} (h : toAlgHom f = toAlgHom g) : f = g :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext h)

end BoundedAlg

/-! ### Cardinality bounds -/

section Cardinal

variable {κ}

/-- A quotient of an algebra of cardinality below `κ` has cardinality below `κ`. -/
lemma mk_quotient_lt {P : Type u} [CommRing P] (J : Ideal P) (hP : #P < κ) : #(P ⧸ J) < κ :=
  (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans_lt hP

/-- A subtype of a type of cardinality below `κ` has cardinality below `κ`. -/
lemma mk_subtype_lt {P : Type u} (p : P → Prop) (hP : #P < κ) : #(Subtype p) < κ :=
  (Cardinal.mk_subtype_le p).trans_lt hP

/-- A product of two types of cardinality below an infinite `κ` has cardinality below `κ`. -/
lemma mk_prod_lt (hκ : ℵ₀ ≤ κ) {P Q : Type u} (hP : #P < κ) (hQ : #Q < κ) : #(P × Q) < κ := by
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt hκ hP hQ

/-- A tensor product of two modules of cardinality below an uncountable `κ` has cardinality
below `κ`: it is spanned by the pure tensors, so it is a quotient of the lists of pairs. -/
lemma mk_tensorProduct_lt (hκ : ℵ₀ < κ) {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (hM : #M < κ) (hN : #N < κ) : #(TensorProduct R M N) < κ := by
  have hsurj : Function.Surjective
      (fun l : List (M × N) => (l.map fun p => p.1 ⊗ₜ[R] p.2).sum) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul m n => exact ⟨[(m, n)], by simp⟩
    | add s t hs ht =>
      obtain ⟨l₁, rfl⟩ := hs
      obtain ⟨l₂, rfl⟩ := ht
      exact ⟨l₁ ++ l₂, by simp⟩
  exact (Cardinal.mk_le_of_surjective hsurj).trans_lt
    ((Cardinal.mk_list_le_max _).trans_lt (max_lt hκ (mk_prod_lt hκ.le hM hN)))

end Cardinal

/-! ### Étale charts -/

variable {R κ}

/-- The functor `Hom_R(C, -)` on `R`-algebras of cardinality below `κ`. -/
abbrev corep (C : CommAlgCat.{u} R) : BoundedAlg R κ ⥤ Type u :=
  ObjectProperty.ι _ ⋙ coyoneda.obj (op C)

/-- An **étale chart** of a functor `F` on `R`-algebras of cardinality below `κ`: a smooth
`R`-algebra `C` and a natural transformation `Hom_R(C, -) ⟶ F` which is formally étale, that
is, along every surjection `Q ⟶ P` with square-zero kernel a section of `F` over `Q` whose
image over `P` comes from an algebra map `C ⟶ P` comes from a unique algebra map `C ⟶ Q`
lifting it. -/
structure EtaleChart (F : BoundedAlg R κ ⥤ Type u) where
  /-- The algebra of the chart. -/
  C : CommAlgCat.{u} R
  /-- The algebra of the chart is smooth. -/
  smooth : Algebra.Smooth R C
  /-- The chart. -/
  α : corep C ⟶ F
  /-- The chart is formally étale. -/
  formallyEtale : ∀ ⦃Q P : BoundedAlg R κ⦄ (π : Q ⟶ P),
    Function.Surjective (BoundedAlg.toAlgHom π) →
    RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥ →
    ∀ (ρ₀ : C ⟶ P.obj) (ξ : F.obj Q), F.map π ξ = α.app P ρ₀ →
      ∃! ρ : C ⟶ Q.obj, ρ ≫ π.hom = ρ₀ ∧ α.app Q ρ = ξ

/-- Two elements of an ideal with square zero multiply to zero. -/
private lemma mul_eq_zero_of_sq_eq_bot {A : Type*} [CommRing A] {I : Ideal A} (h : I ^ 2 = ⊥)
    {i j : A} (hi : i ∈ I) (hj : j ∈ I) : i * j = 0 := by
  have : i * j ∈ I ^ 2 := pow_two I ▸ Ideal.mul_mem_mul hi hj
  rwa [h] at this

/-- A surjection of algebras whose kernel has square zero. -/
structure IsSqZeroExt {Q P : BoundedAlg R κ} (π : Q ⟶ P) : Prop where
  surjective : Function.Surjective (BoundedAlg.toAlgHom π)
  sq_eq_bot : RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥

namespace IsSqZeroExt

variable {Q P : BoundedAlg R κ} {π : Q ⟶ P}

/-- Two elements of the kernel of a square-zero extension multiply to zero. -/
lemma mul_eq_zero (hπ : IsSqZeroExt π) {i j : Q.obj} (hi : BoundedAlg.toAlgHom π i = 0)
    (hj : BoundedAlg.toAlgHom π j = 0) : i * j = 0 :=
  mul_eq_zero_of_sq_eq_bot hπ.sq_eq_bot hi hj

end IsSqZeroExt

variable {F : BoundedAlg R κ ⥤ Type u}

/-- The sections of `F` over `Q` lying over a given section `x` over `P`, along `π : Q ⟶ P`. -/
abbrev Fib {Q P : BoundedAlg R κ} (π : Q ⟶ P) (x : F.obj P) : Type u :=
  {ξ : F.obj Q // F.map π ξ = x}

namespace EtaleChart

variable (c : EtaleChart F)

/-- The naturality of a chart, at an algebra map. -/
lemma map_α {P Q : BoundedAlg R κ} (f : P ⟶ Q) (ρ : c.C ⟶ P.obj) :
    F.map f (c.α.app P ρ) = c.α.app Q (ρ ≫ f.hom) :=
  (NatTrans.naturality_apply c.α f ρ).symm

/-- A section of `F` is a *chart point* when it comes from the chart. -/
def IsChartPoint {P : BoundedAlg R κ} (x : F.obj P) : Prop :=
  ∃ ρ₀ : c.C ⟶ P.obj, c.α.app P ρ₀ = x

/-- The image of a chart point is a chart point. -/
lemma IsChartPoint.map {P Q : BoundedAlg R κ} {x : F.obj P} (hx : c.IsChartPoint x) (f : P ⟶ Q) :
    c.IsChartPoint (F.map f x) := by
  obtain ⟨ρ₀, rfl⟩ := hx
  exact ⟨ρ₀ ≫ f.hom, (c.map_α f ρ₀).symm⟩

/-- The algebra maps `C ⟶ Q` lifting a given algebra map `C ⟶ P` along `π : Q ⟶ P`. -/
abbrev ChartFib {Q P : BoundedAlg R κ} (π : Q ⟶ P) (ρ₀ : c.C ⟶ P.obj) : Type u :=
  {ρ : c.C ⟶ Q.obj // ρ ≫ π.hom = ρ₀}

/-- The chart, from the lifts of a chart point to the sections lying over it. -/
def chartFibMap {Q P : BoundedAlg R κ} (π : Q ⟶ P) (ρ₀ : c.C ⟶ P.obj) :
    c.ChartFib π ρ₀ → Fib (F := F) π (c.α.app P ρ₀) :=
  fun ρ => ⟨c.α.app Q ρ.1, by rw [c.map_α, ρ.2]⟩

/-- **The chart identifies lifts with sections**: along a surjection with square-zero kernel,
the algebra maps `C ⟶ Q` lifting `ρ₀ : C ⟶ P` correspond under the chart to the sections of `F`
over `Q` lying over the chart point of `ρ₀`. -/
theorem bijective_chartFibMap {Q P : BoundedAlg R κ} (π : Q ⟶ P)
    (hπ : Function.Surjective (BoundedAlg.toAlgHom π))
    (hker : RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥) (ρ₀ : c.C ⟶ P.obj) :
    Function.Bijective (c.chartFibMap π ρ₀) := by
  refine ⟨fun ρ₁ ρ₂ h => ?_, fun ξ => ?_⟩
  · obtain ⟨ρ, -, hρ⟩ := c.formallyEtale π hπ hker ρ₀ (c.α.app Q ρ₁.1)
      (by rw [c.map_α, ρ₁.2])
    exact Subtype.ext ((hρ _ ⟨ρ₁.2, rfl⟩).trans (hρ _ ⟨ρ₂.2, (congrArg Subtype.val h).symm⟩).symm)
  · obtain ⟨ρ, ⟨hρ, hρξ⟩, -⟩ := c.formallyEtale π hπ hker ρ₀ ξ.1 ξ.2
    exact ⟨⟨ρ, hρ⟩, Subtype.ext hρξ⟩

/-- The chart, as an equivalence between the lifts of a chart point and the sections lying over
it, along a surjection with square-zero kernel. -/
noncomputable def chartFibEquiv {Q P : BoundedAlg R κ} (π : Q ⟶ P)
    (hπ : Function.Surjective (BoundedAlg.toAlgHom π))
    (hker : RingHom.ker (BoundedAlg.toAlgHom π) ^ 2 = ⊥) (ρ₀ : c.C ⟶ P.obj) :
    c.ChartFib π ρ₀ ≃ Fib (F := F) π (c.α.app P ρ₀) :=
  Equiv.ofBijective _ (c.bijective_chartFibMap π hπ hker ρ₀)

section ChartLift

variable {Q P : BoundedAlg R κ} {π : Q ⟶ P} (hπ : IsSqZeroExt π) {x : F.obj P}
  {ρ₀ : c.C ⟶ P.obj} (h : c.α.app P ρ₀ = x)

/-- **The chart lift** of a section lying over a chart point `x = α(ρ₀)`, along a square-zero
extension: the unique algebra map `C ⟶ Q` over `ρ₀` which the chart sends to it. -/
noncomputable def chartLift (ξ : Fib (F := F) π x) : c.C ⟶ Q.obj :=
  ((c.chartFibEquiv π hπ.surjective hπ.sq_eq_bot ρ₀).symm ⟨ξ.1, ξ.2.trans h.symm⟩).1

variable (ξ : Fib (F := F) π x)

/-- The chart lift of `ξ` lies over `ρ₀`. -/
lemma chartLift_comp : c.chartLift hπ h ξ ≫ π.hom = ρ₀ :=
  ((c.chartFibEquiv π hπ.surjective hπ.sq_eq_bot ρ₀).symm ⟨ξ.1, ξ.2.trans h.symm⟩).2

/-- The chart sends the chart lift of `ξ` to `ξ`. -/
lemma α_chartLift : c.α.app Q (c.chartLift hπ h ξ) = ξ.1 :=
  congrArg Subtype.val ((c.chartFibEquiv π hπ.surjective hπ.sq_eq_bot ρ₀).apply_symm_apply
    ⟨ξ.1, ξ.2.trans h.symm⟩)

/-- An algebra map over `ρ₀` which the chart sends to `ξ` is the chart lift of `ξ`. -/
lemma chartLift_eq (σ : c.C ⟶ Q.obj) (hσ : σ ≫ π.hom = ρ₀) (hσξ : c.α.app Q σ = ξ.1) :
    c.chartLift hπ h ξ = σ := by
  obtain ⟨ρ, -, hρ⟩ := c.formallyEtale π hπ.surjective hπ.sq_eq_bot ρ₀ ξ.1 (ξ.2.trans h.symm)
  exact (hρ _ ⟨c.chartLift_comp hπ h ξ, c.α_chartLift hπ h ξ⟩).trans (hρ σ ⟨hσ, hσξ⟩).symm

/-- Two sections lying over a chart point with the same chart lift are equal. -/
lemma eq_of_chartLift_eq (ξ' : Fib (F := F) π x)
    (he : c.chartLift hπ h ξ = c.chartLift hπ h ξ') : ξ = ξ' := by
  apply Subtype.ext
  rw [← c.α_chartLift hπ h ξ, ← c.α_chartLift hπ h ξ', he]

end ChartLift

end EtaleChart

/-! ### Fibre products -/

section FibreProduct

variable [Fact (ℵ₀ < κ)] {Q₁ Q₂ P : BoundedAlg R κ} (π₁ : Q₁ ⟶ P) (π₂ : Q₂ ⟶ P)

/-- The fibre product `Q₁ ×_P Q₂` of two algebras over `P`, as an object of `BoundedAlg R κ`. -/
abbrev fibreProd : BoundedAlg R κ :=
  BoundedAlg.of (AlgHom.equalizer ((BoundedAlg.toAlgHom π₁).comp (AlgHom.fst R Q₁.obj Q₂.obj))
    ((BoundedAlg.toAlgHom π₂).comp (AlgHom.snd R Q₁.obj Q₂.obj)))
    (mk_subtype_lt _ (mk_prod_lt (Fact.out : ℵ₀ < κ).le Q₁.2 Q₂.2))

/-- The first projection out of a fibre product. -/
abbrev fibreProd.fst : fibreProd π₁ π₂ ⟶ Q₁ :=
  BoundedAlg.ofHom ((AlgHom.fst R Q₁.obj Q₂.obj).comp (Subalgebra.val _))

/-- The second projection out of a fibre product. -/
abbrev fibreProd.snd : fibreProd π₁ π₂ ⟶ Q₂ :=
  BoundedAlg.ofHom ((AlgHom.snd R Q₁.obj Q₂.obj).comp (Subalgebra.val _))

/-- The map from a fibre product to the common base. -/
abbrev fibreProd.base : fibreProd π₁ π₂ ⟶ P :=
  fibreProd.fst π₁ π₂ ≫ π₁

/-- The two projections out of a fibre product agree after composing to the base. -/
lemma fibreProd.condition :
    fibreProd.fst π₁ π₂ ≫ π₁ = fibreProd.snd π₁ π₂ ≫ π₂ :=
  BoundedAlg.hom_ext (AlgHom.ext fun x => x.2)

/-- An algebra map into a fibre product is a pair of algebra maps agreeing over the base. -/
def fibreProd.lift {A : CommAlgCat.{u} R} (f₁ : A ⟶ Q₁.obj) (f₂ : A ⟶ Q₂.obj)
    (h : f₁ ≫ π₁.hom = f₂ ≫ π₂.hom) : A ⟶ (fibreProd π₁ π₂).obj :=
  CommAlgCat.ofHom (AlgHom.codRestrict ((f₁.hom).prod f₂.hom) _ fun a =>
    congrArg (fun g : A ⟶ P.obj => g.hom a) h)

/-- The lift into a fibre product, followed by the first projection, is `f₁`. -/
@[simp]
lemma fibreProd.lift_fst {A : CommAlgCat.{u} R} (f₁ : A ⟶ Q₁.obj) (f₂ : A ⟶ Q₂.obj)
    (h : f₁ ≫ π₁.hom = f₂ ≫ π₂.hom) :
    fibreProd.lift π₁ π₂ f₁ f₂ h ≫ (fibreProd.fst π₁ π₂).hom = f₁ := rfl

/-- The lift into a fibre product, followed by the second projection, is `f₂`. -/
@[simp]
lemma fibreProd.lift_snd {A : CommAlgCat.{u} R} (f₁ : A ⟶ Q₁.obj) (f₂ : A ⟶ Q₂.obj)
    (h : f₁ ≫ π₁.hom = f₂ ≫ π₂.hom) :
    fibreProd.lift π₁ π₂ f₁ f₂ h ≫ (fibreProd.snd π₁ π₂).hom = f₂ := rfl

/-- Two algebra maps into a fibre product agreeing after both projections are equal. -/
lemma fibreProd.hom_ext {A : CommAlgCat.{u} R} {g g' : A ⟶ (fibreProd π₁ π₂).obj}
    (h₁ : g ≫ (fibreProd.fst π₁ π₂).hom = g' ≫ (fibreProd.fst π₁ π₂).hom)
    (h₂ : g ≫ (fibreProd.snd π₁ π₂).hom = g' ≫ (fibreProd.snd π₁ π₂).hom) : g = g' :=
  CommAlgCat.hom_ext <| AlgHom.ext fun a => Subtype.ext <| Prod.ext
    (congrArg (fun k : A ⟶ Q₁.obj => k.hom a) h₁) (congrArg (fun k : A ⟶ Q₂.obj => k.hom a) h₂)

variable {π₁ π₂}

/-- The base map of a fibre product of two surjections is surjective. -/
lemma fibreProd.surjective_base (h₁ : Function.Surjective (BoundedAlg.toAlgHom π₁))
    (h₂ : Function.Surjective (BoundedAlg.toAlgHom π₂)) :
    Function.Surjective (BoundedAlg.toAlgHom (fibreProd.base π₁ π₂)) := by
  intro p
  obtain ⟨a, ha⟩ := h₁ p
  obtain ⟨b, hb⟩ := h₂ p
  exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩

/-- The base map of a fibre product of two square-zero extensions has square-zero kernel. -/
lemma fibreProd.ker_base_sq (h₁ : RingHom.ker (BoundedAlg.toAlgHom π₁) ^ 2 = ⊥)
    (h₂ : RingHom.ker (BoundedAlg.toAlgHom π₂) ^ 2 = ⊥) :
    RingHom.ker (BoundedAlg.toAlgHom (fibreProd.base π₁ π₂)) ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two]
  intro z hz
  refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun _ _ h h' => ?_)
  · have hx₂ : BoundedAlg.toAlgHom π₂ x.1.2 = 0 :=
      (show BoundedAlg.toAlgHom π₁ x.1.1 = BoundedAlg.toAlgHom π₂ x.1.2 from x.2).symm.trans hx
    have hy₂ : BoundedAlg.toAlgHom π₂ y.1.2 = 0 :=
      (show BoundedAlg.toAlgHom π₁ y.1.1 = BoundedAlg.toAlgHom π₂ y.1.2 from y.2).symm.trans hy
    exact Subtype.ext (Prod.ext (mul_eq_zero_of_sq_eq_bot h₁ hx hy)
      (mul_eq_zero_of_sq_eq_bot h₂ hx₂ hy₂))
  · exact Ideal.add_mem _ h h'

end FibreProduct

section RS

variable (F) [Fact (ℵ₀ < κ)] {Q₁ Q₂ P : BoundedAlg R κ} {π₁ : Q₁ ⟶ P} {π₂ : Q₂ ⟶ P}

/-- The comparison map of the Rim–Schlessinger condition: a section over the fibre product lying
over `x` gives a pair of sections over the two factors lying over `x`. -/
def fibreProdFibMap (x : F.obj P) :
    Fib (F := F) (fibreProd.base π₁ π₂) x → Fib (F := F) π₁ x × Fib (F := F) π₂ x :=
  fun ξ => (⟨F.map (fibreProd.fst π₁ π₂) ξ.1, by
      rw [← Functor.map_comp_apply]; exact ξ.2⟩,
    ⟨F.map (fibreProd.snd π₁ π₂) ξ.1, by
      rw [← Functor.map_comp_apply, ← fibreProd.condition]; exact ξ.2⟩)

variable {F}

namespace EtaleChart

variable (c : EtaleChart F)

/-- **The Rim–Schlessinger condition at a chart point.** For two surjections onto `P` with
square-zero kernels, the sections over the fibre product lying over a chart point are the
pairs of sections over the two factors lying over it. -/
theorem bijective_fibreProdFibMap (h₁ : Function.Surjective (BoundedAlg.toAlgHom π₁))
    (h₂ : Function.Surjective (BoundedAlg.toAlgHom π₂))
    (k₁ : RingHom.ker (BoundedAlg.toAlgHom π₁) ^ 2 = ⊥)
    (k₂ : RingHom.ker (BoundedAlg.toAlgHom π₂) ^ 2 = ⊥) (ρ₀ : c.C ⟶ P.obj) :
    Function.Bijective (fibreProdFibMap F (π₁ := π₁) (π₂ := π₂) (c.α.app P ρ₀)) := by
  -- the map on chart lifts
  let φ : c.ChartFib (fibreProd.base π₁ π₂) ρ₀ → c.ChartFib π₁ ρ₀ × c.ChartFib π₂ ρ₀ :=
    fun ρ => (⟨ρ.1 ≫ (fibreProd.fst π₁ π₂).hom, by rw [Category.assoc]; exact ρ.2⟩,
      ⟨ρ.1 ≫ (fibreProd.snd π₁ π₂).hom, by
        rw [Category.assoc]
        refine Eq.trans ?_ ρ.2
        change ρ.1 ≫ (fibreProd.snd π₁ π₂ ≫ π₂).hom = ρ.1 ≫ (fibreProd.fst π₁ π₂ ≫ π₁).hom
        rw [fibreProd.condition]⟩)
  have hφ : Function.Bijective φ :=
    ⟨fun ρ ρ' h => Subtype.ext (fibreProd.hom_ext π₁ π₂
      (congrArg Subtype.val (congrArg Prod.fst h)) (congrArg Subtype.val (congrArg Prod.snd h))),
      fun p => ⟨⟨fibreProd.lift π₁ π₂ p.1.1 p.2.1 (p.1.2.trans p.2.2.symm), p.1.2⟩, rfl⟩⟩
  have hcomm : fibreProdFibMap F (c.α.app P ρ₀) ∘ c.chartFibMap _ ρ₀ =
      Prod.map (c.chartFibMap π₁ ρ₀) (c.chartFibMap π₂ ρ₀) ∘ φ :=
    funext fun _ => Prod.ext (Subtype.ext (c.map_α _ _)) (Subtype.ext (c.map_α _ _))
  refine (Function.Bijective.of_comp_iff _ (c.bijective_chartFibMap _
    (fibreProd.surjective_base h₁ h₂) (fibreProd.ker_base_sq k₁ k₂) ρ₀)).1 ?_
  rw [hcomm]
  exact ((c.bijective_chartFibMap π₁ h₁ k₁ ρ₀).prodMap
    (c.bijective_chartFibMap π₂ h₂ k₂ ρ₀)).comp hφ

/-- **The Rim–Schlessinger condition at a chart point**, for a chart point given by a
property. -/
theorem bijective_fibreProdFibMap_of_isChartPoint
    (h₁ : Function.Surjective (BoundedAlg.toAlgHom π₁))
    (h₂ : Function.Surjective (BoundedAlg.toAlgHom π₂))
    (k₁ : RingHom.ker (BoundedAlg.toAlgHom π₁) ^ 2 = ⊥)
    (k₂ : RingHom.ker (BoundedAlg.toAlgHom π₂) ^ 2 = ⊥) {x : F.obj P} (hx : c.IsChartPoint x) :
    Function.Bijective (fibreProdFibMap F (π₁ := π₁) (π₂ := π₂) x) := by
  obtain ⟨ρ₀, rfl⟩ := hx
  exact c.bijective_fibreProdFibMap h₁ h₂ k₁ k₂ ρ₀

end EtaleChart

end RS

end Stacks.ChartedFunctor

end
