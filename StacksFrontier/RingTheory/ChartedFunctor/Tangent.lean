module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.RingTheory.ChartedFunctor.LiftDifference

/-!
# The tangent of a charted functor at a section

Let `F` be a functor on bounded `R`-algebras with an étale chart, let `P` be an algebra with an
ideal `J`, and let `x` be a section of `F` over `P̄ = P ⧸ J`. The **tangent** of `F` at `x` with
coefficients in the conormal module `J/J²` is the set of sections of `F` over the trivial
square-zero extension `P̄ ⊕ J/J²` lying over `x`.

Its abelian group and module structures are defined intrinsically from `F`: the sum of two
tangent vectors is the image under the ring map `(a, m), (a, m') ↦ (a, m + m')` of the section
over the fibre product `(P̄ ⊕ J/J²) ×_{P̄} (P̄ ⊕ J/J²)` which the Rim–Schlessinger condition
attaches to the pair, and scalar multiplication by `a ∈ P̄` is the image under
`(b, m) ↦ (b, a m)`. So every map of algebras compatible with the ideals induces an additive,
semilinear map of tangents, with no reference to a chart. When `x` comes from the chart the
axioms hold, because the chart identifies the tangent with the derivations of `C` along the
chart point valued in `J/J²`, compatibly with all the operations.

## Main definitions

* `Stacks.ChartedFunctor.quot`, `Stacks.ChartedFunctor.sqZero`: the algebras `P ⧸ J` and
  `P̄ ⊕ J/J²`.
* `Stacks.ChartedFunctor.Tan`: the tangent of `F` at a section over `P ⧸ J`.
* `Stacks.ChartedFunctor.Tan.map`: the map of tangents along a map of algebras.

## Main results

* `Stacks.ChartedFunctor.Tan.instAddCommGroup`, `Stacks.ChartedFunctor.Tan.instModule`: at a
  chart point the tangent is a `P̄`-module.
* `Stacks.ChartedFunctor.Tan.chartVec_add` and its companions: the chart description of the
  operations.

## Implementation notes

`TrivSqZeroExt` asks for a right action of the base ring on the coefficient module; for a
commutative base this is the left action read through the opposite ring, which is supplied by
the scoped instance `Stacks.ChartedFunctor.opModule`.

## References

* [Stacks Project, Tag 06I1](https://stacks.math.columbia.edu/tag/06I1)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace Stacks.ChartedFunctor

/-! ### The right action through the opposite ring -/

section OpModule

variable {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]

/-- The action of a commutative ring on a module, read as an action of the opposite ring. -/
@[instance_reducible]
noncomputable def opModule : Module Aᵐᵒᵖ M :=
  Module.compHom M ((RingEquiv.toOpposite A).symm : Aᵐᵒᵖ →+* A)

attribute [scoped instance] opModule

/-- Through `opModule`, the actions of `A` and of `Aᵐᵒᵖ` on `M` agree. -/
scoped instance : IsCentralScalar A M := ⟨fun _ _ => rfl⟩

/-- The actions of `A` and of `Aᵐᵒᵖ` on `M` commute. -/
scoped instance : SMulCommClass A Aᵐᵒᵖ M :=
  ⟨fun p q m => show p • (MulOpposite.unop q • m) = MulOpposite.unop q • p • m by
    rw [smul_comm]⟩

/-- For an `S`-algebra `A`, the action of `Aᵐᵒᵖ` on `M` is a tower over `S`. -/
scoped instance {S : Type*} [CommRing S] [Algebra S A] [Module S M] [IsScalarTower S A M] :
    IsScalarTower S Aᵐᵒᵖ M :=
  ⟨fun r p m => show MulOpposite.unop (r • p) • m = r • (MulOpposite.unop p • m) by
    rw [MulOpposite.unop_smul, smul_assoc]⟩

end OpModule

/-- The conormal module of an ideal is a tower over the base ring and the quotient. -/
instance instIsScalarTowerCotangent {S P : Type*} [CommRing S] [CommRing P] [Algebra S P]
    (J : Ideal P) : IsScalarTower S (P ⧸ J) J.Cotangent := by
  refine ⟨fun r a m => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h₁ : r • Ideal.Quotient.mk J a = algebraMap P (P ⧸ J) (algebraMap S P r * a) := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl
  have h₂ : Ideal.Quotient.mk J a = algebraMap P (P ⧸ J) a := rfl
  rw [h₁, h₂, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul, mul_smul,
    algebraMap_smul]

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
  {F : BoundedAlg R κ ⥤ Type u}

/-! ### The algebras -/

section Algebras

variable (P : BoundedAlg R κ) (J : Ideal P.obj)

/-- The quotient `P ⧸ J`. -/
abbrev quot : BoundedAlg R κ := BoundedAlg.of (P.obj ⧸ J) (mk_quotient_lt J P.2)

/-- The quotient map `P ⟶ P ⧸ J`. -/
abbrev quotMk : P ⟶ quot P J := BoundedAlg.ofHom (Ideal.Quotient.mkₐ R J)

omit [Fact (ℵ₀ < κ)] in
/-- The conormal module `J/J²` has cardinality less than `κ`. -/
lemma mk_cotangent_lt : #J.Cotangent < κ :=
  ((Cardinal.mk_le_of_surjective J.toCotangent_surjective).trans
    (Cardinal.mk_subtype_le _)).trans_lt P.2

/-- The trivial square-zero extension `P̄ ⊕ J/J²` of `P̄ = P ⧸ J` by the conormal module. -/
abbrev sqZero : BoundedAlg R κ :=
  BoundedAlg.of (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent)
    (mk_prod_lt (Fact.out : ℵ₀ < κ).le (quot P J).2 (mk_cotangent_lt P J))

/-- The projection `P̄ ⊕ J/J² ⟶ P̄`. -/
abbrev sqZeroFst : sqZero P J ⟶ quot P J :=
  BoundedAlg.ofHom (TrivSqZeroExt.fstHom R (P.obj ⧸ J) J.Cotangent)

/-- The zero section `P̄ ⟶ P̄ ⊕ J/J²`. -/
abbrev sqZeroInl : quot P J ⟶ sqZero P J :=
  BoundedAlg.ofHom (TrivSqZeroExt.inlAlgHom R (P.obj ⧸ J) J.Cotangent)

/-- Multiplication by `a ∈ P̄` on the coefficients, `(b, m) ↦ (b, a m)`. -/
abbrev sqZeroSmul (a : P.obj ⧸ J) : sqZero P J ⟶ sqZero P J :=
  BoundedAlg.ofHom ((TrivSqZeroExt.map (a • LinearMap.id)).restrictScalars R)

/-- Addition of the coefficients, `(a, m), (a, m') ↦ (a, m + m')`, out of the fibre product. -/
def sqZeroAdd : fibreProd (sqZeroFst P J) (sqZeroFst P J) ⟶ sqZero P J :=
  BoundedAlg.ofHom
    { toFun := fun z => (z.1.1.fst, z.1.1.snd + z.1.2.snd)
      map_one' := by
        ext
        · rfl
        · change (1 : TrivSqZeroExt (P.obj ⧸ J) J.Cotangent).snd +
            (1 : TrivSqZeroExt (P.obj ⧸ J) J.Cotangent).snd = 0
          simp
      map_mul' := fun z w => by
        have hz : z.1.1.fst = z.1.2.fst := z.2
        have hw : w.1.1.fst = w.1.2.fst := w.2
        ext
        · rfl
        · change (z.1.1 * w.1.1).snd + (z.1.2 * w.1.2).snd =
            z.1.1.fst • (w.1.1.snd + w.1.2.snd) +
              MulOpposite.op w.1.1.fst • (z.1.1.snd + z.1.2.snd)
          rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_mul, ← hz, ← hw]
          simp only [smul_add]
          abel
      map_zero' := by
        ext
        · rfl
        · change (0 : TrivSqZeroExt (P.obj ⧸ J) J.Cotangent).snd +
            (0 : TrivSqZeroExt (P.obj ⧸ J) J.Cotangent).snd = 0
          simp
      map_add' := fun z w => by
        ext
        · rfl
        · change (z.1.1 + w.1.1).snd + (z.1.2 + w.1.2).snd =
            z.1.1.snd + z.1.2.snd + (w.1.1.snd + w.1.2.snd)
          simp only [TrivSqZeroExt.snd_add]
          abel
      commutes' := fun r => by
        ext
        · rfl
        · change (algebraMap R (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent) r).snd +
            (algebraMap R (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent) r).snd =
              (algebraMap R (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent) r).snd
          simp only [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, add_zero] }

/-- The zero section is a section of the projection `P̄ ⊕ J/J² ⟶ P̄`. -/
lemma sqZeroInl_fst : sqZeroInl P J ≫ sqZeroFst P J = 𝟙 _ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- Multiplication by `a` on the coefficients lies over the identity of `P̄`. -/
lemma sqZeroSmul_fst (a : P.obj ⧸ J) : sqZeroSmul P J a ≫ sqZeroFst P J = sqZeroFst P J :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => TrivSqZeroExt.fst_map _ _

/-- Addition of the coefficients lies over the base map of the fibre product to `P̄`. -/
lemma sqZeroAdd_fst : sqZeroAdd P J ≫ sqZeroFst P J = fibreProd.base _ _ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The projection `P̄ ⊕ J/J² ⟶ P̄` is a square-zero extension. -/
lemma isSqZeroExt_sqZeroFst : IsSqZeroExt (sqZeroFst P J) := by
  refine ⟨fun a => ⟨TrivSqZeroExt.inl a, rfl⟩, ?_⟩
  rw [eq_bot_iff, pow_two]
  intro z hz
  refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun _ _ h h' => Ideal.add_mem _ h h')
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  show x * y = 0
  ext
  · simp [hx']
  · simp [hx', hy']

end Algebras

/-! ### The tangent and its operations -/

section Tangent

variable (F) (P : BoundedAlg R κ) (J : Ideal P.obj)

/-- **The tangent of `F` at a section `x` over `P ⧸ J`**, with coefficients in the conormal
module: the sections of `F` over `P̄ ⊕ J/J²` lying over `x`. -/
abbrev Tan (x : F.obj (quot P J)) : Type u := Fib (F := F) (sqZeroFst P J) x

/-- A section of `F` *has a chart point* when some étale chart of `F` passes through it. -/
def HasChartPoint {P : BoundedAlg R κ} (x : F.obj P) : Prop :=
  ∃ c : EtaleChart F, c.IsChartPoint x

variable {F P J}

omit [Fact (ℵ₀ < κ)] in
/-- The image of a section with a chart point has a chart point. -/
lemma HasChartPoint.map {P Q : BoundedAlg R κ} {x : F.obj P} (hx : HasChartPoint F x)
    (f : P ⟶ Q) : HasChartPoint F (F.map f x) :=
  hx.imp fun c hc => hc.map c f

namespace Tan

variable {x : F.obj (quot P J)}

/-- The zero tangent vector: the image of `x` under the zero section `P̄ ⟶ P̄ ⊕ J/J²`. -/
instance : Zero (Tan F P J x) :=
  ⟨⟨F.map (sqZeroInl P J) x, by
    rw [← Functor.map_comp_apply, sqZeroInl_fst, Functor.map_id_apply]⟩⟩

/-- The zero tangent vector is the image of `x` under the zero section. -/
lemma zero_val : (0 : Tan F P J x).1 = F.map (sqZeroInl P J) x := rfl

/-- Scalar multiplication by `a ∈ P̄`: the image of a tangent vector under `(b, m) ↦ (b, a m)`. -/
instance : SMul (P.obj ⧸ J) (Tan F P J x) :=
  ⟨fun a w => ⟨F.map (sqZeroSmul P J a) w.1, by
    rw [← Functor.map_comp_apply, sqZeroSmul_fst, w.2]⟩⟩

/-- The tangent vector `a • w` is the image of `w` under `(b, m) ↦ (b, a m)`. -/
lemma smul_val (a : P.obj ⧸ J) (w : Tan F P J x) :
    (a • w).1 = F.map (sqZeroSmul P J a) w.1 := rfl

/-- The sum of two tangent vectors: the image under `(a, m), (a, m') ↦ (a, m + m')` of a section
over the fibre product gluing them. -/
protected noncomputable def add (w w' : Tan F P J x) : Tan F P J x := by
  classical
  exact if h : ∃ ξ, fibreProdFibMap F (π₁ := sqZeroFst P J) (π₂ := sqZeroFst P J) x ξ =
      (w, w') then ⟨F.map (sqZeroAdd P J) h.choose.1, by
        rw [← Functor.map_comp_apply, sqZeroAdd_fst, h.choose.2]⟩ else w

/-- The sum of tangent vectors is `Tan.add`. -/
instance : Add (Tan F P J x) := ⟨Tan.add⟩

/-- The sum of two tangent vectors is computed by any section over the fibre product which
glues them, as soon as such a gluing is unique. -/
lemma add_eq (w w' : Tan F P J x)
    (ξ : Fib (F := F) (fibreProd.base (sqZeroFst P J) (sqZeroFst P J)) x)
    (hξ : fibreProdFibMap F x ξ = (w, w'))
    (hinj : Function.Injective
      (fibreProdFibMap F (π₁ := sqZeroFst P J) (π₂ := sqZeroFst P J) x)) :
    w + w' = ⟨F.map (sqZeroAdd P J) ξ.1, by
      rw [← Functor.map_comp_apply, sqZeroAdd_fst]; exact ξ.2⟩ := by
  have h : ∃ ξ, fibreProdFibMap F (π₁ := sqZeroFst P J) (π₂ := sqZeroFst P J) x ξ = (w, w') :=
    ⟨ξ, hξ⟩
  have hc : h.choose = ξ := hinj (h.choose_spec.trans hξ.symm)
  show Tan.add w w' = _
  simp only [Tan.add, dite_eq_left h]
  exact Subtype.ext (congrArg (fun ζ : Fib (F := F) (fibreProd.base (sqZeroFst P J)
    (sqZeroFst P J)) x => F.map (sqZeroAdd P J) ζ.1) hc)

/-- The negative of a tangent vector is its multiple by `-1 ∈ P̄`. -/
instance : Neg (Tan F P J x) := ⟨fun w => (-1 : P.obj ⧸ J) • w⟩

/-- The difference `w - w'` of tangent vectors is `w + -w'`. -/
instance : Sub (Tan F P J x) := ⟨fun w w' => w + -w'⟩

/-- The multiple of a tangent vector by `n : ℕ` is its multiple by the image of `n` in `P̄`. -/
instance : SMul ℕ (Tan F P J x) := ⟨fun n w => (n : P.obj ⧸ J) • w⟩

/-- The multiple of a tangent vector by `n : ℤ` is its multiple by the image of `n` in `P̄`. -/
instance : SMul ℤ (Tan F P J x) := ⟨fun n w => (n : P.obj ⧸ J) • w⟩

/-- The multiple of a tangent vector by `r ∈ R` is its multiple by the image of `r` in `P̄`. -/
instance : SMul R (Tan F P J x) := ⟨fun r w => algebraMap R (P.obj ⧸ J) r • w⟩

/-- The negative of a tangent vector is its multiple by `-1 ∈ P̄`. -/
lemma neg_def (w : Tan F P J x) : -w = (-1 : P.obj ⧸ J) • w := rfl
/-- The difference `w - w'` of tangent vectors is `w + -w'`. -/
lemma sub_def (w w' : Tan F P J x) : w - w' = w + -w' := rfl
/-- The multiple of a tangent vector by `n : ℕ` is its multiple by the image of `n` in `P̄`. -/
lemma nsmul_def (n : ℕ) (w : Tan F P J x) : n • w = (n : P.obj ⧸ J) • w := rfl
/-- The multiple of a tangent vector by `n : ℤ` is its multiple by the image of `n` in `P̄`. -/
lemma zsmul_def (n : ℤ) (w : Tan F P J x) : n • w = (n : P.obj ⧸ J) • w := rfl
/-- The multiple of a tangent vector by `r ∈ R` is its multiple by the image of `r` in `P̄`. -/
lemma rsmul_def (r : R) (w : Tan F P J x) : r • w = algebraMap R (P.obj ⧸ J) r • w := rfl

/-! ### The chart description -/

section Chart

variable (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj} (h : c.α.app (quot P J) ρ₀ = x)

/-- **The chart description of a tangent vector**: the coefficient part of its chart lift
`C ⟶ P̄ ⊕ J/J²`, a derivation of `C` along the chart point valued in `J/J²`. -/
def chartVec (w : Tan F P J x) : c.C → J.Cotangent :=
  fun y => ((c.chartLift (isSqZeroExt_sqZeroFst P J) h w).hom y).snd

/-- The chart lift `C ⟶ P̄ ⊕ J/J²` of a tangent vector has base part the chart point `ρ₀`. -/
lemma chartLift_fst (w : Tan F P J x) (y : c.C) :
    ((c.chartLift (isSqZeroExt_sqZeroFst P J) h w).hom y).fst = ρ₀.hom y :=
  congrArg (fun g : c.C ⟶ (quot P J).obj => g.hom y)
    (c.chartLift_comp (isSqZeroExt_sqZeroFst P J) h w)

/-- A tangent vector is determined by its chart description. -/
lemma chartVec_injective : Function.Injective (chartVec c h) := by
  intro w w' hw
  refine c.eq_of_chartLift_eq (isSqZeroExt_sqZeroFst P J) h w w' ?_
  ext y
  · exact (chartLift_fst c h w y).trans (chartLift_fst c h w' y).symm
  · exact congrFun hw y

/-- The chart description of the zero tangent vector is zero. -/
lemma chartVec_zero : chartVec c h (0 : Tan F P J x) = 0 := by
  have e : c.chartLift (isSqZeroExt_sqZeroFst P J) h (0 : Tan F P J x) =
      ρ₀ ≫ (sqZeroInl P J).hom := by
    refine c.chartLift_eq _ h _ _ ?_ ?_
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, sqZeroInl_fst]
      rfl
    · rw [← c.map_α, h]
      rfl
  funext y
  simp only [chartVec, e, Pi.zero_apply]
  rfl

/-- The chart description of `a • w` is `a` times the chart description of `w`. -/
lemma chartVec_smul (a : P.obj ⧸ J) (w : Tan F P J x) :
    chartVec c h (a • w) = a • chartVec c h w := by
  have e : c.chartLift (isSqZeroExt_sqZeroFst P J) h (a • w) =
      c.chartLift (isSqZeroExt_sqZeroFst P J) h w ≫ (sqZeroSmul P J a).hom := by
    refine c.chartLift_eq _ h _ _ ?_ ?_
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, sqZeroSmul_fst]
      exact c.chartLift_comp _ h w
    · rw [← c.map_α, c.α_chartLift]
      rfl
  funext y
  simp only [chartVec, e, Pi.smul_apply]
  exact TrivSqZeroExt.snd_map _ _

/-- **The Rim–Schlessinger condition** for `P̄ ⊕ J/J² ⟶ P̄` at the chart point `ρ₀`. -/
private theorem bijective_fibreProdFibMap_sqZeroFst :
    Function.Bijective
      (fibreProdFibMap F (π₁ := sqZeroFst P J) (π₂ := sqZeroFst P J) (c.α.app _ ρ₀)) :=
  c.bijective_fibreProdFibMap (isSqZeroExt_sqZeroFst P J).surjective
    (isSqZeroExt_sqZeroFst P J).surjective (isSqZeroExt_sqZeroFst P J).sq_eq_bot
    (isSqZeroExt_sqZeroFst P J).sq_eq_bot ρ₀

omit h in
/-- At a chart point `x`, a section of `F` over `(P̄ ⊕ J/J²) ×_{P̄} (P̄ ⊕ J/J²)` lying over `x` is
determined by its two projections. -/
lemma injective_fibreProdFibMap (h : c.α.app (quot P J) ρ₀ = x) :
    Function.Injective
      (fibreProdFibMap F (π₁ := sqZeroFst P J) (π₂ := sqZeroFst P J) x) := by
  subst h
  exact (bijective_fibreProdFibMap_sqZeroFst c).1

/-- The chart description of a sum is the sum of the chart descriptions. -/
lemma chartVec_add (w w' : Tan F P J x) :
    chartVec c h (w + w') = chartVec c h w + chartVec c h w' := by
  set σ₁ := c.chartLift (isSqZeroExt_sqZeroFst P J) h w
  set σ₂ := c.chartLift (isSqZeroExt_sqZeroFst P J) h w'
  have h₁₂ : σ₁ ≫ (sqZeroFst P J).hom = σ₂ ≫ (sqZeroFst P J).hom :=
    (c.chartLift_comp _ h w).trans (c.chartLift_comp _ h w').symm
  set σ := fibreProd.lift (sqZeroFst P J) (sqZeroFst P J) σ₁ σ₂ h₁₂
  have hσb : σ ≫ (fibreProd.base (sqZeroFst P J) (sqZeroFst P J)).hom = ρ₀ :=
    CommAlgCat.hom_ext <| AlgHom.ext fun y => chartLift_fst c h w y
  let ξ : Fib (F := F) (fibreProd.base (sqZeroFst P J) (sqZeroFst P J)) x :=
    ⟨c.α.app (fibreProd (sqZeroFst P J) (sqZeroFst P J)) σ, by rw [c.map_α, hσb, h]⟩
  have hξ : fibreProdFibMap F x ξ = (w, w') := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show F.map _ (c.α.app (fibreProd (sqZeroFst P J) (sqZeroFst P J)) σ) = w.1
      rw [c.map_α, fibreProd.lift_fst, c.α_chartLift]
    · show F.map _ (c.α.app (fibreProd (sqZeroFst P J) (sqZeroFst P J)) σ) = w'.1
      rw [c.map_α, fibreProd.lift_snd, c.α_chartLift]
  have e : c.chartLift (isSqZeroExt_sqZeroFst P J) h (w + w') = σ ≫ (sqZeroAdd P J).hom := by
    refine c.chartLift_eq _ h _ _ ?_ ?_
    · rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, sqZeroAdd_fst]
      exact hσb
    · rw [add_eq w w' ξ hξ (injective_fibreProdFibMap c h), ← c.map_α]
  funext y
  simp only [chartVec, e, Pi.add_apply]
  rfl

/-- The chart description of `-w` is the negative of the chart description of `w`. -/
lemma chartVec_neg (w : Tan F P J x) : chartVec c h (-w) = -chartVec c h w := by
  rw [neg_def, chartVec_smul, neg_one_smul]

/-- The chart description of a difference is the difference of the chart descriptions. -/
lemma chartVec_sub (w w' : Tan F P J x) :
    chartVec c h (w - w') = chartVec c h w - chartVec c h w' := by
  rw [sub_def, chartVec_add, chartVec_neg, sub_eq_add_neg]

/-- The chart description of `n • w`, for `n : ℕ`, is `n` times the chart description of `w`. -/
lemma chartVec_nsmul (n : ℕ) (w : Tan F P J x) : chartVec c h (n • w) = n • chartVec c h w := by
  rw [nsmul_def, chartVec_smul, Nat.cast_smul_eq_nsmul]

/-- The chart description of `n • w`, for `n : ℤ`, is `n` times the chart description of `w`. -/
lemma chartVec_zsmul (n : ℤ) (w : Tan F P J x) : chartVec c h (n • w) = n • chartVec c h w := by
  rw [zsmul_def, chartVec_smul, Int.cast_smul_eq_zsmul]

/-- The chart description of `r • w`, for `r ∈ R`, is `r` times the chart description of `w`. -/
lemma chartVec_rsmul (r : R) (w : Tan F P J x) : chartVec c h (r • w) = r • chartVec c h w := by
  rw [rsmul_def, chartVec_smul, algebraMap_smul]

/-- The chart description of a tangent vector is additive. -/
lemma chartVec_add_apply (w : Tan F P J x) (y y' : c.C) :
    chartVec c h w (y + y') = chartVec c h w y + chartVec c h w y' := by
  simp only [chartVec, map_add, TrivSqZeroExt.snd_add]

/-- The chart description of a tangent vector commutes with multiplication by `r ∈ R`. -/
lemma chartVec_smul_apply (w : Tan F P J x) (r : R) (y : c.C) :
    chartVec c h w (r • y) = r • chartVec c h w y := by
  simp only [chartVec, map_smul, TrivSqZeroExt.snd_smul]

/-- **The chart description of a tangent vector is a derivation along the chart point.** -/
lemma chartVec_mul_apply (w : Tan F P J x) (y y' : c.C) :
    chartVec c h w (y * y') = ρ₀.hom y • chartVec c h w y' + ρ₀.hom y' • chartVec c h w y := by
  simp only [chartVec, map_mul, TrivSqZeroExt.snd_mul, chartLift_fst c h]
  rfl

/-- The algebra map `C ⟶ P̄ ⊕ J/J²`, `y ↦ (ρ₀ y, d y)`, attached to a derivation `d` of `C`
along `ρ₀` valued in `J/J²`. -/
def derivationLift (d : c.C →ₗ[R] J.Cotangent)
    (hd : ∀ y y', d (y * y') = ρ₀.hom y • d y' + ρ₀.hom y' • d y) : c.C ⟶ (sqZero P J).obj :=
  CommAlgCat.ofHom
    { toFun := fun y => (ρ₀.hom y, d y)
      map_one' := by
        have h1 := hd 1 1
        simp only [mul_one, map_one, one_smul] at h1
        ext
        · exact map_one _
        · change d 1 = 0
          have h2 : d 1 + d 1 = d 1 + 0 := by rw [← h1, add_zero]
          exact (add_left_cancel h2)
      map_mul' := fun y y' => by
        ext
        · exact map_mul _ _ _
        · change d (y * y') = ρ₀.hom y • d y' + MulOpposite.op (ρ₀.hom y') • d y
          exact hd y y'
      map_zero' := by
        ext
        · exact map_zero _
        · exact map_zero d
      map_add' := fun y y' => by
        ext
        · exact map_add _ _ _
        · exact map_add d y y'
      commutes' := fun r => by
        have h1 := hd 1 1
        simp only [mul_one, map_one, one_smul] at h1
        have hd1 : d 1 = 0 := by
          have h2 : d 1 + d 1 = d 1 + 0 := by rw [← h1, add_zero]
          exact (add_left_cancel h2)
        ext
        · exact AlgHom.commutes _ r
        · change d (algebraMap R c.C r) =
            (algebraMap R (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent) r).snd
          rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero,
            TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl] }

/-- **Every derivation of `C` along the chart point is the chart description of a tangent
vector.** -/
lemma exists_chartVec_eq (d : c.C →ₗ[R] J.Cotangent)
    (hd : ∀ y y', d (y * y') = ρ₀.hom y • d y' + ρ₀.hom y' • d y) :
    ∃ w : Tan F P J x, chartVec c h w = d := by
  have hσ : derivationLift c d hd ≫ (sqZeroFst P J).hom = ρ₀ :=
    CommAlgCat.hom_ext <| AlgHom.ext fun _ => rfl
  let w : Tan F P J x := ⟨c.α.app _ (derivationLift c d hd), by rw [c.map_α, hσ, h]⟩
  refine ⟨w, ?_⟩
  have e : c.chartLift (isSqZeroExt_sqZeroFst P J) h w = derivationLift c d hd :=
    c.chartLift_eq _ h w _ hσ rfl
  funext y
  simp only [chartVec, e]
  rfl

end Chart

/-! ### The module structure at a chart point -/

section Instances

variable [hx : Fact (HasChartPoint F x)]

/-- A chart through `x`, chosen once and for all. -/
noncomputable def someChart : EtaleChart F := hx.out.choose

/-- The chart point of `someChart` over `x`. -/
noncomputable def someChartPoint : (someChart (x := x)).C ⟶ (quot P J).obj :=
  hx.out.choose_spec.choose

omit [Fact (ℵ₀ < κ)] in
/-- The chart `someChart` carries `someChartPoint` to `x`. -/
lemma someChartPoint_spec : (someChart (x := x)).α.app (quot P J) someChartPoint = x :=
  hx.out.choose_spec.choose_spec

/-- **The tangent at a chart point is an abelian group**, with the intrinsic operations. -/
noncomputable instance instAddCommGroup : AddCommGroup (Tan F P J x) :=
  Function.Injective.addCommGroup _ (chartVec_injective _ someChartPoint_spec)
    (chartVec_zero _ someChartPoint_spec) (chartVec_add _ someChartPoint_spec)
    (chartVec_neg _ someChartPoint_spec) (chartVec_sub _ someChartPoint_spec)
    (fun w n => chartVec_nsmul _ someChartPoint_spec n w)
    (fun w n => chartVec_zsmul _ someChartPoint_spec n w)

/-- The chart description, as an additive map. -/
noncomputable def chartVecHom (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) : Tan F P J x →+ (c.C → J.Cotangent) where
  toFun := chartVec c h
  map_zero' := chartVec_zero c h
  map_add' := chartVec_add c h

/-- **The tangent at a chart point is a `P ⧸ J`-module.** -/
noncomputable instance instModule : Module (P.obj ⧸ J) (Tan F P J x) :=
  Function.Injective.module _ (chartVecHom _ someChartPoint_spec)
    (chartVec_injective _ someChartPoint_spec) (chartVec_smul _ someChartPoint_spec)

/-- The tangent at a chart point is an `R`-module. -/
noncomputable instance instModuleBase : Module R (Tan F P J x) :=
  Function.Injective.module _ (chartVecHom _ someChartPoint_spec)
    (chartVec_injective _ someChartPoint_spec) (chartVec_rsmul _ someChartPoint_spec)

/-- At a chart point, the tangent is a tower over `R` and `P ⧸ J`. -/
instance : IsScalarTower R (P.obj ⧸ J) (Tan F P J x) :=
  ⟨fun r a w => by
    apply chartVec_injective _ (someChartPoint_spec (x := x))
    show chartVec _ _ ((r • a) • w) = chartVec _ _ (r • a • w)
    rw [chartVec_smul, chartVec_rsmul, chartVec_smul, smul_assoc]⟩

end Instances

end Tan

end Tangent

/-! ### Functoriality -/

section Functoriality

variable {P P' : BoundedAlg R κ} {J : Ideal P.obj} {J' : Ideal P'.obj} (f : P ⟶ P')
  (hJ : J ≤ J'.comap (BoundedAlg.toAlgHom f))

/-- The map of quotients induced by a map of algebras carrying `J` into `J'`. -/
abbrev quotMap : quot P J ⟶ quot P' J' :=
  BoundedAlg.ofHom (Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ)

omit [Fact (ℵ₀ < κ)] in
/-- The map of quotients commutes with the quotient maps. -/
lemma quotMk_quotMap : quotMk P J ≫ quotMap f hJ = f ≫ quotMk P' J' :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

omit [Fact (ℵ₀ < κ)] in
/-- The map of conormal modules is semilinear over the map of quotients. -/
lemma mapCotangent_smul (a : P.obj ⧸ J) (m : J.Cotangent) :
    J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (a • m) =
      Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ a •
        J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ m := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨j, rfl⟩ := J.toCotangent_surjective m
  show J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (a • J.toCotangent j) =
    BoundedAlg.toAlgHom f a • J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (J.toCotangent j)
  rw [← map_smul, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, ← map_smul]
  congr 1
  apply Subtype.ext
  simp

/-- The map of trivial square-zero extensions induced by a map of algebras carrying `J`
into `J'`: `(a, m) ↦ (f a, f m)`. -/
def sqZeroMap : sqZero P J ⟶ sqZero P' J' :=
  BoundedAlg.ofHom
    { toFun := fun t => (Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ t.fst,
        J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ t.snd)
      map_one' := by
        ext
        · exact map_one _
        · exact map_zero _
      map_mul' := fun t t' => by
        ext
        · exact map_mul _ _ _
        · change J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (t * t').snd =
            Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ t.fst •
                J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ t'.snd +
              MulOpposite.op (Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ t'.fst) •
                J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ t.snd
          rw [TrivSqZeroExt.snd_mul, map_add]
          exact congrArg₂ (· + ·) (mapCotangent_smul f hJ _ _) (mapCotangent_smul f hJ _ _)
      map_zero' := by ext <;> exact map_zero _
      map_add' := fun t t' => by ext <;> exact map_add _ _ _
      commutes' := fun r => by
        ext
        · exact AlgHom.commutes _ r
        · change J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ
            (algebraMap R (TrivSqZeroExt (P.obj ⧸ J) J.Cotangent) r).snd =
              (algebraMap R (TrivSqZeroExt (P'.obj ⧸ J') J'.Cotangent) r).snd
          simp only [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, map_zero] }

/-- The map of square-zero extensions lies over the map of quotients. -/
lemma sqZeroMap_fst : sqZeroMap f hJ ≫ sqZeroFst P' J' = sqZeroFst P J ≫ quotMap f hJ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The map of square-zero extensions commutes with the zero sections. -/
lemma sqZeroInl_sqZeroMap : sqZeroInl P J ≫ sqZeroMap f hJ = quotMap f hJ ≫ sqZeroInl P' J' := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun a => ?_
  ext
  · rfl
  · exact map_zero _

/-- The map of square-zero extensions carries multiplication by `a` on the coefficients to
multiplication by the image of `a`. -/
lemma sqZeroSmul_sqZeroMap (a : P.obj ⧸ J) :
    sqZeroSmul P J a ≫ sqZeroMap f hJ =
      sqZeroMap f hJ ≫ sqZeroSmul P' J' (Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ a) := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun t => ?_
  show (BoundedAlg.toAlgHom (sqZeroMap f hJ)) (TrivSqZeroExt.map (a • LinearMap.id) t) =
    TrivSqZeroExt.map (_ • LinearMap.id) ((BoundedAlg.toAlgHom (sqZeroMap f hJ)) t)
  ext
  · rw [TrivSqZeroExt.fst_map]
    show Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ (TrivSqZeroExt.map _ t).fst = _
    rw [TrivSqZeroExt.fst_map]
    rfl
  · rw [TrivSqZeroExt.snd_map]
    show J.mapCotangent J' (BoundedAlg.toAlgHom f) hJ (TrivSqZeroExt.map _ t).snd = _
    rw [TrivSqZeroExt.snd_map]
    exact mapCotangent_smul f hJ a t.snd

/-- The map of fibre products of trivial square-zero extensions. -/
def sqZeroPairMap :
    fibreProd (sqZeroFst P J) (sqZeroFst P J) ⟶ fibreProd (sqZeroFst P' J') (sqZeroFst P' J') :=
  BoundedAlg.ofHom
    (AlgHom.codRestrict
      (((BoundedAlg.toAlgHom (sqZeroMap f hJ)).comp
          ((AlgHom.fst R _ _).comp (Subalgebra.val _))).prod
        ((BoundedAlg.toAlgHom (sqZeroMap f hJ)).comp
          ((AlgHom.snd R _ _).comp (Subalgebra.val _)))) _
      fun z => by
        change Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ z.1.1.fst =
          Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ z.1.2.fst
        exact congrArg _ z.2)

/-- The map of fibre products commutes with the first projections. -/
lemma sqZeroPairMap_fst :
    sqZeroPairMap f hJ ≫ fibreProd.fst (sqZeroFst P' J') (sqZeroFst P' J') =
      fibreProd.fst (sqZeroFst P J) (sqZeroFst P J) ≫ sqZeroMap f hJ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The map of fibre products commutes with the second projections. -/
lemma sqZeroPairMap_snd :
    sqZeroPairMap f hJ ≫ fibreProd.snd (sqZeroFst P' J') (sqZeroFst P' J') =
      fibreProd.snd (sqZeroFst P J) (sqZeroFst P J) ≫ sqZeroMap f hJ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The maps of square-zero extensions commute with addition of the coefficients. -/
lemma sqZeroAdd_sqZeroMap :
    sqZeroAdd P J ≫ sqZeroMap f hJ = sqZeroPairMap f hJ ≫ sqZeroAdd P' J' := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun z => ?_
  ext
  · rfl
  · exact map_add _ _ _

variable {x : F.obj (quot P J)} {x' : F.obj (quot P' J')} (hx : F.map (quotMap f hJ) x = x')

/-- **The map of tangents** induced by a map of algebras carrying `J` into `J'`. -/
def Tan.map (w : Tan F P J x) : Tan F P' J' x' :=
  ⟨F.map (sqZeroMap f hJ) w.1, by
    rw [← Functor.map_comp_apply, sqZeroMap_fst, Functor.map_comp_apply, w.2, hx]⟩

/-- The image of a tangent vector is its image under the map of square-zero extensions. -/
lemma Tan.map_val (w : Tan F P J x) : (Tan.map f hJ hx w).1 = F.map (sqZeroMap f hJ) w.1 := rfl

/-- The map of tangents carries zero to zero. -/
lemma Tan.map_zero : Tan.map f hJ hx (0 : Tan F P J x) = 0 := by
  apply Subtype.ext
  show F.map (sqZeroMap f hJ) (F.map (sqZeroInl P J) x) = F.map (sqZeroInl P' J') x'
  rw [← Functor.map_comp_apply, sqZeroInl_sqZeroMap, Functor.map_comp_apply, hx]

/-- The map of tangents is semilinear over the map of quotients. -/
lemma Tan.map_smul (a : P.obj ⧸ J) (w : Tan F P J x) :
    Tan.map f hJ hx (a • w) =
      Ideal.quotientMapₐ J' (BoundedAlg.toAlgHom f) hJ a • Tan.map f hJ hx w := by
  apply Subtype.ext
  show F.map (sqZeroMap f hJ) (F.map (sqZeroSmul P J a) w.1) =
    F.map (sqZeroSmul P' J' _) (F.map (sqZeroMap f hJ) w.1)
  rw [← Functor.map_comp_apply, sqZeroSmul_sqZeroMap, Functor.map_comp_apply]

/-- **Maps of tangents are additive**, between chart points. -/
lemma Tan.map_add (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
    (h : c.α.app (quot P J) ρ₀ = x) (w w' : Tan F P J x) :
    Tan.map f hJ hx (w + w') = Tan.map f hJ hx w + Tan.map f hJ hx w' := by
  obtain ⟨ξ, hξ⟩ := (Tan.bijective_fibreProdFibMap_sqZeroFst c (ρ₀ := ρ₀)).2
    ((⟨w.1, w.2.trans h.symm⟩ : Tan F P J (c.α.app _ ρ₀)), ⟨w'.1, w'.2.trans h.symm⟩)
  let ξ₀ : Fib (F := F) (fibreProd.base (sqZeroFst P J) (sqZeroFst P J)) x := ⟨ξ.1, ξ.2.trans h⟩
  have hξ₀ : fibreProdFibMap F x ξ₀ = (w, w') :=
    Prod.ext (Subtype.ext (congrArg (fun p => p.1.1) hξ))
      (Subtype.ext (congrArg (fun p => p.2.1) hξ))
  let ξ' : Fib (F := F) (fibreProd.base (sqZeroFst P' J') (sqZeroFst P' J')) x' :=
    ⟨F.map (sqZeroPairMap f hJ) ξ₀.1, by
      rw [← Functor.map_comp_apply]
      show F.map (sqZeroPairMap f hJ ≫ fibreProd.fst _ _ ≫ sqZeroFst P' J') ξ₀.1 = x'
      rw [← Category.assoc, sqZeroPairMap_fst, Category.assoc, sqZeroMap_fst,
        ← Category.assoc, Functor.map_comp_apply, ξ₀.2, hx]⟩
  have hξ' : fibreProdFibMap F x' ξ' = (Tan.map f hJ hx w, Tan.map f hJ hx w') := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show F.map (fibreProd.fst _ _) (F.map (sqZeroPairMap f hJ) ξ₀.1) =
        F.map (sqZeroMap f hJ) w.1
      rw [← Functor.map_comp_apply, sqZeroPairMap_fst, Functor.map_comp_apply]
      exact congrArg (fun p => F.map (sqZeroMap f hJ) p.1.1) hξ₀
    · show F.map (fibreProd.snd _ _) (F.map (sqZeroPairMap f hJ) ξ₀.1) =
        F.map (sqZeroMap f hJ) w'.1
      rw [← Functor.map_comp_apply, sqZeroPairMap_snd, Functor.map_comp_apply]
      exact congrArg (fun p => F.map (sqZeroMap f hJ) p.2.1) hξ₀
  have hx' : c.α.app (quot P' J') (ρ₀ ≫ (quotMap f hJ).hom) = x' := by rw [← c.map_α, h, hx]
  rw [Tan.add_eq w w' ξ₀ hξ₀ (Tan.injective_fibreProdFibMap c h),
    Tan.add_eq _ _ ξ' hξ' (Tan.injective_fibreProdFibMap c hx')]
  apply Subtype.ext
  show F.map (sqZeroMap f hJ) (F.map (sqZeroAdd P J) ξ₀.1) =
    F.map (sqZeroAdd P' J') (F.map (sqZeroPairMap f hJ) ξ₀.1)
  rw [← Functor.map_comp_apply, sqZeroAdd_sqZeroMap, Functor.map_comp_apply]

/-- The map of tangents between chart points, as an `R`-linear map. -/
noncomputable def Tan.mapₗ [Fact (HasChartPoint F x)] [Fact (HasChartPoint F x')] :
    Tan F P J x →ₗ[R] Tan F P' J' x' where
  toFun := Tan.map f hJ hx
  map_add' := Tan.map_add f hJ hx Tan.someChart Tan.someChartPoint_spec
  map_smul' r w := by
    change Tan.map f hJ hx (r • w) = r • Tan.map f hJ hx w
    rw [Tan.rsmul_def, Tan.rsmul_def, Tan.map_smul, AlgHom.commutes]

/-- The linear map of tangents `Tan.mapₗ` is `Tan.map`. -/
@[simp]
lemma Tan.mapₗ_apply [Fact (HasChartPoint F x)] [Fact (HasChartPoint F x')]
    (w : Tan F P J x) : Tan.mapₗ f hJ hx w = Tan.map f hJ hx w := rfl

omit [Fact (ℵ₀ < κ)] in
/-- The map of quotients along a composite is the composite of the maps of quotients. -/
lemma quotMap_comp {P'' : BoundedAlg R κ} {J'' : Ideal P''.obj} (f' : P' ⟶ P'')
    (hJ' : J' ≤ J''.comap (BoundedAlg.toAlgHom f')) :
    quotMap f hJ ≫ quotMap f' hJ' = quotMap (f ≫ f') (fun _ hj => hJ' (hJ hj)) := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun a => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- The map of square-zero extensions along a composite is the composite of the maps. -/
lemma sqZeroMap_comp {P'' : BoundedAlg R κ} {J'' : Ideal P''.obj} (f' : P' ⟶ P'')
    (hJ' : J' ≤ J''.comap (BoundedAlg.toAlgHom f')) :
    sqZeroMap f hJ ≫ sqZeroMap f' hJ' = sqZeroMap (f ≫ f') (fun _ hj => hJ' (hJ hj)) := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun t => ?_
  ext
  · exact congrArg (fun g => BoundedAlg.toAlgHom g t.fst) (quotMap_comp f hJ f' hJ')
  · obtain ⟨j, hj⟩ := J.toCotangent_surjective t.snd
    show J'.mapCotangent J'' _ hJ' (J.mapCotangent J' _ hJ t.snd) = J.mapCotangent J'' _ _ t.snd
    rw [← hj, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    exact (Ideal.mapCotangent_toCotangent _ _ _ _ _).symm

/-- Maps of tangents compose. -/
lemma Tan.map_map {P'' : BoundedAlg R κ} {J'' : Ideal P''.obj} (f' : P' ⟶ P'')
    (hJ' : J' ≤ J''.comap (BoundedAlg.toAlgHom f')) {x'' : F.obj (quot P'' J'')}
    (hx' : F.map (quotMap f' hJ') x' = x'') (w : Tan F P J x) :
    Tan.map f' hJ' hx' (Tan.map f hJ hx w) =
      Tan.map (f ≫ f') (fun j hj => hJ' (hJ hj))
        (by rw [← hx', ← hx, ← Functor.map_comp_apply, quotMap_comp]) w := by
  apply Subtype.ext
  show F.map (sqZeroMap f' hJ') (F.map (sqZeroMap f hJ) w.1) = F.map (sqZeroMap (f ≫ f') _) w.1
  rw [← Functor.map_comp_apply, sqZeroMap_comp]

omit [Fact (ℵ₀ < κ)] in
/-- The ideal is carried into itself by the identity. -/
lemma le_comap_id (J : Ideal P.obj) : J ≤ J.comap (BoundedAlg.toAlgHom (𝟙 P)) := fun _ hj => hj

/-- The map of square-zero extensions along the identity is the identity. -/
lemma sqZeroMap_id : sqZeroMap (𝟙 P) (le_comap_id J) = 𝟙 (sqZero P J) := by
  refine BoundedAlg.hom_ext <| AlgHom.ext fun t => ?_
  ext
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective t.fst
    show Ideal.quotientMapₐ J _ _ t.fst = t.fst
    rw [← ha]
    rfl
  · obtain ⟨j, hj⟩ := J.toCotangent_surjective t.snd
    show J.mapCotangent J _ _ t.snd = t.snd
    rw [← hj]
    exact Ideal.mapCotangent_toCotangent J J _ (le_comap_id J) j

/-- The map of tangents along the identity is the identity. -/
lemma Tan.map_id {x : F.obj (quot P J)} (hx : F.map (quotMap (𝟙 P) (le_comap_id J)) x = x)
    (w : Tan F P J x) : Tan.map (𝟙 P) (le_comap_id J) hx w = w := by
  apply Subtype.ext
  show F.map (sqZeroMap (𝟙 P) _) w.1 = w.1
  rw [sqZeroMap_id, Functor.map_id_apply]

end Functoriality

end Stacks.ChartedFunctor

end
