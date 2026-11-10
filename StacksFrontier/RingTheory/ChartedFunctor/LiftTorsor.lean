module

public import StacksFrontier.RingTheory.ChartedFunctor.Tangent

/-!
# The lifts of a section along a square-zero thickening form a torsor under the tangent

Let `F` be a functor on bounded `R`-algebras with an étale chart, let `P` be an algebra with an
ideal `J` of square zero, and let `x` be a section of `F` over `P ⧸ J` through which a chart
passes. The *lifts* of `x` are the sections of `F` over `P` lying over `x`.

The difference of two lifts `z, z'` is defined intrinsically: the Rim–Schlessinger condition
glues them to a section over `P ×_{P ⧸ J} P`, and its image under the ring map
`(b, b') ↦ (b mod J, (b' - b) mod J²)` to `P̄ ⊕ J/J²` is a tangent vector at `x`. The
difference vanishes exactly on the diagonal, adds up along chains of three lifts, takes every
value from a given lift, and commutes with every map of algebras carrying `J` into `J'`: the
lifts form a torsor under the tangent, compatibly with all maps. This is
[Stacks Project, Tag 06I2] for the functor `F`; it is unconditional, the chart being used only
to verify the identities.

## Main definitions

* `Stacks.ChartedFunctor.Lifts`: the lifts of a section along `P ⟶ P ⧸ J`.
* `Stacks.ChartedFunctor.Lifts.diff`: the difference of two lifts, a tangent vector.
* `Stacks.ChartedFunctor.Lifts.map`: the image of a lift under a map of algebras.

## Main results

* `Stacks.ChartedFunctor.Lifts.diff_add_diff`, `Stacks.ChartedFunctor.Lifts.eq_of_diff_eq_zero`,
  `Stacks.ChartedFunctor.Lifts.exists_diff_eq`: the torsor axioms.
* `Stacks.ChartedFunctor.Lifts.map_diff`: compatibility with maps of algebras.

## References

* [Stacks Project, Tag 06I2](https://stacks.math.columbia.edu/tag/06I2)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace Stacks.ChartedFunctor

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
  {F : BoundedAlg R κ ⥤ Type u}

section Thickening

variable (P : BoundedAlg R κ) (J : Ideal P.obj)

omit [Fact (ℵ₀ < κ)] in
/-- The quotient map by an ideal of square zero is a square-zero extension. -/
lemma isSqZeroExt_quotMk (hJ : J ^ 2 = ⊥) : IsSqZeroExt (quotMk P J) :=
  ⟨Ideal.Quotient.mk_surjective, by
    rwa [show RingHom.ker (BoundedAlg.toAlgHom (quotMk P J)) = J from Ideal.mk_ker]⟩

/-- The map `(b, b') ↦ (b mod J, (b' - b) mod J²)` from `P ×_{P ⧸ J} P` to `P̄ ⊕ J/J²`. -/
def diffMap : fibreProd (quotMk P J) (quotMk P J) ⟶ sqZero P J :=
  BoundedAlg.ofHom
    { toFun := fun z => (Ideal.Quotient.mk J z.1.1,
        J.toCotangent ⟨z.1.2 - z.1.1, Ideal.Quotient.eq.1 z.2.symm⟩)
      map_one' := by
        ext
        · exact map_one _
        · change J.toCotangent ⟨1 - 1, _⟩ = 0
          rw [J.toCotangent_eq_zero]
          simp
      map_mul' := fun z w => by
        have hz : z.1.2 - z.1.1 ∈ J := Ideal.Quotient.eq.1 z.2.symm
        have hw : w.1.2 - w.1.1 ∈ J := Ideal.Quotient.eq.1 w.2.symm
        ext
        · exact map_mul _ _ _
        · change J.toCotangent ⟨z.1.2 * w.1.2 - z.1.1 * w.1.1, _⟩ =
            Ideal.Quotient.mk J z.1.1 • J.toCotangent ⟨w.1.2 - w.1.1, hw⟩ +
              Ideal.Quotient.mk J w.1.1 • J.toCotangent ⟨z.1.2 - z.1.1, hz⟩
          change _ = z.1.1 • J.toCotangent ⟨w.1.2 - w.1.1, hw⟩ +
            w.1.1 • J.toCotangent ⟨z.1.2 - z.1.1, hz⟩
          rw [← map_smul, ← map_smul, ← map_add, J.toCotangent_eq]
          simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
          rw [show z.1.2 * w.1.2 - z.1.1 * w.1.1 -
              (z.1.1 * (w.1.2 - w.1.1) + w.1.1 * (z.1.2 - z.1.1)) =
                (z.1.2 - z.1.1) * (w.1.2 - w.1.1) by ring, pow_two]
          exact Ideal.mul_mem_mul hz hw
      map_zero' := by
        ext
        · exact map_zero _
        · change J.toCotangent ⟨0 - 0, _⟩ = 0
          rw [J.toCotangent_eq_zero]
          simp
      map_add' := fun z w => by
        ext
        · exact map_add _ _ _
        · change J.toCotangent ⟨z.1.2 + w.1.2 - (z.1.1 + w.1.1), _⟩ =
            J.toCotangent ⟨z.1.2 - z.1.1, _⟩ + J.toCotangent ⟨w.1.2 - w.1.1, _⟩
          rw [← map_add]
          congr 1
          apply Subtype.ext
          simp only [Submodule.coe_add]
          ring
      commutes' := fun r => by
        ext
        · exact (Ideal.Quotient.mkₐ R J).commutes r
        · change J.toCotangent _ = _
          rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, J.toCotangent_eq_zero]
          simp }

/-- The first component of `diffMap P J` is the base map `P ×_{P ⧸ J} P ⟶ P ⧸ J`. -/
lemma diffMap_fst : diffMap P J ≫ sqZeroFst P J = fibreProd.base _ _ :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

end Thickening

/-! ### Lifts and their differences -/

variable (F) (P : BoundedAlg R κ) (J : Ideal P.obj)

/-- **The lifts** of a section `x` of `F` over `P ⧸ J`: the sections over `P` lying over it. -/
abbrev Lifts (x : F.obj (quot P J)) : Type u := Fib (F := F) (quotMk P J) x

namespace Lifts

variable {F P J} {x : F.obj (quot P J)}

/-- **The difference of two lifts**, a tangent vector at `x`: the image under
`(b, b') ↦ (b mod J, (b' - b) mod J²)` of a section over `P ×_{P ⧸ J} P` gluing them. -/
protected def diff (z z' : Lifts F P J x) : Tan F P J x := by
  classical
  exact if h : ∃ ζ, fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x ζ = (z, z') then
    ⟨F.map (diffMap P J) h.choose.1, by
      rw [← Functor.map_comp_apply, diffMap_fst]; exact h.choose.2⟩ else 0

/-- The difference of two lifts is computed by any section over the fibre product which glues
them, as soon as such a gluing is unique. -/
lemma diff_eq (z z' : Lifts F P J x)
    (ζ : Fib (F := F) (fibreProd.base (quotMk P J) (quotMk P J)) x)
    (hζ : fibreProdFibMap F x ζ = (z, z'))
    (hinj : Function.Injective
      (fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x)) :
    Lifts.diff z z' = ⟨F.map (diffMap P J) ζ.1, by
      rw [← Functor.map_comp_apply, diffMap_fst]; exact ζ.2⟩ := by
  have h : ∃ ζ, fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x ζ = (z, z') :=
    ⟨ζ, hζ⟩
  have hc : h.choose = ζ := hinj (h.choose_spec.trans hζ.symm)
  simp only [Lifts.diff, dite_eq_left h]
  exact Subtype.ext <|
    congrArg (fun ζ : Fib (F := F) (fibreProd.base (quotMk P J) (quotMk P J)) x =>
      F.map (diffMap P J) ζ.1) hc

section Chart

variable (hJ : J ^ 2 = ⊥) (c : EtaleChart F) {ρ₀ : c.C ⟶ (quot P J).obj}
  (h : c.α.app (quot P J) ρ₀ = x)
include hJ c h

/-- Over a chart point, gluing two lifts of `x` to a section over `P ×_{P ⧸ J} P` is bijective. -/
private lemma bijective_fibreProdFibMap :
    Function.Bijective
      (fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x) :=
  c.bijective_fibreProdFibMap_of_isChartPoint (isSqZeroExt_quotMk P J hJ).surjective
    (isSqZeroExt_quotMk P J hJ).surjective (isSqZeroExt_quotMk P J hJ).sq_eq_bot
    (isSqZeroExt_quotMk P J hJ).sq_eq_bot ⟨ρ₀, h⟩

/-- Over a chart point, a section over `P ×_{P ⧸ J} P` lying over `x` is determined by its two
projections. -/
lemma injective_fibreProdFibMap :
    Function.Injective
      (fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x) :=
  (bijective_fibreProdFibMap hJ c h).1

/-- Over a chart point, any two lifts of `x` glue to a section over `P ×_{P ⧸ J} P`. -/
lemma surjective_fibreProdFibMap :
    Function.Surjective
      (fibreProdFibMap F (π₁ := quotMk P J) (π₂ := quotMk P J) x) :=
  (bijective_fibreProdFibMap hJ c h).2

/-- The chart lift of a lift. -/
abbrev chartLift (z : Lifts F P J x) : c.C ⟶ P.obj :=
  c.chartLift (isSqZeroExt_quotMk P J hJ) h z

omit [Fact (ℵ₀ < κ)] in
/-- The chart lift of a lift reduces modulo `J` to the chart point `ρ₀`. -/
lemma chartLift_mk (z : Lifts F P J x) (y : c.C) :
    Ideal.Quotient.mk J ((chartLift hJ c h z).hom y) = ρ₀.hom y :=
  congrArg (fun g : c.C ⟶ (quot P J).obj => g.hom y)
    (c.chartLift_comp (isSqZeroExt_quotMk P J hJ) h z)

omit [Fact (ℵ₀ < κ)] in
/-- The chart lifts of two lifts agree modulo `J`. -/
lemma chartLift_sub_mem (z z' : Lifts F P J x) (y : c.C) :
    (chartLift hJ c h z').hom y - (chartLift hJ c h z).hom y ∈ J := by
  rw [← Ideal.Quotient.eq, chartLift_mk, chartLift_mk]

/-- **The chart description of the difference of two lifts**: the difference of their chart
lifts, read in `J/J²`. -/
lemma chartVec_diff (z z' : Lifts F P J x) (y : c.C) :
    Tan.chartVec c h (Lifts.diff z z') y =
      J.toCotangent ⟨(chartLift hJ c h z').hom y - (chartLift hJ c h z).hom y,
        chartLift_sub_mem hJ c h z z' y⟩ := by
  set σ₁ := chartLift hJ c h z
  set σ₂ := chartLift hJ c h z'
  have h₁₂ : σ₁ ≫ (quotMk P J).hom = σ₂ ≫ (quotMk P J).hom :=
    (c.chartLift_comp _ h z).trans (c.chartLift_comp _ h z').symm
  set σ := fibreProd.lift (quotMk P J) (quotMk P J) σ₁ σ₂ h₁₂
  have hσb : σ ≫ (fibreProd.base (quotMk P J) (quotMk P J)).hom = ρ₀ :=
    CommAlgCat.hom_ext <| AlgHom.ext fun y => chartLift_mk hJ c h z y
  let ζ : Fib (F := F) (fibreProd.base (quotMk P J) (quotMk P J)) x :=
    ⟨c.α.app (fibreProd (quotMk P J) (quotMk P J)) σ, by rw [c.map_α, hσb, h]⟩
  have hζ : fibreProdFibMap F x ζ = (z, z') := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change F.map _ (c.α.app (fibreProd (quotMk P J) (quotMk P J)) σ) = z.1
      rw [c.map_α, fibreProd.lift_fst, c.α_chartLift]
    · change F.map _ (c.α.app (fibreProd (quotMk P J) (quotMk P J)) σ) = z'.1
      rw [c.map_α, fibreProd.lift_snd, c.α_chartLift]
  have e : c.chartLift (isSqZeroExt_sqZeroFst P J) h (Lifts.diff z z') =
      σ ≫ (diffMap P J).hom := by
    refine c.chartLift_eq _ h _ _ ?_ ?_
    · rwa [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, diffMap_fst]
    · rw [diff_eq z z' ζ hζ (injective_fibreProdFibMap hJ c h), ← c.map_α]
  simp only [Tan.chartVec, e]
  rfl

/-- **A lift does not differ from itself, and the differences along three lifts add up.** -/
lemma diff_add_diff (z₁ z₂ z₃ : Lifts F P J x) :
    Lifts.diff z₁ z₂ + Lifts.diff z₂ z₃ = Lifts.diff z₁ z₃ := by
  apply Tan.chartVec_injective c h
  funext y
  rw [Tan.chartVec_add, Pi.add_apply, chartVec_diff hJ c h, chartVec_diff hJ c h,
    chartVec_diff hJ c h, ← map_add]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_add]
  ring

/-- The difference of a lift with itself is zero. -/
lemma diff_self (z : Lifts F P J x) : Lifts.diff z z = 0 := by
  apply Tan.chartVec_injective c h
  funext y
  rw [chartVec_diff hJ c h, Tan.chartVec_zero, Pi.zero_apply, J.toCotangent_eq_zero]
  simp

/-- **Lifts with zero difference are equal.** -/
lemma eq_of_diff_eq_zero (z z' : Lifts F P J x) (h0 : Lifts.diff z z' = 0) : z = z' := by
  refine c.eq_of_chartLift_eq (isSqZeroExt_quotMk P J hJ) h z z'
    (CommAlgCat.hom_ext <| AlgHom.ext fun y => ?_)
  have h1 := congrFun (congrArg (Tan.chartVec c h) h0) y
  rw [chartVec_diff hJ c h, Tan.chartVec_zero, Pi.zero_apply, J.toCotangent_eq_zero, hJ] at h1
  exact (sub_eq_zero.1 (Ideal.mem_bot.1 h1)).symm

/-- **Every tangent vector is the difference of a given lift and another one.** -/
lemma exists_diff_eq (z : Lifts F P J x) (w : Tan F P J x) :
    ∃ z' : Lifts F P J x, Lifts.diff z z' = w := by
  have hinj : Function.Injective J.toCotangent := fun a b hab => by
    rw [J.toCotangent_eq, hJ] at hab
    exact Subtype.ext (sub_eq_zero.1 (Ideal.mem_bot.1 hab))
  let e := LinearEquiv.ofBijective (J.toCotangent.restrictScalars R)
    ⟨hinj, J.toCotangent_surjective⟩
  set σ₁ := chartLift hJ c h z
  let δ : c.C →ₗ[R] P.obj :=
    { toFun := fun y => (e.symm (Tan.chartVec c h w y) : P.obj)
      map_add' := fun y y' => by
        rw [Tan.chartVec_add_apply, map_add, Submodule.coe_add]
      map_smul' := fun r y => by
        rw [Tan.chartVec_smul_apply, map_smul]
        rfl }
  have hδJ : ∀ y, δ y ∈ J := fun y => (e.symm (Tan.chartVec c h w y)).2
  have hcot : ∀ y, J.toCotangent ⟨δ y, hδJ y⟩ = Tan.chartVec c h w y := fun y =>
    e.apply_symm_apply (Tan.chartVec c h w y)
  have hδ : δ ∈ LiftDer (quotMk P J) σ₁ := by
    refine ⟨fun y => Ideal.Quotient.eq_zero_iff_mem.2 (hδJ y), fun y y' => ?_⟩
    have hmem : σ₁.hom y * δ y' + σ₁.hom y' * δ y ∈ J :=
      J.add_mem (J.mul_mem_left _ (hδJ y')) (J.mul_mem_left _ (hδJ y))
    have key : (⟨δ (y * y'), hδJ _⟩ : J) = ⟨σ₁.hom y * δ y' + σ₁.hom y' * δ y, hmem⟩ := by
      apply hinj
      have e₁ : (⟨σ₁.hom y * δ y' + σ₁.hom y' * δ y, hmem⟩ : J) =
          σ₁.hom y • (⟨δ y', hδJ y'⟩ : J) + σ₁.hom y' • (⟨δ y, hδJ y⟩ : J) := rfl
      rw [e₁, map_add, map_smul, map_smul, hcot, hcot, hcot, Tan.chartVec_mul_apply,
        ← chartLift_mk hJ c h z y, ← chartLift_mk hJ c h z y']
      rfl
    exact congrArg Subtype.val key
  let σ₂ := addLift (isSqZeroExt_quotMk P J hJ) σ₁ ⟨δ, hδ⟩
  have hσ₂ : σ₂ ≫ (quotMk P J).hom = ρ₀ :=
    (addLift_comp (isSqZeroExt_quotMk P J hJ) σ₁ ⟨δ, hδ⟩).trans (c.chartLift_comp _ h z)
  let z' : Lifts F P J x := ⟨c.α.app P σ₂, by rw [c.map_α, hσ₂, h]⟩
  refine ⟨z', ?_⟩
  have e₂ : chartLift hJ c h z' = σ₂ := c.chartLift_eq _ h z' σ₂ hσ₂ rfl
  apply Tan.chartVec_injective c h
  funext y
  rw [chartVec_diff hJ c h, ← hcot]
  congr 1
  apply Subtype.ext
  change (chartLift hJ c h z').hom y - σ₁.hom y = δ y
  rw [e₂, addLift_apply]
  ring

end Chart

end Lifts

/-! ### Functoriality -/

section Functoriality

variable {F} {P P' : BoundedAlg R κ} {J : Ideal P.obj} {J' : Ideal P'.obj} (f : P ⟶ P')
  (hJf : J ≤ J'.comap (BoundedAlg.toAlgHom f))

/-- The map of fibre products `P ×_{P ⧸ J} P ⟶ P' ×_{P' ⧸ J'} P'` induced by `f`. -/
def liftPairMap :
    fibreProd (quotMk P J) (quotMk P J) ⟶ fibreProd (quotMk P' J') (quotMk P' J') :=
  BoundedAlg.ofHom
    (AlgHom.codRestrict
      (((BoundedAlg.toAlgHom f).comp ((AlgHom.fst R _ _).comp (Subalgebra.val _))).prod
        ((BoundedAlg.toAlgHom f).comp ((AlgHom.snd R _ _).comp (Subalgebra.val _)))) _
      fun z => by
        change Ideal.Quotient.mk J' (BoundedAlg.toAlgHom f z.1.1) =
          Ideal.Quotient.mk J' (BoundedAlg.toAlgHom f z.1.2)
        rw [Ideal.Quotient.eq, ← map_sub]
        exact hJf (Ideal.Quotient.eq.1 z.2))

/-- The first projection commutes with `liftPairMap f hJf` and `f`. -/
lemma liftPairMap_fst :
    liftPairMap f hJf ≫ fibreProd.fst (quotMk P' J') (quotMk P' J') =
      fibreProd.fst (quotMk P J) (quotMk P J) ≫ f :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The second projection commutes with `liftPairMap f hJf` and `f`. -/
lemma liftPairMap_snd :
    liftPairMap f hJf ≫ fibreProd.snd (quotMk P' J') (quotMk P' J') =
      fibreProd.snd (quotMk P J) (quotMk P J) ≫ f :=
  BoundedAlg.hom_ext <| AlgHom.ext fun _ => rfl

/-- The map `diffMap` commutes with the maps induced by `f` on fibre products and on
`P̄ ⊕ J/J²`. -/
lemma diffMap_sqZeroMap :
    diffMap P J ≫ sqZeroMap f hJf = liftPairMap f hJf ≫ diffMap P' J' := by
  refine BoundedAlg.hom_ext (AlgHom.ext fun z => ?_)
  ext
  · rfl
  · change J.mapCotangent J' (BoundedAlg.toAlgHom f) hJf (J.toCotangent _) = J'.toCotangent _
    rw [Ideal.mapCotangent_toCotangent]
    congr 1
    exact Subtype.ext (map_sub _ _ _)

variable {x : F.obj (quot P J)} {x' : F.obj (quot P' J')} (hx : F.map (quotMap f hJf) x = x')

/-- **The image of a lift** under a map of algebras carrying `J` into `J'`. -/
def Lifts.map (z : Lifts F P J x) : Lifts F P' J' x' :=
  ⟨F.map f z.1, by
    rw [← Functor.map_comp_apply, ← quotMk_quotMap f hJf, Functor.map_comp_apply,
      z.2, hx]⟩

omit [Fact (ℵ₀ < κ)] in
/-- The underlying section of the image of a lift `z` under `f` is `F.map f z`. -/
lemma Lifts.map_val (z : Lifts F P J x) : (Lifts.map f hJf hx z).1 = F.map f z.1 := rfl

/-- **The difference of lifts commutes with maps of algebras**, between chart points. -/
lemma Lifts.map_diff (hJ : J ^ 2 = ⊥) (hJ' : J' ^ 2 = ⊥) (c : EtaleChart F)
    {ρ₀ : c.C ⟶ (quot P J).obj} (h : c.α.app (quot P J) ρ₀ = x) (z z' : Lifts F P J x) :
    Tan.map f hJf hx (Lifts.diff z z') =
      Lifts.diff (Lifts.map f hJf hx z) (Lifts.map f hJf hx z') := by
  obtain ⟨ζ, hζ⟩ := surjective_fibreProdFibMap hJ c h (z, z')
  have hx' : c.α.app (quot P' J') (ρ₀ ≫ (quotMap f hJf).hom) = x' := by rw [← c.map_α, h, hx]
  let ζ' : Fib (F := F) (fibreProd.base (quotMk P' J') (quotMk P' J')) x' :=
    ⟨F.map (liftPairMap f hJf) ζ.1, by
      rw [← Functor.map_comp_apply]
      change F.map (liftPairMap f hJf ≫ fibreProd.fst _ _ ≫ quotMk P' J') ζ.1 = x'
      rw [← Category.assoc, liftPairMap_fst, Category.assoc, ← quotMk_quotMap f hJf,
        ← Category.assoc, Functor.map_comp_apply, ζ.2, hx]⟩
  have hζ' : fibreProdFibMap F x' ζ' = (Lifts.map f hJf hx z, Lifts.map f hJf hx z') := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change F.map (fibreProd.fst _ _) (F.map (liftPairMap f hJf) ζ.1) = F.map f z.1
      rw [← Functor.map_comp_apply, liftPairMap_fst, Functor.map_comp_apply]
      exact congrArg (fun p => F.map f p.1.1) hζ
    · change F.map (fibreProd.snd _ _) (F.map (liftPairMap f hJf) ζ.1) = F.map f z'.1
      rw [← Functor.map_comp_apply, liftPairMap_snd, Functor.map_comp_apply]
      exact congrArg (fun p => F.map f p.2.1) hζ
  rw [Lifts.diff_eq z z' ζ hζ (injective_fibreProdFibMap hJ c h),
    Lifts.diff_eq _ _ ζ' hζ' (injective_fibreProdFibMap hJ' c hx')]
  apply Subtype.ext
  change F.map (sqZeroMap f hJf) (F.map (diffMap P J) ζ.1) =
    F.map (diffMap P' J') (F.map (liftPairMap f hJf) ζ.1)
  rw [← Functor.map_comp_apply, diffMap_sqZeroMap, Functor.map_comp_apply]

omit [Fact (ℵ₀ < κ)] in
/-- The image of a lift under `f` and then `f'` is its image under `f ≫ f'`. -/
lemma Lifts.map_map {P'' : BoundedAlg R κ} {J'' : Ideal P''.obj} (f' : P' ⟶ P'')
    (hJf' : J' ≤ J''.comap (BoundedAlg.toAlgHom f')) {x'' : F.obj (quot P'' J'')}
    (hx' : F.map (quotMap f' hJf') x' = x'') (z : Lifts F P J x) :
    Lifts.map f' hJf' hx' (Lifts.map f hJf hx z) =
      Lifts.map (f ≫ f') (fun j hj => hJf' (hJf hj))
        (by rw [← hx', ← hx, ← Functor.map_comp_apply, quotMap_comp]) z :=
  Subtype.ext <| show F.map f' (F.map f z.1) = F.map (f ≫ f') z.1 by
    rw [Functor.map_comp_apply]

end Functoriality

end Stacks.ChartedFunctor

end
