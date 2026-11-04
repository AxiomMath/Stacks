module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpecOfGlobalFunctions

/-!
# The polynomial-coordinate square of an étale chart over the spectrum of global functions

Let `X` be an algebraic space over `S`, let `A` be a `u`-model of its ring of global functions,
let `V` be an étale scheme chart of `X`, and let

`C = A[x₁, …, xₙ]/(g₁, …, gₙ)`

be a presentation over `A`, together with global functions `h₁, …, hₙ` on `V` satisfying
`g_λ(h₁, …, hₙ) = 0`. Then the square

```
  X   ⟵ V
  ↓      ↓
Spec A ⟵ Spec C
```

commutes: the left vertical is the canonical morphism of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom`, the right vertical is the morphism of
schemes sending the coordinates `x_ν` to the `h_ν`, the top is the chart, and the bottom is the
spectrum of `A → C`.

## Main definitions

* `AlgebraicGeometry.Space.globalFunctionsModel` and
  `AlgebraicGeometry.Space.globalFunctionsModelEquiv`: the canonical `u`-model of the ring of
  global functions of an algebraic space, and its identification with that ring.
* `AlgebraicGeometry.Space.presentationAlgebra` and
  `AlgebraicGeometry.Space.presentationStructureHom`: the algebra `A[x]/(g)` of a family of
  polynomials and the structure homomorphism of `A` into it.
* `AlgebraicGeometry.Space.coordinateHom`: the homomorphism `A[x]/(g) →+* Γ(V, ⊤)` determined by
  a family of global functions on `V` killing the `g`.
* `AlgebraicGeometry.Space.schemePointsMap`: a morphism of schemes, read on functors of points
  over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.finitePresentation_presentationStructureHom`: a presentation by
  finitely many polynomials in finitely many variables is of finite presentation.
* `AlgebraicGeometry.Space.coordinateHom_mk_X` and
  `AlgebraicGeometry.Space.coordinateHom_comp_presentationStructureHom`: the two properties that
  determine the right-hand vertical morphism.
* `AlgebraicGeometry.Space.isPushout_presentationAlgebra_baseChange`: a presentation and its base
  change along a homomorphism of the coefficients form a pushout of commutative rings.
* `AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions`: commutativity of the square.

## References

* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### A presentation over a ring -/

section Presentation

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The algebra `A[x₁, …, xₙ]/(g₁, …, gₙ)` of a family of polynomials. -/
abbrev presentationAlgebra (g : Fin n → MvPolynomial (Fin n) A) : Type u :=
  MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range g)

/-- The structure homomorphism of `A` into a presentation over it. -/
def presentationStructureHom (g : Fin n → MvPolynomial (Fin n) A) :
    A →+* presentationAlgebra g :=
  (Ideal.Quotient.mk (Ideal.span (Set.range g))).comp MvPolynomial.C

/-- The ideal cut out by a finite family of polynomials is finitely generated. -/
theorem fg_span_range (g : Fin n → MvPolynomial (Fin n) A) :
    (Ideal.span (Set.range g)).FG :=
  ⟨(Set.finite_range g).toFinset, by simp⟩

/-- **A presentation by finitely many polynomials in finitely many variables is of finite
presentation.** -/
theorem finitePresentation_presentationStructureHom (g : Fin n → MvPolynomial (Fin n) A) :
    RingHom.FinitePresentation (presentationStructureHom g) :=
  RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.quotient (fg_span_range g))

variable {R : Type u} [CommRing R] (g : Fin n → MvPolynomial (Fin n) A) (ψ : A →+* R)
  (h : Fin n → R) (hrel : ∀ l, MvPolynomial.eval₂ ψ h (g l) = 0)

include hrel

/-- The homomorphism out of a presentation determined by a family of elements killing the
relations. -/
def coordinateHom : presentationAlgebra g →+* R :=
  Ideal.Quotient.lift (Ideal.span (Set.range g)) (MvPolynomial.eval₂Hom ψ h) (by
    have hle : Ideal.span (Set.range g) ≤ RingHom.ker (MvPolynomial.eval₂Hom ψ h) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨l, rfl⟩
      exact RingHom.mem_ker.mpr (hrel l)
    exact fun a ha => RingHom.mem_ker.1 (hle ha))

/-- The homomorphism out of a presentation carries the class of the variable `x_k` to the
prescribed element `h k`. -/
theorem coordinateHom_mk_X (k : Fin n) :
    coordinateHom g ψ h hrel (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k))
      = h k := by
  show MvPolynomial.eval₂Hom ψ h (MvPolynomial.X k) = h k
  simp

/-- The homomorphism out of a presentation restricts along the structure homomorphism to the
given homomorphism. -/
theorem coordinateHom_comp_presentationStructureHom :
    (coordinateHom g ψ h hrel).comp (presentationStructureHom g) = ψ := by
  ext a
  show MvPolynomial.eval₂Hom ψ h (MvPolynomial.C a) = ψ a
  simp

end Presentation

/-! ### The presentation square and its base change -/

section PresentationPushout

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) {m : ℕ}
  (g : Fin m → MvPolynomial (Fin m) R)

/-- **A polynomial presentation and its base change form a pushout of commutative rings.** Let
`φ : R →+* A` be a ring homomorphism and let `g₁, …, g_m` be polynomials in `m` variables over
`R`. Pushing the relations forward along `φ` gives a presentation over `A`, and the square

```
R                  ⟶ R[x₁, …, x_m]/(g)
↓                           ↓
A                  ⟶ A[x₁, …, x_m]/(φ(g))
```

whose right vertical is `Ideal.quotientMap` of `MvPolynomial.map φ`, is a pushout: a
homomorphism out of `A[x]/(φ(g))` is a homomorphism out of `A` together with one out of
`R[x]/(g)` restricting to it over `R`. -/
theorem isPushout_presentationAlgebra_baseChange
    (hbc : Ideal.span (Set.range g) ≤
      Ideal.comap (MvPolynomial.map φ)
        (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k)))) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (presentationStructureHom g))
      (CommRingCat.ofHom (presentationStructureHom fun k => MvPolynomial.map φ (g k)))
      (CommRingCat.ofHom (Ideal.quotientMap
        (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k)))
        (MvPolynomial.map φ) hbc)) := by
  have hbcmk : ∀ p : MvPolynomial (Fin m) R,
      Ideal.quotientMap (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k)))
          (MvPolynomial.map φ) hbc (Ideal.Quotient.mk (Ideal.span (Set.range g)) p)
        = Ideal.Quotient.mk (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k)))
            (MvPolynomial.map φ p) := fun _ => Ideal.quotientMap_mk
  have hsqr : (presentationStructureHom fun k => MvPolynomial.map φ (g k)).comp φ
      = (Ideal.quotientMap (Ideal.span (Set.range fun k => MvPolynomial.map φ (g k)))
          (MvPolynomial.map φ) hbc).comp (presentationStructureHom g) := by
    refine RingHom.ext fun a => ?_
    show Ideal.Quotient.mk _ (MvPolynomial.C (φ a))
      = Ideal.quotientMap _ (MvPolynomial.map φ) hbc (Ideal.Quotient.mk _ (MvPolynomial.C a))
    rw [hbcmk, MvPolynomial.map_C]
  have hC : ∀ s : PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (presentationStructureHom g)), ∀ a : R,
      s.inl.hom (φ a)
        = s.inr.hom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.C a)) := by
    intro s a
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom s.condition) a
  have hrel : ∀ s : PushoutCocone (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (presentationStructureHom g)), ∀ l,
      MvPolynomial.eval₂ s.inl.hom
        (fun k => s.inr.hom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k)))
        (MvPolynomial.map φ (g l)) = 0 := by
    intro s l
    have hcomp : (MvPolynomial.eval₂Hom s.inl.hom
          (fun k => s.inr.hom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k)))
            : MvPolynomial (Fin m) A →+* s.pt).comp (MvPolynomial.map φ)
        = s.inr.hom.comp (Ideal.Quotient.mk (Ideal.span (Set.range g))) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
      · show MvPolynomial.eval₂ s.inl.hom _ (MvPolynomial.map φ (MvPolynomial.C a)) = _
        rw [MvPolynomial.map_C, MvPolynomial.eval₂_C]
        exact hC s a
      · show MvPolynomial.eval₂ s.inl.hom _ (MvPolynomial.map φ (MvPolynomial.X k)) = _
        rw [MvPolynomial.map_X, MvPolynomial.eval₂_X]
        rfl
    refine (RingHom.congr_fun hcomp (g l)).trans ?_
    show s.inr.hom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (g l)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self (f := g) l)), map_zero]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (CommRingCat.hom_ext hsqr)
    (fun s => CommRingCat.ofHom (coordinateHom (fun k => MvPolynomial.map φ (g k)) s.inl.hom
      (fun k => s.inr.hom (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k)))
      (hrel s)))
    (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
  · exact CommRingCat.hom_ext (coordinateHom_comp_presentationStructureHom
      (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s))
  · refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext
      (MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)))
    · show coordinateHom (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s)
        (Ideal.quotientMap _ (MvPolynomial.map φ) hbc
          (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.C a))) = _
      rw [hbcmk, MvPolynomial.map_C]
      refine (RingHom.congr_fun (coordinateHom_comp_presentationStructureHom
        (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s)) (φ a)).trans ?_
      exact hC s a
    · show coordinateHom (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s)
        (Ideal.quotientMap _ (MvPolynomial.map φ) hbc
          (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k))) = _
      rw [hbcmk, MvPolynomial.map_X]
      exact coordinateHom_mk_X (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s) k
  · refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext
      (MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)))
    · refine (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hm1) a).trans ?_
      exact (RingHom.congr_fun (coordinateHom_comp_presentationStructureHom
        (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s)) a).symm
    · have h2 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hm2)
        (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X k))
      change m.hom (Ideal.quotientMap _ (MvPolynomial.map φ) hbc _) = _ at h2
      rw [hbcmk, MvPolynomial.map_X] at h2
      refine h2.trans ?_
      exact (coordinateHom_mk_X (fun k => MvPolynomial.map φ (g k)) s.inl.hom _ (hrel s) k).symm

end PresentationPushout

/-! ### A `u`-model of the ring of global functions -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A `u`-model of the ring of global functions of an algebraic space over `S`: the `Shrink` of
that `u`-small ring. -/
def globalFunctionsModel (X : AlgebraicSpaces B S hS) : Type u :=
  Shrink.{u} (globalFunctions B S hS X.1)

/-- The commutative ring structure on the `u`-model of the ring of global functions. -/
noncomputable instance (X : AlgebraicSpaces B S hS) :
    CommRing (globalFunctionsModel B S hS X) :=
  inferInstanceAs (CommRing (Shrink.{u} (globalFunctions B S hS X.1)))

/-- The identification of the `u`-model with the ring of global functions. -/
def globalFunctionsModelEquiv (X : AlgebraicSpaces B S hS) :
    globalFunctionsModel B S hS X ≃+* globalFunctions B S hS X.1 :=
  Shrink.ringEquiv _

/-! ### Functors of points of a morphism of schemes -/

/-- A morphism of schemes, read on the functors of points over the big fppf site of `S`. -/
abbrev schemePointsMap {T T' : Scheme.{u}} (f : T ⟶ T') :
    schemePoints B S hS T ⟶ schemePoints B S hS T' :=
  Functor.whiskerLeft (BigFppfOver.toScheme B S hS).op (yoneda.map f)

/-- A scheme-valued point of the functor of points, pushed along a morphism of schemes, is the
composite of the point with that morphism. -/
theorem yonedaEquiv_comp_schemePointsMap {U : BigFppfOver B S hS} {T T' : Scheme.{u}}
    (x : yoneda.obj U ⟶ schemePoints B S hS T) (f : T ⟶ T') :
    yonedaEquiv (x ≫ schemePointsMap B S hS f) = yonedaEquiv x ≫ f := by
  rw [yonedaEquiv_comp]
  rfl

/-! ### The chart square over the spectrum of global functions -/

/-- Let `A` be a `u`-model of the ring of global functions of an algebraic space `X` over `S`,
let `V` be an étale scheme chart of `X`, let `g₁, …, gₙ` be polynomials in `n` variables over `A`
and let `h₁, …, hₙ` be global functions on `V` with `g_λ(h) = 0`. Write
`C = A[x₁, …, xₙ]/(g₁, …, gₙ)`. Then the square whose top is the chart, whose left vertical is a
canonical morphism `p : X ⟶ Spec A`, whose right vertical is the morphism `V ⟶ Spec C` attached
to `AlgebraicGeometry.Space.coordinateHom` and whose bottom is the spectrum of `A → C` commutes.

The hypothesis `hp` is the chart formula of `AlgebraicGeometry.Space.exists_specMap_of_globalHom`,
which determines `p`. -/
@[stacks 084U]
theorem commSq_chart_specOfGlobalFunctions (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) (A : Type u) [CommRing A]
    (e : A ≃+* globalFunctions B S hS X.1) {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)
    (h : Fin n → Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (hrel : ∀ l, MvPolynomial.eval₂
      ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom) h (g l) = 0)
    (p : X.1 ⟶ schemePoints B S hS (Spec (CommRingCat.of A)))
    (hp : yonedaEquiv (V.1.hom ≫ p) =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom)) :
    V.1.hom ≫ p =
      yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra g)
          (coordinateHom g ((globalFunctionsChartRestriction B S hS X V).comp e.toRingHom)
            h hrel)) ≫
        schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom g))) := by
  apply yonedaEquiv.injective
  rw [hp, yonedaEquiv_comp_schemePointsMap, Equiv.apply_symm_apply, specMapOfGlobalHom,
    specMapOfGlobalHom, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    coordinateHom_comp_presentationStructureHom g _ h hrel]

end AlgebraicGeometry.Space

end
