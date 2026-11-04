module

public import StacksFrontier.CategoryTheory.Sites.Point.FiniteGerms
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic

/-!
# A fibre of a presheaf of rings which is locally étale is ind-étale

Let `Φ` be a point of a site, let `P` be a presheaf of commutative rings and let `(X₀, x₀)` be a
neighbourhood of `Φ`.  Suppose that every neighbourhood of `Φ` lying over `(X₀, x₀)` is refined
by one over which the restriction map from `P(X₀)` is étale.  Then the fibre `P_Φ` is a filtered
colimit of étale `P(X₀)`-algebras.

This is the abstract form of the statement that the stalk of the structure sheaf of an algebraic
space at a geometric point is ind-étale over the ring of functions of any affine étale chart
through the point (Stacks 04HX, 04KF).

## Main results

* `CategoryTheory.GrothendieckTopology.Point.ind_etale_presheafFiber`: the ind-étaleness above.

## Implementation notes

The proof is the factorization criterion of Lemma 07C3,
`CommRingCat.ind_under_iff_exists_factorization`: a map from a finitely presented algebra
`P(X₀)[x₁, …, xₙ]/(r₁, …, rₘ)` to the fibre sends the variables to germs over a common
neighbourhood, where the relations hold after a further restriction; refining once more to an
étale neighbourhood gives the factorization through an étale `P(X₀)`-algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ CommRingCat.{w})

/-- **The fibre of a locally étale presheaf of rings is ind-étale.** -/
theorem ind_etale_presheafFiber {X₀ : C} (x₀ : Φ.fiber.obj X₀)
    (hgood : ∀ (X : C) (k : X ⟶ X₀) (x : Φ.fiber.obj X), Φ.fiber.map k x = x₀ →
      ∃ (Y : C) (g : Y ⟶ X) (y : Φ.fiber.obj Y), Φ.fiber.map g y = x ∧
        (P.map (g ≫ k).op).hom.Etale) :
    letI := (Φ.toPresheafFiber X₀ x₀ P).hom.toAlgebra
    (CommAlgCat.etale.{w} (P.obj (op X₀))).ind.{w}
      (CommAlgCat.of (P.obj (op X₀)) ((Φ.presheafFiber (A := CommRingCat.{w})).obj P)) := by
  let := (Φ.toPresheafFiber X₀ x₀ P).hom.toAlgebra
  rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk]
  refine (CommRingCat.ind_under_iff_exists_factorization _
    fun B hB => (RingHom.Etale.iff_flat_and_formallyUnramified.mp hB).2.2).mpr ?_
  intro A hA f
  -- A presentation of `A` over `P(X₀)`.
  let := A.hom.hom.toAlgebra
  obtain ⟨n, π, hπ, ⟨S, hS⟩⟩ := (hA : Algebra.FinitePresentation _ _).out
  have hC : ∀ r, π (MvPolynomial.C r) = A.hom r := π.commutes
  -- The images of the variables are germs over a common neighbourhood over `(X₀, x₀)`.
  obtain ⟨X₁, g₁, x₁, hx₁, s, hs⟩ := Φ.exists_toPresheafFiber_eq_fin x₀ n
    (fun k => f.right (π (MvPolynomial.X k)))
  let σ₁ : MvPolynomial (Fin n) (P.obj (op X₀)) →+* P.obj (op X₁) :=
    MvPolynomial.eval₂Hom (P.map g₁.op).hom s
  have hσ₁ : ∀ p, Φ.toPresheafFiber X₁ x₁ P (σ₁ p) = f.right (π p) := by
    intro p
    have h : (Φ.toPresheafFiber X₁ x₁ P).hom.comp σ₁ = f.right.hom.comp π.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, σ₁, MvPolynomial.eval₂Hom_C]
        show Φ.toPresheafFiber X₁ x₁ P (P.map g₁.op r) = f.right (π (MvPolynomial.C r))
        rw [Point.toPresheafFiber_w_apply, hx₁, hC]
        exact (ConcreteCategory.congr_hom f.w r).symm
      · intro k
        show Φ.toPresheafFiber X₁ x₁ P (σ₁ (MvPolynomial.X k)) = _
        rw [MvPolynomial.eval₂Hom_X']
        exact hs k
    exact DFunLike.congr_fun h p
  -- The relations hold over a smaller neighbourhood.
  obtain ⟨X₂, g₂, x₂, hx₂, hrel⟩ := Φ.exists_map_eq_zero_fin x₁ S.card
    (fun k => σ₁ (S.equivFin.symm k).1) (fun k => by
      rw [hσ₁]
      show f.right (π _) = 0
      rw [show π _ = 0 from RingHom.mem_ker.mp (show _ ∈ RingHom.ker π.toRingHom from
        hS ▸ Ideal.subset_span (S.equivFin.symm k).2), map_zero])
  -- Refine to an étale neighbourhood.
  obtain ⟨X₃, g₃, x₃, hx₃, het⟩ := hgood X₂ (g₂ ≫ g₁) x₂ (by
    rw [FunctorToTypes.map_comp_apply, hx₂, hx₁])
  let σ₃ : MvPolynomial (Fin n) (P.obj (op X₀)) →+* P.obj (op X₃) :=
    (P.map g₃.op).hom.comp ((P.map g₂.op).hom.comp σ₁)
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker σ₃ := by
    rw [← hS, Ideal.span_le]
    intro r hr
    have h := hrel (S.equivFin ⟨r, hr⟩)
    rw [Equiv.symm_apply_apply] at h
    show P.map g₃.op (P.map g₂.op (σ₁ r)) = 0
    rw [h, map_zero]
  let ψ : A.right →+* P.obj (op X₃) := (π.toRingHom.liftOfSurjective hπ) ⟨σ₃, hker⟩
  have hψ : ∀ p, ψ (π p) = σ₃ p := fun p =>
    π.toRingHom.liftOfSurjective_comp_apply hπ ⟨σ₃, hker⟩ p
  let k₃ : X₃ ⟶ X₀ := g₃ ≫ g₂ ≫ g₁
  refine ⟨Under.mk (P.map k₃.op), Under.homMk (CommRingCat.ofHom ψ) ?_,
    Under.homMk (Φ.toPresheafFiber X₃ x₃ P) ?_, ?_, het⟩
  · refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show ψ (A.hom r) = P.map k₃.op r
    rw [← hC, hψ]
    simp only [σ₃, σ₁, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, k₃, op_comp,
      Functor.map_comp, CommRingCat.hom_comp]
  · show P.map k₃.op ≫ Φ.toPresheafFiber X₃ x₃ P = Φ.toPresheafFiber X₀ x₀ P
    rw [Point.toPresheafFiber_w]
    congr
    simp only [k₃, FunctorToTypes.map_comp_apply, hx₃, hx₂, hx₁]
  · refine Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    obtain ⟨p, rfl⟩ := hπ a
    show Φ.toPresheafFiber X₃ x₃ P (ψ (π p)) = f.right (π p)
    rw [hψ, ← hσ₁]
    show Φ.toPresheafFiber X₃ x₃ P (P.map g₃.op (P.map g₂.op (σ₁ p))) = _
    rw [Point.toPresheafFiber_w_apply, Point.toPresheafFiber_w_apply, hx₃, hx₂]

end CategoryTheory.GrothendieckTopology.Point

end
