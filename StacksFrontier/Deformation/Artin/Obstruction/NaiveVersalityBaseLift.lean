module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityObstructionVanishing
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityThickeningLift

/-!
# Lifting the base along a small extension

This is the geometric endgame of the base-lifting condition in the direction `(2) ⇒ (1)` of
[Stacks, Tag 07YM]. Let `x` be a family over `Spec A` whose deformation theory is controlled by
`ξ : E ⟶ NL_{A/Λ}` as in hypothesis (i) of the tag, and suppose condition (2) holds in degree
`-1`. Let `fC : C' → C` be a square-zero surjection of `Λ`-algebras whose kernel is a
one-dimensional vector space over a field `k` with `A ⟶ k` factoring through `C`, let
`φ : A → C` be the `Λ`-algebra map a point of `Spec A` with values in `C` names, and suppose the
restriction of `x` to `Spec C` lifts to `Spec C'`. Then `φ` lifts along `fC`.

The three steps are the three chapters of the argument:

* the fibre product `A ×_C C'` is a square-zero thickening of `A` with kernel `k`
  (`StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFibreProduct`);
* axiom (RS\*) lifts `x` across it, because the restriction of `x` to `Spec C` is identified
  with the restriction of the given lift
  (`Deformation.Artin.exists_squareZeroThickening_underFiber_of_satisfiesRSStar`);
* hypothesis (i) then kills `ξ ≫ NL_{A/Λ} ⟶ NL_{A/(A ×_C C')}`, so condition (2) in degree `-1`
  splits the thickening
  (`Deformation.Artin.exists_algHom_section_of_surjective_derivedTensorFibre_neg_one`), and a
  section of `A ×_C C' → A` is a lift of `φ`
  (`Deformation.Artin.exists_algHom_lift_of_algHom_section`).

## Main results

* `Deformation.Artin.exists_algHom_lift_of_surjective_derivedTensorFibre_neg_one` — **the
  step**: `∃ ψ : A →ₐ[Λ] C'` with `fC ∘ ψ = φ`.

## Implementation notes

Hypothesis (i) of the tag is taken in exactly the form
`Deformation.Artin.surjective_derivedTensorFibre_neg_one_of_isVersalAt` takes it for the
opposite direction, except that the implication runs the other way: there a vanishing
`ξ ≫ NL_{A/Λ} ⟶ NL_{A/A'}` produces a lift, here a lift produces the vanishing. The
quantification over the deformation situation is unchanged, so a consumer holding the tag's
hypothesis (i) as an iff has both halves available.

The kernel data is given by plain ring maps `rC : C → k`, `rC' : C' → k` to the field and an
additive isomorphism `Ker fC ≃+ k` with its scalar rule, rather than by the residue structure of
`Deformation.ArtinianLocalAlgCat`: the identification [Stacks, Tag 06H0] provides is linear for
the action of `C'` on the ideal `Ker fC`, and the `A`-action it is compared with factors through
`rC ∘ φ`. Nothing here is Artinian, local or Noetherian.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YI](https://stacks.math.columbia.edu/tag/07YI)
* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

universe u v w

section BaseLift

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  {Λ A C C' k : Type u} [CommRing Λ] [CommRing A] [CommRing C] [CommRing C'] [Field k]
  [Algebra Λ A] [Algebra Λ C] [Algebra Λ C'] [Algebra A k]
  (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
  (hA : B.Contains (Spec (CommRingCat.of A)))
  (φ : A →ₐ[Λ] C) (fC : C' →ₐ[Λ] C)

include hp hRS in
/-- **Stacks 07YM, the base-lifting step of `(2) ⇒ (1)`.** Let `x` be a family over `Spec A`
whose deformation theory is controlled by `ξ : E ⟶ NL_{A/Λ}` in the sense of hypothesis (i) of
the tag, and assume `H^{-1}(ξ ⊗ᴸ_A k)` is surjective. Let `fC : C' → C` be a square-zero
surjection of `Λ`-algebras whose kernel is identified with `k`, and let `φ : A → C` be a
`Λ`-algebra map compatible with the maps to `k`. If the restriction of `x` along `φ` admits a
lift along `fC` inside the fibred category, then `φ` itself lifts along `fC`.

The fibre product `A ×_C C'` is a square-zero thickening of `A` with kernel `k`; axiom (RS\*)
glues the lift and `x` into a family over `Spec (A ×_C C')`; hypothesis (i) therefore kills
`ξ ≫ NL_{A/Λ} ⟶ NL_{A/(A ×_C C')}`, so the obstruction step splits the thickening, and a
`Λ`-algebra section of `A ×_C C' → A` is exactly a `Λ`-algebra map `A → C'` over `φ`. -/
public theorem exists_algHom_lift_of_surjective_derivedTensorFibre_neg_one
    (hC : B.Contains (Spec (CommRingCat.of C)))
    (hC' : B.Contains (Spec (CommRingCat.of C')))
    (hA' : B.Contains (Spec (CommRingCat.of (AlgHom.pullback φ fC))))
    (hfC : Function.Surjective fC)
    (hsqC : RingHom.ker (fC : C' →+* C) ^ 2 = ⊥)
    (rC : C →+* k) (rC' : C' →+* k)
    (hrC' : ∀ c : C', rC (fC c) = rC' c)
    (hrφ : ∀ a : A, rC (φ a) = algebraMap A k a)
    (eker : RingHom.ker (fC : C' →+* C) ≃+ k)
    (heker : ∀ (c : C') (i : RingHom.ker (fC : C' →+* C)), eker (c • i) = rC' c * eker i)
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
    (hsurj : Function.Surjective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
        ((T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A k))).map ξ)))
    {Xf Zf Yf : F}
    (hXf : p.obj Xf = algebraOver A B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA)
    (hKill : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
      [IsScalarTower Λ A' A]
      (D : SquareZeroThickening A B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) hA A'),
      D.q = algebraMap A' A →
      Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ = B.inclusion.map D.toS' →
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hXf ≫ D.arrow))) →
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0)
    (hZf : p.obj Zf = algebraOver C B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ C)) ≫ iΛ) hC)
    (hYf : p.obj Yf = algebraOver C' B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ C')) ≫ iΛ) hC')
    (α : Zf ⟶ Xf) (β : Zf ⟶ Yf)
    (hα : schemeMap (p ⋙ Over.post B.inclusion)
        (algebraOver_post B S hS p _ hC hZf) (algebraOver_post B S hS p _ hA hXf) α =
      Spec.map (CommRingCat.ofHom (φ : A →+* C)))
    (hβ : schemeMap (p ⋙ Over.post B.inclusion)
        (algebraOver_post B S hS p _ hC hZf) (algebraOver_post B S hS p _ hC' hYf) β =
      Spec.map (CommRingCat.ofHom (fC : C' →+* C))) :
    ∃ ψ : A →ₐ[Λ] C', fC.comp ψ = φ := by
  obtain ⟨D, hDq, hDlift, hDchart⟩ := exists_squareZeroThickening_underFiber_of_satisfiesRSStar
    B S hS p hp hRS iΛ φ fC hfC hsqC hA hC hC' hA' hXf hZf hYf α β hα hβ
  have hkill := hKill (AlgHom.pullback φ fC) D hDq hDchart hDlift
  obtain ⟨σ, hσ⟩ := exists_algHom_section_of_surjective_derivedTensorFibre_neg_one
    Λ A (AlgHom.pullback φ fC) k (surjective_fibreProduct_algebraMap φ fC hfC)
    (ker_fibreProduct_sq_eq_bot φ fC hsqC)
    (fibreProductKerEquiv hfC hsqC rC rC' hrC' hrφ eker heker)
    T E hE ξ hsurj hkill
  exact exists_algHom_lift_of_algHom_section φ fC σ hσ

end BaseLift

end Deformation.Artin

end
