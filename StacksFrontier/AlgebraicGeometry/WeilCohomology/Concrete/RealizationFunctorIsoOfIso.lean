module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMonoidal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Isomorphic Weil data have monoidally isomorphic realizations

Let `W`, `W'` be data (D0)–(D3) satisfying (A), (B) and (C), and let `e : W ≅ W'` be an
isomorphism of such data preserving the cycle class maps and the trace maps. This file shows that
the realizations `G, G'` of correspondences of degree zero of the proof of Stacks 0FHL
(`Stacks.WeilCohomology.WeilData.corrFunctor`) are isomorphic, by the isomorphisms
`H^n(X) ≅ H'^n(X)` of `e`, and that this isomorphism is monoidal for the Künneth tensorators and
the units `F ≅ H^*(Spec k)`: `e(pr₁^*a ∪ pr₂^*b) = pr₁^*e(a) ∪ pr₂^*e(b)` since `e` is
multiplicative and commutes with pullbacks, and `e(c · 1) = c · 1` since `e` is an `F`-algebra
map. This is the step "isomorphic data give isomorphic functors" of the proof of Stacks 0FHM.

## Main definitions

* `Stacks.WeilCohomology.WeilData.Iso.corrFunctorIso`: the isomorphism `G ≅ G'`.

## Main results

* `Stacks.WeilCohomology.WeilData.Iso.corrFunctorIso_isMonoidal`: it is monoidal.
* `Stacks.WeilCohomology.WeilData.IsIsomorphic.nonempty_corrFunctorIso`: isomorphic data have
  monoidally isomorphic realizations.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Stacks.Chow CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme GradedObject.Monoidal

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {W W' : WeilData k F}
  {hA : W.PoincareDuality} {hB : W.Kunneth} {hC : W.CycleClassAxiom hA.perfectPairing}
  {hA' : W'.PoincareDuality} {hB' : W'.Kunneth} {hC' : W'.CycleClassAxiom hA'.perfectPairing}

namespace Iso

variable (e : Iso W W') (hγ : e.PreservesCycleClass) (htr : e.PreservesTrace)

include hγ htr

/-- **Isomorphic data have isomorphic realizations**: the isomorphisms `H^n(X) ≅ H'^n(X)` of an
isomorphism `e : W ≅ W'` preserving cycle classes and traces form an isomorphism `G ≅ G'` of the
realizations of correspondences of degree zero. -/
def corrFunctorIso : corrFunctor hA hB hC ≅ corrFunctor hA' hB' hC' :=
  NatIso.ofComponents (fun X ↦ GradedObject.isoMk _ _ fun n ↦ (e.gradeEquiv X.as n).toModuleIso)
    fun {X Y} f ↦ by
      refine GradedObject.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦ ?_)
      exact (e.gradeEquiv_corrMap (hA := hA) (hB := hB) (hC := hC) (hA' := hA') (hB' := hB')
        (hC' := hC') hγ htr X.as Y.as 0 n
        (SmoothProjectiveCorr.toCorr X.as Y.as 0 (ChowMotiveCat.component 0 (DegreeZero.val f)))
        a)

/-- The component of `corrFunctorIso` at `X` in degree `n` sends `a` to `e.gradeEquiv X.as n a`. -/
@[simp]
theorem corrFunctorIso_hom_app_apply (X : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ)
    (a : (corrFunctor hA hB hC).obj X n) :
    (((e.corrFunctorIso (hA' := hA') (hB' := hB') (hC' := hC') hγ htr).hom.app X n).hom a) =
      e.gradeEquiv X.as n a :=
  rfl

/-- The inverse of `corrFunctorIso` at `X` in degree `n` sends `a` to
`(e.gradeEquiv X.as n).symm a`. -/
@[simp]
theorem corrFunctorIso_inv_app_apply (X : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ)
    (a : (corrFunctor hA' hB' hC').obj X n) :
    (((e.corrFunctorIso (hA := hA) (hB := hB) (hC := hC) hγ htr).inv.app X n).hom a) =
      (e.gradeEquiv X.as n).symm a :=
  rfl

end Iso

/-! ### Monoidality -/

section Monoidal

attribute [local instance] corrFunctorMonoidal

variable (hA hB hC) in
/-- The unit of the monoidal structure on `corrFunctor` is the isomorphism `F ≅ H^*(Spec k)`
of `corrFunctorεIso`. -/
theorem corrFunctor_ε :
    Functor.LaxMonoidal.ε (corrFunctor hA hB hC) = (corrFunctorεIso hA hB hC).hom :=
  rfl

variable (hA hB hC) in
/-- The tensorator of the monoidal structure on `corrFunctor` at `X, Y` is the Künneth
isomorphism `corrFunctorμIso`. -/
theorem corrFunctor_μ (X Y : DegreeZero ℚ (CorrespondenceCategory k)) :
    Functor.LaxMonoidal.μ (corrFunctor hA hB hC) X Y = (corrFunctorμIso hA hB hC X Y).hom :=
  rfl

namespace Iso

variable (e : Iso W W') (hγ : e.PreservesCycleClass) (htr : e.PreservesTrace)

/-- **The isomorphism `G ≅ G'` of isomorphic data is monoidal**: it respects the Künneth
tensorators, `e(pr₁^*a ∪ pr₂^*b) = pr₁^*e(a) ∪ pr₂^*e(b)`, and the units `F ≅ H^*(Spec k)`,
`e(c · 1) = c · 1`. -/
instance corrFunctorIso_isMonoidal :
    NatTrans.IsMonoidal (e.corrFunctorIso (hA := hA) (hB := hB) (hC := hC) (hA' := hA')
      (hB' := hB') (hC' := hC') hγ htr).hom where
  unit := by
    rw [corrFunctor_ε, corrFunctor_ε]
    refine GradedObject.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun u ↦ ?_)
    simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      corrFunctorIso_hom_app_apply]
    exact Subtype.ext ((e.equiv (point k)).commutes _)
  tensor X Y := by
    rw [corrFunctor_μ, corrFunctor_μ]
    refine GradedObject.hom_ext _ _ fun n ↦ tensorObj_hom_ext fun p q hpq a b ↦ ?_
    simp only [GradedObject.categoryOfGradedObjects_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tensorHom_apply_ιTensorObj, corrFunctorμIso_hom_apply, corrFunctorμIso_hom_apply]
    exact Subtype.ext ((map_mul (e.equiv _) _ _).trans
      (congrArg₂ (· * ·) (e.equiv_pull _ _) (e.equiv_pull _ _)))

end Iso

/-- **Isomorphic data have monoidally isomorphic realizations**: if `W` and `W'` are isomorphic
data (D0)–(D3) satisfying (A), (B), (C), the realizations of correspondences of degree zero are
isomorphic by a monoidal natural isomorphism. -/
theorem IsIsomorphic.nonempty_corrFunctorIso (h : W.IsIsomorphic W') :
    ∃ θ : corrFunctor hA hB hC ≅ corrFunctor hA' hB' hC', NatTrans.IsMonoidal θ.hom := by
  obtain ⟨e, hγ, htr⟩ := h
  exact ⟨e.corrFunctorIso hγ htr, inferInstance⟩

end Monoidal

end Stacks.WeilCohomology.WeilData

end
