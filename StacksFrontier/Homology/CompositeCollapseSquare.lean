module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Acyclicity across a commutative square of left exact functors

Let `h : 𝒞₁ ⥤ 𝒞₂`, `a : 𝒞₂ ⥤ 𝒞₃`, `f : 𝒞₁ ⥤ 𝒞₄` and `x : 𝒞₄ ⥤ 𝒞₃` be additive left exact
functors between abelian categories with enough injectives, with `h ⋙ a ≅ f ⋙ x`, `h` and `f`
carrying injectives to `a`- and `x`-acyclic objects. If `M` is acyclic for `h` and for `f`, then
`Rⁿa(h M) ≅ Rⁿ(h ⋙ a)(M) ≅ Rⁿ(f ⋙ x)(M) ≅ Rⁿx(f M)` by two collapses of the Grothendieck
spectral sequence (`Stacks.RightDerivedComp.objIsoOfAcyclicImage`). In particular `h M` is
`a`-acyclic as soon as `f M` is `x`-acyclic.

## Main results

* `Stacks.RightDerivedComp.isZero_rightDerived_of_square_compositeCollapseSquare`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [EnoughInjectives C₁] [EnoughInjectives C₂] [EnoughInjectives C₄]
  (h : C₁ ⥤ C₂) (a : C₂ ⥤ C₃) (f : C₁ ⥤ C₄) (x : C₄ ⥤ C₃)
  [ih : h.Additive] [ia : a.Additive] [if' : f.Additive] [ix : x.Additive]
  [lh : PreservesFiniteLimits h] [la : PreservesFiniteLimits a] [lf : PreservesFiniteLimits f]
  [lx : PreservesFiniteLimits x]

/-- **Acyclicity across a commutative square of left exact functors.** With `e : h ⋙ a ≅ f ⋙ x`,
`h` and `f` carrying injectives to `a`- and `x`-acyclic objects, `M` acyclic for `h` and `f`,
`G ≅ h M` and `f M ≅ E` with `E` acyclic for `x`, the object `G` is acyclic for `a`. -/
theorem isZero_rightDerived_of_square_compositeCollapseSquare (e : h ⋙ a ≅ f ⋙ x)
    (hh : ∀ Z : C₁, Injective Z → acyclic a (h.obj Z))
    (hf : ∀ Z : C₁, Injective Z → acyclic x (f.obj Z))
    {M : C₁} (hMh : ∀ n, 0 < n → IsZero ((h.rightDerived n).obj M))
    (hMf : ∀ n, 0 < n → IsZero ((f.rightDerived n).obj M))
    {G : C₂} (eG : G ≅ h.obj M) {E : C₄} (eE : f.obj M ≅ E)
    (hE : ∀ n, 0 < n → IsZero ((x.rightDerived n).obj E)) (n : ℕ) (hn : 0 < n) :
    IsZero ((a.rightDerived n).obj G) :=
  (hE n hn).of_iso
    ((a.rightDerived n).mapIso eG ≪≫ (objIsoOfAcyclicImage h a hMh hh n).symm ≪≫
      (Functor.rightDerivedIsoOfIso e n).app M ≪≫ objIsoOfAcyclicImage f x hMf hf n ≪≫
        (x.rightDerived n).mapIso eE)

end Stacks.RightDerivedComp

end
