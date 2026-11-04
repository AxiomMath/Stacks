module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheafComap
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve

/-!
# Exceptional curves of the first kind descend along an inverse image

Let `q : X ⟶ Y` be a morphism of schemes and `D ⊆ Y` an effective Cartier divisor whose pullback
is defined. If the induced morphism `q^{-1}D ⟶ D` of closed subschemes is an isomorphism and
`q^{-1}D` is an exceptional curve of the first kind, then so is `D`.

This is the shape in which an exceptional curve is transported across a comparison of two
presentations of one blowup, and across a flat base change in which the exceptional divisor does
not change: in both cases the ambient morphism `q` is not an isomorphism (or is one, but between
two different presentations), while the morphism of exceptional divisors is.

## Main results

* `AlgebraicGeometry.exists_isExceptionalCurveOfFirstKind_of_comap`.

## Implementation notes

The effective-Cartier clause of the conclusion is a hypothesis of the statement, so the content
is the normal-sheaf clause, and that is `Stacks.Divisors.normalSheafComapIso`: the normal sheaf
of `q^{-1}D` is the pullback of the normal sheaf of `D` along `q^{-1}D ⟶ D`, so composing the
given presentation `𝐏¹_k ≅ q^{-1}D` with that isomorphism of subschemes presents `D`, and the
pullback of the normal sheaf along the composite is the pullback along the given presentation of
the normal sheaf of `q^{-1}D`.

The divisor `q^{-1}D` is carried as a separate argument `D'` together with the equation
`D' = D.comap q` rather than written out, because at the point of use it has a name of its own —
the exceptional divisor of the blowup of the inverse-image centre — which is only
*propositionally* the inverse image of the exceptional divisor.
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **An exceptional curve of the first kind descends along an inverse image.** If the
scheme-theoretic inverse image of an effective Cartier divisor `D ⊆ Y` along `q : X ⟶ Y` is again
an effective Cartier divisor, the induced morphism of closed subschemes is an isomorphism, and
that inverse image is an exceptional curve of the first kind over `k`, then `D` is an exceptional
curve of the first kind over `k`. -/
theorem exists_isExceptionalCurveOfFirstKind_of_comap {X Y : Scheme.{u}} (q : X ⟶ Y)
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hD : Stacks.Divisors.IsPullbackDefined q D)
    (hiso : IsIso (Stacks.Divisors.comapSubschemeMap' q D))
    (D' : X.IdealSheafData) (hD' : D' = D.comap q)
    (k : Type u) [Field k] (e : projectiveLineProj k ≅ D'.subscheme)
    (hE : D'.IsExceptionalCurveOfFirstKind k e) :
    ∃ e' : projectiveLineProj k ≅ D.subscheme, D.IsExceptionalCurveOfFirstKind k e' := by
  subst hD'
  have := hiso
  refine ⟨e ≪≫ asIso (Stacks.Divisors.comapSubschemeMap' q D), ‹_›, ⟨?_⟩⟩
  refine ((modulePullbackComp e.hom.toLRSHom.toShHom
      (Stacks.Divisors.comapSubschemeMap' q D).toLRSHom.toShHom).app _) ≪≫
    (modulePullback e.hom.toLRSHom.toShHom).mapIso
      (Stacks.Divisors.normalSheafComapIso q D hD).symm ≪≫ hE.2.some

end AlgebraicGeometry

end
