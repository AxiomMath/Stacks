module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionAlgebraic

/-!
# The excision algebraicity criterion with the coproduct discharged

`AlgebraicGeometry.Space.isAlgebraicSpace_of_excisionBaseSource` takes the coproduct of the
two excision legs as data, which is how every coproduct hypothesis in this library is carried.
A consumer of that criterion has to produce the coproduct, so this file produces it once: the
coproduct of a `Bool`-indexed family of fppf sheaves, and then the criterion with the cofan
discharged.

## Main results

* `AlgebraicGeometry.Space.exists_isColimit_cofan_sheaf_bool`: a pair of fppf sheaves on the
  big fppf site of `S` has a coproduct.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_excisionBaseSource'`: the excision criterion
  whose only hypotheses are that the two legs are algebraic spaces.

## Implementation notes

The coproduct is *not* obtained by asking instance search for
`CategoryTheory.Limits.HasColimit` in the sheaf category: that search is what makes the
coproduct awkward to discharge here, and forcing it through would need a raised heartbeat
limit, which this file declines to take on. It is obtained instead by sheafifying the
presheaf-level coproduct, which needs only colimits of presheaves —
`CategoryTheory.Sheaf.sheafifyCocone` applied to
`CategoryTheory.Limits.colimit.cocone`, and
`CategoryTheory.Sheaf.isColimitSheafifyCocone` to see that the result is still a colimit. The
sheafification functor is available because the big fppf category over `S` is essentially
small, which is `AlgebraicGeometry.hasSheafify_bigFppfOver`.

The index type is `Bool` rather than an arbitrary small type because that is the index of
`AlgebraicGeometry.Space.excisionBaseSource`, and keeping it concrete avoids a `Small`
side-condition at every call site. Nothing below uses that it is `Bool` beyond its being a
small type.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A pair of fppf sheaves on the big fppf site of `S` has a coproduct: sheafify the
presheaf-level coproduct. -/
theorem exists_isColimit_cofan_sheaf_bool
    (Fi : Bool → Sheaf (BigFppfOver.topology B S hS) (Type u)) :
    ∃ (G : Sheaf (BigFppfOver.topology B S hS) (Type u)) (ι : ∀ b, Fi b ⟶ G),
      Nonempty (IsColimit (Cofan.mk G ι)) := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  let Fcop : Discrete Bool ⥤ Sheaf (BigFppfOver.topology B S hS) (Type u) := Discrete.functor Fi
  let Ecop : Cocone (Fcop ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)) :=
    colimit.cocone (Fcop ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u))
  refine ⟨(Sheaf.sheafifyCocone (F := Fcop) Ecop).pt,
    fun b => (Sheaf.sheafifyCocone (F := Fcop) Ecop).ι.app (Discrete.mk b), ⟨?_⟩⟩
  change IsColimit (Sheaf.sheafifyCocone (F := Fcop) Ecop)
  exact Sheaf.isColimitSheafifyCocone (F := Fcop) Ecop
    (colimit.isColimit (Fcop ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)))

variable {V W : AlgebraicSpaces B S hS}

/-- **A presheaf over `W` whose two excision legs are algebraic is an algebraic space**, with
the coproduct of the legs discharged.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_of_excisionBaseSource` with its cofan
supplied, so that its only hypotheses are that the part of `X` lying over the open complement
of `T` and the fibre product `X ×_W V` are algebraic spaces. Those two are the computations
`X ×_W W⁰ = W⁰` and `X ×_W V = Y` of Stacks 0BGY. -/
theorem isAlgebraicSpace_of_excisionBaseSource' (f : V ⟶ W) (hf : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (g : X ⟶ W.obj)
    (hsrc : ∀ b, IsAlgebraicSpace B S hS (excisionBaseSource B S hS f T g b)) :
    IsAlgebraicSpace B S hS X := by
  obtain ⟨G, ι, ⟨hcoprod⟩⟩ := exists_isColimit_cofan_sheaf_bool B S hS
    (fun b => ⟨excisionBaseSource B S hS f T g b, (hsrc b).isSheaf⟩)
  exact isAlgebraicSpace_of_excisionBaseSource B S hS f hf hsep T hT hfT hX g hsrc G ι hcoprod

end AlgebraicGeometry.Space

end
