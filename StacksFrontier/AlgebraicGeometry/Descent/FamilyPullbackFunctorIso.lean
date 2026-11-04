module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackCompatibility
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.PullbackFunctorIso

/-!
# Independence of the pullback functor for families from the chosen morphism of families

Two morphisms of families of schemes with fixed target which have the same morphism of base
schemes induce canonically isomorphic pullback functors on descent data, even though their
index maps and their component morphisms may differ.

## Main definitions

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackFunctorCompIso` compares the two pullback
  functors after composing with the equivalence of the source family with its coproduct
  morphism, and
* `AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackFunctorIso` is the canonical natural
  isomorphism between the two pullback functors themselves.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.isoWhiskerRight_pullbackFunctorIso` says that
  composing the latter with that equivalence returns the former, which determines it.

## Implementation notes

The two morphisms of families induce two morphisms between the coproducts of the members, both
lying over the same morphism of base schemes, so the two pullback functors for a single
morphism of schemes are canonically isomorphic by
`AlgebraicGeometry.DescentData.pullbackFunctorIso`. Whiskering that isomorphism with the
equivalence of a family with its coproduct morphism and conjugating by the two comparisons of
`AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackCompatibility` identifies the two pullback
functors for the families after composing with the equivalence for the source family.

Composing with an equivalence is a fully faithful functor between the two functor categories,
so that comparison has a unique preimage, and it is the isomorphism asked for.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.MorphismOfSchemeFamilies

variable {S S' : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S') (𝒱 : PreZeroHypercover.{u} S)
  (h : S' ⟶ S) (φ ψ : 𝒰.HomOver 𝒱 h)

/-- The two pullback functors for the families become isomorphic after composing with the
equivalence of the source family with its coproduct morphism: the two induced morphisms of
coproducts lie over the same morphism of base schemes, so Tag 023Y part (2) applies to them,
and the two comparisons of Tag 02VS part (4) carry the result back. -/
def pullbackFunctorCompIso :
    (pullbackFunctor (ofHomOver 𝒰 𝒱 h φ)).functor ⋙
        (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor ≅
      (pullbackFunctor (ofHomOver 𝒰 𝒱 h ψ)).functor ⋙
        (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor :=
  (pullbackCompatibility (ofHomOver 𝒰 𝒱 h φ)).iso.symm ≪≫
    Functor.isoWhiskerLeft (DescentData.familyCoproductEquivalence 𝒱.f).equivalence.functor
      (DescentData.pullbackFunctorIso (Sigma.desc 𝒱.f) (Sigma.desc 𝒰.f) h
        (ofHomOver 𝒰 𝒱 h φ).coproductHom (ofHomOver 𝒰 𝒱 h ψ).coproductHom
        (ofHomOver 𝒰 𝒱 h φ).coproductHom_comp
        (ofHomOver 𝒰 𝒱 h ψ).coproductHom_comp).iso ≪≫
    (pullbackCompatibility (ofHomOver 𝒰 𝒱 h ψ)).iso

/-- **Stacks Project, Tag 02VS, part (3).** Two morphisms of families of morphisms with fixed
target which have the same morphism `h` of base schemes induce canonically isomorphic pullback
functors on descent data, whatever their index maps and component morphisms are. -/
@[stacks 02VS "part (3)"]
def pullbackFunctorIso :
    (pullbackFunctor (ofHomOver 𝒰 𝒱 h φ)).functor ≅
      (pullbackFunctor (ofHomOver 𝒰 𝒱 h ψ)).functor :=
  Functor.preimageIso
    ((Functor.whiskeringRight (DescentData 𝒱.f) (DescentData 𝒰.f) _).obj
      (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor)
    (pullbackFunctorCompIso 𝒰 𝒱 h φ ψ)

/-- The comparison of part (3) is the unique one which becomes `pullbackFunctorCompIso` after
composing with the equivalence of the source family with its coproduct morphism. -/
lemma isoWhiskerRight_pullbackFunctorIso :
    Functor.isoWhiskerRight (pullbackFunctorIso 𝒰 𝒱 h φ ψ)
        (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor =
      pullbackFunctorCompIso 𝒰 𝒱 h φ ψ :=
  Iso.ext (Functor.map_preimage
    ((Functor.whiskeringRight (DescentData 𝒱.f) (DescentData 𝒰.f)
      (DescentData (fun _ : Unit ↦ Sigma.desc 𝒰.f))).obj
      (DescentData.familyCoproductEquivalence 𝒰.f).equivalence.functor)
    (pullbackFunctorCompIso 𝒰 𝒱 h φ ψ).hom)

end AlgebraicGeometry.MorphismOfSchemeFamilies
