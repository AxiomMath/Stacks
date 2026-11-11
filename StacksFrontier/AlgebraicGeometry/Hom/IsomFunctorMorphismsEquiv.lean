module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Hom.HomFunctorEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Hom.IsomFunctorMorphisms

/-!
# The morphisms from an algebraic space into the relative Isom functor

Let `f : X ⟶ base` be a morphism of algebraic spaces over `S` and let `F`, `G` be quasi-coherent
`𝒪_X`-modules. For an algebraic space `T` over `S`, the morphisms of fppf sheaves
`T ⟶ Isom(F, G)` are in bijection with the pairs `(h, u)` of a morphism `h : T ⟶ base` and an
isomorphism `u : F_T ⟶ G_T` of the modules pulled back to `X ×_{base, h} T`. Here `Isom(F, G)` is
the presheaf built from the pseudofunctoriality of direct images
`AlgebraicGeometry.Space.modulePushforwardCoherence`.

## Main results

* `AlgebraicGeometry.Space.HomSituation.etaleReverseHomDescent`: homomorphisms `G_U ⟶ F_U` whose
  two pullbacks along a kernel pair agree descend along surjective étale morphisms.
* `AlgebraicGeometry.Space.HomSituation.bijective_isomMorOfSpaceIsom`: the map
  `(h, u) ↦ isomMorOfSpaceIsom (h, u)` is a bijection onto the morphisms `T ⟶ Isom(F, G)`.

## References

* [Stacks Project, Tag 0D3T](https://stacks.math.columbia.edu/tag/0D3T)
* [Stacks Project, Tag 0D3S](https://stacks.math.columbia.edu/tag/0D3S)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

namespace HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : HomSituation B S hS)

/-- The fullness clause for the reversed pair of modules: along a surjective étale morphism of
algebraic spaces over the base, a homomorphism `G_U ⟶ F_U` whose two pullbacks along a kernel
pair agree descends. -/
theorem etaleReverseHomDescent : s.EtaleReverseHomDescent :=
  ⟨fun g hsurj hetale _ p q hpb w hw =>
    s.exists_conjHom_spaceBaseChangeComparison_eq (M := s.G) (N := s.F) g hsurj hetale p q hpb
      w hw⟩

/-- Let `T` be an algebraic space over `S`. The assignment `(h, u) ↦ isomMorOfSpaceIsom (h, u)`
is a bijection from the pairs of a morphism `h : T ⟶ base` and an isomorphism `u : F_T ⟶ G_T` of
the modules pulled back to `X ×_{base, h} T` onto the morphisms of presheaves `T ⟶ Isom(F, G)` on
the big fppf site of `S`:

`Mor(T, Isom(F, G)) = {(h, u) | h : T ⟶ base, u : F_T ⟶ G_T an isomorphism}`.

Here `Isom(F, G)` is the presheaf built from the pseudofunctoriality of direct images
`AlgebraicGeometry.Space.modulePushforwardCoherence`. -/
@[stacks 0D3T "the whole identification, in Situation 08JT: for any algebraic space T over S, \
the map (h, u) |-> the morphism T -> Isom(F, G) is a bijection from all pairs of h : T -> base \
and an isomorphism u : F_T -> G_T of the pullbacks to X x_{base, h} T onto all morphisms from T \
into Isom(F, G); the pseudofunctoriality of direct images and both descent clauses are supplied \
by library results, so the statement takes no hypothesis"]
theorem bijective_isomMorOfSpaceIsom (T : AlgebraicSpaces B S hS) :
    Function.Bijective (fun p : (Σ h : T ⟶ s.base,
        {u : s.spaceHomAt (Over.mk h) // s.IsIsomOverAt u}) =>
      s.isomMorOfSpaceIsom (modulePushforwardCoherence B S hS) p.1 p.2.1 p.2.2) := by
  constructor
  · rintro ⟨h, p⟩ ⟨h', p'⟩ e
    obtain rfl : h = h' := by
      simpa only [baseOfIsomMor_isomMorOfSpaceIsom] using
        congrArg (s.baseOfIsomMor (modulePushforwardCoherence B S hS)) e
    obtain rfl := s.injective_isomMorOver (modulePushforwardCoherence B S hS) h
      (a₁ := p) (a₂ := p') (Subtype.ext e)
    rfl
  · intro v
    obtain ⟨p, hp⟩ := s.surjective_isomMorOver (modulePushforwardCoherence B S hS)
      s.etaleHomDescent s.etaleReverseHomDescent
      (s.baseOfIsomMor (modulePushforwardCoherence B S hS) v) ⟨v, rfl⟩
    exact ⟨⟨_, p⟩, congrArg Subtype.val hp⟩

end HomSituation

end AlgebraicGeometry.Space

end
