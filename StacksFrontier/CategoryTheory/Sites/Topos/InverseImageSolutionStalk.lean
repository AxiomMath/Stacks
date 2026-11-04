module

public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageSolutionFork
public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemTransported

/-!
# The comparison of sheaves of solutions is invertible where it is bijective on solutions

Let `(g, g^♯) : (Sh(C), 𝒪') ⟶ (Sh(D), 𝒪)` be a morphism of ringed topoi with structure map
`α : g⁻¹𝒪 ⟶ 𝒪'`, let `H` be the equalizer of the row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` of a polynomial system `P`
downstairs, and let `T` be the equalizer of the row of the same `P` over `𝒪'` upstairs.
`Stacks.Sheaves.inverseImageForkComparison` is the morphism `g⁻¹H ⟶ T` carrying coordinates to
coordinates, and `Stacks.Sheaves.inverseImageForkComparison_eq_lift` says that it is the
canonical map of equalizers induced by `α`.

This file supplies the criterion under which that map is bijective along a left exact functor
`Q` to sets: because `g⁻¹H` is the equalizer of the row of `P` over `g⁻¹𝒪`
(`Stacks.Sheaves.isLimitForkInverseImage`) and `Q` is left exact, both sides become solution
sets of `P` over the transported rings `Q(g⁻¹𝒪)` and `Q(𝒪')`, and the comparison becomes the
coordinatewise map along `Q(α)`.

This is the reduction made in step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6): the small étale
site has enough points, so the comparison is an isomorphism as soon as it is bijective at every
stalk, and at a stalk it is the coordinatewise map between the solutions of an étale system over
two strictly henselian local rings along a local homomorphism — the bijection of
[Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX).  Neither the site nor the
geometry enters here: the stalkwise bijection is the hypothesis `hbij`.

## Main results

* `Stacks.Sheaves.bijective_map_of_comp_forkι`: **the map of equalizers induced by the structure
  map is bijective along a left exact functor to sets as soon as the coordinatewise map of
  solution sets is a bijection.**

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Stacks.Sheaves.ToposPullback
open scoped CommRingObj Obj

universe t w w' v u v' u'

namespace Stacks.Sheaves

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K CommRingCat.{w'})

attribute [local instance] Stacks.sheafCommRingObj

variable {Γ : Type*} [CommRing Γ] (κ : Type) [Finite κ] {ν : Type} [Finite ν]
  {H : Sheaf K (Type w')} (ι : H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf K O)
  (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ Stacks.underlyingRingSheaf K O))
  (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
    Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)))
  (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
  {O' : Sheaf J CommRingCat.{w}} (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O')
  (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))
  (P : ν → MvPolynomial κ Γ)

include hc₁ in
/-- **The map of equalizers induced by the structure map is bijective along a left exact functor
to sets as soon as it is bijective on solution sets.**

Let `H` be the equalizer of the row of `P` over `𝒪` downstairs and `T` the equalizer of the row
of the same `P` over `𝒪'` upstairs, and let `m : g⁻¹H ⟶ T` carry the coordinates of `g⁻¹H` to
the coordinates of `T` — which pins `m` down as
`Stacks.Sheaves.inverseImageForkComparison`.  Let `Q` be a left exact functor to sets.  Then
`Q(m)` is bijective provided the coordinatewise map along `Q(α)` is a bijection from the
solutions of `P` over `Q(g⁻¹𝒪)` onto the solutions of `P` over `Q(𝒪')`.

The two inputs are `Stacks.Sheaves.isLimitForkInverseImage`, which makes `g⁻¹H` the equalizer of
the row of `P` over `g⁻¹𝒪`, and
`Stacks.Sheaves.PolynomialSystem.bijective_map_of_bijOn_solutions`, which reads a left exact
image of such an equalizer as the set of solutions over the transported ring.  No compatibility
between the coefficients downstairs and the coefficients upstairs is used: that compatibility is
what one uses to *prove* `hbij`, not to state it. -/
theorem bijective_map_of_comp_forkι
    (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν)
    (hs : IsLimit (Fork.ofι ι hι))
    {T : Sheaf J (Type w)} {ι' : T ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O'}
    (h' : ι' ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P =
      ι' ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν)
    (hl' : IsLimit (Fork.ofι ι' h'))
    (m : f.inverseImage.obj H ⟶ T)
    (hm : m ≫ ι' = inverseImageCoordinates f O α κ ι)
    (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteLimits Q]
    (hbij : Set.BijOn
      (fun a : κ → Q.obj (Stacks.underlyingRingSheaf J
          (pullbackCommRingSheaf J f.inverseImage O)) =>
        fun i => Q.map (PolynomialSystem.underlyingMap α) (a i))
      (PolynomialSystem.objSolutions Q κ P (pullbackCommRingSheaf J f.inverseImage O) c₁)
      (PolynomialSystem.objSolutions Q κ P O' c')) :
    Function.Bijective (Q.map m) :=
  PolynomialSystem.bijective_map_of_bijOn_solutions α Q κ P c₁ c'
    (inverseImagePullbackCoordinates_comp_evalSystemHom f O κ ι c c₁ hc₁ P hι)
    (isLimitForkInverseImage f O κ ι c c₁ hc₁ P hι hs) h' hl' m
    (hm.trans (inverseImageCoordinates_eq f O κ ι α)) hbij

end Stacks.Sheaves

end
