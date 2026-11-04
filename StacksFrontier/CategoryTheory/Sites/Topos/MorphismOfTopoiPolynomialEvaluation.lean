module

public import StacksFrontier.CategoryTheory.Sites.Topos.InternalPolynomialEvaluation
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing

/-!
# The inverse image of a morphism of topoi carries polynomial evaluation to polynomial evaluation

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and `𝒪` a sheaf of commutative rings on `Sh(D)`.
The inverse image `f⁻¹` is left exact, hence preserves finite products, hence is braided
monoidal for the cartesian structures; so the abstract preservation theorem
`CategoryTheory.CommRingObj.map_evalPowRingHom` applies to it verbatim. The resulting statement is
`Stacks.Sheaves.inverseImage_map_evalPowRingHom`: `f⁻¹` carries the evaluation morphism
`(∏ᵏ 𝒪) ⟶ 𝒪` of a polynomial `P` to the evaluation morphism of the *same* `P` on
`(∏ᵏ f⁻¹𝒪) ⟶ f⁻¹𝒪`, its coefficients read into `f⁻¹𝒪` through
`CategoryTheory.Functor.mapGlobalRingHom`, the two powers being compared by
`Limits.piComparison` — an isomorphism exactly because `f⁻¹` preserves the product.

This is step (3) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6). There `𝒪 = 𝒪_Y`, the
polynomials are the `P_i` of a standard étale presentation
`C = B[x_1, …, x_n]/(P_1, …, P_n)` of an affine `V` étale over `Y = Spec(B)`, and the
coefficients live in `B`; applying `g^{-1}` to the row that cuts `h_V` out of `∏ᵢ 𝒪_Y` by the
vanishing of the `P_i` gives a row of the same shape for the polynomials `φ(P_i)`, which is the
row cutting out `h_{X ×_Y V}` for `X ×_Y V = Spec(A ⊗_B C)`. The identification of
`f⁻¹𝒪` with the structure sheaf upstairs — the composition with `f^\sharp` — is a separate step,
and is *not* asserted here.

## Main results

* `Stacks.Sheaves.inverseImage_map_evalPowRingHom`: the inverse image of a morphism of topoi
  carries the evaluation morphism of the `κ`-fold power of a sheaf of commutative rings to the
  evaluation morphism of the `κ`-fold power of its inverse image.
* `Stacks.Sheaves.inverseImage_map_evalSystemHom` and
  `Stacks.Sheaves.inverseImage_map_zeroSystemHom`: the same for the two legs `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` of the
  equalizer presentation cutting out the solutions of a system of polynomial equations.

## Implementation notes

`Stacks.sheafCommRingObj` and `CategoryTheory.Functor.Braided.ofChosenFiniteProducts` are made
local instances here. Mathlib deliberately keeps the latter out of instance search because it
would produce a diamond for the identity functor and for composites; keying it to
`MorphismOfTopoi.inverseImage` of a given morphism of topoi avoids that, and
`CategoryTheory.Functor.Braided` is a subsingleton in any case.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

universe w w' v u v' u'

namespace Stacks.Sheaves

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

attribute [local instance] Stacks.sheafCommRingObj

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image of a morphism of topoi is braided monoidal for the cartesian monoidal
structures: it is left exact, hence preserves finite products. -/
noncomputable instance inverseImageBraided : f.inverseImage.Braided :=
  Functor.Braided.ofChosenFiniteProducts _

variable (O : Sheaf K CommRingCat.{w'})

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The inverse image of a morphism of topoi carries polynomial evaluation to polynomial
evaluation of the pushed-forward coefficients.**

The evaluation morphism of a polynomial `P` with coefficients in `Γ`, read into the global
sections of `𝒪` by `c`, on the `κ`-fold power of the underlying sheaf of sets of `𝒪`, is carried
by `f⁻¹` to the evaluation morphism of the same `P` on the `κ`-fold power of `f⁻¹𝒪`, with the
coefficients read into the global sections of `f⁻¹𝒪` through
`CategoryTheory.Functor.mapGlobalRingHom`. The two powers are compared by `Limits.piComparison`,
which is an isomorphism because `f⁻¹` preserves the product.

This is the content localized in step (3) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6). -/
theorem inverseImage_map_evalPowRingHom (κ : Type) [Finite κ] {Γ : Type*} [CommRing Γ]
    (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ underlyingRingSheaf K O)) (P : MvPolynomial κ Γ) :
    f.inverseImage.map (CommRingObj.evalPowRingHom (underlyingRingSheaf K O) c κ P) =
      piComparison f.inverseImage (fun _ : κ => underlyingRingSheaf K O) ≫
        CommRingObj.evalPowRingHom (f.inverseImage.obj (underlyingRingSheaf K O))
          ((f.inverseImage.mapGlobalRingHom (underlyingRingSheaf K O)).comp c) κ P :=
  CommRingObj.map_evalPowRingHom f.inverseImage (underlyingRingSheaf K O) c κ P

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The inverse image of a morphism of topoi carries the row of a system of polynomial
equations to the row of the pushed-forward system.**

The first leg of the equalizer presentation: the arrow `∏ᵏ 𝒪 ⟶ ∏ᵛ 𝒪` whose `j`-th component is
the evaluation morphism of `P j` is carried by `f⁻¹`, modulo the two power comparisons, to the
arrow of the same family with coefficients read into `f⁻¹𝒪`. -/
theorem inverseImage_map_evalSystemHom (κ : Type) [Finite κ] {ν : Type} [Finite ν] {Γ : Type*}
    [CommRing Γ] (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ underlyingRingSheaf K O))
    (P : ν → MvPolynomial κ Γ) :
    f.inverseImage.map (CommRingObj.evalSystemHom (underlyingRingSheaf K O) c κ P) ≫
        piComparison f.inverseImage (fun _ : ν => underlyingRingSheaf K O) =
      piComparison f.inverseImage (fun _ : κ => underlyingRingSheaf K O) ≫
        CommRingObj.evalSystemHom (f.inverseImage.obj (underlyingRingSheaf K O))
          ((f.inverseImage.mapGlobalRingHom (underlyingRingSheaf K O)).comp c) κ P :=
  CommRingObj.map_evalSystemHom f.inverseImage (underlyingRingSheaf K O) c κ P

omit [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **The inverse image of a morphism of topoi carries the zero row to the zero row.** The second
leg of the equalizer presentation, the companion of
`Stacks.Sheaves.inverseImage_map_evalSystemHom`. -/
theorem inverseImage_map_zeroSystemHom (κ : Type) [Finite κ] (ν : Type) [Finite ν] :
    f.inverseImage.map (CommRingObj.zeroSystemHom (underlyingRingSheaf K O) κ ν) ≫
        piComparison f.inverseImage (fun _ : ν => underlyingRingSheaf K O) =
      piComparison f.inverseImage (fun _ : κ => underlyingRingSheaf K O) ≫
        CommRingObj.zeroSystemHom (f.inverseImage.obj (underlyingRingSheaf K O)) κ ν :=
  CommRingObj.map_zeroSystemHom f.inverseImage (underlyingRingSheaf K O) κ ν

end Stacks.Sheaves
