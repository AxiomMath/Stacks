module

public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageStructureSharpRow

/-!
# The comparison morphism from the inverse image of a sheaf of solutions

Let `(g, g^♯) : (Sh(C), 𝒪') ⟶ (Sh(D), 𝒪)` be a morphism of ringed topoi with the structure map
in its inverse-image form `α : g⁻¹𝒪 ⟶ 𝒪'`, and let `H` be a sheaf downstairs equipped with
`κ`-many coordinates `ι : H ⟶ ∏ᵏ 𝒪` solving a polynomial system `P` — that is, `ι` equalizes the
two legs of the row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪`.

Then `g⁻¹H` carries `κ`-many coordinates with values in `𝒪'`, namely `g⁻¹ι` followed by the
power comparison and `α`, and these solve the *same* system `P` read over `𝒪'`
(`Stacks.Sheaves.inverseImageCoordinates_comp_evalSystemHom`). Consequently, whenever the
solutions of `P` over `𝒪'` are themselves cut out by a limit fork, there is a canonical
comparison morphism from `g⁻¹H` into that sheaf of solutions
(`Stacks.Sheaves.inverseImageForkComparison`), and it is the unique morphism carrying the
coordinates to the coordinates.

In the proof of [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) this is
the comparison `g⁻¹h_V ⟶ h_{X ×_Y V}`: there `H = h_V` for an affine `V = Spec(C)` étale over
`Y = Spec(B)` with a standard presentation `C = B[x₁, …, x_n]/(P₁, …, P_n)`, the coordinates
downstairs are `Stacks.EtaleCohomology.smallEtaleYonedaCoordinates`, the fork they sit in is
`Stacks.EtaleCohomology.isLimitForkSmallEtaleYoneda`, and upstairs the fork is the one of the
system `φ(P)` over `𝒪_X`, whose sheaf of solutions is `h_{X ×_Y V}` for
`X ×_Y V = Spec(A ⊗_B C)`.

## Main definitions

* `Stacks.Sheaves.inverseImageCoordinates`: the `κ`-tuple of sections of `𝒪'` carried by
  `g⁻¹H`.
* `Stacks.Sheaves.inverseImageForkComparison`: the comparison morphism into a sheaf of solutions
  of `P` over `𝒪'` presented as a limit fork.

## Main results

* `Stacks.Sheaves.inverseImageCoordinates_comp_evalSystemHom`: the coordinates upstairs solve the
  pushed-forward system.
* `Stacks.Sheaves.inverseImageForkComparison_comp_ι` and
  `Stacks.Sheaves.inverseImageForkComparison_unique`: the comparison morphism carries the
  coordinates to the coordinates, and is the only morphism that does.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Stacks.Sheaves.ToposPullback
open scoped CommRingObj Obj

universe w w' v u v' u'

namespace Stacks.Sheaves

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget CommRingCat.{w})] [K.HasSheafCompose (forget CommRingCat.{w'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K CommRingCat.{w'}) {O' : Sheaf J CommRingCat.{w}}

attribute [local instance] Stacks.sheafCommRingObj

variable {Γ : Type*} [CommRing Γ]
  (α : pullbackCommRingSheaf J f.inverseImage O ⟶ O')
  (κ : Type) [Finite κ] {ν : Type} [Finite ν]
  {H : Sheaf K (Type w')} (ι : H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf K O)

/-- **The coordinates carried by the inverse image of a sheaf with coordinates.** If `H` has
`κ`-many coordinates with values in `𝒪` downstairs, then `g⁻¹H` has `κ`-many coordinates with
values in `𝒪'` upstairs: apply `g⁻¹`, compare the two `κ`-fold powers, and push along the
structure map `α`. -/
def inverseImageCoordinates :
    f.inverseImage.obj H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf J O' :=
  f.inverseImage.map ι ≫
    piComparison f.inverseImage (fun _ : κ => Stacks.underlyingRingSheaf K O) ≫
      Limits.Pi.map (fun _ : κ => PolynomialSystem.underlyingMap α)

variable (c : Γ →+* (𝟙_ (Sheaf K (Type w')) ⟶ Stacks.underlyingRingSheaf K O))
  (c₁ : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶
    Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J f.inverseImage O)))
  (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
  (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))
  (hc' : ∀ r, c' r = c₁ r ≫ PolynomialSystem.underlyingMap α)
  (P : ν → MvPolynomial κ Γ)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})] in
include hc₁ hc' in
/-- **The inverse image of a sheaf of solutions solves the pushed-forward system.** If the
coordinates of `H` solve `P` over `𝒪` downstairs — that is, if they equalize the two legs of the
row `∏ᵏ 𝒪 ⇉ ∏ᵛ 𝒪` — then the coordinates of `g⁻¹H` solve the same `P` over `𝒪'`, its
coefficients read into `𝒪'` through `g⁻¹` and the structure map `α`. -/
theorem inverseImageCoordinates_comp_evalSystemHom
    (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν) :
    inverseImageCoordinates f O α κ ι ≫
        CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P =
      inverseImageCoordinates f O α κ ι ≫
        CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν := by
  simp only [inverseImageCoordinates, Category.assoc]
  rw [← inverseImage_evalSystemHom_comp_fSharp f O α κ c c₁ hc₁ c' hc' P,
    ← Category.assoc, ← f.inverseImage.map_comp, hι, f.inverseImage.map_comp, Category.assoc,
    inverseImage_zeroSystemHom_comp_fSharp f O α κ ν]

section Fork

variable {t : Limits.Fork (CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf J O') c' κ P)
    (CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf J O') κ ν)} (ht : IsLimit t)
  (hι : ι ≫ CommRingObj.evalSystemHom (Stacks.underlyingRingSheaf K O) c κ P =
    ι ≫ CommRingObj.zeroSystemHom (Stacks.underlyingRingSheaf K O) κ ν)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

include hc₁ hc' hι in
/-- **The comparison morphism from the inverse image of a sheaf of solutions.** Let the
solutions of `P` over `𝒪'` upstairs be cut out by a limit fork `t` of the two legs of the row
`∏ᵏ 𝒪' ⇉ ∏ᵛ 𝒪'`. The coordinates of `g⁻¹H` are sections of `𝒪'` solving `P`
(`Stacks.Sheaves.inverseImageCoordinates_comp_evalSystemHom`), so they factor through `t`, and
the factorization is the comparison morphism. -/
def inverseImageForkComparison : f.inverseImage.obj H ⟶ t.pt :=
  (Limits.Fork.IsLimit.lift' ht (inverseImageCoordinates f O α κ ι)
    (inverseImageCoordinates_comp_evalSystemHom f O α κ ι c c₁ hc₁ c' hc' P hι)).1

include hc₁ hc' hι in
/-- The comparison morphism carries the coordinates of `g⁻¹H` to the coordinates of the sheaf of
solutions upstairs. -/
theorem inverseImageForkComparison_comp_ι :
    inverseImageForkComparison f O α κ ι c c₁ hc₁ c' hc' P ht hι ≫ Limits.Fork.ι t =
      inverseImageCoordinates f O α κ ι :=
  (Limits.Fork.IsLimit.lift' ht _ _).2

include hc₁ hc' hι in
/-- **The comparison morphism is the only morphism carrying the coordinates to the
coordinates.** -/
theorem inverseImageForkComparison_unique (m : f.inverseImage.obj H ⟶ t.pt)
    (hm : m ≫ Limits.Fork.ι t = inverseImageCoordinates f O α κ ι) :
    m = inverseImageForkComparison f O α κ ι c c₁ hc₁ c' hc' P ht hι :=
  Limits.Fork.IsLimit.hom_ext ht
    (hm.trans (inverseImageForkComparison_comp_ι f O α κ ι c c₁ hc₁ c' hc' P ht hι).symm)

end Fork

end Stacks.Sheaves

end
