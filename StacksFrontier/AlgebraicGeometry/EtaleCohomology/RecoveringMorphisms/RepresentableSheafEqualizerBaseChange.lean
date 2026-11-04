module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableSheafEqualizer
public import StacksFrontier.RingTheory.Etale.StandardPresentationBaseChange

/-!
# The equalizer presentation of an affine chart, with its coefficients read from a base ring

Let `X` be an affine scheme of a big étale site, let `R₀` be a commutative ring with a
homomorphism `φ : R₀ ⟶ Γ(X, ⊤)`, and let `W` be an affine object of the small étale site of `X`
whose ring of global functions is presented as `Γ(X, ⊤)[x₁, …, x_n]/(φP₁, …, φP_n)` for a system
`P₁, …, P_n` of polynomials with coefficients in `R₀`.  Then the representable sheaf `h_W` on the
small étale site of `X` is the equalizer of the two maps `∏ᵢ 𝒪_X ⇉ ∏ⱼ 𝒪_X` given by the system
`P` with its coefficients read into `𝒪_X` through `φ`, and by the zero section.

`Stacks.EtaleCohomology.isLimitForkSmallEtaleYoneda` already presents `h_W` as such an equalizer,
but for the system `φP` over the base ring `Γ(X, ⊤)`.  That is the wrong row for the comparison
of step (3) of the proof of [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6):
there the row downstairs is the row of `P` over `𝒪_Y` with coefficients in `Γ(Y, ⊤)`, and the row
it is carried to by `g⁻¹` and `g^♯` is the row of **the same** `P`, over `𝒪_X`, with coefficients
read through `φ` — the shape `Stacks.Sheaves.inverseImage_evalSystemHom_comp_fSharp` produces and
`Stacks.Sheaves.inverseImageForkComparison` consumes as its `c'`.  Passing between the two
readings is exactly `MvPolynomial.isSolution_map`: a point of `Γ(U, ⊤)` solves `φP` over
`Γ(X, ⊤)` iff it solves `P` over `R₀`.

So this file is the other half of the source's step (3) — "the corresponding row for
`X ×_Y V = Spec(A ⊗_B C)` is an equalizer as well" — in the form the comparison needs, granted
the presentation of `Γ(W, ⊤)` as the base change of the presentation of `Γ(V, ⊤)`.  What it does
not do is identify `W` with the fibre product `X ×_Y V`; it takes the base-changed presentation
as the datum, exactly as `RepresentableSheafEqualizer.lean` takes the presentation downstairs as
the datum rather than producing it from étaleness.

`R₀` is left abstract rather than taken to be `Γ(Y, ⊤)`: nothing here uses `Y` or its
affineness, only the ring of coefficients and the map carrying them into `Γ(X, ⊤)`.

This is a step of the proof of Stacks 04I6 and not a clause of it — the tag asserts a
2-isomorphism of morphisms of ringed topoi together with its uniqueness — so **nothing here
carries an `@[stacks 04I6]` tag.**

## Main definitions

* `Stacks.EtaleCohomology.baseChangeStructureSection`: the structure map `R₀ ⟶ Γ(U, ⊤)` of a
  chart, read through `φ`, which exhibits `𝒪_X` as a sheaf of `R₀`-algebras.
* `Stacks.EtaleCohomology.smallEtaleSolutionEquivBase`: the sections of `h_W` over a chart are
  the solutions of `P` over `R₀` in that chart's ring of functions.
* `Stacks.EtaleCohomology.smallEtaleYonedaCoordinatesBase`: the resulting morphism
  `h_W ⟶ ∏ᵢ 𝒪_X`.

## Main results

* `Stacks.EtaleCohomology.isLimitForkSmallEtaleYonedaBase`: **`h_W` is the equalizer of
  `∏ᵢ 𝒪_X ⇉ ∏ⱼ 𝒪_X` for the row of `P` with coefficients read through `φ`.**

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CommRingObj Obj

universe u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry Stacks.Sheaves.PolynomialSystem

attribute [local instance] Stacks.sheafCommRingObj

attribute [local instance] isAffine_inclusion_obj_base

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) [IsAffine X]
  {R₀ : CommRingCat.{u}} (φ : R₀ ⟶ Γ(X, ⊤))
  (W : SmallEtale B X hX) [IsAffine ((SmallEtale.toScheme B X hX).obj W)] {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) R₀)
  (pres : StandardPresentationOver ((SmallEtale.toScheme B X hX).obj W)
    (B.inclusion.map W.obj.hom) (fun j => MvPolynomial.map φ.hom (P j)))

/-- The structure map of a chart on global functions, read from the base ring `R₀` through `φ`:
`R₀ ⟶ Γ(U, ⊤)`.  It is the composite of `φ` with
`AlgebraicGeometry.SmallEtale.structureBaseSection`, written through `CommRingCat.ofHom` so that
its underlying ring homomorphism is the composite on the nose, which is the form
`MvPolynomial.IsSolution` wants. -/
def baseChangeStructureSection (U : (SmallEtale B X hX)ᵒᵖ) :
    R₀ ⟶ (SmallEtale.commRingStructureSheaf B X hX).obj.obj U :=
  CommRingCat.ofHom ((SmallEtale.structureBaseSection B X hX U).hom.comp φ.hom)

omit [IsAffine X] in
/-- **The structure maps from the base ring are compatible with restriction**, so `𝒪_X` is a
sheaf of `R₀`-algebras.  It is `AlgebraicGeometry.SmallEtale.structureBaseSection_comp_map`
precomposed with `φ`. -/
theorem baseChangeStructureSection_comp_map {U U' : (SmallEtale B X hX)ᵒᵖ} (g : U ⟶ U') :
    baseChangeStructureSection B hX φ U ≫
        (SmallEtale.commRingStructureSheaf B X hX).obj.map g =
      baseChangeStructureSection B hX φ U' := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  exact congrArg (fun ψ : Γ(X, ⊤) ⟶ (SmallEtale.commRingStructureSheaf B X hX).obj.obj U' =>
    ψ.hom (φ.hom r)) (SmallEtale.structureBaseSection_comp_map B X hX g)

/-- **The sections of `h_W` over a chart are the solutions of `P` over the base ring `R₀`.**
This is `Stacks.EtaleCohomology.smallEtaleSolutionEquiv` for the base-changed system `φP` over
`Γ(X, ⊤)`, re-read as a statement about `P` over `R₀` by `MvPolynomial.isSolutionMapEquiv`. -/
def smallEtaleSolutionEquivBase (U : (SmallEtale B X hX)ᵒᵖ) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B X hX) U).obj
        ((smallEtaleYoneda B X hX).obj W) ≃
      {b : Fin n → (SmallEtale.commRingStructureSheaf B X hX).obj.obj U //
        MvPolynomial.IsSolution P (baseChangeStructureSection B hX φ U).hom b} :=
  (smallEtaleSolutionEquiv B hX W (fun j => MvPolynomial.map φ.hom (P j)) pres U).trans
    (MvPolynomial.isSolutionMapEquiv P φ.hom
      (SmallEtale.structureBaseSection B X hX U).hom)

/-- The solution a section of `h_W` names does not depend on which of the two readings of the
system it is taken in: `MvPolynomial.isSolutionMapEquiv` only re-reads the property, not the
tuple. -/
theorem smallEtaleSolutionEquivBase_coe (U : (SmallEtale B X hX)ᵒᵖ)
    (t : (Sheaf.sectionsFunctor (SmallEtale.topology B X hX) U).obj
      ((smallEtaleYoneda B X hX).obj W)) :
    (smallEtaleSolutionEquivBase B hX φ W P pres U t).1 =
      (smallEtaleSolutionEquiv B hX W (fun j => MvPolynomial.map φ.hom (P j)) pres U t).1 :=
  rfl

/-- **The identification is natural in the chart**, which is what makes it a presentation of the
*sheaf* `h_W`.  It is `Stacks.EtaleCohomology.smallEtaleSolutionEquiv_naturality`, the re-reading
of the solution property being invisible to the tuple. -/
theorem smallEtaleSolutionEquivBase_naturality {U U' : (SmallEtale B X hX)ᵒᵖ} (g : U ⟶ U')
    (t : (Sheaf.sectionsFunctor (SmallEtale.topology B X hX) U).obj
      ((smallEtaleYoneda B X hX).obj W)) (i : Fin n) :
    ((SmallEtale.commRingStructureSheaf B X hX).obj.map g).hom
        ((smallEtaleSolutionEquivBase B hX φ W P pres U t).1 i) =
      (smallEtaleSolutionEquivBase B hX φ W P pres U'
        (((smallEtaleYoneda B X hX).obj W).obj.map g t)).1 i :=
  smallEtaleSolutionEquiv_naturality B hX W (fun j => MvPolynomial.map φ.hom (P j)) pres g t i

/-- The morphism `h_W ⟶ ∏ᵢ 𝒪_X` sending an `X`-morphism `U ⟶ W` to the solution of `P` over
`R₀` that it names. -/
def smallEtaleYonedaCoordinatesBase :
    (smallEtaleYoneda B X hX).obj W ⟶
      ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (SmallEtale.commRingStructureSheaf B X hX) :=
  solutionCoordinates (SmallEtale.commRingStructureSheaf B X hX) R₀
    (baseChangeStructureSection B hX φ) P (smallEtaleSolutionEquivBase B hX φ W P pres)
    (fun {_ _} g t i => smallEtaleSolutionEquivBase_naturality B hX φ W P pres g t i)

/-- **The representable sheaf of an affine chart is the equalizer of powers of the structure
sheaf, for the row of a system over an arbitrary base ring.**

Let `X` be an affine scheme of a big étale site, let `φ : R₀ ⟶ Γ(X, ⊤)` be a ring map, and let
`W` be an affine object of the small étale site of `X` with a standard presentation
`Γ(W, ⊤) = Γ(X, ⊤)[x₁, …, x_n]/(φP₁, …, φP_n)` of its ring of global functions over `Γ(X, ⊤)`,
the `Pⱼ` having coefficients in `R₀`.  Then `h_W` is the equalizer of the two maps
`∏ᵢ 𝒪_X ⇉ ∏ⱼ 𝒪_X` of the row of `P` with its coefficients read into `𝒪_X` through `φ`, and the
zero section.

This is the row that step (3) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6) compares `g⁻¹h_V` with: by
`Stacks.Sheaves.inverseImage_evalSystemHom_comp_fSharp` the row of `P` over `𝒪_Y`, pulled back
along `g⁻¹` and pushed along `g^♯`, is the row of `P` over `𝒪_X` with coefficients read through
the ring map `φ` that `g^♯` induces on global functions.  Taking `R₀ = Γ(Y, ⊤)` and `φ` that map,
the fork proved here is the limit fork `t` that
`Stacks.Sheaves.inverseImageForkComparison` maps into.

Étaleness of `W ⟶ X` is not used, only that `W` is affine over an affine base with a chosen
presentation of its ring; étaleness is what produces such a presentation, by
[Stacks Project, Tag 00U9].  Nor is the base change of the presentation produced here: the
presentation of `Γ(W, ⊤)` in the pushed-forward polynomials is the datum, and that it is the
right one for `W = X ×_Y V` is `MvPolynomial.homOverMapCoeffEquiv`. -/
def isLimitForkSmallEtaleYonedaBase :
    IsLimit (Fork.ofι (smallEtaleYonedaCoordinatesBase B hX φ W P pres)
      (solutionCoordinates_comp_evalSystemHom (SmallEtale.commRingStructureSheaf B X hX)
        R₀ (baseChangeStructureSection B hX φ)
        (fun {_ _} g => baseChangeStructureSection_comp_map B hX φ g) P
        (smallEtaleSolutionEquivBase B hX φ W P pres)
        (fun {_ _} g t i => smallEtaleSolutionEquivBase_naturality B hX φ W P pres g t i))) :=
  isLimitForkOfSolutionEquiv (SmallEtale.commRingStructureSheaf B X hX) R₀
    (baseChangeStructureSection B hX φ)
    (fun {_ _} g => baseChangeStructureSection_comp_map B hX φ g) P
    (smallEtaleSolutionEquivBase B hX φ W P pres)
    (fun {_ _} g t i => smallEtaleSolutionEquivBase_naturality B hX φ W P pres g t i)

end Stacks.EtaleCohomology

end
