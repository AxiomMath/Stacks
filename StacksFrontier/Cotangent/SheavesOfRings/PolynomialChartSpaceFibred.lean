module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialChartSpace

/-!
# Polynomial charts of an algebraic space form a fibred category

For an algebraic space `X` over a ring `Λ`, the category `C_{X/Λ}` of polynomial charts of `X`
is fibred over the small étale site of `X`. A chart `(U ⟶ A)` is pulled back along an arrow
`V ⟶ U` of the small étale site by composing its arrow to the affine space with the induced map
of schemes and keeping the same affine space.

## Main results

* `AlgebraicGeometry.Space.PolynomialChart.openFunctor_isFibered`: the forgetful functor from
  polynomial charts of `X` to the small étale site of `X` is fibred.

## Implementation notes

Unlike the Zariski category of open subschemes used for a scheme (Stacks 08V9), the small étale
site of an algebraic space does not have subsingleton hom-sets, so the arrow `V ⟶ U` carries
information and the universal property of a cartesian arrow has to produce both components of
the morphism of charts. The arrow over `X` is forced by `CategoryTheory.IsHomLift`, and the
arrow between the affine spaces is the one already given, because the pullback chart has the
same affine space.

## References

* [Stacks Project, Tag 08VJ](https://stacks.math.columbia.edu/tag/08VJ)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Space.PolynomialChart

noncomputable section

variable {Λ : Type u} [CommRing Λ] {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (CommRingCat.of Λ))}
  {X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u}
  {hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X}

/-- The pullback of a polynomial chart along an arrow of the small étale site of `X`: the same
affine space, with the chart map precomposed with the induced morphism of schemes. -/
private def restrict (P : PolynomialChart Λ B hS X hX)
    (R : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (f : R ⟶ P.openPart) :
    PolynomialChart Λ B hS X hX where
  openPart := R
  variableIndex := P.variableIndex
  affineSpace := P.affineSpace
  affineEquiv := P.affineEquiv
  toAffine := (smallEtaleToScheme Λ B hS X).map f ≫ P.toAffine
  comm := by
    rw [Category.assoc, P.comm]
    let toOver := SmallEtale.toOver B (Spec (CommRingCat.of Λ)) hS X
    change B.inclusion.map ((toOver.map f).left ≫ (toOver.obj P.openPart).hom) =
      B.inclusion.map (toOver.obj R).hom
    exact congrArg B.inclusion.map (Over.w (toOver.map f))

/-- The canonical morphism from a pullback of a polynomial chart to the chart itself; it is the
identity on affine spaces. -/
private def restrictHom (P : PolynomialChart Λ B hS X hX)
    (R : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (f : R ⟶ P.openPart) :
    Hom (restrict P R f) P where
  openMap := f
  affine := 𝟙 P.affineSpace
  map_comm := by simp [restrict]
  base_comm := Category.id_comp _

/-- The pullback morphism of a polynomial chart is strongly cartesian over the arrow of the
small étale site it lies above. -/
private theorem restrict_isStronglyCartesian (P : PolynomialChart Λ B hS X hX)
    (R : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) (f : R ⟶ P.openPart) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsStronglyCartesian f
      (restrictHom P R f) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · change openFunctor.IsHomLift (openFunctor.map (restrictHom P R f)) (restrictHom P R f)
    infer_instance
  intro T g φ hφ
  let gChart : T.openPart ⟶ R := g
  have hopen : φ.openMap = gChart ≫ f := by
    simpa [openFunctor] using
      (@IsHomLift.eq_of_isHomLift _ _ _ _ openFunctor T P (g ≫ f) φ hφ).symm
  let ψ : Hom T (restrict P R f) :=
    { openMap := gChart
      affine := φ.affine
      map_comm := by
        change T.toAffine ≫ φ.affine = (smallEtaleToScheme Λ B hS X).map gChart ≫
          ((smallEtaleToScheme Λ B hS X).map f ≫ P.toAffine)
        rw [φ.map_comm, hopen, Functor.map_comp, Category.assoc]
      base_comm := φ.base_comm }
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · change openFunctor.IsHomLift (openFunctor.map ψ) ψ
    infer_instance
  · exact Hom.ext hopen.symm (Category.comp_id φ.affine)
  · intro χ hχ
    refine Hom.ext ?_ ?_
    · have hχmap :=
        @IsHomLift.eq_of_isHomLift _ _ _ _ openFunctor T (restrict P R f) g χ hχ.1
      simpa [ψ, gChart, openFunctor] using hχmap.symm
    · have h := congrArg Hom.affine hχ.2
      exact (Category.comp_id χ.affine).symm.trans h

end

/-- **Stacks 08VJ.** The category `C_{X/Λ}` of polynomial charts of an algebraic space `X` over
`Λ` is fibred over the small étale site of `X`. -/
@[stacks 08VJ]
noncomputable instance openFunctor_isFibered (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (CommRingCat.of Λ)))
    (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X) :
    (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).IsFibered :=
  .of_exists_isStronglyCartesian fun {P R} f =>
    ⟨restrict P R f, restrictHom P R f, restrict_isStronglyCartesian P R f⟩

end AlgebraicGeometry.Space.PolynomialChart

end
