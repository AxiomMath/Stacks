module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemBaseRing

/-!
# The representable sheaf of an affine chart, as an equalizer of powers of the structure sheaf

Let `Y = Spec B` be an affine scheme of a big étale site and let `V` be an affine scheme étale
over `Y` with a standard presentation `Γ(V, ⊤) = B[x₁, …, x_n]/(P₁, …, P_n)`.  This file proves
**step (2) of the proof of [Stacks Project, Tag 04I6]**: the representable sheaf
`h_V = AlgebraicGeometry.smallEtaleYoneda.obj V` on the small étale site of `Y` is the equalizer
of the two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` given by the polynomials `Pⱼ` and by the zero section.

On sections over an étale chart `U` of `Y` the identification is
`Stacks.EtaleCohomology.homOverEquivSolutions`, natural in `U` by
`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`.  The passage from that sectionwise
identification to a limit in the category of sheaves is
`Stacks.Sheaves.PolynomialSystem.isLimitForkOfSolutionEquiv`, whose row is the internal
polynomial system of the commutative ring object carried by `𝒪_Y`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.homEquivSchemeHomOver`: a morphism of the small étale site is a
  morphism of the underlying schemes over `Y`.
* `AlgebraicGeometry.SmallEtale.structureBaseSection`: the structure map `Γ(Y, ⊤) ⟶ Γ(U, ⊤)` of a
  chart, exhibiting the structure sheaf as a sheaf of `Γ(Y, ⊤)`-algebras.
* `Stacks.EtaleCohomology.smallEtaleSolutionEquiv`: the sections of `h_V` over a chart are the
  solutions of the presented system.
* `Stacks.EtaleCohomology.smallEtaleYonedaCoordinates`: the resulting morphism
  `h_V ⟶ ∏ᵢ 𝒪_Y`.

## Main results

* `Stacks.EtaleCohomology.isLimitForkSmallEtaleYoneda`: **`h_V` is the equalizer of
  `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y`.**

## Implementation notes

The presentation of `Γ(V, ⊤)` is taken as the datum
`Stacks.EtaleCohomology.StandardPresentationOver`; producing it from étaleness is
[Stacks Project, Tag 00U9].

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CommRingObj Obj

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)

/-! ### A morphism of the small étale site is a morphism of schemes over `Y` -/

/-- **The triangle of the slice, on underlying schemes**: a morphism of the small étale site
commutes with the structure morphisms to `Y`. -/
theorem SmallEtale.toScheme_map_comp_structureHom {U U' : SmallEtale B Y hY} (g : U' ⟶ U) :
    (SmallEtale.toScheme B Y hY).map g ≫ B.inclusion.map U.obj.hom =
      B.inclusion.map U'.obj.hom :=
  ((B.inclusion.map_comp _ _).symm).trans
    (congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B Y hY).map g)))

/-- **A morphism of the small étale site of `Y` is a morphism of the underlying schemes
commuting with the structure morphisms to `Y`.**  Both steps are full subcategory inclusions —
of the étale objects into the slice, and of the size-bounded schemes into all schemes — so the
hom-sets agree. -/
def SmallEtale.homEquivSchemeHomOver (U V : SmallEtale B Y hY) :
    (U ⟶ V) ≃ {f : (SmallEtale.toScheme B Y hY).obj U ⟶ (SmallEtale.toScheme B Y hY).obj V //
      f ≫ B.inclusion.map V.obj.hom = B.inclusion.map U.obj.hom} where
  toFun g := ⟨(SmallEtale.toScheme B Y hY).map g,
    SmallEtale.toScheme_map_comp_structureHom B Y hY g⟩
  invFun f := ObjectProperty.homMk
    (Over.homMk ((ObjectProperty.fullyFaithfulι _).preimage f.1)
      ((ObjectProperty.fullyFaithfulι _).map_injective
        ((B.inclusion.map_comp _ _).trans
          ((congrArg (fun m => m ≫ B.inclusion.map V.obj.hom)
            ((ObjectProperty.fullyFaithfulι _).map_preimage f.1)).trans f.2))))
  left_inv g := by
    refine (ObjectProperty.fullyFaithfulι _).map_injective (Over.OverMorphism.ext ?_)
    exact (ObjectProperty.fullyFaithfulι _).preimage_map _
  right_inv f := Subtype.ext ((ObjectProperty.fullyFaithfulι _).map_preimage f.1)

/-- The scheme morphism underlying `SmallEtale.homEquivSchemeHomOver B Y hY U V g` is the image
of `g` under `SmallEtale.toScheme B Y hY`. -/
@[simp]
theorem SmallEtale.homEquivSchemeHomOver_apply_coe (U V : SmallEtale B Y hY) (g : U ⟶ V) :
    (SmallEtale.homEquivSchemeHomOver B Y hY U V g).1 = (SmallEtale.toScheme B Y hY).map g :=
  rfl

/-! ### The structure sheaf is a sheaf of `Γ(Y, ⊤)`-algebras -/

/-- The structure map of a chart on global functions: `Γ(Y, ⊤) ⟶ Γ(U, ⊤)`. -/
abbrev SmallEtale.structureBaseSection (X : (SmallEtale B Y hY)ᵒᵖ) :
    Γ(Y, ⊤) ⟶ (SmallEtale.commRingStructureSheaf B Y hY).obj.obj X :=
  (B.inclusion.map X.unop.obj.hom).appTop

/-- **The structure maps of the charts are compatible with restriction**, so the structure sheaf
of the small étale site of `Y` is a sheaf of `Γ(Y, ⊤)`-algebras.  This is the triangle of the
slice `Over Y`, read on global functions. -/
theorem SmallEtale.structureBaseSection_comp_map {X X' : (SmallEtale B Y hY)ᵒᵖ} (g : X ⟶ X') :
    SmallEtale.structureBaseSection B Y hY X ≫
        (SmallEtale.commRingStructureSheaf B Y hY).obj.map g =
      SmallEtale.structureBaseSection B Y hY X' := by
  show (B.inclusion.map X.unop.obj.hom).appTop ≫
      ((SmallEtale.toScheme B Y hY).map g.unop).appTop = _
  rw [← Scheme.Hom.comp_appTop]
  refine congrArg Scheme.Hom.appTop ?_
  exact SmallEtale.toScheme_map_comp_structureHom B Y hY g.unop

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry Stacks.Sheaves.PolynomialSystem

attribute [local instance] Stacks.sheafCommRingObj

variable (B : BigEtaleSite.{u}) {Y : Scheme.{u}} (hY : B.Contains Y) [IsAffine Y]
  (V : SmallEtale B Y hY) [IsAffine ((SmallEtale.toScheme B Y hY).obj V)] {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤))
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
    (B.inclusion.map V.obj.hom) P)

/-- `Y`, read as an object of the big étale site and back, is affine.  The spelling matters:
`AlgebraicGeometry.SmallEtale.homEquivSchemeHomOver` produces structure morphisms with codomain
`B.inclusion.obj (B.obj Y hY)`, and the affineness hypothesis of
`Stacks.EtaleCohomology.homOverEquivSolutions` has to be found at that spelling. -/
local instance isAffine_inclusion_obj_base : IsAffine (B.inclusion.obj (B.obj Y hY)) :=
  inferInstanceAs (IsAffine Y)

/-- **The sections of `h_V` over a chart are the solutions of the presented system.**  This is
`Stacks.EtaleCohomology.homOverEquivSolutions` read on the small étale site, the morphisms of the
site translated into morphisms of schemes over `Y` by
`AlgebraicGeometry.SmallEtale.homEquivSchemeHomOver`. -/
def smallEtaleSolutionEquiv (X : (SmallEtale B Y hY)ᵒᵖ) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B Y hY) X).obj
        ((smallEtaleYoneda B Y hY).obj V) ≃
      {b : Fin n → (SmallEtale.commRingStructureSheaf B Y hY).obj.obj X //
        MvPolynomial.IsSolution P
          (SmallEtale.structureBaseSection B Y hY X).hom b} :=
  (SmallEtale.homEquivSchemeHomOver B Y hY X.unop V).trans
    (homOverEquivSolutions ((SmallEtale.toScheme B Y hY).obj X.unop)
      ((SmallEtale.toScheme B Y hY).obj V) (B.inclusion.map V.obj.hom)
      (B.inclusion.map X.unop.obj.hom) P pres)

/-- The `i`-th coordinate of the solution attached to a section `t` of `h_V` over `X` is the
image of the class of the variable `xᵢ` under the map on global functions induced by `t`, through
the presentation `pres`. -/
theorem smallEtaleSolutionEquiv_apply_coe (X : (SmallEtale B Y hY)ᵒᵖ)
    (t : (Sheaf.sectionsFunctor (SmallEtale.topology B Y hY) X).obj
      ((smallEtaleYoneda B Y hY).obj V)) (i : Fin n) :
    (smallEtaleSolutionEquiv B hY V P pres X t).1 i =
      (pres.iso.inv ≫ ((SmallEtale.toScheme B Y hY).map t).appTop).hom
        (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i)) :=
  homOverEquivSolutions_apply_coe _ _ _ _ P pres _ i

/-- **The identification is natural in the chart**, which is what makes it a presentation of the
*sheaf* `h_V` and not merely of its sections over one chart.  It is
`Stacks.EtaleCohomology.homOverEquivSolutions_naturality`. -/
theorem smallEtaleSolutionEquiv_naturality {X X' : (SmallEtale B Y hY)ᵒᵖ} (g : X ⟶ X')
    (t : (Sheaf.sectionsFunctor (SmallEtale.topology B Y hY) X).obj
      ((smallEtaleYoneda B Y hY).obj V)) (i : Fin n) :
    ((SmallEtale.commRingStructureSheaf B Y hY).obj.map g).hom
        ((smallEtaleSolutionEquiv B hY V P pres X t).1 i) =
      (smallEtaleSolutionEquiv B hY V P pres X'
        (((smallEtaleYoneda B Y hY).obj V).obj.map g t)).1 i := by
  have h : (SmallEtale.toScheme B Y hY).map
        (((smallEtaleYoneda B Y hY).obj V).obj.map g t) =
      (SmallEtale.toScheme B Y hY).map g.unop ≫ (SmallEtale.toScheme B Y hY).map t :=
    (SmallEtale.toScheme B Y hY).map_comp _ _
  rw [smallEtaleSolutionEquiv_apply_coe B hY V P pres X t i,
    smallEtaleSolutionEquiv_apply_coe B hY V P pres X'
      (((smallEtaleYoneda B Y hY).obj V).obj.map g t) i,
    h, Scheme.Hom.comp_appTop, ← Category.assoc]
  rfl

/-- The morphism `h_V ⟶ ∏ᵢ 𝒪_Y` sending a `Y`-morphism `U ⟶ V` to the solution it names. -/
def smallEtaleYonedaCoordinates :
    (smallEtaleYoneda B Y hY).obj V ⟶
      ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY)
        (SmallEtale.commRingStructureSheaf B Y hY) :=
  solutionCoordinates (SmallEtale.commRingStructureSheaf B Y hY) Γ(Y, ⊤)
    (SmallEtale.structureBaseSection B Y hY) P (smallEtaleSolutionEquiv B hY V P pres)
    (fun {_ _} g t i => smallEtaleSolutionEquiv_naturality B hY V P pres g t i)

/-- **Step (2) of the proof of [Stacks Project, Tag 04I6]: the representable sheaf of an affine
chart is an equalizer of powers of the structure sheaf.**

Let `Y` be an affine scheme of a big étale site and let `V` be an affine object of its small
étale site with a standard presentation `Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, x_n]/(P₁, …, P_n)` of its ring
of global functions over `Γ(Y, ⊤)`.  Then the representable sheaf `h_V` on the small étale site
of `Y` is the equalizer of the two maps `∏ᵢ 𝒪_Y ⇉ ∏ⱼ 𝒪_Y` given by evaluating the `Pⱼ` and by
the zero section.

Étaleness of `V ⟶ Y` is not used: what is used is that `V` is affine over an affine base with a
chosen presentation of its ring.  Étaleness is what produces such a presentation, by
[Stacks Project, Tag 00U9]. -/
def isLimitForkSmallEtaleYoneda :
    IsLimit (Fork.ofι (smallEtaleYonedaCoordinates B hY V P pres)
      (solutionCoordinates_comp_evalSystemHom (SmallEtale.commRingStructureSheaf B Y hY)
        Γ(Y, ⊤) (SmallEtale.structureBaseSection B Y hY)
        (fun {_ _} g => SmallEtale.structureBaseSection_comp_map B Y hY g) P
        (smallEtaleSolutionEquiv B hY V P pres)
        (fun {_ _} g t i => smallEtaleSolutionEquiv_naturality B hY V P pres g t i))) :=
  isLimitForkOfSolutionEquiv (SmallEtale.commRingStructureSheaf B Y hY) Γ(Y, ⊤)
    (SmallEtale.structureBaseSection B Y hY)
    (fun {_ _} g => SmallEtale.structureBaseSection_comp_map B Y hY g) P
    (smallEtaleSolutionEquiv B hY V P pres)
    (fun {_ _} g t i => smallEtaleSolutionEquiv_naturality B hY V P pres g t i)

end Stacks.EtaleCohomology

end
