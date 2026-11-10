module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquares
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# Reading the step of the filtration of Section 0FMK into the quotient

`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfStepSquares` builds
[Stacks, Section 0FMK] at the level of complexes,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f : X ⟶ Y` smooth over a base `S`, from two squares on the `k`-th step `F^kΩ^•_{X/S}` of the
filtration, each read through the projection `CategoryTheory.FilteredObject.grMapπ` onto the
graded piece. Both squares are the Leibniz rule on the step; what stands between the rule and the
squares is that **every object in them is a quotient or a subobject presented in one of several
equivalent ways**, and the Leibniz rule is about none of those presentations — it is about the
wedge product on `Ω^•_{X/S}` itself.

This file supplies the two presentations the squares need:

* the comparison of Section 0FMK **read into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**, where no
  image subobject appears. `SheafOfModules.exteriorGradedQuotientHom` is that reading for a
  generic short complex of sheaves of modules; here it is instantiated at the transitivity
  sequence of `f` and `g`, both at the source
  `⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y}` of
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` and at the source
  `f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y}` of
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`, which is the
  source Section 50.12 writes. In both shapes the target is the single quotient
  `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` rather than the graded piece inside it, so a morphism into it is
  determined by a morphism into `Ω^n_{X/S}` followed by the projection — and that is the shape the
  wedge product is written in;

* the degree-`n` term of the `k`-th step of the filtration of the *complex* `Ω^•_{X/S}`,
  **identified with the restriction of scalars of the `k`-th step of the filtration of the single
  sheaf `Ω^n_{X/S}`**. Those are two presentations of one subobject, separated by the extension by
  zero of `ComplexShape.embeddingUpNat` and by the change of rings from `𝒪_X` to
  `(f∘g)^{-1}𝒪_S`; the identification is `Stacks.DeRhamSmooth.stepXToExteriorFiltration`, and it
  is the prefix that the projection onto the graded piece accumulates when it is carried through
  `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedQuotientHom` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom`: the comparison of
  Section 0FMK read into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, at the two sources, with
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison_comp_arrow` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom_eq` relating them
  to the comparisons themselves, and
  `AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsPullbackGradedQuotientHom`, which is
  what lets a square be checked after reading it into the quotient.
* `Stacks.DeRhamSmooth.stepXToExteriorFiltration`: the degree-`n` term of the `k`-th step of the
  filtration of `Ω^•_{X/S}`, identified with the `k`-th step of the filtration of `Ω^n_{X/S}` read
  over `(f∘g)^{-1}𝒪_S`.
* `SheafOfModules.π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow_of_eq`: the last of the seven
  per-step compatibilities of `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` with the
  projection, **with the two steps of the filtration named by equations rather than written as
  images** — which is the shape the de Rham instance meets them in, and the shape in which the
  prefix collapses to the inclusion `F^kΩ^n_{X/S} ⟶ Ω^n_{X/S}`.

## Implementation notes

Both monomorphy facts are earned at generic objects and not by instance search at the de Rham
binders: `Stacks.CategoryTheory.mono_comp_of_isIso` is the same device as
`Stacks.CategoryTheory.epi_isoHom_comp` of
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonSource`, and the last two factors of
`Stacks.DeRhamSmooth.stepXToExteriorFiltration` are
`Stacks.GradedPieceImage.mapSubobjectsObjIso`, whose own docstring records that the monomorphy of
`U.map P.arrow` is found over an abstract category and not at these binders. Written out inline
here, that instance is not found.

## References

* [Stacks, Section 0FMK]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.CategoryTheory

/-- **A monomorphism precomposed with an isomorphism is a monomorphism.** Stated at generic
objects, with both properties explicit hypotheses rather than instances: at the concrete objects
of the wedge filtration two definitionally equal category instances are in scope, and there
instance search does not find `Mono c` for an invertible `c`. This is the same device as
`Stacks.CategoryTheory.epi_isoHom_comp` and `Stacks.CategoryTheory.mono_comp_of_mono`. -/
theorem mono_comp_of_isIso {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q R : C₁}
    (c : P ⟶ Q) (d : Q ⟶ R) (hc : IsIso c) (hd : Mono d) : Mono (c ≫ d) :=
  have := hc
  have := hd
  have : Mono c := inferInstance
  mono_comp c d

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The comparison of [Stacks, Section 0FMK], read into the quotient
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**: for `f : X ⟶ Y` smooth over a base `S` and `n = k + 1 + m`,

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`.

It is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` followed by the
inclusion of the graded piece `gr^kΩ^n_{X/S}` into the quotient
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison_comp_arrow`), so no
image subobject appears in its target. That is what makes it the shape the wedge product can be
compared against: a morphism into the quotient is a morphism into `Ω^n_{X/S}` followed by the
projection, and `SheafOfModules.tensorLeftFunctor_map_extHom_comp_exteriorGradedQuotientHom` is
its defining equation in exactly those terms.

This is `SheafOfModules.exteriorGradedQuotientHom` at the transitivity sequence
`0 ⟶ f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y} ⟶ 0`, which is short exact for `f` smooth
(`AlgebraicGeometry.Scheme.Hom.shortExact_relativeDifferentialsShortComplex`).

Costs 6,700 heartbeats against the default budget of 200,000. -/
def relativeDifferentialsExteriorGradedQuotientHom [Smooth f] (k m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₁).exteriorPower k)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      cokernel (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (relativeDifferentialsShortComplex f g).f
        (𝟙 (relativeDifferentialsShortComplex f g).X₂) (k + 1) m) :=
  have hSE : (relativeDifferentialsShortComplex f g).ShortExact :=
    shortExact_relativeDifferentialsShortComplex f g
      (Stacks.Smooth.formallySmoothScheme_of_smooth f)
  _root_.SheafOfModules.exteriorGradedQuotientHom
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₃)
    (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
      (relativeDifferentialsShortComplex f g).X₂)
    hSE.exact hSE.epi_g k m

/-- **The comparison onto `gr^kΩ^n_{X/S}`, followed by the inclusion of the graded piece into
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, is the quotient reading of the comparison.** The graded piece is by
definition the image of `SheafOfModules.exteriorGradedHom` inside that quotient, so this holds on
the nose.

The two sides are one term, but reaching that takes most of the budget: the equation unfolds
both `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison`, whose body
names the short exactness of the transitivity sequence, and
`SheafOfModules.exteriorGradedQuotientHom`, and the implicit arguments it carries along are the
algebras of the de Rham complex. Costs 119,668 heartbeats against the default budget of
200,000. -/
theorem relativeDifferentialsExteriorGradedComparison_comp_arrow [Smooth f] (k m : ℕ) :
    relativeDifferentialsExteriorGradedComparison f g k m ≫
        (Subobject.arrow (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₁)
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₂)
          (relativeDifferentialsShortComplex f g).f k m))) =
      relativeDifferentialsExteriorGradedQuotientHom f g k m :=
  rfl

/-- **The comparison of [Stacks, Section 0FMK] at the source Section 50.12 writes, read into the
quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**: for `f : X ⟶ Y` smooth over a base `S` and
`n = k + 1 + m`,

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`.

It is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` followed by the
inclusion of the graded piece into the quotient, equivalently
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedQuotientHom` precomposed with the
identification of [Stacks, Tag 01CI]
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom_eq`).

Costs 8,386 heartbeats against the default budget of 200,000. -/
def relativeDifferentialsPullbackGradedQuotientHom [Smooth f] (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((Scheme.Modules.pullback f).obj (relativeDifferentialForms g (k : ℤ)),
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      cokernel (_root_.SheafOfModules.prodWedgeHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₂)
        (relativeDifferentialsShortComplex f g).f
        (𝟙 (relativeDifferentialsShortComplex f g).X₂) (k + 1) m) :=
  relativeDifferentialsPullbackGradedComparison f g k m ≫
    (Subobject.arrow (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₁)
      (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
        (relativeDifferentialsShortComplex f g).X₂)
      (relativeDifferentialsShortComplex f g).f k m)))

/-- **The quotient reading of the comparison at the pullback source is the quotient reading at the
wedge source, precomposed with [Stacks, Tag 01CI].** Both sides are
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` followed by the
inclusion of the graded piece, grouped the two ways, so associativity is the whole proof — but
seeing that the two groupings are of the same three factors unfolds the comparison at the de Rham
binders. Costs 86,553 heartbeats against the default budget of 200,000. -/
theorem relativeDifferentialsPullbackGradedQuotientHom_eq [Smooth f] (k m : ℕ) :
    relativeDifferentialsPullbackGradedQuotientHom f g k m =
      (relativeDifferentialsPullbackExteriorIso f g k m).hom ≫
        relativeDifferentialsExteriorGradedQuotientHom f g k m :=
  Category.assoc _ _ _

/-- **The quotient reading of the comparison of [Stacks, Section 0FMK] is a monomorphism**, for
`f` smooth. The comparison itself is then an isomorphism
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison`) and the
inclusion of the graded piece into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` is the inclusion of a subobject.

This is what lets a square against the differentials be checked *after* reading it into the
quotient, where the wedge product is written: the reading loses nothing.

Costs 4,485 heartbeats against the default budget of 200,000. -/
theorem mono_relativeDifferentialsPullbackGradedQuotientHom [Smooth f] (k m : ℕ) :
    Mono (relativeDifferentialsPullbackGradedQuotientHom f g k m) :=
  Stacks.CategoryTheory.mono_comp_of_isIso _ _
    (isIso_relativeDifferentialsPullbackGradedComparison f g k m) (Subobject.arrow_mono _)

end AlgebraicGeometry.Scheme.Hom

namespace SheafOfModules

open MonoidalCategory

attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-! The wedge-product morphisms below go out of objects `Stacks.SheafOfModules.Tensor.sheafTensor`
builds, indexed by `Stacks.SheafOfModules.Tensor.ringSheaf`, while the abelian structure their
images are taken in is indexed by `CategoryTheory.Sheaf.toRingCat`. Making `ringSheaf` reducible
for implicit-argument unification identifies the two spellings, so that `HasImage` is found. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {F H : _root_.SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)

/-- **The graded piece of the wedge filtration, reached from the quotient of two steps named by
equations, reads into `⋀ⁿH/F^{k+1}⋀ⁿH` as the inclusion of the larger step**: for `W ≤ N` two
subobjects of `⋀ⁿH`, `n = k + 1 + m`, that are *equal* to the two steps `F^{k+1}⋀ⁿH ≤ F^k⋀ⁿH`,

`π ≫ (N/W ≅ F^k⋀ⁿH/F^{k+1}⋀ⁿH ≅ gr^k⋀ⁿH ⊆ ⋀ⁿH/F^{k+1}⋀ⁿH)  =  (N ⊆ ⋀ⁿH) ≫ π`.

`SheafOfModules.π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow` is this with the two steps
written as the images that cut them out; here they are reached through
`Stacks.GradedPieceImage.cokernelOfLEIsoOfEq'`, and the inclusion of the larger step into the
larger image, which that identification contributes, is absorbed by
`CategoryTheory.Subobject.ofLE_arrow`. **That absorption is the point**: it is why the whole
seven-step chain of `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded`, read through the
projection and into the quotient, leaves behind nothing but the inclusion of the step and the
projection out of it — no image subobject and no graded piece.

Nothing is assumed of the morphism `iF`; this is a statement about the wedge filtration of
`⋀ⁿH` and not about any splitting.

Costs 9,834 heartbeats against the default budget of 200,000. -/
theorem π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow_of_eq (iF : F ⟶ H) (k m : ℕ)
    {P Q : Subobject (A.exteriorPower (k + 1 + m))} (h : P ≤ Q)
    (hW : P = imageSubobject (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m))
    (hN : Q = imageSubobject (prodWedgeHom AF A A iF (𝟙 H) k (1 + m) ≫
      eqToHom (congrArg A.exterior.piece (add_assoc (k : ℤ) (1 : ℤ) (m : ℤ)).symm))) :
    cokernel.π (Subobject.ofLE P Q h) ≫
        (Stacks.GradedPieceImage.cokernelOfLEIsoOfEq' h
            (imageSubobject_prodWedgeHom_succ_le AF A iF k m) hW hN).hom ≫
          (cokernelOfLEIsoExteriorGraded AF A iF k m).hom ≫
            (imageSubobject (exteriorGradedHom AF A iF k m)).arrow =
      Q.arrow ≫ cokernel.π (prodWedgeHom AF A A iF (𝟙 H) (k + 1) m) := by
  refine Eq.trans (Stacks.GradedPieceImage.π_cokernelOfLEIsoOfEq'_hom_assoc ..) ?_
  refine Eq.trans (whisker_eq _
    (_root_.SheafOfModules.π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow AF A iF k m)) ?_
  exact Subobject.ofLE_arrow_assoc _ _

end SheafOfModules

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

/-! The derived-category and abelian structures, pinned rather than restated exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceDegreewise`: resolving them at the
concrete inverse-image ringed space exceeds the default instance-synthesis budget. -/
attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degree-`n` term of the `k`-th step of the filtration of `Ω^•_{X/S}` by the forms pulled
back from `Y`, identified with the `k`-th step of the filtration of the single sheaf `Ω^n_{X/S}`
read over `(f∘g)^{-1}𝒪_S`**, for `n = k + 1 + m`:

`(F^kΩ^•_{X/S})^n  ⟶  F^kΩ^n_{X/S}`.

These are two presentations of one subobject of `Ω^n_{X/S}`, and the four factors are the four
things that separate them: the degree-`n` term of a step of the filtered complex is presented as
a `CategoryTheory.Subobject.mk`, `Stacks.DeRhamSmooth.mk_ι_app_f_eq` identifies that subobject
with the sheaf-level step pushed along the extension by zero and the change of rings,
`CategoryTheory.Subobject.mapObjIso` strips the extension by zero and
`Stacks.GradedPieceImage.mapSubobjectsObjIso` strips the change of rings.

Nothing is assumed of `f`: this is a comparison of presentations, not an identification of graded
pieces. It is the prefix that the projection onto the graded piece accumulates when it is carried
through the seven steps of `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded`, none of which
touches the wedge product.

Costs 9,264 heartbeats against the default budget of 200,000. -/
def stepXToExteriorFiltration (k m : ℕ) :
    ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).X ((k + 1 + m : ℕ) : ℤ) ⟶
      (_root_.SheafOfModules.restrictScalars.{u}
        (AlgebraicGeometry.SheafOfModules.underlyingRingHom
          (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).obj
        (_root_.CategoryTheory.Subobject.underlying.obj
          (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k)) :=
  haveI := Stacks.GradedPieceImage.mono_iso_inv
    ((AlgebraicGeometry.SheafOfModules.deRhamComplex
        (Scheme.Hom.deRhamAlgebras (f ≫ g))
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
      ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl)
  (Subobject.underlyingIso
      (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f
        ((k + 1 + m : ℕ) : ℤ))).inv ≫
    Subobject.ofLE _ _ (mk_ι_app_f_eq f g k (k + 1 + m) (by omega)).le ≫
      (_root_.CategoryTheory.Subobject.mapObjIso
          ((AlgebraicGeometry.SheafOfModules.deRhamComplex
              (Scheme.Hom.deRhamAlgebras (f ≫ g))
              (AlgebraicGeometry.SheafOfModules.deRhamDifferential
                (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
            ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl).inv
          ((AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction
              (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + 1 + m)).obj
            (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k))).hom ≫
        (Stacks.GradedPieceImage.mapSubobjectsObjIso
          (_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHom
              (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
          (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k)).hom

end Stacks.DeRhamSmooth

end
