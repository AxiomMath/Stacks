module

public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange

/-!
# The projection-formula map is compatible with a commutative square

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes, `G` an `𝒪_X`-module and `H` an `𝒪_S`-module.  The
projection-formula map of [Stacks, Tag 0FZE] and the base-change morphism of
[Stacks, Tag 02KG] fit into a hexagon

```
                             g^*(p for f)
  g^*(f_*G ⊗_{𝒪_S} H) ------------------------→ g^*f_*(G ⊗_{𝒪_X} f^*H)
         | t for g                                        | b
         v                                                v
  g^*f_*G ⊗_{𝒪_{S'}} g^*H                       f'_*(g')^*(G ⊗_{𝒪_X} f^*H)
         | b ⊗ 1                                          | f'_*(t for g')
         v                                                v
  f'_*(g')^*G ⊗_{𝒪_{S'}} g^*H                   f'_*((g')^*G ⊗_{𝒪_{X'}} (g')^*f^*H)
         | p for f'                                       | f'_*(1 ⊗ c)
         v                                                v
  f'_*((g')^*G ⊗_{𝒪_{X'}} (f')^*g^*H) ========= f'_*((g')^*G ⊗_{𝒪_{X'}} (f')^*g^*H)
```

which this file proves to commute.  The arrows marked `p` are the projection-formula map, those
marked `t` the comparison of [Stacks, Tag 01CD] of an inverse image with a tensor product, those
marked `b` the base-change morphism, and `c` is the identification
`Stacks.Modules.pullbackSquareIso` of the two composite inverse images around the square.

This is the underived form of [Stacks, Tag 0E48], for sheaves of modules on schemes.  There is no
hypothesis beyond commutativity of the square: the square need not be cartesian, neither `f` nor
`g` carries any condition, and `G` and `H` are arbitrary.

## Main definitions

* `Stacks.RingedSpace.pullbackCompIsoLeft` and `Stacks.Modules.pullbackCompIsoLeft`: the
  identification of `g^* ∘ (f')^*` with the inverse image along the diagonal `g' ≫ f` of the
  square, for ringed spaces and for schemes.
* `Stacks.RingedSpace.squareBaseChangeMap`: the base-change morphism of the square, as the mate
  of that identification and of the composition law along the other side.

## Main results

* `Stacks.RingedSpace.comparisonNatTrans_comp`: the comparison of [Stacks, Tag 01CD] is
  compatible with composition, as an identity of morphisms of bifunctors.  This is
  `Stacks.PullbackTensorComposition.comparison_comp` with the two sides read as natural
  transformations.
* `Stacks.RingedSpace.comparisonCompatibleWithSquare` and
  `Stacks.RingedSpace.tensorComparisonCompatible`: **the coherence of the four comparisons of
  [Stacks, Tag 01CD] around the square** with the identification of the two composite inverse
  images, in the two shapes the abstract chase is stated at.  This is its one input, and the
  composition law discharges it.
* `Stacks.RingedSpace.projectionFormulaMap_baseChange`: **the hexagon**, for a commutative square
  of ringed spaces.
* `Stacks.Modules.pullbackSquareIso_eq` and `Stacks.Modules.map_eq_baseChangeNatTrans`: the
  abstract base-change map `Stacks.CategoryTheory.BaseChange.map` of the two vertical adjunctions
  is the base-change morphism
  `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of [Stacks, Tag 02KG], with
  `Stacks.Modules.squareBaseChangeMap_eq_baseChangeNatTrans` the same at the
  `SheafOfModules (structureSheafRing _)` spelling the hexagon is stated at.

## Implementation notes

*The diagram chase.*  It is
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, carried out over
arbitrary categories, adjunctions and bifunctors for `CategoryTheory.adjunctionTensorMap` and
`Stacks.CategoryTheory.BaseChange.map`; the projection-formula map
`Stacks.AffineProjectionFormula.projectionFormulaMap` is by definition the first of those at the
pullback--pushforward adjunction and the comparison of [Stacks, Tag 01CD], and
`map_eq_baseChangeNatTrans` below identifies the second with the base-change morphism.  What this
file supplies is the chase's single hypothesis.

*Why the coherence is available here and not for ringed topoi.*  The hypothesis is
`Stacks.AffineProjectionFormula.TensorComparisonCompatible`: the comparison along a composite is
the composite of the comparisons, for the two ways around the square.  For sheaves of modules on
ringed spaces the composition law is a theorem,
`Stacks.PullbackTensorComposition.comparison_comp`, so the generic assembly
`Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws`
applies with no hypothesis left over.  The same assembly is what
`Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square` performs
for the derived comparison of [Stacks, Tag 079U]; the ringed-topos statement of [Stacks, Tag 0E48]
carries the coherence as a hypothesis, there being no composition law for [Stacks, Tag 07A4].

*The two descriptions of the base-change morphism.*
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is the mate of the direct-image
square isomorphism along the *horizontal* adjunctions, whereas
`Stacks.CategoryTheory.BaseChange.map` is the mate of the inverse-image square isomorphism along
the *vertical* ones.  `Stacks.Modules.eq_baseChangeNatTrans_app` says the base-change morphism is
the unique morphism with the latter's adjoint transpose, and
`Stacks.CategoryTheory.BaseChange.homEquiv_symm_map` computes that transpose, so the two agree.
By `Stacks.Modules.pullbackSquareIso_eq`, `Stacks.Modules.pullbackSquareIso` is the
`Stacks.AffineProjectionFormula.squareCompositeIso` of `Stacks.Modules.pullbackCompIsoLeft` and
`Scheme.Modules.pullbackComp g' f`.

*No `@[stacks]` attribute.*  [Stacks, Tag 0E48] is Remark 21.19.6 for ringed topoi and the
derived projection-formula map; what is proved here is its underived form for sheaves of modules
on schemes, which is not a separate assertion of the source.  [Stacks, Tag 0FZE] is the
invertibility of the projection-formula map, proved for affine morphisms and quasi-coherent
modules as `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap`.

## References

* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.Prod
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RingedSpace

/-- **The comparison of [Stacks, Tag 01CD] is compatible with composition**, as an identity of
morphisms of bifunctors: the composition law for the inverse image, followed by the comparison
for `f ≫ g`, is the inverse image along `f` of the comparison for `g`, followed by the comparison
for `f` and the composition law in each tensor factor. -/
theorem comparisonNatTrans_comp {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerLeft
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩)))
          (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom ≫
        comparisonNatTrans (f ≫ g) =
      Functor.whiskerRight (comparisonNatTrans g) (pullbackFunctor f) ≫
        Functor.whiskerLeft ((pullbackFunctor g).prod (pullbackFunctor g))
            (comparisonNatTrans f) ≫
          Functor.whiskerRight
            (NatTrans.prod (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom
              (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom)
            ((Functor.uncurry.obj
              (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))) := by
  refine NatTrans.ext (funext fun P => ?_)
  exact Stacks.PullbackTensorComposition.comparison_comp f g P.1 P.2

/-! ### The coherence of the four comparisons around a square -/

section Square

variable {X' X S' S : AlgebraicGeometry.RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

/-- The identification of the composite inverse image `g^* ∘ (f')^*` with the inverse image along
the diagonal of the square, written as the composite of the inverse images along `f' ≫ g`.  The
transport along the commutativity of the square is what makes it an identification with the
*other* composite's target. -/
def pullbackCompIsoLeft (w : g' ≫ f = f' ≫ g) :
    pullbackFunctor g ⋙ pullbackFunctor f' ≅ pullbackFunctor (g' ≫ f) :=
  Stacks.DerivedPullback.Composition.modulePullbackComp f' g ≪≫
    eqToIso (congrArg pullbackFunctor w.symm)

/-- **The comparison of [Stacks, Tag 01CD] is coherent around a commutative square of ringed
spaces.**  Both composites of inverse images around the square are identified with the inverse
image along the common composite, hence with each other, and each carries the composite of the
comparisons along its two factors; this says that the identification carries the one composite
comparison to the other.

It is the single hypothesis of
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, and here it is a theorem:
the composition law `Stacks.RingedSpace.comparisonNatTrans_comp` for the two factorizations of
the common composite discharges it. -/
theorem comparisonCompatibleWithSquare (w : g' ≫ f = f' ≫ g) :
    Stacks.Cohomology.DerivedRelativeCupProduct.ComparisonCompatibleWithSquare
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S)).presheaf, ((S)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S')).presheaf, ((S')).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)))
      (comparisonNatTrans g) (comparisonNatTrans f') (comparisonNatTrans f)
      (comparisonNatTrans g') (pullbackCompIsoLeft g' f' f g w)
      (Stacks.DerivedPullback.Composition.modulePullbackComp g' f) :=
  Stacks.Cohomology.DerivedRelativeCupProduct.comparisonCompatibleWithSquare_of_composition_laws
    _ _ _ _
    (comparisonNatTrans g) (comparisonNatTrans f') (comparisonNatTrans f)
    (comparisonNatTrans g') (fun h : X' ⟶ S => pullbackFunctor h)
    (fun h => comparisonNatTrans h) w.symm
    (Stacks.DerivedPullback.Composition.modulePullbackComp f' g)
    (Stacks.DerivedPullback.Composition.modulePullbackComp g' f)
    (pullbackCompIsoLeft g' f' f g w) rfl
    (comparisonNatTrans_comp f' g) (comparisonNatTrans_comp g' f)

/-- **The coherence at the shape the abstract diagram chase consumes.** -/
theorem tensorComparisonCompatible (w : g' ≫ f = f' ≫ g)
    (M N : SheafOfModules.{u} (structureRingSheaf S)) :
    Stacks.AffineProjectionFormula.TensorComparisonCompatible
      (pullbackCompIsoLeft g' f' f g w)
      (Stacks.DerivedPullback.Composition.modulePullbackComp g' f)
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S)).presheaf, ((S)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S')).presheaf, ((S')).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)))
      (comparisonNatTrans f) (comparisonNatTrans f') (comparisonNatTrans g)
      (comparisonNatTrans g') M N :=
  Stacks.Cohomology.DerivedProjectionFormula.tensorComparisonCompatible_of_comparisonSquare
    _ _ _ _
    (comparisonNatTrans g) (comparisonNatTrans f') (comparisonNatTrans f)
    (comparisonNatTrans g') (comparisonCompatibleWithSquare g' f' f g w) M N

/-! ### The hexagon for ringed spaces -/

/-- The base-change morphism of the square, as the mate of `pullbackCompIsoLeft` and the
composition law along the other side under the two vertical adjunctions. -/
def squareBaseChangeMap (w : g' ≫ f = f' ≫ g)
    (E : SheafOfModules.{u} (structureRingSheaf X)) :
    (pullbackFunctor g).obj ((pushforwardFunctor f).obj E) ⟶
      (pushforwardFunctor f').obj ((pullbackFunctor g').obj E) :=
  Stacks.CategoryTheory.BaseChange.map (pullbackAdjunction f) (pullbackAdjunction f')
    (pullbackCompIsoLeft g' f' f g w)
    (Stacks.DerivedPullback.Composition.modulePullbackComp g' f) E

/-- **The projection-formula map is compatible with a commutative square of ringed spaces.**  The
hexagon of the module docstring commutes: the comparison of [Stacks, Tag 01CD] along `g`, the
base-change morphism in the first tensor factor and the projection-formula map for `f'` compose
to the inverse image along `g` of the projection-formula map for `f`, the base-change morphism at
the tensor product and the direct image of the comparison along `g'` together with the
identification of the two composite inverse images.

This is the underived form of [Stacks, Tag 0E48].  Nothing is assumed beyond commutativity of the
square: `E` and `K` are arbitrary, and neither `f` nor `g` carries a condition. -/
theorem projectionFormulaMap_baseChange (w : g' ≫ f = f' ≫ g)
    (E : SheafOfModules.{u} (structureRingSheaf X))
    (K : SheafOfModules.{u} (structureRingSheaf S)) :
    Stacks.Cohomology.DerivedProjectionFormula.ProjectionFormulaBaseChangeSquare
      (pushforwardFunctor f) (pushforwardFunctor f') (pullbackFunctor f) (pullbackFunctor f')
      (pullbackFunctor g) (pullbackFunctor g')
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S)).presheaf, ((S)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S')).presheaf, ((S')).IsSheaf⟩)))
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X')).presheaf, ((X')).IsSheaf⟩)))
      (comparisonNatTrans g) (comparisonNatTrans g') E K
      (Stacks.AffineProjectionFormula.projectionFormulaMap f E K)
      (squareBaseChangeMap g' f' f g w
        (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩))).obj
          (E, (pullbackFunctor f).obj K)))
      (squareBaseChangeMap g' f' f g w E)
      ((Stacks.AffineProjectionFormula.squareCompositeIso (pullbackCompIsoLeft g' f' f g w)
        (Stacks.DerivedPullback.Composition.modulePullbackComp g' f)).inv.app K)
      (Stacks.AffineProjectionFormula.projectionFormulaMap f' ((pullbackFunctor g').obj E)
        ((pullbackFunctor g).obj K)) :=
  Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square (pullbackAdjunction f)
    (pullbackAdjunction f') (pullbackCompIsoLeft g' f' f g w)
    (Stacks.DerivedPullback.Composition.modulePullbackComp g' f) _ _ _ _
    (comparisonNatTrans f) (comparisonNatTrans f')
    (comparisonNatTrans g) (comparisonNatTrans g') E K
    (tensorComparisonCompatible g' f' f g w _ K)

end Square

end Stacks.RingedSpace

/-! ### The hexagon for schemes -/

namespace Stacks.Modules

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The identification of the composite inverse image `g^* ∘ (f')^*` with the inverse image along
the diagonal of the square, written as the inverse image along `g' ≫ f`. -/
def pullbackCompIsoLeft (w : g' ≫ f = f' ≫ g) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback (g' ≫ f) :=
  Scheme.Modules.pullbackComp f' g ≪≫ Scheme.Modules.pullbackCongr w.symm

/-- The two composite inverse images around the square are identified the same way by
`Stacks.Modules.pullbackSquareIso` and by
`Stacks.AffineProjectionFormula.squareCompositeIso` of the two composition laws.  Only the
bracketing differs. -/
theorem pullbackSquareIso_eq (w : g' ≫ f = f' ≫ g) :
    pullbackSquareIso f f' g g' w =
      Stacks.AffineProjectionFormula.squareCompositeIso (pullbackCompIsoLeft w)
        (Scheme.Modules.pullbackComp g' f) :=
  Iso.ext (NatTrans.ext (funext fun _ => (Category.assoc _ _ _).symm))

/-- **The abstract base-change map of the two vertical adjunctions is the base-change morphism of
[Stacks, Tag 02KG].**  Both transpose, under `(f')^* ⊣ (f')_*`, to the identification of the two
composite inverse images followed by `(g')^*` of the counit of `f^* ⊣ f_*`, and
`Stacks.Modules.eq_baseChangeNatTrans_app` says only one morphism does. -/
theorem map_eq_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (E : X.Modules) :
    Stacks.CategoryTheory.BaseChange.map (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f') (pullbackCompIsoLeft w)
        (Scheme.Modules.pullbackComp g' f) E =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app E := by
  refine eq_baseChangeNatTrans_app w E ?_
  rw [pullbackSquareIso_eq w, Stacks.AffineProjectionFormula.squareCompositeIso_hom_app,
    Category.assoc]
  exact Stacks.CategoryTheory.BaseChange.homEquiv_symm_map _ _ _ _ E

/-- A commutative square of schemes is a commutative square of the underlying morphisms of
ringed spaces. -/
theorem toShHom_comm (w : g' ≫ f = f' ≫ g) :
    g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom :=
  congrArg (fun h : X' ⟶ S => h.toLRSHom.toShHom) w

/-- **`Stacks.RingedSpace.squareBaseChangeMap` of a commutative square of schemes is the
base-change morphism of [Stacks, Tag 02KG].**  This is `map_eq_baseChangeNatTrans` read at the
`SheafOfModules (structureSheafRing _)` spelling, which is the one the hexagon
`Stacks.RingedSpace.projectionFormulaMap_baseChange` is stated at. -/
theorem squareBaseChangeMap_eq_baseChangeNatTrans (w : g' ≫ f = f' ≫ g)
    (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    Stacks.RingedSpace.squareBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
        f.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm w) E =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app E :=
  map_eq_baseChangeNatTrans w E

end Stacks.Modules

end
