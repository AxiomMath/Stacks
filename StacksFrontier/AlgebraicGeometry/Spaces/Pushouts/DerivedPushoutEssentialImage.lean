module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.RingTheory.MilnorPatching.DerivedGlueingMap

/-!
# Pushouts along thickenings and derived categories: the statement of Stacks Tag 0DL7

Let `S` be a scheme and let
```
X  --i-->  X'
|          |
f          f'
v          v
Y  --j-->  Y'
```
be a pushout in the category of algebraic spaces over `S` as in Stacks Tag 07VX: `i` is a
thickening, `f` is affine, and `Y' = Y ⨿_X X'`. Stacks Tag 0DL7 asserts that the essential image of
the functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})`, `M' ↦ (Lj^* M', L(f')^* M', can)`, given by
derived pullback, contains every triple `(M, K', α)` with `M ∈ D(𝒪_Y)` and `K' ∈ D(𝒪_{X'})`
pseudo-coherent and `α : Lf^* M ≅ Li^* K'`. This file states it, at arbitrary models of the four
derived categories, as the proposition `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, and
reduces it to its isomorphism step `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackOfModels`,
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePushforwardOfModels` and
  `AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunctionOfModels`: `Lf^*`, `Rf_*` and
  `Lf^* ⊣ Rf_*`, read at arbitrary models of the two derived categories through the comparisons
  `StacksDraft.DerivedModel.modelEquiv` with the standard models.
* `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`: the 2-cell
  `Lf^* ∘ Lj^* ≅ Li^* ∘ L(f')^*` of the functor to the 2-fibre product: Stacks 0D6D twice
  (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) and the commutativity
  `i ≫ f' = f ≫ j` of the square;
  `AlgebraicGeometry.Space.pushoutDerivedPushforwardSquareIsoOfModels` is its conjugate
  `Rj_* Rf_* ≅ Rf'_* Ri_*`.
* `AlgebraicGeometry.Space.pushoutGlueingMapOfModels`: the map
  `Rj_* M ⊕ Rf'_* K' ⟶ Rj_* Rf_* Li^* K'` of the source's proof.
* `AlgebraicGeometry.Space.DerivedPushoutEssentialImage`: **the statement of Stacks 0DL7.**
* `AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso`: its isomorphism step.

## Main results

* `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels_hom_app_comp_eq`: the maps
  `Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` adjoint to the components of a map
  `M' ⟶ Rj_* M ⊕ Rf'_* K'` killed by the glueing map are compatible with `α`.
* `AlgebraicGeometry.Space.derivedPushoutEssentialImage_of_derivedPushoutGlueingIsIso`: Stacks 0DL7
  from its isomorphism step.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 08GH](https://stacks.math.columbia.edu/tag/08GH)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₁ w₂ w₃ w₄ w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Lf^*` at arbitrary models.** The derived pullback along a morphism `f : X ⟶ Y` of algebraic
spaces (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, defined at the standard models),
read at models `hY` of `D(𝒪_Y)` and `hX` of `D(𝒪_X)` through the comparisons with the standard
models. -/
def smallEtaleDerivedModulePullbackOfModels {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    @DerivedCategory _ _ _ hY ⥤ @DerivedCategory _ _ _ hX :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      hY).inverse ⋙
    smallEtaleDerivedModulePullback B S hS f ⋙
    (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      hX).functor

/-- **`Rf_*` at arbitrary models.** The derived direct image along a morphism `f : X ⟶ Y` of
algebraic spaces (`Stacks.Cohomology.DerivedPushforward.derivedPushforward` of the morphism of
small étale ringed topoi, defined at the standard models), read at models `hX` of `D(𝒪_X)` and
`hY` of `D(𝒪_Y)` through the comparisons with the standard models. -/
def smallEtaleDerivedModulePushforwardOfModels {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    @DerivedCategory _ _ _ hX ⥤ @DerivedCategory _ _ _ hY :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      hX).inverse ⋙
    Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f) ⋙
    (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      hY).functor

/-- **`Lf^* ⊣ Rf_*` at arbitrary models**:
`AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction` conjugated by the comparisons of
models. -/
def smallEtaleDerivedModuleAdjunctionOfModels {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hX : HasDerivedCategory.{w} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hY : HasDerivedCategory.{w'} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    smallEtaleDerivedModulePullbackOfModels B S hS f hX hY ⊣
      smallEtaleDerivedModulePushforwardOfModels B S hS f hX hY :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  (StacksDraft.DerivedModel.modelEquiv
      (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      hY).symm.toAdjunction.comp
    ((smallEtaleDerivedModuleAdjunction B S hS f).comp
      (StacksDraft.DerivedModel.modelEquiv
        (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
        hX).toAdjunction)

section Square

variable {B S hS} {X X' Y Y' : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y')
  (j : Y ⟶ Y') (w : i ≫ f' = f ≫ j)
  (hY' : HasDerivedCategory.{w₁} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
  (hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
  (hX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (hX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))

/-- **The 2-cell of the functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})`**, at arbitrary models:
for a commutative square `i ≫ f' = f ≫ j` of algebraic spaces, the natural isomorphism
`Lf^* ∘ Lj^* ≅ Li^* ∘ L(f')^*` given by Stacks 0D6D twice. -/
def pushoutDerivedPullbackSquareIsoOfModels :
    smallEtaleDerivedModulePullbackOfModels B S hS j hY hY' ⋙
        smallEtaleDerivedModulePullbackOfModels B S hS f hX hY ≅
      smallEtaleDerivedModulePullbackOfModels B S hS f' hX' hY' ⋙
        smallEtaleDerivedModulePullbackOfModels B S hS i hX hX' :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))
  let eY := StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) hY
  let eX' := StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))) hX'
  let eX := StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) hX
  let eY' := StacksDraft.DerivedModel.modelEquiv
    (HasDerivedCategory.standard (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))) hY'
  let Lj := smallEtaleDerivedModulePullback B S hS j
  let Lf := smallEtaleDerivedModulePullback B S hS f
  let Lf' := smallEtaleDerivedModulePullback B S hS f'
  let Li := smallEtaleDerivedModulePullback B S hS i
  let inner : Lj ⋙ eY.functor ⋙ eY.inverse ⋙ Lf ≅ Lf' ⋙ eX'.functor ⋙ eX'.inverse ⋙ Li :=
    Functor.isoWhiskerLeft Lj
        (Functor.isoWhiskerRight eY.unitIso.symm Lf ≪≫ Functor.leftUnitor Lf) ≪≫
      smallEtaleDerivedModulePullbackCompIso B S hS f j ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS w.symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS i f').symm ≪≫
      Functor.isoWhiskerLeft Lf'
        ((Functor.leftUnitor Li).symm ≪≫ Functor.isoWhiskerRight eX'.unitIso Li)
  Functor.isoWhiskerLeft eY'.inverse (Functor.isoWhiskerRight inner eX.functor)

/-- **The identification `Rj_* Rf_* ≅ Rf'_* Ri_*` of the proof of Stacks 0DL7**, at arbitrary
models: the conjugate of the 2-cell `Lf^* Lj^* ≅ Li^* L(f')^*` under the composite adjunctions. -/
def pushoutDerivedPushforwardSquareIsoOfModels :
    smallEtaleDerivedModulePushforwardOfModels B S hS f hX hY ⋙
        smallEtaleDerivedModulePushforwardOfModels B S hS j hY hY' ≅
      smallEtaleDerivedModulePushforwardOfModels B S hS i hX hX' ⋙
        smallEtaleDerivedModulePushforwardOfModels B S hS f' hX' hY' :=
  MilnorPatching.glueingConjugateIso (smallEtaleDerivedModuleAdjunctionOfModels B S hS f hX hY)
    (smallEtaleDerivedModuleAdjunctionOfModels B S hS i hX hX')
    (smallEtaleDerivedModuleAdjunctionOfModels B S hS j hY hY')
    (smallEtaleDerivedModuleAdjunctionOfModels B S hS f' hX' hY')
    (pushoutDerivedPullbackSquareIsoOfModels i f f' j w hY' hY hX hX')

/-- **The glueing map of the proof of Stacks 0DL7**, at arbitrary models: for `M ∈ D(𝒪_Y)`,
`K' ∈ D(𝒪_{X'})` and `α : Lf^* M ⟶ Li^* K'`, the map
`Rj_* M ⊕ Rf'_* K' ⟶ Rj_* Rf_* Li^* K'` with components `Rj_* β` (`β` adjoint to `α`) and minus
`Rf'_*` of the unit `K' ⟶ Ri_* Li^* K'` read through `Rf'_* Ri_* ≅ Rj_* Rf_*`. -/
def pushoutGlueingMapOfModels (M : @DerivedCategory _ _ _ hY) (K' : @DerivedCategory _ _ _ hX')
    (α : (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).obj M ⟶
      (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K') :
    letI := hY'
    (smallEtaleDerivedModulePushforwardOfModels B S hS j hY hY').obj M ⊞
        (smallEtaleDerivedModulePushforwardOfModels B S hS f' hX' hY').obj K' ⟶
      (smallEtaleDerivedModulePushforwardOfModels B S hS j hY hY').obj
        ((smallEtaleDerivedModulePushforwardOfModels B S hS f hX hY).obj
          ((smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K')) :=
  letI := hY'
  MilnorPatching.glueingMap (smallEtaleDerivedModuleAdjunctionOfModels B S hS f hX hY)
    (smallEtaleDerivedModuleAdjunctionOfModels B S hS i hX hX')
    (pushoutDerivedPushforwardSquareIsoOfModels i f f' j w hY' hY hX hX') M K' α

/-- **The maps `Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` of the proof of Stacks 0DL7 are compatible with
`α`.** If `u : M' ⟶ Rj_* M ⊕ Rf'_* K'` is killed by the glueing map of `(M, K', α)`, then the maps
`a : Lj^* M' ⟶ M` and `b : L(f')^* M' ⟶ K'` adjoint to its components satisfy
`σ ≫ Li^* b = Lf^* a ≫ α`, where `σ : Lf^* Lj^* M' ≅ Li^* L(f')^* M'` is the 2-cell. -/
theorem pushoutDerivedPullbackSquareIsoOfModels_hom_app_comp_eq
    (M : @DerivedCategory _ _ _ hY) (K' : @DerivedCategory _ _ _ hX')
    (α : (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).obj M ⟶
      (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K')
    {M' : @DerivedCategory _ _ _ hY'}
    (u : letI := hY'; M' ⟶ (smallEtaleDerivedModulePushforwardOfModels B S hS j hY hY').obj M ⊞
        (smallEtaleDerivedModulePushforwardOfModels B S hS f' hX' hY').obj K')
    (hu : letI := hY'; u ≫ pushoutGlueingMapOfModels i f f' j w hY' hY hX hX' M K' α = 0) :
    letI := hY'
    (pushoutDerivedPullbackSquareIsoOfModels i f f' j w hY' hY hX hX').hom.app M' ≫
        (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').map
          (((smallEtaleDerivedModuleAdjunctionOfModels B S hS f' hX' hY').homEquiv _ _).symm
            (u ≫ biprod.snd)) =
      (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).map
          (((smallEtaleDerivedModuleAdjunctionOfModels B S hS j hY hY').homEquiv _ _).symm
            (u ≫ biprod.fst)) ≫ α :=
  let := hY'
  MilnorPatching.hom_app_comp_map_homEquiv_symm_snd_eq _ _ _ _ _ α u hu

/-- **The triple `(M', a, b)` of the proof of Stacks 0DL7.** If `u : M' ⟶ Rj_* M ⊕ Rf'_* K'` is
killed by the glueing map of `(M, K', α)` and the maps `a : Lj^* M' ⟶ M` and `b : L(f')^* M' ⟶ K'`
adjoint to its components are isomorphisms, then `(M', a, b)` exhibits `(M, K', α)` in the
essential image of `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})`. -/
theorem exists_iso_of_comp_pushoutGlueingMapOfModels_eq_zero
    (M : @DerivedCategory _ _ _ hY) (K' : @DerivedCategory _ _ _ hX')
    (α : (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).obj M ≅
      (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K')
    {M' : @DerivedCategory _ _ _ hY'}
    (u : letI := hY'; M' ⟶ (smallEtaleDerivedModulePushforwardOfModels B S hS j hY hY').obj M ⊞
        (smallEtaleDerivedModulePushforwardOfModels B S hS f' hX' hY').obj K')
    (hu : letI := hY'; u ≫ pushoutGlueingMapOfModels i f f' j w hY' hY hX hX' M K' α.hom = 0)
    (ha : IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS j hY hY').homEquiv _ _).symm
      (letI := hY'; u ≫ biprod.fst)))
    (hb : IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS f' hX' hY').homEquiv _ _).symm
      (letI := hY'; u ≫ biprod.snd))) :
    ∃ (M'' : @DerivedCategory _ _ _ hY')
      (a : (smallEtaleDerivedModulePullbackOfModels B S hS j hY hY').obj M'' ≅ M)
      (b : (smallEtaleDerivedModulePullbackOfModels B S hS f' hX' hY').obj M'' ≅ K'),
      (pushoutDerivedPullbackSquareIsoOfModels i f f' j w hY' hY hX hX').hom.app M'' ≫
          (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').map b.hom =
        (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).map a.hom ≫ α.hom :=
  ⟨M', @asIso _ _ _ _ _ ha, @asIso _ _ _ _ _ hb,
    pushoutDerivedPullbackSquareIsoOfModels_hom_app_comp_eq i f f' j w hY' hY hX hX' M K' α.hom u
      hu⟩

end Square

/-- **Stacks 0DL7.** Let `S` be a scheme, and let `Y' = Y ⨿_X X'` be the pushout of a thickening
`i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`, as in Stacks 07VX,
with `j : Y ⟶ Y'` and `f' : X' ⟶ Y'`. Then, for any models of the derived categories, the
essential image of the functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` given by derived pullback
contains every triple `(M, K', α)` with `M ∈ D(𝒪_Y)` and `K' ∈ D(𝒪_{X'})` pseudo-coherent and
`α : Lf^* M ≅ Li^* K'`: there are `M' ∈ D(𝒪_{Y'})` and isomorphisms `a : Lj^* M' ≅ M` and
`b : L(f')^* M' ≅ K'` with `Li^* b` equal to `α ∘ Lf^* a` through the 2-cell
`Lf^* Lj^* ≅ Li^* L(f')^*`. -/
def DerivedPushoutEssentialImage : Prop :=
  ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
    IsThickeningHom B S hS i → IsAffineHom B S hS f.hom → ∀ [HasPushout i f]
    (hY' : HasDerivedCategory.{w₁}
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (pushout i f))))
    (hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (M : @DerivedCategory _ _ _ hY) (K' : @DerivedCategory _ _ _ hX'),
    (letI : HasDerivedCategory.{w₂} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) := hY;
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent M) →
    (letI : HasDerivedCategory.{w₄} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)) := hX';
      (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K') →
    ∀ α : (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).obj M ≅
        (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K',
      ∃ (M' : @DerivedCategory _ _ _ hY')
        (a : (smallEtaleDerivedModulePullbackOfModels B S hS (pushout.inr i f) hY hY').obj M' ≅ M)
        (b : (smallEtaleDerivedModulePullbackOfModels B S hS (pushout.inl i f) hX' hY').obj M' ≅
          K'),
        (pushoutDerivedPullbackSquareIsoOfModels i f (pushout.inl i f) (pushout.inr i f)
            pushout.condition hY' hY hX hX').hom.app M' ≫
            (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').map b.hom =
          (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).map a.hom ≫ α.hom


/-- **The isomorphism step of the proof of Stacks 0DL7.** In the situation of
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, for every distinguished triangle
`M' → Rj_* M ⊕ Rf'_* K' → Rj_* Rf_* Li^* K' → M'[1]` in `D(𝒪_{Y'})` whose second map is the glueing
map of `(M, K', α)` (`AlgebraicGeometry.Space.pushoutGlueingMapOfModels`), the maps
`Lj^* M' ⟶ M` and `L(f')^* M' ⟶ K'` adjoint to the two components of the first map are
isomorphisms. -/
def DerivedPushoutGlueingIsIso : Prop :=
  ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
    IsThickeningHom B S hS i → IsAffineHom B S hS f.hom → ∀ [HasPushout i f]
    (hY' : HasDerivedCategory.{w₁}
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (pushout i f))))
    (hY : HasDerivedCategory.{w₂} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hX : HasDerivedCategory.{w₃} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hX' : HasDerivedCategory.{w₄} (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (M : @DerivedCategory _ _ _ hY) (K' : @DerivedCategory _ _ _ hX'),
    (letI : HasDerivedCategory.{w₂} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) := hY;
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent M) →
    (letI : HasDerivedCategory.{w₄} (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)) := hX';
      (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K') →
    ∀ (α : (smallEtaleDerivedModulePullbackOfModels B S hS f hX hY).obj M ≅
        (smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K')
      {M' : @DerivedCategory _ _ _ hY'}
      (u : letI := hY'; M' ⟶
        (smallEtaleDerivedModulePushforwardOfModels B S hS (pushout.inr i f) hY hY').obj M ⊞
          (smallEtaleDerivedModulePushforwardOfModels B S hS (pushout.inl i f) hX' hY').obj K')
      (v : letI := hY';
        (smallEtaleDerivedModulePushforwardOfModels B S hS (pushout.inr i f) hY hY').obj
          ((smallEtaleDerivedModulePushforwardOfModels B S hS f hX hY).obj
            ((smallEtaleDerivedModulePullbackOfModels B S hS i hX hX').obj K')) ⟶ M'⟦(1 : ℤ)⟧),
      (letI := hY'; Pretriangulated.Triangle.mk u
        (pushoutGlueingMapOfModels i f (pushout.inl i f) (pushout.inr i f) pushout.condition
          hY' hY hX hX' M K' α.hom) v ∈ distTriang (@DerivedCategory _ _ _ hY')) →
      IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS (pushout.inr i f) hY hY').homEquiv
          _ _).symm (letI := hY'; u ≫ biprod.fst)) ∧
        IsIso (((smallEtaleDerivedModuleAdjunctionOfModels B S hS (pushout.inl i f) hX'
          hY').homEquiv _ _).symm (letI := hY'; u ≫ biprod.snd))

/-- **Stacks 0DL7 from its isomorphism step.** The essential image statement of Stacks 0DL7,
`AlgebraicGeometry.Space.DerivedPushoutEssentialImage`, follows from
`AlgebraicGeometry.Space.DerivedPushoutGlueingIsIso`. -/
theorem derivedPushoutEssentialImage_of_derivedPushoutGlueingIsIso
    (h : DerivedPushoutGlueingIsIso.{w₁, w₂, w₃, w₄, u} B S hS) :
    DerivedPushoutEssentialImage.{w₁, w₂, w₃, w₄, u} B S hS := by
  intro X X' Y i f hi hf _ hY' hY hX hX' M K' hM hK' α
  obtain ⟨M', u, v, hT⟩ := let := hY'; Pretriangulated.distinguished_cocone_triangle₁
    (pushoutGlueingMapOfModels i f (pushout.inl i f) (pushout.inr i f) pushout.condition
      hY' hY hX hX' M K' α.hom)
  obtain ⟨ha, hb⟩ := h i f hi hf hY' hY hX hX' M K' hM hK' α u v hT
  exact exists_iso_of_comp_pushoutGlueingMapOfModels_eq_zero i f _ _ _ hY' hY hX hX' M K' α u
    (let := hY'; Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT) ha hb

end AlgebraicGeometry.Space
