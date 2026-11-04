module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# The derived tensor product commutes with direct sums

Let `X` be a scheme and `L` an object of `D(𝒪_X)`. Then `K ↦ K ⊗ᴸ_{𝒪_X} L` commutes with
direct sums indexed by any type of the scheme universe, and so does its restriction
`Stacks.Duality.quasiCoherentDerivedTensorRight` to `D_QCoh(𝒪_X)`.

This is the fact that
`Stacks.Duality.preservesCoproducts_quasiCoherentDerivedTensorRight_comp_rightAdjoint` of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/RightAdjointDirectSums.lean`
would otherwise need as an instance binder `htensor`: the sheaf-level [Stacks, Tag 05NB] carried
up to the derived category.

## The argument

Three steps, each of them already available below the derived category.

*The complex level.* Tensoring a sheaf of `𝒪_X`-modules with a fixed one commutes with colimits,
which is [Stacks, Tag 05NB] — `Stacks.SheafOfModules.preservesColimits_sheafTensorObj`, and in the
form needed here, with the fixed factor on the *right*,
`Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj`. Colimits of complexes and of double
complexes are computed in each degree, so `K ↦ (K ⊗_{𝒪_X} L)^{p,q}` read as a double complex
commutes with them as well; that is
`preservesColimitsOfShape_mapBifunctorHomologicalComplexFlipObj`. Totalising preserves colimits
too — `CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor`, whose per-degree
content is that `Tot(Z)ⁿ` is the coproduct of the `Z^{p,q}` with `p + q = n` — and
`Stacks.SheafOfModules.Tensor.tensorComplex` is the composite of the two, which is
`map₂HomologicalComplexFlipObjIsoTotal`. Together: `K ↦ Tot(K ⊗_{𝒪_X} L)` commutes with direct
sums, which is `preservesColimitsOfShape_discrete_tensorComplexFlipObj`.

*Descent through the localization.* `Q : C(𝒪_X) ⥤ D(𝒪_X)` commutes with direct sums
([Stacks, Tag 07D9], at the locally small model
`Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts`) and is essentially
surjective. A functor out of `D(𝒪_X)` which, precomposed with `Q`, is isomorphic to a
direct-sum-preserving functor followed by `Q` therefore commutes with direct sums itself: a family
of objects of `D(𝒪_X)` is a family of classes of complexes, and the two routes to the direct sum
of the family agree. That is `preservesColimitsOfShape_discrete_of_essSurj`.

The isomorphism it is applied to is the comparison field `comparisonRight` of the derived tensor
product ([Stacks, Tag 06YU]), which computes `Q(K) ⊗ᴸ Q(L)` as `Q(Tot(K ⊗ L))` for a K-flat `L`
and an *arbitrary* `K` — so, read in `K`, it is a morphism of functors, its naturality being the
field `comparisonRight_naturality` at `g = 𝟙`. A K-flat representative of `L` exists by
[Stacks, Tag 06YS], `Stacks.Duality.exists_kFlatComplex_iso`. This gives
`preservesColimitsOfShape_discrete_derivedTensorRight`.

*The restriction to `D_QCoh`.* `D_QCoh(𝒪_X)` is closed under direct sums ([Stacks, Tag 08DT],
`Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts`), so its
inclusion into `D(𝒪_X)` creates them, hence both preserves and reflects them. The restricted
tensor product of [Stacks, Tag 08DX] part (1) followed by the inclusion is the inclusion followed
by the unrestricted one, so direct-sum preservation transfers.

## Main results

All in the namespace `Stacks.Duality`.

* `preservesColimitsOfShape_discrete_derivedTensorRight` — `K ↦ K ⊗ᴸ_{𝒪_X} L` commutes with
  direct sums on `D(𝒪_X)`.
* `preservesColimitsOfShape_discrete_quasiCoherentDerivedTensorRight` — the same for
  `Stacks.Duality.quasiCoherentDerivedTensorRight`, the restriction to `D_QCoh(𝒪_X)`. This is
  the statement `htensor` asked for.

## What is carried, and why

Nothing. Both main results are unconditional in `X`, `L` and the index type: no quasi-compactness,
no quasi-separatedness, no generator, no adjunction.

No `@[stacks]` attribute. [Stacks, Tag 05NB] is the sheaf-level statement and is registered where
it is proved; the derived statement has no tag of its own in the source. The source uses it
without naming it: the proof of Lemma 48.13.3 ([Stacks, Tag 0A9U]) says only that the objects at
which Equation 48.8.0.1 is invertible form a triangulated subcategory "which is moreover preserved
under taking direct sums", and cites, for that sentence, nothing at all — of the five things its
proof does cite ([Stacks, Tag 0A9R], Theorem 36.18.2, [Stacks, Tag 09IS], More on Algebra
Remark 15.60.11 and [Stacks, Tag 0A9T]) none is the tensor side.

## References

* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0A9U](https://stacks.math.columbia.edu/tag/0A9U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### Tensoring complexes with a fixed complex on the right -/

section Abstract

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
  (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]

/-- **The double complex `F(-, L)` commutes with colimits of shape `J`** as soon as each
`F(-, Y)` does. A colimit of double complexes is computed in each bidegree `(p, q)`, where the
functor is tensoring the degree-`p` part with the degree-`q` part of `L`. -/
theorem preservesColimitsOfShape_mapBifunctorHomologicalComplexFlipObj {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasColimitsOfShape J D] (L : CochainComplex B ℤ)
    (hF : ∀ Y : B, PreservesColimitsOfShape J (F.flip.obj Y)) :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj L) where
  preservesColimit {E} :=
    { preserves := fun {_s} hs => ⟨HomologicalComplex.isColimitOfEval _ _ (fun p =>
        HomologicalComplex.isColimitOfEval _ _ (fun q => by
          have := hF (L.X q)
          exact isColimitOfPreserves
            (HomologicalComplex.eval A (ComplexShape.up ℤ) p ⋙ F.flip.obj (L.X q)) hs))⟩ }

variable
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]

/-- **`K ↦ Tot(F(K, L))` is the double complex `F(-, L)` followed by totalisation.** The two
agree on objects by definition; on a morphism `f` the bifunctor route tensors `f` with `𝟙 L`,
which is the double-complex route composed with the identity. -/
def map₂HomologicalComplexFlipObjIsoTotal (L : CochainComplex B ℤ) :
    (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj L ≅
      (F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj L ⋙
        HomologicalComplex₂.totalFunctor D (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K K' f
    simp only [Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
      HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id, Category.comp_id,
      Iso.refl_hom, Functor.comp_map, HomologicalComplex₂.totalFunctor_map]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Abstract

/-! ### Descent of direct-sum preservation through an essentially surjective functor -/

/-- **Direct-sum preservation descends through an essentially surjective functor.** Let
`Lo : C₀ ⥤ D₀` be essentially surjective and preserve coproducts of shape `ι`, and let
`T : D₀ ⥤ D₀` be a functor whose precomposition with `Lo` is isomorphic to `G ⋙ Lo` for some
`G : C₀ ⥤ C₀` preserving those coproducts. Then `T` preserves them.

A family of objects of `D₀` is, up to isomorphism, the image of a family of objects of `C₀`; the
image under `Lo` of the colimit cocone of the latter is a colimit cocone, and `T` carries it to
one because `Lo ⋙ T` does. -/
theorem preservesColimitsOfShape_discrete_of_essSurj {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    {ι : Type*} (Lo : C₀ ⥤ D₀) [Lo.EssSurj] [HasColimitsOfShape (Discrete ι) C₀]
    [PreservesColimitsOfShape (Discrete ι) Lo] (G : C₀ ⥤ C₀) (T : D₀ ⥤ D₀)
    (hG : PreservesColimitsOfShape (Discrete ι) G) (e : Lo ⋙ T ≅ G ⋙ Lo) :
    PreservesColimitsOfShape (Discrete ι) T := by
  have hGL : PreservesColimitsOfShape (Discrete ι) (G ⋙ Lo) := by
    have := hG
    infer_instance
  have hLT : PreservesColimitsOfShape (Discrete ι) (Lo ⋙ T) :=
    preservesColimitsOfShape_of_natIso e.symm
  constructor
  intro E
  have hc := colimit.isColimit (Discrete.functor fun i => Lo.objPreimage (E.obj ⟨i⟩))
  have hT : PreservesColimit
      (Discrete.functor (fun i => Lo.objPreimage (E.obj ⟨i⟩)) ⋙ Lo) T :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves Lo hc)
      (isColimitOfPreserves (Lo ⋙ T) hc)
  have hiso : Discrete.functor (fun i => Lo.objPreimage (E.obj ⟨i⟩)) ⋙ Lo ≅ E :=
    Discrete.natIso fun i => Lo.objObjPreimageIso (E.obj i)
  exact preservesColimit_of_iso_diagram T hiso

/-! ### The derived tensor product on a scheme -/

section Scheme

variable (X : Scheme.{u}) (J : Type u)

/-- **`K ↦ Tot(K ⊗_{𝒪_X} L)` commutes with direct sums**, for a fixed complex `L` of
`𝒪_X`-modules. The total tensor complex of [Stacks, Tag 06YM] is the tensor double complex
followed by totalisation, and both commute with direct sums — the first by [Stacks, Tag 05NB]
in each bidegree, the second because `Tot(Z)ⁿ` is a coproduct of the `Z^{p,q}`. -/
theorem preservesColimitsOfShape_discrete_tensorComplexFlipObj (L : TensorComplex X) :
    PreservesColimitsOfShape (Discrete J)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).flip.obj L) := by
  have htot : ∀ K : HomologicalComplex₂ (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ), K.HasTotal (ComplexShape.up ℤ) :=
    fun _ => inferInstance
  have hbi : PreservesColimitsOfShape (Discrete J)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj L) :=
    preservesColimitsOfShape_mapBifunctorHomologicalComplexFlipObj _ L fun Y => by
      have := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj X.sheaf Y
      infer_instance
  have htf := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
    (D := Stacks.DerivedTensor.RingedSite.Modules X.sheaf) (J := Discrete J)
  exact preservesColimitsOfShape_of_natIso
    (map₂HomologicalComplexFlipObjIsoTotal
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) L).symm

/-- **`K ↦ K ⊗ᴸ_{𝒪_X} L` commutes with direct sums on `D(𝒪_X)`**, for every object `L` of
`D(𝒪_X)` and every index type of the scheme universe.

Choose a K-flat complex `Lc` representing `L` ([Stacks, Tag 06YS]). Read in `K`, the comparison
field `comparisonRight` of the derived tensor product is an isomorphism of functors
`Q ⋙ (- ⊗ᴸ Q(Lc)) ≅ Tot(- ⊗ Lc) ⋙ Q`; the right-hand side commutes with direct sums because
`Tot(- ⊗ Lc)` does and `Q` does, and that descends to the left-hand factor because `Q` is
essentially surjective. -/
theorem preservesColimitsOfShape_discrete_derivedTensorRight (L : DerivedCategory X.Modules) :
    PreservesColimitsOfShape (Discrete J) ((derivedTensor X).flip.obj L) := by
  obtain ⟨Lc, hLc, ⟨eL⟩⟩ := exists_kFlatComplex_iso X L
  have hQ : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := X.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts X.Modules J
  have key : PreservesColimitsOfShape (Discrete J)
      ((derivedTensor X).flip.obj (DerivedCategory.Q.obj Lc)) := by
    refine preservesColimitsOfShape_discrete_of_essSurj (C₀ := CochainComplex X.Modules ℤ)
      (D₀ := DerivedCategory X.Modules) (DerivedCategory.Q (C := X.Modules))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).flip.obj Lc)
      ((derivedTensor X).flip.obj (DerivedCategory.Q.obj Lc))
      (preservesColimitsOfShape_discrete_tensorComplexFlipObj X J Lc) ?_
    exact NatIso.ofComponents
      (fun K => (Stacks.Cohomology.TorAmplitude.derTensor
        X.toRingedSpace).comparisonRight K Lc hLc)
      (fun {K K'} f => by
        have h := (Stacks.Cohomology.TorAmplitude.derTensor
          X.toRingedSpace).comparisonRight_naturality f (𝟙 Lc) hLc hLc
        simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
        exact h)
  exact preservesColimitsOfShape_of_natIso ((derivedTensor X).flip.mapIso eL)

/-- The restricted derived tensor product of [Stacks, Tag 08DX] part (1), followed by the
inclusion of `D_QCoh(𝒪_X)` into `D(𝒪_X)`, acts on a morphism as the unrestricted one does. The
restriction is the lift of the uncurried tensor product, so the inclusion of its value on `f` is
the unrestricted value on `f` composed with the identity of the second argument. -/
private theorem ι_map_quasiCoherentDerivedTensor_map_app
    (L : quasiCoherentDerivedCategory X) {K K' : quasiCoherentDerivedCategory X} (f : K ⟶ K') :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map
        (((quasiCoherentDerivedTensor X).map f).app L) =
      ((derivedTensor X).map
        ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map f)).app L.obj := by
  show ((derivedTensor X).map
      ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map f)).app L.obj ≫
    ((derivedTensor X).obj
      ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.obj K')).map (𝟙 L.obj) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **`Stacks.Duality.quasiCoherentDerivedTensorRight` commutes with direct sums**: for every
scheme `X`, every object `L` of `D_QCoh(𝒪_X)` and every index type of the scheme universe, the
endofunctor `K ↦ K ⊗ᴸ_{𝒪_X} L` of `D_QCoh(𝒪_X)` preserves coproducts of that shape.

`D_QCoh(𝒪_X)` is closed under direct sums ([Stacks, Tag 08DT]), so its inclusion into `D(𝒪_X)`
creates them and therefore reflects them; and the restricted tensor product followed by the
inclusion is the inclusion followed by `preservesColimitsOfShape_discrete_derivedTensorRight`. -/
theorem preservesColimitsOfShape_discrete_quasiCoherentDerivedTensorRight
    (L : quasiCoherentDerivedCategory X) :
    PreservesColimitsOfShape (Discrete J) (quasiCoherentDerivedTensorRight X L) := by
  have hclosed :=
    Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X J
  have hamb := preservesColimitsOfShape_discrete_derivedTensorRight X J L.obj
  have hnat : (quasiCoherentDerivedTensor X).flip.obj L ⋙
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        (derivedTensor X).flip.obj L.obj :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
      (Category.comp_id _).trans
        ((ι_map_quasiCoherentDerivedTensor_map_app X L f).trans (Category.id_comp _).symm))
  have hcomp : PreservesColimitsOfShape (Discrete J)
      ((quasiCoherentDerivedTensor X).flip.obj L ⋙
        (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι) :=
    preservesColimitsOfShape_of_natIso hnat.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι

end Scheme

end Stacks.Duality

end
