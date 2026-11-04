module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolutionPostnikov
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# The Postnikov system and the derived colimit of `- ⊗^L_O K` on a simplicial site

Let `S` be a simplicial-site situation and let `O` be a sheaf of commutative rings on its total
site, so that `(C_total, O)` is a ringed site and the derived tensor product `- ⊗^L_O -` of
Stacks 06YU is available on `D(O)`. Let `K` be an object of `D(O)`.

Stacks 0D9Q puts
`Xₙ = (g_{n!}Oₙ) ⊗^L_O K` and `Yₙ = (g_{n!}Oₙ → … → g_{0!}O₀)[-n] ⊗^L_O K`,
the lower shriek images `g_{n!}Oₙ` and the maps between them being those of the resolution of
Stacks 0D9B, and asserts

1. the triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` form a Postnikov system for
   `… ⟶ X₂ ⟶ X₁ ⟶ X₀`, and
2. `K = hocolim Yₙ[n]` in `D(O)`.

Both are obtained here by instantiating the statements for an abstract exact functor `T` of
`D(O)` — `CategoryTheory.SimplicialSiteSituation.map_moduleResolutionPostnikovSystem` and
`.isHomotopyColimit_map_moduleResolutionSystem` — at `T = - ⊗^L_O K`. That instantiation needs
the three properties of `- ⊗^L_O K` the source appeals to, and all three are proved below:

* it is exact (`isTriangulated_derivedTensorRight`), which is the `exact_left` field of the
  derived tensor product, i.e. part of Stacks 06YU;
* it commutes with countable direct sums
  (`preservesColimitsOfShape_nat_derivedTensorRight`); and
* it carries the structure sheaf to `K`, `O ⊗^L_O K = K`
  (`derivedTensorRightUnitIso`), which is the left unit constraint of Stacks 0FPT.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.totalRingedSite`: the total site of a
  simplicial-site situation together with a sheaf of commutative rings on it, as a ringed site.
* `CategoryTheory.SimplicialSiteSituation.derivedTensorRight`: the functor `- ⊗^L_O K`.
* `CategoryTheory.SimplicialSiteSituation.tensorTotFunctor`: the complex-level functor
  `A ↦ Tot(A ⊗_O L)`, read as the bicomplex functor followed by totalisation.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionTensorPostnikovSystem`: the Postnikov
  system of Stacks 0D9Q(1).

## Main results

* `CategoryTheory.SimplicialSiteSituation.preservesColimitsOfShape_nat_derivedTensorRight`:
  **`- ⊗^L_O K` commutes with countable direct sums.**
* `CategoryTheory.SimplicialSiteSituation.derivedTensorRightUnitIso`: `O ⊗^L_O K = K`.
* `CategoryTheory.SimplicialSiteSituation.isHomotopyColimit_moduleResolutionTensorSystem`:
  **Stacks 0D9Q(2)**, `K = hocolim Yₙ[n]`.
* `CategoryTheory.SimplicialSiteSituation.moduleResolutionTensorTermIso`: the identification of
  the Postnikov system's terms with the source's `Xₙ = (g_{n!}Oₙ) ⊗^L_O K`.

## Implementation notes

**Why the tensor factor is on the right.** The source tensors on the right, `- ⊗^L_O K`, so the
functor instantiated is `T.tensor.flip.obj K` and not `T.tensor.obj K`. This is what forces the
work in `preservesColimitsOfShape_nat_derivedTensorRight`: the derived tensor product is
computed by `comparisonRight` when the *right* factor is K-flat, so on representatives the
functor is `A ↦ Tot(A ⊗_O K')` with the varying complex in the *first* slot of the tensor
bicomplex. The repository's colimit lemma for that bicomplex,
`CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj`, fixes the first slot
instead, so `HomologicalComplex.preservesColimitsOfShape_mapBifunctorFlipObj` below records the
other variance; it is proved the same way, by evaluating the bicomplex in each bidegree.

**How countable direct sums are transferred.** Direct sums in `D(O)` are the images under `Q`
of termwise direct sums of complexes, `Q` preserving them because `Mod(O)` is Grothendieck
abelian (Stacks 0A5L). Every object of `D(O)` is `Q` of a complex, so a countable family in
`D(O)` is, up to isomorphism, `Q ∘ P` for a family `P` of complexes; the natural isomorphism
`derivedTensorRightKFlatIso` identifies `Q ⋙ (- ⊗^L_O Q K') ` with `tensorTotFunctor ⋙ Q`,
and both `tensorTotFunctor` and `Q` preserve the direct sum, which is what
`preservesColimitsOfShape_nat_derivedTensorRight` then reads off. The K-flat representative
`K'` of `K` comes from Stacks 06YS, through
`Stacks.DerivedTensor.RingedSite.kFlatModel`.

**The structure sheaf is commutative here.** The resolution of Stacks 0D9B is available for a
sheaf of possibly noncommutative rings, whereas the derived tensor product of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/OnARingedSite.lean` is built on a
ringed site, whose structure sheaf takes values in `CommRingCat`. The two meet by taking the
sheaf of rings of the resolution to be `Tensor.ringSheaf O`, the structure sheaf of the ringed
site with commutativity forgotten; `Mod(O)` is then literally the same category on both sides,
which is what lets the abstract-`T` statements be instantiated.

**The derived category is the standard one**, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/DerivedSymmetryAndUnit.lean`, whose
unit constraints are stated there.

## References

* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace HomologicalComplex

/-- A bifunctor-valued double complex functor with its *second* complex fixed preserves colimits
of shape `J` as soon as each `F(-, Y)` does: colimits of double complexes are computed in each
bidegree, where the functor is `F(-, Y)` applied to a single degree.

This is the companion of `CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj`,
which fixes the first complex instead. -/
theorem preservesColimitsOfShape_mapBifunctorFlipObj
    {A B E : Type*} [Category* A] [Category* B] [Category* E]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms E]
    {I₁ I₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
    {J : Type*} [Category* J] [HasColimitsOfShape J A] [HasColimitsOfShape J E]
    (F : A ⥤ B ⥤ E) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    (L : HomologicalComplex B c₂)
    (hF : ∀ Y : B, PreservesColimitsOfShape J (F.flip.obj Y)) :
    PreservesColimitsOfShape J ((F.mapBifunctorHomologicalComplex c₁ c₂).flip.obj L) where
  preservesColimit :=
    { preserves := fun {_s} hs => ⟨isColimitOfEval _ _ (fun p =>
        isColimitOfEval _ _ (fun q => by
          have := hF (L.X q)
          exact isColimitOfPreserves (eval A c₁ p ⋙ F.flip.obj (L.X q)) hs))⟩ }

end HomologicalComplex

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

section

variable {S : SimplicialSiteSituation.{u}} (R : Sheaf S.totalTopology CommRingCat.{u})

/-- **The total site of a simplicial-site situation as a ringed site**, for a chosen sheaf of
commutative rings on it. This is the site on which Stacks 0D9Q reads: the resolution of
Stacks 0D9B lives on the total site, and the derived tensor product of Stacks 06YU is
constructed on a ringed site. -/
abbrev totalRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := S.totalCategory
  J := S.totalTopology
  O := R

variable [HasSheafify S.totalTopology AddCommGrpCat.{u}]
  [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-! ### The complex-level functor `A ↦ Tot(A ⊗_O L)` and its countable direct sums -/

/-- The complex-level functor `A ↦ Tot(A ⊗_O L)` for a fixed complex `L`, written as the
tensor-bicomplex functor with its second complex fixed followed by totalisation. On objects this
is `(Tensor.tensorComplex R).flip.obj L`; writing it this way is what lets its colimits be read
off `HomologicalComplex.preservesColimitsOfShape_mapBifunctorFlipObj` and
`CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor`. -/
def tensorTotFunctor (L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ) :
    CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ ⥤
      CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj L ⋙
    HomologicalComplex₂.totalFunctor (Stacks.DerivedTensor.RingedSite.Modules.{u} R)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- On morphisms `tensorTotFunctor` is the map `Tot(f ⊗ 𝟙)` of the ordinary tensor product: the
identity on the fixed factor contributes nothing. -/
theorem tensorTotFunctor_map
    {X Y L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ} (f : X ⟶ Y) :
    (tensorTotFunctor R L).map f =
      HomologicalComplex.mapBifunctorMap f (𝟙 L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R) (ComplexShape.up ℤ) := by
  dsimp only [HomologicalComplex.mapBifunctorMap, tensorTotFunctor, Functor.comp_map,
    HomologicalComplex₂.totalFunctor_map, Functor.flip_obj_map]
  rw [Functor.map_id, Category.comp_id]
  rfl

omit [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- Tensoring a complex on the right with a fixed complex commutes with countable direct sums:
the ordinary tensor product of sheaves of modules does (Stacks 05NB), colimits of complexes and
of double complexes are computed degreewise, and a total complex is a direct sum over each
antidiagonal. -/
theorem preservesColimitsOfShape_nat_tensorTotFunctor
    (L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ) :
    PreservesColimitsOfShape (Discrete ℕ) (tensorTotFunctor R L) := by
  have hsheaf : ∀ Y : Stacks.DerivedTensor.RingedSite.Modules.{u} R,
      PreservesColimitsOfShape (Discrete ℕ)
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).flip.obj Y) := by
    intro Y
    have h : PreservesColimitsOfSize.{u, u}
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).flip.obj Y) :=
      Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj.{u, u, u} R Y
    have : PreservesColimitsOfSize.{0, 0}
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R).flip.obj Y) :=
      preservesSmallestColimits_of_preservesColimits _
    infer_instance
  have := HomologicalComplex.preservesColimitsOfShape_mapBifunctorFlipObj
    (J := Discrete ℕ) (c₁ := ComplexShape.up ℤ)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} R) L hsheaf
  have := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
    (D := Stacks.DerivedTensor.RingedSite.Modules.{u} R) (J := Discrete ℕ)
  dsimp only [tensorTotFunctor]
  infer_instance

/-- **Stacks 0A5L for sheaves of modules on the total site**: `Q` carries the termwise direct sum
of a countable family of complexes to the direct sum in `D(O)`. -/
instance preservesColimitsOfShape_nat_Q :
    PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules.{u} R)) :=
  derivedCategory_Q_preservesCoproductsOfShape _
    (hasExactCountableDirectSums_of_isGrothendieckAbelian.{u} _) ℕ

/-! ### The functor `- ⊗^L_O K` -/

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)

/-- The functor `- ⊗^L_O K` of Stacks 0D9Q, the derived tensor product with `K` in the right
variable. -/
abbrev derivedTensorRight (K : Stacks.DerivedTensor.RingedSite.DerivedModules R) :
    Stacks.DerivedTensor.RingedSite.DerivedModules R ⥤
      Stacks.DerivedTensor.RingedSite.DerivedModules R :=
  T.tensor.flip.obj K

/-- **The first of the three properties of `- ⊗^L_O K` that Stacks 0D9Q uses: it is exact.**
This is the `exact_left` field of a derived tensor product, i.e. part of Stacks 06YU. -/
theorem isTriangulated_derivedTensorRight
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules R) :
    (derivedTensorRight R T K).IsTriangulated :=
  T.exact_left K

/-- On complexes with a K-flat right factor, `- ⊗^L_O Q K'` is the ordinary total tensor
product: the natural isomorphism `Q ⋙ (- ⊗^L_O Q K') ≅ Tot(- ⊗_O K') ⋙ Q` given by
`comparisonRight`, whose naturality in the left variable is part of Stacks 06YU. -/
def derivedTensorRightKFlatIso
    (K' : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ)
    (hK' : Stacks.SheafOfModules.KFlat.KFlat R K') :
    DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules.{u} R) ⋙
        derivedTensorRight R T (DerivedCategory.Q.obj K') ≅
      tensorTotFunctor R K' ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun A => T.comparisonRight A K' hK') (by
    intro A A' f
    have h := T.comparisonRight_naturality f (𝟙 K') hK' hK'
    simp only [DerivedCategory.Q.map_id K',
      (T.tensor.obj (DerivedCategory.Q.obj A')).map_id (DerivedCategory.Q.obj K'),
      Category.id_comp] at h
    refine h.trans ?_
    dsimp only [Functor.comp_map]
    rw [tensorTotFunctor_map]
    rfl)

/-- **The second of the three properties of `- ⊗^L_O K` that Stacks 0D9Q uses: it commutes with
countable direct sums.**

A countable family in `D(O)` is, up to isomorphism, the image under `Q` of a family of
complexes, and `Q` carries the termwise direct sum of the latter to the direct sum of the former
(`preservesColimitsOfShape_nat_Q`, Stacks 0A5L). A K-flat representative `K'` of `K`
(Stacks 06YS) turns `- ⊗^L_O K` on those representatives into the ordinary `Tot(- ⊗_O K')`
(`derivedTensorRightKFlatIso`), which commutes with the direct sum by
`preservesColimitsOfShape_nat_tensorTotFunctor`. -/
theorem preservesColimitsOfShape_nat_derivedTensorRight
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules R) :
    PreservesColimitsOfShape (Discrete ℕ) (derivedTensorRight R T K) := by
  let K' := Stacks.DerivedTensor.RingedSite.kFlatModel R K
  have hK' : Stacks.SheafOfModules.KFlat.KFlat R K' :=
    Stacks.DerivedTensor.RingedSite.kFlatModel_kFlat R K
  have hmodel : PreservesColimitsOfShape (Discrete ℕ)
      (derivedTensorRight R T (DerivedCategory.Q.obj K')) := by
    refine ⟨fun {F} => ?_⟩
    let P : ℕ → CochainComplex (Stacks.DerivedTensor.RingedSite.Modules.{u} R) ℤ :=
      fun n => DerivedCategory.Q.objPreimage (F.obj ⟨n⟩)
    have : PreservesColimit (Discrete.functor P)
        (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules.{u} R) ⋙
          derivedTensorRight R T (DerivedCategory.Q.obj K')) := by
      have := preservesColimitsOfShape_nat_tensorTotFunctor R K'
      exact preservesColimit_of_natIso _ (derivedTensorRightKFlatIso R T K' hK').symm
    have hiso : Discrete.functor P ⋙
        DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules.{u} R) ≅ F :=
      Discrete.natIso (fun i => DerivedCategory.Q.objObjPreimageIso (F.obj i))
    have : PreservesColimit (Discrete.functor P ⋙
        DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules.{u} R))
        (derivedTensorRight R T (DerivedCategory.Q.obj K')) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct P))
        (isColimitOfPreserves (DerivedCategory.Q ⋙
          derivedTensorRight R T (DerivedCategory.Q.obj K')) (coproductIsCoproduct P))
    exact preservesColimit_of_iso_diagram _ hiso
  exact preservesColimitsOfShape_of_natIso
    (T.tensor.flip.mapIso (Stacks.DerivedTensor.RingedSite.kFlatModelIso R K))

/-- **The third of the three properties of `- ⊗^L_O K` that Stacks 0D9Q uses: it carries the
structure sheaf to `K`**, `O ⊗^L_O K = K`. This is the left unit constraint of Stacks 0FPT. -/
def derivedTensorRightUnitIso
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules R) :
    (derivedTensorRight R T K).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))) ≅ K :=
  T.leftUnitIso (totalRingedSite R) K

/-! ### Stacks 0D9Q -/

variable (D : SimplicialModuleResolutionActual S
  (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
  (K : Stacks.DerivedTensor.RingedSite.DerivedModules R)

/-- The terms of the Postnikov system of Stacks 0D9Q(1) are the source's
`Xₙ = (g_{n!}Oₙ) ⊗^L_O K`: the object `Xₙ` of
`CategoryTheory.SimplicialSiteSituation.moduleResolutionTerm` is `g_{n!}Oₙ` placed in degree
zero, by `moduleResolutionTermIso`. -/
def moduleResolutionTensorTermIso (n : ℕ) :
    (derivedTensorRight R T K).obj (moduleResolutionTerm D n) ≅
      (T.tensor.obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) 0).obj
          ((componentModuleLowerShriek S (Stacks.SheafOfModules.Tensor.ringSheaf R) ⦋n⦌).obj
            (SheafOfModules.unit
              (componentRingSheaf S (Stacks.SheafOfModules.Tensor.ringSheaf R) ⦋n⦌))))).obj K :=
  (T.tensor.mapIso (moduleResolutionTermIso D n)).app K

/-- **Stacks 0D9Q(1).** For each length `N`, the triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` with `Xₙ = (g_{n!}Oₙ) ⊗^L_O K` and
`Yₙ = (g_{n!}Oₙ → … → g_{0!}O₀)[-n] ⊗^L_O K` form a Postnikov system (Derived Categories,
Definition 0D7Z) for `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀`.

The triangles are the images under `- ⊗^L_O K` of the brutal-truncation triangles of the
resolution of Stacks 0D9B, and `- ⊗^L_O K` is exact by `isTriangulated_derivedTensorRight`;
the terms are the source's `Xₙ` by `moduleResolutionTensorTermIso`. -/
@[stacks 0D9Q "part (1), the Postnikov system of - ⊗^L_O K"]
def moduleResolutionTensorPostnikovSystem (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) => (derivedTensorRight R T K).obj (moduleResolutionTerm D (i : ℕ)))
      (fun i : Fin N => (derivedTensorRight R T K).map (moduleResolutionTermDiff D (i : ℕ))) :=
  have := isTriangulated_derivedTensorRight R T K
  map_moduleResolutionPostnikovSystem D (derivedTensorRight R T K) N

/-- **Stacks 0D9Q(2).** `K = hocolim Yₙ[n]` in `D(O)`, where
`Yₙ = (g_{n!}Oₙ → … → g_{0!}O₀)[-n] ⊗^L_O K`.

The system `Yₙ[n]` is the image under `- ⊗^L_O K` of the tower of brutal truncations of the
resolution of Stacks 0D9B, whose derived colimit is the structure sheaf
(`isHomotopyColimit_moduleResolutionSystem`, Stacks 0D9Q(2) for `O`); the functor `- ⊗^L_O K` is
exact and commutes with countable direct sums, so it carries that derived colimit to the derived
colimit of the images, and it sends `O` to `K` by `derivedTensorRightUnitIso`. -/
@[stacks 0D9Q "part (2), the homotopy colimit, K = hocolim Yₙ[n] for Yₙ = (…)[-n] ⊗^L_O K"]
theorem isHomotopyColimit_moduleResolutionTensorSystem :
    IsHomotopyColimit (moduleResolutionSystem D ⋙ derivedTensorRight R T K) K :=
  have := isTriangulated_derivedTensorRight R T K
  have := preservesColimitsOfShape_nat_derivedTensorRight R T K
  StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso
    (isHomotopyColimit_map_moduleResolutionSystem D (derivedTensorRight R T K))
    (derivedTensorRightUnitIso R T K)

end

end CategoryTheory.SimplicialSiteSituation

end
