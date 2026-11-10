module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexFlip
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# The derived tensor product of abelian sheaves

Let `J` be a Grothendieck topology on a small category `C`. This file builds the derived tensor
product over `ℤ`

`- ⊗^{L}_ℤ - : D(Ab(C, J)) ⥤ D(Ab(C, J)) ⥤ D(Ab(C, J))`

on the unbounded derived category of abelian sheaves, and proves the four properties a client
needs of it: it is a bifunctor, each partial functor is exact, tensoring on the right with a
fixed object commutes with countable direct sums, and the constant sheaf `ℤ` in degree zero is
a unit.

## Main definitions

* `Stacks.DerivedTensor.AbelianSheaves.intRingSheaf`: the constant sheaf of commutative rings
  `ℤ` on the site.
* `Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence`: **abelian sheaves are the sheaves of
  modules over the constant sheaf of rings `ℤ`.**
* `Stacks.DerivedTensor.AbelianSheaves.derivedTensor`: the derived tensor product
  `- ⊗^{L}_ℤ -` on `D(Ab(C, J))`.
* `Stacks.DerivedTensor.AbelianSheaves.intSheaf` and
  `Stacks.DerivedTensor.AbelianSheaves.unitObject`: the constant abelian sheaf `ℤ`, and that
  sheaf placed in degree zero as an object of `D(Ab(C, J))`.

## Main results

* `Stacks.DerivedTensor.AbelianSheaves.isTriangulated_derivedTensorFlipObj` and
  `isTriangulated_derivedTensorObj`: `- ⊗^{L}_ℤ K` and `K ⊗^{L}_ℤ -` are exact functors of
  triangulated categories.
* `Stacks.DerivedTensor.AbelianSheaves.preservesCountableCoproducts_derivedTensorFlipObj`:
  **`- ⊗^{L}_ℤ K` commutes with countable direct sums.**
* `Stacks.DerivedTensor.AbelianSheaves.leftUnitIso` and `constantSheafLeftUnitIso`:
  `ℤ ⊗^{L}_ℤ K ≅ K`, with the unit written first as the structure sheaf carried across the
  equivalence and then as the constant sheaf `ℤ`.
* `Stacks.DerivedTensor.AbelianSheaves.intSheafIsoConstantSheaf`: the unit really is the
  constant sheaf `ℤ`, and not merely the structure sheaf of the ringed site the construction
  passes through.
* `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesColimitsCountable_tensorFlipObj`:
  the same statement about direct sums for the derived tensor product of sheaves of modules on
  a ringed site, which is what the abelian-sheaf statement is transported from.

## Implementation notes

The construction is a transport, not a second development. The derived tensor product of
sheaves of modules on a ringed site is `Stacks.DerivedTensor.RingedSite` (Stacks 06YU), and an
abelian sheaf is the same thing as a sheaf of modules over the constant sheaf of rings `ℤ`: an
additive map of abelian sheaves is automatically `ℤ`-linear and an abelian sheaf carries a
unique action of the constant sheaf `ℤ`, which extends along the sheafification of the scalars.
That is `Stacks.Cohomology.full_toSheaf_of_constant_int` and
`Stacks.Cohomology.essSurj_toSheaf_of_constant_int`, used here at the sheaf of rings underlying
the constant sheaf of *commutative* rings `ℤ` — the ringed-site tensor product is built from a
`Sheaf J CommRingCat`, whereas those two lemmas take the sheaf of rings and the locally
bijective map of scalars as data. The bridge is `intRingSheafScalars`: whiskering the
sheafification unit of the constant presheaf with `forget₂ CommRingCat RingCat` changes neither
the underlying presheaf of sets nor therefore the local bijectivity, which is exactly what
`Presheaf.isLocallySurjective_iff_whisker_forget` and
`Presheaf.isLocallyInjective_forget_iff` say.

Only the *left* unit is supplied, `ℤ ⊗^{L}_ℤ K ≅ K`, since that is the one a Postnikov-system
client uses; the right unit is the same construction read through
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`.

**What commuting with direct sums needs.** The two comparison isomorphisms of a
`DerivedTensorProduct` are natural in both variables, so for a K-flat right factor `L` the
functor `- ⊗^{L}_𝒪 Q(L)` is, after `DerivedCategory.Q`, the ordinary total tensor complex
`Tot(- ⊗_𝒪 L)`; that functor commutes with countable direct sums because `⊗_𝒪` does
(`Stacks.SheafOfModules.preservesColimitsCountable_sheafTensorObj`, which is Stacks 05NB) and
because both the double-complex construction and totalisation are computed degreewise
(`CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj` and
`preservesColimitsOfShape_totalFunctor`). Passing back across `DerivedCategory.Q` is
`CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_essSurj_comp`: a discrete diagram in
the derived category lifts objectwise to complexes, which is all the transfer needs. The
*variance* is the one point of friction: the existing machinery fixes the first tensor factor,
while `- ⊗^{L}_ℤ K` fixes the second, and the two are exchanged by the Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` together with its naturality
`tensorComplexFlipIso_hom_naturality` — so no second copy of the colimit machinery in the
opposite variance is written.

**Universes.** Everything is at one universe `u`, with `C` small. This is inherited from the
ringed-site development, which pins all four universes of Stacks 06YU to a single `u` because
the existence of K-flat resolutions does; see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnARingedSite`. The derived category
is the standard model throughout, as it is for
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso`.

**Auxiliary declarations outside the file's own namespace.** Several statements the
construction needs are about objects that have nothing to do with abelian sheaves, and are
stated where they belong rather than being inlined:
`CategoryTheory.Limits.preservesColimitsOfShape_discrete_of_essSurj_comp`,
`HomologicalComplex.mapBifunctorMap_id_left`,
`Stacks.SheafOfModules.preservesColimitsCountable_sheafTensorObj` and the three declarations in
`Stacks.SheafOfModules.Tensor` about the total tensor complex.

**No tag.** Neither the equivalence nor the derived tensor product on abelian sheaves is
assigned a tag by the source at this point: Stacks 06YU is the ringed-site statement, which is
already registered in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite`, and the
specialisation to the constant sheaf `ℤ` is infrastructure.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- **Transfer of commutation with direct sums along an essentially surjective functor.** If
`Φ` is essentially surjective and commutes with `I`-indexed direct sums, and `Φ ⋙ F` does too,
then so does `F`. A discrete diagram is a family of objects, so it lifts through `Φ` objectwise;
no lifting of morphisms is needed, which is why the statement is for discrete shapes and not
for a general shape. -/
theorem preservesColimitsOfShape_discrete_of_essSurj_comp
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (Φ : C ⥤ D) [Φ.EssSurj] {I : Type*} [HasColimitsOfShape (Discrete I) C]
    [PreservesColimitsOfShape (Discrete I) Φ]
    (F : D ⥤ E) [PreservesColimitsOfShape (Discrete I) (Φ ⋙ F)] :
    PreservesColimitsOfShape (Discrete I) F := by
  refine ⟨fun {d} => ?_⟩
  let d' : Discrete I ⥤ C := Discrete.functor fun i => Φ.objPreimage (d.obj ⟨i⟩)
  have : PreservesColimit (d' ⋙ Φ) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves Φ (colimit.isColimit d'))
      (isColimitOfPreserves (Φ ⋙ F) (colimit.isColimit d'))
  exact preservesColimit_of_iso_diagram F
    (Discrete.natIso fun i => Φ.objObjPreimageIso (d.obj i) : d' ⋙ Φ ≅ d)

end CategoryTheory.Limits

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-- **Tag 05NB in the countable case.** Tensoring on the left with a fixed sheaf of modules
commutes with countable direct sums. This is `preservesColimits_sheafTensorObj` with the index
universe brought down to `Type 0`, which is where a countable family lives. -/
theorem preservesColimitsCountable_sheafTensorObj
    (X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (I : Type) :
    PreservesColimitsOfShape (Discrete I) ((sheafTensor R).obj X) := by
  have := preservesColimits_sheafTensorObj R X
  exact preservesColimitsOfShape_discrete_shrink.{u} _ I

end Stacks.SheafOfModules

namespace HomologicalComplex

/-- The map of total complexes induced by a morphism in the second variable alone is the
totalisation of the map of double complexes: `mapBifunctorMap` carries the identity of the
first variable through `F` before composing, and `F` sends an identity to an identity. -/
theorem mapBifunctorMap_id_left {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    {I₁ I₂ I : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape I}
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    [TotalComplexShape c₁ c₂ c] [DecidableEq I]
    (L : HomologicalComplex C₁ c₁) {K K' : HomologicalComplex C₂ c₂} (f : K ⟶ K')
    [HasMapBifunctor L K F c] [HasMapBifunctor L K' F c] :
    mapBifunctorMap (𝟙 L) f F c =
      HomologicalComplex₂.total.map
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj L).map f) c := by
  unfold mapBifunctorMap
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

end HomologicalComplex

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The tensor product bifunctor `⊗_O` on sheaves of modules is additive. -/
local instance sheafTensorAdditiveLocal : (sheafTensor.{u, u, u, u, u} R).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} R

/-- Tensoring on the left with a fixed sheaf of modules `X` is an additive functor. -/
local instance sheafTensorObjAdditiveLocal (X : SheafOfModules.{u} (ringSheaf R)) :
    ((sheafTensor.{u, u, u, u, u} R).obj X).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} R X

/-- `Tot(L ⊗_O -)` as the K-flat bifunctor machinery builds it is the partial functor of the
total tensor bifunctor of Stacks 06YM. -/
def totFunctorIsoTensorComplexObj
    (L : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ) :
    CochainComplex.KFlatBifunctor.totFunctor (sheafTensor R) L ≅ (tensorComplex R).obj L :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K K' f
    simp only [Iso.refl_hom]
    exact (HomologicalComplex.mapBifunctorMap_id_left (sheafTensor R) L f).symm)

/-- **The Koszul symmetry of the total tensor complex as an isomorphism of functors.**
Tensoring on the right with a fixed complex is, up to the Koszul signs, tensoring on the left
with it; the symmetry is natural by
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso_hom_naturality`. -/
def tensorComplexFlipObjIso (L : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ) :
    (tensorComplex R).flip.obj L ≅ (tensorComplex R).obj L :=
  NatIso.ofComponents (fun K => tensorComplexFlipIso R K L)
    (fun f => tensorComplexFlipIso_hom_naturality R f (𝟙 L))

/-- **Tensoring on the right with a fixed complex commutes with countable direct sums.** The
double complex and its totalisation are computed degreewise, where the functor is `⊗_O` with
one variable fixed, and that commutes with direct sums by Stacks 05NB; the variance is turned
round by the Koszul symmetry. -/
theorem preservesColimitsCountable_tensorComplexFlipObj
    (L : CochainComplex (SheafOfModules.{u} (ringSheaf R)) ℤ) (I : Type) :
    PreservesColimitsOfShape (Discrete I) ((tensorComplex R).flip.obj L) := by
  have h₁ := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_mapBifunctorObj
    (J := Discrete I) (sheafTensor R) L
    (fun X => preservesColimitsCountable_sheafTensorObj R X I)
  have h₂ := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
    (D := SheafOfModules.{u} (ringSheaf R)) (J := Discrete I)
  have h₃ : PreservesColimitsOfShape (Discrete I)
      (CochainComplex.KFlatBifunctor.totFunctor (sheafTensor R) L) :=
    comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete I) ((tensorComplex R).obj L) :=
    preservesColimitsOfShape_of_natIso (totFunctorIsoTensorComplexObj R L)
  exact preservesColimitsOfShape_of_natIso (tensorComplexFlipObjIso R L).symm

end Stacks.SheafOfModules.Tensor

namespace Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

open Stacks.SheafOfModules.Tensor

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (T : DerivedTensorProduct R)

attribute [local instance] Stacks.SheafOfModules.Tensor.sheafTensorAdditiveLocal
  Stacks.SheafOfModules.Tensor.sheafTensorObjAdditiveLocal

/-- **The right K-flat comparison as an isomorphism of functors.** For a K-flat complex `L`,
`- ⊗^{L}_𝒪 Q(L)` precomposed with `DerivedCategory.Q` is the ordinary total tensor complex
`Tot(- ⊗_𝒪 L)` followed by `Q`; this is `DerivedTensorProduct.comparisonRight` read as a
natural isomorphism, its naturality field at the identity of `L`. -/
def comparisonRightNatIso (L : CochainComplex (Modules R) ℤ)
    (hL : Stacks.SheafOfModules.KFlat R L) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj L) ≅
      (tensorComplex R).flip.obj L ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => T.comparisonRight K L hL) (fun {_ _} f => by
    have h := T.comparisonRight_naturality f (𝟙 L) hL hL
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h)

/-- **`- ⊗^{L}_𝒪 B` commutes with countable direct sums.** Replacing `B` by a K-flat model
turns the derived tensor product into the ordinary total tensor complex, which commutes with
direct sums by `preservesColimitsCountable_tensorComplexFlipObj`; the passage back across
`DerivedCategory.Q` is `preservesColimitsOfShape_discrete_of_essSurj_comp`, using that `Q`
itself commutes with direct sums (Stacks 07D9). -/
theorem preservesColimitsCountable_tensorFlipObj
    (B : DerivedCategory (Modules R)) (I : Type) :
    PreservesColimitsOfShape (Discrete I) (T.tensor.flip.obj B) := by
  have hQ : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := Modules R)) :=
    preservesColimitsOfShape_discrete_shrink.{u} _ I
  have key : ∀ L : CochainComplex (Modules R) ℤ, Stacks.SheafOfModules.KFlat R L →
      PreservesColimitsOfShape (Discrete I) (T.tensor.flip.obj (DerivedCategory.Q.obj L)) := by
    intro L hL
    have h₁ : PreservesColimitsOfShape (Discrete I)
        ((tensorComplex R).flip.obj L ⋙ DerivedCategory.Q) := by
      have := preservesColimitsCountable_tensorComplexFlipObj R L I
      exact comp_preservesColimitsOfShape _ _
    have h₂ : PreservesColimitsOfShape (Discrete I)
        (DerivedCategory.Q ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj L)) :=
      preservesColimitsOfShape_of_natIso (comparisonRightNatIso R T L hL).symm
    exact preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q _
  have := key (kFlatModel R B) (kFlatModel_kFlat R B)
  exact preservesColimitsOfShape_of_natIso (T.tensor.flip.mapIso (kFlatModelIso R B))

end Stacks.DerivedTensor.RingedSite.DerivedTensorProduct

namespace Stacks.DerivedTensor.AbelianSheaves

open Stacks.SheafOfModules.Tensor Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)

/-! ### Abelian sheaves as modules over the constant sheaf of rings `ℤ` -/

/-- The constant sheaf of commutative rings `ℤ` on the site. -/
abbrev intRingSheaf : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The sheaf of (not necessarily commutative) rings underlying the constant sheaf of
commutative rings `ℤ`: the one over which the sheaves of modules are taken. -/
abbrev intRings : Sheaf J RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (intRingSheaf J)

/-- The scalars of the constant sheaf of rings `ℤ`: the sheafification unit of the constant
presheaf `ℤ`, read in `RingCat` along `forget₂ CommRingCat RingCat`. -/
def intRingSheafScalars :
    (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u} ℤ)) ⟶ (intRings J).obj :=
  Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))))
    (forget₂ CommRingCat RingCat)

/-- The scalars of the constant sheaf of rings `ℤ` are locally surjective. -/
instance isLocallySurjective_intRingSheafScalars :
    Presheaf.IsLocallySurjective J (intRingSheafScalars J) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective J
    (Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))))
      (forget CommRingCat))
  infer_instance

/-- The scalars of the constant sheaf of rings `ℤ` are locally injective. -/
instance isLocallyInjective_intRingSheafScalars :
    Presheaf.IsLocallyInjective J (intRingSheafScalars J) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective J
    (Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))))
      (forget CommRingCat))
  infer_instance

/-- **Abelian sheaves are the sheaves of modules over the constant sheaf of rings `ℤ`.** The
forgetful functor from sheaves of modules over the constant sheaf of rings `ℤ` to abelian
sheaves is an equivalence. -/
theorem isEquivalence_toSheaf_intRingSheaf :
    (SheafOfModules.toSheaf.{u} (intRings J)).IsEquivalence := by
  have _ := Stacks.Cohomology.full_toSheaf_of_constant_int (intRingSheafScalars J)
  have _ := Stacks.Cohomology.essSurj_toSheaf_of_constant_int (intRingSheafScalars J)
  exact {}

/-- **Abelian sheaves are the sheaves of modules over the constant sheaf of rings `ℤ`**, as an
equivalence of categories. -/
def moduleEquivalence : Modules (intRingSheaf J) ≌ Sheaf J Ab.{u} :=
  have := isEquivalence_toSheaf_intRingSheaf J
  (SheafOfModules.toSheaf.{u} (intRings J)).asEquivalence

/-- The functor of `moduleEquivalence` is additive. -/
instance : (moduleEquivalence J).functor.Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{u} (intRings J)).Additive

/-- The inverse of `moduleEquivalence` is additive. -/
instance : (moduleEquivalence J).inverse.Additive := (moduleEquivalence J).inverse_additive

/-- The tensor product bifunctor on sheaves of modules over the constant sheaf of rings `ℤ` is
additive. -/
local instance sheafTensorAdditiveInt :
    (sheafTensor.{u, u, u, u, u} (intRingSheaf J)).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (intRingSheaf J)

/-- Tensoring on the left with a fixed sheaf of modules over the constant sheaf of rings `ℤ` is
an additive functor. -/
local instance sheafTensorObjAdditiveInt (X : SheafOfModules.{u} (intRings J)) :
    ((sheafTensor.{u, u, u, u, u} (intRingSheaf J)).obj X).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} (intRingSheaf J) X

/-- Any two cochain complexes of sheaves of modules over the constant sheaf of rings `ℤ` have a
total tensor complex. -/
local instance hasMapBifunctorInt (K L : CochainComplex (SheafOfModules.{u} (intRings J)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (sheafTensor (intRingSheaf J)) (ComplexShape.up ℤ) :=
  @Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ _ J (intRingSheaf J)
    (inferInstance : HasWeakSheafify J AddCommGrpCat.{u})
    (inferInstance : J.WEqualsLocallyBijective AddCommGrpCat.{u}) _ K L

/-! ### The derived tensor product -/

/-- The derived tensor product on sheaves of modules over the constant sheaf of rings `ℤ`,
i.e. Stacks 06YU at that structure sheaf. -/
abbrev intDerivedTensorProduct : DerivedTensorProduct (intRingSheaf J) :=
  @canonicalDerivedTensorProduct _ _ J (intRingSheaf J) _ _ _
    (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (intRingSheaf J))
    (fun M => Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (intRingSheaf J) M)
    (fun K L => hasMapBifunctorInt J K L)

/-- **The derived tensor product of abelian sheaves**, `- ⊗^{L}_ℤ -` on `D(Ab(C, J))`: the
derived tensor product of sheaves of modules over the constant sheaf of rings `ℤ`, carried
across the equivalence `moduleEquivalence`. -/
def derivedTensor :
    DerivedCategory (Sheaf J Ab.{u}) ⥤ DerivedCategory (Sheaf J Ab.{u}) ⥤
      DerivedCategory (Sheaf J Ab.{u}) :=
  (moduleEquivalence J).inverse.mapDerivedCategory ⋙
    ((intDerivedTensorProduct J).tensor ⋙
        (Functor.whiskeringRight _ _ _).obj (moduleEquivalence J).functor.mapDerivedCategory) ⋙
      (Functor.whiskeringLeft _ _ _).obj (moduleEquivalence J).inverse.mapDerivedCategory

/-- `- ⊗^{L}_ℤ K` is the corresponding functor on sheaves of modules, conjugated by the
equivalence. -/
theorem derivedTensor_flip_obj (K : DerivedCategory (Sheaf J Ab.{u})) :
    (derivedTensor J).flip.obj K =
      (moduleEquivalence J).inverse.mapDerivedCategory ⋙
        ((intDerivedTensorProduct J).tensor.flip.obj
          ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ⋙
          (moduleEquivalence J).functor.mapDerivedCategory := rfl

/-- `K ⊗^{L}_ℤ -` is the corresponding functor on sheaves of modules, conjugated by the
equivalence. -/
theorem derivedTensor_obj (K : DerivedCategory (Sheaf J Ab.{u})) :
    (derivedTensor J).obj K =
      (moduleEquivalence J).inverse.mapDerivedCategory ⋙
        ((intDerivedTensorProduct J).tensor.obj
          ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ⋙
          (moduleEquivalence J).functor.mapDerivedCategory := rfl

/-! ### Exactness -/

/-- The conjugated functor, spelled out: this is the composite whose shift-compatibility and
exactness the instances below read off. -/
abbrev flipComp (K : DerivedCategory (Sheaf J Ab.{u})) :
    DerivedCategory (Sheaf J Ab.{u}) ⥤ DerivedCategory (Sheaf J Ab.{u}) :=
  (moduleEquivalence J).inverse.mapDerivedCategory ⋙
    ((intDerivedTensorProduct J).tensor.flip.obj
      ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ⋙
      (moduleEquivalence J).functor.mapDerivedCategory

/-- The conjugated functor in the other variable, spelled out. -/
abbrev objComp (K : DerivedCategory (Sheaf J Ab.{u})) :
    DerivedCategory (Sheaf J Ab.{u}) ⥤ DerivedCategory (Sheaf J Ab.{u}) :=
  (moduleEquivalence J).inverse.mapDerivedCategory ⋙
    ((intDerivedTensorProduct J).tensor.obj
      ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ⋙
      (moduleEquivalence J).functor.mapDerivedCategory

/-- `- ⊗^{L}_ℤ K` commutes with the shift. -/
instance commShift_derivedTensorFlipObj (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).flip.obj K).CommShift ℤ :=
  inferInstanceAs ((flipComp J K).CommShift ℤ)

/-- `K ⊗^{L}_ℤ -` commutes with the shift. -/
instance commShift_derivedTensorObj (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).obj K).CommShift ℤ :=
  inferInstanceAs ((objComp J K).CommShift ℤ)

/-- **`- ⊗^{L}_ℤ K` is exact**: it is an exact functor of triangulated categories. -/
instance isTriangulated_derivedTensorFlipObj (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).flip.obj K).IsTriangulated :=
  inferInstanceAs ((flipComp J K).IsTriangulated)

/-- **`K ⊗^{L}_ℤ -` is exact**: it is an exact functor of triangulated categories. -/
instance isTriangulated_derivedTensorObj (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).obj K).IsTriangulated :=
  inferInstanceAs ((objComp J K).IsTriangulated)

/-! ### Direct sums -/

/-- **`- ⊗^{L}_ℤ K` commutes with countable direct sums**, and more generally with direct sums
indexed by any type in `Type`. The two conjugating functors are equivalences, so they commute
with every colimit; the content is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesColimitsCountable_tensorFlipObj`
for the derived tensor product on sheaves of modules. -/
theorem preservesCountableCoproducts_derivedTensorFlipObj
    (K : DerivedCategory (Sheaf J Ab.{u})) (I : Type) :
    PreservesColimitsOfShape (Discrete I) ((derivedTensor J).flip.obj K) := by
  have h₁ : (moduleEquivalence J).inverse.mapDerivedCategory.IsEquivalence :=
    Stacks.Cohomology.isEquivalence_mapDerivedCategory (moduleEquivalence J).inverse
  have h₂ : (moduleEquivalence J).functor.mapDerivedCategory.IsEquivalence :=
    Stacks.Cohomology.isEquivalence_mapDerivedCategory (moduleEquivalence J).functor
  have h₃ := DerivedTensorProduct.preservesColimitsCountable_tensorFlipObj (intRingSheaf J)
    (intDerivedTensorProduct J) ((moduleEquivalence J).inverse.mapDerivedCategory.obj K) I
  exact inferInstanceAs (PreservesColimitsOfShape (Discrete I) (flipComp J K))

/-! ### The unit -/

/-- The site equipped with the constant sheaf of rings `ℤ`, as a ringed site. -/
abbrev intRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} where
  C := C
  J := J
  O := intRingSheaf J

/-- The constant sheaf `ℤ` as an abelian sheaf: the structure sheaf of `intRingedSite`, read
through the equivalence. -/
abbrev intSheaf : Sheaf J Ab.{u} :=
  (moduleEquivalence J).functor.obj (SheafOfModules.unit (intRings J))

/-- The scalars of the constant sheaf of rings `ℤ`, read as a map of abelian presheaves. -/
def intSheafScalars :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (intSheaf J).obj :=
  Functor.whiskerRight (intRingSheafScalars J) (forget₂ RingCat AddCommGrpCat)

/-- The scalars `intSheafScalars` are locally surjective. -/
instance isLocallySurjective_intSheafScalars :
    Presheaf.IsLocallySurjective J (intSheafScalars J) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective J
    (Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))))
      (forget CommRingCat))
  infer_instance

/-- The scalars `intSheafScalars` are locally injective. -/
instance isLocallyInjective_intSheafScalars :
    Presheaf.IsLocallyInjective J (intSheafScalars J) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective J
    (Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))))
      (forget CommRingCat))
  infer_instance

/-- **The unit is the constant sheaf `ℤ`.** The abelian sheaf underlying the structure sheaf of
the ringed site with the constant sheaf of rings `ℤ` is the constant abelian sheaf `ℤ`: the
scalars of the one are the sheafification unit of the other, which is locally bijective, and
both are sheaves. -/
def intSheafIsoConstantSheaf :
    (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ≅ intSheaf J :=
  @asIso _ _ _ _ ((presheafToSheaf J Ab.{u}).map (intSheafScalars J))
      ((J.W_iff _).mp (GrothendieckTopology.W_of_isLocallyBijective J (intSheafScalars J))) ≪≫
    asIso ((sheafificationAdjunction J Ab.{u}).counit.app (intSheaf J))

/-- The constant sheaf `ℤ` placed in degree zero: the unit of `- ⊗^{L}_ℤ -`. -/
abbrev unitObject : DerivedCategory (Sheaf J Ab.{u}) :=
  (DerivedCategory.singleFunctor (Sheaf J Ab.{u}) 0).obj (intSheaf J)

/-- The data exhibiting `e⁻¹ ⋙ e` on derived categories as a lift of the corresponding
composite on complexes, where `e` is `moduleEquivalence`. -/
def derivedCounitLifting :
    DerivedCategory.Q ⋙ ((moduleEquivalence J).inverse.mapDerivedCategory ⋙
        (moduleEquivalence J).functor.mapDerivedCategory) ≅
      (moduleEquivalence J).inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (moduleEquivalence J).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEquivalence J).inverse.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (moduleEquivalence J).functor.mapDerivedCategoryFactors

/-- `e⁻¹ ⋙ e` on complexes is the identity up to the counit of `e`, where `e` is
`moduleEquivalence`. -/
def complexCounitIso :
    (moduleEquivalence J).inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (moduleEquivalence J).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ≅
      DerivedCategory.Q (C := Sheaf J Ab.{u}) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((moduleEquivalence J).mapHomologicalComplex (ComplexShape.up ℤ)).counitIso
      DerivedCategory.Q ≪≫
      Functor.leftUnitor _

/-- **The equivalence of abelian sheaves with modules over the constant sheaf `ℤ` is an
equivalence of derived categories**, in the form needed below: the composite of the two induced
functors is the identity. -/
def derivedCounitIso :
    (moduleEquivalence J).inverse.mapDerivedCategory ⋙
        (moduleEquivalence J).functor.mapDerivedCategory ≅
      𝟭 (DerivedCategory (Sheaf J Ab.{u})) :=
  letI : Localization.Lifting (DerivedCategory.Q (C := Sheaf J Ab.{u}))
      (HomologicalComplex.quasiIso (Sheaf J Ab.{u}) (ComplexShape.up ℤ))
      ((moduleEquivalence J).inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (moduleEquivalence J).functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)
      ((moduleEquivalence J).inverse.mapDerivedCategory ⋙
        (moduleEquivalence J).functor.mapDerivedCategory) := ⟨derivedCounitLifting J⟩
  Localization.liftNatIso (DerivedCategory.Q (C := Sheaf J Ab.{u}))
    (HomologicalComplex.quasiIso (Sheaf J Ab.{u}) (ComplexShape.up ℤ)) _ _ _ _
    (complexCounitIso J)

/-- The unit of `- ⊗^{L}_ℤ -` corresponds, across the equivalence, to the structure sheaf of
the ringed site with the constant sheaf of rings `ℤ`. -/
def inverseUnitObjectIso :
    (moduleEquivalence J).inverse.mapDerivedCategory.obj (unitObject J) ≅
      RingedSite.unitObject (intRingedSite J) :=
  ((moduleEquivalence J).inverse.mapDerivedCategorySingleFunctor 0).app (intSheaf J) ≪≫
    (DerivedCategory.singleFunctor (Modules (intRingSheaf J)) 0).mapIso
      (((moduleEquivalence J).unitIso.app (SheafOfModules.unit (intRings J))).symm)

/-- **`ℤ ⊗^{L}_ℤ K ≅ K`**: the constant sheaf `ℤ` in degree zero is a unit for the derived
tensor product of abelian sheaves. -/
def leftUnitIso (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).obj (unitObject J)).obj K ≅ K :=
  (moduleEquivalence J).functor.mapDerivedCategory.mapIso
      ((((intDerivedTensorProduct J).tensor.mapIso (inverseUnitObjectIso J)).app
        ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ≪≫
        DerivedTensorProduct.leftUnitIso (intRingedSite J) (intDerivedTensorProduct J)
          ((moduleEquivalence J).inverse.mapDerivedCategory.obj K)) ≪≫
    (derivedCounitIso J).app K

/-- **`ℤ ⊗^{L}_ℤ K ≅ K`**, with the unit spelled out as the constant sheaf `ℤ` rather than as
the structure sheaf of the ringed site the construction passes through. -/
def constantSheafLeftUnitIso (K : DerivedCategory (Sheaf J Ab.{u})) :
    ((derivedTensor J).obj ((DerivedCategory.singleFunctor (Sheaf J Ab.{u}) 0).obj
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))))).obj K ≅ K :=
  ((derivedTensor J).mapIso ((DerivedCategory.singleFunctor (Sheaf J Ab.{u}) 0).mapIso
    (intSheafIsoConstantSheaf J))).app K ≪≫ leftUnitIso J K

end Stacks.DerivedTensor.AbelianSheaves

end
