module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Homology.TensorComplex.CohomologyProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafExt
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal

/-!
# The cohomology product of a derived tensor product on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of `D(O_X)`. Tensoring cocycle
representatives on K-flat models gives a canonical map of sheaves of `O_X`-modules

`Hⁱ(K) ⊗_{O_X} Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^L_{O_X} L)`.

This is the sheaf-level counterpart of the product on the cohomology of a derived tensor
product of complexes of modules over a commutative ring.

Composing it with the map induced by the derived composition morphism of Stacks 0A8V gives the
multiplication on Ext sheaves,

`Ext^a_{O_X}(L, M) ⊗_{O_X} Ext^b_{O_X}(K, L) ⟶ Ext^{a + b}_{O_X}(K, M)`.

## Main definitions

* `Stacks.SheafOfModules.tensorComplexHomology`: the product at the level of complexes, for the
  total tensor complex.
* `Stacks.SheafOfModules.derivedCohomologyTensorProduct`: the product on the cohomology sheaves
  of a derived tensor product.
* `Stacks.SheafOfModules.sheafExtProduct`: the composition product on Ext sheaves.
* `Stacks.SheafOfModules.selfSheafExtProduct`: its self-Ext case, the multiplication of the
  Ext algebra of a single object.

## Implementation notes

The construction at the level of complexes is `CochainComplex.tensorHomology`, which is stated
for an arbitrary monoidal preadditive category with homology; what this file adds is the
monoidal seating of `Mod(O_X)` on the sheafified tensor product and the passage from complexes
to the derived category.

The monoidal structure on `Mod(O_X)` is a named local instance rather than a synthesized one,
as in the internal Hom development: the universes of the site `Opens X` and of the sections of
`O_X` coincide, so instance search would have to solve `max ?u ?v =?= u` with both unknown.

The passage to the derived category chooses the K-flat models supplied by the ringed site, and
transports the complex-level product along the comparison isomorphisms identifying the derived
tensor product of two K-flat complexes with their total tensor complex. No coherence across
different choices of model is asserted.

**Why the total tensor complex is named at this file's spelling.** The chosen K-flat
representative `Stacks.SheafOfModules.kFlatRepresentative` is stated over
`SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc)`, which pairs
`Rc.obj ⋙ forget₂ CommRingCat RingCat` with the sheaf condition directly, whereas the monoidal
structure above is `monoidalSpace'` over `StructureSheafModules Rc`, i.e. over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`. The two sheaves of rings are the same
sheaf, but `Tensor.ringSheaf` is a plain `def`, so seeing it needs default transparency, which
*elaboration* has and instance search does not; and the two spellings differ in an explicit
argument of `SheafOfModules`, so the goal's discrimination key is computed at the first spelling
and the `*Space'` instances carried at the second are never retrieved. No transparency attribute
helps, and nothing is missing from the library: the monoidal structure at the first spelling is
`SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc`, which
typechecks there and which search cannot reach for the universe reason recorded above.

So the two kinds of crossing are each resolved at elaboration time, with no instance registered
and no term changed. Where the category of the result is still a metavariable — the applications
of `HomologicalComplex.tensorObj` — the application is ascribed to
`CochainComplex (StructureSheafModules Rc) ℤ`: the expected type is propagated into it before
its arguments are elaborated, so its category and that category's instance come out as this
file's, and the representatives are then checked against a concrete type at default
transparency. Where the category is read off an argument whose type is already fixed — `⊗ᵢ`,
`⊗ₘ` and `CochainComplex.tensorCycles` — ascription cannot redirect it, because the application
elaborator takes the category from the argument's own inferred type; there the monoidal witness
is handed over positionally instead, with the category and preadditive slots left to resolve as
they did before. This is the device the sibling
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCohomologyProductNaturality` uses for
the same crossing, in the form of a functor ascription on `Tensor.sheafTensor`.

`CategoryTheory.sheafCompose` and `Stacks.SheafOfModules.Tensor.ringSheaf` are made
`instance_reducible` for this file, as they are in that sibling. That is not what clears the
instances above — it cannot, for the discrimination-key reason just given — but the last `rw` of
`homologyπ_derivedCohomologyTensorProduct` needs it: keyed matching runs at `instances`
transparency, and without it the pattern of `homologyπ_tensorComplexHomology` is not found in a
goal whose complexes are spelled through `Tensor.ringSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

attribute [local instance] monoidalSpace' symmetricSpace' monoidalPreadditiveSpace'
  monoidalClosedSpace'

/-- `- ⊗_{O_X} 𝒢` commutes with colimits. -/
local instance preservesColimitTensorRightSpace' {T : Type*} [Category T]
    (F : T ⥤ StructureSheafModules Rc) (N : StructureSheafModules Rc) :
    PreservesColimit F (tensorRight N) :=
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
    (J := Opens.grothendieckTopology X) Rc F N

/-- `- ⊗_{O_X} 𝒢` commutes with finite colimits. -/
local instance preservesFiniteColimitsTensorRight'
    (N : StructureSheafModules Rc) : PreservesFiniteColimits (tensorRight N) where
  preservesFiniteColimits _ := ⟨fun {_} => inferInstance⟩

/-- `𝒢 ⊗_{O_X} -` commutes with finite colimits: the symmetry identifies it with
`- ⊗_{O_X} 𝒢`. -/
local instance preservesFiniteColimitsTensorLeft'
    (N : StructureSheafModules Rc) : PreservesFiniteColimits (tensorLeft N) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm

/-- The product on the homology sheaves of a total tensor complex of complexes of
`O_X`-modules, `Hⁱ(P) ⊗_{O_X} Hʲ(Q) ⟶ Hⁱ⁺ʲ(Tot(P ⊗_{O_X} Q))`, induced by tensoring
cocycles. -/
def tensorComplexHomology (P Q : CochainComplex (StructureSheafModules Rc) ℤ) (i j : ℤ) :
    P.homology i ⊗ Q.homology j ⟶ (HomologicalComplex.tensorObj P Q).homology (i + j) :=
  CochainComplex.tensorHomology P Q i j

/-- The defining property of the product on the homology of a total tensor complex: it sends
the tensor of the classes of two cocycles to the class of the tensor of those cocycles. -/
theorem homologyπ_tensorComplexHomology
    (P Q : CochainComplex (StructureSheafModules Rc) ℤ) (i j : ℤ) :
    (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ tensorComplexHomology Rc P Q i j =
      CochainComplex.tensorCycles P Q i j ≫
        (HomologicalComplex.tensorObj P Q).homologyπ (i + j) :=
  CochainComplex.homologyπ_tensorHomology P Q i j

/-- The chosen K-flat representative of an object of `D(O_X)` does represent it. -/
def kFlatRepresentativeIso (K : DerivedCategory (StructureSheafModules Rc)) :
    DerivedCategory.Q.obj (kFlatRepresentative Rc K) ≅ K :=
  RingedSite.kFlatModelIso (ringedSite Rc) K

/-- The chosen K-flat representative is K-flat. -/
theorem isKFlat_kFlatRepresentative (K : DerivedCategory (StructureSheafModules Rc)) :
    IsKFlat (ringedSite Rc).O (kFlatRepresentative Rc K) :=
  RingedSite.isKFlat_kFlatModel (ringedSite Rc) K

/-- The comparison identifying the derived tensor product of two objects of `D(O_X)` with the
class of the total tensor complex of their chosen K-flat representatives. -/
def derivedTensorKFlatRepresentativeIso
    (K L : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj K).obj L ≅
      DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)) :=
  (((derivedTensor Rc).mapIso (kFlatRepresentativeIso Rc K).symm).app L) ≪≫
    (((derivedTensor Rc).obj
      (DerivedCategory.Q.obj (kFlatRepresentative Rc K))).mapIso
        (kFlatRepresentativeIso Rc L).symm) ≪≫
    (canonicalDerivedTensorProduct (ringedSite Rc)).comparison
      (kFlatRepresentative Rc K) (kFlatRepresentative Rc L)
      (isKFlat_kFlatRepresentative Rc K) (isKFlat_kFlatRepresentative Rc L)

/-- The cohomology sheaves of an object of `D(O_X)` are those of its chosen K-flat
representative. -/
def homologyKFlatRepresentativeIso (K : DerivedCategory (StructureSheafModules Rc)) (i : ℤ) :
    (kFlatRepresentative Rc K).homology i ≅
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).obj K :=
  ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).symm.app
      (kFlatRepresentative Rc K)) ≪≫
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).mapIso
      (kFlatRepresentativeIso Rc K)

/-- The cohomology sheaf of a derived tensor product, read on the total tensor complex of the
chosen K-flat representatives. -/
def homologyDerivedTensorKFlatIso
    (K L : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).obj
        (((derivedTensor Rc).obj K).obj L) ≅
      (HomologicalComplex.tensorObj (kFlatRepresentative Rc K) (kFlatRepresentative Rc L) :
        CochainComplex (StructureSheafModules Rc) ℤ).homology n :=
  (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).mapIso
      (derivedTensorKFlatRepresentativeIso Rc K L) ≪≫
    (DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) n).app
      (HomologicalComplex.tensorObj
        (kFlatRepresentative Rc K) (kFlatRepresentative Rc L))

/-- **The cohomology product of a derived tensor product on a ringed space.** For objects `K`,
`L` of `D(O_X)`, tensoring cocycle representatives on K-flat models gives a canonical map of
sheaves of `O_X`-modules

`Hⁱ(K) ⊗_{O_X} Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^L_{O_X} L)`.

This is the sheaf-level counterpart of the cohomology product of a derived tensor product of
complexes of modules over a commutative ring. Composed with the derived composition morphism
of Stacks 0A8V it produces the multiplication on the Ext sheaves of a ringed space. -/
def derivedCohomologyTensorProduct
    (K L : DerivedCategory (StructureSheafModules Rc)) (i j : ℤ) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).obj K ⊗
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) j).obj L ⟶
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).obj
        (((derivedTensor Rc).obj K).obj L) :=
  (@tensorIso _ _ (monoidalSpace' Rc) _ _ _ _ (homologyKFlatRepresentativeIso Rc K i)
      (homologyKFlatRepresentativeIso Rc L j)).inv ≫
    tensorComplexHomology Rc (kFlatRepresentative Rc K) (kFlatRepresentative Rc L) i j ≫
      (homologyDerivedTensorKFlatIso Rc K L (i + j)).inv

/-- The cohomology product is, on the chosen K-flat representatives, the product induced by
tensoring cocycles: it sends the tensor of the classes of two cocycles to the class of the
tensor of those cocycles. -/
theorem homologyπ_derivedCohomologyTensorProduct
    (K L : DerivedCategory (StructureSheafModules Rc)) (i j : ℤ) :
    @MonoidalCategoryStruct.tensorHom _ _ (monoidalSpace' Rc).toMonoidalCategoryStruct _ _ _ _
          ((kFlatRepresentative Rc K).homologyπ i) ((kFlatRepresentative Rc L).homologyπ j) ≫
        (@tensorIso _ _ (monoidalSpace' Rc) _ _ _ _ (homologyKFlatRepresentativeIso Rc K i)
          (homologyKFlatRepresentativeIso Rc L j)).hom ≫
        derivedCohomologyTensorProduct Rc K L i j =
      @CochainComplex.tensorCycles _ _ _ (monoidalSpace' Rc) (monoidalPreadditiveSpace' Rc) _
          (inferInstanceAs ((curriedTensor (StructureSheafModules Rc)).Additive)) _
          (kFlatRepresentative Rc K) (kFlatRepresentative Rc L) _ i j ≫
        (HomologicalComplex.tensorObj (kFlatRepresentative Rc K) (kFlatRepresentative Rc L) :
            CochainComplex (StructureSheafModules Rc) ℤ).homologyπ (i + j) ≫
          (homologyDerivedTensorKFlatIso Rc K L (i + j)).inv := by
  rw [derivedCohomologyTensorProduct]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, homologyπ_tensorComplexHomology, Category.assoc]

/-! ### The composition product on Ext sheaves -/

/-- **The composition product on the Ext sheaves of a ringed space.** For objects `K`, `L`, `M`
of `D(O_X)` the derived composition morphism of Stacks 0A8V,

`RSheafHom(L, M) ⊗^L_{O_X} RSheafHom(K, L) ⟶ RSheafHom(K, M)`,

induces on cohomology sheaves the multiplication

`Ext^a_{O_X}(L, M) ⊗_{O_X} Ext^b_{O_X}(K, L) ⟶ Ext^{a + b}_{O_X}(K, M)`,

obtained by first applying the cohomology product of the derived tensor product and then the
map induced by composition. -/
def sheafExtProduct (K L M : DerivedCategory (StructureSheafModules Rc)) (a b : ℤ) :
    derivedSheafExt Rc L M a ⊗ derivedSheafExt Rc K L b ⟶ derivedSheafExt Rc K M (a + b) :=
  derivedCohomologyTensorProduct Rc
      (((derivedSheafHom Rc).obj (op L)).obj M)
      (((derivedSheafHom Rc).obj (op K)).obj L) a b ≫
    derivedSheafExtComposition Rc K L M (a + b)

/-- The composition product on Ext sheaves is the cohomology product of the derived tensor
product followed by the map induced by derived composition. -/
theorem sheafExtProduct_eq (K L M : DerivedCategory (StructureSheafModules Rc)) (a b : ℤ) :
    sheafExtProduct Rc K L M a b =
      derivedCohomologyTensorProduct Rc
          (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) a b ≫
        derivedSheafExtComposition Rc K L M (a + b) :=
  rfl

/-- The composition product on Ext sheaves is contravariant in the source object. -/
theorem sheafExtProduct_natural_source
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K)
    (L M : DerivedCategory (StructureSheafModules Rc)) (a b : ℤ) :
    sheafExtProduct Rc K L M a b ≫ derivedSheafExtMap Rc (a + b) k (𝟙 M) =
      derivedCohomologyTensorProduct Rc
          (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) a b ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (a + b)).map
          (derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M))
            (derivedSheafHomMap Rc k (𝟙 L))) ≫
        derivedSheafExtComposition Rc K' L M (a + b) := by
  rw [sheafExtProduct_eq, Category.assoc,
    derivedSheafExtComposition_natural_source]

/-- The composition product on Ext sheaves is covariant in the target object. -/
theorem sheafExtProduct_natural_target
    (K L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M') (a b : ℤ) :
    sheafExtProduct Rc K L M a b ≫ derivedSheafExtMap Rc (a + b) (𝟙 K) m =
      derivedCohomologyTensorProduct Rc
          (((derivedSheafHom Rc).obj (op L)).obj M)
          (((derivedSheafHom Rc).obj (op K)).obj L) a b ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (a + b)).map
          (derivedTensorMap Rc (derivedSheafHomMap Rc (𝟙 L) m)
            (𝟙 (((derivedSheafHom Rc).obj (op K)).obj L))) ≫
        derivedSheafExtComposition Rc K L M' (a + b) := by
  rw [sheafExtProduct_eq, Category.assoc,
    derivedSheafExtComposition_natural_target]

/-- The self-Ext sheaves of an object of `D(O_X)`, with the multiplication given by the
composition product: `Ext^a(K, K) ⊗_{O_X} Ext^b(K, K) ⟶ Ext^{a + b}(K, K)`. -/
abbrev selfSheafExtProduct (K : DerivedCategory (StructureSheafModules Rc)) (a b : ℤ) :
    derivedSheafExt Rc K K a ⊗ derivedSheafExt Rc K K b ⟶ derivedSheafExt Rc K K (a + b) :=
  sheafExtProduct Rc K K K a b

end Stacks.SheafOfModules

end
