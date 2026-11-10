module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMapAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import StacksFrontier.Homology.TensorComplex.CohomologyProduct

/-!
# The composition product on the cohomology of an internal Hom complex, on a ringed site

Let `X` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. The internal Hom
complexes carry the composition morphism of Stacks 0A91 out of the total tensor product
`SheafHom^•(L, M) ⊗_O SheafHom^•(K, L)`, and the cohomology sheaves of a total tensor complex
carry the product induced by tensoring cocycles (`CochainComplex.tensorHomology`). Composing the
two gives the composition pairing on cohomology sheaves,

`Hⁱ(SheafHom(L, M)) ⊗_O Hʲ(SheafHom(K, L)) ⟶ Hⁱ⁺ʲ(SheafHom(K, M))`.

Taking `K = L = M = P` is the diagonal instance, a product on the cohomology sheaves of
`SheafHom^•(P, P)`, and that is the one assembled into a graded algebra below.

This is the ringed-*site* form of the development in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct`, which states
the same product for a ringed *space*. Nothing here is space-specific: every chain-level input —
`AlgebraicGeometry.RingedSite.compositionMap`, its associativity and its unitality on local
sections — is a statement about a ringed site, and so are the monoidal structure on `Mod(O)` and
the sheafification machinery. The point of having it at this generality is the **slice site**:
`AlgebraicGeometry.RingedSite.over` of a ringed site is a ringed site but not a ringed space, so
the graded algebra of the restriction of a complex to a slice can be written down here and
cannot be written down there. That is what the comparison of the composition product with slice
restriction (`AlgebraicGeometry.RingedSite.compositionMap_over`,
`AlgebraicGeometry.RingedSite.homologyMap_compositionMap_over`,
`AlgebraicGeometry.RingedSite.sheafHomHomologyOverIso`) is for.

## Main definitions

* `AlgebraicGeometry.RingedSite.homologyComposition`: **the composition pairing on the cohomology
  sheaves of internal Hom complexes**, for three complexes `K`, `L`, `M`.
* `AlgebraicGeometry.RingedSite.homologyMul`: the same pairing as a bilinear map on local
  sections, which is the shape the multiplication field of `SheafOfModules.GradedAlgebra` takes.
* `AlgebraicGeometry.RingedSite.homologyOne`: **the unit**, the class of the identity.
* `AlgebraicGeometry.RingedSite.homologyGradedAlgebra`: **the graded algebra on the cohomology
  sheaves of `SheafHom(P, P)`**, the diagonal instance of the pairing.

## Main results

* `AlgebraicGeometry.RingedSite.homologyπ_homologyComposition`: **the defining property** — the
  pairing sends the tensor of the classes of two cocycles to the class of their composite.
* `AlgebraicGeometry.RingedSite.compositionTotalMap_tensorPairSection`: **the composition
  morphism sends a local pure tensor of the total tensor product to the composite of its
  factors.** This is the bridge between the two spellings of the total tensor product, and it is
  what reduces any computation with the pairing to the pairing on local sections.
* `AlgebraicGeometry.RingedSite.homologyMul_assoc`: **the product is associative**, and
  `AlgebraicGeometry.RingedSite.homologyMul_one_mul` with
  `AlgebraicGeometry.RingedSite.homologyMul_mul_one`: **the class of the identity is a two-sided
  unit**. Each is proved on classes of cocycles and then lifted, the lift being local.
* `AlgebraicGeometry.RingedSite.eq_of_forall_lift₃`: the three-section lifting principle the
  associativity descent needs, with three possibly different locally surjective morphisms.

## Implementation notes

**Why the product is assembled at the level of complexes and not in the derived category.** The
Ext sheaves already carry a composition product built from the derived composition morphism of
Stacks 0A8V. That product is unusable for an associativity statement: establishing associativity
of the derived composition requires the clause of Tag 0FPT computing the derived associator on
K-flat representatives, which
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity` records as absent. The
product below is instead induced by `AlgebraicGeometry.RingedSite.compositionMap`, a morphism of
complexes, whose associativity and unitality on local sections are available
(`AlgebraicGeometry.RingedSite.compositionMap_assoc`,
`AlgebraicGeometry.RingedSite.compositionMap_idSection_left` and `..._right`).

**The two spellings of the total tensor product.** `CochainComplex.tensorHomology` lands in the
cohomology of `HomologicalComplex.tensorObj`, which is the degreewise sheaf tensor product
totalised, whereas `AlgebraicGeometry.RingedSite.compositionMap` is defined out of
`AlgebraicGeometry.RingedSite.tensorTotal`, which totalises the presheaf tensor products and
sheafifies afterwards. The two are identified by
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, and that isomorphism is the only
transport in the definition below.

**How the three laws are proved, and why not by cancelling an epimorphism.** Each law is first
proved on *classes of cocycles*, where the product is computed by `homologyMul_app_homologyπ`,
the resulting cycle is computed inside the complex by `iCycles_cycleComposition_pureSection`, and
the identity to be checked is the corresponding law for the pairing on local sections. It is then
extended to arbitrary cohomology sections by lifting them to cocycles on a common refinement:
`homologyπ` is an epimorphism, hence locally surjective, and the covering sieves so produced are
intersected. The alternative — phrasing each law as an identity of morphisms out of a triple
tensor product and cancelling `homologyπ ⊗ homologyπ ⊗ homologyπ` — would additionally need the
associator of the sheaf tensor product on *complexes*, and that associator admits no description
on local sections: `tensorHom_pureSection` holds for `⊗ₘ` precisely because the re-seated
whiskerings are sheafifications of the objectwise ones, and the associator of the same re-seated
structure is a genuine conjugate for which no such statement is available.

**Why the two halves of the descent have the shapes they do.** `castHom_compositionSection` is a
single `subst` only because the total degree of
`AlgebraicGeometry.RingedSite.compositionSection` is a parameter constrained by a hypothesis
rather than a value computed from the two factor degrees; that is the device which makes
`AlgebraicGeometry.RingedSite.compositionSection_assoc` an honest equality instead of an `HEq`,
and transporting the total degree is then proof irrelevance and nothing more. At the other end,
the cycles are compared by `Stacks.SheafOfModules.injective_app_of_mono`, whose own docstring
records that there is deliberately no epimorphism analogue — finite limits of sheaves of modules
need no sheafification, finite colimits do. That is the same fact which forced this descent to
lift sections locally rather than cancel an epimorphism of sheaves.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `⊗_O` is additive in its first variable. -/
local instance sheafTensorAdditive' :
    (_root_.Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive :=
  _root_.Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} (J := X.J) X.O

/-- `ℱ ⊗_O -` is additive. -/
local instance sheafTensorObjAdditive'
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((_root_.Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive :=
  _root_.Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} (J := X.J) X.O A

/-- The monoidal structure on `Mod(O)` whose tensor product is `⊗_O`. -/
local instance monoidalSite' :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.monoidalCategorySheafTensor (J := X.J) X.O

/-- `⊗_O` is symmetric. -/
local instance symmetricSite' :
    SymmetricCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.symmetricCategorySheafTensor (J := X.J) X.O

/-- `⊗_O` is bilinear on morphisms. -/
local instance monoidalPreadditiveSite' :
    MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.monoidalPreadditiveSheafTensor (J := X.J) X.O

/-- `Mod(O)` is monoidal closed. -/
local instance monoidalClosedSite' :
    MonoidalClosed (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  SheafOfModules.monoidalClosedSheafTensor (J := X.J) X.O

/-- `- ⊗_O 𝒢` commutes with colimits. -/
local instance preservesColimitTensorRightSite' {T : Type*} [Category T]
    (F : T ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesColimit F (tensorRight N) :=
  SheafOfModules.preservesColimit_tensorRight_sheafTensor (J := X.J) X.O F N

/-- `- ⊗_O 𝒢` commutes with finite colimits. -/
local instance preservesFiniteColimitsTensorRightSite'
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesFiniteColimits (tensorRight N) where
  preservesFiniteColimits _ := ⟨fun {_} => inferInstance⟩

/-- `𝒢 ⊗_O -` commutes with finite colimits: the symmetry identifies it with `- ⊗_O 𝒢`. -/
local instance preservesFiniteColimitsTensorLeftSite'
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesFiniteColimits (tensorLeft N) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm

/-- Sheafification of presheaves of modules is additive, at the spelling in which the
total-complex comparison is stated. The universes of the site and of the sections of `O`
coincide, so instance search would have to solve `max ?u ?v =?= u` with both unknown; this is a
named local instance for the same reason as the monoidal ones above. -/
local instance sheafificationAdditive' :
    (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).Additive :=
  PresheafOfModules.sheafification_additive (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)

/-- The composition morphism of internal Hom complexes of Stacks 0A91, read on the total tensor
product of `SheafHom^•(L, M)` and `SheafHom^•(K, L)` in the spelling
`HomologicalComplex.tensorObj` that the cohomology product uses. The only content is the
identification `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` of the two total
tensor complexes. -/
def compositionTotalMap
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    HomologicalComplex.tensorObj (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj ⟶
      (sheafHomComplex X K M).obj :=
  (tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj).inv ≫
    compositionMap X K L M

/-- **The composition pairing on the cohomology sheaves of internal Hom complexes.** It is the
product induced by tensoring cocycles, followed by the map that the composition morphism of
internal Hom complexes of Stacks 0A91 induces on cohomology,

`Hⁱ(SheafHom(L, M)) ⊗_O Hʲ(SheafHom(K, L)) ⟶ Hⁱ⁺ʲ(SheafHom(K, M))`.

The diagonal instance `K = L = M = P` is the composition product on the cohomology sheaves of
`SheafHom^•(P, P)` that `AlgebraicGeometry.RingedSite.homologyGradedAlgebra` is built from. -/
def homologyComposition
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i j : ℤ) :
    (sheafHomComplex X L M).obj.homology i ⊗ (sheafHomComplex X K L).obj.homology j ⟶
      (sheafHomComplex X K M).obj.homology (i + j) :=
  CochainComplex.tensorHomology (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj i j ≫
    HomologicalComplex.homologyMap (compositionTotalMap X K L M) (i + j)

/-- **The defining property of the composition pairing on cohomology:** it sends the tensor of
the classes of two cocycles to the class of their composite, the composite being taken by the
composition morphism of internal Hom complexes of Stacks 0A91. -/
theorem homologyπ_homologyComposition
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i j : ℤ) :
    ((sheafHomComplex X L M).obj.homologyπ i ⊗ₘ
          (sheafHomComplex X K L).obj.homologyπ j) ≫ homologyComposition X K L M i j =
      CochainComplex.tensorCycles (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj i j ≫
        (HomologicalComplex.tensorObj (sheafHomComplex X L M).obj
            (sheafHomComplex X K L).obj).homologyπ (i + j) ≫
          HomologicalComplex.homologyMap (compositionTotalMap X K L M) (i + j) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg
          (fun z => z ≫ HomologicalComplex.homologyMap (compositionTotalMap X K L M) (i + j))
          (CochainComplex.homologyπ_tensorHomology (sheafHomComplex X L M).obj
            (sheafHomComplex X K L).obj i j)).trans
      (Category.assoc _ _ _))

/-- **The composition pairing on cohomology, as a bilinear map on local sections.** This is the
shape the multiplication field of `SheafOfModules.GradedAlgebra` takes: a map on sections,
additive and `O`-linear in each variable and compatible with restriction, rather than a morphism
out of a tensor product.

The sheaf tensor product is the sheafification of the objectwise one, so a morphism out of it
restricts along the unit of the sheafification adjunction to a morphism out of the objectwise
tensor product, and `PresheafOfModules.toBilinear` reads that off as a bilinear map. -/
def homologyMul
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i j : ℤ) :
    _root_.Stacks.BilinearMap
      ((sheafHomComplex X L M).obj.homology i).val
      ((sheafHomComplex X K L).obj.homology j).val
      ((sheafHomComplex X K M).obj.homology (i + j)).val :=
  PresheafOfModules.toBilinear
    ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (((sheafHomComplex X L M).obj.homology i).val ⊗
          ((sheafHomComplex X K L).obj.homology j).val) ≫
      (homologyComposition X K L M i j).val)

section Summand

variable
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The presheaf-level double complex of tensor products whose two totalisations are the two
spellings of the total tensor product of `SheafHom^•(L, M)` and `SheafHom^•(K, L)`. -/
abbrev tensorPairBicomplex :=
  presheafTensorBicomplex X (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj

/-- The summand inclusion of the total tensor product, in the bicomplex spelling in which the
comparison of the two total complexes is stated. It is the monoidal summand inclusion
`HomologicalComplex.ιTensorObj`. -/
abbrev ιTensorPair (i j : ℤ) :=
  (HomologicalComplex₂.TotalMap.mapBicomplex
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
      (tensorPairBicomplex X K L M)).ιTotal (ComplexShape.up ℤ) i j (i + j) rfl

/-- The monoidal summand inclusion `HomologicalComplex.ιTensorObj` of the total tensor product
is `ιTensorPair`. -/
theorem ιTensorObj_eq_ιTensorPair (i j : ℤ) :
    HomologicalComplex.ιTensorObj (sheafHomComplex X L M).obj
        (sheafHomComplex X K L).obj i j (i + j) rfl =
      ιTensorPair X K L M i j :=
  rfl

/-- In each degree, `compositionTotalMap` is the comparison of the two total tensor complexes,
`HomologicalComplex₂.TotalMap.totalMapf`, followed by `compositionMap`. -/
theorem compositionTotalMap_f (n : ℤ) :
    (compositionTotalMap X K L M).f n =
      HomologicalComplex₂.TotalMap.totalMapf
          (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
          (tensorPairBicomplex X K L M) n ≫
        (compositionMap X K L M).f n :=
  rfl

/-- On the degree-`(i, j)` summand, the composition morphism read on the total tensor product is
the sheafification of the presheaf-level summand inclusion followed by the composition morphism
of Stacks 0A91. This is the summand compatibility of the comparison of the two total tensor
complexes, which is `HomologicalComplex₂.TotalMap.ι_totalMapf`. -/
theorem ι_compositionTotalMap (i j : ℤ) :
    ιTensorPair X K L M i j ≫ (compositionTotalMap X K L M).f (i + j) =
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
          ((tensorPairBicomplex X K L M).ιTotal (ComplexShape.up ℤ) i j (i + j) rfl) ≫
        (compositionMap X K L M).f (i + j) := by
  rw [compositionTotalMap_f]
  exact HomologicalComplex₂.TotalMap.ι_totalMapf_assoc
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj))
    (tensorPairBicomplex X K L M) (i + j) i j rfl ((compositionMap X K L M).f (i + j))

/-- **The local pure tensor in the degree-`(i, j)` summand of the total tensor product of
`SheafHom^•(L, M)` and `SheafHom^•(K, L)`.** These sections generate the total tensor product,
and they are what the cohomology pairing is computed on. -/
def tensorPairSection (i j : ℤ) (U : X.C)
    (β : ((sheafHomComplex X L M).obj.X i).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X j).val.obj (op U)) :
    ((HomologicalComplex.tensorObj (sheafHomComplex X L M).obj
      (sheafHomComplex X K L).obj).X (i + j)).val.obj (op U) :=
  (ιTensorPair X K L M i j).val.app (op U)
    (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (((sheafHomComplex X L M).obj.X i).val ⊗
          ((sheafHomComplex X K L).obj.X j).val)).app (op U)
      (β ⊗ₜ[X.O.obj.obj (op U)] γ))

/-- **The composition morphism sends a local pure tensor of the total tensor product to the
composite of its factors.** This is the bridge between the two spellings of the total tensor
product: the monoidal one, in which the cohomology product of `CochainComplex.tensorHomology` is
stated, and `AlgebraicGeometry.RingedSite.tensorTotal`, in which the composition morphism of
Stacks 0A91 is defined. Its three ingredients are the summand compatibility of the comparison,
the naturality of the sheafification unit, and the characterisation
`AlgebraicGeometry.RingedSite.compositionMap_tensorTotalSection` of the composition morphism on
local pure tensors. -/
theorem compositionTotalMap_tensorPairSection (i j : ℤ) (U : X.C)
    (β : ((sheafHomComplex X L M).obj.X i).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X j).val.obj (op U)) :
    ((compositionTotalMap X K L M).f (i + j)).val.app (op U)
        (tensorPairSection X K L M i j U β γ) =
      compositionSection X U i j (i + j) rfl β γ :=
  (congrArg
      (fun z => (SheafOfModules.Hom.val z).app (op U)
        (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (((sheafHomComplex X L M).obj.X i).val ⊗
              ((sheafHomComplex X K L).obj.X j).val)).app (op U)
          (β ⊗ₜ[X.O.obj.obj (op U)] γ)))
      (ι_compositionTotalMap X K L M i j)).trans
    ((congrArg
        (fun y => ((compositionMap X K L M).f (i + j)).val.app (op U) y)
        (sheafification_map_unit_apply X
          ((tensorPairBicomplex X K L M).ιTotal (ComplexShape.up ℤ) i j (i + j) rfl) (op U)
          (β ⊗ₜ[X.O.obj.obj (op U)] γ))).trans
      (compositionMap_tensorTotalSection X K L M U i j β γ))

/-- **The tensor product of two morphisms, on a local pure tensor.** The sheaf tensor product is
the sheafification of the objectwise one and the re-seated whiskerings are the sheafifications of
the objectwise whiskerings, so `⊗ₘ` acts on a local pure tensor by acting on its two factors.
This holds for `⊗ₘ` but *not* for the associator; see the implementation notes. -/
theorem tensorHom_pureSection
    {M N M' N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : M ⟶ M')
    (g : N ⟶ N') (U : X.Cᵒᵖ) (a : M.val.obj U) (b : N.val.obj U) :
    ((f ⊗ₘ g).val.app U)
        (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            (M.val ⊗ N.val)).app U (a ⊗ₜ[X.O.obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (M'.val ⊗ N'.val)).app U
        ((f.val.app U a) ⊗ₜ[X.O.obj.obj U] (g.val.app U b)) := by
  rw [MonoidalCategory.tensorHom_def]
  exact (congrArg (fun y => ((M' ◁ g).val.app U) y)
      (sheafification_map_unit_apply X (f.val ▷ N.val) U
        (a ⊗ₜ[X.O.obj.obj U] b))).trans
    (sheafification_map_unit_apply X (M'.val ◁ g.val) U
      ((f.val.app U a) ⊗ₜ[X.O.obj.obj U] b))

/-- **The composition pairing at the level of cycles.** Tensoring a cycle of `SheafHom^•(L, M)`
with a cycle of `SheafHom^•(K, L)` and composing them gives a cycle of `SheafHom^•(K, M)`,
because the composition morphism is a morphism of complexes. -/
def cycleComposition (i j : ℤ) :
    (sheafHomComplex X L M).obj.cycles i ⊗ (sheafHomComplex X K L).obj.cycles j ⟶
      (sheafHomComplex X K M).obj.cycles (i + j) :=
  CochainComplex.tensorCycles (sheafHomComplex X L M).obj (sheafHomComplex X K L).obj i j ≫
    HomologicalComplex.cyclesMap (compositionTotalMap X K L M) (i + j)

/-- **The composite of two cycles is, inside the complex, the pairing of the sections they
are.** This is the computation that every statement about the pairing reduces to. -/
theorem iCycles_cycleComposition_pureSection (i j : ℤ) (U : X.C)
    (x : ((sheafHomComplex X L M).obj.cycles i).val.obj (op U))
    (y : ((sheafHomComplex X K L).obj.cycles j).val.obj (op U)) :
    (((sheafHomComplex X K M).obj.iCycles (i + j)).val.app (op U))
        ((cycleComposition X K L M i j).val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
              (((sheafHomComplex X L M).obj.cycles i).val ⊗
                ((sheafHomComplex X K L).obj.cycles j).val)).app (op U)
            (x ⊗ₜ[X.O.obj.obj (op U)] y))) =
      compositionSection X U i j (i + j) rfl
        ((((sheafHomComplex X L M).obj.iCycles i).val.app (op U)) x)
        ((((sheafHomComplex X K L).obj.iCycles j).val.app (op U)) y) := by
  have hmor :
      cycleComposition X K L M i j ≫ (sheafHomComplex X K M).obj.iCycles (i + j) =
        ((sheafHomComplex X L M).obj.iCycles i ⊗ₘ
            (sheafHomComplex X K L).obj.iCycles j) ≫
          HomologicalComplex.ιTensorObj (sheafHomComplex X L M).obj
              (sheafHomComplex X K L).obj i j (i + j) rfl ≫
            (compositionTotalMap X K L M).f (i + j) := by
    rw [cycleComposition, Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, CochainComplex.tensorCycles_i, Category.assoc]
  refine (congrArg (fun z => (SheafOfModules.Hom.val z).app (op U)
      (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          (((sheafHomComplex X L M).obj.cycles i).val ⊗
            ((sheafHomComplex X K L).obj.cycles j).val)).app (op U)
        (x ⊗ₜ[X.O.obj.obj (op U)] y))) hmor).trans ?_
  refine (congrArg (fun w => ((compositionTotalMap X K L M).f (i + j)).val.app (op U)
      ((HomologicalComplex.ιTensorObj (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj i j (i + j) rfl).val.app (op U) w))
    (tensorHom_pureSection X
      ((sheafHomComplex X L M).obj.iCycles i)
      ((sheafHomComplex X K L).obj.iCycles j) (op U) x y)).trans ?_
  exact compositionTotalMap_tensorPairSection X K L M i j U _ _

/-- **The pairing of two classes of cycles is the class of their cycle-level composite.** This
is the defining property in the form a computation on local sections uses it: it turns a value of
the pairing at two classes into a single class, whose representative
`iCycles_cycleComposition_pureSection` then computes. -/
theorem homologyMul_app_homologyπ (i j : ℤ) (U : X.C)
    (x : ((sheafHomComplex X L M).obj.cycles i).val.obj (op U))
    (y : ((sheafHomComplex X K L).obj.cycles j).val.obj (op U)) :
    (homologyMul X K L M i j).app (op U)
        (((sheafHomComplex X L M).obj.homologyπ i).val.app (op U) x)
        (((sheafHomComplex X K L).obj.homologyπ j).val.app (op U) y) =
      ((sheafHomComplex X K M).obj.homologyπ (i + j)).val.app (op U)
        ((cycleComposition X K L M i j).val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
              (((sheafHomComplex X L M).obj.cycles i).val ⊗
                ((sheafHomComplex X K L).obj.cycles j).val)).app (op U)
            (x ⊗ₜ[X.O.obj.obj (op U)] y))) := by
  have h1 :
      ((sheafHomComplex X L M).obj.homologyπ i ⊗ₘ
            (sheafHomComplex X K L).obj.homologyπ j) ≫ homologyComposition X K L M i j =
        cycleComposition X K L M i j ≫
          (sheafHomComplex X K M).obj.homologyπ (i + j) := by
    rw [homologyπ_homologyComposition, HomologicalComplex.homologyπ_naturality]
    exact (Category.assoc _ _ _).symm
  refine (congrArg (fun w => (homologyComposition X K L M i j).val.app (op U) w)
    (tensorHom_pureSection X
      ((sheafHomComplex X L M).obj.homologyπ i)
      ((sheafHomComplex X K L).obj.homologyπ j) (op U) x y).symm).trans ?_
  exact congrArg (fun z => (SheafOfModules.Hom.val z).app (op U)
    (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
        (((sheafHomComplex X L M).obj.cycles i).val ⊗
          ((sheafHomComplex X K L).obj.cycles j).val)).app (op U)
      (x ⊗ₜ[X.O.obj.obj (op U)] y))) h1

end Summand

section Lifting

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Three-section version of `Stacks.eq_of_forall_lift`.** Two sections of a separated presheaf
of modules agree as soon as they agree after restriction along every *simultaneous* local lift of
three given sections along three locally surjective morphisms.

This belongs upstream beside `Stacks.eq_of_forall_lift₂`, whose proof it is with one further
application of `CategoryTheory.GrothendieckTopology.intersection_covering`; it is stated here
because the descent of the composition product is its first consumer. The three morphisms are
allowed to differ, which `eq_of_forall_lift₂` does not permit and which is what a product of
three classes in three different cohomology sheaves needs. -/
theorem eq_of_forall_lift₃
    {Q M₁ M₂ M₃ N₁ N₂ N₃ : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    (hQ : Presheaf.IsSeparated X.J Q.presheaf)
    (α₁ : M₁ ⟶ N₁) (α₂ : M₂ ⟶ N₂) (α₃ : M₃ ⟶ N₃)
    [PresheafOfModules.IsLocallySurjective X.J α₁]
    [PresheafOfModules.IsLocallySurjective X.J α₂]
    [PresheafOfModules.IsLocallySurjective X.J α₃]
    {V : X.Cᵒᵖ} (a₁ : N₁.obj V) (a₂ : N₂.obj V) (a₃ : N₃.obj V) (u v : Q.obj V)
    (h : ∀ {W : X.Cᵒᵖ} (f : V ⟶ W) (m₁ : M₁.obj W) (m₂ : M₂.obj W) (m₃ : M₃.obj W),
      α₁.app W m₁ = N₁.map f a₁ → α₂.app W m₂ = N₂.map f a₂ → α₃.app W m₃ = N₃.map f a₃ →
      Q.map f u = Q.map f v) :
    u = v := by
  refine hQ _ _ (X.J.intersection_covering
    (X.J.intersection_covering
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₁) a₁)
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₂) a₂))
    (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₃) a₃)) _ _ ?_
  rintro W f ⟨⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩, ⟨m₃, hm₃⟩⟩
  exact h f.op m₁ m₂ m₃ hm₁ hm₂ hm₃

end Lifting

section Transport

variable (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The endomorphism Hom complex of `P`, abbreviated for the statements below. -/
abbrev endComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (sheafHomComplex X P P).obj

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transporting a degree commutes with restriction. -/
theorem castHom_map (Y : ℤ → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {a b : ℤ} (hab : a = b)
    {V W : X.Cᵒᵖ} (f : V ⟶ W) (w : (Y a).val.obj V) :
    (Y b).val.map f (SheafOfModules.castHom Y hab V w) =
      SheafOfModules.castHom Y hab W ((Y a).val.map f w) := by
  subst hab; rfl

/-- Transporting a degree commutes with taking the class of a cycle. -/
theorem castHom_homologyπ
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {a b : ℤ} (hab : a = b) (V : X.Cᵒᵖ) (w : (E.cycles a).val.obj V) :
    SheafOfModules.castHom (fun d => E.homology d) hab V ((E.homologyπ a).val.app V w) =
      (E.homologyπ b).val.app V (SheafOfModules.castHom (fun d => E.cycles d) hab V w) := by
  subst hab; rfl

/-- Transporting a degree commutes with the inclusion of cycles into the complex. -/
theorem castHom_iCycles
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {a b : ℤ} (hab : a = b) (V : X.Cᵒᵖ) (w : (E.cycles a).val.obj V) :
    ((E.iCycles b).val.app V) (SheafOfModules.castHom (fun d => E.cycles d) hab V w) =
      SheafOfModules.castHom (fun d => E.X d) hab V (((E.iCycles a).val.app V) w) := by
  subst hab; rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transporting the total degree of a pairing of local sections changes nothing: the total
degree is a parameter of `AlgebraicGeometry.RingedSite.compositionSection`, constrained by a
hypothesis, and the hypothesis is a proposition. -/
theorem castHom_compositionSection
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (p q n n' : ℤ) (hn : p + q = n) (hn' : p + q = n')
    (hnn' : n = n') (W : X.C)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op W))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op W)) :
    SheafOfModules.castHom (fun d => (sheafHomComplex X K M).obj.X d) hnn' (op W)
        (compositionSection X W p q n hn β γ) =
      compositionSection X W p q n' hn' β γ := by
  subst hnn'; rfl

/-- Two cycles have equal classes up to a degree transport once their images in the complex agree
up to that transport. -/
private theorem castHom_homologyπ_eq_of_iCycles_eq
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {a b : ℤ} (hab : a = b) (V : X.Cᵒᵖ) (w : (E.cycles a).val.obj V) (m : (E.cycles b).val.obj V)
    (h : SheafOfModules.castHom (fun d => E.X d) hab V ((E.iCycles a).val.app V w) =
      (E.iCycles b).val.app V m) :
    SheafOfModules.castHom (fun d => E.homology d) hab V ((E.homologyπ a).val.app V w) =
      (E.homologyπ b).val.app V m := by
  rw [castHom_homologyπ]
  refine congrArg (fun w => (E.homologyπ b).val.app V w) ?_
  refine _root_.Stacks.SheafOfModules.injective_app_of_mono (E.iCycles b) V ?_
  rw [castHom_iCycles]
  exact h

/-- **Associativity of the pairing on classes of cocycles**, for four complexes. On classes of
cycles the pairing is computed by `homologyMul_app_homologyπ`, the cycle it produces is computed
inside the complex by `iCycles_cycleComposition_pureSection`, and there associativity is
`AlgebraicGeometry.RingedSite.compositionSection_assoc`. The two cycles themselves are compared
by `Stacks.SheafOfModules.injective_app_of_mono` applied to the inclusion of cycles, a
monomorphism.

This is the whole mathematical content of associativity; what remains is to lift arbitrary
cohomology sections to cocycles, which is local. -/
theorem homologyMul_assoc_of_cycles
    (K L M N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i j k : ℤ) (W : X.C)
    (m₁ : ((sheafHomComplex X M N).obj.cycles i).val.obj (op W))
    (m₂ : ((sheafHomComplex X L M).obj.cycles j).val.obj (op W))
    (m₃ : ((sheafHomComplex X K L).obj.cycles k).val.obj (op W)) :
    SheafOfModules.castHom (fun d => (sheafHomComplex X K N).obj.homology d)
        (add_assoc i j k) (op W)
        ((homologyMul X K L N (i + j) k).app (op W)
          ((homologyMul X L M N i j).app (op W)
            ((((sheafHomComplex X M N).obj.homologyπ i).val.app (op W)) m₁)
            ((((sheafHomComplex X L M).obj.homologyπ j).val.app (op W)) m₂))
          ((((sheafHomComplex X K L).obj.homologyπ k).val.app (op W)) m₃)) =
      (homologyMul X K M N i (j + k)).app (op W)
        ((((sheafHomComplex X M N).obj.homologyπ i).val.app (op W)) m₁)
        ((homologyMul X K L M j k).app (op W)
          ((((sheafHomComplex X L M).obj.homologyπ j).val.app (op W)) m₂)
          ((((sheafHomComplex X K L).obj.homologyπ k).val.app (op W)) m₃)) := by
  rw [homologyMul_app_homologyπ, homologyMul_app_homologyπ, homologyMul_app_homologyπ,
    homologyMul_app_homologyπ]
  refine castHom_homologyπ_eq_of_iCycles_eq X _ _ _ _ _ ?_
  rw [iCycles_cycleComposition_pureSection, iCycles_cycleComposition_pureSection,
    iCycles_cycleComposition_pureSection, iCycles_cycleComposition_pureSection,
    compositionSection_assoc X W i j k (i + j) (j + k) (i + j + k) rfl rfl rfl (by omega),
    castHom_compositionSection]

/-- **Associativity of the composition pairing on cohomology**, for four complexes `K`, `L`,
`M`, `N`. Stated in the transported form that the multiplication field of
`SheafOfModules.GradedAlgebra` asks for, with the degree transport `SheafOfModules.castHom`
along `add_assoc` on one side.

The three cohomology sections are lifted to cocycles simultaneously on a common refinement --
`homologyπ` is an epimorphism, hence locally surjective, and `eq_of_forall_lift₃` intersects the
three resulting covering sieves -- and on those lifts the identity is
`homologyMul_assoc_of_cycles`. Restriction is moved past the transport by `castHom_map` and
inside the pairings by the naturality of a bilinear map.

The three off-diagonal instances are the module laws a bimodule argument runs on: with `N = M`
and `L = K` it says that right multiplication by a class of `H^*(SheafHom(K, K))` on
`H^*(SheafHom(K, M))` commutes with left multiplication by a class of `H^*(SheafHom(M, M))`. -/
theorem homologyMul_assoc
    (K L M N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (i j k : ℤ) (V : X.Cᵒᵖ)
    (x : ((sheafHomComplex X M N).obj.homology i).val.obj V)
    (y : ((sheafHomComplex X L M).obj.homology j).val.obj V)
    (z : ((sheafHomComplex X K L).obj.homology k).val.obj V) :
    SheafOfModules.castHom (fun d => (sheafHomComplex X K N).obj.homology d)
        (add_assoc i j k) V
        ((homologyMul X K L N (i + j) k).app V
          ((homologyMul X L M N i j).app V x y) z) =
      (homologyMul X K M N i (j + k)).app V x ((homologyMul X K L M j k).app V y z) := by
  have hi : PresheafOfModules.IsLocallySurjective X.J
    ((sheafHomComplex X M N).obj.homologyπ i).val :=
    _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _
  have hj : PresheafOfModules.IsLocallySurjective X.J
    ((sheafHomComplex X L M).obj.homologyπ j).val :=
    _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _
  have hk : PresheafOfModules.IsLocallySurjective X.J
    ((sheafHomComplex X K L).obj.homologyπ k).val :=
    _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _
  refine eq_of_forall_lift₃ X
    (((sheafHomComplex X K N).obj.homology (i + (j + k))).isSheaf.isSeparated)
    ((sheafHomComplex X M N).obj.homologyπ i).val
    ((sheafHomComplex X L M).obj.homologyπ j).val
    ((sheafHomComplex X K L).obj.homologyπ k).val x y z _ _ ?_
  intro W f m₁ m₂ m₃ hm₁ hm₂ hm₃
  rw [castHom_map X (fun d => (sheafHomComplex X K N).obj.homology d) (add_assoc i j k) f,
    _root_.Stacks.BilinearMap.naturality, _root_.Stacks.BilinearMap.naturality,
    _root_.Stacks.BilinearMap.naturality, _root_.Stacks.BilinearMap.naturality,
    ← hm₁, ← hm₂, ← hm₃]
  exact homologyMul_assoc_of_cycles X K L M N i j k W.unop m₁ m₂ m₃

/-! ### The unit -/

/-- The identity sections of all objects of the site, as a global section of the degree-zero
term of `SheafHom(P, P)`. -/
def idSections : ((endComplex X P).X 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => idSection X P U.unop)
    (fun {_ _} f => idSection_restrict X P f.unop)

/-- The identity, as a morphism from the unit sheaf of modules into the degree-zero term of
`SheafHom(P, P)`. A global section of a sheaf of modules is the same thing as such a morphism,
by `SheafOfModules.unitHomEquiv`; passing to the morphism is what lets the cycle be produced by
the morphism-level `HomologicalComplex.liftCycles` rather than sectionwise. -/
def idMor :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ (endComplex X P).X 0 :=
  ((endComplex X P).X 0).unitHomEquiv.symm (idSections X P)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On every object of the site, `idMor` sends the unit section `1` to the identity section. -/
theorem idMor_val_app_one (U : X.Cᵒᵖ) :
    (idMor X P).val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) =
      idSection X P U.unop :=
  congrFun (congrArg Subtype.val
    (((endComplex X P).X 0).unitHomEquiv.apply_symm_apply (idSections X P))) U

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identity morphism is killed by the differential: the identity section is a cocycle. -/
theorem idMor_comp_d : idMor X P ≫ (endComplex X P).d 0 1 = 0 := by
  refine ((endComplex X P).X 1).unitHomEquiv.injective ?_
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  change ((endComplex X P).d 0 1).val.app U
    ((idMor X P).val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) = _
  rw [idMor_val_app_one, d_idSection]
  rfl

/-- **The unit cycle**: the identity, as a morphism from the unit sheaf into the degree-zero
cycles of `SheafHom(P, P)`. -/
def oneCycle :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ (endComplex X P).cycles 0 :=
  (endComplex X P).liftCycles (idMor X P) 1 (by simp) (idMor_comp_d X P)

/-- The cycle `oneCycle`, viewed in the degree-zero term of `SheafHom(P, P)`, sends the unit
section `1` to the identity section on every object of the site. -/
theorem iCycles_oneCycle (U : X.Cᵒᵖ) :
    (((endComplex X P).iCycles 0).val.app U)
        ((oneCycle X P).val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) =
      idSection X P U.unop :=
  (congrArg (fun z => (SheafOfModules.Hom.val z).app U
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U))
    ((endComplex X P).liftCycles_i (idMor X P) 1 (by simp)
      (idMor_comp_d X P))).trans (idMor_val_app_one X P U)

/-- **The unit of the graded algebra on the cohomology of `SheafHom(P, P)`**: the class of the
identity. -/
def homologyOne : ((endComplex X P).homology 0).sections :=
  ((endComplex X P).homology 0).unitHomEquiv
    (oneCycle X P ≫ (endComplex X P).homologyπ 0)

/-- The unit is the class of the identity cycle, on every object of the site. -/
theorem homologyOne_eval (U : X.Cᵒᵖ) :
    (homologyOne X P).val U =
      (((endComplex X P).homologyπ 0).val.app U)
        ((oneCycle X P).val.app U (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)) :=
  rfl

/-- **The unit is a left unit, on a class of cycles.** -/
theorem homologyMul_one_mul_of_cycles (i : ℤ) (W : X.C)
    (m : ((endComplex X P).cycles i).val.obj (op W)) :
    SheafOfModules.castHom (fun d => (endComplex X P).homology d) (zero_add i) (op W)
        ((homologyMul X P P P 0 i).app (op W) ((homologyOne X P).val (op W))
          (((endComplex X P).homologyπ i).val.app (op W) m)) =
      ((endComplex X P).homologyπ i).val.app (op W) m := by
  rw [homologyOne_eval, homologyMul_app_homologyπ]
  refine castHom_homologyπ_eq_of_iCycles_eq X _ _ _ _ _ ?_
  rw [iCycles_cycleComposition_pureSection, iCycles_oneCycle,
    castHom_compositionSection X P P P 0 i (0 + i) i rfl (zero_add i) (zero_add i) W,
    compositionSection_idSection_left]

/-- **The unit is a right unit, on a class of cycles.** -/
theorem homologyMul_mul_one_of_cycles (i : ℤ) (W : X.C)
    (m : ((endComplex X P).cycles i).val.obj (op W)) :
    SheafOfModules.castHom (fun d => (endComplex X P).homology d) (add_zero i) (op W)
        ((homologyMul X P P P i 0).app (op W)
          (((endComplex X P).homologyπ i).val.app (op W) m)
          ((homologyOne X P).val (op W))) =
      ((endComplex X P).homologyπ i).val.app (op W) m := by
  rw [homologyOne_eval, homologyMul_app_homologyπ]
  refine castHom_homologyπ_eq_of_iCycles_eq X _ _ _ _ _ ?_
  rw [iCycles_cycleComposition_pureSection, iCycles_oneCycle,
    castHom_compositionSection X P P P i 0 (i + 0) i rfl (add_zero i) (add_zero i) W,
    compositionSection_idSection_right]

/-- A natural map out of the cohomology sheaf which is the identity up to a degree transport on
classes of cycles is so on all sections, by lifting them locally to cycles. -/
private theorem castHom_apply_eq_of_forall_cycles
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {a b : ℤ} (hab : a = b)
    (T : ∀ V : X.Cᵒᵖ, (E.homology b).val.obj V → (E.homology a).val.obj V)
    (hT : ∀ {V W : X.Cᵒᵖ} (f : V ⟶ W) (y : (E.homology b).val.obj V),
      (E.homology a).val.map f (T V y) = T W ((E.homology b).val.map f y))
    (h : ∀ (W : X.C) (m : (E.cycles b).val.obj (op W)),
      SheafOfModules.castHom (fun d => E.homology d) hab (op W)
        (T (op W) ((E.homologyπ b).val.app (op W) m)) = (E.homologyπ b).val.app (op W) m)
    (V : X.Cᵒᵖ) (x : (E.homology b).val.obj V) :
    SheafOfModules.castHom (fun d => E.homology d) hab V (T V x) = x := by
  have hi : PresheafOfModules.IsLocallySurjective X.J (E.homologyπ b).val :=
    _root_.Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi _
  refine _root_.Stacks.eq_of_forall_lift (((E.homology b)).isSheaf.isSeparated)
    (E.homologyπ b).val x _ _ ?_
  intro W f m hm
  rw [castHom_map X (fun d => E.homology d) hab f, hT, ← hm]
  exact h W.unop m

/-- **The unit is a left unit.** -/
theorem homologyMul_one_mul (i : ℤ) (V : X.Cᵒᵖ)
    (x : ((endComplex X P).homology i).val.obj V) :
    SheafOfModules.castHom (fun d => (endComplex X P).homology d) (zero_add i) V
        ((homologyMul X P P P 0 i).app V ((homologyOne X P).val V) x) = x := by
  refine castHom_apply_eq_of_forall_cycles X _ (zero_add i)
    (fun V y => (homologyMul X P P P 0 i).app V ((homologyOne X P).val V) y)
    (fun f y => ?_) (homologyMul_one_mul_of_cycles X P i) V x
  refine (_root_.Stacks.BilinearMap.naturality _ f _ y).trans ?_
  rw [PresheafOfModules.sections_property (homologyOne X P) f]

/-- **The unit is a right unit.** -/
theorem homologyMul_mul_one (i : ℤ) (V : X.Cᵒᵖ)
    (x : ((endComplex X P).homology i).val.obj V) :
    SheafOfModules.castHom (fun d => (endComplex X P).homology d) (add_zero i) V
        ((homologyMul X P P P i 0).app V x ((homologyOne X P).val V)) = x := by
  refine castHom_apply_eq_of_forall_cycles X _ (add_zero i)
    (fun V y => (homologyMul X P P P i 0).app V y ((homologyOne X P).val V))
    (fun f y => ?_) (homologyMul_mul_one_of_cycles X P i) V x
  refine (_root_.Stacks.BilinearMap.naturality _ f y _).trans ?_
  rw [PresheafOfModules.sections_property (homologyOne X P) f]

/-- **The graded algebra on the cohomology of `SheafHom(P, P)`.** The degree-`n` piece is the
`n`-th cohomology sheaf, the multiplication is the composition product `homologyMul`, and the
unit is the class of the identity.

For `P` a bounded resolution of `K` by direct summands of finite free modules the pieces are the
Ext sheaves of `K`, so this is the Ext algebra -- obtained at the level of complexes rather than
through the derived category, for the reason given in the implementation notes.

The three laws are the `HEq` form of `homologyMul_assoc`, `homologyMul_one_mul` and
`homologyMul_mul_one`, whose degree transports are removed by
`SheafOfModules.heq_castHom`. -/
def homologyGradedAlgebra :
    SheafOfModules.GradedAlgebra (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  piece n := (endComplex X P).homology n
  mul i j := homologyMul X P P P i j
  one := homologyOne X P
  mul_assoc i j k U x y z :=
    (SheafOfModules.heq_castHom (fun d => (endComplex X P).homology d)
      (add_assoc i j k) U _).symm.trans (heq_of_eq (homologyMul_assoc X P P P P i j k U x y z))
  one_mul i U x :=
    (SheafOfModules.heq_castHom (fun d => (endComplex X P).homology d)
      (zero_add i) U _).symm.trans (heq_of_eq (homologyMul_one_mul X P i U x))
  mul_one i U x :=
    (SheafOfModules.heq_castHom (fun d => (endComplex X P).homology d)
      (add_zero i) U _).symm.trans (heq_of_eq (homologyMul_mul_one X P i U x))

/-- The degree-`n` piece of the graded algebra is the `n`-th cohomology sheaf. -/
theorem homologyGradedAlgebra_piece (n : ℤ) :
    (homologyGradedAlgebra X P).piece n = (endComplex X P).homology n := rfl

/-- The multiplication of the graded algebra is the composition product. -/
theorem homologyGradedAlgebra_mul (i j : ℤ) :
    (homologyGradedAlgebra X P).mul i j = homologyMul X P P P i j := rfl

/-- The unit of the graded algebra is the class of the identity. -/
theorem homologyGradedAlgebra_one : (homologyGradedAlgebra X P).one = homologyOne X P := rfl

end Transport

end AlgebraicGeometry.RingedSite

end
