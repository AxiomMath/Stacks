module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCohomologyProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The composition product on the cohomology of an internal Hom complex

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be complexes of `O_X`-modules. The
internal Hom complexes carry the composition morphism of Stacks 0A91 out of the total tensor
product `SheafHom^•(L, M) ⊗_{O_X} SheafHom^•(K, L)`, and the cohomology sheaves of a total tensor
complex carry the product induced by tensoring cocycles
(`Stacks.SheafOfModules.tensorComplexHomology`). Composing the two gives the composition pairing
on cohomology sheaves,

`Hⁱ(SheafHom(L, M)) ⊗_{O_X} Hʲ(SheafHom(K, L)) ⟶ Hⁱ⁺ʲ(SheafHom(K, M))`.

Taking `K = L = M = P` is the diagonal instance, a product on the cohomology sheaves of
`SheafHom^•(P, P)`, and that is the one assembled into a graded algebra below. The off-diagonal
instances are what a bimodule argument needs: for a fixed class in `H^*(SheafHom(K, L))` the
pairing makes `H^*(SheafHom(K, L))` a module over `H^*(SheafHom(L, L))` on one side and over
`H^*(SheafHom(K, K))` on the other, which is how two models of a self-Ext algebra are compared.

When `P` is a bounded resolution of a complex `K` by direct summands of finite free modules, the
cohomology sheaves of `SheafHom^•(P, P)` are the Ext sheaves of `K`
(`Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution`), so the diagonal instance is the
composition product of the Ext algebra, obtained at the level of complexes rather than through
the derived category.

## Main definitions

* `Stacks.SheafOfModules.homologyComposition`: **the composition pairing on the cohomology
  sheaves of internal Hom complexes**, for three complexes `K`, `L`, `M`.
* `Stacks.SheafOfModules.homologyMul`: the same pairing as a bilinear map on local sections,
  which is the shape the multiplication field of `SheafOfModules.GradedAlgebra` takes.
* `Stacks.SheafOfModules.homologyOne`: **the unit**, the class of the identity.
* `Stacks.SheafOfModules.homologyGradedAlgebra`: **the graded algebra on the cohomology sheaves
  of `SheafHom(P, P)`**, the diagonal instance of the pairing.

## Main results

* `Stacks.SheafOfModules.homologyπ_homologyComposition`: **the defining property** — the pairing
  sends the tensor of the classes of two cocycles to the class of their composite.
* `Stacks.SheafOfModules.compositionTotalMap_tensorPairSection`: **the composition morphism
  sends a local pure tensor of the total tensor product to the composite of its factors.** This
  is the bridge between the two spellings of the total tensor product, and it is what reduces any
  computation with the pairing to the pairing on local sections.
* `Stacks.SheafOfModules.homologyMul_assoc`: **the product is associative**, and
  `Stacks.SheafOfModules.homologyMul_one_mul` with
  `Stacks.SheafOfModules.homologyMul_mul_one`: **the class of the identity is a two-sided
  unit**. Each is proved on classes of cocycles and then lifted, the lift being local.
* `Stacks.SheafOfModules.eq_of_forall_lift₃`: the three-section lifting principle the
  associativity descent needs, with three possibly different locally surjective morphisms.

## Implementation notes

**Nothing is proved here any more: every declaration below is the corresponding one of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct` read at
`Stacks.SheafOfModules.ringedSite`.** That file states the same product for a ringed *site*, and
none of the argument was ever space-specific: `AlgebraicGeometry.RingedSite.compositionMap` and
its associativity and unitality on local sections, the monoidal structure on `Mod(O)` and the
sheafification machinery are all site-level. What this file keeps is the *spelling* — the
statements are the ones a ringed space's consumers use, with `Stacks.SheafOfModules.structureSheaf
Rc` for the sheaf of rings and `Opens X` for the site — and
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProductSite` records the
identification of the two spellings, which is `rfl` in each case. The site-level generality is
what the local-to-global step of Stacks 0BQY needs: the restriction of a sheaf of modules to a
member of a cover lives on a *slice site*, which is a ringed site and not a ringed space, so the
graded algebra of a restricted complex cannot be written down at this file's generality at all.

**Why the product is assembled at the level of complexes and not in the derived category.** The
Ext sheaves already carry a composition product, `Stacks.SheafOfModules.sheafExtProduct`, built
from the derived composition morphism of Stacks 0A8V. That product is unusable for an
associativity statement: establishing associativity of the derived composition requires the
clause of Tag 0FPT computing the derived associator on K-flat representatives, which
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity` records as absent. The
product below is instead induced by `AlgebraicGeometry.RingedSite.compositionMap`, a morphism of
complexes, whose associativity and unitality on local sections are available
(`AlgebraicGeometry.RingedSite.compositionMap_assoc`,
`AlgebraicGeometry.RingedSite.compositionMap_idSection_left` and `..._right`).

**The two spellings of the total tensor product.** `Stacks.SheafOfModules.tensorComplexHomology`
lands in the cohomology of `HomologicalComplex.tensorObj`, which is the degreewise sheaf tensor
product totalised, whereas `AlgebraicGeometry.RingedSite.compositionMap` is defined out of
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
on local sections: `Stacks.SheafOfModules.tensorHom_pureSection` holds for `⊗ₘ` precisely because
the re-seated whiskerings are sheafifications of the objectwise ones, and the associator of the
same re-seated structure is a genuine conjugate for which no such statement is available. The
generic file `StacksFrontier.Homology.TensorComplex.CohomologyProduct` also proves nothing about
associators or unitors for `CochainComplex.tensorHomology`, so that route has no shortcut through
it either.

**Why the two halves of the descent have the shapes they do, and why that is consistent.**
`castHom_compositionSection` is a single `subst` only because the total degree of
`AlgebraicGeometry.RingedSite.compositionSection` is a parameter constrained by a hypothesis
rather than a value computed from the two factor degrees; that is the device which makes
`AlgebraicGeometry.RingedSite.compositionSection_assoc` an honest equality instead of an `HEq`,
and transporting the total degree is then proof irrelevance and nothing more. At the other end,
the cycles are compared by `SheafOfModules.injective_app_of_mono`, whose own docstring records
that there is deliberately no epimorphism analogue — finite limits of sheaves of modules need no
sheafification, finite colimits do. That is the same fact which forced this descent to lift
sections locally rather than cancel an epimorphism of sheaves, so the two halves of the argument
agree about why each has the shape it has.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace'
  symmetricSpace' monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms

variable {X : TopCat.{u}} (Rc : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafification of presheaves of modules is additive, at the spelling in which the
total-complex comparison is stated. The universes of `Opens X` and of the sections of `O_X`
coincide, so instance search would have to solve `max ?u ?v =?= u` with both unknown; this is a
named local instance for the same reason as the monoidal ones above. -/
local instance sheafificationAdditive' :
    (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).Additive :=
  PresheafOfModules.sheafification_additive (Tensor.ringSheaf.{u, u, u} Rc)
    (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)

/-- The composition morphism of internal Hom complexes of Stacks 0A91, read on the total tensor
product of `SheafHom^•(L, M)` and `SheafHom^•(K, L)` in the spelling
`HomologicalComplex.tensorObj` that the cohomology product uses. The only content is the
identification `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex` of the two total
tensor complexes. -/
def compositionTotalMap
    (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) :
    HomologicalComplex.tensorObj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
        (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj ⟶
      (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj :=
  RingedSite.compositionTotalMap (ringedSite Rc) K L M

/-- **The composition pairing on the cohomology sheaves of internal Hom complexes.** It is the
product induced by tensoring cocycles, followed by the map that the composition morphism of
internal Hom complexes of Stacks 0A91 induces on cohomology,

`Hⁱ(SheafHom(L, M)) ⊗_{O_X} Hʲ(SheafHom(K, L)) ⟶ Hⁱ⁺ʲ(SheafHom(K, M))`.

The diagonal instance `K = L = M = P` is the composition product on the cohomology sheaves of
`SheafHom^•(P, P)` that `Stacks.SheafOfModules.homologyGradedAlgebra` is built from. -/
def homologyComposition
    (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) (i j : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homology i ⊗
        (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homology j ⟶
      (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.homology (i + j) :=
  RingedSite.homologyComposition (ringedSite Rc) K L M i j

/-- **The defining property of the composition pairing on cohomology:** it sends the tensor of
the classes of two cocycles to the class of their composite, the composite being taken by the
composition morphism of internal Hom complexes of Stacks 0A91. -/
theorem homologyπ_homologyComposition
    (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) (i j : ℤ) :
    ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homologyπ i ⊗ₘ
          (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homologyπ j) ≫
        homologyComposition Rc K L M i j =
      CochainComplex.tensorCycles (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj i j ≫
        (HomologicalComplex.tensorObj
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj).homologyπ (i + j) ≫
          HomologicalComplex.homologyMap (compositionTotalMap Rc K L M) (i + j) :=
  RingedSite.homologyπ_homologyComposition (ringedSite Rc) K L M i j

/-- **The composition pairing on cohomology, as a bilinear map on local sections.** This is the
shape the multiplication field of `SheafOfModules.GradedAlgebra` takes: a map on sections,
additive and `O_X`-linear in each variable and compatible with restriction, rather than a
morphism out of a tensor product.

The sheaf tensor product is the sheafification of the objectwise one, so a morphism out of it
restricts along the unit of the sheafification adjunction to a morphism out of the objectwise
tensor product, and `PresheafOfModules.toBilinear` reads that off as a bilinear map. -/
def homologyMul
    (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) (i j : ℤ) :
    _root_.Stacks.BilinearMap
      ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homology i).val
      ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homology j).val
      ((RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.homology (i + j)).val :=
  RingedSite.homologyMul (ringedSite Rc) K L M i j

section Summand

variable (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)

/-- The presheaf-level double complex of tensor products whose two totalisations are the two
spellings of the total tensor product of `SheafHom^•(L, M)` and `SheafHom^•(K, L)`. -/
abbrev tensorPairBicomplex :=
  RingedSite.tensorPairBicomplex (ringedSite Rc) K L M

/-- The summand inclusion of the total tensor product, in the bicomplex spelling in which the
comparison of the two total complexes is stated. It is the monoidal summand inclusion
`HomologicalComplex.ιTensorObj`. -/
abbrev ιTensorPair (i j : ℤ) :=
  RingedSite.ιTensorPair (ringedSite Rc) K L M i j

/-- The monoidal summand inclusion `HomologicalComplex.ιTensorObj` of `SheafHom^•(L, M)` and
`SheafHom^•(K, L)` in degree `(i, j)` is `ιTensorPair`. -/
theorem ιTensorObj_eq_ιTensorPair (i j : ℤ) :
    HomologicalComplex.ιTensorObj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
        (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj i j (i + j) rfl =
      ιTensorPair Rc K L M i j :=
  rfl

/-- In degree `n`, `compositionTotalMap` is the comparison map `totalMapf` of the total complexes
of `tensorPairBicomplex`, followed by the composition morphism `RingedSite.compositionMap`. -/
theorem compositionTotalMap_f (n : ℤ) :
    (compositionTotalMap Rc K L M).f n =
      HomologicalComplex₂.TotalMap.totalMapf
          (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj))
          (tensorPairBicomplex Rc K L M) n ≫
        (RingedSite.compositionMap (ringedSite Rc) K L M).f n :=
  rfl

/-- On the degree-`(i, j)` summand, the composition morphism read on the total tensor product is
the sheafification of the presheaf-level summand inclusion followed by the composition morphism
of Stacks 0A91. This is the summand compatibility of the comparison of the two total tensor
complexes, which is `HomologicalComplex₂.TotalMap.ι_totalMapf`. -/
theorem ι_compositionTotalMap (i j : ℤ) :
    ιTensorPair Rc K L M i j ≫ (compositionTotalMap Rc K L M).f (i + j) =
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).map
          ((tensorPairBicomplex Rc K L M).ιTotal (ComplexShape.up ℤ) i j (i + j) rfl) ≫
        (RingedSite.compositionMap (ringedSite Rc) K L M).f (i + j) :=
  RingedSite.ι_compositionTotalMap (ringedSite Rc) K L M i j

/-- **The local pure tensor in the degree-`(i, j)` summand of the total tensor product of
`SheafHom^•(L, M)` and `SheafHom^•(K, L)`.** These sections generate the total tensor product,
and they are what the cohomology pairing is computed on. -/
def tensorPairSection (i j : ℤ) (U : Opens ↥X)
    (β : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.X i).val.obj (op U))
    (γ : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.X j).val.obj (op U)) :
    ((HomologicalComplex.tensorObj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
      (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj).X (i + j)).val.obj (op U) :=
  RingedSite.tensorPairSection (ringedSite Rc) K L M i j U β γ

/-- **The composition morphism sends a local pure tensor of the total tensor product to the
composite of its factors.** This is the bridge between the two spellings of the total tensor
product: the monoidal one, in which the cohomology product of
`Stacks.SheafOfModules.tensorComplexHomology` is stated, and
`AlgebraicGeometry.RingedSite.tensorTotal`, in which the composition morphism of Stacks 0A91 is
defined. Its three ingredients are the summand compatibility of the comparison, the naturality
of the sheafification unit, and the characterisation
`AlgebraicGeometry.RingedSite.compositionMap_tensorTotalSection` of the composition morphism on
local pure tensors. -/
theorem compositionTotalMap_tensorPairSection (i j : ℤ) (U : Opens ↥X)
    (β : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.X i).val.obj (op U))
    (γ : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.X j).val.obj (op U)) :
    ((compositionTotalMap Rc K L M).f (i + j)).val.app (op U)
        (tensorPairSection Rc K L M i j U β γ) =
      RingedSite.compositionSection (ringedSite Rc) U i j (i + j) rfl β γ :=
  RingedSite.compositionTotalMap_tensorPairSection (ringedSite Rc) K L M i j U β γ

/-- **The tensor product of two morphisms, on a local pure tensor.** The sheaf tensor product is
the sheafification of the objectwise one and the re-seated whiskerings are the sheafifications of
the objectwise whiskerings, so `⊗ₘ` acts on a local pure tensor by acting on its two factors.
This holds for `⊗ₘ` but *not* for the associator; see the implementation notes. -/
theorem tensorHom_pureSection {M N M' N' : SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)}
    (f : M ⟶ M') (g : N ⟶ N')
    (U : (Opens ↥X)ᵒᵖ) (a : M.val.obj U) (b : N.val.obj U) :
    ((f ⊗ₘ g).val.app U)
        (((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf.{u, u, u} Rc)
              (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).unit.app
            (M.val ⊗ N.val)).app U (a ⊗ₜ[(Tensor.ringSheaf.{u, u, u} Rc).obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf.{u, u, u} Rc)
            (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).unit.app
          (M'.val ⊗ N'.val)).app U
        ((f.val.app U a) ⊗ₜ[(Tensor.ringSheaf.{u, u, u} Rc).obj.obj U] (g.val.app U b)) :=
  RingedSite.tensorHom_pureSection (ringedSite Rc) f g U a b

/-- **The composition pairing at the level of cycles.** Tensoring a cycle of `SheafHom^•(L, M)`
with a cycle of `SheafHom^•(K, L)` and composing them gives a cycle of `SheafHom^•(K, M)`,
because the composition morphism is a morphism of complexes. -/
def cycleComposition (i j : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles i ⊗
        (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles j ⟶
      (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.cycles (i + j) :=
  RingedSite.cycleComposition (ringedSite Rc) K L M i j

/-- **The composite of two cycles is, inside the complex, the pairing of the sections they
are.** This is the computation that every statement about the pairing reduces to. -/
theorem iCycles_cycleComposition_pureSection (i j : ℤ) (U : Opens ↥X)
    (x : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles i).val.obj (op U))
    (y : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles j).val.obj (op U)) :
    (((RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.iCycles (i + j)).val.app (op U))
        ((cycleComposition Rc K L M i j).val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf.{u, u, u} Rc)
                (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).unit.app
              (((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles i).val ⊗
                ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles j).val)).app (op U)
            (x ⊗ₜ[(Tensor.ringSheaf.{u, u, u} Rc).obj.obj (op U)] y))) =
      RingedSite.compositionSection (ringedSite Rc) U i j (i + j) rfl
        ((((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.iCycles i).val.app (op U)) x)
        ((((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.iCycles j).val.app (op U)) y) :=
  RingedSite.iCycles_cycleComposition_pureSection (ringedSite Rc) K L M i j U x y

/-- **The pairing of two classes of cycles is the class of their cycle-level composite.** This
is the defining property in the form a computation on local sections uses it: it turns a value of
the pairing at two classes into a single class, whose representative
`iCycles_cycleComposition_pureSection` then computes. -/
theorem homologyMul_app_homologyπ (i j : ℤ) (U : Opens ↥X)
    (x : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles i).val.obj (op U))
    (y : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles j).val.obj (op U)) :
    (homologyMul Rc K L M i j).app (op U)
        (((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homologyπ i).val.app (op U) x)
        (((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homologyπ j).val.app (op U) y) =
      ((RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.homologyπ (i + j)).val.app (op U)
        ((cycleComposition Rc K L M i j).val.app (op U)
          (((PresheafOfModules.sheafificationAdjunction.{u} (R := Tensor.ringSheaf.{u, u, u} Rc)
                (𝟙 (Tensor.ringSheaf.{u, u, u} Rc).obj)).unit.app
              (((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles i).val ⊗
                ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles j).val)).app (op U)
            (x ⊗ₜ[(Tensor.ringSheaf.{u, u, u} Rc).obj.obj (op U)] y))) :=
  RingedSite.homologyMul_app_homologyπ (ringedSite Rc) K L M i j U x y

end Summand

section Lifting

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Three-section version of `Stacks.eq_of_forall_lift`.** Two sections of a separated presheaf
of modules agree as soon as they agree after restriction along every *simultaneous* local lift of
three given sections along three locally surjective morphisms.

This belongs upstream beside `Stacks.eq_of_forall_lift₂`, whose proof it is with one further
application of `CategoryTheory.GrothendieckTopology.intersection_covering`; it is stated here
because the descent of the composition product is its first consumer. The three morphisms are
allowed to differ, which `eq_of_forall_lift₂` does not permit and which is what a product of
three classes in three different cohomology sheaves needs. -/
theorem eq_of_forall_lift₃
    {Q M₁ M₂ M₃ N₁ N₂ N₃ : PresheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc).obj}
    (hQ : Presheaf.IsSeparated (Opens.grothendieckTopology ↥X) Q.presheaf)
    (α₁ : M₁ ⟶ N₁) (α₂ : M₂ ⟶ N₂) (α₃ : M₃ ⟶ N₃)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) α₁]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) α₂]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) α₃]
    {V : (Opens ↥X)ᵒᵖ} (a₁ : N₁.obj V) (a₂ : N₂.obj V) (a₃ : N₃.obj V) (u v : Q.obj V)
    (h : ∀ {W : (Opens ↥X)ᵒᵖ} (f : V ⟶ W) (m₁ : M₁.obj W) (m₂ : M₂.obj W) (m₃ : M₃.obj W),
      α₁.app W m₁ = N₁.map f a₁ → α₂.app W m₂ = N₂.map f a₂ → α₃.app W m₃ = N₃.map f a₃ →
      Q.map f u = Q.map f v) :
    u = v :=
  RingedSite.eq_of_forall_lift₃ (ringedSite Rc) hQ α₁ α₂ α₃ a₁ a₂ a₃ u v h

end Lifting

section Transport

variable (P : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)

/-- The endomorphism Hom complex of `P`, abbreviated for the statements below. -/
abbrev endComplex : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ :=
  (RingedSite.sheafHomComplex (ringedSite Rc) P P).obj

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transporting a degree commutes with restriction. -/
theorem castHom_map (Y : ℤ → SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) {a b : ℤ}
    (hab : a = b)
    {V W : (Opens ↥X)ᵒᵖ} (f : V ⟶ W) (w : (Y a).val.obj V) :
    (Y b).val.map f (_root_.SheafOfModules.castHom Y hab V w) =
      _root_.SheafOfModules.castHom Y hab W ((Y a).val.map f w) :=
  RingedSite.castHom_map (ringedSite Rc) Y hab f w

/-- Transporting a degree commutes with taking the class of a cycle. -/
theorem castHom_homologyπ
    (E : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) {a b : ℤ}
    (hab : a = b) (V : (Opens ↥X)ᵒᵖ) (w : (E.cycles a).val.obj V) :
    _root_.SheafOfModules.castHom (fun d => E.homology d) hab V
        ((E.homologyπ a).val.app V w) =
      (E.homologyπ b).val.app V
        (_root_.SheafOfModules.castHom (fun d => E.cycles d) hab V w) :=
  RingedSite.castHom_homologyπ (ringedSite Rc) E hab V w

/-- Transporting a degree commutes with the inclusion of cycles into the complex. -/
theorem castHom_iCycles
    (E : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ) {a b : ℤ}
    (hab : a = b) (V : (Opens ↥X)ᵒᵖ) (w : (E.cycles a).val.obj V) :
    ((E.iCycles b).val.app V)
        (_root_.SheafOfModules.castHom (fun d => E.cycles d) hab V w) =
      _root_.SheafOfModules.castHom (fun d => E.X d) hab V
        (((E.iCycles a).val.app V) w) :=
  RingedSite.castHom_iCycles (ringedSite Rc) E hab V w

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Transporting the total degree of a pairing of local sections changes nothing: the total
degree is a parameter of `AlgebraicGeometry.RingedSite.compositionSection`, constrained by a
hypothesis, and the hypothesis is a proposition. -/
theorem castHom_compositionSection
    (K L M : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)
    (p q n n' : ℤ) (hn : p + q = n) (hn' : p + q = n')
    (hnn' : n = n') (W : Opens ↥X)
    (β : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.X p).val.obj (op W))
    (γ : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.X q).val.obj (op W)) :
    _root_.SheafOfModules.castHom
        (fun d => (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj.X d) hnn' (op W)
        (RingedSite.compositionSection (ringedSite Rc) W p q n hn β γ) =
      RingedSite.compositionSection (ringedSite Rc) W p q n' hn' β γ :=
  RingedSite.castHom_compositionSection (ringedSite Rc) K L M p q n n' hn hn' hnn' W β γ

/-- **Associativity of the pairing on classes of cocycles**, for four complexes. On classes of
cycles the pairing is computed by `homologyMul_app_homologyπ`, the cycle it produces is computed
inside the complex by `iCycles_cycleComposition_pureSection`, and there associativity is
`AlgebraicGeometry.RingedSite.compositionSection_assoc`. The two cycles themselves are compared
by `SheafOfModules.injective_app_of_mono` applied to the inclusion of cycles, a monomorphism.

This is the whole mathematical content of associativity; what remains is to lift arbitrary
cohomology sections to cocycles, which is local. -/
theorem homologyMul_assoc_of_cycles
    (K L M N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)
    (i j k : ℤ) (W : Opens ↥X)
    (m₁ : ((RingedSite.sheafHomComplex (ringedSite Rc) M N).obj.cycles i).val.obj (op W))
    (m₂ : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.cycles j).val.obj (op W))
    (m₃ : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.cycles k).val.obj (op W)) :
    _root_.SheafOfModules.castHom
        (fun d => (RingedSite.sheafHomComplex (ringedSite Rc) K N).obj.homology d)
        (add_assoc i j k) (op W)
        ((homologyMul Rc K L N (i + j) k).app (op W)
          ((homologyMul Rc L M N i j).app (op W)
            ((((RingedSite.sheafHomComplex (ringedSite Rc) M N).obj.homologyπ i).val.app
              (op W)) m₁)
            ((((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homologyπ j).val.app
              (op W)) m₂))
          ((((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homologyπ k).val.app
            (op W)) m₃)) =
      (homologyMul Rc K M N i (j + k)).app (op W)
        ((((RingedSite.sheafHomComplex (ringedSite Rc) M N).obj.homologyπ i).val.app (op W)) m₁)
        ((homologyMul Rc K L M j k).app (op W)
          ((((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homologyπ j).val.app
            (op W)) m₂)
          ((((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homologyπ k).val.app
            (op W)) m₃)) :=
  RingedSite.homologyMul_assoc_of_cycles (ringedSite Rc) K L M N i j k W m₁ m₂ m₃

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
    (K L M N : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)
    (i j k : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((RingedSite.sheafHomComplex (ringedSite Rc) M N).obj.homology i).val.obj V)
    (y : ((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homology j).val.obj V)
    (z : ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homology k).val.obj V) :
    _root_.SheafOfModules.castHom
        (fun d => (RingedSite.sheafHomComplex (ringedSite Rc) K N).obj.homology d)
        (add_assoc i j k) V
        ((homologyMul Rc K L N (i + j) k).app V
          ((homologyMul Rc L M N i j).app V x y) z) =
      (homologyMul Rc K M N i (j + k)).app V x ((homologyMul Rc K L M j k).app V y z) :=
  RingedSite.homologyMul_assoc (ringedSite Rc) K L M N i j k V x y z

/-! ### The unit -/

/-- The identity sections of all objects of the site, as a global section of the degree-zero
term of `SheafHom(P, P)`. -/
def idSections : ((endComplex Rc P).X 0).sections :=
  RingedSite.idSections (ringedSite Rc) P

/-- The identity, as a morphism from the unit sheaf of modules into the degree-zero term of
`SheafHom(P, P)`. A global section of a sheaf of modules is the same thing as such a morphism,
by `SheafOfModules.unitHomEquiv`; passing to the morphism is what lets the cycle be produced by
the morphism-level `HomologicalComplex.liftCycles` rather than sectionwise. -/
def idMor : _root_.SheafOfModules.unit (Tensor.ringSheaf.{u, u, u} Rc) ⟶ (endComplex Rc P).X 0 :=
  RingedSite.idMor (ringedSite Rc) P

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On an open `U`, `idMor` sends the section `1` to the identity section of `SheafHom(P, P)`
over `U`. -/
theorem idMor_val_app_one (U : (Opens ↥X)ᵒᵖ) :
    (idMor Rc P).val.app U (1 : (Tensor.ringSheaf.{u, u, u} Rc).obj.obj U) =
      RingedSite.idSection (ringedSite Rc) P U.unop :=
  RingedSite.idMor_val_app_one (ringedSite Rc) P U

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identity morphism is killed by the differential: the identity section is a cocycle. -/
theorem idMor_comp_d : idMor Rc P ≫ (endComplex Rc P).d 0 1 = 0 :=
  RingedSite.idMor_comp_d (ringedSite Rc) P

/-- **The unit cycle**: the identity, as a morphism from the unit sheaf into the degree-zero
cycles of `SheafHom(P, P)`. -/
def oneCycle :
    _root_.SheafOfModules.unit (Tensor.ringSheaf.{u, u, u} Rc) ⟶ (endComplex Rc P).cycles 0 :=
  RingedSite.oneCycle (ringedSite Rc) P

/-- On an open `U`, the image of `1` under `oneCycle`, followed by the inclusion of cycles, is
the identity section of `SheafHom(P, P)` over `U`. -/
theorem iCycles_oneCycle (U : (Opens ↥X)ᵒᵖ) :
    (((endComplex Rc P).iCycles 0).val.app U)
        ((oneCycle Rc P).val.app U (1 : (Tensor.ringSheaf.{u, u, u} Rc).obj.obj U)) =
      RingedSite.idSection (ringedSite Rc) P U.unop :=
  RingedSite.iCycles_oneCycle (ringedSite Rc) P U

/-- **The unit of the graded algebra on the cohomology of `SheafHom(P, P)`**: the class of the
identity. -/
def homologyOne : ((endComplex Rc P).homology 0).sections :=
  RingedSite.homologyOne (ringedSite Rc) P

/-- The unit is the class of the identity cycle, on every object of the site. -/
theorem homologyOne_eval (U : (Opens ↥X)ᵒᵖ) :
    (homologyOne Rc P).val U =
      (((endComplex Rc P).homologyπ 0).val.app U)
        ((oneCycle Rc P).val.app U (1 : (Tensor.ringSheaf.{u, u, u} Rc).obj.obj U)) :=
  rfl

/-- **The unit is a left unit, on a class of cycles.** -/
theorem homologyMul_one_mul_of_cycles (i : ℤ) (W : Opens ↥X)
    (m : ((endComplex Rc P).cycles i).val.obj (op W)) :
    _root_.SheafOfModules.castHom (fun d => (endComplex Rc P).homology d) (zero_add i) (op W)
        ((homologyMul Rc P P P 0 i).app (op W) ((homologyOne Rc P).val (op W))
          (((endComplex Rc P).homologyπ i).val.app (op W) m)) =
      ((endComplex Rc P).homologyπ i).val.app (op W) m :=
  RingedSite.homologyMul_one_mul_of_cycles (ringedSite Rc) P i W m

/-- **The unit is a right unit, on a class of cycles.** -/
theorem homologyMul_mul_one_of_cycles (i : ℤ) (W : Opens ↥X)
    (m : ((endComplex Rc P).cycles i).val.obj (op W)) :
    _root_.SheafOfModules.castHom (fun d => (endComplex Rc P).homology d) (add_zero i) (op W)
        ((homologyMul Rc P P P i 0).app (op W)
          (((endComplex Rc P).homologyπ i).val.app (op W) m)
          ((homologyOne Rc P).val (op W))) =
      ((endComplex Rc P).homologyπ i).val.app (op W) m :=
  RingedSite.homologyMul_mul_one_of_cycles (ringedSite Rc) P i W m

/-- **The unit is a left unit.** -/
theorem homologyMul_one_mul (i : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((endComplex Rc P).homology i).val.obj V) :
    _root_.SheafOfModules.castHom (fun d => (endComplex Rc P).homology d) (zero_add i) V
        ((homologyMul Rc P P P 0 i).app V ((homologyOne Rc P).val V) x) = x :=
  RingedSite.homologyMul_one_mul (ringedSite Rc) P i V x

/-- **The unit is a right unit.** -/
theorem homologyMul_mul_one (i : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((endComplex Rc P).homology i).val.obj V) :
    _root_.SheafOfModules.castHom (fun d => (endComplex Rc P).homology d) (add_zero i) V
        ((homologyMul Rc P P P i 0).app V x ((homologyOne Rc P).val V)) = x :=
  RingedSite.homologyMul_mul_one (ringedSite Rc) P i V x

/-- **The graded algebra on the cohomology of `SheafHom(P, P)`.** The degree-`n` piece is the
`n`-th cohomology sheaf, the multiplication is the composition product `homologyMul`, and the
unit is the class of the identity.

For `P` a bounded resolution of `K` by direct summands of finite free modules the pieces are the
Ext sheaves of `K`, by `Stacks.SheafOfModules.derivedSheafExtIsoHomologyOfResolution`, so this is
the Ext algebra -- obtained at the level of complexes rather than through the derived category,
for the reason given in the implementation notes.

The three laws are the `HEq` form of `homologyMul_assoc`, `homologyMul_one_mul` and
`homologyMul_mul_one`, whose degree transports are removed by
`SheafOfModules.heq_castHom`. -/
def homologyGradedAlgebra : _root_.SheafOfModules.GradedAlgebra (structureSheaf Rc) :=
  RingedSite.homologyGradedAlgebra (ringedSite Rc) P

/-- The degree-`n` piece of the graded algebra is the `n`-th cohomology sheaf. -/
theorem homologyGradedAlgebra_piece (n : ℤ) :
    (homologyGradedAlgebra Rc P).piece n = (endComplex Rc P).homology n := rfl

/-- The multiplication of the graded algebra is the composition product. -/
theorem homologyGradedAlgebra_mul (i j : ℤ) :
    (homologyGradedAlgebra Rc P).mul i j = homologyMul Rc P P P i j := rfl

/-- The unit of the graded algebra is the class of the identity. -/
theorem homologyGradedAlgebra_one : (homologyGradedAlgebra Rc P).one = homologyOne Rc P := rfl

end Transport

end Stacks.SheafOfModules
