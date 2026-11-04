module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to an object preserves flatness

Let `(C, O)` be a ringed site, `U` an object of `C` and `F` a flat sheaf of `O`-modules. Then
the restriction `F|_U` of `F` to the site localized at `U` is a flat sheaf of `O|_U`-modules.
This is Stacks 0E8J.

The proof is the one in the source. Flatness of `F|_U` is exactness of `G ↦ G ⊗ F|_U` on
sheaves of modules on `C/U`. Extension by zero `j_{U!}` both preserves and reflects exactness
(Stacks 0E8G), so it is enough to see that `j_{U!}(G ⊗ F|_U)` is exact in `G`; and
`j_{U!}(G ⊗ F|_U)` is naturally `j_{U!}G ⊗ F`, which is exact in `G` because `j_{U!}` is exact
and `- ⊗ F` is exact by the flatness of `F`.

## Main results

* `Stacks.SheafOfModules.FlatRestriction.isFlat_over`: restriction to an object of a ringed
  site preserves flatness of sheaves of modules.

## Implementation notes

The comparison isomorphism `j_{U!}(-) ⊗ F ≅ j_{U!}(- ⊗ F|_U)` is not built here: it is
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso`, stated over a site
whose objects need not lie in the universe of its morphisms and used here at the single
universe, together with the three steps it is assembled from — `sheafifyModules`,
`tensorLeftIsoSheafTensorRight` and `tensorSheafificationIso` of the same namespace. Those
three were private declarations of this file, pinned to one universe, until the comparison was
needed over a site with large objects. In each of them the identification is made once, at the
place where the object is named, rather than rewritten through at every use:

* on presheaves of modules, extension from `C/U` commutes with the objectwise tensor product,
  because the sections of an extension over `V` are the direct sum of the sections over the
  arrows `V ⟶ U` (the extension formula of Stacks 03EJ) and tensoring distributes over a direct
  sum (`TensorProduct.directSumLeft`). This is
  `Stacks.Sites.OverModules.FormulaExtension.extensionTensorIso`, built on the concrete
  direct-sum model `FormulaExtension.extensionFunctor` of extension; both live in
  `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SliceExtensionTensor.lean`, at independent
  universes, and are used here at the single one;
* tensoring commutes with sheafification, which is
  `Stacks.SheafOfModules.TensorColimits.tensorSheafificationIsoGeneral` of Stacks 05NB,
  transported from tensoring on the left to tensoring on the right by `tensorCommIso`;
* sheafification commutes with the sheaf-level extension by zero, which is Mathlib's
  `SheafOfModules.sheafificationCompPullback`.

Extension from `C/U` appears here in two models: Mathlib's `PresheafOfModules.pullback`, which
is where the adjunction and the sheaf-level comparison live, and the concrete direct sum of the
extension formula, which is where the tensor comparison can be computed. They are identified by
the uniqueness of left adjoints, in `presheafExtendByZeroIsoExtension`.

The statement is at a single universe. That is forced by one step of the vocabulary this proof
runs through and not by the rest: `Stacks.Sites.ExtensionByZero.extensionByZero_exact_iff`
(Stacks 0E8G) is stated for a site whose objects, morphisms and ring sections all lie in one
universe `u`, and that reflection of exactness is the hypothesis of the source's argument.
Neither the presheaf-level comparison nor the sheaf-level one it assembles is so pinned, and
both are kept where they are general.

## References

* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ZeroObject

universe u ua va ub vb

namespace Stacks.SheafOfModules.FlatRestriction

open Stacks.Sites.OverModules
open Stacks.Sites.ExtensionByZero.OfEssentiallySmall
  (tensorLeftIsoSheafTensorRight extendByZero restrictionTensorIso)


variable {C : Type u} [Category.{u} C]

attribute [local instance] Classical.decEq


section SheafLevel

open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)
open Stacks.SheafOfModules.TensorColimits
  (tensorCommIso tensorSheafificationIsoGeneral tensorLeft_preservesColimits)

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- A functor between abelian categories preserving finite colimits is additive. -/
private theorem additive_of_preservesFiniteColimits
    {A : Type ua} [Category.{va} A] [Abelian A] {B : Type ub} [Category.{vb} B] [Abelian B]
    (T : A ⥤ B) [PreservesFiniteColimits T] : T.Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  Functor.additive_of_preservesBinaryBiproducts T

/-- Tensoring with a sheaf of modules preserves finite colimits. -/
private theorem tensorLeft_preservesFiniteColimits (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj F) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj F
  have : PreservesColimitsOfSize.{0, u} T := tensorLeft_preservesColimits J O F
  exact PreservesColimitsOfSize.preservesFiniteColimits T

/-- Tensoring with a sheaf of modules is an additive functor, because it preserves
coproducts. -/
private instance tensorLeft_additive (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj F).Additive :=
  have := tensorLeft_preservesFiniteColimits J O F
  additive_of_preservesFiniteColimits _

/-- For a flat sheaf of modules, tensoring on the left with it is exact. -/
private theorem tensorLeft_exact_of_isFlat (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).obj F) := by
  have hRight : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} O).flip.obj F) := hF
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight J O F).symm hRight

end SheafLevel

section Flat

open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]

/-- Extension by zero is additive, being a left adjoint. -/
private instance extendByZero_additive : (extendByZero X U).Additive :=
  have : PreservesFiniteColimits (extendByZero X U) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} (extendByZero X U)
  additive_of_preservesFiniteColimits _

/-- **The source's argument, in the abstract.** Let `E : B ⥤ A` be a functor that both
preserves and reflects exactness of short complexes, `T` an exact endofunctor of `A`, and `G`
an endofunctor of `B` preserving finite colimits, with `E ⋙ T ≅ G ⋙ E`.  Then `G` is exact.

This is stated for abstract categories on purpose: the two spellings of the ring sheaf of the
localized site (`(ringSheaf X.O).over U` and
`ringSheaf (X.O.over U)`) are definitionally equal but not reducibly so, and
instance search does not see through them.  Taking the three functors as arguments makes the
application's own defeq check discharge that identification once. -/
private theorem exactFunctor_of_reflecting_extension
    {A : Type ua} [Category.{va} A] [Abelian A] {B : Type ub} [Category.{vb} B] [Abelian B]
    (E : B ⥤ A) (T : A ⥤ A) (G : B ⥤ B)
    [E.Additive] [T.Additive] [G.Additive]
    (hE : ∀ S : ShortComplex B, (S.map E).Exact ↔ S.Exact)
    (hT : exactFunctor A A T) (hG : PreservesFiniteColimits G)
    (α : E ⋙ T ≅ G ⋙ E) :
    exactFunctor B B G := by
  have hmap : ∀ S : ShortComplex B, S.Exact → (S.map G).Exact := by
    intro S hS
    have hSE : (S.map E).Exact := (hE S).2 hS
    have hSET : ((S.map E).map T).Exact := by
      have hT' := (exactFunctor_iff T).mp hT
      have : PreservesFiniteLimits T := hT'.1
      have : PreservesFiniteColimits T := hT'.2
      exact hSE.map T
    have hIso : S.map (E ⋙ T) ≅ S.map (G ⋙ E) := S.mapNatIso α
    have hSGE : (S.map (G ⋙ E)).Exact := by
      apply (ShortComplex.exact_iff_of_iso hIso).mp
      simpa only [ShortComplex.map_comp] using hSET
    exact (hE (S.map G)).1 (by simpa only [ShortComplex.map_comp] using hSGE)
  rw [exactFunctor_iff]
  refine ⟨?_, hG⟩
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono G).2
  intro S hS
  refine ⟨hmap S hS.exact, ?_⟩
  let Smono : ShortComplex B := ShortComplex.mk (0 : 0 ⟶ S.X₁) S.f (by simp)
  have hSmono : Smono.Exact := (Smono.exact_iff_mono (by simp [Smono])).2 hS.mono_f
  exact ((Smono.map G).exact_iff_mono (by simp [Smono])).1 (hmap Smono hSmono)

/-- `Stacks.SheafOfModules.FlatRestriction.exactFunctor_of_reflecting_extension`, exported.

The free-module-universe statement of 0E8J, in
`StacksFrontier/CategoryTheory/Sites/Modules/Gate18b/FlatRestrictionFreeModuleUniverse.lean`, runs
this same argument. Its five universes are already independent of one another, so there is
nothing about it to restate at a freer shape: it is shared rather than twinned, and this is the
name it is shared under. The declaration it delegates to stays private, so that the statement
the base exports is unchanged by this file. -/
public alias exactFunctor_of_reflecting_extension_exported := exactFunctor_of_reflecting_extension

/-- **Stacks Project, Tag 0E8J.** Restriction to an object of a ringed site preserves flatness
of module sheaves. -/
@[stacks 0E8J, sga "4 V 1.6.1"]
public theorem isFlat_over
    (F : SheafOfModules.{u} (ringSheaf X.O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) (F.over U) := by
  have hG : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).obj (F.over U)) :=
    @exactFunctor_of_reflecting_extension _ _ _ _ _ _
      (extendByZero X U) ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj F)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).obj (F.over U))
      inferInstance inferInstance
      (tensorLeft_additive (X.J.over U) (X.O.over U) (F.over U))
      (fun S => Stacks.Sites.ExtensionByZero.extensionByZero_exact_iff X.J
        (ringSheaf X.O) U S)
      (tensorLeft_exact_of_isFlat X.J X.O F hF)
      (tensorLeft_preservesFiniteColimits (X.J.over U) (X.O.over U) (F.over U))
      (Functor.isoWhiskerLeft (extendByZero X U)
          (tensorLeftIsoSheafTensorRight X.J X.O F) ≪≫
        restrictionTensorIso X U F ≪≫
        Functor.isoWhiskerRight
          (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)).symm
          (extendByZero X U))
  show exactFunctor _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.O.over U)).flip.obj (F.over U))
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)) hG

end Flat

end Stacks.SheafOfModules.FlatRestriction
