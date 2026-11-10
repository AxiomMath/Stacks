module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to an object preserves flatness, over a site with large objects

Let `(C, O)` be a ringed site whose objects form a type in a universe `c` of their own while its
morphisms, the sections of `O` and the sections of its modules lie in one universe `u`, with `C`
essentially `u`-small. Let `U` be an object of `C` and `F` a flat sheaf of `O`-modules. Then
`F|_U` is a flat sheaf of `O|_U`-modules. The single-universe statement is
`Stacks.SheafOfModules.FlatRestriction.isFlat_over`.

Extension by zero `j_{U!}` preserves and reflects exactness (`extensionByZero_exact_iff` over an
essentially small site), and `j_{U!}(G ⊗ F|_U) ≅ j_{U!}G ⊗ F` naturally in `G`
(`restrictionTensorIso` over an essentially small site), which is exact in `G` by flatness of `F`.

## Main results

* `Stacks.SheafOfModules.FlatRestriction.OfEssentiallySmall.isFlat_over_of_essentiallySmall`:
  restriction to an object preserves flatness, over an essentially small site with large objects.

## References

* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
* [Stacks Project, Tag 0E8G](https://stacks.math.columbia.edu/tag/0E8G)
* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u c

namespace Stacks.SheafOfModules.FlatRestriction.OfEssentiallySmall

open Stacks.Sites.ExtensionByZero.OfEssentiallySmall
  (tensorLeftIsoSheafTensorRight extendByZero restrictionTensorIso)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.SheafOfModules.TensorColimits (tensorLeft_preservesColimits)

/-- A functor between abelian categories that preserves small colimits is additive. -/
private theorem additive_of_preservesColimitsOfSize {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] (T : A ⥤ B) [PreservesColimitsOfSize.{0, u} T] : T.Additive := by
  have : PreservesFiniteColimits T := PreservesColimitsOfSize.preservesFiniteColimits T
  have : PreservesBinaryBiproducts T := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  exact Functor.additive_of_preservesBinaryBiproducts T

section Helpers

variable (X : AlgebraicGeometry.RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]

omit [EssentiallySmall.{u} X.C] [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- Tensoring with a sheaf of modules on the slice is an additive functor. -/
theorem sliceTensorLeft_additive (F : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj
      F).Additive := by
  have := tensorLeft_preservesColimits (X.J.over U) (X.O.over U) F
  exact additive_of_preservesColimitsOfSize _

omit [EssentiallySmall.{u} X.C] [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- Tensoring with a sheaf of modules on the slice preserves finite colimits. -/
theorem sliceTensorLeft_preservesFiniteColimits (F : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj F) := by
  have : PreservesColimitsOfSize.{0, u}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj F) :=
    tensorLeft_preservesColimits (X.J.over U) (X.O.over U) F
  exact PreservesColimitsOfSize.preservesFiniteColimits _

omit [EssentiallySmall.{u} X.C] [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Tensoring with a sheaf of modules on `X` is an additive functor. -/
theorem tensorLeft_additive (F : SheafOfModules.{u} (ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj F).Additive := by
  have := tensorLeft_preservesColimits X.J X.O F
  exact additive_of_preservesColimitsOfSize _

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Extension by zero is additive. -/
theorem extendByZero_additive : (extendByZero X U).Additive := by
  exact additive_of_preservesColimitsOfSize.{0} (extendByZero X U)

end Helpers

/-- Restriction to an object of a ringed site whose objects form a type in a universe of their
own, with morphisms, sections and modules in one universe `u` and the site essentially `u`-small,
preserves flatness of sheaves of modules. -/
@[stacks 0E8J "for a site essentially u-small, objects in Type c, morphisms and modules in u"]
theorem isFlat_over_of_essentiallySmall
    (X : AlgebraicGeometry.RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} (ringSheaf X.O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := X.O.over U) (F.over U) := by
  have abstract : ∀ {A : Type (max c (u + 1))} [Category.{max c u} A] [Abelian A]
      {B : Type (max c (u + 1))} [Category.{max c u} B] [Abelian B]
      (E : B ⥤ A) (T : A ⥤ A) (G : B ⥤ B) [E.Additive] [T.Additive] [G.Additive],
      (∀ S : ShortComplex B, (S.map E).Exact ↔ S.Exact) → exactFunctor A A T →
        PreservesFiniteColimits G → (E ⋙ T ≅ G ⋙ E) → exactFunctor B B G := by
    intro A _ _ B _ _ E T G _ _ _ hE hT hG α
    obtain ⟨_, _⟩ := (exactFunctor_iff T).mp hT
    have hmap : ∀ S : ShortComplex B, S.Exact → (S.map G).Exact := by
      intro S hS
      have hSGE : (S.map (G ⋙ E)).Exact :=
        (ShortComplex.exact_iff_of_iso (S.mapNatIso α)).mp
          (by simpa only [ShortComplex.map_comp] using ((hE S).2 hS).map T)
      exact (hE (S.map G)).1 (by simpa only [ShortComplex.map_comp] using hSGE)
    rw [exactFunctor_iff]
    refine ⟨?_, hG⟩
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono G).2
    intro S hS
    refine ⟨hmap S hS.exact, ?_⟩
    let Smono : ShortComplex B := ShortComplex.mk (0 : 0 ⟶ S.X₁) S.f (by simp)
    have hSmono : Smono.Exact := (Smono.exact_iff_mono (by simp [Smono])).2 hS.mono_f
    exact ((Smono.map G).exact_iff_mono (by simp [Smono])).1 (hmap Smono hSmono)
  have := extendByZero_additive X U
  have hA := sliceTensorLeft_additive X U (F.over U)
  have := tensorLeft_additive X F
  have hRight : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).flip.obj F) := hF
  have hLeft : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj F) :=
    ObjectProperty.IsClosedUnderIsomorphisms.of_iso
      (tensorLeftIsoSheafTensorRight X.J X.O F).symm hRight
  have hG : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj
        (F.over U)) :=
    @abstract _ _ _ _ _ _
      (extendByZero X U) ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj F)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).obj
        (F.over U)) inferInstance inferInstance hA
      (fun S => Stacks.Sites.ExtensionByZero.OfEssentiallySmall.extensionByZero_exact_iff X.J
        (ringSheaf X.O) U S)
      hLeft
      (sliceTensorLeft_preservesFiniteColimits X U (F.over U))
      (Functor.isoWhiskerLeft (extendByZero X U)
          (tensorLeftIsoSheafTensorRight X.J X.O F) ≪≫
        restrictionTensorIso X U F ≪≫
        Functor.isoWhiskerRight
          (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)).symm
          (extendByZero X U))
  change exactFunctor _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.O.over U)).flip.obj
      (F.over U))
  exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (tensorLeftIsoSheafTensorRight (X.J.over U) (X.O.over U) (F.over U)) hG

end Stacks.SheafOfModules.FlatRestriction.OfEssentiallySmall
