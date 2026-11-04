module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Sheafifying the homology of a complex of presheaves of modules

Let `R` be a sheaf of rings on a site. Sheafification of presheaves of `R`-modules is exact,
and the forgetful functor from sheaves of modules followed by sheafification is the identity,
so the homology of the complex of underlying presheaves of modules, sheafified, is the
homology of the original complex of sheaves of modules.

## Main definitions

* `Stacks.Cohomology.sheafificationHomologyIso`: the comparison itself.

## Implementation notes

The derived category of presheaves of modules is taken at an arbitrary `HasDerivedCategory`
instance rather than at the standard model: only the comparison
`DerivedCategory.homologyFunctorFactorsh`, which holds at every model, is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Homology (mapHomotopyCategoryIso homotopyHomologyIso)

namespace Stacks.Cohomology

universe w u

/-- Sheafifying the `q`-th homology of the complex of underlying presheaves of modules gives
the `q`-th homology of the complex of sheaves of modules. -/
public def sheafificationHomologyIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (PresheafOfModules.{u} R.obj)]
    (q : ℤ) :
    (((SheafOfModules.forget R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{u} R.obj) q) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) ≅
      HomotopyCategory.homologyFunctor (SheafOfModules.{u} R) (ComplexShape.up ℤ) q := by
  let A := SheafOfModules.{u} R
  let P := PresheafOfModules.{u} R.obj
  let c := ComplexShape.up ℤ
  let F := SheafOfModules.forget R
  let a := PresheafOfModules.sheafification (𝟙 R.obj)
  let HqP := DerivedCategory.homologyFunctor P q
  let hP := HomotopyCategory.homologyFunctor P c q
  let hA := HomotopyCategory.homologyFunctor A c q
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  haveI : PreservesFiniteColimits a := by
    have := adj.leftAdjoint_preservesColimits
    exact ⟨fun _ _ _ => inferInstance⟩
  haveI : a.Additive := by
    let : a.PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_preserves_terminal_object
    have hbp : PreservesBinaryBiproducts a :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts a
    exact Functor.additive_of_preservesBinaryBiproducts a
  haveI : PreservesFiniteLimits a := inferInstance
  let Fmap := F.mapHomotopyCategory c
  let amap := a.mapHomotopyCategory c
  let eL : ((Fmap ⋙ DerivedCategory.Qh) ⋙ HqP) ⋙ a ≅
      Fmap ⋙ ((DerivedCategory.Qh ⋙ HqP) ⋙ a) :=
    Functor.isoWhiskerRight (Functor.associator Fmap DerivedCategory.Qh HqP) a ≪≫
      Functor.associator Fmap (DerivedCategory.Qh ⋙ HqP) a
  let eFactor : (DerivedCategory.Qh ⋙ HqP) ⋙ a ≅ hP ⋙ a :=
    Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactorsh P q) a
  let eH : Fmap ⋙ (hP ⋙ a) ≅ Fmap ⋙ (amap ⋙ hA) :=
    Functor.isoWhiskerLeft Fmap (by simpa [amap, hP, hA, c] using homotopyHomologyIso a q)
  let eComp : Fmap ⋙ (amap ⋙ hA) ≅ (F ⋙ a).mapHomotopyCategory c ⋙ hA :=
    (Functor.associator Fmap amap hA).symm ≪≫
      (by
        simpa [Fmap, amap] using
          Functor.isoWhiskerRight
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ a)) c) hA)
  have hCounit : IsIso adj.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun G => Adjunction.instIsIsoAppCounitOfFullOfFaithful adj G
  let eF : F ⋙ a ≅ 𝟭 A := @asIso _ _ _ _ adj.counit hCounit
  let eHF : (F ⋙ a).mapHomotopyCategory c ⋙ hA ≅ hA := by
    let eId : (F ⋙ a).mapHomotopyCategory c ≅ (𝟭 A).mapHomotopyCategory c :=
      mapHomotopyCategoryIso eF c
    let idIso : (𝟭 A).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory A c) := by
      refine NatIso.ofComponents (fun K => Iso.refl K) ?_
      intro K L f
      obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
      obtain ⟨f₀, rfl⟩ := (HomotopyCategory.quotient A c).map_surjective f
      rw [Functor.mapHomotopyCategory_map]
      have hf : ((𝟭 A).mapHomologicalComplex c).map f₀ = f₀ := rfl
      rw [hf]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    exact Functor.isoWhiskerRight eId hA ≪≫
      Functor.isoWhiskerRight idIso hA ≪≫ Functor.leftUnitor hA
  exact eL ≪≫ Functor.isoWhiskerLeft Fmap eFactor ≪≫ eH ≪≫ eComp ≪≫ eHF

end Stacks.Cohomology

end
