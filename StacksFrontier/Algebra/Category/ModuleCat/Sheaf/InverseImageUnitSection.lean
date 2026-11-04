module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Limits.TerminalGlobalSectionMap

/-!
# The unit section of the inverse image of a global section of a sheaf of modules

A global section `t : O ⟶ N` of a sheaf of `O`-modules is determined by the global section
`⊤ ⟶ O ⟶ N` of the underlying sheaf of sets, the unit section followed by `t`. For the inverse
image `Φ⁻¹N` of sheaves of modules along a finite-product-preserving functor `Φ` between
categories of sheaves of sets (Stacks 03D2), the global section `Φ⁻¹t` of `Φ⁻¹N` (read through
`Φ⁻¹O ≅ Φ⁻¹(unit O)`) corresponds to the image of that global section of sets along `Φ`
(`CategoryTheory.Functor.globalSectionMap`): the underlying sheaf of sets of `Φ⁻¹N` is `Φ` of
that of `N`, and the unit section of `Φ⁻¹O` is the image of the unit section of `O`.

## Main results

* `Stacks.Sheaves.ToposPullback.ringOneHom_comp_map_pullbackModuleUnitIso_hom_comp_map`

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe ww ww' vv uu vv' uu'

namespace CategoryTheory.Sheaf

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}

/-- Equal morphisms of sheaves of sets agree on every section. -/
theorem sectionsFunctor_map_congr {A B : Sheaf J (Type ww)} {m m' : A ⟶ B} (h : m = m')
    (U : Cᵒᵖ) (p : (sectionsFunctor J U).obj A) :
    (sectionsFunctor J U).map m p = (sectionsFunctor J U).map m' p := by
  rw [h]

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  [IsIso (terminalComparison Φ)] (O : Sheaf K RingCat.{ww'})

/-- **The inverse image of a global section, on the unit section**: for a global section
`t : O ⟶ N`, the unit section of `Φ⁻¹O` followed by `Φ⁻¹O ≅ Φ⁻¹(unit O) ⟶ Φ⁻¹N` is the image
along `Φ` of the unit section of `O` followed by `t`. -/
theorem ringOneHom_comp_map_pullbackModuleUnitIso_hom_comp_map {N : SheafOfModules.{ww'} O}
    (t : SheafOfModules.unit O ⟶ N) :
    ringOneHom (pullbackRingSheaf J Φ O) ≫ (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
        ((pullbackModuleUnitIso J Φ O).hom ≫ (pullbackModuleFunctor J Φ O).map t) =
      Φ.globalSectionMap (ringOneHom O ≫ (moduleSheafFunctor O).map t) := by
  have h1 : ringOneHom (pullbackRingSheaf J Φ O) =
      CategoryTheory.inv (terminalComparison Φ) ≫ Φ.map (ringOneHom O) :=
    (IsIso.inv_hom_id_assoc (terminalComparison Φ) _).symm.trans
      (congrArg (CategoryTheory.inv (terminalComparison Φ) ≫ ·)
        (ToposPushforward.ringOneHom_comp J Φ O).symm)
  have h2 : (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
      ((pullbackModuleUnitIso J Φ O).hom ≫ (pullbackModuleFunctor J Φ O).map t) =
        Φ.map ((moduleSheafFunctor O).map t) :=
    ((moduleSheafFunctor (pullbackRingSheaf J Φ O)).map_comp _ _).trans
      (((congrArg (· ≫ (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map
        ((pullbackModuleFunctor J Φ O).map t))
          ((moduleSheafFunctor (pullbackRingSheaf J Φ O)).map_id _)).trans
            (Category.id_comp _)).trans (moduleSheafFunctor_map_pullbackModuleMap J Φ O t))
  exact (congrArg (ringOneHom (pullbackRingSheaf J Φ O) ≫ ·) h2).trans
    ((congrArg (· ≫ Φ.map ((moduleSheafFunctor O).map t)) h1).trans
      ((Category.assoc _ _ _).trans (congrArg (CategoryTheory.inv (terminalComparison Φ) ≫ ·)
        (Φ.map_comp _ _).symm)))

end Stacks.Sheaves.ToposPullback

end
