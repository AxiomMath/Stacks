module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicSectionsConstant
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData

/-!
# Existence of a regular meromorphic section on an integral scheme

Let `X` be an integral scheme with generic point `η` and `F` a quasi-coherent sheaf of
`𝒪_X`-modules. Every element `v` of the stalk `F_η` determines a meromorphic section of `F`,
which is regular when multiplication by `v` is injective on the local ring `𝒪_{X,η}`. An
invertible module on an integral scheme has a regular meromorphic section.

## Main definitions

* `AlgebraicGeometry.constantGenericStalkSections`: the global section of the constant
  generic-stalk module sheaf which is constantly a given element of the generic stalk.
* `AlgebraicGeometry.meromorphicSectionOfConstantGenericStalk`: the meromorphic section of `F`
  determined by an element of the stalk of `F` at the generic point.

## Main results

* `AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk`: the
  meromorphic section determined by `v` is regular when multiplication by `v` is injective on
  the local ring at the generic point.
* `AlgebraicGeometry.exists_isRegularMeromorphicSection_of_isIntegral`: an invertible module on
  an integral scheme has a regular meromorphic section.

## References

* [Stacks Project, Tag 02OZ](https://stacks.math.columbia.edu/tag/02OZ)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02OX](https://stacks.math.columbia.edu/tag/02OX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace CategoryTheory.SheafOfModules

/-- The morphism from the structure sheaf attached to a global section `t` of a sheaf of modules
sends a section `r` over `V` to `r • t` over `V`. -/
theorem unitHomEquiv_symm_val_app_apply {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] (M : SheafOfModules.{u} R) (t : M.sections)
    (V : Cᵒᵖ) (r : R.obj.obj V) :
    (M.unitHomEquiv.symm t).val.app V r = r • t.eval V := rfl

end CategoryTheory.SheafOfModules

namespace AlgebraicGeometry

/-- The sections of an isomorphism of sheaves of rings over a fixed open set are injective. -/
theorem injective_ringSheafIso_hom_app {Y : TopCat.{u}}
    {A B : TopCat.Sheaf RingCat.{u} Y} (e : A ≅ B) (V : (Opens Y)ᵒᵖ) :
    Function.Injective (e.hom.hom.app V) := by
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{u}).map e.hom) :=
    Functor.map_isIso _ e.hom
  have : IsIso (e.hom.hom.app V) :=
    NatIso.isIso_app_of_isIso
      ((sheafToPresheaf (Opens.grothendieckTopology Y) RingCat.{u}).map e.hom) V
  exact (ConcreteCategory.bijective_of_isIso (e.hom.hom.app V)).1

variable (X : Scheme.{u}) [IsIntegral X] (F : X.Modules)

/-- The isomorphism of sheaves of rings, valued in `RingCat`, between the sheaf of meromorphic
functions of an integral scheme and the constant sheaf on its function field. -/
abbrev totalQuotientRingSheafIsoConstant :
    Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X) (totalQuotientSheaf X.sheaf) ≅
      Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X)
        (constantSheafOnSpace X CommRingCat.{u} X.functionField) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).mapIso (totalQuotientSheafIsoConstant X).val

/-- The global section of the constant generic-stalk module sheaf of `F` which is constantly a
given element `v` of the stalk of `F` at the generic point, viewed as a module over the sheaf of
meromorphic functions through the comparison isomorphism of Tag 01X5 part (1). -/
def constantGenericStalkSections (v : F.presheaf.stalk (genericPoint X)) :
    ((SheafOfModules.restrictScalars (totalQuotientRingSheafIsoConstant X).hom).obj
      (constantGenericStalkModuleSheaf X F)).sections :=
  PresheafOfModules.sectionsMk (fun V => constantGenericStalkModuleSection X F V.unop v)
    fun {_ _} f => (constantGenericStalkModuleSection_naturality X F f.unop v).symm

/-- The meromorphic section of `F` determined by an element `v` of the stalk of `F` at the
generic point of an integral scheme: the global section of `K_X(F)` which the comparison
isomorphism of Tag 01X5 part (2) carries to the constant section of `v`. -/
def meromorphicSectionOfConstantGenericStalk [F.IsQuasicoherent]
    (v : F.presheaf.stalk (genericPoint X)) : MeromorphicSection X.sheaf F :=
  SheafOfModules.sectionsMap (meromorphicSectionSheafIsoConstant X F).val.inv
    (constantGenericStalkSections X F v)

/-- The sections of the sheaf of meromorphic functions over an open set omitting the generic
point of an integral scheme form a subsingleton. -/
theorem subsingleton_unitTotalQuotientRingSheaf_of_notMem {V : (Opens X)ᵒᵖ}
    (hV : genericPoint X ∉ V.unop) :
    Subsingleton ((SheafOfModules.unit (Stacks.Sheaves.Differentials.ringSheaf
      (C := Opens X) (J := Opens.grothendieckTopology X)
      (totalQuotientSheaf X.sheaf))).val.obj V) := by
  have hbot : V = op (⊥ : Opens X) :=
    (Opposite.op_unop V).symm.trans (congrArg op (Opens.eq_bot_of_genericPoint_notMem hV))
  rw [hbot]
  exact SheafOfModules.subsingleton_obj_bot _ (SheafOfModules.unit _)

/-- Multiplication by the constant section of `v` is injective on the sections of the constant
sheaf on the function field over an open set containing the generic point, provided
multiplication by `v` is injective on the local ring at the generic point. -/
theorem injective_smul_constantGenericStalkModuleSection
    {v : F.presheaf.stalk (genericPoint X)}
    (hv : Function.Injective fun r : X.presheaf.stalk (genericPoint X) => r • v)
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective fun a : (Stacks.Sheaves.Differentials.ringSheaf (C := Opens X)
        (J := Opens.grothendieckTopology X)
        (constantSheafOnSpace X CommRingCat.{u} X.functionField)).obj.obj (op U) =>
      a • constantGenericStalkModuleSection X F U v := by
  have hne : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  intro a b hab
  obtain ⟨c, hc⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U hne a
  obtain ⟨d, hd⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U hne b
  have hcd : c • v = d • v :=
    (constantGenericStalkModuleSection_bijective X F U hU).1
      ((constantGenericStalkModuleSection_smul X F U c a hc v).trans
        (hab.trans (constantGenericStalkModuleSection_smul X F U d b hd v).symm))
  exact hc.trans ((congrArg _ (hv hcd)).trans hd.symm)

/-- Multiplication by the constant section of `v` is a monomorphism from the sheaf of
meromorphic functions to the constant generic-stalk module sheaf when multiplication by `v` is
injective on the local ring at the generic point. -/
theorem mono_unitHomEquiv_symm_constantGenericStalkSections
    {v : F.presheaf.stalk (genericPoint X)}
    (hv : Function.Injective fun r : X.presheaf.stalk (genericPoint X) => r • v) :
    Mono ((SheafOfModules.unitHomEquiv _).symm (constantGenericStalkSections X F v)) := by
  classical
  refine SheafOfModules.mono_of_forall_app_injective _ fun V a b hab => ?_
  by_cases hV : genericPoint X ∈ V.unop
  · refine injective_ringSheafIso_hom_app (totalQuotientRingSheafIsoConstant X) V ?_
    exact injective_smul_constantGenericStalkModuleSection X F hv V.unop hV hab
  · exact @Subsingleton.elim _
      (subsingleton_unitTotalQuotientRingSheaf_of_notMem X hV) a b

/-- The meromorphic section determined by an element `v` of the generic stalk is regular when
multiplication by `v` is injective on the local ring at the generic point. -/
theorem isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk [F.IsQuasicoherent]
    {v : F.presheaf.stalk (genericPoint X)}
    (hv : Function.Injective fun r : X.presheaf.stalk (genericPoint X) => r • v) :
    IsRegularMeromorphicSection X.sheaf F (meromorphicSectionOfConstantGenericStalk X F v) := by
  have := mono_unitHomEquiv_symm_constantGenericStalkSections X F hv
  have hgoal : Mono ((SheafOfModules.unitHomEquiv _).symm (constantGenericStalkSections X F v) ≫
      (meromorphicSectionSheafIsoConstant X F).val.inv) := inferInstance
  rwa [SheafOfModules.unitHomEquiv_symm_comp] at hgoal

/-- An invertible sheaf of modules on an integral scheme has a regular meromorphic section. -/
@[stacks 02OZ "part (1)"]
theorem exists_isRegularMeromorphicSection_of_isIntegral
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] :
    ∃ s : MeromorphicSection X.sheaf F, IsRegularMeromorphicSection X.sheaf F s := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isInvertible F
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F := ‹_›
  obtain ⟨W, hηW, t, hb⟩ :=
    Stacks.Divisors.isTrivializedNear_of_isInvertible F (genericPoint X)
  exact ⟨meromorphicSectionOfConstantGenericStalk X F (F.presheaf.germ W (genericPoint X) hηW t),
    isRegularMeromorphicSection_meromorphicSectionOfConstantGenericStalk X F (hb _ hηW).injective⟩

end AlgebraicGeometry

end
