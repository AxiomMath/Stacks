module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange

/-!
# The unit of derived base change at a single complex

Let `f : R → S` be a flat homomorphism of commutative rings. Termwise extension of scalars and
restriction of scalars are adjoint, and the induced adjunction on cochain complexes has a
termwise unit; at a complex concentrated in one degree that unit is the single complex on the
unit `N ⟶ S ⊗_R N` of the module-level adjunction. Passing to the derived category identifies
the unit of the adjunction of [stacks 0GMT] at a single complex with the same morphism, and
therefore turns the vanishing of the derived base change of an `Ext` class into the vanishing of
that class composed with the unit.

## Main results

* `CategoryTheory.Adjunction.mapHomologicalComplex_unit_app_single`: the unit of the adjunction
  induced on homological complexes by an adjunction of additive functors is, at a complex
  concentrated in one degree, the single complex on the unit of the original adjunction.
* `StacksDraft.DerivedHom.SingleBaseChange.comp_Q_map_single_map_unit_eq_zero` and
  `StacksDraft.DerivedHom.SingleBaseChange.comp_singleFunctor_map_unit_eq_zero`: a morphism of
  `D(R)` into a single complex which is annihilated by derived extension of scalars is
  annihilated by composition with the single complex on the unit.
* `StacksDraft.DerivedHom.SingleBaseChange.ext_comp_mk₀_unit_eq_zero`: an `Ext` class over `R`
  whose derived base change vanishes is killed by composition with the degree-zero class of the
  unit `N ⟶ S ⊗_R N`.

## Implementation notes

The last statement is proved by shifting the class down: a morphism `K ⟶ L⟦n⟧` is carried by the
inverse shift to a morphism `K⟦-n⟧ ⟶ L`, and postcomposition with an `n`-fold shift becomes
postcomposition with the morphism itself.

## References

* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open StacksDraft.DerivedHom.HomModuleBaseChange

universe u

namespace CategoryTheory

/-- **The unit of the adjunction induced on homological complexes is termwise.** At a complex
concentrated in the degree `j`, the unit of the adjunction `F.mapHomologicalComplex c ⊣
G.mapHomologicalComplex c` induced by an adjunction `F ⊣ G` of additive functors is the single
complex on the unit `N ⟶ G (F N)`, read through the comparison of `F` and `G` with the single
complex functors. -/
public theorem Adjunction.mapHomologicalComplex_unit_app_single
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
    {ι : Type*} (c : ComplexShape ι) [DecidableEq ι] (j : ι) (N : A) :
    (adj.mapHomologicalComplex c).unit.app ((single A c j).obj N) ≫
        (G.mapHomologicalComplex c).map
            ((singleMapHomologicalComplex F c j).hom.app N) ≫
          (singleMapHomologicalComplex G c j).hom.app (F.obj N) =
      (single A c j).map (adj.unit.app N) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [Adjunction.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
      singleMapHomologicalComplex_hom_app_self, single_map_f_self]
  · apply (isZero_single_obj_X c j N i h).eq_of_src

end CategoryTheory

namespace StacksDraft.DerivedHom.SingleBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A morphism `f ≫ F.map g` vanishes if it does after composing with a natural isomorphism. -/
private theorem comp_map_eq_zero_of_comp_hom_app_comp_map_eq_zero
    {C D : Type*} [Category C] [Category D] [Preadditive D] {F G : C ⥤ D} (e : F ≅ G)
    {X : D} {Y Z : C} (f : X ⟶ F.obj Y) (g : Y ⟶ Z)
    (h : (f ≫ e.hom.app Y) ≫ G.map g = 0) : f ≫ F.map g = 0 := by
  refine zero_of_comp_mono (e.hom.app Z) ?_
  rw [Category.assoc, e.hom.naturality, ← Category.assoc]
  exact h

/-- **Derived base change annihilates a morphism into a single complex only if the termwise unit
does.** Let `S` be a flat `R`-algebra and let `F` be a total left derived functor of termwise
extension of scalars. A morphism of `D(R)` from `K` to the single complex on `N`, annihilated by
`F`, is annihilated by composition with the single complex on the unit `N ⟶ S ⊗_R N`. -/
public theorem comp_Q_map_single_map_unit_eq_zero
    (hflat : Module.Flat R S)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    {K : DerivedCategory (ModuleCat.{u} R)} (N : ModuleCat.{u} R)
    (ξ : K ⟶ DerivedCategory.Q.obj ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N))
    (hξ : F.map ξ = 0) :
    ξ ≫ DerivedCategory.Q.map ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).unit.app N)) = 0 := by
  have : IsIso comparison := isIso_comparison_of_flat hflat F comparison
  have : IsIso (comparison.app ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N)) :=
    inferInstance
  have h0 := (map_eq_zero_iff_comp_unit_eq_zero F comparison ξ).mp hξ
  rw [unit_app_Q_eq F comparison ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N),
    ← Category.assoc] at h0
  have hz := zero_of_comp_mono _ h0
  rw [← Adjunction.mapHomologicalComplex_unit_app_single
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)) (ComplexShape.up ℤ) 0 N]
  simp only [Functor.map_comp, ← Category.assoc, hz, Limits.zero_comp]

/-- The previous statement with the single complex taken in the derived category: a morphism of
`D(R)` into `single N` annihilated by derived extension of scalars is annihilated by composition
with `single` applied to the unit `N ⟶ S ⊗_R N`. -/
public theorem comp_singleFunctor_map_unit_eq_zero
    (hflat : Module.Flat R S)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    {K : DerivedCategory (ModuleCat.{u} R)} (N : ModuleCat.{u} R)
    (ξ : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)
    (hξ : F.map ξ = 0) :
    ξ ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).unit.app N) = 0 := by
  have hcore := comp_Q_map_single_map_unit_eq_zero hflat F comparison N
    (ξ ≫ (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).hom.app N)
    (by rw [F.map_comp, hξ, Limits.zero_comp])
  exact comp_map_eq_zero_of_comp_hom_app_comp_map_eq_zero
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0) ξ _ hcore

/-- **An `Ext` class killed by derived base change is killed by the unit.** Let `S` be a flat
`R`-algebra and let `F` be a total left derived functor of termwise extension of scalars. If the
morphism of `D(R)` attached to a class `x` in `Ext^n_R(M, N)` is annihilated by `F`, then `x`
composed with the degree-zero class of the unit `N ⟶ S ⊗_R N` vanishes. -/
public theorem ext_comp_mk₀_unit_eq_zero
    (hflat : Module.Flat R S)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [F.CommShift ℤ]
    {M N : ModuleCat.{u} R} {n : ℕ} (x : Ext.{u} M N n)
    (hx : F.map x.hom = 0) :
    x.comp (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).unit.app N))
      (add_zero n) = 0 := by
  have hmm : (n : ℤ) + (-(n : ℤ)) = 0 := by ring
  set T := DerivedCategory (ModuleCat.{u} R) with hT
  set θ := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).unit.app N with hθ
  set ψ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map θ with hψ
  set e := shiftFunctorCompIsoId T (n : ℤ) (-(n : ℤ)) hmm with he
  have hFsh : F.map ((shiftFunctor T (-(n : ℤ))).map x.hom) = 0 := by
    have hnat := F.commShiftIso_hom_naturality x.hom (-(n : ℤ))
    rw [hx] at hnat
    simp only [Functor.map_zero, Limits.comp_zero] at hnat
    exact zero_of_comp_mono _ hnat
  have hunit := comp_singleFunctor_map_unit_eq_zero hflat F comparison N
    ((shiftFunctor T (-(n : ℤ))).map x.hom ≫
      e.hom.app ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))
    (by rw [F.map_comp, hFsh, Limits.zero_comp])
  have hzz : (shiftFunctor T (-(n : ℤ))).map (x.hom ≫ (shiftFunctor T (n : ℤ)).map ψ) = 0 := by
    rw [Functor.map_comp]
    exact comp_map_eq_zero_of_comp_hom_app_comp_map_eq_zero e _ ψ hunit
  have hfin : x.hom ≫ (shiftFunctor T (n : ℤ)).map ψ = 0 := by
    apply (shiftFunctor T (-(n : ℤ))).map_injective
    rw [hzz, Functor.map_zero]
  rw [Ext.ext_iff, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, Ext.zero_hom]
  exact hfin

end StacksDraft.DerivedHom.SingleBaseChange

end
