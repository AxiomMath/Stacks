module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.RingTheory.Dualizing.DerivedTorsion
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Flat change of rings for torsion derived categories (Stacks chapter Dualizing Complexes)

Let `A → B` be a flat ring map inducing an isomorphism `A/I ≅ B/IB` for a finitely generated
ideal `I ⊆ A`. Then derived extension and restriction of scalars are quasi-inverse
equivalences between the full subcategories of `D(A)` and `D(B)` consisting of the objects
whose cohomology is `I`-power torsion, respectively `IB`-power torsion. Concretely: the
ordinary adjunction between extension and restriction of scalars derives to an adjunction on
derived categories, its unit and counit are isomorphisms on power-torsion objects (this is
where flatness and the isomorphism modulo `I` enter), and the adjunction therefore restricts
to an equivalence of the two full subcategories.

The equivalence is produced together with natural isomorphisms identifying its two functors,
after inclusion into the ambient derived categories, with derived base change and restriction
of scalars. Those isomorphisms are what pins the statement down: without them the conclusion
would only assert that the two subcategories happen to be equivalent.

## Main results

* `Dualizing.powerTorsionDerivedEquivalence` — the equivalence, with its two functors
  canonically identified with derived extension and restriction of scalars.

## References

* [Stacks Project, Tag 0AM0](https://stacks.math.columbia.edu/tag/0AM0)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

private lemma isIso_Q_map_mapHomologicalComplex_app
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] [HasDerivedCategory D]
    {H₁ H₂ : C ⥤ D} [H₁.Additive] [H₂.Additive]
    [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
    [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
    (α : H₁ ⟶ H₂) (P : CochainComplex C ℤ)
    (h : ∀ i, IsIso (α.app ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj P))) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app P)) := by
  have hq : HomologicalComplex.quasiIso D (ComplexShape.up ℤ)
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app P) := by
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (ShortComplex.homologyMap ((P.sc i).mapNatTrans α))
    rw [ShortComplex.homologyMap_mapNatTrans]
    have : IsIso (α.app (P.sc i).homology) := h i
    infer_instance
  exact (Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))) _ hq

private lemma mapDerivedAdjunction_unit_app_isIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex C ℤ)
    (hη : ∀ i, IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj P))) :
    IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).unit.app
      (DerivedCategory.Q.obj P)) := by
  have : IsIso (DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P)) :=
    isIso_Q_map_mapHomologicalComplex_app adj.unit P hη
  rw [CategoryTheory.Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
  infer_instance

private lemma mapDerivedAdjunction_counit_app_isIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (P : CochainComplex D ℤ)
    (hε : ∀ i, IsIso (adj.counit.app
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).obj P))) :
    IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app
      (DerivedCategory.Q.obj P)) := by
  have : IsIso (DerivedCategory.Q.map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app P)) :=
    isIso_Q_map_mapHomologicalComplex_app adj.counit P hε
  rw [CategoryTheory.Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
  infer_instance

private lemma mapDerivedAdjunction_unit_isIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : DerivedCategory C)
    (hη : ∀ i, IsIso (adj.unit.app ((DerivedCategory.homologyFunctor C i).obj X))) :
    IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).unit.app X) := by
  let P := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hηP : ∀ i, IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj P)) := fun i ↦
    (NatTrans.isIso_app_iff_of_iso adj.unit
      ((DerivedCategory.homologyFunctorFactors C i).app P).symm).2
      ((NatTrans.isIso_app_iff_of_iso adj.unit
        ((DerivedCategory.homologyFunctor C i).mapIso e)).2 (hη i))
  exact (NatTrans.isIso_app_iff_of_iso (CategoryTheory.Adjunction.mapDerivedCategory adj).unit
    e.symm).2
    (mapDerivedAdjunction_unit_app_isIso adj P hηP)

private lemma mapDerivedAdjunction_counit_isIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (X : DerivedCategory D)
    (hε : ∀ i, IsIso (adj.counit.app ((DerivedCategory.homologyFunctor D i).obj X))) :
    IsIso ((CategoryTheory.Adjunction.mapDerivedCategory adj).counit.app X) := by
  let P := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hεP : ∀ i, IsIso (adj.counit.app
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).obj P)) := fun i ↦
    (NatTrans.isIso_app_iff_of_iso adj.counit
      ((DerivedCategory.homologyFunctorFactors D i).app P).symm).2
      ((NatTrans.isIso_app_iff_of_iso adj.counit
        ((DerivedCategory.homologyFunctor D i).mapIso e)).2 (hε i))
  exact (NatTrans.isIso_app_iff_of_iso (CategoryTheory.Adjunction.mapDerivedCategory adj).counit
    e.symm).2
    (mapDerivedAdjunction_counit_app_isIso adj P hεP)

private lemma isIPowerTorsion_of_moduleIso
    {R : Type*} [CommRing R] {I : Ideal R}
    (M N : ModuleCat R) (e : M ≅ N)
    (hN : IsIPowerTorsion R N I) : IsIPowerTorsion R M I := by
  intro m
  obtain ⟨k, hk, hkill⟩ := hN (e.hom m)
  refine ⟨k, hk, fun a ha ↦ ?_⟩
  simpa only [map_smul, map_zero, ← ModuleCat.comp_apply, e.hom_inv_id,
    ModuleCat.id_apply]
    using congrArg e.inv (hkill a ha)

private lemma extendScalars_preserves_powerTorsion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) (hM : IsIPowerTorsion R M I) :
    IsIPowerTorsion S ((ModuleCat.extendScalars.{u, v, max u v w}
      (algebraMap R S)).obj M) (I.map (algebraMap R S)) := by
  let P : ObjectProperty (ModuleCat.{max u v w} R) := fun X ↦ IsIPowerTorsion R X I
  obtain ⟨e, he⟩ := (IPowerTorsion.baseChange_equiv_of_quotientMap_bijective
    R S I hI hflat hq).2.2
  let iso := Classical.choice he
  let X : P.FullSubcategory := ⟨M, hM⟩
  let Y := e.functor.obj X
  let h : Y.obj ⟶ (ModuleCat.extendScalars.{u, v, max u v w}
      (algebraMap R S)).obj M := iso.hom.app X
  intro z
  obtain ⟨y, hy⟩ := ((ConcreteCategory.isIso_iff_bijective h).mp inferInstance).2 z
  obtain ⟨n, hn, hkill⟩ := Y.property y
  refine ⟨n, hn, fun b hb ↦ ?_⟩
  calc
    b • z = b • h.hom y := by rw [hy]
    _ = h.hom (b • y) := by simp
    _ = h.hom 0 := by rw [hkill b hb]
    _ = 0 := map_zero h.hom

private lemma restrictScalars_preserves_powerTorsion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (M : ModuleCat.{max u v w} S)
    (hM : IsIPowerTorsion S M (I.map (algebraMap R S))) :
    IsIPowerTorsion R ((ModuleCat.restrictScalars.{max u v w} (algebraMap R S)).obj M) I := by
  intro m
  obtain ⟨n, hn, hkill⟩ := hM m
  refine ⟨n, hn, fun a ha ↦ ?_⟩
  show algebraMap R S a • m = 0
  exact hkill _ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha)

private lemma extendRestrictScalars_unit_isIso_of_powerTorsion
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) (hM : IsIPowerTorsion R M I) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj.{max u w, u, v}
      (algebraMap R S)).unit.app M) := by
  have hbase := (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
    R S I hflat).2 hq M hM
  let e := TensorProduct.comm R S M
  have hunit0 : Function.Bijective (fun m : M => (1 : S) ⊗ₜ[R] m) := by
    have he (m : M) : e ((1 : S) ⊗ₜ[R] m) = m ⊗ₜ[R] (1 : S) := by simp [e]
    constructor
    · intro x y hxy
      have hh := congrArg e hxy
      rw [he, he] at hh
      exact hbase.1 hh
    · intro z
      obtain ⟨m, hm⟩ := hbase.2 (e z)
      refine ⟨m, ?_⟩
      apply e.injective
      rw [he m]
      simpa using hm
  let E := IPowerTorsion.tensorModuleCatEquiv (R := R) (S := S) M
  have hunit : Function.Bijective (fun m : M => E ((1 : S) ⊗ₜ[R] m)) :=
    E.bijective.comp hunit0
  apply (ConcreteCategory.isIso_iff_bijective _).2
  convert hunit using 1 <;> try rfl

private theorem preservesFiniteLimits_extendScalars_flat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, max v (max u w)} f) := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have : (ModuleCat.extendScalars.{u, v, max v (max u w)} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} f).left_adjoint_additive
  have hExact : ∀ T : ShortComplex (ModuleCat.{max v (max u w)} R), T.Exact →
      (T.map (ModuleCat.extendScalars.{u, v, max v (max u w)} f)).Exact := by
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact S hT
  have hBoth : PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, max v (max u w)} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, v, max v (max u w)} f) :=
    ((Functor.exact_tfae (ModuleCat.extendScalars.{u, v, max v (max u w)} f)).out 2 4).mp hExact
  exact hBoth.1

private noncomputable def flatDerivedExtensionIso
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    (f : A →+* B) (_hf : f.Flat)
    [(ModuleCat.extendScalars.{u, v, max v (max u w)} f).Additive]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, v, max v (max u w)} f)]
    [PreservesFiniteColimits (ModuleCat.extendScalars.{u, v, max v (max u w)} f)] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, v, w} f).functor ≅
      (ModuleCat.extendScalars.{u, v, max v (max u w)} f).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, v, max v (max u w)} f
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, v, w} f
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{max v (max u w)} A) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomologicalComplex.quasiIso (ModuleCat.{max v (max u w)} A) (ComplexShape.up ℤ))
      F.mapDerivedCategory F.mapDerivedCategoryFactors
  exact Functor.leftDerivedNatIso D.functor F.mapDerivedCategory D.comparison
    F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{max v (max u w)} A) (ComplexShape.up ℤ)) (Iso.refl _)

private noncomputable def liftAdjunctionOfObjectProperties
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj)) :
    (Q.lift (P.ι ⋙ F) (fun X ↦ hF X)) ⊣ (P.lift (Q.ι ⋙ G) (fun Y ↦ hG Y)) := by
  let homEquiv (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
      ((Q.lift (P.ι ⋙ F) (fun Z ↦ hF Z)).obj X ⟶ Y) ≃
        (X ⟶ (P.lift (Q.ι ⋙ G) (fun Z ↦ hG Z)).obj Y) := {
    toFun := fun f ↦ ObjectProperty.homMk (adj.homEquiv X.obj Y.obj f.hom)
    invFun := fun g ↦ ObjectProperty.homMk ((adj.homEquiv X.obj Y.obj).symm g.hom)
    left_inv := fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (adj.homEquiv X.obj Y.obj).left_inv f.hom
    right_inv := fun g ↦ by
      apply ObjectProperty.hom_ext
      exact (adj.homEquiv X.obj Y.obj).right_inv g.hom }
  exact Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      apply ObjectProperty.hom_ext
      exact adj.homEquiv_naturality_left_symm f.hom g.hom
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply ObjectProperty.hom_ext
      exact adj.homEquiv_naturality_right f.hom g.hom }

private lemma liftAdjunctionOfObjectProperties_unit_app_isIso
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))
    (X : P.FullSubcategory) (h : IsIso (adj.unit.app X.obj)) :
    IsIso ((liftAdjunctionOfObjectProperties adj hF hG).unit.app X) := by
  have heq : P.ι.map ((liftAdjunctionOfObjectProperties adj hF hG).unit.app X) =
      adj.unit.app X.obj := by
    simp [liftAdjunctionOfObjectProperties, Adjunction.mkOfHomEquiv_unit_app, adj.homEquiv_unit]
  have : IsIso (P.ι.map ((liftAdjunctionOfObjectProperties adj hF hG).unit.app X)) := by
    rw [heq]
    exact h
  have : P.ι.ReflectsIsomorphisms := P.fullyFaithfulι.reflectsIsomorphisms
  exact isIso_of_reflects_iso _ P.ι

private lemma liftAdjunctionOfObjectProperties_counit_app_isIso
    {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D}
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ Y : Q.FullSubcategory, P (G.obj Y.obj))
    (Y : Q.FullSubcategory) (h : IsIso (adj.counit.app Y.obj)) :
    IsIso ((liftAdjunctionOfObjectProperties adj hF hG).counit.app Y) := by
  have heq : Q.ι.map ((liftAdjunctionOfObjectProperties adj hF hG).counit.app Y) =
      adj.counit.app Y.obj := by
    simp [liftAdjunctionOfObjectProperties, Adjunction.mkOfHomEquiv_counit_app,
      adj.homEquiv_counit]
  have : IsIso (Q.ι.map ((liftAdjunctionOfObjectProperties adj hF hG).counit.app Y)) := by
    rw [heq]
    exact h
  have : Q.ι.ReflectsIsomorphisms := Q.fullyFaithfulι.reflectsIsomorphisms
  exact isIso_of_reflects_iso _ Q.ι

/-- **Stacks 0AM0.** Flat base change and restriction of scalars are quasi-inverse on
the derived categories of objects with power-torsion cohomology. -/
@[stacks 0AM0]
theorem powerTorsionDerivedEquivalence
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (hI : I.FG) (hflat : Module.Flat A B)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map)) :
    ∃ e : PowerTorsionDerivedCategory.{u, max u v w} A I hI ≌
        PowerTorsionDerivedCategory.{v, max u v w} B
          (I.map (algebraMap A B)) (Ideal.FG.map hI (algebraMap A B)),
      Nonempty (e.functor ⋙
          (derivedPowerTorsionProperty B (I.map (algebraMap A B))
            (Ideal.FG.map hI (algebraMap A B))).ι ≅
        (derivedPowerTorsionProperty A I hI).ι ⋙
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, v, w}
            (algebraMap A B)).functor) ∧
      Nonempty (e.inverse ⋙ (derivedPowerTorsionProperty A I hI).ι ≅
        (derivedPowerTorsionProperty B (I.map (algebraMap A B))
          (Ideal.FG.map hI (algebraMap A B))).ι ⋙
          (ModuleCat.restrictScalars.{max u v w} (algebraMap A B)).mapDerivedCategory) := by
  have hflat' : (algebraMap A B).Flat := by
    rw [RingHom.Flat, toAlgebra_algebraMap]
    exact hflat
  let IB := I.map (algebraMap A B)
  let hIB := Ideal.FG.map hI (algebraMap A B)
  let MA := ModuleCat.{max v (max u w)} A
  let MB := ModuleCat.{max v (max u w)} B
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} (algebraMap A B)
  let F := ModuleCat.extendScalars.{u, v, max v (max u w)} (algebraMap A B)
  let G := ModuleCat.restrictScalars.{max v (max u w)} (algebraMap A B)
  have : F.IsLeftAdjoint := adj.isLeftAdjoint
  have : PreservesFiniteColimits F := inferInstance
  have : F.Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits F := preservesFiniteLimits_extendScalars_flat A B _ hflat'
  have : G.Additive := adj.right_adjoint_additive
  have : PreservesFiniteLimits G := inferInstance
  have : PreservesFiniteColimits G := inferInstance
  let Fd := F.mapDerivedCategory
  let Gd := G.mapDerivedCategory
  let adjD := CategoryTheory.Adjunction.mapDerivedCategory adj
  let P : ObjectProperty (DerivedCategory MA) := derivedPowerTorsionProperty A I hI
  let Q : ObjectProperty (DerivedCategory MB) := derivedPowerTorsionProperty B IB hIB
  have hF (X : P.FullSubcategory) : Q (Fd.obj X.obj) := by
    intro i
    exact isIPowerTorsion_of_moduleIso _ _ ((mapDerivedCategoryHomologyIso F i).app X.obj)
      (extendScalars_preserves_powerTorsion A B I hI hflat hquot
        ((DerivedCategory.homologyFunctor MA i).obj X.obj) (X.property i))
  have hG (Y : Q.FullSubcategory) : P (Gd.obj Y.obj) := by
    intro i
    exact isIPowerTorsion_of_moduleIso _ _ ((mapDerivedCategoryHomologyIso G i).app Y.obj)
      (restrictScalars_preserves_powerTorsion A B I
        ((DerivedCategory.homologyFunctor MB i).obj Y.obj) (Y.property i))
  let adjP := liftAdjunctionOfObjectProperties adjD hF hG
  have (X : P.FullSubcategory) : IsIso (adjP.unit.app X) :=
    liftAdjunctionOfObjectProperties_unit_app_isIso adjD hF hG X <|
      mapDerivedAdjunction_unit_isIso adj X.obj fun i ↦
        extendRestrictScalars_unit_isIso_of_powerTorsion A B I hflat hquot
          ((DerivedCategory.homologyFunctor MA i).obj X.obj) (X.property i)
  have (Y : Q.FullSubcategory) : IsIso (adjP.counit.app Y) :=
    liftAdjunctionOfObjectProperties_counit_app_isIso adjD hF hG Y <|
      mapDerivedAdjunction_counit_isIso adj Y.obj fun i ↦
        (ConcreteCategory.isIso_iff_bijective _).2 <|
          IPowerTorsion.extendRestrictScalarsAdj_counit_app_bijective I hflat hquot _
            (Y.property i)
  exact ⟨adjP.toEquivalence, ⟨(Q.liftCompιIso (P.ι ⋙ Fd) hF).trans
      (Functor.isoWhiskerLeft P.ι (flatDerivedExtensionIso A B (algebraMap A B) hflat').symm)⟩,
    ⟨P.liftCompιIso (Q.ι ⋙ Gd) hG⟩⟩

end Dualizing

-- Tag 0BJC: `V(I + J) = V(I) ∩ V(J)`, with `I + J = I ⊔ J` for ideals; no finite-generation
-- hypothesis is needed.
add_to_stacks 0BJC "intersection_of_zero_loci" PrimeSpectrum.zeroLocus_sup
add_to_ega "I 1.1.2" "(iii), special case" PrimeSpectrum.zeroLocus_sup
add_to_ega "I 1.1.5" "special case" PrimeSpectrum.zeroLocus_sup
