module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologyDerivedHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftFunctorFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionToposQuotient
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.CategoryTheory.Functor.Derived.CoresolutionCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforwardComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward commutes with forgetting the differential graded action

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O_C`-algebras, `B` one of `O_D`-algebras and `φ : B ⟶ f_*A` a unital
homomorphism. This file proves [Stacks, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW):
the square

`Rf_* ⋙ forget ≅ forget ⋙ Rf_* : D(A, d) ⥤ D(O_D)`

commutes, where the top `Rf_*` is the derived pushforward of differential graded modules
(`SheafOfModules.DifferentialGradedModule.derivedToposPushforward`), the bottom one is the derived
pushforward of sheaves of modules, and the two horizontal arrows forget the action.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedModulePushforward`: the derived pushforward
  `Rf_* : D(O_C) ⥤ D(O_D)` of sheaves of modules, the right derived functor of the direct image,
  with its comparison map `derivedModulePushforwardUnit`.
* `SheafOfModules.DifferentialGradedModule.derivedToposPushforwardForgetIso`: **Tag 0FTW**, the
  isomorphism `Rf_* ⋙ forget ≅ forget ⋙ Rf_*`, and `derivedToposPushforwardForgetIso_fac` its
  compatibility with the comparison maps.

## Main results

* `SheafOfModules.DifferentialGradedModule.bijective_Qh_map_of_isUnitFlat`: for a graded
  injective K-injective right differential graded `A`-module `I` and a flat K-flat
  `(O, 0)`-module `Q`, morphisms from `Q` into `I` in `K(O)` are morphisms in `D(O)`.
* `SheafOfModules.DifferentialGradedModule.quasiIso_mapHomologicalComplex_map_of_isDGInjective`:
  the direct image of sheaves of modules carries a quasi-isomorphism from the underlying complex
  of a graded injective K-injective module into a K-injective complex to a quasi-isomorphism.
* `isIso_derivedModulePushforwardUnit_app_of_isDGInjective`: hence `Rf_*` of sheaves of modules is
  computed by `f_*` on the underlying complex of a graded injective K-injective module.

## Implementation notes

The source identifies `Mod(O, 0)` with `Comp(O)`, reads both forgetful functors as derived
pushforwards along identity morphisms, and concludes from Tag 0FTU. Here the argument is the same
mathematics, carried out directly. Both composites are right derived functors of the direct image
of differential graded modules followed by forgetting the action, and two right derived functors
of one functor are canonically isomorphic. For `Rf_* ⋙ forget` this holds because `Rf_*` is
computed on graded injective K-injective modules, so composing it with any functor gives a right
derived functor. For `forget ⋙ Rf_*` it holds as soon as `Rf_*` of sheaves of modules is computed
by `f_*` on the underlying complex of a graded injective K-injective module `I`. That complex
need not be K-injective, and the point is proved as follows. Let `t : I ⟶ J` be a K-injective
resolution of the underlying complex, with mapping cone `E`. Against a flat and K-flat
`(O_C, 0)`-module the underlying complex of `I` behaves as a K-injective complex, by the
adjunction of Tag 0FRP and clause (1) of Tag 0FSI, as in Tag 0FTX; so no such module maps to `E`
nontrivially up to homotopy. A good `(O_D, 0)`-module (Tag 0FSA) has a flat and K-flat pullback
along `(f, (O_C, 0), (O_D, 0) ⟶ f_*(O_C, 0))`, and morphisms out of a pullback are homotopic
exactly when their transposes are; so no good module maps to `f_*E` nontrivially up to homotopy.
Every complex is resolved by a good module (Tag 0FSH), so `f_*E` is acyclic, and `f_*t` is a
quasi-isomorphism.

The ringed topoi have their sites, morphisms and structure sheaves in one universe `u`, the
setting in which the derived pushforward of differential graded modules is constructed.

## References

* [Stacks Project, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW)
* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FTX](https://stacks.math.columbia.edu/tag/0FTX)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

namespace SheafOfModules.DifferentialGradedModule

open DifferentialGradedAlgebra

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

section Site

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J (Type u)]
  (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- A right differential graded `(O, 0)`-module is *flat* when it is flat as a graded module and
K-flat. -/
abbrev IsUnitFlat (Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)) : Prop :=
  RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧ RelativeTensor.IsKFlat Q

/-- A quasi-isomorphism `s : P ⟶ Q` into the underlying complex of a flat `(O, 0)`-module is
refined by a quasi-isomorphism `t : P' ⟶ P` such that precomposition with `t ≫ s` is bijective
on homotopy classes of morphisms into the underlying complex of a graded injective K-injective
right differential graded `A`-module. -/
theorem exists_quasiIso_bijective_precomp_of_isUnitFlat
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (hQ : IsUnitFlat Q)
    {P : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ}
    (s : P ⟶ Q.complex) (hs : QuasiIso s) :
    ∃ (P' : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ) (t : P' ⟶ P),
      QuasiIso t ∧
        (∀ f : P' ⟶ I.complex, ∃ g : Q.complex ⟶ I.complex,
          (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g) =
            (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) ∧
        ∀ g g' : Q.complex ⟶ I.complex,
          (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g) =
              (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (t ≫ s ≫ g') →
            (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g =
              (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g' := by
  obtain ⟨P', t, ht, hP'₁, hP'₂⟩ := exists_flat_quasiIso (ofComplex (Osharp := X.O) P)
  let s' : P' ⟶ Q := homMk (M := P') (N := Q) (t.toHomologicalComplex ≫ s)
  have hs' : QuasiIso s'.toHomologicalComplex :=
    quasiIso_comp (K := P'.complex) (L := P) t.toHomologicalComplex s (hφ := ht) (hφ' := hs)
  have hb := bijective_precomp_structureRestriction A s' ⟨hP'₁, hP'₂⟩ hQ hs' hI hI'
  refine ⟨P'.complex, t.toHomologicalComplex, ht, fun f => ?_, fun g g' hgg' => ?_⟩
  · obtain ⟨γ, hγ⟩ := hb.2 ((HomotopyCategory.quotient _).map
      (homMk (M := P') (N := (structureRestriction A).obj I) f))
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _).map_surjective γ
    refine ⟨g.toHomologicalComplex, ?_⟩
    have hγ' : (HomotopyCategory.quotient _).map (s' ≫ g) =
        (HomotopyCategory.quotient _).map
          (homMk (M := P') (N := (structureRestriction A).obj I) f) :=
      ((HomotopyCategory.quotient _).map_comp _ _).trans hγ
    exact (structure_quotient_map_eq_iff (s' ≫ g) _).2 hγ'
  · let G : Q ⟶ (structureRestriction A).obj I :=
      homMk (M := Q) (N := (structureRestriction A).obj I) g
    let G' : Q ⟶ (structureRestriction A).obj I :=
      homMk (M := Q) (N := (structureRestriction A).obj I) g'
    have h1 : (HomotopyCategory.quotient _).map (s' ≫ G) =
        (HomotopyCategory.quotient _).map (s' ≫ G') :=
      (structure_quotient_map_eq_iff (s' ≫ G) (s' ≫ G')).1 (by
        have e : ∀ k : Q.complex ⟶ I.complex,
            (s' ≫ homMk (M := Q) (N := (structureRestriction A).obj I) k).toHomologicalComplex =
              t.toHomologicalComplex ≫ s ≫ k := fun k =>
          (Category.assoc _ _ _)
        exact (congrArg _ (e g)).trans (hgg'.trans (congrArg _ (e g')).symm))
    rw [Functor.map_comp, Functor.map_comp] at h1
    exact (structure_quotient_map_eq_iff G G').2 (hb.1 h1)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The localization `K(C) ⥤ D(C)` inverts the class of a quasi-isomorphism. -/
private theorem isIso_Qh_map_quotient_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (t : K ⟶ L) (ht : QuasiIso t) :
    IsIso (DerivedCategory.Qh.map
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)) :=
  Localization.inverts _ (_root_.HomotopyCategory.quasiIso _ _) _
    ((_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff t).2
      ((HomologicalComplex.mem_quasiIso_iff _).2 ht))

/-- **For a graded injective K-injective right differential graded `A`-module `I` and a flat
`(O, 0)`-module `Q`, the localization functor `K(O) ⥤ D(O)` is bijective on morphisms from the
underlying complex of `Q` into the underlying complex of `I`.** The underlying complex of `I`
need not be K-injective; it behaves as one against flat and K-flat complexes. -/
theorem bijective_Qh_map_of_isUnitFlat
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (hQ : IsUnitFlat Q) :
    Function.Bijective (fun g : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        Q.complex ⟶ (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          I.complex => DerivedCategory.Qh.map g) := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  let W := _root_.HomotopyCategory.quasiIso (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  have hq : ∀ {P R : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} (s : P ⟶ R),
      W (q.map s) → QuasiIso s := fun s hs =>
    (HomologicalComplex.mem_quasiIso_iff _).1
      ((_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs)
  refine ⟨fun g₁ g₂ h => ?_, fun φ => ?_⟩
  · obtain ⟨Y, s, hs, hs'⟩ :=
      (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh W g₁ g₂).1 h
    obtain ⟨P, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := q.map_surjective s
    obtain ⟨h₁, rfl⟩ := q.map_surjective g₁
    obtain ⟨h₂, rfl⟩ := q.map_surjective g₂
    obtain ⟨P', t, -, -, hinj⟩ :=
      exists_quasiIso_bijective_precomp_of_isUnitFlat A hI hI' hQ s (hq s hs)
    refine hinj h₁ h₂ ?_
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    rw [← Functor.map_comp, ← Functor.map_comp] at hs'
    exact congrArg (q.map t ≫ ·) ((q.map_comp _ _).symm.trans (hs'.trans (q.map_comp _ _)))
  · obtain ⟨@⟨Y, s, hs, f⟩, rfl⟩ := Localization.exists_rightFraction DerivedCategory.Qh W φ
    obtain ⟨P, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨s, rfl⟩ := q.map_surjective s
    obtain ⟨f, rfl⟩ := q.map_surjective f
    obtain ⟨P', t, ht, hsurj, -⟩ :=
      exists_quasiIso_bijective_precomp_of_isUnitFlat A hI hI' hQ s (hq s hs)
    obtain ⟨g, hg⟩ := hsurj (t ≫ f)
    refine ⟨q.map g, ?_⟩
    have : IsIso (DerivedCategory.Qh.map (q.map s)) := Localization.inverts _ W _ hs
    have := isIso_Qh_map_quotient_map t ht
    show DerivedCategory.Qh.map (q.map g) =
      inv (DerivedCategory.Qh.map (q.map s)) ≫ DerivedCategory.Qh.map (q.map f)
    rw [← cancel_epi (DerivedCategory.Qh.map (q.map s)), IsIso.hom_inv_id_assoc,
      ← cancel_epi (DerivedCategory.Qh.map (q.map t))]
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map hg

/-- **Postcomposition with a quasi-isomorphism from the underlying complex of a graded injective
K-injective module into a K-injective complex is bijective on homotopy classes of morphisms out of
a flat `(O, 0)`-module**: both ends are morphisms of `D(O)`. -/
theorem bijective_comp_quotient_map_of_isUnitFlat
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {J : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} [J.IsKInjective]
    (t : I.complex ⟶ J) (ht : QuasiIso t)
    {Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (hQ : IsUnitFlat Q) :
    Function.Bijective (fun g : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        Q.complex ⟶ (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I.complex =>
      g ≫ (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t) := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  have h₁ := bijective_Qh_map_of_isUnitFlat A hI hI' hQ
  have h₂ := CochainComplex.IsKInjective.Qh_map_bijective (q.obj Q.complex) J
  have := isIso_Qh_map_quotient_map t ht
  have key : (fun g : q.obj Q.complex ⟶ q.obj I.complex => g ≫ q.map t) =
      (Equiv.ofBijective _ h₂).symm ∘ (fun k => k ≫ DerivedCategory.Qh.map (q.map t)) ∘
        (Equiv.ofBijective _ h₁) := by
    funext g
    apply (Equiv.ofBijective _ h₂).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply,
      Functor.map_comp]
  rw [key]
  exact (Equiv.bijective _).comp (((asIso (DerivedCategory.Qh.map (q.map t))).homToEquiv
    ).bijective.comp (Equiv.bijective _))

/-- Postcomposition with the shift of the class of `t` is injective on morphisms out of the
underlying complex of a flat `(O, 0)`-module: through the shift equivalence it is postcomposition
with the class of `t` on morphisms out of the translate of the module by `-1`, which is flat. -/
theorem injective_comp_shift_quotient_map_of_isUnitFlat
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {J : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} [J.IsKInjective]
    (t : I.complex ⟶ J) (ht : QuasiIso t)
    {Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (hQ : IsUnitFlat Q)
    (a b : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q.complex ⟶
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I.complex)⟦(1 : ℤ)⟧)
    (hab : a ≫ ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)⟦(1 : ℤ)⟧' =
      b ≫ ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t)⟦(1 : ℤ)⟧') :
    a = b := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  let Q' : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O) :=
    translate (unitDGAlgebra X.O) (-1) Q
  have hQ' : IsUnitFlat Q' :=
    ⟨isGradedFlat_translate (unitDGAlgebra X.O) (-1) Q hQ.1,
      isKFlat_translate (unitDGAlgebra X.O) (-1) Q hQ.2⟩
  let eQ : q.obj Q'.complex ≅ (q.obj Q.complex)⟦(-1 : ℤ)⟧ :=
    eqToIso (congrArg q.obj (translate_complex (-1) Q)) ≪≫ (q.commShiftIso (-1 : ℤ)).app Q.complex
  let ε := shiftFunctorCompIsoId (_root_.HomotopyCategory (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)) (1 : ℤ) (-1) (by omega)
  have hinj := (bijective_comp_quotient_map_of_isUnitFlat A hI hI' t ht hQ').1
  have key : ∀ c : q.obj Q.complex ⟶ (q.obj I.complex)⟦(1 : ℤ)⟧,
      (eQ.hom ≫ c⟦(-1 : ℤ)⟧' ≫ ε.hom.app _) ≫ q.map t =
        eQ.hom ≫ (c ≫ (q.map t)⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ ε.hom.app _ := by
    intro c
    have hn := ε.hom.naturality (q.map t)
    simp only [Functor.comp_map, Functor.id_map] at hn
    rw [Functor.map_comp]
    simp only [Category.assoc, hn]
  have h := hinj (a₁ := eQ.hom ≫ a⟦(-1 : ℤ)⟧' ≫ ε.hom.app _)
    (a₂ := eQ.hom ≫ b⟦(-1 : ℤ)⟧' ≫ ε.hom.app _) (by
      simp only
      rw [key, key, hab])
  rw [cancel_epi, cancel_mono] at h
  exact (shiftFunctor _ (-1 : ℤ)).map_injective h

/-- **Every morphism from the underlying complex of a flat `(O, 0)`-module into the mapping cone of
a quasi-isomorphism from the underlying complex of a graded injective K-injective module into a
K-injective complex is null-homotopic**: postcomposition with the quasi-isomorphism and with its
shift are bijective on such morphisms, and the mapping cone triangle is distinguished. -/
theorem eq_zero_of_isUnitFlat_mappingCone
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {J : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} [J.IsKInjective]
    (t : I.complex ⟶ J) (ht : QuasiIso t)
    {Q : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O)} (hQ : IsUnitFlat Q)
    (g : (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Q.complex ⟶
      (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone t)) :
    g = 0 := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  have hT := _root_.HomotopyCategory.mappingCone_triangleh_distinguished t
  have h31 : (CochainComplex.mappingCone.triangleh t).mor₃ ≫ (q.map t)⟦(1 : ℤ)⟧' = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₃₁ _ hT
  have h12 : q.map t ≫ (CochainComplex.mappingCone.triangleh t).mor₂ = 0 :=
    Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
  have h3 : g ≫ (CochainComplex.mappingCone.triangleh t).mor₃ = 0 :=
    injective_comp_shift_quotient_map_of_isUnitFlat A hI hI' t ht hQ _ 0
      ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) h31).trans
        (comp_zero.trans zero_comp.symm)))
  obtain ⟨h, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hT g h3
  obtain ⟨h', rfl⟩ := (bijective_comp_quotient_map_of_isUnitFlat A hI hI' t ht hQ).2 h
  exact (Category.assoc _ _ _).trans ((congrArg (h' ≫ ·) h12).trans comp_zero)

end Derived

end Site

section Topos

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **A complex of `O`-modules into which every morphism from the underlying complex of a good
`(O, 0)`-module is null-homotopic is acyclic**: a good module resolving it (Tag 0FSH) maps to it
by a quasi-isomorphism which is null-homotopic, so its homology vanishes. -/
theorem acyclic_of_forall_isGoodToposBaseChange
    (C : CochainComplex (SheafOfModules.{u} (toRingCat Y.J Y.O)) ℤ)
    (h : ∀ P : DifferentialGradedModule.{u, u, u} (unitDGAlgebra Y.O),
      IsGoodToposBaseChange.{u, u, u} P → ∀ g : P.complex ⟶ C,
        (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g = 0) :
    C.Acyclic := by
  obtain ⟨P, s, hs, hP⟩ :=
    exists_good_quasiIso.{u, u, u} (A := unitDGAlgebra Y.O) (ofComplex C)
  have H := _root_.HomotopyCategory.homotopyOfEq _ _
    ((h P hP s.toHomologicalComplex).trans (Functor.map_zero _ _ _).symm)
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hi : IsIso (HomologicalComplex.homologyMap s.toHomologicalComplex n) := inferInstance
  have e : HomologicalComplex.homologyMap s.toHomologicalComplex n = 0 :=
    (H.homologyMap_eq n).trans (HomologicalComplex.homologyMap_zero _ _ _)
  rw [e] at hi
  exact IsZero.of_epi_zero (HomologicalComplex.homology P.complex n)
    (HomologicalComplex.homology (ofComplex C).complex n)

variable (f : RingedToposHom X Y)

/-- The unit `(O_Y, 0) ⟶ f_*(O_X, 0)` of the direct image of the structure sheaf. -/
noncomputable abbrev toposUnitAlgebraHom :
    unitDGAlgebra Y.O ⟶ toposPushforwardAlgebra (toposDirectImageModules f) (unitDGAlgebra X.O) :=
  unitAlgebraHom _

/-- The unit `(O_Y, 0) ⟶ f_*(O_X, 0)` is unital. -/
theorem isUnital_toposUnitAlgebraHom : (toposUnitAlgebraHom f).IsUnital :=
  unitAlgebraHom_preservesOne _

variable {f} in
/-- **The direct image carries a complex into which no flat `(O_X, 0)`-module maps nontrivially
up to homotopy to a complex into which no good `(O_Y, 0)`-module maps nontrivially up to
homotopy.** A good module has a pullback along `(f, (O_X, 0), (O_Y, 0) ⟶ f_*(O_X, 0))` which is
flat, and two morphisms out of a pullback are homotopic exactly when their transposes are. -/
theorem quotient_map_eq_zero_of_isGoodToposBaseChange
    {K : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ}
    (hK : ∀ T : DifferentialGradedModule.{u, u, u} (unitDGAlgebra X.O),
      IsUnitFlat (X := X.toRingedSite) T →
      ∀ g : T.complex ⟶ K, (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g = 0)
    {P : DifferentialGradedModule.{u, u, u} (unitDGAlgebra Y.O)}
    (hP : IsGoodToposBaseChange.{u, u, u} P)
    (a : P.complex ⟶ ((toposDirectImageModules f).mapHomologicalComplex _).obj K) :
    (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a = 0 := by
  obtain ⟨⟨T, ⟨e⟩⟩, hT⟩ := hP.baseChange f (unitDGAlgebra X.O) (toposUnitAlgebraHom f)
    (isUnital_toposUnitAlgebraHom f)
  let G := toposDirectImageModules f
  let F := toposPushforward G (toposUnitAlgebraHom f) (isUnital_toposUnitAlgebraHom f)
  let a' : P ⟶ F.obj (ofComplex K) := homMk a
  have h0 : e.homEquiv.symm (0 : P ⟶ F.obj (ofComplex K)) = 0 := by
    have := toposHomEquiv_symm_sub G _ (isUnital_toposUnitAlgebraHom f) e
      (0 : P ⟶ F.obj (ofComplex K)) 0
    rwa [sub_self, sub_self] at this
  have hb : Homotopic (e.homEquiv.symm a') (e.homEquiv.symm (0 : P ⟶ F.obj (ofComplex K))) := by
    rw [h0]
    refine (HomotopyCategory.quotient_map_eq_iff _ _).1 ?_
    refine (structure_quotient_map_eq_iff (X := X.toRingedSite) _ _).1 ?_
    exact (hK T (hT T e) _).trans (Functor.map_zero _ _ _).symm
  obtain ⟨H⟩ := (homotopic_homEquiv_symm_iff G _ (isUnital_toposUnitAlgebraHom f) e a'
    (0 : P ⟶ F.obj (ofComplex K))).1 hb
  exact (_root_.HomotopyCategory.eq_of_homotopy _ _ H.toComplexHomotopy).trans
    (Functor.map_zero _ _ _)

/-- **The direct image of sheaves of modules carries a quasi-isomorphism from the underlying
complex of a graded injective K-injective right differential graded `A`-module into a
K-injective complex to a quasi-isomorphism.** The mapping cone `E` of the quasi-isomorphism
receives no nonzero morphism up to homotopy from a flat `(O_X, 0)`-module, so its direct image
receives none from a good `(O_Y, 0)`-module and is therefore acyclic; it is the mapping cone of
the direct image of the quasi-isomorphism. -/
theorem quasiIso_mapHomologicalComplex_map_of_isDGInjective
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I)
    {J : CochainComplex (SheafOfModules.{u} (toRingCat X.J X.O)) ℤ} [J.IsKInjective]
    (t : I.complex ⟶ J) (ht : QuasiIso t) :
    QuasiIso (((toposDirectImageModules f).mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  have hE : ((toposDirectImageModules f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone t) |>.Acyclic :=
    acyclic_of_forall_isGoodToposBaseChange _ fun _ hP a =>
      quotient_map_eq_zero_of_isGoodToposBaseChange
        (fun _ hT g => eq_zero_of_isUnitFlat_mappingCone (X := X.toRingedSite) A hI hI' t ht hT
          ((_root_.HomotopyCategory.quotient _ _).map g)) hP a
  rw [← CochainComplex.mappingCone.acyclic_iff_quasiIso]
  exact fun n => (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso t _)

/-! ### The derived pushforward of sheaves of modules -/

section ModuleDerived

attribute [local instance] HasDerivedCategory.standard

/-- The direct image of sheaves of modules on homotopy categories followed by the localization
`K(O_Y) ⥤ D(O_Y)`: the functor whose right derived functor is `Rf_* : D(O_X) ⥤ D(O_Y)`. -/
noncomputable abbrev modulePushforwardToDerived :
    _root_.HomotopyCategory (SheafOfModules.{u} (toRingCat X.J X.O)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (toRingCat Y.J Y.O)) :=
  (toposDirectImageModules f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The direct image followed by the localization has a pointwise right derived functor
(Tag 070K), every complex of sheaves of modules having a K-injective resolution. -/
theorem modulePushforwardToDerived_hasPointwiseRightDerivedFunctor :
    (modulePushforwardToDerived f).HasPointwiseRightDerivedFunctor
      (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u, u + 1,
    u + 1, u + 1, u + 1, u + 1} _
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)).1

/-- The direct image followed by the localization has a right derived functor. -/
instance modulePushforwardToDerived_hasRightDerivedFunctor :
    (modulePushforwardToDerived f).HasRightDerivedFunctor
      (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  haveI := modulePushforwardToDerived_hasPointwiseRightDerivedFunctor f
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **The derived pushforward `Rf_* : D(O_X) ⥤ D(O_Y)` of sheaves of modules** along a morphism
of ringed topoi: the right derived functor of the direct image, which exists because every
complex of sheaves of modules has a K-injective resolution. -/
noncomputable def derivedModulePushforward :
    DerivedCategory (SheafOfModules.{u} (toRingCat X.J X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (toRingCat Y.J Y.O)) :=
  (modulePushforwardToDerived f).totalRightDerived DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The comparison map `K(f_*) ⋙ Q ⟶ Q ⋙ Rf_*` of the derived pushforward of sheaves of
modules. -/
noncomputable def derivedModulePushforwardUnit :
    modulePushforwardToDerived f ⟶ DerivedCategory.Qh ⋙ derivedModulePushforward f :=
  (modulePushforwardToDerived f).totalRightDerivedUnit DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- `Rf_*` with its comparison map is the right derived functor of the direct image. -/
instance isRightDerivedFunctor_derivedModulePushforward :
    (derivedModulePushforward f).IsRightDerivedFunctor (derivedModulePushforwardUnit f)
      (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  inferInstanceAs (((modulePushforwardToDerived f).totalRightDerived DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((modulePushforwardToDerived f).totalRightDerivedUnit DerivedCategory.Qh
        (_root_.HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))) _)

variable {f}

/-- **The derived pushforward of sheaves of modules is computed on the underlying complex of a
graded injective K-injective right differential graded module**: its comparison map is
invertible there. Resolve the complex by a K-injective one; the comparison map is invertible at
the resolution, and the direct image of the resolving quasi-isomorphism is a quasi-isomorphism by
`quasiIso_mapHomologicalComplex_map_of_isDGInjective`. -/
theorem isIso_derivedModulePushforwardUnit_app_of_isDGInjective
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
    {I : DifferentialGradedModule.{u, u, u} A} (hI : IsKInjective I) (hI' : GradedInjective I) :
    IsIso ((derivedModulePushforwardUnit f).app
      ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I.complex)) := by
  let q := _root_.HomotopyCategory.quotient (SheafOfModules.{u} (toRingCat X.J X.O))
    (ComplexShape.up ℤ)
  let t := (Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (toRingCat X.J X.O))).app I.complex
  have h₁ : IsIso ((derivedModulePushforwardUnit f).app (q.obj
      ((Stacks.Injectives.kInjectiveResolutionFunctor
        (SheafOfModules.{u} (toRingCat X.J X.O))).obj I.complex))) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)).2
      DerivedCategory.Qh (derivedModulePushforward f) (derivedModulePushforwardUnit f) _
      inferInstance
  have h₂ : IsIso ((modulePushforwardToDerived f).map (q.map t)) :=
    isIso_Qh_map_quotient_map _
      (quasiIso_mapHomologicalComplex_map_of_isDGInjective f hI hI' t inferInstance)
  have h₃ : IsIso ((DerivedCategory.Qh ⋙ derivedModulePushforward f).map (q.map t)) := by
    have := isIso_Qh_map_quotient_map t
      (Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso _ I.complex)
    exact inferInstanceAs (IsIso ((derivedModulePushforward f).map
      (DerivedCategory.Qh.map (q.map t))))
  have : IsIso ((derivedModulePushforwardUnit f).app (q.obj I.complex) ≫
      (DerivedCategory.Qh ⋙ derivedModulePushforward f).map (q.map t)) := by
    rw [← (derivedModulePushforwardUnit f).naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Qh ⋙ derivedModulePushforward f).map
    (q.map t))

end ModuleDerived

/-! ### The square of derived pushforwards and forgetful functors -/

section Square

attribute [local instance] HasDerivedCategory.standard

variable (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
  (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
  (φ : B ⟶ toposPushforwardAlgebra (toposDirectImageModules f) A) (hφ : φ.IsUnital)

/-- Every object of the homotopy category has a quasi-isomorphism into an object on whose
morphisms into it the localization is bijective: a graded injective K-injective module. -/
theorem exists_quasiIso_bijective_toDerivedCategory_map_topos
    (K : HomotopyCategory.{u, u, u} A) :
    ∃ (I : HomotopyCategory.{u, u, u} A) (s : K ⟶ I), quasiIsomorphisms.{u, u, u} A s ∧
      ∀ Z : HomotopyCategory.{u, u, u} A,
        Function.Bijective ((toDerivedCategory A).map : (Z ⟶ I) → _) := by
  obtain ⟨I, s, hs, hI⟩ := exists_quasiIso_isDGInjective_topos X A K
  exact ⟨I, s, hs, fun Z => bijective_toDerivedCategory_map_topos I hI Z⟩

/-- **The derived pushforward of differential graded modules followed by forgetting the action is
the right derived functor of the direct image followed by forgetting the action**: the derived
pushforward is computed on graded injective K-injective modules, so composing it with any
functor gives a right derived functor. -/
instance isRightDerivedFunctor_derivedToposPushforward_comp_derivedForget :
    (derivedToposPushforward f A B φ hφ ⋙ derivedForget B).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedToposPushforwardUnit f A B φ hφ) (derivedForget B) ≫
        (Functor.associator _ _ _).hom) (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_comp_of_coresolutions _ _ _
    (exists_quasiIso_bijective_toDerivedCategory_map_topos A)

/-- The comparison `f_* ⋙ Q ⟶ Q ⋙ Rf_*` on complexes of sheaves of modules: the comparison
map of the derived pushforward, read through `K(O) ⥤ D(O)`. -/
noncomputable def complexPushforwardComparison :
    (toposDirectImageModules f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedModulePushforward f :=
  Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso _).inv ≫
    Functor.whiskerRight ((toposDirectImageModules f).mapHomotopyCategoryFactors _).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (_root_.HomotopyCategory.quotient _ _) (derivedModulePushforwardUnit f) ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom (derivedModulePushforward f)

/-- The comparison `K(f_*) ⋙ forget ⟶ forget ⋙ Rf_*` on the homotopy category of right
differential graded `A`-modules: the comparison map of the derived pushforward of sheaves of
modules at the underlying complex, the underlying complex of the direct image of a module being
the direct image of its underlying complex. -/
noncomputable def homotopyForgetPushforwardComparison :
    homotopyToposPushforward (toposDirectImageModules f) φ hφ ⋙ homotopyForget B ⟶
      homotopyForget A ⋙ derivedModulePushforward f :=
  CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerLeft (toCochainComplex A) (complexPushforwardComparison f))

variable {A} in
/-- The comparison `K(f_*) ⋙ forget ⟶ forget ⋙ Rf_*` is invertible at a graded injective
K-injective right differential graded module. -/
theorem isIso_homotopyForgetPushforwardComparison_app {I : HomotopyCategory.{u, u, u} A}
    (hI : IsKInjective I.as ∧ GradedInjective I.as) :
    IsIso ((homotopyForgetPushforwardComparison f A B φ hφ).app I) := by
  have := isIso_derivedModulePushforwardUnit_app_of_isDGInjective (f := f) hI.1 hI.2
  show IsIso ((complexPushforwardComparison f).app I.as.complex)
  simp only [complexPushforwardComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- The comparison map exhibiting `forget ⋙ Rf_*` as a right derived functor of the direct image
followed by forgetting the action: `homotopyForgetPushforwardComparison`, read through the
factorizations of `forget` through the two localizations. -/
noncomputable def forgetPushforwardUnit :
    toposPushforwardToDerived f A B φ hφ ⋙ derivedForget B ⟶
      toDerivedCategory A ⋙ (derivedForget A ⋙ derivedModulePushforward f) :=
  eqToHom (by rw [Functor.assoc, toDerivedCategory_comp_derivedForget]) ≫
    homotopyForgetPushforwardComparison f A B φ hφ ≫
    eqToHom (by rw [← Functor.assoc, toDerivedCategory_comp_derivedForget])

/-- **Forgetting the action followed by the derived pushforward of sheaves of modules is the right
derived functor of the direct image followed by forgetting the action**: at a graded injective
K-injective module its comparison map is the comparison map of `Rf_*` at the underlying complex,
which is invertible by `isIso_derivedModulePushforwardUnit_app_of_isDGInjective`. -/
instance isRightDerivedFunctor_derivedForget_comp_derivedModulePushforward :
    (derivedForget A ⋙ derivedModulePushforward f).IsRightDerivedFunctor
      (forgetPushforwardUnit f A B φ hφ) (quasiIsomorphisms.{u, u, u} A) :=
  Functor.isRightDerivedFunctor_of_coresolutions _ _
    (fun I : HomotopyCategory.{u, u, u} A => IsKInjective I.as ∧ GradedInjective I.as)
    (exists_quasiIso_isDGInjective_topos X A)
    (fun I hI K => bijective_toDerivedCategory_map_topos I hI K)
    (fun I hI => by
      have := isIso_homotopyForgetPushforwardComparison_app f B φ hφ hI
      simp only [forgetPushforwardUnit, NatTrans.comp_app, eqToHom_app]
      infer_instance)

/-- **The square of derived pushforwards and forgetful functors commutes**, over ringed topoi
carrying the instance that the forgetful functor from commutative rings to rings is compatible
with sheaves. Tag 0FTW, with that instance discharged, is
`SheafOfModules.DifferentialGradedModule.derivedToposPushforwardForgetIsoTopos`. -/
noncomputable def derivedToposPushforwardForgetIso :
    derivedToposPushforward f A B φ hφ ⋙ derivedForget B ≅
      derivedForget A ⋙ derivedModulePushforward (X := X) (Y := Y) f :=
  Functor.rightDerivedIso (quasiIsomorphisms.{u, u, u} A)
    (Functor.whiskerRight (derivedToposPushforwardUnit f A B φ hφ) (derivedForget B) ≫
      (Functor.associator _ _ _).hom) (forgetPushforwardUnit f A B φ hφ)

/-- The isomorphism of Tag 0FTW is compatible with the comparison maps of the two composites. -/
theorem derivedToposPushforwardForgetIso_fac :
    (Functor.whiskerRight (derivedToposPushforwardUnit f A B φ hφ) (derivedForget B) ≫
        (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft (toDerivedCategory A)
        (derivedToposPushforwardForgetIso f A B φ hφ).hom =
      forgetPushforwardUnit f A B φ hφ :=
  Functor.rightDerivedIso_fac _ _ _

end Square

end Topos

/-! ### Tag 0FTW -/

section Tag

open Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat
  AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat HasDerivedCategory.standard

/-- **Stacks Project, Tag 0FTW.** Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi, let `A` be a sheaf of differential graded `O_C`-algebras, `B` one of
`O_D`-algebras and `φ : B ⟶ f_*A` a homomorphism of sheaves of differential graded
`O_D`-algebras. Homomorphisms of differential graded algebras preserve `1` in the source, while a
homomorphism in this development need not, so this is the hypothesis `hφ : φ.IsUnital`. Then the
square

`D(A, d) ⥤ D(O_C) ⥤ D(O_D)` and `D(A, d) ⥤ D(B, d) ⥤ D(O_D)`

of the forgetful functors and the derived pushforwards commutes: `Rf_* ⋙ forget ≅ forget ⋙ Rf_*`.
Both composites are right derived functors of the direct image of differential graded modules
followed by forgetting the action, and the isomorphism is the one compatible with their
comparison maps. -/
@[stacks 0FTW]
noncomputable def derivedToposPushforwardForgetIsoTopos
    {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O))
    (φ : B ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := Y.O)
      (toposDirectImageModules (X := X) (Y := Y) f) A) (hφ : φ.IsUnital) :
    derivedToposPushforward f A B φ hφ ⋙ derivedForget B ≅
      derivedForget A ⋙ derivedModulePushforward (X := X) (Y := Y) f :=
  derivedToposPushforwardForgetIso f A B φ hφ

end Tag

end SheafOfModules.DifferentialGradedModule
