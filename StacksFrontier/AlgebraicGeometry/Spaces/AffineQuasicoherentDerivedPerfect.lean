module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Perfect objects on an affine representable algebraic space

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring of
global functions `R`, let `Φ : D(R) ⥤ D(𝒪_{yoneda.obj U})` be the derived associated-module
functor and `RΓ` its right adjoint. This file compares perfect objects on the two sides:

* a perfect object `M` of `D(R)` goes to a perfect object `Φ(M)`, which even has a global strictly
  perfect model;
* if `E` is isomorphic to a strictly perfect complex `P`, then `RΓ(E)` is perfect in `D(R)`: the
  terms of `P` are associated modules of finite projective `R`-modules, so `P` is the associated
  complex of its complex of sections, and `RΓ ∘ Φ ≅ id`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect`: a strictly perfect complex
  of `O`-modules represents a perfect object of `D(O)`.
* `AlgebraicGeometry.Space.isPerfect_representedAffineDerivedAssociated_obj`:
  `Φ` carries perfect objects to perfect objects.
* `AlgebraicGeometry.Space.isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect`:
  `RΓ` carries an object with a strictly perfect model to a perfect object of `D(R)`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w d

namespace AlgebraicGeometry.RingedSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- A strictly perfect complex is a perfect complex: over every object, its own restriction is a
strictly perfect model. -/
theorem isPerfectComplex_of_isStrictlyPerfect
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) :
    X.IsPerfectComplex P := fun _ =>
  ⟨⊤, by simp, fun V _ _ => ⟨X.restrictComplex P V, isStrictlyPerfect_over_general X V hP, 𝟙 _,
    inferInstance⟩⟩

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **A strictly perfect complex represents a perfect object of `D(O)`.** -/
theorem isPerfect_Q_obj_of_isStrictlyPerfect
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) :
    X.IsPerfect (DerivedCategory.Q.obj P) :=
  ⟨P, isPerfectComplex_of_isStrictlyPerfect X P hP, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

section Associated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-! ### Perfect objects of `D(R)` go to perfect objects -/

/-- `Φ` of a perfect object of `D(R)` is isomorphic to a strictly perfect complex. -/
theorem exists_isStrictlyPerfect_iso_representedAffineDerivedAssociated_obj
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    ∃ P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) ℤ,
      IsStrictlyPerfect.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U)).O)) P ∧
      Nonempty ((representedAffineDerivedAssociated B S hS U).obj M ≅
        DerivedCategory.Q.obj P) := by
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hM
  exact ⟨_, isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex B S hS U P a b
    hGE hLE hfin hproj, ⟨(representedAffineDerivedAssociated B S hS U).mapIso e ≪≫
      (representedAffineAssociated B S hS U).mapDerivedCategoryFactors.app P⟩⟩

/-- **`Φ` carries perfect objects of `D(R)` to perfect objects of `D(𝒪_{yoneda.obj U})`.** -/
theorem isPerfect_representedAffineDerivedAssociated_obj
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((representedAffineDerivedAssociated B S hS U).obj M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ :=
    exists_isStrictlyPerfect_iso_representedAffineDerivedAssociated_obj B S hS U M hM
  exact RingedSite.IsPerfect.of_iso _
    (RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect _ P hP) e.symm

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- A strictly perfect complex is bounded: its terms vanish outside an interval. -/
theorem exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P) :
    ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  refine ⟨a, b, (CochainComplex.isStrictlyGE_iff P a).2 fun i hi => ?_,
    (CochainComplex.isStrictlyLE_iff P b).2 fun i hi => ?_⟩
  · by_contra h
    exact absurd (ha h) (by omega)
  · by_contra h
    exact absurd (hb h) (by omega)

/-! ### Strictly perfect objects go to perfect objects of `D(R)` -/

section Sections

variable {B S hS U}

/-- The finite free module `𝒪^n` is the associated module of `R^{⊕n}`. -/
def representedAffineAssociatedSigmaUnitIso (n : ℕ) :
    (representedAffineAssociated B S hS U).obj (∐ (fun _ : ULift.{u} (Fin n) =>
        ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅
      SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)) (ULift.{u} (Fin n)) :=
  have : PreservesColimitsOfSize.{u, u} (representedAffineAssociated B S hS U) :=
    (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  haveI : HasFiniteBiproducts (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := Abelian.hasFiniteBiproducts
  haveI : HasFiniteCoproducts (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := hasFiniteCoproducts_of_hasFiniteBiproducts _
  haveI : HasColimitsOfShape (Discrete (ULift.{u} (Fin n))) (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) := hasColimitsOfShape_discrete _ _
  PreservesCoproduct.iso (representedAffineAssociated B S hS U) _ ≪≫
    Sigma.mapIso (fun _ => representedAffineAssociatedObjUnitIso B S hS U)

/-- The counit `Φ₀(Γ(M)) ⟶ M` is invertible at a direct summand of a finite free module, and the
sections of such a module are a finite projective `R`-module. -/
theorem isIso_counit_app_and_finite_projective_of_isDirectSummandOfFiniteFree
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hM : IsDirectSummandOfFiniteFree.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) M) :
    IsIso ((representedAffineAssociatedAdjunction B S hS U).counit.app M) ∧
      Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        ((representedAffineSections B S hS U).obj M) ∧
      Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        ((representedAffineSections B S hS U).obj M) := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hM
  have hff := representedAffineAssociatedFullyFaithful B S hS U
  have := hff.full
  have := hff.faithful
  let eF := representedAffineAssociatedSigmaUnitIso (B := B) (S := S) (hS := hS) (U := U) n
  have hF : IsIso ((representedAffineAssociatedAdjunction B S hS U).counit.app
      (SheafOfModules.free (ULift.{u} (Fin n)))) :=
    (representedAffineAssociatedAdjunction B S hS U).isIso_counit_app_of_iso eF.symm
  refine ⟨⟨i ≫ inv ((representedAffineAssociatedAdjunction B S hS U).counit.app
      (SheafOfModules.free (ULift.{u} (Fin n)))) ≫
    (representedAffineAssociated B S hS U).map ((representedAffineSections B S hS U).map r),
    ?_, ?_⟩, ?_⟩
  · have h := (representedAffineAssociatedAdjunction B S hS U).counit_naturality i
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
      ← Functor.map_comp, hir, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  · have h := (representedAffineAssociatedAdjunction B S hS U).counit_naturality r
    rw [Category.assoc, Category.assoc, h, IsIso.inv_hom_id_assoc, hir]
    rfl
  -- the sections are a retract of `R^{⊕n}`
  let A := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let N := ModuleCat.of A (DirectSum (ULift.{u} (Fin n)) fun _ => A)
  let eN :
      (representedAffineSections B S hS U).obj (SheafOfModules.free (ULift.{u} (Fin n))) ≅ N :=
    (representedAffineSections B S hS U).mapIso eF.symm ≪≫
      (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app _)).symm ≪≫
      ModuleCat.coprodIsoDirectSum _
  let i' := ((representedAffineSections B S hS U).map i ≫ eN.hom).hom
  let r' := (eN.inv ≫ (representedAffineSections B S hS U).map r).hom
  have hir' : r'.comp i' = LinearMap.id := by
    have : ((representedAffineSections B S hS U).map i ≫ eN.hom) ≫
        (eN.inv ≫ (representedAffineSections B S hS U).map r) = 𝟙 _ := by
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir,
        CategoryTheory.Functor.map_id]
    exact congrArg ModuleCat.Hom.hom this
  exact ⟨Module.Finite.of_surjective r' fun x => ⟨i' x, LinearMap.congr_fun hir' x⟩,
    Module.Projective.of_split i' r' hir'⟩

/-- **An object with a strictly perfect model is `Φ` of a bounded complex of finite projective
`R`-modules.** The terms of the strictly perfect complex are associated modules of their sections,
which are finite projective, so the complex is the associated complex of its complex of
sections. -/
theorem exists_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P)
    (e : E ≅ DerivedCategory.Q.obj P) :
    ∃ (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) (a b : ℤ),
      N.IsStrictlyGE a ∧ N.IsStrictlyLE b ∧
      (∀ j, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X j)) ∧
      (∀ j, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X j)) ∧
      Nonempty (E ≅
        (representedAffineDerivedAssociated B S hS U).obj (DerivedCategory.Q.obj N)) := by
  let adj₀ := representedAffineAssociatedAdjunction B S hS U
  let Φ₀ := representedAffineAssociated B S hS U
  let Γ₀ := representedAffineSections B S hS U
  have h := fun j => isIso_counit_app_and_finite_projective_of_isDirectSummandOfFiniteFree
    (P.X j) (hP.termDirectSummand j)
  let N := (Γ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let c : (Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ P :=
    HomologicalComplex.Hom.isoOfComponents
      (fun j => @asIso _ _ _ _ (adj₀.counit.app (P.X j)) (h j).1)
      (fun i j _ => (adj₀.counit.naturality (P.d i j)).symm)
  obtain ⟨a, b, hGE, hLE⟩ := exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect B S hS U P hP
  exact ⟨N, a, b, (CochainComplex.isStrictlyGE_iff N a).2 fun j hj =>
      Γ₀.map_isZero (P.isZero_of_isStrictlyGE a j hj),
    (CochainComplex.isStrictlyLE_iff N b).2 fun j hj =>
      Γ₀.map_isZero (P.isZero_of_isStrictlyLE b j hj),
    fun j => (h j).2.1, fun j => (h j).2.2,
    ⟨e ≪≫ DerivedCategory.Q.mapIso c.symm ≪≫ (Φ₀.mapDerivedCategoryFactors.app N).symm⟩⟩

/-- **`RΓ` of an object with a strictly perfect model is perfect.** If `E` is isomorphic in
`D(𝒪_{yoneda.obj U})` to a strictly perfect complex, then `RΓ(E)` is a perfect object of
`D(R)`. -/
theorem isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P)
    (e : E ≅ DerivedCategory.Q.obj P) :
    StacksDraft.Perfect.IsPerfect ((representedAffineDerivedSections B S hS U).obj E) := by
  obtain ⟨N, a, b, hGE, hLE, hfin, hproj, ⟨e'⟩⟩ :=
    exists_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect E P hP e
  exact ⟨N, a, b, hGE, hLE, hfin, hproj, ⟨(representedAffineDerivedSections B S hS U).mapIso e' ≪≫
    (asIso ((representedAffineDerivedAdjunction B S hS U).unit.app
      (DerivedCategory.Q.obj N))).symm⟩⟩

/-- An object with a strictly perfect model lies in `D_QCoh`. -/
theorem qcohDerived_of_isStrictlyPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ℤ)
    (hP : IsStrictlyPerfect.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)).O)) P)
    (e : E ≅ DerivedCategory.Q.obj P) :
    QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E := by
  obtain ⟨N, -, -, -, -, -, -, ⟨e'⟩⟩ :=
    exists_iso_representedAffineDerivedAssociated_of_isStrictlyPerfect E P hP e
  exact ObjectProperty.prop_of_iso _ e'.symm
    (qcohDerived_representedAffineDerivedAssociated_obj B S hS U _)

end Sections

end Associated

end AlgebraicGeometry.Space

end
