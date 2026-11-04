module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.HypercohomologyExtUnit

/-!
# Hypercohomology is corepresented by the structure sheaf, canonically

Let `k` be a field and `f : X ⟶ Spec k` a scheme over `k`. For every object `M` of `D(𝒪_X)`
this file constructs the `k`-linear isomorphism

  `Hom_{D(𝒪_X)}(𝒪_X[0], M) ≃ₗ[k] H^0(X, M)`,

`Stacks.Duality.UnitCorepresentation.unitHomLinearEquiv`, sending `α` to the image under
`H^0(X, α)` of the class of the section `1` of `𝒪_X`. Being defined by this formula it is
natural in `M` (`unitHomLinearEquiv_naturality`) and involves no choice; bijectivity is checked
on a K-injective representative `I` of `M`, where `H^0(X, I) = H^0(Γ(X, I))` and maps
`𝒪_X[0] ⟶ I` up to homotopy are the degree-zero cocycles of `Γ(X, I)` up to coboundaries.

`Stacks.Duality.nonempty_derivedCohomologyOverFieldLinearEquivExtUnit` gives such an
isomorphism only up to existence, depending on a choice of representative; the one here is
canonical.

## References

* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality.UnitCorepresentation

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

variable (X) in
/-- `𝒪_X[0]`, as a complex. -/
abbrev unitComplex : CochainComplex X.Modules ℤ :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj (Stacks.Ample.unitModule X)

/-- `Γ(X, -)` applied termwise. -/
abbrev sectionsComplex (I : CochainComplex X.Modules ℤ) : CochainComplex (ModuleCat.{u} k) ℤ :=
  ((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- The section `1` of `𝒪_X`, as a `k`-linear map `k ⟶ Γ(X, 𝒪_X)`. -/
def unitPoint : ModuleCat.of k k ⟶ (globalSectionsOver f).obj (Stacks.Ample.unitModule X) :=
  ModuleCat.homEquiv.symm ((unitHomLinearEquivGlobalSections f _).toLinearMap ∘ₗ
    LinearMap.toSpanSingleton k _ (𝟙 (Stacks.Ample.unitModule X)))

/-- The value of `unitPoint ≫ Γ(a)` at `1` is the section `a(1)`. -/
theorem unitPoint_comp_map {M : X.Modules} (a : Stacks.Ample.unitModule X ⟶ M) :
    (unitPoint f ≫ (globalSectionsOver f).map a).hom 1 =
      unitHomLinearEquivGlobalSections f M a := by
  show (globalSectionsOver f).map a (unitHomLinearEquivGlobalSections f _ ((1 : k) • 𝟙 _)) = _
  rw [one_smul, ← unitHomLinearEquivGlobalSections_naturality, Category.id_comp]

/-- The class in `H^0(Γ(X, I))` of the global section `a(1)` of `I^0`, for a map
`a : 𝒪_X ⟶ I^0` killed by the differential. -/
def sectionClass (I : CochainComplex X.Modules ℤ) (a : Stacks.Ample.unitModule X ⟶ I.X 0)
    (ha : a ≫ I.d 0 1 = 0) :
    ModuleCat.of k k ⟶ (sectionsComplex f I).homology 0 :=
  (sectionsComplex f I).liftCycles (unitPoint f ≫ (globalSectionsOver f).map a) 1
    (by simp) (by
      change unitPoint f ≫ (globalSectionsOver f).map a ≫ (globalSectionsOver f).map (I.d 0 1) = 0
      rw [← Functor.map_comp, ha, Functor.map_zero, Limits.comp_zero]) ≫
    (sectionsComplex f I).homologyπ 0

/-- `H^0(Q(C)) ≅ H^0(C)` for a complex of `k`-modules, read through the homotopy category. -/
def homologyBridgeNatIso :
    HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0 ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ) 0 :=
  Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} k) 0) ≪≫
    HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} k) (ComplexShape.up ℤ) 0

/-- `H^0(Q(C)) ≅ H^0(C)`, at one complex. -/
def homologyBridge (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj C)) ≅ C.homology 0 :=
  homologyBridgeNatIso.app C

/-- The comparison `H^0(Γ(X, I)) ⟶ H^0(X, I)`, the degree-zero cohomology of the unit of the
right derived functor. -/
def unitH0 (I : CochainComplex X.Modules ℤ) :
    (sectionsComplex f I).homology 0 ⟶ derivedCohomologyOverField f
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) 0 :=
  (homologyBridge (sectionsComplex f I)).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
      ((derivedGlobalSectionsOverUnit f).app ((HomotopyCategory.quotient _ _).obj I))

omit [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)] in
/-- `unitH0` is natural for morphisms of complexes. -/
theorem unitH0_naturality {I J : CochainComplex X.Modules ℤ} (b : I ⟶ J) :
    HomologicalComplex.homologyMap
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map b) 0 ≫
      unitH0 f J =
      unitH0 f I ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map b))) := by
  have h1 : HomologicalComplex.homologyMap
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map b) 0 ≫
        (homologyBridge (sectionsComplex f J)).inv =
      (homologyBridge (sectionsComplex f I)).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ _).map
            (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map b))) :=
    homologyBridgeNatIso.inv.naturality
      (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map b)
  have h2 := (derivedGlobalSectionsOverUnit f).naturality ((HomotopyCategory.quotient _ _).map b)
  simp only [unitH0]
  rw [← Category.assoc, h1, Category.assoc]
  exact congrArg (fun z => _ ≫ z)
    ((((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map_comp _ _).symm.trans
      (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map h2)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map_comp _ _))

/-- `sectionClass` is natural for morphisms of complexes. -/
theorem sectionClass_comp_homologyMap {I J : CochainComplex X.Modules ℤ}
    (a : Stacks.Ample.unitModule X ⟶ I.X 0) (ha : a ≫ I.d 0 1 = 0) (b : I ⟶ J) :
    sectionClass f I a ha ≫ HomologicalComplex.homologyMap
        (((globalSectionsOver f).mapHomologicalComplex (ComplexShape.up ℤ)).map b) 0 =
      sectionClass f J (a ≫ b.f 0)
        (by rw [Category.assoc, b.comm, reassoc_of% ha, Limits.zero_comp]) := by
  simp only [sectionClass, Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 2

variable (X) in
/-- `𝒪_X[0]` in the homotopy category. -/
abbrev unitHomotopy : HomotopyCategory X.Modules (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ _).obj (unitComplex X)

/-- The class of the section `1` in `H^0(X, 𝒪_X[0])`. -/
def unitClass : ModuleCat.of k k ⟶
    derivedCohomologyOverField f (DerivedCategory.Qh.obj (unitHomotopy X)) 0 :=
  sectionClass f (unitComplex X)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Stacks.Ample.unitModule X)).inv
    (by simp) ≫ unitH0 f (unitComplex X)

/-- **The comparison `Hom_{D(𝒪_X)}(𝒪_X[0], M) ⟶ H^0(X, M)`**: a morphism `α` goes to the image
of the class of `1` under `H^0(X, α)`. -/
def evalUnit (M : DerivedCategory X.Modules) (α : DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) :
    ModuleCat.of k k ⟶ derivedCohomologyOverField f M 0 :=
  unitClass f ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
    ((derivedGlobalSectionsOver f).map α)

/-- `evalUnit` is natural in `M`. -/
theorem evalUnit_naturality {M N : DerivedCategory X.Modules}
    (α : DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) (g : M ⟶ N) :
    evalUnit f N (α ≫ g) = evalUnit f M α ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map g) := by
  simp only [evalUnit, Functor.map_comp, Category.assoc]

/-- `evalUnit` on the class of a morphism of complexes `𝒪_X[0] ⟶ I`. -/
theorem evalUnit_Qh_quotient_map {I : CochainComplex X.Modules ℤ} (b : unitComplex X ⟶ I) :
    evalUnit f _ (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map b)) =
      sectionClass f I
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (Stacks.Ample.unitModule X)).inv ≫ b.f 0)
        (by rw [Category.assoc, b.comm]; simp) ≫ unitH0 f I := by
  simp only [evalUnit, unitClass, Category.assoc]
  rw [← unitH0_naturality, ← Category.assoc, sectionClass_comp_homologyMap]

/-- `sectionClass` depends only on the morphism `a`. -/
theorem sectionClass_congr (I : CochainComplex X.Modules ℤ)
    {a a' : Stacks.Ample.unitModule X ⟶ I.X 0} (h : a = a') (ha : a ≫ I.d 0 1 = 0)
    (ha' : a' ≫ I.d 0 1 = 0) : sectionClass f I a ha = sectionClass f I a' ha' := by
  subst h
  rfl

/-- `sectionClass` evaluated at `1` is the homology class of the section `a(1)`, read through the
cycles. -/
theorem sectionClass_eq_of_cycles (I : CochainComplex X.Modules ℤ)
    (a : Stacks.Ample.unitModule X ⟶ I.X 0) (ha : a ≫ I.d 0 1 = 0) {A : ModuleCat.{u} k}
    (z : A ⟶ (sectionsComplex f I).X 0) (hz : z ≫ (sectionsComplex f I).d 0 1 = 0) (x : A)
    (hx : z.hom x = unitHomLinearEquivGlobalSections f _ a) :
    (sectionClass f I a ha).hom 1 =
      ((sectionsComplex f I).liftCycles z 1 (by simp) hz ≫
        (sectionsComplex f I).homologyπ 0).hom x := by
  simp only [sectionClass, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective ((sectionsComplex f I).iCycles 0)).1 inferInstance
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, HomologicalComplex.liftCycles_i,
    HomologicalComplex.liftCycles_i, unitPoint_comp_map, hx]

/-- `Hom(𝒪_X, -) = Γ(X, -)` is natural. -/
theorem unitHom_comp_d {M N : X.Modules} (a : Stacks.Ample.unitModule X ⟶ M) (d : M ⟶ N) :
    unitHomLinearEquivGlobalSections f N (a ≫ d) =
      (globalSectionsOver f).map d (unitHomLinearEquivGlobalSections f M a) :=
  unitHomLinearEquivGlobalSections_naturality f a d

section KInjective

variable (I : CochainComplex X.Modules ℤ) [I.IsKInjective]

/-- On a K-injective complex `H^0(Γ(X, I)) ⟶ H^0(X, I)` is an isomorphism. -/
instance isIso_unitH0 : IsIso (unitH0 f I) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (homotopyGlobalSectionsOver f) (Scheme.Modules.exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) I
    inferInstance
  have h : IsIso ((derivedGlobalSectionsOverUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) := this
  have h' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
      ((derivedGlobalSectionsOverUnit f).app
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) :=
    @Functor.map_isIso _ _ _ _ _ _ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0) _ h
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h'

/-- `evalUnit` is surjective at a K-injective complex. -/
theorem evalUnit_surjective :
    Function.Surjective (evalUnit f (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ _).obj I))) := by
  intro y
  obtain ⟨A', π, hπ, z, hz, hγ⟩ := (sectionsComplex f I).eq_liftCycles_homologyπ_up_to_refinements
    (y ≫ inv (unitH0 f I)) 1 (by simp)
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
  obtain ⟨a, hea⟩ := (unitHomLinearEquivGlobalSections f _).surjective (z.hom a')
  have ha : a ≫ I.d 0 1 = 0 := by
    apply (unitHomLinearEquivGlobalSections f _).injective
    rw [unitHom_comp_d, hea, map_zero]
    exact congrArg (fun t => t.hom a') hz
  let b : unitComplex X ⟶ I := HomologicalComplex.mkHomFromSingle a (fun j hj => by
    obtain rfl : j = 1 := by simpa using hj.symm
    exact ha)
  refine ⟨DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map b), ?_⟩
  rw [evalUnit_Qh_quotient_map]
  have hb : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (Stacks.Ample.unitModule X)).inv ≫ b.f 0 = a := by
    simp [b, HomologicalComplex.mkHomFromSingle_f]
  rw [sectionClass_congr f I hb _ ha]
  have key : sectionClass f I a ha = y ≫ inv (unitH0 f I) := by
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    rw [sectionClass_eq_of_cycles f I a ha z hz a' hea.symm, ← hγ, ModuleCat.comp_apply, ha']
  rw [key, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- `evalUnit` has trivial kernel at a K-injective complex. -/
theorem evalUnit_eq_zero {α : DerivedCategory.Qh.obj (unitHomotopy X) ⟶
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)} (hα : evalUnit f _ α = 0) :
    α = 0 := by
  obtain ⟨β, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ I).2 α
  obtain ⟨b, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  rw [evalUnit_Qh_quotient_map] at hα
  set a := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (Stacks.Ample.unitModule X)).inv ≫ b.f 0 with ha_def
  have ha : a ≫ I.d 0 1 = 0 := by
    rw [ha_def, Category.assoc, b.comm]
    simp
  have h0 : sectionClass f I a ha = 0 := by
    simpa using congrArg (fun t => t ≫ inv (unitH0 f I)) hα
  simp only [sectionClass] at h0
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    ((sectionsComplex f I).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
      (-1) 0 1 (by simp) (by simp) _ _).1 h0
  obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
  obtain ⟨w, hw₁⟩ := (unitHomLinearEquivGlobalSections f _).surjective (x₁.hom a'')
  have hw : w ≫ I.d (-1) 0 = a := by
    apply (unitHomLinearEquivGlobalSections f _).injective
    rw [unitHom_comp_d, hw₁, ← unitPoint_comp_map]
    have := congrArg (fun t => t.hom a'') hx₁
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ha''] at this
    exact this.symm
  have hb : Homotopy b 0 := (CochainComplex.HomComplex.Cochain.equivHomotopy b 0).symm
    ⟨CochainComplex.HomComplex.Cochain.fromSingleMk w (show (0 : ℤ) + -1 = -1 by norm_num), by
      rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk _ _ 0 0 (by norm_num),
        CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero]
      refine CochainComplex.HomComplex.Cochain.ext _ _ (fun p q hpq => ?_)
      obtain rfl : p = q := by omega
      by_cases hp : p = 0
      · subst hp
        rw [CochainComplex.HomComplex.Cochain.ofHom_v,
          CochainComplex.HomComplex.Cochain.fromSingleMk_v, hw, ha_def, Iso.hom_inv_id_assoc]
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _⟩
  rw [HomotopyCategory.eq_of_homotopy b 0 hb, Functor.map_zero, Functor.map_zero]

end KInjective

/-- `evalUnit` as a `k`-linear map. -/
def evalUnitLinear (M : DerivedCategory X.Modules) :
    (DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) →ₗ[k]
      (ModuleCat.of k k ⟶ derivedCohomologyOverField f M 0) where
  toFun := evalUnit f M
  map_add' α β := by
    simp only [evalUnit, Functor.map_add, Preadditive.comp_add]
  map_smul' a α := by
    simp only [evalUnit, Functor.map_smul, Linear.comp_smul, RingHom.id_apply]

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_comp_hom {C : Type*} [Category C] {A B D : C} (e : B ≅ D) :
    Function.Bijective (fun β : A ⟶ B => β ≫ e.hom) :=
  ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun δ => ⟨δ ≫ e.inv, by simp⟩⟩

/-- **`evalUnit` is bijective.** -/
theorem evalUnit_bijective (M : DerivedCategory X.Modules) :
    Function.Bijective (evalUnit f M) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_atModel
    (Scheme.Modules.exists_quasiIso_isKInjective X) M
  let e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ M :=
    (DerivedCategory.quotientCompQhIso X.Modules).app I ≪≫ e
  have h : evalUnit f M = (fun β => β ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
      ((derivedGlobalSectionsOver f).map e'.hom)) ∘ evalUnit f _ ∘ (fun α => α ≫ e'.inv) := by
    funext α
    simp only [Function.comp_apply, ← evalUnit_naturality, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [h]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_)
  · exact bijective_comp_hom ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
      ((derivedGlobalSectionsOver f).mapIso e'))
  · refine ⟨fun α β hαβ => ?_, evalUnit_surjective f I⟩
    have : evalUnit f _ (α - β) = 0 := by
      rw [show evalUnit f _ (α - β) = evalUnitLinear f _ (α - β) from rfl, map_sub]
      exact sub_eq_zero.2 hαβ
    exact sub_eq_zero.1 (evalUnit_eq_zero f I this)
  · exact bijective_comp_hom e'.symm

/-- **`Hom_{D(𝒪_X)}(𝒪_X[0], M) ≃ₗ[k] H^0(X, M)`**, canonically: a morphism `α` goes to the
image under `H^0(X, α)` of the class of the section `1`. -/
def unitHomLinearEquiv (M : DerivedCategory X.Modules) :
    (DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) ≃ₗ[k] derivedCohomologyOverField f M 0 :=
  (LinearEquiv.ofBijective (evalUnitLinear f M) (evalUnit_bijective f M)).trans
    (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf k k _))

/-- The formula for `unitHomLinearEquiv`. -/
theorem unitHomLinearEquiv_apply (M : DerivedCategory X.Modules)
    (α : DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) :
    unitHomLinearEquiv f M α = (evalUnit f M α).hom 1 := rfl

/-- **`unitHomLinearEquiv` is natural in `M`.** -/
theorem unitHomLinearEquiv_naturality {M N : DerivedCategory X.Modules}
    (α : DerivedCategory.Qh.obj (unitHomotopy X) ⟶ M) (g : M ⟶ N) :
    unitHomLinearEquiv f N (α ≫ g) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        ((derivedGlobalSectionsOver f).map g)).hom (unitHomLinearEquiv f M α) := by
  rw [unitHomLinearEquiv_apply, unitHomLinearEquiv_apply, evalUnit_naturality]
  rfl

end Stacks.Duality.UnitCorepresentation
