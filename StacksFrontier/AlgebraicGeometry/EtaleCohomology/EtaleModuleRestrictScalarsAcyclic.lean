module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalarsInt
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeSplitUniverse
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of scalars carries injective sheaves to acyclic sheaves

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings with `Λ` a Dedekind domain (for instance
`ℤ`, or `ℤ_ℓ`), and let `I` be an injective sheaf of `Λ'`-modules on the small étale site of a
scheme `X`.  The sheaf `res_ρ I` of `Λ`-modules is in general not injective, but it is acyclic
for the sections over every object of the site.  This is the input of the comparison of the
cohomology of a sheaf of `ℤ/ℓⁿ⁺¹ℤ`-modules with the cohomology of the same sheaf viewed as a
sheaf of `ℤ_ℓ`-modules, which [Tag 03V2] uses implicitly.

The argument is the one behind [Tag 03FD]:

* `Ext^{n+1}(P, res_ρ I) = 0` for every sectionwise torsion-free sheaf `P`.  Sectionwise
  torsion-free sheaves are closed under subobjects and every sheaf is a quotient of one, so
  by dévissage it is enough to extend maps to `res_ρ I` along a monomorphism with torsion-free
  cokernel; the left adjoint of `res_ρ`, sheafified extension of scalars, keeps such a
  monomorphism a monomorphism because over a Dedekind domain torsion-free modules are flat.
* The sections over an object `U` are corepresented by the sheafified free module on the
  representable presheaf of `U`, which is sectionwise torsion-free.

## Main results

* `Stacks.EtaleCohomology.ext_restrictScalars_eq_zero_of_isTorsionFree`: the `Ext`-vanishing.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (X : Scheme.{u})

/-- `Ext`-groups of sheaves of modules on the small étale site exist in the universe of the
morphisms of that category. -/
instance etaleModules_hasExt (Λ : Type) [Ring Λ] : HasExt.{u + 1} (EtaleModules.{u, 0} Λ X) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-! ### Sectionwise torsion-free sheaves -/

section TorsionFree

variable {Λ : Type} [CommRing Λ] [IsDomain Λ] {X}

/-- A sheaf of `Λ`-modules is **sectionwise torsion-free** if all of its modules of sections
are torsion-free. -/
def IsSectionwiseTorsionFree (F : EtaleModules.{u, 0} Λ X) : Prop :=
  ∀ U : X.Etaleᵒᵖ, Module.IsTorsionFree Λ (F.obj.obj U)

omit [IsDomain Λ] in
/-- A subsheaf of a sectionwise torsion-free sheaf is sectionwise torsion-free. -/
theorem IsSectionwiseTorsionFree.of_mono {F G : EtaleModules.{u, 0} Λ X} (f : F ⟶ G) [Mono f]
    (hG : IsSectionwiseTorsionFree G) : IsSectionwiseTorsionFree F := by
  intro U
  have := hG U
  have : Mono ((sheafToPresheaf _ _).map f) := inferInstance
  have : Mono (((sheafToPresheaf _ _).map f).app U) := inferInstance
  exact Function.Injective.moduleIsTorsionFree (f.hom.app U).hom
    ((ModuleCat.mono_iff_injective _).mp this) (fun r m => map_smul _ r m)

/-- Multiplication by a scalar `a`, as an endomorphism of a presheaf of `Λ`-modules. -/
def presheafSMulEnd (a : Λ) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) : P ⟶ P where
  app U := ModuleCat.ofHom (a • LinearMap.id)
  naturality U V g := by
    ext x
    exact ((P.map g).hom.map_smul a x).symm

omit [IsDomain Λ] in
/-- Multiplication by a scalar commutes with every morphism of presheaves of modules. -/
@[reassoc]
theorem presheafSMulEnd_comp {P Q : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ} (a : Λ) (η : P ⟶ Q) :
    presheafSMulEnd a P ≫ η = η ≫ presheafSMulEnd a Q := by
  ext U x
  exact (η.app U).hom.map_smul a x

omit [IsDomain Λ] in
/-- Sheafification carries multiplication by a scalar to multiplication by that scalar. -/
theorem sheafifyMap_presheafSMulEnd (a : Λ) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    sheafifyMap X.smallEtaleTopology (presheafSMulEnd a P) =
      presheafSMulEnd a (sheafify X.smallEtaleTopology P) := by
  apply sheafify_hom_ext _ _ _ ((presheafToSheaf X.smallEtaleTopology _).obj P).property
  rw [← toSheafify_naturality, presheafSMulEnd_comp]

omit [IsDomain Λ] in
/-- **Sheafification preserves sectionwise torsion-freeness.** -/
theorem isSectionwiseTorsionFree_sheafify (P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ)
    (hP : ∀ U, Module.IsTorsionFree Λ (P.obj U)) :
    IsSectionwiseTorsionFree ((presheafToSheaf X.smallEtaleTopology _).obj P) := by
  intro U
  refine ⟨fun a ha x y hxy => ?_⟩
  have hm : Mono (presheafSMulEnd a P) := by
    have (V : X.Etaleᵒᵖ) : Mono ((presheafSMulEnd a P).app V) := by
      have := hP V
      rw [ModuleCat.mono_iff_injective]
      exact ha.isSMulRegular
    exact NatTrans.mono_of_mono_app _
  have hm' : Mono ((sheafToPresheaf _ _).map
      ((presheafToSheaf X.smallEtaleTopology _).map (presheafSMulEnd a P))) := inferInstance
  have hm'' : Mono ((presheafSMulEnd a (sheafify X.smallEtaleTopology P)).app U) := by
    rw [← sheafifyMap_presheafSMulEnd]
    exact inferInstanceAs (Mono (((sheafToPresheaf _ _).map
      ((presheafToSheaf X.smallEtaleTopology _).map (presheafSMulEnd a P))).app U))
  exact (ModuleCat.mono_iff_injective _).mp hm'' hxy

/-- The counit `Λ^{(M)} ⟶ M` of the free module on the underlying set of a module. -/
def freeSplitCounit (M : ModuleCat.{u + 1} Λ) :
    (ModuleCat.freeSplit.{u + 1, 0} Λ).obj ((forget (ModuleCat.{u + 1} Λ)).obj M) ⟶ M :=
  ModuleCat.freeSplitDesc (fun x => x)

omit [IsDomain Λ] in
/-- The counit `Λ^{(M)} ⟶ M` sends the basis vector of `x` to `x`. -/
theorem freeSplitCounit_freeSplitMk (M : ModuleCat.{u + 1} Λ)
    (x : (forget (ModuleCat.{u + 1} Λ)).obj M) :
    freeSplitCounit M (ModuleCat.freeSplitMk x) = x :=
  ModuleCat.freeSplitDesc_apply _ x

omit [IsDomain Λ] in
/-- The counit `Λ^{(M)} ⟶ M` is natural in the module `M`. -/
@[reassoc]
theorem freeSplitCounit_naturality {M N : ModuleCat.{u + 1} Λ} (f : M ⟶ N) :
    (ModuleCat.freeSplit.{u + 1, 0} Λ).map ((forget (ModuleCat.{u + 1} Λ)).map f) ≫
        freeSplitCounit N = freeSplitCounit M ≫ f := by
  refine ModuleCat.freeSplit_hom_ext (fun x => ?_)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.freeSplit_map_apply,
    freeSplitCounit_freeSplitMk, freeSplitCounit_freeSplitMk]
  rfl

omit [IsDomain Λ] in
/-- **Every sheaf of `Λ`-modules is a quotient of a sectionwise torsion-free one**: the
sheafified free module on its underlying sheaf of sets maps onto it. -/
theorem exists_isSectionwiseTorsionFree_epi (F : EtaleModules.{u, 0} Λ X) :
    ∃ (G : EtaleModules.{u, 0} Λ X) (p : G ⟶ F), IsSectionwiseTorsionFree G ∧ Epi p := by
  let P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
    F.obj ⋙ forget (ModuleCat.{u + 1} Λ) ⋙ ModuleCat.freeSplit.{u + 1, 0} Λ
  let ε : P ⟶ F.obj :=
    { app U := freeSplitCounit (F.obj.obj U)
      naturality U V g := freeSplitCounit_naturality (F.obj.map g) }
  have hε : Epi ε := by
    have (U : X.Etaleᵒᵖ) : Epi (ε.app U) := by
      rw [ModuleCat.epi_iff_surjective]
      intro x
      exact ⟨ModuleCat.freeSplitMk x, freeSplitCounit_freeSplitMk _ x⟩
    exact NatTrans.epi_of_epi_app ε
  have : Epi ((presheafToSheaf X.smallEtaleTopology _).map ε) := inferInstance
  refine ⟨(presheafToSheaf X.smallEtaleTopology _).obj P,
    (presheafToSheaf X.smallEtaleTopology _).map ε ≫
      (sheafificationAdjunction X.smallEtaleTopology _).counit.app F, ?_, epi_comp _ _⟩
  apply isSectionwiseTorsionFree_sheafify
  intro U
  show Module.IsTorsionFree Λ (((forget (ModuleCat.{u + 1} Λ)).obj (F.obj.obj U)) →₀ Λ)
  infer_instance

end TorsionFree

/-! ### Extension of scalars on sequences with torsion-free cokernel -/

section ExtendScalars

variable {Λ Λ' : Type} [CommRing Λ] [IsDedekindDomain Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X}

/-- Sheafified `G` keeps `S.f` a monomorphism for a short exact `S` as soon as `G` keeps each
sectionwise `S.f` injective, given that sectionwise `S.f` is injective and `S.f, S.g` exact. -/
private theorem mono_composeAndSheafify_map_of_shortExact {R R' : Type} [Ring R] [Ring R']
    (G : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} R') (S : ShortComplex (EtaleModules.{u, 0} R X))
    (hS : S.ShortExact)
    (h : ∀ U : X.Etaleᵒᵖ, Function.Injective (S.f.hom.app U).hom →
      Function.Exact (S.f.hom.app U).hom (S.g.hom.app U).hom →
        Function.Injective (G.map (S.f.hom.app U)).hom) :
    Mono ((Sheaf.composeAndSheafify X.smallEtaleTopology G).map S.f) := by
  have := hS.mono_f
  have hpre : Mono (Functor.whiskerRight S.f.hom G) := by
    have (U : X.Etaleᵒᵖ) : Mono (G.map (S.f.hom.app U)) := by
      let E := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
        (evaluation X.Etaleᵒᵖ (ModuleCat.{u + 1} R)).obj U
      obtain ⟨hE, hEm⟩ :=
        (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp inferInstance S hS
      rw [ModuleCat.mono_iff_injective]
      exact h U ((ModuleCat.mono_iff_injective _).mp hEm)
        (LinearMap.exact_iff.mpr hE.moduleCat_range_eq_ker.symm)
    exact @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ this
  have : Mono (((Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u + 1} R)
      (ModuleCat.{u + 1} R')).obj G).map
        ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).map S.f)) := hpre
  exact (presheafToSheaf X.smallEtaleTopology _).map_mono _

/-- **Extension of scalars keeps a monomorphism with sectionwise torsion-free cokernel a
monomorphism.**  Sectionwise, the sequence is exact on the left, and tensoring over a Dedekind
domain with any module keeps the first map injective when the last term is torsion-free;
sheafification preserves monomorphisms. -/
theorem mono_extendScalars_map_of_shortExact (S : ShortComplex (EtaleModules.{u, 0} Λ X))
    (hS : S.ShortExact) (hP : IsSectionwiseTorsionFree S.X₃) :
    Mono ((etaleModuleExtendScalars ρ X).map S.f) :=
  mono_composeAndSheafify_map_of_shortExact _ S hS fun U hf hex => by
    have := hP U
    exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree (R := Λ)
      (S.f.hom.app U).hom (S.g.hom.app U).hom hf hex
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of Λ' Λ'))

/-- **`Ext^{n+1}(P, res_ρ I) = 0`** for every injective sheaf of `Λ'`-modules `I` and every
sectionwise torsion-free sheaf of `Λ`-modules `P`, when `Λ` is a Dedekind domain. -/
theorem ext_restrictScalars_eq_zero_of_isTorsionFree (I : EtaleModules.{u, 0} Λ' X)
    [Injective I] (P : EtaleModules.{u, 0} Λ X) (hP : IsSectionwiseTorsionFree P) (n : ℕ)
    (e : Ext.{u + 1} P ((etaleModuleRestrictScalars ρ X).obj I) (n + 1)) : e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_adjunction (etaleModuleExtendScalars ρ X)
    (etaleModuleRestrictScalars ρ X) (etaleModuleExtendScalarsAdj ρ X)
    IsSectionwiseTorsionFree (fun f _ hY => IsSectionwiseTorsionFree.of_mono f hY)
    exists_isSectionwiseTorsionFree_epi
    (fun S hS hP => mono_extendScalars_map_of_shortExact ρ S hS hP) I n P hP e

end ExtendScalars

/-! ### Sections over an object -/

section Sections

variable {Λ : Type} [Ring Λ] {X}

/-- The sections over an object are additive. -/
instance sheafSections_obj_additive (U : X.Etale) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)).Additive where
  map_add := rfl

/-- The sections over an object are left exact. -/
instance sheafSections_obj_preservesFiniteLimits (U : X.Etale) :
    PreservesFiniteLimits ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (op U)) :=
  preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (X := U)).symm

end Sections

/-! ### Sections over an object are corepresentable -/

section Corepresentation

variable {Λ : Type} [CommRing Λ] {X}

/-- The free presheaf of `Λ`-modules on the presheaf represented by `U`. -/
abbrev freeYonedaPresheaf (U : X.Etale) : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  yoneda.obj U ⋙ uliftFunctor.{u + 1} ⋙ ModuleCat.freeSplit.{u + 1, 0} Λ

/-- Morphisms out of the free presheaf on the presheaf represented by `U` are sections over
`U`. -/
def freeYonedaPresheafHomAddEquiv (U : X.Etale) (M : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ) :
    (freeYonedaPresheaf (Λ := Λ) U ⟶ M) ≃+ M.obj (op U) where
  toFun φ := φ.app (op U) (ModuleCat.freeSplitMk (ULift.up (𝟙 U)))
  invFun m :=
    { app V := ModuleCat.freeSplitDesc (fun g : ULift.{u + 1} (V.unop ⟶ U) => M.map g.down.op m)
      naturality V W h := by
        refine ModuleCat.freeSplit_hom_ext (fun g => ?_)
        rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
        refine ((congrArg _ (ModuleCat.freeSplit_map_apply _ g)).trans
          (ModuleCat.freeSplitDesc_apply _ _)).trans ?_
        refine Eq.trans ?_ (congrArg (M.map h) (ModuleCat.freeSplitDesc_apply _ g).symm)
        change M.map (h.unop ≫ g.down).op m = M.map h (M.map g.down.op m)
        rw [op_comp, Functor.map_comp, ModuleCat.comp_apply]
        rfl }
  left_inv φ := by
    ext V : 2
    refine ModuleCat.freeSplit_hom_ext (fun g => ?_)
    refine (ModuleCat.freeSplitDesc_apply _ g).trans ?_
    have h := congrArg (fun f => f (ModuleCat.freeSplitMk (ULift.up (𝟙 U))))
      (congrArg ModuleCat.Hom.hom (φ.naturality g.down.op))
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
    refine h.symm.trans ?_
    congr 1
    refine (ModuleCat.freeSplit_map_apply _ _).trans ?_
    change ModuleCat.freeSplitMk (ULift.up (g.down ≫ 𝟙 U)) = _
    rw [Category.comp_id]
    rfl
  right_inv m := by
    refine (ModuleCat.freeSplitDesc_apply
      (fun g : ULift.{u + 1} (U ⟶ U) => M.map g.down.op m) (ULift.up (𝟙 U))).trans ?_
    change M.map (𝟙 (op U)) m = m
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_add' φ ψ := rfl

/-- The sheafified free module on the presheaf represented by `U`. -/
abbrev freeYonedaSheaf (U : X.Etale) : EtaleModules.{u, 0} Λ X :=
  (presheafToSheaf X.smallEtaleTopology _).obj (freeYonedaPresheaf (Λ := Λ) U)

/-- **The sections over `U` are corepresented by the sheafified free module on the presheaf
represented by `U`**, as abelian groups. -/
@[sga "4 XVIII 1.4.24" "special case"]
def freeYonedaSheafSectionsCorepresentation (U : X.Etale) :
    (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      preadditiveCoyoneda.obj (op (freeYonedaSheaf (Λ := Λ) U)) := by
  refine (NatIso.ofComponents (fun F =>
    (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homAddEquiv
      (freeYonedaPresheaf (Λ := Λ) U) F).trans
      (freeYonedaPresheafHomAddEquiv U F.obj)).toAddCommGrpIso) ?_).symm
  intro F G map
  ext element
  change ((presheafToSheaf X.smallEtaleTopology _).obj (freeYonedaPresheaf (Λ := Λ) U) ⟶ F)
    at element
  change freeYonedaPresheafHomAddEquiv U G.obj
    ((sheafificationAdjunction X.smallEtaleTopology _).homEquiv _ G (element ≫ map)) =
    map.hom.app (op U) (freeYonedaPresheafHomAddEquiv U F.obj
      ((sheafificationAdjunction X.smallEtaleTopology _).homEquiv _ F element))
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The sheafified free module on a representable presheaf is sectionwise torsion-free. -/
theorem isSectionwiseTorsionFree_freeYonedaSheaf [IsDomain Λ] (U : X.Etale) :
    IsSectionwiseTorsionFree (freeYonedaSheaf (Λ := Λ) U) :=
  isSectionwiseTorsionFree_sheafify _ (fun V => by
    show Module.IsTorsionFree Λ (ULift.{u + 1} (V.unop ⟶ U) →₀ Λ)
    infer_instance)

end Corepresentation

/-! ### Acyclicity for the sections over an object -/

section Acyclic

variable {Λ Λ' : Type} [CommRing Λ] [IsDedekindDomain Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X}

/-- If all `Ext^{n+1}` out of the free sheaf on `U` into `A` vanish, the sections over `U` have no
cohomology in degree `n + 1` on `A`. -/
private theorem isZero_rightDerived_sections_of_ext_eq_zero {R : Type} [CommRing R]
    (A : EtaleModules.{u, 0} R X) (U : X.Etale) (n : ℕ)
    (h : ∀ e : Ext.{u + 1} (freeYonedaSheaf (Λ := R) U) A (n + 1), e = 0) :
    IsZero ((((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U) ⋙
        forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).rightDerived (n + 1)).obj A) := by
  refine IsZero.of_iso ?_ ((ModuleSheafCohomology.rightDerivedIso
    (freeYonedaSheafSectionsCorepresentation U) (n + 1)).app _ ≪≫
      (ModuleSheafCohomology.rightDerivedCoyonedaSuccIso _ n).app _)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ⟨fun a b => by rw [h a, h b]⟩

/-- A sheaf with vanishing higher derived sections over `U` is acyclic for the sections over
`U`, read through the forgetful functor to abelian groups. -/
private theorem rightAcyclic_sections_of_isZero_rightDerived {R : Type} [CommRing R]
    (A : EtaleModules.{u, 0} R X) (U : X.Etale)
    (h : ∀ n : ℕ, IsZero ((((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
      (op U) ⋙ forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).rightDerived (n + 1)).obj A)) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U)).rightAcyclic A := by
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have h' := (h n).of_iso
    ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op U))
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) (n + 1)).app A)
  rw [IsZero.iff_id_eq_zero] at h' ⊢
  exact (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map_injective
    (by rw [CategoryTheory.Functor.map_id, Functor.map_zero]; exact h')

/-- **`res_ρ I` has no higher cohomology over any object `U`** of the small étale site, for an
injective sheaf of `Λ'`-modules `I`: the higher right derived functors of the sections over `U`
vanish on it. -/
theorem isZero_rightDerived_sections_restrictScalars (I : EtaleModules.{u, 0} Λ' X)
    [Injective I] (U : X.Etale) (n : ℕ) :
    IsZero ((((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).rightDerived (n + 1)).obj
      ((etaleModuleRestrictScalars ρ X).obj I)) :=
  isZero_rightDerived_sections_of_ext_eq_zero _ U n
    (ext_restrictScalars_eq_zero_of_isTorsionFree ρ I _
      (isSectionwiseTorsionFree_freeYonedaSheaf U) n)

/-- **`res_ρ I` is acyclic for the sections over every object `U`**, `I` an injective sheaf of
`Λ'`-modules: it is the vanishing above, read through the forgetful functor to abelian groups,
which is exact and reflects zero objects. -/
theorem rightAcyclic_sections_restrictScalars (I : EtaleModules.{u, 0} Λ' X) [Injective I]
    (U : X.Etale) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)).rightAcyclic
      ((etaleModuleRestrictScalars ρ X).obj I) :=
  rightAcyclic_sections_of_isZero_rightDerived _ U
    (isZero_rightDerived_sections_restrictScalars ρ I U)

end Acyclic

/-! ### Restriction of scalars to `ℤ` from a noncommutative ring -/

section IntNoncomm

variable {Λ' : Type} [Ring Λ'] {X}

/-- **Extension of scalars from `ℤ` to a ring `Λ'`, not necessarily commutative, keeps a
monomorphism with sectionwise torsion-free cokernel a monomorphism.** -/
theorem mono_noncommExtendScalars_int_map_of_shortExact
    (S : ShortComplex (EtaleModules.{u, 0} ℤ X)) (hS : S.ShortExact)
    (hP : IsSectionwiseTorsionFree S.X₃) :
    Mono ((etaleModuleNoncommExtendScalars (Int.castRingHom Λ') X).map S.f) :=
  mono_composeAndSheafify_map_of_shortExact _ S hS fun U hf hex => by
    have := hP U
    exact Stacks.NoncommChangeOfRings.map_intCast_injective (B := Λ')
      (S.f.hom.app U).hom (S.g.hom.app U).hom hf hex

/-- **`Ext^{n+1}(P, I) = 0` over `ℤ`** for every injective sheaf of `Λ'`-modules `I`, read as an
abelian sheaf, and every sectionwise torsion-free abelian sheaf `P`; `Λ'` is any ring. -/
theorem ext_restrictScalars_int_eq_zero_of_isTorsionFree (I : EtaleModules.{u, 0} Λ' X)
    [Injective I] (P : EtaleModules.{u, 0} ℤ X) (hP : IsSectionwiseTorsionFree P) (n : ℕ)
    (e : Ext.{u + 1} P ((etaleModuleRestrictScalars (Int.castRingHom Λ') X).obj I) (n + 1)) :
    e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_adjunction
    (etaleModuleNoncommExtendScalars (Int.castRingHom Λ') X)
    (etaleModuleRestrictScalars (Int.castRingHom Λ') X)
    (etaleModuleNoncommExtendScalarsAdj (Int.castRingHom Λ') X)
    IsSectionwiseTorsionFree (fun f _ hY => IsSectionwiseTorsionFree.of_mono f hY)
    exists_isSectionwiseTorsionFree_epi
    (fun S hS hP => mono_noncommExtendScalars_int_map_of_shortExact S hS hP) I n P hP e

/-- The underlying abelian sheaf of an injective sheaf of `Λ'`-modules has no higher cohomology
over any object `U`; `Λ'` is any ring. -/
theorem isZero_rightDerived_sections_restrictScalars_int (I : EtaleModules.{u, 0} Λ' X)
    [Injective I] (U : X.Etale) (n : ℕ) :
    IsZero ((((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)).obj (op U) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).rightDerived (n + 1)).obj
      ((etaleModuleRestrictScalars (Int.castRingHom Λ') X).obj I)) :=
  isZero_rightDerived_sections_of_ext_eq_zero _ U n
    (ext_restrictScalars_int_eq_zero_of_isTorsionFree I _
      (isSectionwiseTorsionFree_freeYonedaSheaf U) n)

/-- **The underlying abelian sheaf of an injective sheaf of `Λ'`-modules is acyclic for the
sections over every object**; `Λ'` is any ring. -/
theorem rightAcyclic_sections_restrictScalars_int (I : EtaleModules.{u, 0} Λ' X) [Injective I]
    (U : X.Etale) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)).obj (op U)).rightAcyclic
      ((etaleModuleRestrictScalars (Int.castRingHom Λ') X).obj I) :=
  rightAcyclic_sections_of_isZero_rightDerived _ U
    (isZero_rightDerived_sections_restrictScalars_int I U)

end IntNoncomm

/-! ### Sheaves acyclic over every object -/

section Everywhere

variable {Λ : Type} [Ring Λ] {X}

/-- A sheaf of `Λ`-modules is **acyclic everywhere** if it is acyclic for the sections over
every object of the small étale site. -/
@[sga "4 V 4.1" "special case", sga "4 V 4.2" "special case"]
def IsAcyclicEverywhere (A : EtaleModules.{u, 0} Λ X) : Prop :=
  ∀ U : X.Etale, ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op U)).rightAcyclic A

/-- An injective sheaf of `Λ`-modules is acyclic everywhere. -/
theorem isAcyclicEverywhere_of_injective (A : EtaleModules.{u, 0} Λ X) [Injective A] :
    IsAcyclicEverywhere A :=
  fun _ => Functor.rightAcyclic_of_injective _ _

/-- For a morphism of commutative rings `ρ : Λ₀ →+* Λ` with `Λ₀` a Dedekind domain, the
restriction of scalars along `ρ` of an injective sheaf of `Λ`-modules is acyclic everywhere. -/
theorem isAcyclicEverywhere_restrictScalars {Λ : Type} [CommRing Λ] {Λ₀ : Type} [CommRing Λ₀]
    [IsDedekindDomain Λ₀] (ρ : Λ₀ →+* Λ) (I : EtaleModules.{u, 0} Λ X) [Injective I] :
    IsAcyclicEverywhere ((etaleModuleRestrictScalars ρ X).obj I) :=
  fun U => rightAcyclic_sections_restrictScalars (X := X) ρ I U

/-- **Sheaves acyclic everywhere are adapted to direct image**: a short exact sequence whose
first two terms are acyclic everywhere has its third term acyclic everywhere, and stays short
exact after direct image, because it stays short exact on the sections over every object. -/
theorem isAcyclicEverywhere_and_shortExact_map {Y : Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex (EtaleModules.{u, 0} Λ X)) (hS : S.ShortExact)
    (h₁ : IsAcyclicEverywhere S.X₁) (h₂ : IsAcyclicEverywhere S.X₂) :
    IsAcyclicEverywhere S.X₃ ∧ (S.map (etaleModuleDirectImage.{u, 0} Λ f)).ShortExact := by
  refine ⟨fun U => ((Functor.rightAcyclic_and_shortExact_map_of_shortExact _ S hS).2.1
    (h₁ U) (h₂ U)).1, ?_⟩
  have : (etaleModuleDirectImage.{u, 0} Λ f).IsRightAdjoint :=
    (etaleModuleInverseImageAdj.{u, 0} Λ f).isRightAdjoint
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (etaleModuleDirectImage.{u, 0} Λ f)).1 inferInstance S hS
  refine { exact := h.1, mono_f := h.2, epi_g := ?_ }
  apply (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).epi_of_epi_map
  have (V : Y.Etaleᵒᵖ) : Epi (((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((etaleModuleDirectImage.{u, 0} Λ f).map S.g)).app V) :=
    ((Functor.rightAcyclic_and_shortExact_map_of_shortExact
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op ((smallEtaleBaseChange f).obj V.unop))) S hS).2.1
      (h₁ _) (h₂ _)).2.epi_g
  exact @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ this

/-- **A sheaf acyclic everywhere is acyclic for direct image.** -/
theorem rightAcyclic_directImage_of_isAcyclicEverywhere {Y : Scheme.{u}} (f : X ⟶ Y)
    (A : EtaleModules.{u, 0} Λ X) (hA : IsAcyclicEverywhere A) :
    (etaleModuleDirectImage.{u, 0} Λ f).rightAcyclic A :=
  Functor.le_rightAcyclic _ (fun A => IsAcyclicEverywhere A)
    (fun A => ⟨Injective.under A, isAcyclicEverywhere_of_injective (Injective.under A),
      Injective.ι A, inferInstance⟩)
    (fun S hS h₁ h₂ => isAcyclicEverywhere_and_shortExact_map f S hS h₁ h₂) A hA

/-- **Acyclicity everywhere can be tested on the underlying sheaf of abelian groups**, read as a
sheaf of `ℤ`-modules: the cohomology of `B` over `U`, read as a `ℤ`-module, is the cohomology of
the underlying `ℤ`-module sheaf, because restriction of scalars to `ℤ` carries injectives to
sheaves acyclic everywhere. -/
theorem IsAcyclicEverywhere.of_restrictScalars_int (B : EtaleModules.{u, 0} Λ X)
    (h : IsAcyclicEverywhere ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj B)) :
    IsAcyclicEverywhere B := by
  intro U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  have hU := h U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hU
  let G := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)
  let G₀ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)).obj (op U)
  let F := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let r := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let e : G ⋙ r ≅ F ⋙ G₀ := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have hz : IsZero (r.obj ((G.rightDerived p).obj B)) :=
    (hU p hp).of_iso
      ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso G r p).app B ≪≫
        (ModuleSheafCohomology.rightDerivedIso e p).app B ≪≫
        (Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic F G₀
          (fun I _ => rightAcyclic_sections_restrictScalars_int I U) p).app B)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact r.map_injective (by rw [CategoryTheory.Functor.map_id, Functor.map_zero]; exact hz)

/-- **Restriction of scalars along any morphism of rings carries injectives to sheaves acyclic
everywhere.** Restricting further to `ℤ` gives the underlying abelian sheaf of the injective,
which is acyclic everywhere, `ℤ` being a Dedekind domain. -/
theorem isAcyclicEverywhere_restrictScalars' {Λ' : Type} [Ring Λ'] (ρ : Λ →+* Λ')
    (I : EtaleModules.{u, 0} Λ' X) [Injective I] :
    IsAcyclicEverywhere ((etaleModuleRestrictScalars ρ X).obj I) := by
  apply IsAcyclicEverywhere.of_restrictScalars_int
  intro U
  let e := ModuleCat.restrictScalarsComp'.{u + 1}
      (Int.castRingHom Λ) ρ (Int.castRingHom Λ') (RingHom.ext_int _ _)
  exact (Functor.rightAcyclic _).prop_of_iso
    { hom := (sheafCompose_map X.smallEtaleTopology e.hom).app I
      inv := (sheafCompose_map X.smallEtaleTopology e.inv).app I
      hom_inv_id := by ext; rfl
      inv_hom_id := by ext; rfl } (rightAcyclic_sections_restrictScalars_int I U)

end Everywhere

end Stacks.EtaleCohomology

end
