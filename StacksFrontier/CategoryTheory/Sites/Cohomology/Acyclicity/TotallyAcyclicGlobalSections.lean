module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# A totally acyclic sheaf of modules is acyclic for global sections

Let `(C, J)` be a small site and `O` a sheaf of rings on it. A sheaf of `O`-modules whose
underlying abelian sheaf is totally acyclic in the sense of Stacks 072Y — its cohomology over
every sheaf of sets vanishes in positive degrees — is right acyclic for the global sections
functor `Γ(C, -)` of Stacks 071H. This is part (3) of Stacks 0731.

The proof is the one the source gives: part (3) is the special case of total acyclicity at
`K = e`, the final object of the topos. Concretely, global sections of abelian sheaves are
corepresented by the constant sheaf on `ℤ` (`ModuleSheafCohomology.globalSectionsRepresentation`),
and that constant sheaf is the free abelian sheaf on the final presheaf of sets, so total
acyclicity gives vanishing of `Ext^{n+1}` out of it; `Ext` out of a fixed object is the right
derived functor of the corepresented functor, so the higher derived functors of
`Γ(C, -)` on the underlying abelian sheaf vanish. Stacks 03FD transports that vanishing from
the underlying abelian sheaf to the sheaf of modules, and
`globalSectionsUnderlyingIso` identifies the module-valued global sections of 071H with the
abelian-group-valued ones, so the vanishing is vanishing of `R^{n+1} Γ` in modules. Finally
right acyclicity of a left exact functor is exactly vanishing of its higher right derived
functors (Stacks 015C).

## Main definitions

* `Stacks.Cohomology.globalSectionsUnderlyingIso`: the module-valued global sections functor
  of Stacks 071H, followed by the forgetful functor to abelian groups, is the global sections
  functor of the underlying abelian sheaf.

## Main results

* `Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections`: part (3) of Stacks 0731.
* `Stacks.Cohomology.isZero_rightDerived_moduleGlobalSections_of_isTotallyAcyclic` and
  `Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_moduleGlobalSections`: the same for the global
  sections functor valued in abelian groups, the underlying abelian sheaf followed by
  `CategoryTheory.Sheaf.Γ`; the module-valued statement is deduced from it.
* `Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived`: right acyclicity of an object for a
  left exact functor is vanishing of all its higher `ℕ`-indexed right derived functors there.
* `Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`: postcomposing with a
  homology-preserving functor commutes with right derived functors, object by object.

## Implementation notes

Global sections of a sheaf of modules are a limit over the site, computed sectionwise; that is
the content of `moduleSectionsConeIsLimit`, and it is what makes
`globalSectionsUnderlyingIso` an isomorphism and the global sections functor left exact.

The universe of the `Ext`-groups witnessing total acyclicity is independent of the universe of
the sheaves, as it is in `Stacks.Cohomology.IsTotallyAcyclic`; it is changed to the sheaf
universe with `Abelian.Ext.chgUniv` where the derived-functor comparison needs it.

Stating `Functor.rightAcyclic` requires a `HasRightDerivedFunctor` instance, and that is proved
here rather than assumed: `SheafOfModules.{u} R` on a small site is Grothendieck abelian, hence
has enough injectives, and the cheap instance that `EnoughInjectives` supplies is given
precedence over the default route, which would try to prove termwise injectivity of an unknown
complex. The only hypothesis on the module is therefore the total acyclicity the source assumes.

Only part (3) of Stacks 0731 is proved here, and only its clause carries the tag. Parts (1),
(2) and (4) — sections over an object of the site, sections against a presheaf of sets, and
direct image along a morphism of ringed topoi — are proved elsewhere and by a different route:
not through the comparison of `Ext` out of a sheafified free module with the derived functors
of sections against an abelian presheaf that the source's argument suggests, but through the
adapted-class criterion of Stacks 05T8. See
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicDirectImage.lean` for
part (4) and
`StacksFrontier/CategoryTheory/Sites/Cohomology/Acyclicity/TotallyAcyclicSections.lean` for
parts (1) and (2).

## References

* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe x u

namespace Stacks.Cohomology

/-! ### Right acyclicity in terms of the `ℕ`-indexed derived functors -/

/-- For a left exact functor, right acyclicity of an object is vanishing of all its higher
right derived functors there. This is Stacks 015C read through the comparison of the two
indexings of the right derived functors. -/
@[sga "4 V 0.4"]
lemma rightAcyclic_iff_isZero_rightDerived
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] (M : A) :
    F.rightAcyclic M ↔ ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj M) := by
  rw [(F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 inferInstance]
  refine ⟨fun h p hp => ?_, fun h i hi => ?_⟩
  · exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F p M).2
      (h (p : ℤ) (by exact_mod_cast hp))
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F p M).1
      (h p (by exact_mod_cast hi))

/-- Postcomposing with a homology-preserving functor commutes with right derived functors,
object by object. -/
theorem rightDerived_comp_iso_of_preservesHomology
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E] [HasInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ E) [G.Additive] [G.PreservesHomology]
    [(F ⋙ G).Additive] (i : ℕ) (Z : A) :
    Nonempty (G.obj ((F.rightDerived i).obj Z) ≅ ((F ⋙ G).rightDerived i).obj Z) := by
  let c := ComplexShape.up ℕ
  let I := injectiveResolution Z
  let K := (F.mapHomologicalComplex c).obj I.cocomplex
  have hpres : G.obj ((HomologicalComplex.homologyFunctor B c i).obj K) ≅
      (HomologicalComplex.homologyFunctor E c i).obj ((G.mapHomologicalComplex c).obj K) :=
    (G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ i).app K)) ≪≫
      ((K.sc i).mapHomologyIso G).symm ≪≫
      ((HomologicalComplex.homologyFunctorIso _ _ i).app
        ((G.mapHomologicalComplex c).obj K)).symm
  exact ⟨G.mapIso (I.isoRightDerivedObj F i) ≪≫ hpres ≪≫
    (I.isoRightDerivedObj (F ⋙ G) i).symm⟩

/-! ### Global sections of a sheaf of modules as a limit -/

section GlobalSections

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The cone exhibiting the compatible global sections of a sheaf of modules as the limit of
its sections over the site. -/
def moduleSectionsCone (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    Cone ((SheafOfModules.toSheaf R).obj M).obj where
  pt := AddCommGrpCat.of M.sections
  π :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => s.eval U
          map_zero' := rfl
          map_add' := fun s t => rfl }
      naturality := by
        intro U V f
        ext s
        change s.eval V = M.val.map f (s.eval U)
        exact (s.property f).symm }

/-- Global sections of a sheaf of modules are the limit of its sections over the site. -/
def moduleSectionsConeIsLimit (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    IsLimit (moduleSectionsCone R M) := by
  let F := ((SheafOfModules.toSheaf R).obj M).obj
  let c := moduleSectionsCone R M
  apply isLimitOfReflects (forget AddCommGrpCat.{u})
  have hb : Function.Bijective
      (Types.sectionOfCone ((forget AddCommGrpCat.{u}).mapCone c)) :=
    ⟨fun s t h => PresheafOfModules.sections_ext _ _ fun U =>
      congrArg (fun z : ((F ⋙ forget AddCommGrpCat.{u}).sections) => z.1 U) h,
      fun s => ⟨s, rfl⟩⟩
  exact Classical.choice ((Types.isLimit_iff_bijective_sectionOfCone _).2 hb)

/-- The limit of the sections of a sheaf of modules is its group of compatible global
sections. -/
def moduleSectionsLimitIso (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    limit ((SheafOfModules.toSheaf R).obj M).obj ≅ AddCommGrpCat.of M.sections :=
  (limit.isLimit _).conePointUniqueUpToIso (moduleSectionsConeIsLimit R M)

/-- `moduleSectionsLimitIso` is natural in the sheaf of modules. -/
lemma moduleSectionsLimitIso_naturality (R : Sheaf J RingCat.{u})
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
    ((sheafToPresheaf J AddCommGrpCat.{u} ⋙ lim).map
        ((SheafOfModules.toSheaf R).map f)) ≫ (moduleSectionsLimitIso R N).hom =
      (moduleSectionsLimitIso R M).hom ≫
        (forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}).map
          ((SiteModules.globalSectionsFunctor R).map f) := by
  apply (moduleSectionsConeIsLimit R N).hom_ext
  intro U
  let FM := ((SheafOfModules.toSheaf R).obj M).obj
  let FN := ((SheafOfModules.toSheaf R).obj N).obj
  let α := (sheafToPresheaf J AddCommGrpCat.{u}).map ((SheafOfModules.toSheaf R).map f)
  have hN : (moduleSectionsLimitIso R N).hom ≫ (moduleSectionsCone R N).π.app U =
      limit.π FN U :=
    IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit FN)
      (moduleSectionsConeIsLimit R N) U
  have hM : (moduleSectionsLimitIso R M).hom ≫ (moduleSectionsCone R M).π.app U =
      limit.π FM U :=
    IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit FM)
      (moduleSectionsConeIsLimit R M) U
  have hmaps :
      ((SiteModules.globalSectionsFunctor R ⋙
        forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}).map f ≫
        (moduleSectionsCone R N).π.app U) =
      ((moduleSectionsCone R M).π.app U ≫ α.app U) := by
    ext s
    rfl
  calc
    (((sheafToPresheaf J AddCommGrpCat.{u} ⋙ lim).map
        ((SheafOfModules.toSheaf R).map f)) ≫ (moduleSectionsLimitIso R N).hom) ≫
        (moduleSectionsCone R N).π.app U =
      lim.map α ≫ limit.π FN U := by
        change lim.map α ≫
          ((moduleSectionsLimitIso R N).hom ≫ (moduleSectionsCone R N).π.app U) =
          lim.map α ≫ limit.π FN U
        exact congrArg (fun k => lim.map α ≫ k) hN
    _ = limit.π FM U ≫ α.app U := limMap_π α U
    _ = ((moduleSectionsLimitIso R M).hom ≫ (moduleSectionsCone R M).π.app U) ≫
        α.app U := by rw [← hM]
    _ = (moduleSectionsLimitIso R M).hom ≫
        ((moduleSectionsCone R M).π.app U ≫ α.app U) := Category.assoc _ _ _
    _ = (moduleSectionsLimitIso R M).hom ≫
        ((SiteModules.globalSectionsFunctor R ⋙
          forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}).map f ≫
          (moduleSectionsCone R N).π.app U) :=
          congrArg (fun k => (moduleSectionsLimitIso R M).hom ≫ k) hmaps.symm
    _ = ((moduleSectionsLimitIso R M).hom ≫
        (SiteModules.globalSectionsFunctor R ⋙
          forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}).map f) ≫
        (moduleSectionsCone R N).π.app U := (Category.assoc _ _ _).symm

/-- The global sections functor of Stacks 071H, followed by the forgetful functor to abelian
groups, is the global sections functor of the underlying abelian sheaf. -/
def globalSectionsUnderlyingIso (R : Sheaf J RingCat.{u}) :
    SheafOfModules.toSheaf R ⋙ Sheaf.Γ J AddCommGrpCat.{u} ≅
      SiteModules.globalSectionsFunctor R ⋙
        forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (Sheaf.ΓNatIsoLim J AddCommGrpCat.{u}) ≪≫
    NatIso.ofComponents (fun M => moduleSectionsLimitIso R M)
      (fun f => moduleSectionsLimitIso_naturality R f)

end GlobalSections

/-! ### Part (3) of Stacks 0731 -/

-- As in `TotallyAcyclicDirectImage.lean`: `CategoryTheory.Functor.rightAcyclic` mentions
-- `HasRightDerivedFunctor`, and the cheap instance coming from `EnoughInjectives` is given
-- precedence over the route that would try to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R)
  [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{x} (Sheaf J AddCommGrpCat.{u})]

/-- **Total acyclicity kills `Ext` out of the constant sheaf on `ℤ`** in positive degrees: the
constant sheaf on `ℤ` is the free abelian sheaf on the final sheaf of sets. -/
theorem subsingleton_ext_constantSheaf_of_isTotallyAcyclic [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    {F : Sheaf J AddCommGrpCat.{u}} (hF : IsTotallyAcyclic.{x} J F) (n : ℕ) :
    Subsingleton (Ext.{u} ((constantSheaf J AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) F (n + 1)) := by
  let Kpre : Cᵒᵖ ⥤ Type u := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}
  let K := (presheafToSheaf J (Type u)).obj Kpre
  let X := (Presheaf.freeAbelianSheaf J).obj Kpre
  let Xsh := (Presheaf.freeAbelianSheaf J).obj K.obj
  -- The sheafification unit is a local isomorphism and the free abelian sheaf functor inverts
  -- those, so the free abelian sheaf on the final presheaf is the one on the final sheaf.
  have hiso : IsIso ((Presheaf.freeAbelianSheaf J).map (toSheafify J Kpre)) :=
    Presheaf.isIso_freeAbelianSheaf_map_of_W J _ (J.W_toSheafify Kpre)
  let ex : X ≅ Xsh := asIso ((Presheaf.freeAbelianSheaf J).map (toSheafify J Kpre))
  -- Total acyclicity at the final object of the topos.
  have hExtSh : Subsingleton (Ext.{u} Xsh F (n + 1)) := by
    have : Subsingleton (Ext.{x} Xsh F (n + 1)) := hF K (n + 1) (by omega)
    exact Ext.chgUniv.{u, x}.symm.subsingleton
  have hExt : Subsingleton (Ext.{u} X F (n + 1)) :=
    (((extFunctor (n + 1)).mapIso ex.op).app F).addCommGroupIsoToAddEquiv.subsingleton_congr.mp
      hExtSh
  -- The free abelian sheaf on the final presheaf is the constant sheaf on `ℤ`.
  let eFree : AddCommGrpCat.free.obj PUnit.{u + 1} ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
    ((FreeAbelianGroup.uniqueEquiv PUnit.{u + 1}).trans
      { toFun := ULift.up
        invFun := ULift.down
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }).toAddCommGrpIso
  let e := ((extFunctor (n + 1)).mapIso
    ((constantSheaf J AddCommGrpCat.{u}).mapIso eFree).op).app F
  let eX : X ≅ (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.free.obj PUnit.{u + 1}) :=
    (presheafToSheaf J AddCommGrpCat.{u}).mapIso
      (Functor.constComp Cᵒᵖ PUnit.{u + 1} AddCommGrpCat.free)
  let eXExt := ((extFunctor (n + 1)).mapIso eX.op).app F
  have hX : Subsingleton (((extFunctor (n + 1)).obj (op X)).obj F) := hExt
  exact (e ≪≫ eXExt).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr hX

/-- **The higher right derived functors of `Γ(C, -)` vanish at a sheaf of modules with totally
acyclic underlying abelian sheaf**, for the global sections functor valued in abelian groups:
the underlying abelian sheaf followed by `CategoryTheory.Sheaf.Γ`. This is the abelian-group
form of part (3) of Stacks 0731, from which the module-valued form below is deduced. -/
theorem isZero_rightDerived_moduleGlobalSections_of_isTotallyAcyclic
    [(Sheaf.Γ J AddCommGrpCat.{u}).Additive]
    (hM : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M)) (n : ℕ) :
    IsZero (((SheafOfModules.toSheaf R ⋙
      Sheaf.Γ J AddCommGrpCat.{u}).rightDerived (n + 1)).obj M) := by
  obtain ⟨eSite, -, -⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying J R
  have : HasExt.{u} (Sheaf J AddCommGrpCat.{u}) := inferInstance
  let Xrep := (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have := subsingleton_ext_constantSheaf_of_isTotallyAcyclic hM n
  have hExtRepZero : IsZero ((extFunctorObj Xrep (n + 1)).obj
      ((SheafOfModules.toSheaf R).obj M)) := by
    change IsZero (AddCommGrpCat.of (Ext.{u} Xrep ((SheafOfModules.toSheaf R).obj M) (n + 1)))
    exact AddCommGrpCat.isZero_of_subsingleton _
  -- `Ext` out of `Xrep` is the right derived functor of the functor it corepresents.
  have hCoy : IsZero (((preadditiveCoyoneda.obj (op Xrep)).rightDerived (n + 1)).obj
      ((SheafOfModules.toSheaf R).obj M)) :=
    hExtRepZero.of_iso ((ModuleSheafCohomology.rightDerivedCoyonedaSuccIso Xrep n).app
      ((SheafOfModules.toSheaf R).obj M))
  have hGamma : IsZero ((SheafOfModules.toSheaf R ⋙
      (Sheaf.Γ J AddCommGrpCat.{u}).rightDerived (n + 1)).obj M) :=
    hCoy.of_iso ((Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (ModuleSheafCohomology.rightDerivedIso
        (ModuleSheafCohomology.globalSectionsRepresentation J) (n + 1))).app M)
  -- Stacks 03FD: pass from the underlying abelian sheaf to the sheaf of modules.
  exact hGamma.of_iso ((eSite (n + 1)).app M)

/-- **A sheaf of modules with totally acyclic underlying abelian sheaf is right acyclic for
`Γ(C, -)`**, the global sections functor valued in abelian groups: the underlying abelian sheaf
followed by `CategoryTheory.Sheaf.Γ`. -/
theorem isTotallyAcyclic_rightAcyclic_moduleGlobalSections
    [(Sheaf.Γ J AddCommGrpCat.{u}).Additive]
    (hM : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M))
    [HasDerivedCategory (SheafOfModules.{u} R)] [HasDerivedCategory AddCommGrpCat.{u}] :
    (SheafOfModules.toSheaf R ⋙ Sheaf.Γ J AddCommGrpCat.{u}).rightAcyclic M := by
  apply (rightAcyclic_iff_isZero_rightDerived _ M).2
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  exact isZero_rightDerived_moduleGlobalSections_of_isTotallyAcyclic R M hM n

/-- **Stacks 0731, part (3).** A sheaf of modules whose underlying abelian sheaf is totally
acyclic is right acyclic for the functor of global sections. -/
@[stacks 0731 "part (3): the functor of global sections", sga "4 V 4.6" "flasque ⇒ Γ-acyclic"]
theorem isTotallyAcyclic_rightAcyclic_globalSections
    (hM : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M))
    [HasDerivedCategory.{u} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} (RingCat.sectionsSubring R.obj))] :
    (SiteModules.globalSectionsFunctor R).rightAcyclic M := by
  let E := SiteModules.globalSectionsFunctor R
  let G := forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}
  let eSections := (globalSectionsUnderlyingIso R).symm
  have : PreservesFiniteLimits (E ⋙ G) := preservesFiniteLimits_of_natIso eSections.symm
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E G
  apply (rightAcyclic_iff_isZero_rightDerived E M).2
  intro p hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have : (Sheaf.Γ J AddCommGrpCat.{u}).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hcomp : IsZero (((E ⋙ G).rightDerived (n + 1)).obj M) :=
    (isZero_rightDerived_moduleGlobalSections_of_isTotallyAcyclic R M hM n).of_iso
      ((ModuleSheafCohomology.rightDerivedIso eSections (n + 1)).app M)
  have hforg : IsZero ((E.rightDerived (n + 1) ⋙ G).obj M) :=
    hcomp.of_iso (rightDerived_comp_iso_of_preservesHomology E G (n + 1) M).some
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hforg)

end Stacks.Cohomology
