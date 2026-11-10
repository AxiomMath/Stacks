module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesAffineCaseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomSiteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Induction
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ConstructionDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable

/-!
# Global sections of coherent modules on a proper algebraic space are finite

Let `A` be a Noetherian ring and let `X` be an algebraic space proper over `Spec A`.  This file
proves that for every coherent `𝒪_X`-module `𝓕` the `A`-module `Γ(X, 𝓕)` is finite, and in
particular that the ring `Γ(X, 𝒪_X)` of global functions is a finite `A`-algebra.  This is the
degree-zero case of [Stacks, Tag 08AS].

The proof uses no higher cohomology.  By the dévissage of [Stacks, Tag 07US] it suffices to treat
an extension of two coherent modules, where left exactness of `Γ` and the Noetherian hypothesis
conclude, and a module `i_*𝓘` for a quasi-coherent sheaf of ideals `𝓘` on a reduced closed
subspace `i : Z ⟶ X`.  There `Γ(X, i_*𝓘) = Γ(Z, 𝓘) ⊆ Γ(Z, 𝒪_Z)`, and Chow's lemma for algebraic
spaces, [Stacks, Tag 089J], gives a proper surjective `π : Y ⟶ Z` from a scheme `Y`; because `Z`
is reduced and `π` surjective, pulling back functions along `π` embeds `Γ(Z, 𝒪_Z)` into
`Γ(Y, 𝒪_Y)`, which is a finite `A`-module because `Y` is a proper scheme over `Spec A`
([Stacks, Tag 02O6] in degree zero).  That reduced case is
`AlgebraicGeometry.Space.module_finite_globalFunctions_of_isProper`.

## Main definitions

* `AlgebraicGeometry.Space.sectionsOverBase`: global sections of `𝒪_X`-modules as `A`-modules.
* `AlgebraicGeometry.Space.sectionsOverBasePushforwardIso`: global sections of a direct image are
  global sections, as `A`-modules.

## Main results

* `AlgebraicGeometry.Space.globalSectionsRingHomSite_comp_baseRingHom`: the ring map of global
  sections along a morphism of algebraic spaces over `Spec A` is `A`-linear.
* `AlgebraicGeometry.Space.moduleFinite_sectionsOverBase_of_isProper`: `Γ(X, 𝓕)` is a finite
  `A`-module for coherent `𝓕` on a proper `X`.
* `AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper`: `Γ(X, 𝒪_X)` is a finite
  `A`-module.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- Global sections of `𝒪_X`-modules, read as `A`-modules. -/
abbrev sectionsOverBase : Modules.{u, u} B (Spec (.of A)) hA X hX ⥤ ModuleCat.{u + 1} A :=
  globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O) ⋙
    ModuleCat.restrictScalars (baseRingHom A B hA X hX)

/-- Global sections over the base are left exact. -/
instance : PreservesFiniteLimits (sectionsOverBase A B hA X hX) := by
  have := preservesFiniteLimits_globalSectionsFunctor_ringUniverse
    (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  infer_instance

/-- A global section of the structure module is a global function. -/
def unitSectionsToGlobalFunctions :
    (sectionsOverBase A B hA X hX).obj (SheafOfModules.unit _) →
      globalFunctions' B (Spec (.of A)) hA X :=
  fun s => ⟨s.1, s.2⟩

/-- The `A`-action on global sections of the structure module is multiplication by constants. -/
theorem unitSectionsToGlobalFunctions_smul (a : A)
    (s : (sectionsOverBase A B hA X hX).obj (SheafOfModules.unit _)) :
    unitSectionsToGlobalFunctions A B hA X hX (a • s) =
      baseToGlobalFunctions A B hA X a * unitSectionsToGlobalFunctions A B hA X hX s := rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- Pullback along a morphism of the site over `Spec A` is compatible with the structure maps. -/
theorem Γ_map_algebraMap_siteObj {T T' : BigFppfOver B (Spec (.of A)) hA} (g : T' ⟶ T) (a : A) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of A)) hA).map g).op).hom
      (@algebraMap A _ _ _ (siteObjSectionsAlgebra A T) a) =
        @algebraMap A _ _ _ (siteObjSectionsAlgebra A T') a := by
  have hw : B.inclusion.map g.left ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom := by
    simpa only [← Functor.map_comp] using congrArg B.inclusion.map (Over.w g)
  change ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T.hom).appTop ≫
      (B.inclusion.map g.left).appTop).hom a =
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T'.hom).appTop).hom a
  rw [← Scheme.Hom.comp_appTop, hw]

/-- The value of a scalar at an étale chart is its image under the chart's structure map. -/
theorem baseRingHom_val_apply (X : AlgebraicSpaces B (Spec (.of A)) hA) (a : A)
    (U : SmallEtale B (Spec (.of A)) hA X.1) :
    (baseRingHom A B hA X.1 X.2 a).1 (op U) =
      @algebraMap A _ _ _
        (siteObjSectionsAlgebra A ((SmallEtale.toOver B (Spec (.of A)) hA X.1).obj U)) a :=
  rfl

/-- **The ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` along a morphism of algebraic spaces over `Spec A` is
`A`-linear.**  Both sides are compared on the base change of an étale atlas of `Y` along each
étale chart of `X`, where the chart-diagram formula computes the left side. -/
theorem globalSectionsRingHomSite_comp_baseRingHom {X Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ Y) :
    (globalSectionsRingHomSite B (Spec (.of A)) hA f).comp (baseRingHom A B hA Y.1 Y.2) =
      baseRingHom A B hA X.1 X.2 := by
  ext a : 1
  apply Subtype.ext
  funext U
  obtain ⟨V, q, hqsurj, hqet⟩ := Y.2.exists_atlas
  have hrep := hqet.1
  have hpb := hrep.isPullback' (U.unop.1.hom ≫ f.hom)
  have hsnd_et := hqet.2 _ _ _ hpb
  set g := U.unop.1.hom ≫ f.hom
  let PC : SmallEtale B (Spec (.of A)) hA X.1 :=
    chartFromEtaleHom B (Spec (.of A)) hA X (hrep.pullback g)
      (yoneda.map (hrep.snd g) ≫ U.unop.1.hom)
      (chart_preimage_etale B (Spec (.of A)) hA X U.unop.1.hom U.unop.2 (hrep.snd g) hsnd_et)
  let d : ChartDiagram B (Spec (.of A)) hA X.1 Y.1 f.hom :=
    ⟨PC, ⟨CostructuredArrow.mk q, hqet⟩, hrep.fst' g, by
      change (yoneda.map (hrep.snd g) ≫ U.unop.1.hom) ≫ f.hom = yoneda.map (hrep.fst' g) ≫ q
      rw [Category.assoc]
      exact hpb.w.symm⟩
  let ι : PC ⟶ U.unop := ObjectProperty.homMk (CostructuredArrow.homMk (hrep.snd g) rfl)
  have hL : (((globalSectionsRingHomSite B (Spec (.of A)) hA f).comp
      (baseRingHom A B hA Y.1 Y.2)) a).1 (op PC) = (baseRingHom A B hA X.1 X.2 a).1 (op PC) := by
    rw [RingHom.comp_apply, globalSectionsRingHomSite_val_chartDiagram B (Spec (.of A)) hA f
      (baseRingHom A B hA Y.1 Y.2 a) d]
    exact Γ_map_algebraMap_siteObj A (hrep.fst' g) a
  have compat : ∀ x : RingCat.sectionsSubring (structureRingSheaf B (Spec (.of A)) hA X).obj,
      x.1 (op PC) = (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (hrep.snd g)).op).hom (x.1 U) := fun x => (x.2 ι.op).symm
  exact gamma_injective_of_etale_surjection B (Spec (.of A)) hA (hrep.snd g)
    (hqsurj.2 _ _ _ hpb) hsnd_et ((compat _).symm.trans (hL.trans (compat _)))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- Global sections over the base of a direct image are global sections over the base. -/
def sectionsOverBasePushforwardIso {X Y : AlgebraicSpaces B (Spec (.of A)) hA} (f : X ⟶ Y)
    (N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    (sectionsOverBase A B hA Y.1 Y.2).obj ((modulePushforward B (Spec (.of A)) hA f).obj N) ≅
      (sectionsOverBase A B hA X.1 X.2).obj N :=
  (ModuleCat.restrictScalars (baseRingHom A B hA Y.1 Y.2)).mapIso
      ((globalSectionsPushforwardIsoSite B (Spec (.of A)) hA f).app N) ≪≫
    (ModuleCat.restrictScalarsComp'App (baseRingHom A B hA Y.1 Y.2)
      (globalSectionsRingHomSite B (Spec (.of A)) hA f) (baseRingHom A B hA X.1 X.2)
      (globalSectionsRingHomSite_comp_baseRingHom A f).symm _).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- The base is étale-locally Noetherian when `A` is. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_base [IsNoetherianRing A] :
    HasEtaleLocalProperty B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA))))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  refine ⟨Over.mk (𝟙 (B.obj hA)), 𝟙 _, ?_, ?_, ?_⟩
  · rw [← CategoryTheory.Functor.map_id, presheaf_yoneda_map_iff B _ hA
      (P := @Surjective) inferInstance, CategoryTheory.Functor.map_id]
    infer_instance
  · rw [← CategoryTheory.Functor.map_id, presheaf_yoneda_map_iff B _ hA
      (P := @Etale) inferInstance, CategoryTheory.Functor.map_id]
    infer_instance
  · change IsLocallyNoetherian (Spec (.of A))
    infer_instance

/-- An algebraic space proper over a Noetherian affine base is Noetherian. -/
theorem isNoetherian_of_isProper_toBase [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1)) :
    IsNoetherian B (Spec (.of A)) hA B.contains_terminal X.1 :=
  ⟨isQuasiCompactSpace_of_isQuasiCompact_toBase B _ hA _ hX.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B _ hA B.contains_terminal _
      X.2 (isAffineSpace_yoneda B _ hA _ (inferInstanceAs (IsAffine (Spec (.of A)))))
      (isQuasiSeparated_of_isSeparated B _ hA hX.1),
    isLocallyNoetherian_of_isLocallyOfFiniteType B _ hA X.2 (isAlgebraicSpace_yoneda B _ hA _) _
      hX.2.1.1 (hasEtaleLocalProperty_isLocallyNoetherian_base A)⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- Global sections over the base carry monomorphisms to injections. -/
theorem sectionsOverBase_map_injective_of_mono {X : AlgebraicSpaces B (Spec (.of A)) hA}
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (f : M ⟶ N) [Mono f] :
    Function.Injective ((sectionsOverBase A B hA X.1 X.2).map f) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The global sections of the structure module are the global functions, as `A`-modules. -/
def unitSectionsLinearEquivGlobalFunctions (X : AlgebraicSpaces B (Spec (.of A)) hA) :
    (sectionsOverBase A B hA X.1 X.2).obj (SheafOfModules.unit _) ≃ₗ[A]
      globalFunctions B (Spec (.of A)) hA X.1 where
  toFun := unitSectionsToGlobalFunctions A B hA X.1 X.2
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a s := by
    rw [unitSectionsToGlobalFunctions_smul, RingHom.id_apply, Algebra.smul_def]
    rfl

/-- The global sections of the structure module of a reduced algebraic space proper over a
Noetherian ring `A` form a finite `A`-module. -/
theorem moduleFinite_sectionsOverBase_unit_of_isReduced [IsNoetherianRing A]
    (Z : AlgebraicSpaces B (Spec (.of A)) hA)
    (hZp : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from Z.1))
    (hred : HasEtaleLocalProperty B (Spec (.of A)) hA Z.1 (fun T : Scheme.{u} => IsReduced T)) :
    Module.Finite A ((sectionsOverBase A B hA Z.1 Z.2).obj (SheafOfModules.unit _)) :=
  have := module_finite_globalFunctions_of_isProper B A hA Z _ hZp hred
  Module.Finite.equiv (unitSectionsLinearEquivGlobalFunctions A Z).symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- Properness of a closed subspace of a proper algebraic space. -/
theorem isProper_toBase_closedSubfunctorSpace {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B (Spec (.of A)) hA Z) :
    IsProper B (Spec (.of A)) hA
      ((isTerminal_yoneda_obj_base B _ hA).from (closedSubfunctorSpace B _ hA hZ).1) := by
  have h := isProper_comp B _ hA hZ.1 X.2 (isAlgebraicSpace_yoneda B _ hA _) Z.ι _
    (isProper_of_isClosedImmersion B _ hA hZ.1 X.2 _ hZ.2) hX
  rwa [show Z.ι ≫ (isTerminal_yoneda_obj_base B _ hA).from X.1 =
    (isTerminal_yoneda_obj_base B _ hA).from (closedSubfunctorSpace B _ hA hZ).1 from
      (isTerminal_yoneda_obj_base B _ hA).hom_ext _ _] at h

omit [CommRing A] in
/-- The middle term of a left exact sequence of `A`-modules over a Noetherian ring is finite when
the outer ones are. -/
theorem _root_.Module.Finite.of_exact_of_finite {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module A M₁]
    [Module A M₂] [Module A M₃] [Module.Finite A M₁] [Module.Finite A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.Finite A M₂ := by
  have := isNoetherian_of_isNoetherianRing_of_finite A M₁
  have := isNoetherian_of_isNoetherianRing_of_finite A M₃
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker g (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq, ← Submodule.map_comap_eq_of_le h]
  exact (IsNoetherian.noetherian _).map f

omit [CommRing A] in
/-- A module injecting into a finite module over a Noetherian ring is finite. -/
theorem _root_.Module.Finite.of_injective_of_isNoetherianRing {A : Type*} [CommRing A]
    [IsNoetherianRing A] {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (hN : Module.Finite A N) (f : M →ₗ[A] N) (hf : Function.Injective f) : Module.Finite A M :=
  have := isNoetherian_of_isNoetherianRing_of_finite A N
  Module.Finite.of_injective f hf

/-- **Finiteness of global sections of coherent modules on a proper algebraic space.** -/
theorem moduleFinite_sectionsOverBase_of_isProper [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1))
    (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hM : IsCoherent B _ hA X.1 X.2 M) :
    Module.Finite A ((sectionsOverBase A B hA X.1 X.2).obj M) := by
  refine property_of_ideal_pushforward_and_extensions B _ hA X
    (isNoetherian_of_isProper_toBase A X hX)
    (fun M => Module.Finite A ((sectionsOverBase A B hA X.1 X.2).obj M)) (Or.inr fun N hN => ?_)
    (fun E hE _ _ _ h₁ h₃ => ?_) (fun Z hZ hred I => ?_) M hM
  · have : Subsingleton ((sectionsOverBase A B hA X.1 X.2).obj N) :=
      ModuleCat.subsingleton_of_isZero ((sectionsOverBase A B hA X.1 X.2).map_isZero hN)
    infer_instance
  · have hex := hE.exact.map_of_mono_of_preservesKernel (sectionsOverBase A B hA X.1 X.2)
      hE.mono_f inferInstance
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
    exact Module.Finite.of_exact_of_finite ((sectionsOverBase A B hA X.1 X.2).map E.f).hom
      ((sectionsOverBase A B hA X.1 X.2).map E.g).hom hex
  · let Zs := closedSubfunctorSpace B _ hA hZ
    have hI : Module.Finite A ((sectionsOverBase A B hA Zs.1 Zs.2).obj I.1.toSheafOfModules) :=
      Module.Finite.of_injective_of_isNoetherianRing
        (moduleFinite_sectionsOverBase_unit_of_isReduced A Zs
          (isProper_toBase_closedSubfunctorSpace A hX hZ) hred.1)
        ((sectionsOverBase A B hA Zs.1 Zs.2).map I.1.ι).hom
        (@sectionsOverBase_map_injective_of_mono A _ B hA Zs _ _ I.1.ι
          (inferInstanceAs (Mono I.1.ι)))
    exact Module.Finite.equiv
      (sectionsOverBasePushforwardIso A (closedSubfunctorι B _ hA hZ) _).symm.toLinearEquiv

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}

/-- **The global functions of an algebraic space proper over a Noetherian ring `A` form a finite
`A`-module.** -/
theorem moduleFinite_globalFunctions_of_isProper [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (hX : IsProper B (Spec (.of A)) hA ((isTerminal_yoneda_obj_base B _ hA).from X.1)) :
    Module.Finite A (globalFunctions B (Spec (.of A)) hA X.1) := by
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨(isNoetherian_of_isProper_toBase A X hX).2.2⟩
  have := moduleFinite_sectionsOverBase_of_isProper A X hX _
    (isCoherent_structureSheaf B (Spec (.of A)) hA X.1 X.2)
  exact Module.Finite.equiv (unitSectionsLinearEquivGlobalFunctions A X)

end AlgebraicGeometry.Space
