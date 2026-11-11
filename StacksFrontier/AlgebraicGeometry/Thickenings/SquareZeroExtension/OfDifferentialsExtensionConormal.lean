module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.OfDifferentialsExtension
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Vanishing
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Uniqueness
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.ConormalDifferentialIdealSections
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafKer
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift

/-!
# The conormal sequence of the thickening attached to an extension of the differentials

Let `f : X ⟶ S` be a morphism of schemes and `0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0` a short exact sequence
of `𝒪_X`-modules with `𝓜` quasi-coherent, and let `X ⊂ X'` be the first-order thickening over `S`
with structure sheaf `𝒪_{X'} = 𝒪_X ×_{Ω_{X/S}} 𝓔`
(`Stacks.Thickenings.DifferentialsExtension.differentialsThickening`).

The second projection `(a, e) ↦ e` is a derivation of `𝒪_{X'}` over `S` with values in `𝓔`, so it
induces `i^*Ω_{X'/S} ⟶ 𝓔`; it lies over the identity of `Ω_{X/S}` because `p e = d a`. Hence the
conormal sequence `𝒞_{X/X'} ⟶ i^*Ω_{X'/S} ⟶ Ω_{X/S}` maps to the given sequence, and when `X` is
smooth over `S` its class in `Ext¹(Ω_{X/S}, 𝒞_{X/X'})`, pushed forward along the induced map
`𝒞_{X/X'} ⟶ 𝓜`, is the class of the given extension.

## Main definitions

* `Stacks.Thickenings.DifferentialsExtension.thickeningDifferentialsMap`: `i^*Ω_{X'/S} ⟶ 𝓔`.
* `Stacks.Thickenings.DifferentialsExtension.thickeningConormalHom`: `𝒞_{X/X'} ⟶ 𝓜`.
* `Stacks.Thickenings.DifferentialsExtension.conormalShortComplexHom`: the morphism from the
  conormal sequence to the given extension.

## Main results

* `Stacks.Thickenings.DifferentialsExtension.isIso_thickeningConormalHom`: `𝒞_{X/X'} ⟶ 𝓜` is an
  isomorphism.
* `Stacks.Thickenings.DifferentialsExtension.extClass_comp_thickeningConormalHom`: the class of the
  conormal sequence, pushed forward to `𝓜`, is the class of the extension.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules Stacks.AlgebraicGeometry.RegularIdealSheaf
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings.DifferentialsExtension

attribute [local instance] Stacks.Smooth.moduleMulOpposite
attribute [local instance] moduleSectionsScheme

/-- The identification of the sheaves of differentials of two equal morphisms carries one universal
derivation to the other. -/
theorem eqToHom_relativeDifferentials_app_d {X S : Scheme.{u}} {g g' : X ⟶ S} (h : g = g')
    (V : X.Opens) (t : Γ(X, V)) :
    ((eqToHom (congrArg Scheme.Hom.relativeDifferentials h)).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation g).d t) =
      (Scheme.Hom.universalRelativeDerivation g').d t := by
  subst h
  rfl

variable {X S : Scheme.{u}} {f : X ⟶ S} {M E : X.Modules} {j : M ⟶ E}
  {p : E ⟶ Scheme.Hom.relativeDifferentials f} [M.IsQuasicoherent] (w : j ≫ p = 0)
  (hT : (ShortComplex.mk j p w).ShortExact)

/-- **The second projection `(a, e) ↦ e`**, a derivation of `𝒪_{X'}` with values in `i_*𝓔`
along the comorphism of `X' ⟶ S`: the Leibniz rule is the multiplication of `𝒪_X ⋉ 𝓔`, and the
sections `(f^♯ r, 0)` coming from `S` have vanishing second component. -/
def thickeningDerivationAlong :
    PresheafOfModulesOfCommRing.Derivation
      ((Scheme.Modules.pushforward (differentialsThickeningι w hT)).obj E).val
      (differentialsThickeningToBase w hT).c where
  d {V} :=
    { toFun := fun s => (show (extensionSheaf f p).presheaf.obj V from s).1.snd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  d_mul {V} a b := extensionSheaf_mul_snd (f := f) (p := p) V a b
  d_map g s := extensionSheaf_map_snd (f := f) (p := p) g s
  d_app _ := rfl

/-- `thickeningDerivationAlong`, as a derivation relative to `X'` over `S` in the sense of the
sheaf of relative differentials. -/
def thickeningDerivation :
    SheafOfModules.SheafDerivation (inverseImageStructureMap (differentialsThickeningToBase w hT))
      ((Scheme.Modules.pushforward (differentialsThickeningι w hT)).obj E) :=
  Stacks.AlgebraicGeometry.AffineDifferentialsIso.toStructuralDerivation _ _
    (thickeningDerivationAlong w hT)

/-- The morphism `Ω_{X'/S} ⟶ i_*𝓔` induced by the second projection. -/
def thickeningDifferentialsHom :
    Scheme.Hom.relativeDifferentials (differentialsThickeningToBase w hT) ⟶
      (Scheme.Modules.pushforward (differentialsThickeningι w hT)).obj E :=
  (SheafOfModules.universalDerivation_isUniversal _).desc (thickeningDerivation w hT)

/-- `Ω_{X'/S} ⟶ i_*𝓔` sends `d (a, e)` to `e`. -/
theorem thickeningDifferentialsHom_d (V : (differentialsThickening w hT).Opens)
    (s : Γ(differentialsThickening w hT, V)) :
    ((thickeningDifferentialsHom w hT).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (differentialsThickeningToBase w hT)).d s) =
      (show (extensionSheaf f p).presheaf.obj (op V) from s).1.snd :=
  congrArg (fun D : SheafOfModules.SheafDerivation _ _ => D.d s)
    ((SheafOfModules.universalDerivation_isUniversal _).postcomp_desc (thickeningDerivation w hT))

/-- **The morphism `i^*Ω_{X'/S} ⟶ 𝓔`** induced by the second projection. -/
def thickeningDifferentialsMap :
    (Scheme.Modules.pullback (differentialsThickeningι w hT)).obj
        (Scheme.Hom.relativeDifferentials (differentialsThickeningToBase w hT)) ⟶ E :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (differentialsThickeningι w hT)).homEquiv _ _).symm
    (thickeningDifferentialsHom w hT)

/-- The identification `Ω_{X/S} = Ω_{X/S}` of the two spellings `X ⟶ X' ⟶ S` and `f` of the
structure morphism. -/
abbrev thickeningDifferentialsEq :
    Scheme.Hom.relativeDifferentials
        (differentialsThickeningι w hT ≫ differentialsThickeningToBase w hT) ⟶
      Scheme.Hom.relativeDifferentials f :=
  eqToHom (congrArg Scheme.Hom.relativeDifferentials (differentialsThickeningι_comp_toBase w hT))

/-- **`i^*Ω_{X'/S} ⟶ 𝓔 ⟶ Ω_{X/S}` is the canonical map**: on `d (a, e)` both give `p e = d a`. -/
theorem thickeningDifferentialsMap_comp :
    thickeningDifferentialsMap w hT ≫ p =
      Scheme.Hom.relativeDifferentialsMap (differentialsThickeningι w hT)
        (differentialsThickeningToBase w hT)
        (differentialsThickeningι w hT ≫ differentialsThickeningToBase w hT) (𝟙 S)
        (by simp) ≫ thickeningDifferentialsEq w hT := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (differentialsThickeningι w hT)).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    thickeningDifferentialsMap, Equiv.apply_symm_apply]
  refine Stacks.ConormalSequenceRight.relativeDifferentials_hom_ext _ _ _ fun V t => ?_
  refine (congrArg (fun y => (p.val.app (op V)).hom y)
    (thickeningDifferentialsHom_d w hT V t)).trans ?_
  refine Eq.trans ?_ (congrArg (fun y => ((thickeningDifferentialsEq w hT).val.app (op V)).hom y)
    (Scheme.Hom.relativeDifferentialsMap_app_d (f := differentialsThickeningι w hT)
    (p := differentialsThickeningToBase w hT)
    (p' := differentialsThickeningι w hT ≫ differentialsThickeningToBase w hT) (𝟙 S) (by simp)
    V t)).symm
  refine Eq.trans ?_ (eqToHom_relativeDifferentials_app_d
    (differentialsThickeningι_comp_toBase w hT) _ _).symm
  exact ((show (extensionSheaf f p).presheaf.obj (op V) from t).2).symm

/-- **The map `𝒞_{X/X'} ⟶ 𝓜`** induced on kernels by `i^*Ω_{X'/S} ⟶ 𝓔`. -/
def thickeningConormalHom :
    (conormalSheaf (differentialsThickeningι w hT) : X.Modules) ⟶ M :=
  haveI := hT.mono_f
  hT.exact.lift (Stacks.ConormalSequenceRight.conormalDifferential _ _ ≫
      thickeningDifferentialsMap w hT)
    ((Category.assoc _ _ _).trans ((congrArg (fun g =>
      Stacks.ConormalSequenceRight.conormalDifferential (differentialsThickeningι w hT)
        (differentialsThickeningToBase w hT) ≫ g) (thickeningDifferentialsMap_comp w hT)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun g => g ≫ thickeningDifferentialsEq w hT)
        (Stacks.ConormalSequenceRight.conormalDifferential_comp_relativeDifferentialsMap _ _)).trans
        zero_comp))))

/-- `𝒞_{X/X'} ⟶ 𝓜 ⟶ 𝓔` is `𝒞_{X/X'} ⟶ i^*Ω_{X'/S} ⟶ 𝓔`. -/
theorem thickeningConormalHom_comp :
    thickeningConormalHom w hT ≫ j =
      Stacks.ConormalSequenceRight.conormalDifferential _ _ ≫ thickeningDifferentialsMap w hT :=
  haveI := hT.mono_f
  hT.exact.lift_f _ _

/-- **`𝒞_{X/X'} ⟶ 𝓜` is an isomorphism.** On a section `(0, e)` of the ideal of `X` in `X'`, the
composite `ℐ ⟶ i_*𝒞_{X/X'} ⟶ i_*𝓜 ⟶ i_*𝓔` is `e`; and the sections of the ideal are exactly the
`(0, j m)`. -/
theorem isIso_thickeningConormalHom : IsIso (thickeningConormalHom w hT) := by
  refine Stacks.ConormalSequenceRight.isIso_of_bijective_idealConormalQuotientMap_comp
    (differentialsThickeningι w hT) (differentialsThickeningι_ker_sq w hT) _ fun V => ?_
  let incl : (Stacks.ClosedImmersion.idealSheaf
      (differentialsThickeningι w hT).toLRSHom.toShHom).val.obj (op V) →
        Γ(differentialsThickening w hT, V) := fun y =>
    ((Stacks.ClosedImmersion.idealSheafι
      (differentialsThickeningι w hT).toLRSHom.toShHom).val.app (op V)).hom y
  have key : ∀ y, (j.val.app (op V)).hom
      (((Stacks.ConormalSequenceRight.idealConormalQuotientMap (differentialsThickeningι w hT) ≫
        (modulePushforward (differentialsThickeningι w hT).toLRSHom.toShHom).map
          (thickeningConormalHom w hT)).val.app (op V)).hom y) =
      (show (extensionSheaf f p).presheaf.obj (op V) from incl y).1.snd := by
    intro y
    have h1 := congrArg (fun φ => ((Stacks.ConormalSequenceRight.idealConormalQuotientMap
      (differentialsThickeningι w hT) ≫ (modulePushforward
        (differentialsThickeningι w hT).toLRSHom.toShHom).map φ).val.app (op V)).hom y)
      (thickeningConormalHom_comp w hT)
    refine Eq.trans ?_ (h1.trans ?_)
    · rfl
    · refine
        (ConormalSequenceRight.idealConormalQuotientMap_comp_map_conormalDifferential_comp_val_app
          _ _ _ V y).trans ?_
      rw [thickeningDifferentialsMap, Equiv.apply_symm_apply]
      exact thickeningDifferentialsHom_d w hT V _
  have hfst : ∀ y, (show (extensionSheaf f p).presheaf.obj (op V) from incl y).1.fst = 0 :=
    fun y => by
      have hy : incl y ∈ RingHom.ker ((differentialsThickeningι w hT).app V).hom := by
        rw [← Stacks.ClosedImmersion.range_idealSheafι_val_app]
        exact ⟨y, rfl⟩
      exact RingHom.mem_ker.mp hy
  have hj : Function.Injective (j.val.app (op V)).hom := fun m m' h => by
    obtain ⟨_, -, huniq⟩ := existsUnique_app_eq_of_shortExact hT (op V) ((j.val.app (op V)).hom m)
      (congrArg (fun φ : M ⟶ _ => (φ.val.app (op V)).hom m) w)
    exact (huniq m rfl).trans (huniq m' h.symm).symm
  refine ⟨fun y y' h => Stacks.ClosedImmersion.injective_idealSheafι_val_app _ V
    (Subtype.ext (TrivSqZeroExt.ext ((hfst y).trans (hfst y').symm)
      ((key y).symm.trans ((congrArg _ h).trans (key y'))))), fun m => ?_⟩
  obtain ⟨y, hy⟩ : (extensionKernelInclusion w (op V) m : Γ(differentialsThickening w hT, V)) ∈
      LinearMap.range ((Stacks.ClosedImmersion.idealSheafι
        (differentialsThickeningι w hT).toLRSHom.toShHom).val.app (op V)).hom := by
    rw [Stacks.ClosedImmersion.range_idealSheafι_val_app]
    exact RingHom.mem_ker.mpr (extensionKernelInclusion_mem_kernel w _ m)
  exact ⟨y, hj ((key y).trans (congrArg (fun z : Γ(differentialsThickening w hT, V) =>
    (show (extensionSheaf f p).presheaf.obj (op V) from z).1.snd) hy))⟩

/-- **The morphism from the conormal sequence of `X ⊂ X'` to the given extension**, the identity
on `Ω_{X/S}`. -/
def conormalShortComplexHom :
    Stacks.ConormalSequenceRight.conormalShortComplex (differentialsThickeningι w hT)
        (differentialsThickeningToBase w hT) ⟶ ShortComplex.mk j p w where
  τ₁ := thickeningConormalHom w hT
  τ₂ := thickeningDifferentialsMap w hT
  τ₃ := thickeningDifferentialsEq w hT
  comm₁₂ := thickeningConormalHom_comp w hT
  comm₂₃ := thickeningDifferentialsMap_comp w hT

/-- **The class of the conormal sequence of `X ⊂ X'`, pushed forward along `𝒞_{X/X'} ⟶ 𝓜`, is the
class of the extension** `0 ⟶ 𝓜 ⟶ 𝓔 ⟶ Ω_{X/S} ⟶ 0`, for `X` smooth over `S`; the two spellings of
`Ω_{X/S}` are identified by `thickeningDifferentialsEq`. -/
theorem extClass_comp_thickeningConormalHom
    (hsm : AlgebraicGeometry.Smooth (differentialsThickeningι w hT ≫
      differentialsThickeningToBase w hT)) :
    (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact _ _ hsm).extClass.comp
        (Abelian.Ext.mk₀ (thickeningConormalHom w hT)) (add_zero 1) =
      (Abelian.Ext.mk₀ (thickeningDifferentialsEq w hT)).comp hT.extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality _ hT (conormalShortComplexHom w hT)

end Stacks.Thickenings.DifferentialsExtension

end
