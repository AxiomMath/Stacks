module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionCoefficientsDirectSums
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveTopIso
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# The top-degree trace on a curve over a separably closed field

Let `Ω` be a separably closed field, `p : C ⟶ Spec Ω` proper with fibres of dimension `≤ 1`,
`N ≥ 1`, `Λ = ℤ/N` and `c ∈ Ext²(Λ_C, Λ_C)`. The top-degree trace `ν : U ⟶ T` of `c`
(`Stacks.EtaleCohomology.TopTrace.trace`, `T(M) = R²p_*(p⁻¹M)`) is a natural transformation of
functors on sheaves of `Λ`-modules on `Spec Ω`, which form the category of `Λ`-modules. Both
functors are right exact and commute with direct sums: `U` because it is the forgetful functor,
`T` because `R³p_*` vanishes on torsion sheaves (Tag 095U) and `R²p_*` commutes with direct sums
for `p` quasi-compact and quasi-separated. Hence, as in the Eilenberg–Watts theorem, `ν` is an
isomorphism everywhere as soon as it is one at the constant sheaf `Λ`, or at any sheaf
isomorphic to it (`Stacks.EtaleCohomology.TopTrace.isIso_trace_of_isSeparator`): every sheaf has
a presentation by direct sums of copies of it.

This is the fibrewise step of the construction of the top-degree trace of a relative curve in the
proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main results

* `Stacks.EtaleCohomology.TopTrace.isIso_app_of_isSeparator`: a natural transformation of right
  exact functors commuting with direct sums is invertible as soon as it is at a separator.
* `Stacks.EtaleCohomology.TopTrace.topSheafIsoRightDerived`: `T ≅ R²p_* ∘ U ∘ p⁻¹`, naturally.
* `Stacks.EtaleCohomology.TopTrace.isSeparator_constantModuleSheaf`: the constant sheaf `Λ` is a
  separator of sheaves of `Λ`-modules on `Spec Ω`.
* `Stacks.EtaleCohomology.TopTrace.isIso_trace_of_isSeparator`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard
  isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Sheaf.monoidalCategory
  isMonoidal_W_etaleModules

/-! ### A natural transformation invertible at a separator -/

section Separator

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  {F₁ F₂ : 𝒜 ⥤ ℬ} (η : F₁ ⟶ F₂)

omit [Abelian 𝒜] [Abelian ℬ] in
/-- On a direct sum of copies of `G` preserved by both functors, `η` is the direct sum of copies
of `η_G`. -/
theorem app_sigma_eq {G : 𝒜} {I : Type*} [HasCoproduct (fun _ : I => G)]
    [HasCoproductsOfShape I ℬ]
    [PreservesColimit (Discrete.functor fun _ : I => G) F₁]
    [PreservesColimit (Discrete.functor fun _ : I => G) F₂] :
    η.app (∐ fun _ : I => G) =
      inv (sigmaComparison F₁ fun _ : I => G) ≫ Limits.Sigma.map (fun _ => η.app G) ≫
        sigmaComparison F₂ fun _ : I => G := by
  rw [← cancel_epi (sigmaComparison F₁ fun _ : I => G), IsIso.hom_inv_id_assoc]
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  simp only [ι_comp_sigmaComparison_assoc, Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison]
  exact η.naturality _

omit [Abelian 𝒜] [Abelian ℬ] in
/-- **`η` is invertible on a direct sum of copies of `G`** preserved by both functors, when it is
invertible at `G`. -/
theorem isIso_app_sigma {G : 𝒜} {I : Type*} [HasCoproduct (fun _ : I => G)]
    [HasCoproductsOfShape I ℬ]
    [PreservesColimit (Discrete.functor fun _ : I => G) F₁]
    [PreservesColimit (Discrete.functor fun _ : I => G) F₂] [IsIso (η.app G)] :
    IsIso (η.app (∐ fun _ : I => G)) := by
  rw [app_sigma_eq η]
  infer_instance

/-- **Eilenberg–Watts for a separator.** Let `η : F₁ ⟶ F₂` be a natural transformation of
functors of abelian categories, `G` a separator of the source such that both functors commute
with the direct sums `⨁_{G ⟶ A} G`, `F₁` preserving epimorphisms and `F₂` right exact. If `η` is
invertible at `G`, it is invertible everywhere: every `A` has a presentation
`⨁ G ⟶ ⨁ G ⟶ A ⟶ 0` (`CategoryTheory.isSeparator_iff_epi`), and
`Stacks.EtaleCohomology.TopTrace.isIso_of_presentation` applies. -/
theorem isIso_app_of_isSeparator {G : 𝒜} (hG : IsSeparator G)
    [∀ A : 𝒜, HasCoproduct fun _ : G ⟶ A => G] [∀ A : 𝒜, HasCoproductsOfShape (G ⟶ A) ℬ]
    [∀ A : 𝒜, PreservesColimit (Discrete.functor fun _ : G ⟶ A => G) F₁]
    [∀ A : 𝒜, PreservesColimit (Discrete.functor fun _ : G ⟶ A => G) F₂]
    [F₁.PreservesZeroMorphisms] [F₂.PreservesZeroMorphisms]
    (h₁ : ∀ {X Y : 𝒜} (f : X ⟶ Y), Epi f → Epi (F₁.map f))
    (h₂ : ∀ {S : ShortComplex 𝒜}, S.ShortExact → (S.map F₂).Exact ∧ Epi (F₂.map S.g))
    [IsIso (η.app G)] (A : 𝒜) : IsIso (η.app A) := by
  have he := (isSeparator_iff_epi G).1 hG
  let b := Limits.Sigma.desc fun f : G ⟶ A => f
  let e := Limits.Sigma.desc fun f : G ⟶ kernel b => f
  have := he A
  have := he (kernel b)
  have hS : ∀ {X Y : 𝒜} (f : X ⟶ Y) [Epi f],
      (ShortComplex.mk (kernel.ι f) f (kernel.condition _)).ShortExact := fun f _ =>
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk (kernel.ι f) f (kernel.condition _)) (kernelIsKernel f))
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  have : Epi (F₂.map b) := (h₂ (hS b)).2
  have : Epi (F₂.map e) := (h₂ (hS e)).2
  have : Epi (F₁.map b) := h₁ b inferInstance
  have := isIso_app_sigma η (G := G) (I := G ⟶ A)
  have := isIso_app_sigma η (G := G) (I := G ⟶ kernel b)
  exact isIso_of_presentation η e (kernel.ι b) b (kernel.condition _) (h₂ (hS b)).1

omit [Abelian 𝒜] in
/-- A separator is a separator up to isomorphism. -/
theorem isSeparator_of_iso {G G' : 𝒜} (i : G ≅ G') (hG : IsSeparator G') : IsSeparator G := by
  rw [isSeparator_def] at hG ⊢
  intro X Y f g h
  exact hG f g fun k => by simpa using congrArg (i.inv ≫ ·) (h (i.hom ≫ k))

end Separator

/-! ### `T = R²p_* ∘ U ∘ p⁻¹` commutes with direct sums -/

section RightDerived

variable {N : ℕ} {B Y : Scheme.{u}} (p : Y ⟶ B)

/-- `H⁰(Rp_*(F[0]⟦2⟧)) ≅ R²p_* F`, naturally in the abelian sheaf `F`. -/
def singleShiftDirectImageIso :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        shiftFunctor _ ((2 : ℕ) : ℤ) ⋙ etaleAbelianDerivedDirectImage.{u, 0} p ⋙
          DerivedCategory.homologyFunctor _ 0 ≅
      (etaleAbelianDirectImage.{u, 0} p).rightDerived 2 :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((DerivedCategory.singleFunctors _).shiftIso ((2 : ℕ) : ℤ) (-2) 0
      (by norm_num)) _ ≪≫
    Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived
      (etaleAbelianDirectImage.{u, 0} p) (etaleAbelianDerivedDirectImage.{u, 0} p)
      (etaleAbelianDerivedDirectImageUnit.{u, 0} p)
      (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K) (-2) 0 2 (by norm_num)

/-- **`T(G) = H⁰(Rp_*(p⁻¹G[2])) ≅ R²p_*(p⁻¹G)`**, naturally in the sheaf of `ℤ/N`-modules `G`. -/
def topSheafIsoRightDerived :
    topSheaf p (N := N) ≅ etaleModuleInverseImage.{u, 0} (ZMod N) p ⋙
      etaleModuleUnderlyingAbelian Y (ZMod N) ⋙ (etaleAbelianDirectImage.{u, 0} p).rightDerived 2 :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (singleShiftDirectImageIso p))

/-- **`T` commutes with direct sums** for `p` quasi-compact and quasi-separated: so do `p⁻¹`, a
left adjoint, the forgetful functor, and `R²p_*`. -/
theorem topSheaf_preservesColimitsOfShape [QuasiCompact p] [QuasiSeparated p] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (topSheaf p (N := N)) := by
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleAbelianDirectImage.{u, 0} p).rightDerived 2) :=
    preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{0} p 2 I
  have : PreservesColimitsOfShape (Discrete I) (etaleModuleInverseImage.{u, 0} (ZMod N) p) :=
    (etaleModuleInverseImageAdj.{u, 0} (ZMod N) p).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) (etaleModuleUnderlyingAbelian Y (ZMod N)) :=
    etaleModuleForget_preservesColimitsOfShape (ZMod N) Y _
  exact preservesColimitsOfShape_of_natIso (topSheafIsoRightDerived p).symm

end RightDerived

/-! ### Over a separably closed field -/

section SepClosed

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (N : ℕ)

/-- **The constant sheaf `Λ` is a separator** of sheaves of `Λ`-modules on `Spec Ω`, `Ω`
separably closed: morphisms out of it are the sections over the final object, and taking those
sections is an equivalence. -/
theorem isSeparator_constantModuleSheaf :
    IsSeparator (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod N)
      (Spec (.of Ω)).smallEtaleTopology) := by
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} (ZMod N)) :=
    hasLimitsOfSizeShrink.{0, u, u + 1, u + 1} _
  have := isEquivalence_sheafSections_final_of_isSepClosed Ω (ModuleCat.{u + 1} (ZMod N))
  let adj := constantSheafAdj (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))
    (isTerminal_etale_mk_id Ω).some
  let E := (sheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))).obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))))
  rw [isSeparator_def]
  intro X Y f g h
  apply E.map_injective
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let s : ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)) ⟶ E.obj X :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton (ZMod N) _ x).comp
      (ULift.moduleEquiv (R := ZMod N) (M := ZMod N)).toLinearMap)
  have hs := congrArg (fun k => (adj.homEquiv _ _ k).hom (ULift.up 1))
    (h ((adj.homEquiv _ _).symm s))
  simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at hs
  simp only [Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.flip_obj_map,
    ObjectProperty.ι_map, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, ULift.moduleEquiv_apply,
    LinearMap.toSpanSingleton_apply, one_smul, s] at hs
  exact hs

variable {Ω N}

omit [IsSepClosed Ω] in
/-- **The top-degree trace on a curve over a separably closed field is invertible once it is at a
separator**, e.g. at a sheaf isomorphic to the constant sheaf `Λ`. -/
theorem isIso_trace_of_isSeparator {C : Scheme.{u}} (p : C ⟶ Spec (.of Ω)) [IsProper p]
    (hfib : ∀ b, topologicalKrullDim (p.fiber b) ≤ 1) (hN : N ≠ 0)
    (c : Ext.{u + 1} (MonoidalCategory.tensorUnit (EtaleModules.{u, 0} (ZMod N) C))
      (MonoidalCategory.tensorUnit _) 2)
    (G : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω))) (hG : IsSeparator G)
    [IsIso ((trace p c).app G)] (M : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω))) :
    IsIso ((trace p c).app M) := by
  have hC : ∀ A : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω)),
      HasColimitsOfShape (Discrete (G ⟶ A)) (EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω))) :=
    fun A => by
      have : HasColimitsOfShape (Discrete (G ⟶ A)) (ModuleCat.{u + 1} (ZMod N)) :=
        (ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod N)).has_colimits_of_shape _
      exact Sheaf.instHasColimitsOfShape
  have : ∀ A : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω)), HasCoproduct fun _ : G ⟶ A => G :=
    fun A => (hC A).has_colimit _
  have : ∀ A : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω)),
      HasCoproductsOfShape (G ⟶ A)
        (Sheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    fun A =>
      AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtaleTopology.{u, 0} (Spec (.of Ω)) _
  have := topSheaf_preservesZeroMorphisms p (N := N)
  have : ∀ A : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω)),
      PreservesColimit (Discrete.functor fun _ : G ⟶ A => G) (topSheaf p (N := N)) :=
    fun A => (topSheaf_preservesColimitsOfShape p (G ⟶ A)).preservesColimit
  have : ∀ A : EtaleModules.{u, 0} (ZMod N) (Spec (.of Ω)),
      PreservesColimit (Discrete.functor fun _ : G ⟶ A => G)
        (etaleModuleUnderlyingAbelian (Spec (.of Ω)) (ZMod N)) :=
    fun A => (etaleModuleForget_preservesColimitsOfShape (ZMod N) (Spec (.of Ω))
      (Discrete (G ⟶ A))).preservesColimit
  exact isIso_app_of_isSeparator (trace p c) hG (fun f _ => inferInstance)
    (fun hS => topSheaf_exact p hfib hN hS) M

end SepClosed

end Stacks.EtaleCohomology.TopTrace
