module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GenericPointSupport
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LipmanLocalStepTransport
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The zeros of a morphism from an invertible module to the structure sheaf of a curve

Let `X` be a proper integral scheme of dimension at most one over a field `k`, let `𝒩` be an
invertible `𝒪_X`-module and let `θ : 𝒩 ⟶ 𝒪_X` be nonzero. Then `θ` is injective, its cokernel
`𝒬` is supported on finitely many closed points, and

  `χ(X, 𝒬) = dim_k H⁰(X, 𝒬) = -deg(𝒩)`.

The support of `𝒬` is the set of points `x` at which the image of `𝒩_x` in `𝒪_{X,x}` is a proper
ideal, i.e. where `θ` vanishes; since each of these points contributes at least one to
`dim_k H⁰(X, 𝒬)`, there are at most `-deg(𝒩)` of them.

## Main results

* `AlgebraicGeometry.encard_supp_le_finrank_cohomologyOverField_zero`: a coherent module with
  zero-dimensional support on a proper scheme over a field has at most `dim_k H⁰` points in its
  support.
* `AlgebraicGeometry.eq_zero_of_mapFun_genericPoint_eq_zero`: a morphism into `𝒪_X` on an
  integral scheme is determined by its stalk at the generic point.
* `AlgebraicGeometry.mono_of_ne_zero_toUnit`: a nonzero morphism from an invertible module to
  `𝒪_X` on an integral scheme is a monomorphism.
* `AlgebraicGeometry.eulerCharacteristic_cokernel_toUnit`: `χ(X, 𝒬) = -deg(𝒩)`.
* `AlgebraicGeometry.encard_supp_cokernel_toUnit_le`: the number of points of the support of `𝒬`
  is at most `-deg(𝒩)`.
* `AlgebraicGeometry.mem_supp_cokernel_iff_not_surjective`: a point lies in the support of `𝒬`
  exactly when the stalk of `θ` there is not surjective.

## Implementation notes

`H⁰(X, 𝒬)` is identified `k`-linearly with `Γ(X, 𝒬)` by
`AlgebraicGeometry.cohomologyOverFieldZeroIsoSections`, where `k` acts through the structure
morphism. Each stalk `𝒬_x` is a `k`-vector space through `k ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}`, the germ
maps are `k`-linear for these structures, and together they are a bijection onto the product of
the stalks along the support (`AlgebraicGeometry.bijective_suppGermHom_of_supp_le_zero`). A
nonzero finite-dimensional vector space has positive dimension, which gives the count.

## References

* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ModuleStalk

universe u

namespace AlgebraicGeometry

/-! ### Counting the points of a zero-dimensional support -/

section Count

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- A surjection from a finite-dimensional space onto a finite product of nontrivial modules
has at least as many dimensions as there are factors. -/
private theorem card_le_finrank_of_surjective_pi {K G ι : Type*} [Field K] [AddCommGroup G]
    [Module K G] [FiniteDimensional K G] [Fintype ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, Nontrivial (M i)]
    (L : G →ₗ[K] ∀ i, M i) (hL : Function.Surjective L) :
    Fintype.card ι ≤ Module.finrank K G := by
  classical
  have : ∀ i, Module.Finite K (M i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp L) fun m => by
      obtain ⟨s, hs⟩ := hL (Pi.single i m)
      exact ⟨s, by simp [hs]⟩
  calc Fintype.card ι = ∑ _ : ι, 1 := by simp
    _ ≤ ∑ i, Module.finrank K (M i) := Finset.sum_le_sum fun i _ => Module.finrank_pos
    _ = Module.finrank K (∀ i, M i) := (Module.finrank_pi_fintype K).symm
    _ ≤ Module.finrank K G := LinearMap.finrank_le_finrank_of_surjective hL

/-- **A coherent module with zero-dimensional support on a proper scheme over a field has at
most `dim_k H⁰` points in its support.** -/
theorem encard_supp_le_finrank_cohomologyOverField_zero (F : X.Modules) [F.IsCoherent]
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) :
    (_root_.SheafOfModules.supp F).encard ≤
      (Module.finrank k (cohomologyOverField k f F 0) : ℕ∞) := by
  classical
  let : Fintype ↥(_root_.SheafOfModules.supp F) :=
    (finite_supp_of_supp_le_zero k f F hF).fintype
  let hmod : ∀ x : ↥(_root_.SheafOfModules.supp F),
      Module k (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) :=
    fun x => Module.compHom _ (baseToStalk f x.1)
  let G := (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)
  let e := cohomologyOverFieldZeroIsoSections k f F
  have : FiniteDimensional k (cohomologyOverField k f F 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 0
  have : FiniteDimensional k G := LinearEquiv.finiteDimensional e.toLinearEquiv
  let L : G →ₗ[k] ∀ x : ↥(_root_.SheafOfModules.supp F),
      TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1 :=
    { toFun := fun s x => (F.presheaf.Γgerm x.1).hom s
      map_add' := fun s t => funext fun x => map_add _ s t
      map_smul' := fun c s => funext fun x =>
        (Γgerm_smul F x.1 (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c)
          (show Γ(F, ⊤) from s) :) }
  have : ∀ x : ↥(_root_.SheafOfModules.supp F),
      Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x.1) := fun x => by
    obtain ⟨a, ha⟩ := x.2
    exact ⟨⟨a, 0, ha⟩⟩
  have hcard :=
    card_le_finrank_of_surjective_pi L (bijective_suppGermHom_of_supp_le_zero k f F hF).2
  rw [← e.toLinearEquiv.finrank_eq] at hcard
  rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
  exact_mod_cast hcard

end Count

/-! ### Morphisms into the structure sheaf of an integral scheme -/

section Integral

variable {X : Scheme.{u}}

/-- An invertible module on a locally Noetherian scheme is coherent, at the invertibility
spelling `SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2`. -/
theorem isCoherent_of_isInvertible' [IsLocallyNoetherian X] (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] : N.IsCoherent :=
  have hN' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN'
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X N

/-- An invertible module on a locally Noetherian scheme is quasi-coherent. -/
private theorem isQuasicoherent_of_isInvertible' [IsLocallyNoetherian X] (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] : N.IsQuasicoherent :=
  have := isCoherent_of_isInvertible' N
  isQuasicoherent_of_isCoherent N

/-- The stalk map of the zero morphism is zero. -/
private theorem mapFun_zero_apply {M N : X.Modules} (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : mapFun (0 : M ⟶ N) x m = 0 := by
  obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ m
  rw [mapFun_germ]
  simp

/-- **A morphism into `𝒪_X` on an integral scheme is determined by its stalk at the generic
point.** -/
theorem eq_zero_of_mapFun_genericPoint_eq_zero [IsIntegral X] {N : X.Modules}
    (φ : N ⟶ Stacks.UnitStalk.unitModule X)
    (h : ∀ a, mapFun φ (genericPoint X) a = 0) : φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext t
  by_cases hV : Nonempty V.unop
  · have hη : genericPoint X ∈ V.unop :=
      ((genericPoint_spec X).mem_open_set_iff V.unop.isOpen).mpr (by simpa using hV)
    have h1 := (mapFun_germ φ (genericPoint X) V.unop hη t).symm.trans
      (h ((N.presheaf.germ V.unop (genericPoint X) hη).hom t))
    have h2 := (Stacks.UnitStalk.unitStalkLinearEquiv X (genericPoint X)).injective
      (((Stacks.UnitStalk.unitStalkLinearEquiv_germ X (genericPoint X) V.unop hη _).trans
        h1).trans (map_zero _).symm)
    exact germ_injective_of_isIntegral X (genericPoint X) hη (h2.trans (map_zero _).symm)
  · let underlying : TopCat.Sheaf Ab.{u} X.toTopCat :=
      ⟨Scheme.Modules.presheaf (Stacks.UnitStalk.unitModule X),
        Scheme.Modules.isSheaf (Stacks.UnitStalk.unitModule X)⟩
    exact TopCat.Presheaf.section_ext underlying V.unop (φ.val.app V t) 0 fun x hx =>
      False.elim (hV ⟨⟨x, hx⟩⟩)

/-- **A nonzero morphism from an invertible module to `𝒪_X` on an integral locally Noetherian
scheme is a monomorphism.** -/
theorem mono_of_ne_zero_toUnit [IsIntegral X] [IsLocallyNoetherian X] {N : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (φ : N ⟶ Stacks.UnitStalk.unitModule X) (hφ : φ ≠ 0) : Mono φ := by
  refine Preadditive.mono_of_kernel_zero ?_
  have hK : genericPoint X ∉ SheafOfModules.supp (kernel φ) := by
    rintro ⟨a₀, ha⟩
    let a : TopCat.Presheaf.stalk (C := Ab.{u}) (kernel φ).presheaf (genericPoint X) := a₀
    let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have hinj : Function.Injective (mapFun (kernel.ι φ) (genericPoint X)) :=
      TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (f := (kernel.ι φ).mapPresheaf)
        (fun U => Scheme.Modules.injective_app_of_mono (kernel.ι φ) U) (genericPoint X)
    have hb : mapFun (kernel.ι φ) (genericPoint X) a ≠ 0 := fun h0 =>
      ha (hinj (h0.trans (map_zero _).symm))
    have hrank :=
      Stacks.AlgebraicGeometry.ReflexiveModules.finrank_stalk_genericPoint_eq_one_of_isInvertible N
    have hspan := (finrank_eq_one_iff_of_nonzero' _ hb).mp hrank
    refine hφ (eq_zero_of_mapFun_genericPoint_eq_zero φ fun c => ?_)
    obtain ⟨r, hr⟩ := hspan c
    rw [← hr, mapFun_smul, ← mapFun_comp, kernel.condition, mapFun_zero_apply, smul_zero]
  have := isQuasicoherent_of_isInvertible' N
  have : (kernel φ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel φ
  exact (isZero_of_mono_of_genericPoint_notMem (kernel.ι φ) hK).eq_of_src _ _

end Integral

/-! ### The cokernel of a nonzero morphism into the structure sheaf -/

section Cokernel

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) {N : X.Modules}
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
  (θ : N ⟶ Stacks.UnitStalk.unitModule X)

omit [IsIntegral X] in
include f in
/-- **The cokernel of a morphism into `𝒪_X` is coherent.** -/
theorem isCoherent_cokernel_toUnit : (cokernel θ).IsCoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isQuasicoherent_of_isInvertible' N
  have : (cokernel θ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel θ
  @Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent X _
    (Stacks.UnitStalk.unitModule X) (cokernel θ) _
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (cokernel.π θ)
    coequalizer.π_epi

include f hdim in
/-- **The cokernel of a nonzero morphism from an invertible module to `𝒪_X` has
zero-dimensional support.** -/
theorem topologicalKrullDim_supp_cokernel_toUnit_le_zero (hθ : θ ≠ 0) :
    topologicalKrullDim (SheafOfModules.supp (cokernel θ)) ≤ 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have := isCoherent_cokernel_toUnit k f θ
  have hU : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  have hne : ∃ a, mapFun (θ ≫ 𝟙 _) (genericPoint X) a ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hθ (eq_zero_of_mapFun_genericPoint_eq_zero θ fun a => by
      simpa using hall a)
  exact topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim _
    (@_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ ‹_›)
    (genericPoint_notMem_supp_cokernel_of_genericPoint_mem_supp θ (𝟙 _) hne)

include hdim in
/-- **`χ(X, 𝒬) = -deg(𝒩)`** for the cokernel `𝒬` of a nonzero morphism `𝒩 ⟶ 𝒪_X`. -/
@[sga "7 X 1.4" "special case"]
theorem eulerCharacteristic_cokernel_toUnit (hθ : θ ≠ 0) :
    @eulerCharacteristic k _ X f _ (cokernel θ) (isCoherent_cokernel_toUnit k f θ) =
      -invertibleCurveDegree k f hdim N := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := mono_of_ne_zero_toUnit θ hθ
  have := isCoherent_cokernel_toUnit k f θ
  have : N.IsCoherent := isCoherent_of_isInvertible' N
  have : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hS : (ShortComplex.mk θ (cokernel.π θ) (cokernel.condition θ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel θ) inferInstance inferInstance
  have hadd := eulerCharacteristic_add_of_shortExact k f hS
  have hdeg := invertibleCurveDegree_eq_eulerCharacteristic_sub k f hdim N
  change eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) =
    eulerCharacteristic k f N + eulerCharacteristic k f (cokernel θ) at hadd
  linarith

include hdim in
/-- **The support of the cokernel of a nonzero morphism `𝒩 ⟶ 𝒪_X` has at most `-deg(𝒩)`
points**, on a proper integral scheme of dimension at most one over a field. In particular
`-deg(𝒩)` is nonnegative. -/
theorem encard_supp_cokernel_toUnit_le (hθ : θ ≠ 0) :
    0 ≤ -invertibleCurveDegree k f hdim N ∧
      (SheafOfModules.supp (cokernel θ)).encard ≤
        ((-invertibleCurveDegree k f hdim N).toNat : ℕ∞) := by
  have := isCoherent_cokernel_toUnit k f θ
  have hsupp := topologicalKrullDim_supp_cokernel_toUnit_le_zero k f hdim θ hθ
  have hχ := eulerCharacteristic_cokernel_toUnit k f hdim θ hθ
  rw [eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero k f (cokernel θ)
    hsupp] at hχ
  refine ⟨hχ ▸ Int.natCast_nonneg _, ?_⟩
  rw [← hχ, Int.toNat_natCast]
  exact encard_supp_le_finrank_cohomologyOverField_zero k f (cokernel θ) hsupp

end Cokernel

/-! ### The support of the cokernel -/

section Support

variable {X : Scheme.{u}} {N : X.Modules} (θ : N ⟶ Stacks.UnitStalk.unitModule X)

/-- **A point lies in the support of the cokernel of `θ : 𝒩 ⟶ 𝒪_X` exactly when the stalk of `θ`
there is not surjective.** -/
theorem mem_supp_cokernel_iff_not_surjective (x : X) :
    x ∈ SheafOfModules.supp (cokernel θ) ↔ ¬ Function.Surjective (mapFun θ x) := by
  constructor
  · rintro ⟨a, ha⟩ hsurj
    obtain ⟨b, rfl⟩ := @Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi _
      X.ringCatSheaf _ _ (cokernel.π θ)
      ⟨fun g₁ g₂ hg => (inferInstance : Epi (cokernel.π θ)).left_cancellation g₁ g₂ hg⟩ x a
    obtain ⟨c, rfl⟩ := hsurj b
    apply ha
    show mapFun (cokernel.π θ) x (mapFun θ x c) = 0
    rw [← mapFun_comp, cokernel.condition, mapFun_zero_apply]
  · refine not_imp_comm.mpr fun hx => ?_
    let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
    have hzero : IsZero (T.obj (cokernel θ)) := by
      refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      by_contra hab
      exact hx ⟨a - b, sub_ne_zero.mpr hab⟩
    exact (ModuleCat.epi_iff_surjective (T.map θ)).mp <| Abelian.epi_of_cokernel_π_eq_zero _ <|
      (IsZero.of_iso hzero (PreservesCokernel.iso T θ).symm).eq_of_tgt _ _

end Support

end AlgebraicGeometry

end
