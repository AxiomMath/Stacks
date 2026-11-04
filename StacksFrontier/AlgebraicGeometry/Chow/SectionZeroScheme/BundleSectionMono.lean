module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.MulTMono
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# The hyperplane section of a nowhere vanishing section is a regular section

Let `E` be a finite locally free module on a scheme `X`, `π : P = 𝐏(E) ⟶ X` its projective bundle
with tautological quotient `π^*E ⟶ 𝒪_P(1)`, and `s ∈ Γ(X, E)` a global section which vanishes
nowhere. The image `t ∈ Γ(P, 𝒪_P(1))` of `π^*s` is a regular section: multiplication by `t`,
`𝒪_P ⟶ 𝒪_P(1)`, is a monomorphism.

On the stalk at a point `ξ`, write `t = f e` over an affine neighbourhood on which `e` trivializes
`𝒪_P(1)`. The ideal of `Z(t)` there lies in `(f)`. At a point of `Z(t)` the ideal it cuts out in
`𝒪_{P,ξ}` contains a nonzerodivisor
(`Stacks.Chow.SectionZeroScheme.exists_nonZeroDivisor_mem_stalkIdeal_bundleSectionOf`, which is
where the non-vanishing of `s` is used); off `Z(t)` that ideal is the unit ideal. Either way the
germ of `f` is a nonzerodivisor, so multiplication by the germ of `t` is injective.

## Main results

* `Stacks.Chow.SectionZeroScheme.injective_smul_germ_bundleSectionOf`: multiplication by the germ
  of `t` on the local rings of `P` is injective.
* `Stacks.Chow.SectionZeroScheme.mono_of_injective_smul_germ`: a map `𝒪 ⟶ L` to an
  `𝒪`-module is a monomorphism when multiplication by the germs of the image of `1` is injective.
* `Stacks.Chow.SectionZeroScheme.mono_pullbackUnitIso_inv_comp_tautologicalMap`: **the map
  `𝒪_P ≅ π^*𝒪_X ⟶ π^*E ⟶ 𝒪_P(1)` given by a nowhere vanishing `s : 𝒪_X ⟶ E` is a
  monomorphism.**

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open scoped nonZeroDivisors

universe u

namespace Stacks.Chow.SectionZeroScheme

/-- **The map `𝒪 ⟶ L` of a global section is a monomorphism when multiplication by its germs is
injective**: on stalks the map is multiplication by the germ of the section. -/
theorem mono_unitHomEquiv_symm_of_injective_smul_germ {P : Scheme.{u}} (L : P.Modules)
    (σ : L.sections)
    (h : ∀ ξ : P, Function.Injective fun c : P.presheaf.stalk ξ =>
      c • L.presheaf.germ ⊤ ξ trivial (σ.val (op ⊤))) :
    Mono (L.unitHomEquiv.symm σ) := by
  refine (SheafOfModules.toSheaf P.ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 fun ξ => ?_)
  rw [AddCommGrpCat.mono_iff_injective]
  let O : P.Modules := SheafOfModules.unit P.ringCatSheaf
  have hlin : ∀ (U : P.Opens) (a : Γ(P, U)),
      ((L.unitHomEquiv.symm σ).val.app (op U)).hom a =
        (a • L.presheaf.map (homOfLE le_top).op (σ.val (op ⊤) : Γ(L, ⊤)) : Γ(L, U)) :=
    fun U a => congrArg (fun m : Γ(L, U) => a • m) (σ.property (homOfLE (le_top : U ≤ ⊤)).op).symm
  have key : ∀ (U : P.Opens) (hξ : ξ ∈ U) (a : Γ(P, U)),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat ξ).map
          ((SheafOfModules.toSheaf P.ringCatSheaf).map (L.unitHomEquiv.symm σ)).hom
          (O.presheaf.germ U ξ hξ a) =
        P.presheaf.germ U ξ hξ a • L.presheaf.germ ⊤ ξ trivial (σ.val (op ⊤)) := by
    intro U hξ a
    have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply U ξ hξ
      ((SheafOfModules.toSheaf P.ringCatSheaf).map (L.unitHomEquiv.symm σ)).hom a
    refine h1.trans ?_
    show L.presheaf.germ U ξ hξ (((L.unitHomEquiv.symm σ).val.app (op U)).hom a) = _
    rw [hlin, Scheme.Modules.germ_smul L hξ]
    exact congrArg (fun m => P.presheaf.germ U ξ hξ a • m)
      (L.presheaf.germ_res_apply (homOfLE le_top) ξ hξ (σ.val (op ⊤) : Γ(L, ⊤)))
  intro y₁ y₂ hy
  obtain ⟨U₁, hξ₁, a₁, rfl⟩ := O.presheaf.exists_germ_eq y₁
  obtain ⟨U₂, hξ₂, a₂, rfl⟩ := O.presheaf.exists_germ_eq y₂
  have hy' := h ξ ((key U₁ hξ₁ a₁).symm.trans (hy.trans (key U₂ hξ₂ a₂)))
  obtain ⟨W, hξW, i₁, i₂, hW⟩ := P.presheaf.germ_eq ξ hξ₁ hξ₂ a₁ a₂ hy'
  rw [← O.presheaf.germ_res_apply i₁ ξ hξW a₁, ← O.presheaf.germ_res_apply i₂ ξ hξW a₂]
  exact congrArg (O.presheaf.germ W ξ hξW) hW

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **Multiplication by the germ of the hyperplane section of a nowhere vanishing section is
injective** on the local rings of the projective bundle. -/
theorem injective_smul_germ_bundleSectionOf (s : Γ(E, ⊤))
    (hs : ∀ x : X, x ∉ (zeroSchemeOfSection X E s).supportSet)
    (ξ : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme) :
    Function.Injective
      fun c : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.stalk ξ =>
        c • (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ ⊤ ξ trivial
          (bundleSectionOf E hqc s) := by
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.sheaf.obj
      (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.ringCatSheaf.property
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) :=
    Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E hqc
  obtain ⟨W, hξW, e, hbij⟩ := Stacks.Divisors.exists_bijective_smul_of_isInvertible
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) hLinv ξ
  obtain ⟨U, hU, hξU, hUW⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hξW
  replace hUW : U ≤ W := hUW
  obtain ⟨f, hf⟩ := (hbij U hUW).2
    ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.map (homOfLE le_top).op
      (bundleSectionOf E hqc s))
  replace hf : f • (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.map
        (homOfLE hUW).op e =
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.map (homOfLE le_top).op
        (bundleSectionOf E hqc s) := hf
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := isFiniteLocallyFreeOfRank_one_of_isInvertible
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc))
  -- the ideal of `Z(t)` over `U` lies in `(f)`
  have hideal : (Stacks.Divisors.zeroScheme _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
        (bundleSectionOf E hqc s)).ideal ⟨U, hU⟩ ≤ Ideal.span {f} := by
    rw [← zeroSchemeOfSection_eq_zeroScheme, zeroSchemeOfSection_ideal, Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [← hf, φ.map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
  -- the germ of `f` is a nonzerodivisor
  have hgfnzd : ∀ x : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.stalk ξ,
      x * ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.germ U ξ hξU).hom f =
        0 → x = 0 := by
    by_cases hsupp : ξ ∈ (Stacks.Divisors.zeroScheme _
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) (bundleSectionOf E hqc s)).support
    · obtain ⟨a₀, ha₀, haI₀⟩ := exists_nonZeroDivisor_mem_stalkIdeal_bundleSectionOf E hqc s ξ
        hsupp (hs _)
      let a : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.stalk ξ := a₀
      have ha : a ∈ nonZeroDivisors
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.stalk ξ) := ha₀
      have haI : a ∈ Stacks.AlgebraicGeometry.stalkIdeal
          (Stacks.Divisors.zeroScheme _ (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
            (bundleSectionOf E hqc s)) ξ hsupp := haI₀
      rw [Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ _ ξ hsupp hU hξU] at haI
      have hspan := Ideal.map_mono
        (f := ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.germ U ξ hξU).hom)
        hideal haI
      rw [Ideal.map_span, Set.image_singleton] at hspan
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hspan
      intro x hx
      refine (mem_nonZeroDivisors_iff.mp ha).1 x ?_
      rw [← hc, mul_assoc, mul_comm _ x, hx, mul_zero]
    · -- off `Z(t)` the ideal over `U` contains a function invertible at `ξ`
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hξU,
        Scheme.mem_zeroLocus_iff] at hsupp
      push Not at hsupp
      obtain ⟨g, hg, hξg⟩ := hsupp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hideal hg)
      have hunit : IsUnit
          (((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.germ U ξ hξU).hom
            (c * f)) :=
        (Scheme.mem_basicOpen _ (c * f) ξ hξU).mp hξg
      rw [map_mul] at hunit
      exact fun x hx => (isUnit_of_mul_isUnit_right hunit).mul_left_eq_zero.mp hx
  -- the germ of `e` is a stalk basis, and the germ of `t` is the germ of `f` times it
  have he : Stacks.Divisors.IsStalkBasis (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)
      ξ ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ W ξ hξW e) :=
    Stacks.Divisors.isStalkBasis_germ_of_bijective_smul e hbij ξ hξW
  have hgerm : (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ ⊤ ξ trivial
        (bundleSectionOf E hqc s) =
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.presheaf.germ U ξ hξU).hom f •
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ W ξ hξW e := by
    rw [← (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ_res_apply
        (homOfLE le_top) ξ hξU (bundleSectionOf E hqc s), ← hf,
      Scheme.Modules.germ_smul (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc) hξU,
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ_res_apply
        (homOfLE hUW) ξ hξU e]
  intro x y hxy
  replace hxy : x • (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ ⊤ ξ
        trivial (bundleSectionOf E hqc s) =
      y • (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).presheaf.germ ⊤ ξ trivial
        (bundleSectionOf E hqc s) := hxy
  rw [hgerm, smul_smul, smul_smul] at hxy
  exact sub_eq_zero.mp (hgfnzd _ ((sub_mul _ _ _).trans (sub_eq_zero.mpr (he.1 hxy))))

omit [E.IsQuasicoherent] in
/-- **A split section vanishes nowhere.** If `σ : 𝒪_X ⟶ E` has a retraction `τ : E ⟶ 𝒪_X`, then
on every affine open `τ` is a linear form taking the value `1` at `σ(1)`, so the ideal of the
zero scheme of `σ(1)` is the unit ideal. -/
theorem notMem_supportSet_zeroSchemeOfSection_of_comp_eq_id
    (σ : Scheme.unitModule X ⟶ E) (τ : E ⟶ Scheme.unitModule X) (hστ : σ ≫ τ = 𝟙 _) (x : X) :
    x ∉ (zeroSchemeOfSection X E (σ.app ⊤ (1 : Γ(X, ⊤)))).supportSet := by
  obtain ⟨U, hU, hxU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let φ : Γ(E, U) →ₗ[Γ(X, U)] Γ(X, U) := (τ.val.app (op U)).hom
  have hmem : (1 : Γ(X, U)) ∈
      (zeroSchemeOfSection X E (σ.app ⊤ (1 : Γ(X, ⊤)))).ideal ⟨U, hU⟩ := by
    rw [zeroSchemeOfSection_ideal]
    refine Ideal.subset_span ⟨φ, ?_⟩
    have h1 : φ (E.presheaf.map (homOfLE le_top).op (σ.app ⊤ (1 : Γ(X, ⊤)))) =
        X.presheaf.map (homOfLE le_top).op
          ((τ.val.app (op ⊤)).hom (σ.app ⊤ (1 : Γ(X, ⊤)))) :=
      PresheafOfModules.naturality_apply τ.val (homOfLE le_top).op _
    have h2 : (τ.val.app (op ⊤)).hom (σ.app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) :=
      congrArg (fun k : Scheme.unitModule X ⟶ Scheme.unitModule X =>
        (k.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) hστ
    rw [h1, h2, map_one]
  intro hx
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU,
    Scheme.mem_zeroLocus_iff] at hx
  exact hx 1 hmem (by rw [Scheme.basicOpen_one]; exact hxU)

/-- **The map `𝒪_P ≅ π^*𝒪_X ⟶ π^*E ⟶ 𝒪_P(1)` of a split section `σ : 𝒪_X ⟶ E` is a
monomorphism**: it is the map of the hyperplane section of `σ(1)`, which vanishes nowhere. -/
theorem mono_pullbackUnitIso_inv_comp_tautologicalMap
    (σ : Scheme.unitModule X ⟶ E) (τ : E ⟶ Scheme.unitModule X) (hστ : σ ≫ τ = 𝟙 _) :
    Mono ((Scheme.Modules.pullbackUnitIso
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv ≫
      (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).map σ ≫
        Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc) := by
  set g := (Scheme.Modules.pullbackUnitIso
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv ≫
      (Scheme.Modules.pullback (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).map σ ≫
        Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc with hg
  have hg' : g = (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).unitHomEquiv.symm
      ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).unitHomEquiv g) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [hg']
  refine mono_unitHomEquiv_symm_of_injective_smul_germ _ _ fun ξ => ?_
  -- the global section of `g` is the hyperplane section of `σ(1)`
  have hval : ((Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc).unitHomEquiv g).val
      (op ⊤) = bundleSectionOf E hqc (σ.app ⊤ (1 : Γ(X, ⊤))) := by
    show ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).app ⊤
      (((Scheme.Modules.pullback
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).map σ).app ⊤
        ((Scheme.Modules.pullbackUnitIso
          (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app ⊤
            (1 : Γ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme, ⊤))))) = _
    have hu : (Scheme.Modules.pullbackUnitIso
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase).inv.app ⊤
          (1 : Γ((relativeProj (schemeSheafGradedAlgebra E hqc)).scheme, ⊤)) =
          pullbackGlobalSections (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase
            (Scheme.unitModule X) (1 : Γ(X, ⊤)) := by
      have h1 := AlgebraicGeometry.SectionsEqualizer.pullbackUnitIso_unit
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase (1 : Γ(X, ⊤))
      rw [map_one] at h1
      rw [← h1]
      exact (ConcreteCategory.congr_hom (congrArg (fun t => Scheme.Modules.Hom.app t ⊤)
        (Iso.hom_inv_id (Scheme.Modules.pullbackUnitIso
          (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase))) _).trans
        (CategoryTheory.id_apply _)
    rw [hu]
    exact congrArg ((Stacks.ProjectiveBundleSplitting.tautologicalMap E hqc).app ⊤)
      (pullbackGlobalSections_natural (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase σ
        (show Γ(Scheme.unitModule X, ⊤) from (1 : Γ(X, ⊤)))).symm
  rw [hval]
  exact injective_smul_germ_bundleSectionOf E hqc _
    (notMem_supportSet_zeroSchemeOfSection_of_comp_eq_id E σ τ hστ) ξ

end Stacks.Chow.SectionZeroScheme

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- **The hyperplane section of a split section is regular**, on the projective bundle
`π : 𝐏(F) ⟶ X` of `Stacks.RelativeProj.projectiveBundle`: for `σ : 𝒪_X ⟶ F` with a retraction,
the map `π^*𝒪_X ⟶ π^*F ⟶ 𝒪_{𝐏(F)}(1)` is a monomorphism. The tautological surjection of this
presentation is the inverse image of the one of `Stacks.RelativeProj.symGradedBundle` along the
comparison of the two presentations, where this is
`Stacks.Chow.SectionZeroScheme.mono_pullbackUnitIso_inv_comp_tautologicalMap`. -/
theorem mono_pullback_map_comp_tautologicalDatumUniv
    (σ : Scheme.unitModule X ⟶ F) (τ : F ⟶ Scheme.unitModule X) (hστ : σ ≫ τ = 𝟙 _) :
    Mono ((Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
      tautologicalDatumUniv F) := by
  have hqc := isQuasicoherentPieces_of_isQuasicoherent F
  -- monomorphism on the other presentation
  have h₀ := Stacks.Chow.SectionZeroScheme.mono_pullbackUnitIso_inv_comp_tautologicalMap F hqc
    σ τ hστ
  have h₁ : Mono ((Scheme.Modules.pullback (symGradedBundle F).toBase).map σ ≫
      Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc) := by
    have e : (Scheme.Modules.pullback (symGradedBundle F).toBase).map σ ≫
        Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc =
        (Scheme.Modules.pullbackUnitIso (symGradedBundle F).toBase).hom ≫
          ((Scheme.Modules.pullbackUnitIso (symGradedBundle F).toBase).inv ≫
            (Scheme.Modules.pullback (symGradedBundle F).toBase).map σ ≫
              Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc) := by
      rw [Iso.hom_inv_id_assoc]
    rw [e]
    exact mono_comp _ _
  -- transport along the comparison of the presentations
  have h₂ : Mono ((Scheme.Modules.pullback (bundlePresentationIso F).inv).map
      ((Scheme.Modules.pullback (symGradedBundle F).toBase).map σ ≫
        Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc)) :=
    Functor.map_mono _ _
  have e : (Scheme.Modules.pullback (projectiveBundleToBase X F)).map σ ≫
      tautologicalDatumUniv F =
      ((Scheme.Modules.pullbackCongr (bundlePresentationIso_inv_comp_toBase F)).inv.app _ ≫
        (Scheme.Modules.pullbackComp (bundlePresentationIso F).inv
          (symGradedBundle F).toBase).inv.app _) ≫
        (Scheme.Modules.pullback (bundlePresentationIso F).inv).map
          ((Scheme.Modules.pullback (symGradedBundle F).toBase).map σ ≫
            Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc) := by
    simp only [tautologicalDatumUniv, Functor.map_comp, Category.assoc]
    rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc]
    rfl
  rw [e]
  exact mono_comp _ _

end Stacks.RelativeProj

end
