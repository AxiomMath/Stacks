module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitChartTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingNoetherianAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealInjectionDevissageStep
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealProductPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleSectionsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealQuasicoherent

/-!
# A Noetherian algebraic space with a finite surjection from an affine scheme is affine

Stacks 07VP: let `f : Y ⟶ X` be a finite surjective morphism of algebraic spaces over a scheme
`S`, with `Y` affine and `X` Noetherian.  Then `X` is affine.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace`: the
  higher cohomology of a quasi-coherent module on an affine algebraic space vanishes.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_modulePushforward_of_isPullback`:
  `Hⁿ(X, i_* f'_* 𝓜) = 0` for `n > 0` and `𝓜` quasi-coherent on `Y ×_X Z`, `Y` affine.
* `AlgebraicGeometry.Space.exists_generic_trivialization_le`: a generic trivialization of a
  coherent module of full support by copies of a sheaf of ideals inside a prescribed one.
* `AlgebraicGeometry.Space.exists_mono_pi_modulePushforward`: property (3)(b) of Stacks 07UT for
  `f'_*𝒪_{Z'}`.
* `AlgebraicGeometry.Space.isZero_rightDerived_one_idealPushforward_of_lt`: the step of the
  Noetherian induction.
* `AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective`: **Stacks 07VP.**

## Implementation notes

The source applies Stacks 07UT, whose hypothesis (1) — closure under extensions — is all that
`H¹(X, −) = 0` satisfies.  Here the same argument is run through Stacks 07US with the filtration
of Stacks 07UR and the Noetherian induction
`AlgebraicGeometry.Space.forall_property_idealPushforward_of_step`; at a reduced irreducible `Z`
the comparison of `ℐ` with `𝒢 = f'_*𝒪_{Z'}` is made through a generic trivialization
`ψ : 𝒥^{⊕ r} ⟶ 𝒢` with `𝒥 ⊆ ℐ`, whose cokernel is killed by some `𝒥ᵏ` (Stacks 07UK), so that
`𝒥ᵏ𝒢 = f'_*(f'⁻¹𝒥ᵏ · 𝒪_{Z'})` (Stacks 0GF8) lies in the image of `ψ`.  This replaces the
extension of an inverse by Stacks 07UM and the Artin–Rees step of the source.

The structure sheaf appears in two spellings, `AlgebraicGeometry.Space.structureRingSheaf` and
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, which are definitionally but not reducibly equal;
the statements about inverse-image ideals and base change of charts are in the second spelling,
as Stacks 0GF8 is, and the others in the first.

## References

* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
* [Stacks Project, Tag 0GF7](https://stacks.math.columbia.edu/tag/0GF7)
* [Stacks Project, Tag 0GF8](https://stacks.math.columbia.edu/tag/0GF8)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 0D2V](https://stacks.math.columbia.edu/tag/0D2V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe w v₁ u₁ u

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{u}}

/-- **A morphism of sheaves of modules carries `I · M` into `I · N`.**  A section of `I · M` is
locally a combination of products `a · m`, and a morphism of modules carries such a combination
to the combination of the products `a · φ(m)`. -/
theorem map_mem_idealSmul_top {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (φ : M ⟶ N) (I : IdealSubsheaf O) {Z : Cᵒᵖ} {x : M.val.obj Z}
    (hx : x ∈ (idealSmul I (⊤ : M.Submodule)).obj Z) :
    φ.val.app Z x ∈ (idealSmul I (⊤ : N.Submodule)).obj Z := by
  obtain ⟨T, hT, hmem⟩ := mem_idealSmul_iff.1 hx
  refine mem_idealSmul_of_mem hT fun W g hg => ?_
  rw [← PresheafOfModules.naturality_apply φ.val g.op x]
  have key : ∀ z, z ∈ (presheafIdealSmul I (⊤ : M.Submodule).toSubmodule).obj (op W) →
      φ.val.app (op W) z ∈ (presheafIdealSmul I (⊤ : N.Submodule).toSubmodule).obj (op W) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, m, -, rfl⟩ := hz
      rw [(φ.val.app (op W)).hom.map_smul]
      refine smul_mem_presheafIdealSmul I ha ?_
      rw [Stacks.SheafOfModules.toSubmodule_top]
      trivial
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add z z' _ _ h₁ h₂ =>
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂
    | smul c z _ h₁ =>
      rw [(φ.val.app (op W)).hom.map_smul]
      exact Submodule.smul_mem _ c h₁
  exact key _ (hmem g hg)

/-- A sheaf of ideals lies in its product with the structure sheaf: a section `a` is `a · 1`. -/
theorem le_idealSmul_top (I : IdealSubsheaf O) :
    I ≤ idealSmul I (⊤ : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        O)).Submodule) := by
  intro Z a ha
  have h := smul_mem_idealSmul (N := (⊤ : (SheafOfModules.unit
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).Submodule)) I ha
    (m := (1 : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Z))
    (by rw [Stacks.SheafOfModules.toSubmodule_top]; trivial)
  convert h using 1
  exact (mul_one (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Z from a)).symm

/-- The product of a sheaf of ideals with the structure sheaf is the sheaf of ideals. -/
theorem idealSmul_top_eq (I : IdealSubsheaf O) :
    idealSmul I (⊤ : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)).Submodule) =
        I :=
  le_antisymm (idealSmul_le_left I ⊤) (le_idealSmul_top I)

/-- Over an object on which a sheaf of ideals is everything, so is each of its powers. -/
theorem idealPow_obj_eq_top (I : IdealSubsheaf O) {Z : Cᵒᵖ} (hZ : I.obj Z = ⊤) (n : ℕ) :
    (idealPow I n).obj Z = ⊤ := by
  have h1 : (1 : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj Z) ∈ (idealPow I n).obj Z := by
    refine mem_idealPow_of_mem_pow I n ?_
    rw [show sectionIdeal I Z = ⊤ from hZ, Ideal.top_pow]
    exact Submodule.mem_top
  exact (Ideal.eq_top_iff_one _).2 h1

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cohomology on affine algebraic spaces and along affine morphisms -/

section Cohomology

attribute [local instance 5000] SheafOfModules.instAbelian

/-- Zero objects transfer along an isomorphism of their images under faithful zero-preserving
functors to `AddCommGrpCat`. -/
private theorem isZero_of_isZero_of_iso_forget₂ {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] (G₁ : C₁ ⥤ AddCommGrpCat.{u + 1})
    (G₂ : C₂ ⥤ AddCommGrpCat.{u + 1}) [G₁.PreservesZeroMorphisms] [G₂.Faithful]
    [G₂.PreservesZeroMorphisms] {A : C₁} {B : C₂} (e : G₁.obj A ≅ G₂.obj B) (h : IsZero A) :
    IsZero B :=
  isZero_of_faithful G₂ ((Functor.map_isZero G₁ h).of_iso e.symm)

/-- **The higher cohomology of a quasi-coherent module on an affine algebraic space vanishes.**
The space is isomorphic to the algebraic space of an affine scheme of the site, the isomorphism
is an affine morphism, so Stacks 0D2U moves the cohomology to that scheme, where it vanishes. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace (X : AlgebraicSpaces B S hS)
    (hX : IsAffineSpace B S hS X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) (hi : 0 < i) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  obtain ⟨V, hV, ⟨e⟩⟩ := hX
  let f : X ⟶ _root_.AlgebraicGeometry.schemeSpace V := ObjectProperty.homMk e.hom
  have hf : IsAffineHom B S hS f.hom := isAffineHom_of_isIso e.hom
  have := hasInjectiveResolutions_modules B S hS (_root_.AlgebraicGeometry.schemeSpace V).1
    (_root_.AlgebraicGeometry.schemeSpace V).2
  exact isZero_of_isZero_of_iso_forget₂ (forget₂ _ AddCommGrpCat.{u + 1})
    (forget₂ _ AddCommGrpCat.{u + 1}) (cohomologyIsoOfIsAffineHom B S hS f hf F hF i).symm
    (isZero_rightDerived_globalSectionsFunctor_of_isAffine B S hS V hV _
      (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' f hf hF) i hi)

/-- **Cohomology vanishes on a quasi-coherent module exactly when it vanishes on its direct image
along an affine morphism**, degree by degree: Stacks 0D2U. -/
theorem isZero_rightDerived_iff_of_isAffineHom {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := enoughInjectives_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj F) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).obj
          ((modulePushforward B S hS f).obj F))) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  have e := cohomologyIsoOfIsAffineHom B S hS f hf F hF i
  exact ⟨isZero_of_isZero_of_iso_forget₂ (forget₂ _ AddCommGrpCat.{u + 1})
      (forget₂ _ AddCommGrpCat.{u + 1}) e,
    isZero_of_isZero_of_iso_forget₂ (forget₂ _ AddCommGrpCat.{u + 1})
      (forget₂ _ AddCommGrpCat.{u + 1}) e.symm⟩

/-- **The cohomology of a direct image from the inverse image of a closed subspace under a
finite morphism with affine source vanishes.**  Let `f : Y ⟶ X` be finite with `Y` affine, let
`i : Z ⟶ X` be a closed immersion and `Z' = Y ×_X Z`, with projections `i' : Z' ⟶ Y` and
`f' : Z' ⟶ Z`.  For a quasi-coherent `𝒪_{Z'}`-module `𝓜` and `n > 0`,
`Hⁿ(X, i_* f'_* 𝓜) = 0`.

The three morphisms `i`, `f'` and `i'` are affine, so by Stacks 0D2U this is
`Hⁿ(Y, i'_* 𝓜)`, which vanishes because `Y` is affine. -/
theorem isZero_rightDerived_modulePushforward_modulePushforward_of_isPullback
    {X Y Z Z' : AlgebraicSpaces B S hS} {f : Y ⟶ X} {i : Z ⟶ X} {i' : Z' ⟶ Y} {f' : Z' ⟶ Z}
    (sq : IsPullback i' f' f i) (hf : IsFinite B S hS f.hom)
    (hi : IsClosedImmersion B S hS i.hom) (hY : IsAffineSpace B S hS Y.1)
    (M : Modules.{u, u} B S hS Z'.1 Z'.2) (hM : M.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n).obj
        ((modulePushforward B S hS i).obj ((modulePushforward B S hS f').obj M))) := by
  have hf' : IsFinite B S hS f'.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hi' : IsClosedImmersion B S hS i'.hom := isClosedImmersion_of_isPullback B S hS sq.flip hi
  have hai := isAffineHom_of_isClosedImmersion B S hS i.hom hi
  have hai' := isAffineHom_of_isClosedImmersion B S hS i'.hom hi'
  have haf' := hf'.isAffineHom
  have h0 := isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace B S hS Y hY _
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' i' hai' hM) n hn
  have h1 := (isZero_rightDerived_iff_of_isAffineHom B S hS i' hai' M hM n).2 h0
  have h2 := (isZero_rightDerived_iff_of_isAffineHom B S hS f' haf' M hM n).1 h1
  exact (isZero_rightDerived_iff_of_isAffineHom B S hS i hai _
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom' f' haf' hM) n).1 h2

end Cohomology

/-! ### The unit locus of a meet of sheaves of ideals -/

attribute [local instance] pointTopology in
/-- **A point of the unit loci of two sheaves of ideals lies in the unit locus of their meet**:
the chart witnessing the first can be refined to one over which the second is the whole
structure sheaf too. -/
theorem mem_idealUnitLocus_inf (W : AlgebraicSpaces B S hS)
    (I J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    {x : points B S hS W.1} (hI : x ∈ idealUnitLocus B S hS W I)
    (hJ : x ∈ idealUnitLocus B S hS W J) : x ∈ idealUnitLocus B S hS W (I ⊓ J) := by
  obtain ⟨V, hV, y, rfl⟩ := hI
  obtain ⟨V', g, hV', y', rfl⟩ := (mem_idealUnitLocus_iff_exists_over B S hS W J V y).1 hJ
  refine ⟨V', ?_, y', ?_⟩
  · change I.obj (op V') ⊓ J.obj (op V') = ⊤
    rw [SheafOfModules.Submodule.unit_obj_eq_top_of_map I g.op hV, hV', inf_top_eq]
  · rw [← pointsMap_comp_apply, yoneda_map_toOver_map_comp_hom g]

/-! ### A generic trivialization by copies of a smaller sheaf of ideals -/

/-- **On a Noetherian reduced algebraic space with irreducible space of points, a coherent module
of full support is generically trivialized by copies of a sheaf of ideals inside any prescribed
nonzero one.**  Let `ℐ ≠ 0` be quasi-coherent and `𝒢` coherent with support everything.  There
are a quasi-coherent sheaf of ideals `𝒥 ⊆ ℐ` with nonempty unit locus, an `r > 0` and a morphism
`ψ : 𝒥^{⊕ r} ⟶ 𝒢` which is bijective on sections over every chart on which `𝒥` is the whole
structure sheaf.

The generic trivialization of `𝒢` gives such a `ψ₀ : 𝒥₀^{⊕ r} ⟶ 𝒢`; `𝒥 = ℐ ∩ 𝒥₀` has nonempty
unit locus because the two unit loci are nonempty opens of an irreducible space, and `ψ` is `ψ₀`
restricted to `𝒥^{⊕ r}`. -/
theorem exists_generic_trivialization_le (hZtop : B.Contains (⊤_ Scheme.{u}))
    (W : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZtop W.1)
    (hred : HasEtaleLocalProperty B S hS W.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : @IrreducibleSpace (points B S hS W.1) (pointTopology B S hS W.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hI : I ≠ ⊥)
    (G : Modules.{u, u} B S hS W.1 W.2) (hG : IsCoherent B S hS W.1 W.2 G)
    (hsupp : moduleSupportSet B S hS W G = Set.univ) :
    ∃ J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule, J ≤ I ∧
      J.toSheafOfModules.IsQuasicoherentOnSite ∧ (idealUnitLocus B S hS W J).Nonempty ∧
      ∃ (r : ℕ) (ψ : (∏ᶜ fun _ : Fin r =>
          (J.toSheafOfModules : Modules.{u, u} B S hS W.1 W.2)) ⟶ G),
        0 < r ∧ ∀ V : SmallEtale B S hS W.1, J.obj (op V) = ⊤ →
          Function.Bijective (ψ.val.app (op V)).hom := by
  let := pointTopology B S hS W.1
  obtain ⟨J₀, hJ₀q, hJ₀ne, r, ψ₀, hr, hψ₀⟩ :=
    exists_generic_trivialization_pos B S hS hZtop W hN hred hirr.toNonempty G hG hsupp
  have hJne : (idealUnitLocus B S hS W (I ⊓ J₀)).Nonempty := by
    obtain ⟨x, hx⟩ := idealUnitLocus_nonempty_of_ne_bot B S hS W hred I hI
    obtain ⟨y, hy⟩ := hJ₀ne
    obtain ⟨z, -, hzI, hzJ⟩ := (IrreducibleSpace.isIrreducible_univ (points B S hS W.1)).2
      _ _ (isOpen_idealUnitLocus B S hS W I) (isOpen_idealUnitLocus B S hS W J₀)
      ⟨x, trivial, hx⟩ ⟨y, trivial, hy⟩
    exact ⟨z, mem_idealUnitLocus_inf B S hS W I J₀ hzI hzJ⟩
  let F₁ := fun _ : Fin r => ((I ⊓ J₀).toSheafOfModules : Modules.{u, u} B S hS W.1 W.2)
  let F₀ := fun _ : Fin r => (J₀.toSheafOfModules : Modules.{u, u} B S hS W.1 W.2)
  let ι : ∏ᶜ F₁ ⟶ ∏ᶜ F₀ := Limits.Pi.map fun _ => Stacks.SheafOfModules.submoduleInfSnd I J₀
  refine ⟨I ⊓ J₀, inf_le_left, isQuasicoherentOnSite_idealInf B S hS W I J₀ hIq hJ₀q, hJne, r,
    ι ≫ ψ₀, hr, fun V hV => ?_⟩
  have hJ₀V : J₀.obj (op V) = ⊤ := eq_top_iff.2 (hV ▸ inf_le_right)
  let e₁ := fun x : (∏ᶜ F₁).val.obj (op V) => fun k => ((Pi.π F₁ k).val.app (op V)).hom x
  let e₀ := fun x : (∏ᶜ F₀).val.obj (op V) => fun k => ((Pi.π F₀ k).val.app (op V)).hom x
  have hbij₁ : Function.Bijective e₁ := bijective_pi_π_val_app_fin B S hS F₁ (op V)
  have hbij₀ : Function.Bijective e₀ := bijective_pi_π_val_app_fin B S hS F₀ (op V)
  let c : (Fin r → (I ⊓ J₀).toSheafOfModules.val.obj (op V)) →
      (Fin r → J₀.toSheafOfModules.val.obj (op V)) := fun a k =>
    ((Stacks.SheafOfModules.submoduleInfSnd I J₀).val.app (op V)).hom (a k)
  have hcomm : e₀ ∘ (ι.val.app (op V)).hom = c ∘ e₁ := by
    funext t k
    exact congrArg (fun φ => (φ.val.app (op V)).hom t)
      (Limits.Pi.map_π (fun _ : Fin r => Stacks.SheafOfModules.submoduleInfSnd I J₀) k)
  have hc : Function.Bijective c := by
    refine ⟨fun a a' h => funext fun k => Subtype.ext (by
      have h' := congrArg Subtype.val (congrFun h k)
      exact h'),
      fun b => ⟨fun k => ⟨(b k).1, by rw [hV]; exact Submodule.mem_top⟩, rfl⟩⟩
  have hι : Function.Bijective (ι.val.app (op V)).hom :=
    (Function.Bijective.of_comp_iff' hbij₀ _).1 (by rw [hcomm]; exact hc.comp hbij₁)
  exact (hψ₀ V hJ₀V).comp hι

/-! ### Direct images of inverse-image ideals -/

section InverseImageIdeal

variable {Z' W : AlgebraicSpaces B S hS} (f : Z' ⟶ W) (haff : IsAffineHom B S hS f.hom)
  (K : (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).Submodule)

/-- **The direct image of `f⁻¹𝒦 · 𝒪_{Z'}` lands in `𝒦 · 𝒞` under every morphism
`π : f_*𝒪_{Z'} ⟶ 𝒞`.**  For an affine `f : Z' ⟶ W` and a quasi-coherent sheaf of ideals
`𝒦 ⊆ 𝒪_W`, the image of `f_*(f⁻¹𝒦 · 𝒪_{Z'}) ⟶ f_*𝒪_{Z'}` is `𝒦 · f_*𝒪_{Z'}` by Stacks 0GF8,
which `π` carries into `𝒦 · 𝒞`.  The direct image is base change of charts,
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`. -/
theorem smallBaseChangeModulePushforward_map_pullbackIdealSubsheaf_ι_mem_idealSmul
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    {C : SheafOfModules.{u} (smallEtaleRingSheaf B S hS W.1 W.2)}
    (π : (smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).obj
        (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2)) ⟶ C)
    (Q : (SmallEtale B S hS W.1)ᵒᵖ) (x : ((smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).obj
        (pullbackIdealSubsheaf B S hS f
          (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) K).toSheafOfModules).val.obj
            Q) :
    π.val.app Q (((smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).map
        (pullbackIdealSubsheaf B S hS f
          (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) K).ι).val.app Q x) ∈
      (Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) K (⊤ : C.Submodule)).obj Q := by
  have hmem : ((smallBaseChangeModulePushforward B S hS f
      (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).map
        (pullbackIdealSubsheaf B S hS f
          (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) K).ι).val.app Q x ∈
      (Stacks.Sites.idealSmul (O := structureSheaf B S hS W.1 W.2) K
        (⊤ : ((smallBaseChangeModulePushforward B S hS f
          (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).obj
          (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2))).Submodule)).obj Q := by
    rw [idealSmul_pushforward_eq_of_isQuasicoherentOnSite B S hS f haff K _ hK
      (SheafOfModules.isQuasicoherentOnSite_unit _)]
    exact Stacks.Sites.le_idealSmul_top (O := structureSheaf B S hS Z'.1 Z'.2)
      (pullbackIdealSubsheaf B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) K) _ x.2
  exact Stacks.Sites.map_mem_idealSmul_top (O := structureSheaf B S hS W.1 W.2) π K hmem

/-- **Over a chart on which `𝒦` is everything, `f_*(f⁻¹𝒦 · 𝒪_{Z'}) ⟶ f_*𝒪_{Z'}` is surjective on
sections**: the inverse-image ideal contains `f♯(1) = 1` over the base-changed chart. -/
theorem surjective_smallBaseChangeModulePushforward_map_pullbackIdealSubsheaf_ι
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS W.1)
    (hV : K.obj (op V) = ⊤) :
    Function.Surjective (((smallBaseChangeModulePushforward B S hS f hf).map
      (pullbackIdealSubsheaf B S hS f hf K).ι).val.app (op V)) := by
  set N := pullbackIdealSubsheaf B S hS f hf K
  have h1 : chartIdealPullbackHom B S hS f hf V 1 ∈
      N.obj (op ((smallBaseChange B S hS f hf).obj V)) :=
    chartIdealPullbackHom_mem_pullbackIdealSubsheaf B S hS f hf K V (by
      change _ ∈ K.obj (op V)
      rw [hV]
      trivial)
  rw [map_one] at h1
  intro s
  have h2 : (N.obj _ : Ideal (chartSectionsRing B S hS Z' ((smallBaseChange B S hS f hf).obj V))) =
      ⊤ := (Ideal.eq_top_iff_one _).2 h1
  exact ⟨⟨s, h2 ▸ Submodule.mem_top⟩, rfl⟩

end InverseImageIdeal

/-! ### The step of the Noetherian induction -/

section Step

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

/-- If `m = m' ≫ ψ` with `ψ` injective and `m` surjective on the sections over `V`, then `m'` is
surjective on the sections over `V`. -/
theorem surjective_val_app_of_comp_eq {X : AlgebraicSpaces B S hS}
    {A P G : Modules.{u, u} B S hS X.1 X.2} {m' : A ⟶ P} {ψ : P ⟶ G} {m : A ⟶ G}
    (h : m' ≫ ψ = m) (V : (SmallEtale B S hS X.1)ᵒᵖ) (hψ : Function.Injective (ψ.val.app V))
    (hm : ∀ s : G.val.obj V, ∃ y : A.val.obj V, m.val.app V y = s) (s : P.val.obj V) :
    ∃ y : A.val.obj V, m'.val.app V y = s := by
  obtain ⟨y, hy⟩ := hm (ψ.val.app V s)
  refine ⟨y, hψ ?_⟩
  rw [← hy, ← h]
  rfl

/-- **A direct image from `Z'` factoring through a generic trivialization.**  Let `f : Z' ⟶ W`
be finite, `ψ : 𝒫 ⟶ f_*𝒪_{Z'}` a monomorphism injective over the charts on which a quasi-coherent
`𝒥 ⊆ 𝒪_W` is everything, and suppose `𝒥ᵏ` kills the cokernel of `ψ`.  Then
`f_*(f⁻¹𝒥ᵏ · 𝒪_{Z'}) ⟶ f_*𝒪_{Z'}` factors through `ψ` by a monomorphism which is surjective on
sections over those charts, and `f⁻¹𝒥ᵏ · 𝒪_{Z'}` is quasi-coherent and coherent.

The image of `f_*(f⁻¹𝒥ᵏ · 𝒪_{Z'})` is `𝒥ᵏ · f_*𝒪_{Z'}` (Stacks 0GF8), which dies in the cokernel
of `ψ`; over a chart on which `𝒥` is everything the inverse-image ideal contains `1`. -/
theorem exists_mono_factor_of_idealPowSmul_cokernel_eq_bot {Z' W : AlgebraicSpaces B S hS}
    (f : Z' ⟶ W)
    (hf : IsFinite B S hS f.hom)
    (hZ'N : HasEtaleLocalProperty B S hS Z'.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hJq : J.toSheafOfModules.IsQuasicoherentOnSite) (k : ℕ)
    {P : Modules.{u, u} B S hS W.1 W.2} (ψ : P ⟶ ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f hf.isAffineHom)).obj
          (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2)) :
            Modules.{u, u} B S hS W.1 W.2)) (hψm : Mono ψ)
    (hψ : ∀ V : SmallEtale B S hS W.1, J.obj (op V) = ⊤ → Function.Injective (ψ.val.app (op V)))
    (hk : Stacks.Sites.idealSmul (M := cokernel ψ)
      (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS W.1 W.2).O) J k) ⊤ = ⊥) :
    ∃ (A : Modules.{u, u} B S hS W.1 W.2) (m' : A ⟶ P), Mono m' ∧
      (∀ V : SmallEtale B S hS W.1, J.obj (op V) = ⊤ →
        ∀ s : P.val.obj (op V), ∃ y : A.val.obj (op V), m'.val.app (op V) y = s) ∧
      ∃ M : Modules.{u, u} B S hS Z'.1 Z'.2, M.IsQuasicoherentOnSite ∧
        IsCoherent B S hS Z'.1 Z'.2 M ∧
        Nonempty ((modulePushforward B S hS f).obj M ≅ A) := by
  have haff := hf.isAffineHom
  have := hψm
  let K : (SheafOfModules.unit (smallEtaleRingSheaf B S hS W.1 W.2)).Submodule :=
    Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS W.1 W.2).O) J k
  have hKq : K.toSheafOfModules.IsQuasicoherentOnSite := by
    have h := isQuasicoherentOnSite_idealPowSubmodule B S hS W.1 W.2 J
      (SheafOfModules.unit (structureRingSheaf B S hS W))
      (SheafOfModules.isQuasicoherentOnSite_unit _) hJq k
    have hKeq : idealPowSubmodule J k (SheafOfModules.unit (structureRingSheaf B S hS W)) = K :=
      Stacks.Sites.idealSmul_top_eq (O := (smallEtaleRingedSite B S hS W.1 W.2).O) K
    change (idealPowSubmodule J k
      (SheafOfModules.unit
        (structureRingSheaf B S hS W))).toSheafOfModules.IsQuasicoherentOnSite at h
    rwa [hKeq] at h
  let N := pullbackIdealSubsheaf B S hS f
    (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) K
  let A : Modules.{u, u} B S hS W.1 W.2 := (smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).obj N.toSheafOfModules
  let m : A ⟶ ((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f hf.isAffineHom)).obj
          (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2)) :
            Modules.{u, u} B S hS W.1 W.2) := (smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).map N.ι
  have hmm : Mono m := by
    have : (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff))).IsRightAdjoint :=
      isRightAdjoint_pushforward_smallBaseChangeSharp B S hS f _
    exact Functor.map_mono (SheafOfModules.pushforward.{u} (smallBaseChangeSharp B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff))) N.ι
  have hm0 : (m ≫ cokernel.π ψ : A ⟶ cokernel ψ) = (0 : A ⟶ cokernel ψ) := by
    ext Q x
    have h' : (cokernel.π ψ).val.app Q (((smallBaseChangeModulePushforward B S hS f
        (relativelyRepresentable_hom_of_isAffineHom B S hS f haff)).map N.ι).val.app Q x) ∈
        (Stacks.Sites.idealSmul (M := cokernel ψ)
          (Stacks.Sites.idealPow (O := (smallEtaleRingedSite B S hS W.1 W.2).O) J k) ⊤).obj Q :=
      smallBaseChangeModulePushforward_map_pullbackIdealSubsheaf_ι_mem_idealSmul B S hS f
        haff K hKq (cokernel.π ψ) Q x
    rw [hk] at h'
    have h'' := (SheafOfModules.Submodule.bot_obj (cokernel ψ) Q).le h'
    rwa [Submodule.mem_bot] at h''
  let m' := Abelian.monoLift ψ m hm0
  have hm'' : m' ≫ ψ = m := Abelian.monoLift_comp ψ m hm0
  have hm'm : Mono m' := by
    have h : Mono (m' ≫ ψ) := hm'' ▸ hmm
    exact mono_of_mono m' ψ
  refine ⟨A, m', hm'm, fun V hV => surjective_val_app_of_comp_eq B S hS hm'' (op V) (hψ V hV)
    fun s => surjective_smallBaseChangeModulePushforward_map_pullbackIdealSubsheaf_ι B S hS f K
      (relativelyRepresentable_hom_of_isAffineHom B S hS f haff) V
      (Stacks.Sites.idealPow_obj_eq_top J hV k) s, N.toSheafOfModules,
    isQuasicoherentOnSite_pullbackIdealSubsheaf B S hS f _ K hKq,
    isCoherent_quasicoherentIdeal B S hS Z' hZ'N
      ⟨N, isQuasicoherentOnSite_pullbackIdealSubsheaf B S hS f _ K hKq⟩,
    ⟨(modulePushforwardChartIso B S hS f _).app _⟩⟩

/-- **Property (3)(b) of Stacks 07UT for `𝒢 = f_*𝒪_{Z'}`, in the form the proof of Stacks 07UT
consumes.**  Let `W` be Noetherian, reduced, with irreducible space of points, `f : Z' ⟶ W` finite
with `f_*𝒪_{Z'}` coherent of full support, and `ℐ ≠ 0` a quasi-coherent sheaf of ideals.  There are
a quasi-coherent `𝒥 ⊆ ℐ` with nonempty unit locus, an `r > 0`, a quasi-coherent and coherent
`𝒪_{Z'}`-module `𝓜` and a monomorphism `f_*𝓜 ⟶ 𝒥^{⊕ r}` whose cokernel is coherent and supported
in `V(𝒥)`.

`𝒥` and the monomorphism `ψ : 𝒥^{⊕ r} ⟶ f_*𝒪_{Z'}` come from
`AlgebraicGeometry.Space.exists_generic_trivialization_le`; the cokernel of `ψ` is supported in
`V(𝒥)`, so a power `𝒥ᵏ` kills it (Stacks 07UK), and
`AlgebraicGeometry.Space.exists_mono_factor_of_idealPowSmul_cokernel_eq_bot` gives the
factorization, with `𝓜 = f⁻¹𝒥ᵏ · 𝒪_{Z'}`. -/
theorem exists_mono_pi_modulePushforward (hZtop : B.Contains (⊤_ Scheme.{u}))
    {Z' W : AlgebraicSpaces B S hS} (f : Z' ⟶ W) (hf : IsFinite B S hS f.hom)
    (hN : IsNoetherian B S hS hZtop W.1)
    (hred : HasEtaleLocalProperty B S hS W.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : @IrreducibleSpace (points B S hS W.1) (pointTopology B S hS W.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hI : I ≠ ⊥)
    (hG : IsCoherent B S hS W.1 W.2
      ((modulePushforward B S hS f).obj (SheafOfModules.unit (structureRingSheaf B S hS Z'))))
    (hGs : moduleSupportSet B S hS W
      ((modulePushforward B S hS f).obj (SheafOfModules.unit (structureRingSheaf B S hS Z'))) =
        Set.univ) :
    ∃ J : (SheafOfModules.unit (structureRingSheaf B S hS W)).Submodule, J ≤ I ∧
      J.toSheafOfModules.IsQuasicoherentOnSite ∧ (idealUnitLocus B S hS W J).Nonempty ∧
      ∃ (r : ℕ), 0 < r ∧ ∃ (M : Modules.{u, u} B S hS Z'.1 Z'.2), M.IsQuasicoherentOnSite ∧
        IsCoherent B S hS Z'.1 Z'.2 M ∧ ∃ m : (modulePushforward B S hS f).obj M ⟶
            ∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS W.1 W.2),
          Mono m ∧ IsCoherent B S hS W.1 W.2 (cokernel m) ∧
            moduleSupportSet B S hS W (cokernel m) ⊆ idealZeroLocus B S hS W J := by
  let e := modulePushforwardChartIso B S hS f (relativelyRepresentable_hom_of_isAffineHom B S hS f
    hf.isAffineHom)
  have hG' : IsCoherent B S hS W.1 W.2 ((smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isAffineHom B S hS f hf.isAffineHom)).obj
      (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2)) :
        Modules.{u, u} B S hS W.1 W.2) := isCoherent_of_iso B S hS W.2 (e.app _) hG
  have hGs' : moduleSupportSet B S hS W ((smallBaseChangeModulePushforward B S hS f
    (relativelyRepresentable_hom_of_isAffineHom B S hS f hf.isAffineHom)).obj
      (SheafOfModules.unit (smallEtaleRingSheaf B S hS Z'.1 Z'.2)) :
        Modules.{u, u} B S hS W.1 W.2) = Set.univ :=
    (moduleSupportSet_congr B S hS W (e.app _)).symm.trans hGs
  have hZ'N : HasEtaleLocalProperty B S hS Z'.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z'.2 W.2 f.hom
      (isLocallyOfFiniteType_of_isFinite B S hS Z'.2 W.2 hf) hN.2.2
  obtain ⟨J, hJI, hJq, hJne, r, ψ, hr, hψ⟩ := exists_generic_trivialization_le B S hS hZtop W
    hN hred hirr I hIq hI _ hG' hGs'
  have hψm : Mono ψ := mono_of_injective_on_idealUnitCharts B S hS W hred hirr J hJne ψ
    (fun V hV y hy => (hψ V hV).1 (hy.trans (map_zero _).symm))
  have hJc := isCoherent_quasicoherentIdeal B S hS W hN.2.2 ⟨J, hJq⟩
  have hPc : IsCoherent B S hS W.1 W.2
      (∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS W.1 W.2)) :=
    isCoherent_piConst B S hS W.1 W.2 _ hJc r
  have hC : IsCoherent B S hS W.1 W.2 (cokernel ψ) := isCoherent_cokernel B S hS W.1 W.2 hPc hG' ψ
  obtain ⟨k, hk⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus B S hS
    hZtop W hN (cokernel ψ) hC J hJq).2
    (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS W J ψ
      (fun V hV s => (hψ V hV).2 s))
  have hψi : ∀ V : SmallEtale B S hS W.1, J.obj (op V) = ⊤ →
      Function.Injective (ψ.val.app (op V)) := fun V hV => (hψ V hV).1
  have := hψm
  have key := exists_mono_factor_of_idealPowSmul_cokernel_eq_bot B S hS
    f hf hZ'N J hJq k ψ hψm hψi hk
  obtain ⟨A, m', hm'm, hm's, M, hMq, hMc, hA⟩ := key
  obtain ⟨eA⟩ := hA
  have hAc : IsCoherent B S hS W.1 W.2 ((modulePushforward B S hS f).obj M) :=
    isCoherent_modulePushforward_of_isFinite' B S hS f hf hN.2.2 M hMc
  have hcm' : moduleSupportSet B S hS W (cokernel m') ⊆ idealZeroLocus B S hS W J :=
    supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS W J m' hm's
  let m₁ : (modulePushforward B S hS f).obj M ⟶
      ∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS W.1 W.2) := eA.hom ≫ m'
  have hm₁ : Mono m₁ :=
    @mono_comp _ _ _ _ _ eA.hom (@IsIso.mono_of_iso _ _ _ _ eA.hom (Iso.isIso_hom eA)) m' hm'm
  have hc₁ : IsCoherent B S hS W.1 W.2 (cokernel m₁) :=
    isCoherent_cokernel B S hS W.1 W.2 hAc hPc _
  have hs₁ : moduleSupportSet B S hS W (cokernel m₁) ⊆ idealZeroLocus B S hS W J :=
    (moduleSupportSet_congr B S hS W (@cokernelEpiComp _ _ _ _ _ _ eA.hom m'
      (@IsIso.epi_of_iso _ _ _ _ eA.hom (Iso.isIso_hom eA)) _)).le.trans hcm'
  exact ⟨J, hJI, hJq, hJne, r, hr, M, hMq, hMc, m₁, hm₁, hc₁, hs₁⟩

/-- A functor which kills a finite direct sum of `r ≥ 1` copies of an object kills the object:
it is a retract of the sum, and functors preserve retracts. -/
theorem isZero_obj_of_isZero_obj_biproduct {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [HasZeroMorphisms D] (F : C ⥤ D) (M : C) {r : ℕ} (hr : 0 < r)
    [HasBiproduct fun _ : Fin r => M] (h : IsZero (F.obj (⨁ fun _ : Fin r => M))) :
    IsZero (F.obj M) := by
  have : IsSplitMono (F.map (biproduct.ι (fun _ : Fin r => M) ⟨0, hr⟩)) :=
    IsSplitMono.mk' ⟨F.map (biproduct.π _ ⟨0, hr⟩), by
      rw [← F.map_comp, biproduct.ι_π_self, F.map_id]⟩
  exact IsZero.of_mono (F.map (biproduct.ι (fun _ : Fin r => M) ⟨0, hr⟩)) h

variable (hZtop : B.Contains (⊤_ Scheme.{u}))

/-- **The step of the Noetherian induction of Stacks 07UT along a finite surjection.**  Let
`f : Y ⟶ X` be finite and surjective with `X` Noetherian, let `i : Z ⟶ X` be a reduced closed
subspace with `|Z|` irreducible and let `ℐ ⊆ 𝒪_Z` be a quasi-coherent sheaf of ideals.  Let `P` be
a property of `𝒪_X`-modules which holds on zero modules, is closed under extensions of coherent
modules, passes from a finite direct sum `N^{⊕ r}`, `r ≥ 1`, of a coherent `N` to `N`, and holds on
`i_*f'_*𝓜` for every quasi-coherent coherent `𝓜` on `Z' = Y ×_X Z`, `f' : Z' ⟶ Z` the base change.
If `P` holds on every coherent `𝒩` whose support is strictly smaller than that of `i_*ℐ`, then it
holds on `i_*ℐ`.

This is property (3)(b) of Stacks 07UT for `𝒢 = f'_*𝒪_{Z'}`, carried through the proof of
Stacks 07UT.  For `ℐ ≠ 0`, the coherent `𝒢` has full support (Stacks 0GF7), so it receives a
monomorphism `ψ : 𝒥^{⊕ r} ⟶ 𝒢` from copies of a sheaf of ideals `𝒥 ⊆ ℐ`, bijective over the
charts on which `𝒥` is everything (`AlgebraicGeometry.Space.exists_generic_trivialization_le`).
Its cokernel is supported in `V(𝒥)`, so it is killed by some `𝒥ᵏ` (Stacks 07UK), and then so is
the image of `f'_*(f'⁻¹𝒥ᵏ · 𝒪_{Z'}) ⟶ 𝒢` (Stacks 0GF8); hence this map factors as `ψ ∘ m'`, with
`m'` a monomorphism whose cokernel is supported in `V(𝒥)`.  So `P(i_*𝒥^{⊕ r})` by extension of
`P(i_*f'_*(f'⁻¹𝒥ᵏ · 𝒪_{Z'}))` and of the cokernel, `P(i_*𝒥)` because it is a summand, and
`P(i_*ℐ)` by the extension `0 ⟶ 𝒥 ⟶ ℐ ⟶ ℐ/𝒥 ⟶ 0`, the quotient being supported in `V(𝒥)`. -/
theorem property_idealPushforward_of_lt
    (X Y : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P)
    (hsum : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N → ∀ r : ℕ, 0 < r →
      P (⨁ fun _ : Fin r => N) → P N)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (hbase : ∀ M : Modules.{u, u} B S hS (pullback f (closedSubfunctorι B S hS hZ)).1
        (pullback f (closedSubfunctorι B S hS hZ)).2,
      M.IsQuasicoherentOnSite → IsCoherent B S hS _ _ M →
        P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          ((modulePushforward B S hS (pullback.snd f (closedSubfunctorι B S hS hZ))).obj M)))
    (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hsmall : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
      P N) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  let Zs := closedSubfunctorSpace B S hS hZ
  let iZ := closedSubfunctorι B S hS hZ
  by_cases hI : I.1 = ⊥
  · exact hzero _ (isZero_modulePushforward_of_eq_bot B S hS X hZ I hI)
  have hNZ := isNoetherian_closedSubfunctor B S hS hZtop X hX hZ
  have hIimg := moduleSupportSet_idealPushforward_eq_image B S hS X hX.2.2 hZ hint I hI
  have sq := IsPullback.of_hasPullback f iZ
  set f' := pullback.snd f iZ
  have hf' : IsFinite B S hS f'.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have : Fact (HasEtaleLocalProperty B S hS (pullback f iZ).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :=
    ⟨isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (pullback f iZ).2 Zs.2 f'.hom
      (isLocallyOfFiniteType_of_isFinite B S hS (pullback f iZ).2 Zs.2 hf') hNZ.2.2⟩
  have hG : IsCoherent B S hS Zs.1 Zs.2 ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS (pullback f iZ)))) :=
    isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hNZ.2.2 _
      (isCoherent_structureSheaf B S hS (pullback f iZ).1 (pullback f iZ).2)
  have hGs := supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ B S hS f iZ sq hfs
  obtain ⟨J, hJI, hJq, hJne, r, hr, M, hMq, hMc, m, hm, hcok, hcoksupp⟩ :=
    exists_mono_pi_modulePushforward B S hS hZtop f' hf' hNZ hint.1 hint.2 I.1 I.2 hI hG hGs
  have hJbot : J ≠ ⊥ := ne_bot_of_idealUnitLocus_nonempty B S hS Zs J hJne
  have hJc := isCoherent_quasicoherentIdeal B S hS Zs hNZ.2.2 ⟨J, hJq⟩
  have hPc : IsCoherent B S hS Zs.1 Zs.2
      (∏ᶜ fun _ : Fin r => (J.toSheafOfModules : Modules.{u, u} B S hS Zs.1 Zs.2)) :=
    isCoherent_piConst B S hS Zs.1 Zs.2 _ hJc r
  have hiZf : IsFinite B S hS iZ.hom := isFinite_of_isClosedImmersion B S hS _ hZ.2
  have hAc : IsCoherent B S hS Zs.1 Zs.2 ((modulePushforward B S hS f').obj M) :=
    isCoherent_modulePushforward_of_isFinite' B S hS f' hf' hNZ.2.2 M hMc
  have hAX := isCoherent_modulePushforward_of_isFinite' B S hS iZ hiZf hX.2.2 _ hAc
  have hPX := isCoherent_modulePushforward_of_isFinite' B S hS iZ hiZf hX.2.2 _ hPc
  have hlt : moduleSupportSet B S hS X (cokernel ((modulePushforward B S hS iZ).map m)) ⊂
      moduleSupportSet B S hS X ((modulePushforward B S hS iZ).obj I.1.toSheafOfModules) := by
    rw [hIimg, moduleSupportSet_cokernel_modulePushforward B S hS X Zs iZ hZ.2 m hcok]
    exact lt_of_le_of_lt (Set.image_mono hcoksupp)
      (image_idealZeroLocus_ssubset B S hS hZ hint J hJbot)
  have hPprod := hext _ (shortExact_cokernelSequence_modulePushforward B S hS X Zs iZ m hm)
    hAX hPX (isCoherent_cokernel B S hS X.1 X.2 hAX hPX _) (hbase M hMq hMc)
    (hsmall _ (isCoherent_cokernel B S hS X.1 X.2 hAX hPX _) hlt)
  have hJX := isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 iZ hZ.2 ⟨J, hJq⟩
  have hPJ : P ((modulePushforward B S hS iZ).obj J.toSheafOfModules) :=
    hsum _ hJX r hr (property_of_iso B S hS X P hzero hext hPX
      (isCoherent_of_iso B S hS X.2
        (modulePushforwardBiproductConstIso B S hS X iZ r J.toSheafOfModules).symm hPX)
      (modulePushforwardBiproductConstIso B S hS X iZ r J.toSheafOfModules).symm hPprod)
  let incl : J.toSheafOfModules ⟶ I.1.toSheafOfModules := I.1.factorThru J.ι
    fun W x => hJI W x.2
  have hincl : Mono incl := by
    have h : incl ≫ I.1.ι = J.ι := SheafOfModules.Submodule.factorThru_ι _ _ _
    have : Mono (incl ≫ I.1.ι) := h ▸ SheafOfModules.Submodule.mono_ι_via_forget J
    exact mono_of_mono _ I.1.ι
  have hIc := isCoherent_quasicoherentIdeal B S hS Zs hNZ.2.2 I
  have hcokI : IsCoherent B S hS Zs.1 Zs.2 (cokernel incl) :=
    isCoherent_cokernel B S hS Zs.1 Zs.2 hJc hIc incl
  have hIX := isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2 iZ hZ.2 I
  have hltI : moduleSupportSet B S hS X (cokernel ((modulePushforward B S hS iZ).map incl)) ⊂
      moduleSupportSet B S hS X ((modulePushforward B S hS iZ).obj I.1.toSheafOfModules) := by
    rw [hIimg, moduleSupportSet_cokernel_modulePushforward B S hS X Zs iZ hZ.2 incl hcokI]
    refine lt_of_le_of_lt (Set.image_mono ?_) (image_idealZeroLocus_ssubset B S hS hZ hint J hJbot)
    exact supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective B S hS Zs J incl
      fun V hV s => ⟨⟨s.1, (Submodule.eq_top_iff'.1 hV) _⟩, rfl⟩
  exact hext _ (shortExact_cokernelSequence_modulePushforward B S hS X Zs iZ incl hincl) hJX hIX
    (isCoherent_cokernel B S hS X.1 X.2 hJX hIX _) hPJ
    (hsmall _ (isCoherent_cokernel B S hS X.1 X.2 hJX hIX _) hltI)

/-- **The step of Stacks 07VP.**  Let `f : Y ⟶ X` be finite and surjective with `Y` affine and
`X` Noetherian, let `i : Z ⟶ X` be a reduced closed subspace with `|Z|` irreducible and let
`ℐ ⊆ 𝒪_Z` be a quasi-coherent sheaf of ideals.  If `H¹(X, 𝒩) = 0` for every coherent `𝒩` whose
support is strictly smaller than that of `i_*ℐ`, then `H¹(X, i_*ℐ) = 0`.

This is `AlgebraicGeometry.Space.property_idealPushforward_of_lt` for `P 𝒩 := H¹(X, 𝒩) = 0`:
that property is closed under extensions by the long exact cohomology sequence and under direct
summands by additivity, and `H¹(X, i_*f'_*𝓜) = 0` for `𝓜` quasi-coherent on `Y ×_X Z` because
`Y ×_X Z` is affine (Stacks 0D2U). -/
theorem isZero_rightDerived_one_idealPushforward_of_lt
    (X Y : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hsmall : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
      moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
      have := enoughInjectives_modules B S hS X.1 X.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj N)) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
        ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)
  exact property_idealPushforward_of_lt B S hS hZtop X Y hX f hf hfs
    (fun N => IsZero ((Γ.rightDerived 1).obj N)) (fun N hN => Functor.map_isZero _ hN)
    (fun E hE _ _ _ h1 h3 => Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE Γ 1
      h1 h3)
    (fun N _ r hr h => isZero_obj_of_isZero_obj_biproduct (Γ.rightDerived 1) N hr h) Z hZ
    (fun M hMq _ => isZero_rightDerived_modulePushforward_modulePushforward_of_isPullback B S hS
      (IsPullback.of_hasPullback f (closedSubfunctorι B S hS hZ)) hf hZ.2 hY M hMq 1 one_pos)
    hint I hsmall

/-- **Stacks 07VP.**  Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` which is finite
and surjective, with `Y` affine and `X` Noetherian.  Then `X` is affine.

By Stacks 0D2V it suffices that `H¹(X, 𝓕) = 0` for every coherent `𝓕`.  That property is closed
under extensions, by the long exact cohomology sequence, and holds on zero modules; so by
Stacks 07US, with the filtration of Stacks 07UR, it suffices to prove it for the direct image
`i_*ℐ` of every quasi-coherent sheaf of ideals on every reduced closed subspace `i : Z ⟶ X` with
`|Z|` irreducible, which is done by Noetherian induction on the support
(`AlgebraicGeometry.Space.forall_property_idealPushforward_of_step`), the step being
`AlgebraicGeometry.Space.isZero_rightDerived_one_idealPushforward_of_lt`: property (3) of
Stacks 07UT for `𝒢 = f'_*𝒪_{Y ×_X Z}`. -/
theorem isAffineSpace_of_isFinite_of_isSurjective (X Y : AlgebraicSpaces B S hS) (f : Y ⟶ X)
    (hf : IsFinite B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) (hX : IsNoetherian B S hS hZtop X.1) :
    IsAffineSpace B S hS X.1 := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let Γ := globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)
  have hzero : ∀ N : Modules.{u, u} B S hS X.1 X.2, IsZero N → IsZero ((Γ.rightDerived 1).obj N) :=
    fun N hN => Functor.map_isZero _ hN
  have hext : ClosedUnderCoherentExtensions B S hS X (fun N => IsZero ((Γ.rightDerived 1).obj N)) :=
    fun E hE _ _ _ h1 h3 => Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE Γ 1 h1 h3
  exact isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one B S hS hZtop X hX
    fun F hF => property_of_ideal_pushforward_and_extensions B S hS X hX
      (fun N => IsZero ((Γ.rightDerived 1).obj N)) (Or.inr hzero) hext
      (fun Z hZ hint I => forall_property_idealPushforward_of_step B S hS hZtop X hX _ hzero hext
        (fun Z' hZ' hint' I' hsmall => isZero_rightDerived_one_idealPushforward_of_lt B S hS hZtop X
          Y hX f hf hfs hY Z' hZ' hint' I' hsmall) Z hZ hint I) F hF

end Step

end AlgebraicGeometry.Space
