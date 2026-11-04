module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Module.FinitePresentationRel.BaseChange
public import StacksFrontier.Algebra.Module.FinitePresentationRel.Localization
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing relative finite presentation on affine opens

For a quasi-coherent module on a scheme locally of finite type over a base, finite presentation
relative to the base can be checked on every pair of compatible affine opens. The property is
then preserved when both schemes and the module are restricted to compatible open subschemes.

## Main results

* `AlgebraicGeometry.isFinitelyPresentedRelative_iff_affine`: the affine-open characterization
  of relative finite presentation.
* `AlgebraicGeometry.isFinitelyPresentedRelative_resLE`: relative finite presentation is
  preserved by restriction to compatible open subschemes.

## Implementation notes

The morphism between compatible open subschemes is `Scheme.Hom.resLE`, and restriction of the
module is `Scheme.Modules.restrict`. The algebra structure on sections is the canonical one
induced by the restricted map on sections.

## References

* [Stacks Project, Tag 09T7](https://stacks.math.columbia.edu/tag/09T7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry


private lemma finitePresentationRel_of_semilinearEquiv
    {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (eA : A ≃ₐ[R] B) (eM : M ≃+ N)
    (he : ∀ a m, eM (a • m) = eA a • eM m)
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R B N := by
  obtain ⟨n, α, hα, hfp⟩ := h
  let β : MvPolynomial (Fin n) R →ₐ[R] B := eA.toAlgHom.comp α
  refine ⟨n, β, eA.surjective.comp hα, ?_⟩
  let _ : Module (MvPolynomial (Fin n) R) M := Module.compHom M α.toRingHom
  let _ : Module (MvPolynomial (Fin n) R) N := Module.compHom N β.toRingHom
  let e : M ≃ₗ[MvPolynomial (Fin n) R] N :=
    { eM with map_smul' := fun p m => he (α p) m }
  exact (LinearEquiv.finitePresentation_iff e).mp hfp

private lemma finitePresentationRel_of_linearEquiv
    {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R A N :=
  finitePresentationRel_of_semilinearEquiv (AlgEquiv.refl) e.toAddEquiv e.map_smul h

private lemma finitePresentationRel_localized_of_isLocalized
    {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (g : A) [IsLocalization.Away g B]
    (φ : M →ₗ[A] N) [IsLocalizedModule.Away g φ]
    (h : Module.FinitePresentationRel R B N) :
    Module.FinitePresentationRel R (Localization.Away g) (LocalizedModule.Away g M) := by
  let eA : Localization.Away g ≃ₐ[A] B :=
    IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) B
  let : Module (Localization.Away g) N := Module.compHom N eA.toRingHom
  let : IsScalarTower A (Localization.Away g) N := ⟨fun a b n => by
    rw [Algebra.smul_def]
    show eA (algebraMap A (Localization.Away g) a * b) • n = a • (eA b • n)
    rw [map_mul, eA.commutes a, mul_smul]
    exact IsScalarTower.algebraMap_smul B a (eA b • n)⟩
  let eM : LocalizedModule.Away g M ≃ₗ[A] N :=
    IsLocalizedModule.linearEquiv (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) M) φ
  let eML : LocalizedModule.Away g M ≃ₗ[Localization.Away g] N :=
    eM.extendScalarsOfIsLocalization (Submonoid.powers g) (Localization.Away g)
  let eAR : Localization.Away g ≃ₐ[R] B := eA.restrictScalars R
  refine finitePresentationRel_of_semilinearEquiv eAR.symm eML.symm.toAddEquiv (fun b n => ?_) h
  show eML.symm (b • n) = eA.symm b • eML.symm n
  conv_lhs => rw [← eA.apply_symm_apply b]
  exact eML.symm.map_smul (eA.symm b) n

private lemma finitePresentationRel_of_baseChange
    {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FinitePresentation A B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (φ : M →ₗ[A] N) (hφ : IsBaseChange B φ)
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R B N :=
  finitePresentationRel_of_linearEquiv hφ.equiv
    (finitelyPresentedRelative_baseChange R A B M h)

private lemma finitePresentationRel_of_localizedModule
    {R A B M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (g : A) [IsLocalization.Away g B]
    (φ : M →ₗ[A] N) [IsLocalizedModule.Away g φ]
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R B N := by
  let : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation g
  exact finitePresentationRel_of_baseChange φ
    (IsLocalizedModule.isBaseChange (Submonoid.powers g) B φ) h

private lemma finitePresentationRel_of_finitePresentation_base
    {R R' A M : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
    [Algebra.FinitePresentation R R'] [Algebra.FiniteType R' A]
    [AddCommGroup M] [Module A M]
    (h : Module.FinitePresentationRel R A M) :
    Module.FinitePresentationRel R' A M := by
  apply Module.FinitePresentationRel.finitePresentationRel_of_allPresentations
  intro n α hα
  let P := MvPolynomial (Fin n) R'
  let : Algebra R P := ((algebraMap R' P).comp (algebraMap R R')).toAlgebra
  let : IsScalarTower R R' P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.trans R R' P
  exact (Module.FinitePresentationRel.allFPCovers_of_finitePresentationRel h)
    P inferInstance (α.restrictScalars R) hα

private lemma finitePresentationRel_iff_of_localizedBase
    {R R' A M : Type u} [CommRing R] [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
    [AddCommGroup M] [Module A M] [Algebra.FiniteType R' A]
    (g : R) [IsLocalization.Away g R'] :
    Module.FinitePresentationRel R A M ↔
      Module.FinitePresentationRel R' A M := by
  let : Algebra.FinitePresentation R R' := IsLocalization.Away.finitePresentation g
  exact ⟨finitePresentationRel_of_finitePresentation_base,
    Module.finitePresentationRel_comp⟩

private lemma finitePresentationRel_basicOpen_of_isLocalized
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (r : Γ(X, U))
    (hLoc : letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
      letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
        Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
      IsLocalizedModule.Away r (basicOpenSectionMap M r))
    (h : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U)) :
    letI : Algebra Γ(S, V) Γ(X, X.basicOpen r) :=
      (f.appLE V (X.basicOpen r) ((X.basicOpen_le r).trans hUV)).hom.toAlgebra
    Module.FinitePresentationRel Γ(S, V) Γ(X, X.basicOpen r)
      Γ(M, X.basicOpen r) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, X.basicOpen r) :=
    (f.appLE V (X.basicOpen r) ((X.basicOpen_le r).trans hUV)).hom.toAlgebra
  let : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, X.basicOpen r) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.appLE_map])
  let : Module Γ(X, U) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
  let : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    IsScalarTower.of_compHom _ _ _
  let : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  let : IsLocalizedModule.Away r (basicOpenSectionMap M r) := hLoc
  exact finitePresentationRel_of_localizedModule r (basicOpenSectionMap M r) h

private lemma finitePresentationRel_iff_base_basicOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (b : Γ(S, V))
    (hUb : U ≤ f ⁻¹ᵁ (S.basicOpen b)) :
    (letI : Algebra Γ(S, V) Γ(X, U) :=
        (f.appLE V U (hUb.trans (f.preimage_mono (S.basicOpen_le b)))).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U)) ↔
    (letI : Algebra Γ(S, S.basicOpen b) Γ(X, U) :=
        (f.appLE (S.basicOpen b) U hUb).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, S.basicOpen b) Γ(X, U) Γ(M, U)) := by
  let : Algebra Γ(S, V) Γ(S, S.basicOpen b) :=
    (S.presheaf.map (homOfLE (S.basicOpen_le b)).op).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, U) :=
    (f.appLE V U (hUb.trans (f.preimage_mono (S.basicOpen_le b)))).hom.toAlgebra
  let : Algebra Γ(S, S.basicOpen b) Γ(X, U) :=
    (f.appLE (S.basicOpen b) U hUb).hom.toAlgebra
  let : IsScalarTower Γ(S, V) Γ(S, S.basicOpen b) Γ(X, U) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.map_appLE])
  have : IsLocalization.Away b Γ(S, S.basicOpen b) :=
    hV.isLocalization_basicOpen b
  have : Algebra.FiniteType Γ(S, S.basicOpen b) Γ(X, U) :=
    f.finiteType_appLE (hV.basicOpen b) hU hUb
  exact finitePresentationRel_iff_of_localizedBase b

private lemma basicOpen_appLE_le_preimage
    {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} {V : S.Opens} (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(S, V)) :
    X.basicOpen (f.appLE V U hUV b) ≤ f ⁻¹ᵁ S.basicOpen b := by
  rw [Scheme.basicOpen_appLE]
  exact inf_le_right

private lemma exists_standard_refinement_of_le_iSup
    (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (V : X.Opens) (hV : IsAffineOpen V)
    (hcover : V ≤ ⨆ i, U i) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, V)) (i : Fin n → ι)
      (g : ∀ j, Γ(X, U (i j))),
      PrimeSpectrum.IsStandardOpenCoverOfSpectrum f ∧
        (⨆ j, X.basicOpen (f j)) = V ∧
        ∀ j, X.basicOpen (f j) = X.basicOpen (g j) := by
  classical
  have hlocal : ∀ x : V, ∃ (i : ι) (f : Γ(X, V)) (g : Γ(X, U i)),
      X.basicOpen f = X.basicOpen g ∧ x.1 ∈ X.basicOpen f := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover x.2)
    obtain ⟨f, g, hfg, hx⟩ :=
      exists_basicOpen_le_affine_inter hV (hU i) x.1 ⟨x.2, hi⟩
    exact ⟨i, f, g, hfg, hfg ▸ hx⟩
  choose i₀ f₀ g₀ hfg₀ hx₀ using hlocal
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover
    (fun x : V => (X.basicOpen (f₀ x) : Set X))
    (fun x => (X.basicOpen (f₀ x)).2)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hx₀ ⟨x, hx⟩⟩)
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let f : Fin (Fintype.card t) → Γ(X, V) := fun j => f₀ (e.symm j)
  let i : Fin (Fintype.card t) → ι := fun j => i₀ (e.symm j)
  let g : ∀ j, Γ(X, U (i j)) := fun j => g₀ (e.symm j)
  have hcover' : (⨆ j, X.basicOpen (f j)) = V := by
    apply le_antisymm (iSup_le fun j => X.basicOpen_le _)
    intro x hx
    obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := ht hx
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    exact (le_iSup (fun j => X.basicOpen (f j)) (e ⟨y, hy⟩)) (by simpa [f] using hxy)
  refine ⟨Fintype.card t, f, i, g, ?_, hcover', fun j => hfg₀ (e.symm j)⟩
  show (⨆ j, PrimeSpectrum.basicOpen (f j)) = PrimeSpectrum.basicOpen (1 : Γ(X, V))
  rw [PrimeSpectrum.basicOpen_one]
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  apply (hV.iSup_basicOpen_eq_self_iff (s := Set.range f)).mp
  simpa only [iSup_range'] using hcover'

private lemma finitePresentationRel_of_basicOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) {n : ℕ} (r : Fin n → Γ(X, U))
    (hcover : (⨆ i, X.basicOpen (r i)) = U)
    (h : ∀ i, letI : Algebra Γ(S, V) Γ(X, X.basicOpen (r i)) :=
        (f.appLE V (X.basicOpen (r i)) ((X.basicOpen_le (r i)).trans hUV)).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, X.basicOpen (r i))
        Γ(M, X.basicOpen (r i))) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra;
    Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U) := by
  classical
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    apply (hU.iSup_basicOpen_eq_self_iff (s := Set.range r)).mp
    simpa only [iSup_range'] using hcover
  apply (Module.finitePresentationRel_iff_of_span_eq_top r hspan).mp
  intro i
  let : Algebra Γ(X, U) Γ(X, X.basicOpen (r i)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (r i))).op).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, X.basicOpen (r i)) :=
    (f.appLE V (X.basicOpen (r i))
      ((X.basicOpen_le (r i)).trans hUV)).hom.toAlgebra
  let : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, X.basicOpen (r i)) :=
    .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.appLE_map])
  let : Module Γ(X, U) Γ(M, X.basicOpen (r i)) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen (r i)))
  let : IsScalarTower Γ(X, U) Γ(X, X.basicOpen (r i))
      Γ(M, X.basicOpen (r i)) := IsScalarTower.of_compHom _ _ _
  let : IsLocalization.Away (r i) Γ(X, X.basicOpen (r i)) :=
    hU.isLocalization_basicOpen (r i)
  let : IsLocalizedModule.Away (r i) (basicOpenSectionMap M (r i)) :=
    Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ M hU (r i) rfl
      (X.basicOpen_le (r i))
  exact finitePresentationRel_localized_of_isLocalized (r i)
    (basicOpenSectionMap M (r i)) (h i)

private lemma finitePresentationRel_of_affineOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ f ⁻¹ᵁ V)
    (hcover : U ≤ ⨆ i, W i)
    (h : ∀ i, letI : Algebra Γ(S, V) Γ(X, W i) :=
        (f.appLE V (W i) (hWV i)).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, W i) Γ(M, W i)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra;
    Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U) := by
  classical
  obtain ⟨n, r, i, g, _, hrcover, heq⟩ :=
    exists_standard_refinement_of_le_iSup X W hW U hU hcover
  apply finitePresentationRel_of_basicOpenCover f M hU hV hUV r hrcover
  intro j
  have hLoc := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ M
    (hW (i j)) (g j) rfl (X.basicOpen_le (g j))
  have hj := finitePresentationRel_basicOpen_of_isLocalized f M (hW (i j))
    (hWV (i j)) (g j) hLoc (h (i j))
  let P : X.Opens → Prop := fun E =>
    ∀ (hEV : E ≤ f ⁻¹ᵁ V),
      let : Algebra Γ(S, V) Γ(X, E) := (f.appLE V E hEV).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, E) Γ(M, E)
  exact (congrArg P (heq j).symm).mp (fun _ => hj) ((X.basicOpen_le (r j)).trans hUV)

private lemma finitePresentationRel_over_base_basicOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent]
    {V : S.Opens} (hV : IsAffineOpen V) (b : Γ(S, V))
    {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i))
    (hWcover : (⨆ i, W i) = f ⁻¹ᵁ V)
    (h : ∀ i, letI : Algebra Γ(S, V) Γ(X, W i) :=
        (f.appLE V (W i) ((le_iSup W i).trans hWcover.le)).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, W i) Γ(M, W i))
    {T : X.Opens} (hT : IsAffineOpen T)
    (hTB : T ≤ f ⁻¹ᵁ (S.basicOpen b)) :
    letI : Algebra Γ(S, S.basicOpen b) Γ(X, T) :=
      (f.appLE (S.basicOpen b) T hTB).hom.toAlgebra;
    Module.FinitePresentationRel Γ(S, S.basicOpen b) Γ(X, T) Γ(M, T) := by
  classical
  let d : ∀ i, Γ(X, W i) := fun i => f.appLE V (W i)
    ((le_iSup W i).trans hWcover.le) b
  let W' : ι → X.Opens := fun i => X.basicOpen (d i)
  have hW' : ∀ i, IsAffineOpen (W' i) := fun i => (hW i).basicOpen (d i)
  have hW'B : ∀ i, W' i ≤ f ⁻¹ᵁ S.basicOpen b := fun i => basicOpen_appLE_le_preimage f _ b
  have hcover : T ≤ ⨆ i, W' i := by
    intro x hx
    have hxB : x ∈ f ⁻¹ᵁ S.basicOpen b := hTB hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hWcover.ge (f.preimage_mono (S.basicOpen_le b) hxB))
    exact Opens.mem_iSup.mpr ⟨i, (Scheme.basicOpen_appLE ..).ge ⟨hi, hxB⟩⟩
  apply finitePresentationRel_of_affineOpenCover f M hT (hV.basicOpen b)
    hTB W' hW' hW'B hcover
  intro i
  have hLoc := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ M
    (hW i) (d i) rfl (X.basicOpen_le (d i))
  have hi := finitePresentationRel_basicOpen_of_isLocalized f M
    (hW i) ((le_iSup W i).trans hWcover.le) (d i) hLoc (h i)
  exact (finitePresentationRel_iff_base_basicOpen f M (hW' i) hV b (hW'B i)).mp hi

private lemma of_affineSections
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (h : ∀ (U : X.Opens), IsAffineOpen U →
      ∀ (V : S.Opens), IsAffineOpen V →
        ∀ (hUV : U ≤ f ⁻¹ᵁ V),
          letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
          Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U)) :
    IsFinitelyPresentedRelative f M := by
  classical
  refine ⟨S.affineOpens, fun V => (V : S.Opens), ?_, fun V => V.property, fun V => ?_⟩
  · simpa [TopologicalSpace.IsOpenCover] using iSup_affineOpens_eq_top S
  · let I := {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)}
    let U : I → X.Opens := fun i => (i.1 : X.Opens)
    have hU : (⨆ i, U i) = f ⁻¹ᵁ (V : S.Opens) := by
      refine le_antisymm (iSup_le fun i => i.2) ?_
      rw [← SetLike.coe_subset_coe]
      intro x hx
      obtain ⟨W, hW, hxW, hWle⟩ :=
        exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ (V : S.Opens)) hx
      change (W : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens) at hWle
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
    exact ⟨I, U, hU, fun i => i.1.property,
      fun i => h (U i) i.1.property (V : S.Opens) V.property i.2⟩

/-- **Stacks Project, Tag 09T7.** A quasi-coherent module on a scheme locally of finite type
over a base is finitely presented relative to that base if and only if its sections over every
affine open are finitely presented relative to the sections over every compatible affine open
of the base. -/
@[stacks 09T7 "affine-open characterization"]
theorem isFinitelyPresentedRelative_iff_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsFinitelyPresentedRelative f M ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∀ (hUV : U ≤ f ⁻¹ᵁ V),
            letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
            Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(M, U) := by
  constructor
  · intro h U hU V hV hUV
    classical
    obtain ⟨J, V₀, hV₀cover, hV₀, hcharts⟩ := h
    obtain ⟨n, b, j, c, _, hbcover, heq⟩ :=
      Scheme.exists_isStandardOpenCover_basicOpen_eq_of_iSup_eq_top
        S V₀ hV₀ hV₀cover V hV
    let r : Fin n → Γ(X, U) := fun k => f.appLE V U hUV (b k)
    have hrcover : (⨆ k, X.basicOpen (r k)) = U := by
      apply le_antisymm (iSup_le fun k => X.basicOpen_le (r k))
      intro x hx
      have hfxCover : x ∈ f ⁻¹ᵁ (⨆ k, S.basicOpen (b k)) := by
        rw [hbcover]
        exact hUV hx
      rw [f.preimage_iSup] at hfxCover
      obtain ⟨k, hxk⟩ := Opens.mem_iSup.mp hfxCover
      exact Opens.mem_iSup.mpr ⟨k, (Scheme.basicOpen_appLE ..).ge ⟨hx, hxk⟩⟩
    apply finitePresentationRel_of_basicOpenCover f M hU hV hUV r hrcover
    intro k
    have hrB : X.basicOpen (r k) ≤ f ⁻¹ᵁ S.basicOpen (b k) :=
      basicOpen_appLE_le_preimage f hUV (b k)
    have hrC : X.basicOpen (r k) ≤ f ⁻¹ᵁ S.basicOpen (c k) := by rwa [← heq k]
    obtain ⟨I, W, hWcover, hWaff, hWfp⟩ := hcharts (j k)
    have hC := finitePresentationRel_over_base_basicOpen f M
      (hV₀ (j k)) (c k) W hWaff hWcover hWfp
      (hU.basicOpen (r k)) hrC
    let P : S.Opens → Prop := fun B =>
      ∀ (hTB : X.basicOpen (r k) ≤ f ⁻¹ᵁ B),
        let : Algebra Γ(S, B) Γ(X, X.basicOpen (r k)) :=
          (f.appLE B (X.basicOpen (r k)) hTB).hom.toAlgebra;
        Module.FinitePresentationRel Γ(S, B) Γ(X, X.basicOpen (r k))
          Γ(M, X.basicOpen (r k))
    exact (finitePresentationRel_iff_base_basicOpen f M
      (hU.basicOpen (r k)) hV (b k) hrB).mpr ((congrArg P (heq k).symm).mp (fun _ => hC) hrB)
  · exact of_affineSections f M

/-- **Stacks Project, Tag 09T7.** Once a quasi-coherent module is finitely presented relative
to a base, its restriction to any open subscheme is finitely presented relative to every
compatible open subscheme of the base. -/
@[stacks 09T7 "restriction to open subschemes"]
theorem isFinitelyPresentedRelative_resLE
    {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (M : X.Modules) [M.IsQuasicoherent]
    (hM : IsFinitelyPresentedRelative f M)
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    IsFinitelyPresentedRelative (f.resLE V U hUV) (M.restrict U.ι) := by
  apply (isFinitelyPresentedRelative_iff_affine (f.resLE V U hUV) (M.restrict U.ι)).2
  intro W hW T hT hWT
  have hWT' : U.ι ''ᵁ W ≤ f ⁻¹ᵁ (V.ι ''ᵁ T) :=
    (f.le_resLE_preimage_iff hUV T W).mp hWT
  have h := (isFinitelyPresentedRelative_iff_affine f M).1 hM
    (U.ι ''ᵁ W) (hW.image_of_isOpenImmersion U.ι) (V.ι ''ᵁ T)
    (hT.image_of_isOpenImmersion V.ι) hWT'
  let : Module Γ(U, W) Γ(M, U.ι ''ᵁ W) := by
    show Module Γ(X, U.ι ''ᵁ W) Γ(M, U.ι ''ᵁ W)
    infer_instance
  let e : Γ(M.restrict U.ι, W) ≃ₗ[Γ(U, W)] Γ(M, U.ι ''ᵁ W) :=
    { (M.restrictAppIso U.ι W).addCommGroupIsoToAddEquiv with
      map_smul' := fun r m => by
        show (M.restrictAppIso U.ι W).hom (r • m) =
          r • (M.restrictAppIso U.ι W).hom m
        have hr : (U.ι.appIso W).inv r = r := by
          rw [Scheme.Opens.ι_appIso]
          exact CategoryTheory.id_apply r
        have h0 := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M W r m
        rwa [hr] at h0 }
  rw [Scheme.Hom.resLE_appLE]
  let : Algebra Γ(V, T) Γ(U, W) :=
    (f.appLE (V.ι ''ᵁ T) (U.ι ''ᵁ W) hWT').hom.toAlgebra
  exact finitePresentationRel_of_linearEquiv e.symm h

end AlgebraicGeometry
