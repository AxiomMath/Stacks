module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulStalk
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartRegular
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackStalkBasis
public import StacksFrontier.LinearAlgebra.Basis.KernelOfRankOneQuotient
public import StacksFrontier.LinearAlgebra.ExteriorPower.KoszulExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelRank
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle

/-!
# Exactness of the Koszul complex of the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])` with tautological surjection `u : π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1)`, its
kernel `𝒦` of rank `r` and `φ : 𝒦 ⟶ 𝒪_E` the restriction of the projection to `π^*𝒪_X = 𝒪_E`.
The Koszul complex of `φ` is exact in positive homological degrees.

## Main results

* `Stacks.Chow.ProjectiveCompletion.exists_basis_stalkDual`: at a point `ξ` of the image `W` of
  the chart `D₊(T)` over an affine open `V`, the stalk `𝒦_ξ` has a basis on which `φ_ξ` takes the
  values `y_j`.
* `Stacks.Chow.ProjectiveCompletion.exactAt_koszulChain`: the Koszul complex of `φ` is exact in
  positive homological degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V : X.Opens}
  (hV : IsAffineOpen V)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The basis `(b_j, T)` of the sections of `𝒞 ⊕ 𝒪_X` over `V` given by a basis `b` of the
sections of `𝒞`. -/
def sectionsBasis {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V)) :
    Module.Basis (Fin r ⊕ Unit) Γ(X, V) Γ(module 𝒞, V) :=
  (b.prod (Module.Basis.singleton Unit Γ(X, V))).map (sectionsSplit 𝒞 V).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- The basis vector of `sectionsBasis 𝒞 b` indexed by `j` is the image of `b j` under the
inclusion `𝒞 ⟶ 𝒞 ⊕ 𝒪_X`. -/
theorem sectionsBasis_inl {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V)) (j : Fin r) :
    sectionsBasis 𝒞 b (.inl j) = Scheme.Modules.Hom.app (inl 𝒞) V (b j) := by
  have h : (b.prod (Module.Basis.singleton Unit Γ(X, V))) (.inl j) = (b j, 0) := by
    ext <;> simp [Module.Basis.prod_apply]
  rw [sectionsBasis, Module.Basis.map_apply, h]
  change Scheme.Modules.Hom.app (inl 𝒞) V (b j) +
    Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V 0) = _
  rw [show toUnitM V (0 : Γ(X, V)) = 0 from rfl, map_zero, add_zero]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- The last basis vector of `sectionsBasis 𝒞 b` is the restriction to `V` of the global
section `T` of `𝒞 ⊕ 𝒪_X`. -/
theorem sectionsBasis_inr {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V)) :
    sectionsBasis 𝒞 b (.inr ()) =
      (module 𝒞).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (sectionT 𝒞) := by
  rw [sectionT_restrict]
  have h : (b.prod (Module.Basis.singleton Unit Γ(X, V))) (.inr ()) =
      (0, Module.Basis.singleton Unit Γ(X, V) ()) := by
    ext <;> simp [Module.Basis.prod_apply]
  rw [sectionsBasis, Module.Basis.map_apply, h]
  change Scheme.Modules.Hom.app (inl 𝒞) V 0 +
    Scheme.Modules.Hom.app (inr 𝒞) V (toUnitM V (Module.Basis.singleton Unit Γ(X, V) ())) = _
  rw [map_zero, zero_add, Module.Basis.singleton_apply]

/-- In a short exact sequence of modules the composite of the two maps vanishes, read on
elements. -/
theorem moduleCat_g_f_apply {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{u} R)}
    (_h : S.ShortExact) (x : S.X₁) : S.g (S.f x) = 0 :=
  S.moduleCat_zero_apply x

/-- The germ at a point of `W` of `π^*x`, for a section `x` of `𝒞 ⊕ 𝒪_X` over `V`, is the germ of
its restriction to `W`. -/
theorem germ_pullRes_openW (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) (x : Γ(module 𝒞, V)) :
    ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ (openW 𝒞 hV) ξ hξ
        (pullRes 𝒞 (openW_le 𝒞 hV) x) =
      ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ
        (openW_le 𝒞 hV hξ) (unitSection (proj 𝒞) (module 𝒞) V x) :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE (openW_le 𝒞 hV)) ξ hξ _

/-- `u_ξ` on the germ of `π^*x` at a point of `W`. -/
theorem stalkMapL_taut_germ (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) (x : Γ(module 𝒞, V)) :
    PresheafOfModules.stalkMapL ξ (taut 𝒞).val
        (((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ
          (openW_le 𝒞 hV hξ) (unitSection (proj 𝒞) (module 𝒞) V x)) =
      (twist 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ
        ((twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op
          (((twistData 𝒞).ψ 1).val.app (op V)
            ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V) x))) := by
  refine (PresheafOfModules.stalkMapL_germ ξ (taut 𝒞).val (proj 𝒞 ⁻¹ᵁ V) (openW_le 𝒞 hV hξ)
    _).trans ?_
  refine (congrArg _ (taut_unitSection 𝒞 V x)).trans ?_
  exact (TopCat.Presheaf.germ_res_apply _ (homOfLE (openW_le 𝒞 hV)) ξ hξ _).symm

/-- The projection to `𝒪_E` on the germ of `π^*x`. -/
theorem stalkDual_sndUnit_germ (ξ : space 𝒞) (hξ : (proj 𝒞).base ξ ∈ V)
    (x : Γ(module 𝒞, V)) :
    Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ
        (((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ
          hξ (unitSection (proj 𝒞) (module 𝒞) V x)) =
      (space 𝒞).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ hξ
        ((proj 𝒞).app V (Scheme.Modules.Hom.app (snd 𝒞) V x)) :=
  (Stacks.KoszulStalk.stalkDual_germ (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ _ hξ _).trans
    (congrArg _ (sndUnit_unitSection 𝒞 V x))

/-- The germ at a point of `W` of the degree-one section `T` of `𝒪_E(1)`. -/
def germT (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) :
    ↑(TopCat.Presheaf.stalk (twist 𝒞).val.presheaf ξ) :=
  (twist 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ
    ((twist 𝒞).presheaf.map (homOfLE (openW_le 𝒞 hV)).op
      (((twistData 𝒞).ψ 1).val.app (op V)
        ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
          ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞)))))

/-- **The stalk of `π^*(𝒞 ⊕ 𝒪_X)` at a point of `W`** has the basis of germs of `π^*b_j` and
`π^*T`, on which `u_ξ` takes the values `y_j u(π^*T)` and `u(π^*T)`. -/
theorem exists_basis_taut {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V))
    (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) :
    ∃ f : Module.Basis (Fin r ⊕ Unit) ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
      ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).val.presheaf ξ),
      (∀ i, f i = ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ
        (proj 𝒞 ⁻¹ᵁ V) ξ (openW_le 𝒞 hV hξ)
          (unitSection (proj 𝒞) (module 𝒞) V (sectionsBasis 𝒞 b i))) ∧
      PresheafOfModules.stalkMapL (R := (space 𝒞).sheaf.obj) ξ (taut 𝒞).val (f (.inr ())) =
        germT 𝒞 hV ξ hξ ∧
      ∀ j, PresheafOfModules.stalkMapL (R := (space 𝒞).sheaf.obj) ξ (taut 𝒞).val (f (.inl j)) =
        (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ (coordY 𝒞 hV (b j)) • germT 𝒞 hV ξ hξ := by
  have hξV : (proj 𝒞).base ξ ∈ V := openW_le 𝒞 hV hξ
  refine (show ∃ f : Module.Basis (Fin r ⊕ Unit)
      ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
      ↑(TopCat.Presheaf.stalk ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).val.presheaf ξ),
      ∀ i, f i = ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ
        (proj 𝒞 ⁻¹ᵁ V) ξ hξV (unitSection (proj 𝒞) (module 𝒞) V (sectionsBasis 𝒞 b i)) from
    ⟨Stacks.ModuleStalkSpecialization.pullbackStalkBasis (module 𝒞) hV (sectionsBasis 𝒞 b)
      (proj 𝒞) hξV, Stacks.ModuleStalkSpecialization.pullbackStalkBasis_apply (module 𝒞) hV
      (sectionsBasis 𝒞 b) (proj 𝒞) hξV⟩).elim fun f hfx => ⟨f, hfx, ?_, fun j => ?_⟩
  · rw [hfx, sectionsBasis_inr]
    exact stalkMapL_taut_germ 𝒞 hV ξ hξ _
  · rw [hfx, sectionsBasis_inl, stalkMapL_taut_germ 𝒞 hV ξ hξ]
    refine (congrArg _ (psi_restrict_openW 𝒞 hV (b j))).trans ?_
    exact Stacks.ModuleStalkSpecialization.germ_smul (twist 𝒞) hξ _ _

/-- **`u(π^*T)` generates `𝒪_E(1)` at the points of `W`**: its germ is a stalk basis. -/
theorem bijective_smul_germT {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V))
    (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) :
    Function.Bijective fun c : ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ) =>
      c • germT 𝒞 hV ξ hξ := by
  have hS := (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).1
    (shortExact_taut 𝒞) ξ
  refine (exists_basis_taut 𝒞 hV b ξ hξ).elim fun f hf => ?_
  obtain ⟨-, hu_inr, hu_inl⟩ := hf
  have hsurj : Function.Surjective fun c : ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ) =>
      c • germT 𝒞 hV ξ hξ := by
    intro z
    obtain ⟨p, rfl⟩ := hS.moduleCat_surjective_g z
    refine ⟨(∑ j, f.repr p (.inl j) * (show ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ) from
      (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ (coordY 𝒞 hV (b j)))) + f.repr p (.inr ()), ?_⟩
    change _ = PresheafOfModules.stalkMapL (R := (space 𝒞).sheaf.obj) ξ (taut 𝒞).val p
    conv_rhs => rw [← f.sum_repr p]
    rw [map_sum, Fintype.sum_sum_type]
    simp only [Finset.univ_unique, Finset.sum_singleton, map_smul, hu_inl, hu_inr,
      add_smul, Finset.sum_smul]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => mul_smul _ _ _) rfl
  have := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (twist 𝒞) (isInvertible_twist 𝒞)
  obtain ⟨eL⟩ := Stacks.SheafOfModules.TopWedge.nonempty_stalkLinearEquiv_finsupp
    (Osharp := (space 𝒞).sheaf) (twist 𝒞) 1 ξ
  exact ⟨injective_smul_of_surjective_smul
    (eL.trans (Finsupp.uniqueLinearEquiv _ _ (0 : Fin 1))) hsurj, hsurj⟩

/-- **The stalk of `𝒦` at a point of `W`**: it has a basis on which `φ_ξ` takes the values
`y_{b_j}`. -/
theorem exists_basis_stalkDual {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V))
    (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) :
    ∃ e : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
        ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ),
      ∀ j, Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
          (koszulMap 𝒞) ξ (e j) =
        (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ (coordY 𝒞 hV (b j)) := by
  have hξV : (proj 𝒞).base ξ ∈ V := openW_le 𝒞 hV hξ
  have hS := (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).1
    (shortExact_taut 𝒞) ξ
  set u := PresheafOfModules.stalkMapL (R := (space 𝒞).sheaf.obj) ξ (taut 𝒞).val with hu
  set κ := PresheafOfModules.stalkMapL (R := (space 𝒞).sheaf.obj) ξ (kernel.ι (taut 𝒞)).val
    with hκ
  set y : Fin r → ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ) := fun j =>
    (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ (coordY 𝒞 hV (b j)) with hy
  refine (exists_basis_taut 𝒞 hV b ξ hξ).elim fun f hf => ?_
  obtain ⟨hfx, hu_inr, hu_inl⟩ := hf
  have hinj := (bijective_smul_germT 𝒞 hV b ξ hξ).1
  rw [← hu_inr] at hinj
  have hu_inl' : ∀ j, u (f (.inl j)) = y j • u (f (.inr ())) := fun j =>
    (hu_inl j).trans (congrArg (y j • ·) hu_inr.symm)
  obtain ⟨e, he⟩ := Module.Basis.exists_basis_of_ker f u κ hS.moduleCat_injective_f
    (fun k => moduleCat_g_f_apply hS k)
    (fun p hp => (ShortComplex.moduleCat_exact_iff _).1 hS.exact p hp) y hu_inl'
    (fun c hc => hinj (show c • u (f (.inr ())) = (0 : _) • u (f (.inr ())) from
      hc.trans (zero_smul _ _).symm))
  refine ⟨e, fun j => ?_⟩
  have h1 := stalkDual_koszulMap 𝒞 ξ (e j)
  have h2 := congrArg (Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ)
    (he j)
  have key : ∀ (i) (x : Γ(module 𝒞, V)), f i =
      ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ hξV
        (unitSection (proj 𝒞) (module 𝒞) V x) →
      Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ (f i) =
        (space 𝒞).presheaf.germ (proj 𝒞 ⁻¹ᵁ V) ξ hξV
          ((proj 𝒞).app V (Scheme.Modules.Hom.app (snd 𝒞) V x)) := fun i x h =>
    (congrArg _ h).trans (stalkDual_sndUnit_germ 𝒞 ξ hξV x)
  have h5 : Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ
      (f (.inr ())) = 1 := by
    rw [key _ _ (by rw [hfx, sectionsBasis_inr]), snd_sectionT]
    change (space 𝒞).presheaf.germ _ ξ hξV ((proj 𝒞).app V (1 : Γ(X, V))) = 1
    rw [map_one, map_one]
  have h6 : Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (sndUnit 𝒞) ξ
      (f (.inl j)) = 0 := by
    rw [key _ _ (by rw [hfx, sectionsBasis_inl]), snd_inl]
    change (space 𝒞).presheaf.germ _ ξ hξV ((proj 𝒞).app V (0 : Γ(X, V))) = 0
    rw [map_zero, map_zero]
  refine h1.trans (h2.trans ?_)
  rw [map_sub, map_smul, h5, h6, sub_zero, smul_eq_mul, mul_one]

/-- **The chart over `V` is covered by `D₊(T)` and the `D₊(b_k)`**, for a basis `b` of the
sections of `𝒞` over `V`. -/
theorem mem_chartD_or_exists_mem_basicOpen {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V))
    (x : AlgebraicGeometry.Proj ((symAlg 𝒞).grading V)) (hV : IsAffineOpen V) :
    x ∈ chartD 𝒞 (V := V) ∨ ∃ k, x ∈ AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
      ((chartE 𝒞 (b k) : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) := by
  have hcov := AlgebraicGeometry.Proj.iSup_basicOpen_eq_top' ((symAlg 𝒞).grading V)
    (ι := (symAlg 𝒞).grading V 1) (fun a => (a : (symAlg 𝒞).sectionRing V))
    (fun a => ⟨1, a.2⟩) (by
      rw [Subtype.range_coe_subtype]
      exact adjoin_grading_one_eq_top (module 𝒞) V (bundlePieces (module 𝒞)) hV)
  have hx : x ∈ (⊤ : (AlgebraicGeometry.Proj ((symAlg 𝒞).grading V)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨a, ha⟩ := hx
  by_contra! ⟨hT, he⟩
  rw [AlgebraicGeometry.Proj.mem_basicOpen, not_not] at hT
  have he' : ∀ k, ((chartE 𝒞 (b k) : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) ∈
      x.asHomogeneousIdeal := fun k => by
    simpa only [AlgebraicGeometry.Proj.mem_basicOpen, not_not] using he k
  rw [AlgebraicGeometry.Proj.mem_basicOpen] at ha
  apply ha
  have hmem : chartRingHom 𝒞 hV (a : (symAlg 𝒞).sectionRing V) ∈
      SymPow.symmetricPower 1 Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) := (chartGradedHom 𝒞 hV).map_mem a.2
  rw [SymPow.symmetricPower, pow_one] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hpdec : SymmetricAlgebra.ι Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) p =
      (∑ k, algebraMap Γ(X, V) _ (b.repr p.1 k) *
          SymmetricAlgebra.ι Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) (b k, 0)) +
        algebraMap Γ(X, V) _ p.2 * Stacks.SymAdjoinChart.adjoinedGen Γ(X, V) Γ(𝒞, V) := by
    have h1 : p = (∑ k, b.repr p.1 k • ((b k, 0) : Γ(𝒞, V) × Γ(X, V))) + p.2 • (0, 1) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_zero, add_zero]
        exact (b.sum_repr p.1).symm
      · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, Finset.sum_const_zero,
          zero_add, smul_eq_mul, mul_one, mul_zero]
    conv_lhs => rw [h1]
    simp only [map_add, map_sum, map_smul, Algebra.smul_def]
    rfl
  have ha' : (a : (symAlg 𝒞).sectionRing V) =
      chartRingInv 𝒞 hV (SymmetricAlgebra.ι Γ(X, V) (Γ(𝒞, V) × Γ(X, V)) p) := by
    rw [hp, chartRingInv_chartRingHom]
  rw [ha', hpdec, map_add, map_sum, map_mul, chartRingInv_adjoinedGen]
  refine Ideal.add_mem _ (Ideal.sum_mem _ fun k _ => ?_) (Ideal.mul_mem_left _ _ hT)
  rw [map_mul, chartRingInv_ι]
  exact Ideal.mul_mem_left _ _ (he' k)

/-- **The Koszul complex of `φ_ξ` is exact in positive degrees at every point `ξ` of `E`**, for
`𝒞` of rank `r`. -/
theorem exists_contraction_stalkDual_eq {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] (ξ : space 𝒞)
    (n : ℕ) (z) (hz : exteriorPower.contraction (Stacks.KoszulStalk.stalkDual
      (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞) (koszulMap 𝒞) ξ) n z = 0) :
    ∃ w, exteriorPower.contraction (Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
      (M := kernelModule 𝒞) (koszulMap 𝒞) ξ) (n + 1) w = z := by
  have : 𝒞.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  have hex : ∃ V : X.Opens, IsAffineOpen V ∧ (proj 𝒞).base ξ ∈ V ∧
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V)) :=
    exists_isAffineOpen_basis_sections 𝒞 r ((proj 𝒞).base ξ)
  obtain ⟨V, hV, hξV, ⟨b⟩⟩ := hex
  have hξ : ξ ∈ chart 𝒞 V hV ''ᵁ ⊤ := by rwa [chart_image_top_eq]
  have hr : ξ ∈ Set.range (chart 𝒞 V hV) := by
    rwa [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.image_top_eq_opensRange]
  obtain ⟨ζ, hζ⟩ := hr
  refine (mem_chartD_or_exists_mem_basicOpen 𝒞 b ζ hV).elim (fun h => ?_) (fun hk => ?_)
  · have hW : ξ ∈ openW 𝒞 hV := by
      rw [← hζ]
      exact (Scheme.Hom.apply_mem_image_iff _).2 h
    refine (exists_basis_stalkDual 𝒞 hV b ξ hW).elim fun e he => ?_
    refine exteriorPower.exists_contraction_eq_of_isKoszulRegular _ e ?_ n z hz
    have hfun : (fun j => Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
        (M := kernelModule 𝒞) (koszulMap 𝒞) ξ (e j)) = fun j =>
          (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hW (coordY 𝒞 hV (b j)) := funext he
    rw [hfun]
    exact isKoszulRegular_germ_coordY 𝒞 hV b ξ hW
  · obtain ⟨k, hk⟩ := hk
    have hk' : ξ ∈ chartOpen 𝒞 hV (chartE 𝒞 (b k)) := by
      rw [← hζ]
      exact (Scheme.Hom.apply_mem_image_iff _).2 hk
    exact (exists_stalkDual_eq_one 𝒞 hV (b k) ξ hk').elim fun v hv =>
      exteriorPower.exists_contraction_eq_of_eq_one _ hv n z hz

/-- **The Koszul complex of `φ : 𝒦 ⟶ 𝒪_E` is exact in positive homological degrees.** -/
theorem exactAt_koszulChain {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] (n : ℕ) :
    (Scheme.Modules.koszulChain (kernelModule 𝒞) (koszulMap 𝒞)).ExactAt (n + 1) :=
  Scheme.Modules.exactAt_koszulChain_of_stalk (kernelModule 𝒞) (koszulMap 𝒞) n
    fun ξ z hz => exists_contraction_stalkDual_eq 𝒞 (r := r) ξ n z hz


end Stacks.Chow.ProjectiveCompletion
