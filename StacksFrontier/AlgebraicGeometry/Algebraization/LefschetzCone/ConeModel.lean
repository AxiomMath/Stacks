module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ChartDegreeZero
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.FiniteSheaves
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ChartTorsion

/-!
# The punctured affine cone over `P` and the coherent formal module it carries

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L` for which the canonical morphism
`X ⟶ Proj A`, `A = Γ_*(X, L)`, is an isomorphism and `A` is Noetherian, let `s` be a global
section of `L` and `f ∈ A₁` its image. The algebraization situation of the proof of Stacks 0EL5
is `(A, I = (f), 𝔞 = A₊)`: its open `U = Spec(A) ∖ V(A₊)` is the punctured affine cone over `X`.

Let `(Tₙ)` be an inverse system of graded `A`-modules whose sheaves `(T̃ₙ|_X)` form an object of
`Coh(X, 𝓘)`, `𝓘` the ideal of the zero scheme of `s`, every `Tₙ` being finite. Then the system
`(Tₙ / fⁿ⁺¹ Tₙ)` is a finite module model in the sense of Stacks 0DXT, so its sheaves on `U` form
an object of `Coh(U, I𝒪_U)`.

The two torsion conditions of a finite module model are checked on the degree-zero localizations
at the products `g = cb` of the charts of consecutive degrees. There the transitions of `(Tₙ)` are
surjective with kernel `wⁿ⁺¹ Tₙ₊₁₍g₎` (`Stacks.LefschetzCone.ChartDegreeZero`), which gives, after
a power of `g`, surjectivity and the description of the kernel in `Tₙ₊₁` itself
(`Stacks.DegreeOneUnitAway.ChartTorsion`); every prime off `V(A₊)` misses one of these `g`, so the
kernel and cokernel are `A₊`-power torsion.

## Main definitions

* `Stacks.LefschetzCone.coneSituation`: the algebraization situation `(Γ_*(X, L), (f), A₊)`.
* `Stacks.LefschetzCone.truncatedSystem`: the system `(Tₙ / fⁿ⁺¹ Tₙ)`.

## Main results

* `Stacks.LefschetzCone.isFiniteModuleModel_truncatedSystem`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization Pointwise

universe u

namespace Stacks.LefschetzCone

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤))

/-- The section `f` lies in the irrelevant ideal. -/
theorem sectionElt_mem_irrelevant :
    sectionElt L s ∈ (HomogeneousIdeal.irrelevant (grading L)).toIdeal :=
  HomogeneousIdeal.mem_irrelevant_of_mem (grading L) Nat.one_pos (sectionElt_mem L s)

/-- **The algebraization situation of the proof of Stacks 0EL5**: the section ring
`A = Γ_*(X, L)`, the ideal `I = (f)` of the section `f ∈ A₁` and `𝔞 = A₊`. -/
abbrev coneSituation [IsNoetherianRing (sectionRing L)] :
    Stacks.Algebraization.AlgebraizationSituation.{u} where
  A := sectionRing L
  I := Ideal.span {sectionElt L s}
  a := (HomogeneousIdeal.irrelevant (grading L)).toIdeal
  I_le_a := (Ideal.span_singleton_le_iff_mem _).2 (sectionElt_mem_irrelevant L s)

/-- The powers of `(f)` times a submodule decrease. -/
theorem pow_succ_smul_top_le_comap {N N' : GradedModuleCat.{u, u, u} (grading L)} (φ : N ⟶ N')
    {n m : ℕ} (h : n ≤ m) :
    Ideal.span {sectionElt L s} ^ (m + 1) • (⊤ : Submodule (sectionRing L) N.carrier) ≤
      (Ideal.span {sectionElt L s} ^ (n + 1) •
        (⊤ : Submodule (sectionRing L) N'.carrier)).comap φ.toLinearMap := by
  exact (Submodule.smul_top_le_comap_smul_top _ φ.toLinearMap).trans
    (Submodule.comap_mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.succ_le_succ h))))

/-- The map `N / fᵐ⁺¹N ⟶ N' / fⁿ⁺¹N'` induced by a degree-preserving map, for `n ≤ m`. -/
def powQuotientMap {N N' : GradedModuleCat.{u, u, u} (grading L)} (φ : N ⟶ N') {n m : ℕ}
    (h : n ≤ m) : powQuotient L s N (m + 1) ⟶ powQuotient L s N' (n + 1) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (pow_succ_smul_top_le_comap L s φ h)
  map_grade := by
    rintro _ _ ⟨x, hx, rfl⟩
    exact ⟨φ.toLinearMap x, φ.map_grade _ x hx, rfl⟩

/-- The map `powQuotientMap L s φ h` sends the class of `x` to the class of `φ x`. -/
theorem powQuotientMap_mk {N N' : GradedModuleCat.{u, u, u} (grading L)} (φ : N ⟶ N') {n m : ℕ}
    (h : n ≤ m) (x : N.carrier) :
    (powQuotientMap L s φ h).toLinearMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.toLinearMap x) :=
  rfl

/-- **The system `(Tₙ / fⁿ⁺¹ Tₙ)`.** -/
def truncatedSystem (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L)) :
    ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L) where
  obj n := powQuotient L s (T.obj n) (n.unop + 1)
  map {n m} f := powQuotientMap L s (T.map f) (leOfHom f.unop)
  map_id n := GradedModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    change Submodule.Quotient.mk ((T.map (𝟙 n)).toLinearMap x) = Submodule.Quotient.mk x
    rw [T.map_id]
    rfl))
  map_comp {n m k} f g := GradedModuleCat.hom_ext (Submodule.linearMap_qext _
    (LinearMap.ext fun x => by
      change Submodule.Quotient.mk ((T.map (f ≫ g)).toLinearMap x) =
        Submodule.Quotient.mk ((T.map g).toLinearMap ((T.map f).toLinearMap x))
      rw [T.map_comp]
      rfl))

/-- A transition of `truncatedSystem L s T` sends the class of `x` to the class of the image of
`x` under the corresponding transition of `T`. -/
theorem truncatedSystem_map_mk (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L)) {n m : ℕᵒᵖ}
    (f : n ⟶ m) (x : (T.obj n).carrier) :
    ((truncatedSystem L s T).map f).toLinearMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((T.map f).toLinearMap x) :=
  rfl

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- A quotient by `J • ⊤` is killed by `J`. -/
theorem smul_top_quotient_eq_bot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) : (J • (⊤ : Submodule R (M ⧸ J • (⊤ : Submodule R M)))) = ⊥ := by
  refine eq_bot_iff.2 (Submodule.smul_le.2 fun a ha x _ => ?_)
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

variable (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)]

/-- A multiple of `(f)ᵏ` maps into `(f)ᵏ` times the quotient. -/
theorem mkQ_mem_pow_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) (K : Submodule R M) {x : M} (hx : x ∈ J • (⊤ : Submodule R M)) :
    K.mkQ x ∈ J • (⊤ : Submodule R (M ⧸ K)) := by
  exact Submodule.smul_top_le_comap_smul_top J K.mkQ hx

include hL in
/-- The primes off `V(A₊)` miss the products of the charts of consecutive degrees. -/
theorem exists_mem_range_gR_notMem (p : Ideal (sectionRing L)) (hp : p.IsPrime)
    (hnot : ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ p) :
    ∃ g ∈ Set.range (fun ch : ConsecutiveChart L => ch.gR), g ∉ p := by
  obtain ⟨ch, hch⟩ := exists_consecutiveChart_notMem hL p hp hnot
  exact ⟨_, ⟨ch, rfl⟩, hch⟩

/-- **Surjectivity of a transition up to a power of `g`.** -/
theorem exists_pow_smul_mem_range_transition (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) (n : ℕ) (ch : ConsecutiveChart L)
    (y : (T.obj (op n)).carrier) :
    ∃ q : ℕ, ch.gR ^ q • y ∈
      LinearMap.range (T.map (homOfLE (Nat.le_succ n)).op).toLinearMap := by
  have : Epi ((restrictedTildeFunctor L hL).map (T.map (homOfLE (Nat.le_succ n)).op)) :=
    hT.epi_map_succ n
  refine Stacks.DegreeOneUnitAway.exists_pow_smul_mem_range (𝓜 := (T.obj (op (n + 1))).grade)
    (𝓝 := (T.obj (op n)).grade) ch.cR_mem ch.bR_mem ch.cR_mul_bR _ (fun z hz => ?_) y
  obtain ⟨z', hz'⟩ := exists_map_eq_of_epi (T.map (homOfLE (Nat.le_succ n)).op) ch ⟨z, hz⟩
  exact ⟨z', z'.2, hz'⟩

/-- **The kernel of a transition up to a power of `g`.** -/
theorem exists_pow_smul_mem_of_transition_eq_zero
    (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) (n : ℕ) (ch : ConsecutiveChart L)
    {x : (T.obj (op (n + 1))).carrier}
    (hx : (T.map (homOfLE (Nat.le_succ n)).op).toLinearMap x = 0) :
    ∃ p : ℕ, ch.gR ^ p • x ∈ Ideal.span {sectionElt L s} ^ (n + 1) •
      (⊤ : Submodule (sectionRing L) (T.obj (op (n + 1))).carrier) := by
  refine Stacks.DegreeOneUnitAway.exists_pow_smul_mem_of_map_eq_zero
    (𝓜 := (T.obj (op (n + 1))).grade) (𝓝 := (T.obj (op n)).grade) ch.cR_mem ch.bR_mem
    ch.cR_mul_bR (sectionElt_mem L s) (n + 1) _
    (T.map (homOfLE (Nat.le_succ n)).op).map_grade (fun z hz hz0 => ?_) hx
  obtain ⟨z', hz'⟩ := exists_eq_chartRatio_pow_smul_of_map_eq_zero L hL s T hT n ch ⟨z, hz⟩ hz0
  exact ⟨z', z'.2, congrArg Subtype.val hz'⟩

/-- **`(Tₙ / fⁿ⁺¹ Tₙ)` is a finite module model** (Stacks 0DXT) on the punctured cone, for an
inverse system `(Tₙ)` of finite graded modules whose sheaves on `X` form a coherent adic system
along the zero scheme of `s`. -/
public theorem isFiniteModuleModel_truncatedSystem [IsNoetherianRing (sectionRing L)]
    (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L) (T.obj (op n)).carrier) :
    Stacks.Algebraization.IsFiniteModuleModel (coneSituation L s)
      (truncatedSystem L s T ⋙ GradedModuleCat.toModuleCat (grading L)) := by
  set J : Ideal (sectionRing L) := Ideal.span {sectionElt L s} with hJ
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have := hfin n
    exact Module.Finite.quotient (sectionRing L) _
  · exact smul_top_quotient_eq_bot (J ^ (n + 1))
  · exact Stacks.DegreeOneUnitAway.exists_liftQ_isIPowerTorsion
      (T.map (homOfLE (Nat.le_succ n)).op).toLinearMap J _ (IsNoetherian.noetherian _) n _
      (exists_mem_range_gR_notMem L hL)
      (fun g hg y => by
        obtain ⟨ch, rfl⟩ := hg
        exact exists_pow_smul_mem_range_transition L s hL T hT n ch y)
      (fun g hg x hx => by
        obtain ⟨ch, rfl⟩ := hg
        exact exists_pow_smul_mem_of_transition_eq_zero L s hL T hT n ch hx)
      _ (fun _ => rfl)

end Monoidal

end Stacks.LefschetzCone

end
