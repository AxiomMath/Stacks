module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalFibre
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness

/-!
# The ring `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`

For a morphism `g : X ⟶ V` from an algebraic space to an affine Noetherian object of the site and
an ideal `I ⊆ A = Γ(V, 𝒪_V)`, this file defines the ring
`C^∧ = lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`
of compatible families of functions on the fibres. In the proof of Stacks 0GI5 this is the ring
`C_μ^∧ = lim_n H⁰(V'_μ ×_{V_μ} Z_{μ, n}, 𝒪)`. It comes with:

* the ring map `α : A^∧ ⟶ C^∧`;
* the ring map `ψ_F : B ⟶ C^∧` of a morphism `F : X_{/g⁻¹ V(I)} ⟶ Spf B`, which determines `F`;
* the filtration `F_n C^∧` of the families vanishing on the first `n` fibres. It is separated,
  `α` maps `I^n A^∧` into it, and `ψ_F` is continuous for it.

For `F` given by a continuous `φ : B → A^∧` through `X_{/g⁻¹ V(I)} ⟶ V_{/V(I)} ≅ Spf A^∧`, one has
`ψ_F = α ∘ φ` (`FormalRing.towerRingHom_completionSheafRestrict_comp_continuousHomEquiv`).

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `I`-adic topology on the completion `A^∧` of `A`. -/
local instance instTopologicalSpaceAdicCompletion'''' {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V)

/-- The functions on the fibre `X ×_V Spec (A / I^{n+1})`. -/
abbrev FibreRing (n : ℕ) : Type (u + 1) :=
  ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B S hS (fibreSpace V I (spaceHom V g) (n + 1)).1
        (fibreSpace V I (spaceHom V g) (n + 1)).2).O))

variable (I) in
/-- **The ring `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`** of compatible families of functions on
the fibres. -/
def towerRing : Subring (∀ n, FibreRing (I := I) g n) where
  carrier := {x | ∀ n, globalSectionsRingHomSite B S hS
    (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1))) (x (n + 1)) = x n}
  mul_mem' {x y} hx hy n := by
    rw [Pi.mul_apply, map_mul, hx n, hy n]
    rfl
  one_mem' n := by
    rw [Pi.one_apply, map_one]
    rfl
  add_mem' {x y} hx hy n := by
    rw [Pi.add_apply, map_add, hx n, hy n]
    rfl
  zero_mem' n := by
    rw [Pi.zero_apply, map_zero]
    rfl
  neg_mem' {x} hx n := by
    rw [Pi.neg_apply, map_neg, hx n]
    rfl

/-- The ring map into `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)` of a compatible family of ring
maps into the functions on the fibres. -/
def towerLift {R : Type*} [CommRing R] (c : ∀ n, R →+* FibreRing (I := I) g n)
    (hc : ∀ n, (globalSectionsRingHomSite B S hS
      (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))).comp (c (n + 1)) = c n) :
    R →+* towerRing I g :=
  (RingHom.pi c).codRestrict _ fun r n => congrArg (fun φ => φ r) (hc n)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The `n`-th component of `towerLift g c hc r` is `c n r`. -/
theorem towerLift_apply {R : Type*} [CommRing R] (c : ∀ n, R →+* FibreRing (I := I) g n)
    (hc : ∀ n, (globalSectionsRingHomSite B S hS
      (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))).comp (c (n + 1)) = c n)
    (r : R) (n : ℕ) : (towerLift g c hc r).1 n = c n r := rfl

variable (I) in
/-- The families vanishing on the first `n` fibres. -/
def towerFiltration (n : ℕ) : Ideal (towerRing I g) where
  carrier := {x | ∀ m < n, x.1 m = 0}
  add_mem' {x y} hx hy m hm := by
    change x.1 m + y.1 m = 0
    rw [hx m hm, hy m hm, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c x hx m hm := by
    change c.1 m * x.1 m = 0
    rw [hx m hm, mul_zero]

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The filtration `F_n` of `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)` is decreasing. -/
theorem antitone_towerFiltration : Antitone (towerFiltration I g) :=
  fun _ _ h _ hx m hm => hx m (lt_of_lt_of_le hm h)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The filtration `F_n` is separated: a family lying in every `F_n` is zero. -/
theorem eq_zero_of_mem_towerFiltration (x : towerRing I g) (hx : ∀ n, x ∈ towerFiltration I g n) :
    x = 0 :=
  Subtype.ext (funext fun m => hx (m + 1) m (Nat.lt_succ_self m))

/-- An element of an ideal `J` maps to zero in `Γ(Spec (R ⧸ J), 𝒪)`. -/
private theorem ΓSpecIso_inv_quotient_mk_eq_zero {R : Type u} [CommRing R] {J : Ideal R} {x : R}
    (hx : x ∈ J) :
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom (Ideal.Quotient.mk J x) = 0 :=
  (congrArg _ (Ideal.Quotient.eq_zero_iff_mem.2 hx)).trans (map_zero _)

variable {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : QuotientSystem B S hS Bt}

/-- **The ring map `ψ_F : B ⟶ lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`** of a morphism
`F : X_{/g⁻¹ V(I)} ⟶ Spf B`. -/
def towerRingHom
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB) :
    Bt →+* towerRing I g :=
  towerLift g (fibreRingHom g hZI hB hqc F) (fibreRingHom_transition g hZI hB hqc F)

/-- **A morphism `X_{/g⁻¹ V(I)} ⟶ Spf B` is determined by its ring map `ψ_F`.** -/
theorem eq_of_towerRingHom_eq
    {F₁ F₂ : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB}
    (h : towerRingHom g hZI hqc hB F₁ = towerRingHom g hZI hqc hB F₂) : F₁ = F₂ :=
  eq_of_fibreRingHom_eq g hZI hB hqc fun n => RingHom.ext fun b =>
    congrArg (fun x : towerRing I g => x.1 n) (congrArg (fun φ => φ b) h)

/-- **`ψ_F` is continuous** for the filtration of `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`: a
morphism into `Spf B` factors on each fibre through a quotient `Spec (B ⧸ J)` by an open ideal. -/
theorem towerRingHom_preimage_mem_nhds
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB)
    (n : ℕ) :
    (towerRingHom g hZI hqc hB F ⁻¹' (towerFiltration I g n : Set (towerRing I g))) ∈
      𝓝 (0 : Bt) := by
  have hm : ∀ m, {b : Bt | fibreRingHom g hZI hB hqc F m b = 0} ∈ 𝓝 (0 : Bt) := by
    intro m
    obtain ⟨J, t, ht⟩ := exists_isStageFactor hB _ (hqc (m + 1))
      (toCompletion (fibreInclusion V I (spaceHom V g) (m + 1)).hom _
        (pointsMap_fibreInclusion_mem g hZI m) ≫ F)
    refine Filter.mem_of_superset ((OrderDual.ofDual J).2.1.mem_nhds (zero_mem _)) ?_
    intro b hb
    show formalRingHom hB _ (hqc (m + 1)) _ b = 0
    rw [formalRingHom_eq hB _ (hqc (m + 1)) ht]
    have h0 : stageRingHom DB J b = 0 := ΓSpecIso_inv_quotient_mk_eq_zero hb
    rw [stageFactorRingHom, RingHom.comp_apply, h0, map_zero]
  have hfin : (⋂ m ∈ Finset.range n, {b : Bt | fibreRingHom g hZI hB hqc F m b = 0}) ∈
      𝓝 (0 : Bt) :=
    (Filter.biInter_finset_mem _).2 fun m _ => hm m
  refine Filter.mem_of_superset hfin fun b hb m hmn => ?_
  exact Set.mem_iInter₂.1 hb m (Finset.mem_range.2 hmn)

variable (I) in
/-- The component `A^∧ ⟶ A^∧ ⧸ I^{n+1} A^∧ ⟶ Γ(X ×_V Spec (A / I^{n+1}), 𝒪)` of `α`. -/
def alphaComp (n : ℕ) :
    AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* FibreRing (I := I) g n :=
  (pullbackRingHom B (powStage V I n) (ObjectProperty.homMk (fibreToPowStage V I g n))).comp
    (powStageRingHom' I n)

include hZI hqc in
/-- On the `n`-th fibre, the ring map of `X_{/g⁻¹ V(I)} ⟶ V_{/V(I)} ⟶ Spf B` given by
`φ : B → A^∧` is `alphaComp I g n ∘ φ`. -/
theorem fibreRingHom_eq_alphaComp_comp (φ : ContinuousHom DB (completionQuotientSystem V I))
    (n : ℕ) :
    fibreRingHom g hZI hB hqc (completionSheafRestrict B S hS g (pointsMap B S hS X.1 g ⁻¹' Z) Z
        (fun _ hx => hx) ≫ continuousHomEquiv hZI hB φ) n =
      (alphaComp I g n).comp φ.toRingHom :=
  fibreRingHom_completionSheafRestrict_comp_continuousHomEquiv g hZI hB hqc φ n

include hZI hqc in
/-- The components `alphaComp I g n` are compatible with the transition maps between the fibres.
-/
theorem alphaComp_transition (n : ℕ) :
    (globalSectionsRingHomSite B S hS
      (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))).comp (alphaComp I g (n + 1)) =
      alphaComp I g n := by
  obtain ⟨hTR, hLT, -, -, hAw⟩ := adicCompletion_isAdic_of_fg I I.fg_of_isNoetherianRing
  have h := fibreRingHom_transition g hZI hAw hqc (completionSheafRestrict B S hS g
    (pointsMap B S hS X.1 g ⁻¹' Z) Z (fun _ hx => hx) ≫
      continuousHomEquiv hZI hAw (ContinuousHom.id (completionQuotientSystem V I))) n
  rw [fibreRingHom_eq_alphaComp_comp g hZI hqc hAw, fibreRingHom_eq_alphaComp_comp g hZI hqc hAw]
    at h
  exact h

include hZI hqc in
/-- **The ring map `α : A^∧ ⟶ lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`.** -/
def alpha : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* towerRing I g :=
  towerLift g (alphaComp I g) (alphaComp_transition g hZI hqc)

include hZI hqc in
/-- **The ring map of `X_{/g⁻¹ V(I)} ⟶ V_{/V(I)} ⟶ Spf B` given by `φ : B → A^∧` is `α ∘ φ`.** -/
theorem towerRingHom_completionSheafRestrict_comp_continuousHomEquiv
    (φ : ContinuousHom DB (completionQuotientSystem V I)) :
    towerRingHom g hZI hqc hB (completionSheafRestrict B S hS g (pointsMap B S hS X.1 g ⁻¹' Z) Z
        (fun _ hx => hx) ≫ continuousHomEquiv hZI hB φ) =
      (alpha g hZI hqc).comp φ.toRingHom :=
  RingHom.ext fun b => Subtype.ext (funext fun n =>
    congrArg (fun ψ => ψ b) (fibreRingHom_eq_alphaComp_comp g hZI hqc hB φ n))

/-- The map `A^∧ ⟶ Γ(Spec (A^∧ ⧸ I^{n+1} A^∧), 𝒪)` vanishes on `I^{n+1} A^∧`. -/
theorem powStageRingHom'_eq_zero {n : ℕ}
    {x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hx : x ∈ (adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1) :
    powStageRingHom' I n x = 0 :=
  ΓSpecIso_inv_quotient_mk_eq_zero hx

include hZI hqc in
/-- **`α` maps `I^n A^∧` into the `n`-th step of the filtration.** -/
theorem alpha_mem_towerFiltration {n : ℕ}
    {x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hx : x ∈ (I.map (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
      ^ n) : alpha g hZI hqc x ∈ towerFiltration I g n := by
  intro m hm
  show (pullbackRingHom B _ _) (powStageRingHom' I m x) = 0
  have hx' : x ∈ (adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing m).1 := by
    show x ∈ (I ^ (m + 1)).map _
    rw [Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hm) hx
  rw [powStageRingHom'_eq_zero hx', map_zero]

end AlgebraicGeometry.Artin.FormalRing

end
