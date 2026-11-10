module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Abelian
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing of first Čech cohomology gives surjectivity on sections

Let `0 → F → G → H → 0` be a short exact sequence of abelian sheaves on a topological space `X`
and let `U ⊆ X` be open. If there is a cofinal system `S` of open coverings of `U` such that the
first Čech cohomology `Ȟ¹(𝒰, F)` vanishes for every `𝒰 ∈ S`, then the map on sections
`G(U) → H(U)` is surjective. Sheaves of `O_X`-modules enter only through their underlying abelian
sheaves, so the short exact sequence is a short exact `ShortComplex` in
`TopCat.Sheaf AddCommGrpCat X`.

The Čech complex is the ordered (non-alternating) one of [Stacks, Tag 01ED]: a `p`-cochain
assigns to each `σ : Fin (p+1) → ι` a section over `U_{σ 0} ∩ ⋯ ∩ U_{σ p}`, and the differential
is `d(s)_σ = Σ_j (-1)^j · (s_{σ ∘ j.succAbove})|_{U_σ}`. The vanishing `Ȟ¹(𝒰, F) = 0` is stated
concretely: every `1`-cocycle is a `1`-coboundary.

All names are in the namespace `Stacks.Cohomology.CechDegreeOneVanishing`.

## Main definitions

* `OpenCovering`: an open covering of an open subset `U`.
* `CechCochain`, `cechDiff`: ordered Čech cochains and the Čech differential.
* `CechH1IsZero`: every Čech `1`-cocycle is a `1`-coboundary.
* `CofinalCoveringSystem`: a system of open coverings of `U` refining every open covering of `U`.

## Main results

* `cech_h1_vanishing_implies_surjective_on_sections`: under these hypotheses `G(U) → H(U)` is
  surjective.

## References

* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU) (Lemma 20.11.7)
-/

open CategoryTheory TopologicalSpace Opposite

namespace Stacks.Cohomology.CechDegreeOneVanishing

variable {X : TopCat}

/-- An open covering of an open set `U ⊆ X`: an index type `ι` and a family of opens
`obj : ι → Opens X`, each contained in `U`, whose supremum is `U`. -/
structure OpenCovering (U : Opens X) where
  /-- The index set `I` of the covering. -/
  ι : Type
  /-- The members `U_i` of the covering. -/
  obj : ι → Opens X
  /-- Each member is contained in `U`. -/
  le : ∀ i, obj i ≤ U
  /-- The members cover `U`. -/
  covers : ⨆ i, obj i = U

/-- The `(p+1)`-fold intersection `U_{σ 0} ∩ ⋯ ∩ U_{σ p}` for a tuple `σ : Fin (p+1) → ι`. -/
noncomputable def OpenCovering.inter {U : Opens X} (𝒰 : OpenCovering U) {p : ℕ}
    (σ : Fin (p + 1) → 𝒰.ι) : Opens X :=
  ⨅ j, 𝒰.obj (σ j)

/-- A Čech `p`-cochain assigns to every `(p+1)`-tuple of indices a section of `F` over the
corresponding intersection. As an abelian group this is the product `∏_{σ} F(U_σ)`. -/
def CechCochain (F : TopCat.Presheaf AddCommGrpCat X) {U : Opens X} (𝒰 : OpenCovering U)
    (p : ℕ) : Type _ :=
  ∀ σ : Fin (p + 1) → 𝒰.ι, ↥(F.obj (op (𝒰.inter σ)))

/-- Čech cochains form an abelian group under componentwise addition. -/
noncomputable instance instCechCochainAddCommGroup (F : TopCat.Presheaf AddCommGrpCat X)
    {U : Opens X} (𝒰 : OpenCovering U) (p : ℕ) : AddCommGroup (CechCochain F 𝒰 p) := by
  unfold CechCochain; infer_instance

/-- The intersection over a full tuple is contained in the intersection over the `j`-th face (the
tuple with the `j`-th coordinate omitted). -/
lemma OpenCovering.inter_le_face {U : Opens X} (𝒰 : OpenCovering U) {p : ℕ}
    (σ : Fin (p + 2) → 𝒰.ι) (j : Fin (p + 2)) :
    𝒰.inter σ ≤ 𝒰.inter (σ ∘ j.succAbove) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

/-- The intersection over a tuple is contained in each individual member. -/
lemma OpenCovering.inter_le_index {U : Opens X} (𝒰 : OpenCovering U) {p : ℕ}
    (σ : Fin (p + 1) → 𝒰.ι) (j : Fin (p + 1)) :
    𝒰.inter σ ≤ 𝒰.obj (σ j) :=
  iInf_le _ j

/-- The intersection over the constant `Fin 1`-tuple `(fun _ => k)` is just `𝒰.obj k`. -/
lemma OpenCovering.inter_single {U : Opens X} (𝒰 : OpenCovering U) (k : 𝒰.ι) :
    𝒰.inter (fun _ : Fin 1 => k) = 𝒰.obj k := by
  unfold OpenCovering.inter; simp

/-- Restriction of a section `x ∈ F(V)` along an inclusion `W ≤ V`. -/
noncomputable def CechCochain.res (F : TopCat.Presheaf AddCommGrpCat X) {V W : Opens X}
    (h : W ≤ V) (x : ↥(F.obj (op V))) : ↥(F.obj (op W)) :=
  (F.map (homOfLE h).op) x

/-- The Čech differential `d : Č^p(𝒰, F) → Č^{p+1}(𝒰, F)`, given by
`d(s)_σ = Σ_j (-1)^j · (s_{σ ∘ (face j)})|_{U_σ}`. -/
noncomputable def cechDiff (F : TopCat.Presheaf AddCommGrpCat X) {U : Opens X}
    (𝒰 : OpenCovering U) (p : ℕ) (s : CechCochain F 𝒰 p) : CechCochain F 𝒰 (p + 1) :=
  fun σ => ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    CechCochain.res F (𝒰.inter_le_face σ j) (s (σ ∘ j.succAbove))

/-- In degree `0` the Čech differential is
`d⁰(t)_{i₀i₁} = t_{i₁}|_{U_{i₀i₁}} - t_{i₀}|_{U_{i₀i₁}}`: here `σ ∘ (0).succAbove` is the tuple
`(σ 1)` and `σ ∘ (1).succAbove` is the tuple `(σ 0)`. -/
theorem cechDiff_zero_apply (F : TopCat.Presheaf AddCommGrpCat X) {U : Opens X}
    (𝒰 : OpenCovering U) (t : CechCochain F 𝒰 0) (σ : Fin 2 → 𝒰.ι) :
    cechDiff F 𝒰 0 t σ
      = CechCochain.res F (𝒰.inter_le_face σ 0) (t (σ ∘ (0 : Fin 2).succAbove))
        - CechCochain.res F (𝒰.inter_le_face σ 1) (t (σ ∘ (1 : Fin 2).succAbove)) := by
  rw [cechDiff, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  rw [sub_eq_add_neg]

/-- The vanishing `Ȟ¹(𝒰, F) = 0`: every Čech `1`-cocycle (`d¹ s = 0`) is a `1`-coboundary
(`s = d⁰ t` for some `t`), that is, `ker(d¹) ⊆ im(d⁰)`. -/
def CechH1IsZero (F : TopCat.Presheaf AddCommGrpCat X) {U : Opens X} (𝒰 : OpenCovering U) :
    Prop :=
  ∀ s : CechCochain F 𝒰 1, cechDiff F 𝒰 1 s = 0 →
    ∃ t : CechCochain F 𝒰 0, s = cechDiff F 𝒰 0 t

/-- `𝒱` refines `𝒰` if there is a map `c : 𝒱.ι → 𝒰.ι` with `V_k ⊆ U_{c k}` for all `k`. -/
def OpenCovering.Refines {U : Opens X} (𝒱 𝒰 : OpenCovering U) : Prop :=
  ∃ c : 𝒱.ι → 𝒰.ι, ∀ k, 𝒱.obj k ≤ 𝒰.obj (c k)

/-- A system `S` of open coverings of `U` is cofinal if every open covering `𝒲` of `U` is refined
by some `𝒰 ∈ S`. -/
def CofinalCoveringSystem {U : Opens X} (S : Set (OpenCovering U)) : Prop :=
  ∀ 𝒲 : OpenCovering U, ∃ 𝒰 ∈ S, 𝒰.Refines 𝒲

/-- The underlying presheaf of an abelian sheaf, as its image under the forgetful functor. -/
noncomputable abbrev psh (P : TopCat.Sheaf AddCommGrpCat X) : TopCat.Presheaf AddCommGrpCat X :=
  (TopCat.Sheaf.forget AddCommGrpCat X).obj P

/-- Restriction map on sections of an abelian sheaf for `W ≤ V`. -/
noncomputable def secRes (P : TopCat.Sheaf AddCommGrpCat X) {V W : Opens X} (h : W ≤ V)
    (x : (psh P).obj (op V)) : (psh P).obj (op W) :=
  (psh P).map (homOfLE h).op x

/-- `b : G → H` as a morphism of underlying presheaves (a natural transformation). -/
noncomputable abbrev bMap (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) :
    psh S.X₂ ⟶ psh S.X₃ := (TopCat.Sheaf.forget AddCommGrpCat X).map S.g

/-- `a : F → G` as a morphism of underlying presheaves (a natural transformation). -/
noncomputable abbrev aMap (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) :
    psh S.X₁ ⟶ psh S.X₂ := (TopCat.Sheaf.forget AddCommGrpCat X).map S.f

/-- Restriction is functorial: restricting from `V` to `W` to `Z` equals restricting from `V` to
`Z`. -/
lemma secRes_secRes (P : TopCat.Sheaf AddCommGrpCat X) {V W Z : Opens X}
    (h₁ : W ≤ V) (h₂ : Z ≤ W) (x : (psh P).obj (op V)) :
    secRes P h₂ (secRes P h₁ x) = secRes P (h₂.trans h₁) x := by
  unfold secRes
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← (psh P).map_comp]
  rfl

/-- Restriction at the identity inclusion is the identity. -/
lemma secRes_self (P : TopCat.Sheaf AddCommGrpCat X) {V : Opens X} (h : V ≤ V)
    (x : (psh P).obj (op V)) : secRes P h x = x := by
  unfold secRes
  rw [show (homOfLE h).op = (CategoryTheory.CategoryStruct.id (op V)) from rfl, (psh P).map_id]
  rfl

/-- Restriction is additive (preserves subtraction). -/
lemma secRes_sub (P : TopCat.Sheaf AddCommGrpCat X) {V W : Opens X} (h : W ≤ V)
    (x y : (psh P).obj (op V)) : secRes P h (x - y) = secRes P h x - secRes P h y := by
  unfold secRes; rw [map_sub]

/-- Restriction is additive (preserves addition). -/
lemma secRes_add (P : TopCat.Sheaf AddCommGrpCat X) {V W : Opens X} (h : W ≤ V)
    (x y : (psh P).obj (op V)) : secRes P h (x + y) = secRes P h x + secRes P h y := by
  unfold secRes; rw [map_add]

/-- If `W₂ = W₁` (both contained in `V`), restricting `x ∈ P(V)` to `W₂` is restricting it to `W₁`
followed by the isomorphism `(psh P).map (eqToHom _)`. -/
lemma secRes_congr_source (P : TopCat.Sheaf AddCommGrpCat X) {V W₁ W₂ : Opens X}
    (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (hW : W₂ = W₁) (x : (psh P).obj (op V)) :
    secRes P h₂ x = (psh P).map (eqToHom (by rw [hW]) : op W₁ ⟶ op W₂) (secRes P h₁ x) := by
  subst hW
  unfold secRes
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← (psh P).map_comp]
  rfl

/-- A sheaf morphism commutes with restriction (naturality), for `b = S.g`. -/
lemma map_secRes (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X))
    {V W : Opens X} (hVW : W ≤ V) (x : (psh S.X₂).obj (op V)) :
    (bMap S).app (op W) (secRes S.X₂ hVW x) = secRes S.X₃ hVW ((bMap S).app (op V) x) := by
  unfold secRes
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← (bMap S).naturality]

/-- A sheaf morphism commutes with restriction (naturality), for `a = S.f`. -/
lemma map_secRes_f (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X))
    {V W : Opens X} (hVW : W ≤ V) (x : (psh S.X₁).obj (op V)) :
    (aMap S).app (op W) (secRes S.X₁ hVW x) = secRes S.X₂ hVW ((aMap S).app (op V) x) := by
  unfold secRes
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← (aMap S).naturality]

/-- The composite `b ∘ a` vanishes on sections over every open `V`. -/
lemma sectionwise_comp_zero (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X))
    (V : Opens X) (y : (psh S.X₁).obj (op V)) :
    (bMap S).app (op V) ((aMap S).app (op V) y) = 0 := by
  have hSpsh : ((TopCat.Sheaf.forget AddCommGrpCat X).map S.f
      ≫ (TopCat.Sheaf.forget AddCommGrpCat X).map S.g) = (0 : psh S.X₁ ⟶ psh S.X₃) := by
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  have h2 : (aMap S).app (op V) ≫ (bMap S).app (op V) = 0 :=
    congrArg (fun η : psh S.X₁ ⟶ psh S.X₃ => η.app (op V)) hSpsh
  rw [← CategoryTheory.ConcreteCategory.comp_apply, h2]
  rfl

/-- For a short exact sequence of abelian sheaves `0 → F → G → H → 0` and an open `V`, a section
`x ∈ G(V)` with `b(x) = 0` is `a(y)` for some `y ∈ F(V)`: the sequence of sections
`F(V) → G(V) → H(V)` is exact. -/
lemma sectionwise_ker (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) (hS : S.ShortExact)
    (V : Opens X) (x : (psh S.X₂).obj (op V)) (hx : (bMap S).app (op V) x = 0) :
    ∃ y : (psh S.X₁).obj (op V), (aMap S).app (op V) y = x := by
  have hmono : Mono S.f := hS.mono_f
  have hker := hS.exact.fIsKernel
  have hF : Limits.PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) := by
    constructor; intro J _ _; exact inferInstance
  have hFk : Limits.PreservesLimit (Limits.parallelPair S.g 0)
      (TopCat.Sheaf.forget AddCommGrpCat X) :=
    (hF.preservesFiniteLimits Limits.WalkingParallelPair).preservesLimit
  have hker2 := Limits.KernelFork.mapIsLimit _ hker (TopCat.Sheaf.forget AddCommGrpCat X)
  have hpzE : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).PreservesZeroMorphisms :=
    inferInstance
  have hE : Limits.PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) := by
    constructor; intro J _ _; exact inferInstance
  have hEk : Limits.PreservesLimit (Limits.parallelPair (bMap S) 0)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) :=
    (hE.preservesFiniteLimits Limits.WalkingParallelPair).preservesLimit
  have hker3 := @Limits.KernelFork.mapIsLimit (TopCat.Presheaf AddCommGrpCat X) _ _ AddCommGrpCat _
    _ _ _ (bMap S) _ hker2 ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) hpzE hEk
  let TV : ShortComplex AddCommGrpCat :=
    { X₁ := (psh S.X₁).obj (op V), X₂ := (psh S.X₂).obj (op V), X₃ := (psh S.X₃).obj (op V),
      f := (aMap S).app (op V), g := (bMap S).app (op V),
      zero := AddCommGrpCat.hom_ext (AddMonoidHom.ext (sectionwise_comp_zero S V)) }
  have hTexact : TV.Exact := ShortComplex.exact_of_f_is_kernel TV hker3
  rw [ShortComplex.ab_exact_iff] at hTexact
  exact hTexact x hx

/-- For a short exact sequence of abelian sheaves `0 → F → G → H → 0` and an open `V`, the map
`a : F(V) → G(V)` is injective. -/
lemma sectionwise_mono (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) (hS : S.ShortExact)
    (V : Opens X) (y₁ y₂ : (psh S.X₁).obj (op V))
    (hy : (aMap S).app (op V) y₁ = (aMap S).app (op V) y₂) : y₁ = y₂ := by
  have hmono : Mono S.f := hS.mono_f
  have hF : Limits.PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat X) := by
    constructor; intro J _ _; exact inferInstance
  have hE : Limits.PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) := by
    constructor; intro J _ _; exact inferInstance
  have hFm : (TopCat.Sheaf.forget AddCommGrpCat X).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have hEm : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have hmf : Mono (aMap S) := Functor.map_mono _ S.f
  have : Mono (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map (aMap S)) :=
    Functor.map_mono _ (aMap S)
  exact (AddCommGrpCat.mono_iff_injective ((aMap S).app (op V))).mp this hy

/-- Local surjectivity of an epimorphism of abelian sheaves: for a short exact sequence
`0 → F → G → H → 0`, every section `h ∈ H(U)` lifts locally, that is, there is an open covering `𝒲`
of `U` and sections `g i ∈ G(𝒲.obj i)` with `b(g i) = h|_{𝒲.obj i}`. -/
lemma local_lift (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) (hS : S.ShortExact)
    (U : Opens X) (h : (psh S.X₃).obj (op U)) :
    ∃ (𝒲 : OpenCovering U) (g : ∀ i, (psh S.X₂).obj (op (𝒲.obj i))),
      ∀ i, (bMap S).app (op (𝒲.obj i)) (g i) = secRes S.X₃ (𝒲.le i) h := by
  classical
  have hpt : ∀ (u : X), u ∈ U →
      ∃ (W : Opens X) (_ : u ∈ W) (hWU : W ≤ U) (gw : (psh S.X₂).obj (op W)),
        (bMap S).app (op W) gw = secRes S.X₃ hWU h := by
    intro u hu
    have hsurj : Function.Surjective
        (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat u).map (bMap S))) := by
      have : Epi S.g := hS.epi_g
      have hadj := stalkSkyscraperSheafAdjunction (C := AddCommGrpCat) (X := X) u
      have : Limits.PreservesColimitsOfShape Limits.WalkingSpan
          (TopCat.Sheaf.forget AddCommGrpCat X ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat u) :=
        hadj.leftAdjoint_preservesColimits.preservesColimitsOfShape
      have : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat u).PreservesEpimorphisms :=
        preservesEpimorphisms_of_preservesColimitsOfShape _
      have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat u).map (bMap S)) :=
        Functor.map_epi (TopCat.Sheaf.forget AddCommGrpCat X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat u) S.g
      exact (AddCommGrpCat.epi_iff_surjective _).mp hepi
    set gh := (ConcreteCategory.hom ((psh S.X₃).germ U u hu)) h with hgh_def
    obtain ⟨t, ht⟩ := hsurj gh
    obtain ⟨V, m, s, hs⟩ := (psh S.X₂).exists_germ_eq t
    have hkey : (ConcreteCategory.hom ((psh S.X₃).germ V u m))
          ((ConcreteCategory.hom ((bMap S).app (op V)) s)) = gh := by
      rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply V u m (bMap S) s, hs, ht]
    rw [hgh_def] at hkey
    obtain ⟨W, mW, iWV, iWU, hWeq⟩ := (psh S.X₃).germ_eq u m hu _ h hkey
    refine ⟨W, mW, iWU.le, secRes S.X₂ iWV.le s, ?_⟩
    rw [map_secRes S iWV.le s]
    change (psh S.X₃).map (homOfLE iWV.le).op _ = (psh S.X₃).map (homOfLE iWU.le).op h
    rw [show homOfLE iWV.le = iWV from Subsingleton.elim _ _,
        show homOfLE iWU.le = iWU from Subsingleton.elim _ _]
    exact hWeq
  choose W mW hWU gw hgw using fun (p : {u : X // u ∈ U}) => hpt p.1 p.2
  refine ⟨{ ι := {u : X // u ∈ U}, obj := W, le := hWU, covers := ?_ }, gw, hgw⟩
  exact le_antisymm (iSup_le hWU) fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, mW ⟨x, hx⟩⟩

universe u

/-- The morphism of abelian groups `ULift ℤ ⟶ M` sending the generator `ULift.up 1` to `m`. -/
noncomputable def genHom (M : AddCommGrpCat.{u}) (m : M) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ M :=
  AddCommGrpCat.ofHom (((LinearMap.toSpanSingleton ℤ M m).comp
    (ULift.moduleEquiv).toLinearMap).toAddMonoidHom)

/-- Evaluating `genHom M m` at the generator `ULift.up 1` recovers `m`. -/
lemma genHom_apply (M : AddCommGrpCat.{u}) (m : M) : (genHom M m) (ULift.up 1) = m := by
  simp [genHom, LinearMap.toSpanSingleton]

/-- `genHom` followed by any group hom `h` is `genHom` of the image of the generator. -/
lemma genHom_comp {M N : AddCommGrpCat.{u}} (m : M) (h : M ⟶ N) :
    genHom M m ≫ h = genHom N (h m) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  obtain ⟨n⟩ := z
  simp only [CategoryTheory.ConcreteCategory.comp_apply] at *
  change h ((genHom M m) (ULift.up n)) = (genHom N (h m)) (ULift.up n)
  simp [genHom, LinearMap.toSpanSingleton, map_zsmul]

/-- The sieve generated by the members of an open covering of `U` covers `U`. -/
private lemma ofArrows_mem_grothendieckTopology {U : Opens X} (𝒰 : OpenCovering U) :
    Sieve.ofArrows 𝒰.obj (fun i => homOfLE (𝒰.le i)) ∈ (Opens.grothendieckTopology X) U := by
  intro x hx
  rw [← 𝒰.covers] at hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨𝒰.obj i, homOfLE (𝒰.le i), Sieve.ofArrows_mk 𝒰.obj _ i, hi⟩

/-- Sections `e k ∈ P(𝒰.obj k)` of an abelian sheaf `P` that agree on all double overlaps
`𝒰.obj k₀ ⊓ 𝒰.obj k₁` glue to a section of `P` over `U`. -/
lemma sheaf_glue (P : TopCat.Sheaf AddCommGrpCat X) {U : Opens X} (𝒰 : OpenCovering U)
    (e : ∀ k, (psh P).obj (op (𝒰.obj k)))
    (hagree : ∀ k₀ k₁ : 𝒰.ι,
      secRes P (inf_le_left : 𝒰.obj k₀ ⊓ 𝒰.obj k₁ ≤ 𝒰.obj k₀) (e k₀)
        = secRes P (inf_le_right : 𝒰.obj k₀ ⊓ 𝒰.obj k₁ ≤ 𝒰.obj k₁) (e k₁)) :
    ∃ σ : (psh P).obj (op U), ∀ k, secRes P (𝒰.le k) σ = e k := by
  have hsheaf : TopCat.Presheaf.IsSheaf (psh P) := P.property
  set x : ∀ i : 𝒰.ι, AddCommGrpCat.of (ULift.{_} ℤ) ⟶ (psh P).obj (op (𝒰.obj i)) :=
    fun i => genHom _ (e i) with hx_def
  have hcompat : ∀ ⦃W : Opens X⦄ ⦃i j : 𝒰.ι⦄ (a : W ⟶ 𝒰.obj i) (b : W ⟶ 𝒰.obj j),
      a ≫ homOfLE (𝒰.le i) = b ≫ homOfLE (𝒰.le j) →
        x i ≫ (psh P).map a.op = x j ≫ (psh P).map b.op := by
    intro W i j a b _
    rw [hx_def]
    simp only
    rw [genHom_comp (e i) ((psh P).map a.op), genHom_comp (e j) ((psh P).map b.op)]
    congr 1
    have hWi : W ≤ 𝒰.obj i := a.le
    have hWj : W ≤ 𝒰.obj j := b.le
    have hWij : W ≤ 𝒰.obj i ⊓ 𝒰.obj j := le_inf hWi hWj
    change secRes P hWi (e i) = secRes P hWj (e j)
    rw [show secRes P hWi (e i)
          = secRes P (hWij.trans inf_le_left) (e i) from rfl,
        show secRes P hWj (e j)
          = secRes P (hWij.trans inf_le_right) (e j) from rfl,
        ← secRes_secRes P inf_le_left hWij (e i),
        ← secRes_secRes P inf_le_right hWij (e j),
        hagree i j]
  obtain ⟨g, hg, -⟩ := hsheaf.existsUnique_amalgamation_ofArrows
    (fun i => homOfLE (𝒰.le i)) (ofArrows_mem_grothendieckTopology 𝒰) x hcompat
  refine ⟨g (ULift.up 1), fun k => ?_⟩
  have hk := hg k
  change secRes P (𝒰.le k) (g (ULift.up 1)) = e k
  have h2 : (g ≫ (psh P).map (homOfLE (𝒰.le k)).op) (ULift.up 1) = (x k) (ULift.up 1) := by
    rw [hk]
  rw [CategoryTheory.ConcreteCategory.comp_apply, hx_def] at h2
  simp only at h2
  rw [genHom_apply] at h2
  change (psh P).map (homOfLE (𝒰.le k)).op (g (ULift.up 1)) = e k
  exact h2

/-- Two sections of an abelian sheaf over `U` that agree on every member of an open covering of `U`
are equal. -/
@[ega "IV 11.9.3" "more general"]
lemma sheaf_separated (P : TopCat.Sheaf AddCommGrpCat X) {U : Opens X} (𝒰 : OpenCovering U)
    (σ₁ σ₂ : (psh P).obj (op U))
    (hrestr : ∀ k, secRes P (𝒰.le k) σ₁ = secRes P (𝒰.le k) σ₂) : σ₁ = σ₂ := by
  have hsheaf : TopCat.Presheaf.IsSheaf (psh P) := P.property
  have hsep := hsheaf.isSeparated
  set S : Sieve U := Sieve.ofArrows 𝒰.obj (fun i => homOfLE (𝒰.le i)) with hS
  apply hsep U S
  · exact ofArrows_mem_grothendieckTopology 𝒰
  · rintro Y _ ⟨Z, g, h, ⟨i⟩, rfl⟩
    rw [op_comp, (psh P).map_comp]
    change (psh P).map g.op (secRes P (𝒰.le i) σ₁) = (psh P).map g.op (secRes P (𝒰.le i) σ₂)
    rw [hrestr i]

/-- **Theorem (Stacks project, Tag 01EU; Lemma 20.11.7).** Let `X` be a (ringed) space and
`0 → F → G → H → 0` a short exact sequence of abelian sheaves on `X` (the underlying short exact
sequence of the given short exact sequence of `O_X`-modules), encoded as a short exact
`ShortComplex` `S` with `S.X₁ = F`, `S.X₂ = G`, `S.X₃ = H`, `S.f = a`, `S.g = b`. Let `U ⊆ X` be
open and suppose there is a cofinal system `𝒮` of open coverings of `U` with `Ȟ¹(𝒰, F) = 0` for
every `𝒰 ∈ 𝒮`. Then the map on sections over `U` induced by `b`, `b_U : G(U) → H(U)`, is
surjective. -/
@[stacks 01EU]
theorem cech_h1_vanishing_implies_surjective_on_sections
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat X)) (hS : S.ShortExact)
    (U : Opens X)
    (𝒮 : Set (OpenCovering U)) (hcof : CofinalCoveringSystem 𝒮)
    (hH1 : ∀ 𝒰 ∈ 𝒮, CechH1IsZero (S.X₁.1) 𝒰) :
    Function.Surjective
      (((TopCat.Sheaf.forget AddCommGrpCat X).map S.g).app (op U)) := by
  intro h
  obtain ⟨𝒲, gW, hgW⟩ := local_lift S hS U h
  obtain ⟨𝒰, h𝒰mem, c, hc⟩ := hcof 𝒲
  set g : ∀ k : 𝒰.ι, (psh S.X₂).obj (op (𝒰.obj k)) :=
    fun k => secRes S.X₂ (hc k) (gW (c k)) with hg_def
  have hgb : ∀ k : 𝒰.ι, (bMap S).app (op (𝒰.obj k)) (g k) = secRes S.X₃ (𝒰.le k) h := by
    intro k
    rw [hg_def]
    simp only
    rw [map_secRes S (hc k) (gW (c k)), hgW (c k), secRes_secRes S.X₃ (𝒲.le (c k)) (hc k) h]
  set d : ∀ σ : Fin 2 → 𝒰.ι, (psh S.X₂).obj (op (𝒰.inter σ)) :=
    fun σ => secRes S.X₂ (𝒰.inter_le_index σ 0) (g (σ 0))
              - secRes S.X₂ (𝒰.inter_le_index σ 1) (g (σ 1)) with hd_def
  have hbd : ∀ σ : Fin 2 → 𝒰.ι, (bMap S).app (op (𝒰.inter σ)) (d σ) = 0 := by
    intro σ
    simp only [hd_def, map_sub]
    rw [map_secRes S (𝒰.inter_le_index σ 0) (g (σ 0)),
        map_secRes S (𝒰.inter_le_index σ 1) (g (σ 1)),
        hgb (σ 0), hgb (σ 1),
        secRes_secRes S.X₃ (𝒰.le (σ 0)) (𝒰.inter_le_index σ 0) h,
        secRes_secRes S.X₃ (𝒰.le (σ 1)) (𝒰.inter_le_index σ 1) h,
        sub_self]
  have hfchoose : ∀ σ : Fin 2 → 𝒰.ι,
      ∃ y : (psh S.X₁).obj (op (𝒰.inter σ)), (aMap S).app (op (𝒰.inter σ)) y = d σ :=
    fun σ => sectionwise_ker S hS (𝒰.inter σ) (d σ) (hbd σ)
  choose f hf using hfchoose
  have hcocycle : cechDiff (psh S.X₁) 𝒰 1 (f : CechCochain (psh S.X₁) 𝒰 1) = 0 := by
    funext τ
    apply sectionwise_mono S hS (𝒰.inter τ)
        (cechDiff (psh S.X₁) 𝒰 1 (f : CechCochain (psh S.X₁) 𝒰 1) τ) 0
    rw [map_zero]
    change (aMap S).app (op (𝒰.inter τ))
      (∑ j : Fin 3, (-1 : ℤ) ^ (j : ℕ) •
        CechCochain.res (psh S.X₁) (𝒰.inter_le_face τ j) (f (τ ∘ j.succAbove))) = 0
    rw [map_sum, Fin.sum_univ_three]
    have hterm : ∀ (k : Fin 3),
        (aMap S).app (op (𝒰.inter τ))
          ((-1 : ℤ) ^ (k : ℕ) • CechCochain.res (psh S.X₁) (𝒰.inter_le_face τ k)
            (f (τ ∘ k.succAbove)))
        = (-1 : ℤ) ^ (k : ℕ) • secRes S.X₂ (𝒰.inter_le_face τ k) (d (τ ∘ k.succAbove)) := by
      intro k
      rw [map_zsmul]
      congr 1
      change (aMap S).app (op (𝒰.inter τ)) (secRes S.X₁ (𝒰.inter_le_face τ k) (f (τ ∘ k.succAbove)))
        = secRes S.X₂ (𝒰.inter_le_face τ k) (d (τ ∘ k.succAbove))
      rw [map_secRes_f S (𝒰.inter_le_face τ k) (f (τ ∘ k.succAbove)), hf (τ ∘ k.succAbove)]
    rw [hterm 0, hterm 1, hterm 2]
    simp only [hd_def, secRes_sub, secRes_secRes]
    simp only [Function.comp_apply, Fin.succAbove_zero]
    set_option backward.isDefEq.respectTransparency true in
    change (-1 : ℤ) ^ (0 : ℕ) • (secRes S.X₂ (𝒰.inter_le_index τ 1) (g (τ 1))
          - secRes S.X₂ (𝒰.inter_le_index τ 2) (g (τ 2)))
        + (-1 : ℤ) ^ (1 : ℕ) • (secRes S.X₂ (𝒰.inter_le_index τ 0) (g (τ 0))
          - secRes S.X₂ (𝒰.inter_le_index τ 2) (g (τ 2)))
        + (-1 : ℤ) ^ (2 : ℕ) • (secRes S.X₂ (𝒰.inter_le_index τ 0) (g (τ 0))
          - secRes S.X₂ (𝒰.inter_le_index τ 1) (g (τ 1))) = 0
    abel
  obtain ⟨t, ht⟩ := hH1 𝒰 h𝒰mem (f : CechCochain (psh S.X₁) 𝒰 1) hcocycle
  set e : ∀ k : 𝒰.ι, (psh S.X₂).obj (op (𝒰.obj k)) :=
    fun k => g k + (aMap S).app (op (𝒰.obj k))
      (CechCochain.res (psh S.X₁) (𝒰.inter_single k).ge (t (fun _ => k)))
    with he_def
  have hagree : ∀ k₀ k₁ : 𝒰.ι,
      secRes S.X₂ (inf_le_left : 𝒰.obj k₀ ⊓ 𝒰.obj k₁ ≤ 𝒰.obj k₀) (e k₀)
        = secRes S.X₂ (inf_le_right : 𝒰.obj k₀ ⊓ 𝒰.obj k₁ ≤ 𝒰.obj k₁) (e k₁) := by
    intro k₀ k₁
    have heq : 𝒰.inter ![k₀, k₁] = 𝒰.obj k₀ ⊓ 𝒰.obj k₁ := by
      apply le_antisymm
      · exact le_inf (𝒰.inter_le_index ![k₀, k₁] 0) (𝒰.inter_le_index ![k₀, k₁] 1)
      · refine le_iInf (fun j => ?_)
        fin_cases j
        · exact inf_le_left
        · exact inf_le_right
    have h0 : 𝒰.inter ![k₀, k₁] ≤ 𝒰.obj k₀ := (le_of_eq heq).trans inf_le_left
    have h1 : 𝒰.inter ![k₀, k₁] ≤ 𝒰.obj k₁ := (le_of_eq heq).trans inf_le_right
    have hkey := hf ![k₀, k₁]
    rw [ht, cechDiff_zero_apply, map_sub] at hkey
    simp only [hd_def, Matrix.cons_val_zero, Matrix.cons_val_one] at hkey
    have hfun0 : (![k₀, k₁] ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => k₁) := by
      funext i; fin_cases i; rfl
    have hfun1 : (![k₀, k₁] ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => k₀) := by
      funext i; fin_cases i; rfl
    have hbr : ∀ (ff : Fin 1 → 𝒰.ι) (k : 𝒰.ι) (hfk : ff = fun _ => k)
        (hff : 𝒰.inter ![k₀, k₁] ≤ 𝒰.inter ff) (hk : 𝒰.inter ![k₀, k₁] ≤ 𝒰.obj k),
        CechCochain.res (S.X₁.1) hff (t ff)
          = secRes S.X₁ hk (secRes S.X₁ (𝒰.inter_single k).ge (t (fun _ => k))) := by
      intro ff k hfk hff hk
      subst hfk
      rw [secRes_secRes]
      rfl
    rw [hbr _ k₁ hfun0 _ h1, hbr _ k₀ hfun1 _ h0] at hkey
    have goal_inter :
        secRes S.X₂ h0 (e k₀) = secRes S.X₂ h1 (e k₁) := by
      simp only [he_def, secRes_add]
      rw [← map_secRes_f S h0
            (CechCochain.res (psh S.X₁) (𝒰.inter_single k₀).ge (t (fun _ => k₀))),
          ← map_secRes_f S h1
            (CechCochain.res (psh S.X₁) (𝒰.inter_single k₁).ge (t (fun _ => k₁)))]
      change secRes S.X₂ h0 (g k₀)
            + (aMap S).app (op (𝒰.inter ![k₀, k₁]))
              (secRes S.X₁ h0 (secRes S.X₁ (𝒰.inter_single k₀).ge (t (fun _ => k₀))))
          = secRes S.X₂ h1 (g k₁)
            + (aMap S).app (op (𝒰.inter ![k₀, k₁]))
              (secRes S.X₁ h1 (secRes S.X₁ (𝒰.inter_single k₁).ge (t (fun _ => k₁))))
      have rearrange : ∀ {G : Type} [AddCommGroup G] (A B P Q : G),
          Q - P = A - B → A + P = B + Q := by
        intro G _ A B P Q hh; rw [add_comm B Q]; exact sub_eq_sub_iff_add_eq_add.mp hh.symm
      refine rearrange _ _ _ _ ?_
      set_option backward.isDefEq.respectTransparency true in
      exact hkey
    rw [secRes_congr_source S.X₂ h0 inf_le_left heq.symm (e k₀),
        secRes_congr_source S.X₂ h1 inf_le_right heq.symm (e k₁),
        goal_inter]
  obtain ⟨σ, hσ⟩ := sheaf_glue S.X₂ 𝒰 e hagree
  refine ⟨σ, ?_⟩
  apply sheaf_separated S.X₃ 𝒰
  intro k
  rw [← map_secRes S (𝒰.le k) σ, hσ k, he_def]
  simp only [map_add]
  rw [hgb k,
      sectionwise_comp_zero S (𝒰.obj k)
        (CechCochain.res (psh S.X₁) (𝒰.inter_single k).ge (t (fun _ => k))),
      add_zero]

end Stacks.Cohomology.CechDegreeOneVanishing
