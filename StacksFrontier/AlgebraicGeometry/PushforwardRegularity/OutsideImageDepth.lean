module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Module.DepthSubsingleton
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.Basic
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.RingTheory.Depth.HomRestriction

/-!
# Depth two for a module that is the pushforward of its restriction to an open

Let `X` be a locally Noetherian scheme, let `V ⊆ X` be open and let `ℋ` be an `𝒪_X`-module of
finite type which is canonically the pushforward `j_*(ℋ|_V)` of its own restriction to `V`.
Then the stalk of `ℋ` at a point `y` outside `V` has depth at least two.

This is [Stacks, Tag 0EY0] part (3) for the open immersion `j : V → X`.  The source proves part
(3) for a general quasi-compact quasi-separated morphism by flat base change to
`Spec 𝒪_{S,s}`; for an open immersion no base change is needed, because of one topological
fact: an open set meeting the closure of `{y}` contains `y`, so `V ∩ closure {y} = ∅`.  Hence
if `W ∋ y` is an affine open and `𝔭 ⊆ Γ(X, W)` is the prime of `y`, the basic opens of a
generating set of `𝔭` already cover `V ⊓ W` — which over `Spec 𝒪_{X,y}` is what the base
change was for.

The depth bound itself is then the commutative-algebra criterion
`Module.two_le_depth_of_bijective_restrict_maximalIdeal`: the restriction
`Hom(𝒪_{X,y}, ℋ_y) → Hom(𝔪_y, ℋ_y)` is bijective.  Both halves of that bijectivity come from
the same cover.  Surjectivity divides a representing section by each generator on its basic
open and glues; injectivity kills a section annihilated by `𝔪_y` on each basic open of the
cover.  In both cases the resulting identity on `V ⊓ W` is transported back to `W` by the
hypothesis, which says exactly that restriction `Γ(ℋ, W) → Γ(ℋ, V ⊓ W)` is bijective.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardRegularity.bijective_resF_inf_of_isIso_unit`: the
  hypothesis in the form used throughout — restriction to `V ⊓ W` is bijective on sections over
  any open `W`.
* `Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem`:
  **[Stacks, Tag 0EY0] part (3)** for an open immersion.

## Implementation notes

The germ toolkit (`resF`, `exists_glue`, `section_ext_F` and their algebra) is the one already
set up for parts (4) and (5) in `StacksFrontier/AlgebraicGeometry/PushforwardRegularity/Basic.lean`,
which likewise carries those parts out on germs rather than by base change.

Two shrinking steps are packaged as `exists_nbhd_resF_eq_zero` and `exists_nbhd_germ_repr`, each
proved by induction over a `Finset`, because the generators of `𝔭` and the finitely many
relations between their representing sections have to be brought onto one neighbourhood of `y`.

The hypothesis is stated with the unit of `Scheme.Modules.pullbackPushforwardAdjunction`, as in
`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`, of which this is the
converse; it is transported to the unit of `Scheme.Modules.restrictAdjunction`, whose component
at an open is literally a restriction map, by `Adjunction.unit_leftAdjointUniq_hom_app`.  The
open `V.ι ''ᵁ V.ι ⁻¹ᵁ W` that the latter restricts to is `V ⊓ W`, and the single `eqToHom`
transport in this file converts between the two.

`Module.depth` of a zero module is `⊤`, which is the degenerate case of the theorem; the
library has that fact only as a `private` lemma in
`StacksFrontier/RingTheory/Depth/Acyclicity.lean`, so it is re-derived here in one line.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)

### No unrestricted `@[stacks 0EY0]`

Part (3) is proved here only for an open immersion, and with `X` locally Noetherian in place of
the source's hypothesis that `𝒪_{S,s}` be Noetherian.  The general case — an arbitrary
quasi-compact quasi-separated morphism — is the source's own argument, and its one missing
ingredient is now available: flat base change for direct images in degree zero over an
arbitrary base is `isIso_baseChangeNatTrans_of_flat` of
`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/AffineDegreeZero/Modules.lean`. What that
route additionally needs, and this file does not provide, is flatness of `Scheme.fromSpecStalk`,
the ideal sheaf of the closed point of a local spectrum, and the identification of `(f_*ℱ)_s` with
the global sections of its pullback to `Spec 𝒪_{S,s}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.PushforwardRegularity

/-! ### Two auxiliary facts -/

variable {X : Scheme.{u}}

/-- Finitely many sections with vanishing germ at `y` all vanish on one neighbourhood of `y`. -/
private theorem exists_nbhd_resF_eq_zero (H : X.Modules) {κ : Type*} (W : X.Opens) (y : X)
    (hy : y ∈ W) (t : Finset κ) (τ : κ → Γ(H, W))
    (h : ∀ i ∈ t, TopCat.Presheaf.germ H.val.presheaf W y hy (τ i) = 0) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), y ∈ W' ∧ ∀ i ∈ t, resF H hW' (τ i) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨W, le_rfl, hy, by simp⟩
  | insert a t ha ih =>
    obtain ⟨W₁, hW₁, hyW₁, h₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨W₂, hyW₂, iU, iV, h₂⟩ := TopCat.Presheaf.germ_eq H.val.presheaf y hy hy (τ a) 0
      ((h a (Finset.mem_insert_self a t)).trans (germF_zero H y hy).symm)
    have hW₂ : W₂ ≤ W := iU.le
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans hW₁, ⟨hyW₁, hyW₂⟩, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h₂' : resF H hW₂ (τ i) = 0 := h₂.trans (resF_zero H hW₂)
      rw [← resF_resF H hW₂ (inf_le_right : W₁ ⊓ W₂ ≤ W₂), h₂', resF_zero]
    · rw [← resF_resF H hW₁ (inf_le_left : W₁ ⊓ W₂ ≤ W₁), h₁ i hi, resF_zero]

/-- Finitely many elements of a stalk are germs of sections over one neighbourhood. -/
private theorem exists_nbhd_germ_repr (H : X.Modules) {κ : Type*} (W₀ : X.Opens) (y : X)
    (hy₀ : y ∈ W₀) (t : Finset κ)
    (m : κ → TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :
    ∃ (W : X.Opens) (_ : W ≤ W₀) (hy : y ∈ W) (ξ : κ → Γ(H, W)),
      ∀ i ∈ t, TopCat.Presheaf.germ H.val.presheaf W y hy (ξ i) = m i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨W₀, le_rfl, hy₀, fun _ => 0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨W₁, hW₁, hyW₁, ξ₁, h₁⟩ := ih
    obtain ⟨W₂, hyW₂, σ, hσ⟩ := TopCat.Presheaf.exists_germ_eq H.val.presheaf (m a)
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans hW₁, ⟨hyW₁, hyW₂⟩,
      Function.update (fun i => resF H (inf_le_left : W₁ ⊓ W₂ ≤ W₁) (ξ₁ i)) a
        (resF H (inf_le_right : W₁ ⊓ W₂ ≤ W₂) σ), ?_⟩
    intro i hi
    by_cases hia : i = a
    · subst hia
      rw [Function.update_self]
      exact (germ_resF H (inf_le_right : W₁ ⊓ W₂ ≤ W₂) σ y ⟨hyW₁, hyW₂⟩).trans hσ
    · rw [Function.update_of_ne hia]
      exact (germ_resF H (inf_le_left : W₁ ⊓ W₂ ≤ W₁) (ξ₁ i) y ⟨hyW₁, hyW₂⟩).trans
        (h₁ i ((Finset.mem_insert.mp hi).resolve_left hia))

/-- Restricting a section of `𝒪_X` before or after scaling agrees. -/
private lemma res_res (U U' U'' : X.Opens) (h : U' ≤ U) (h' : U'' ≤ U') (a : Γ(X, U)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op a) =
      X.presheaf.map (homOfLE (h'.trans h)).op a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- The germ of a section scaled by a restricted section of `𝒪_X`. -/
private lemma germ_smul_res (H : X.Modules) {U U' : X.Opens} (h : U' ≤ U) (a : Γ(X, U))
    (ξ : Γ(H, U')) (z : X) (hz : z ∈ U') :
    TopCat.Presheaf.germ H.val.presheaf U' z hz (X.presheaf.map (homOfLE h).op a • ξ) =
      X.presheaf.germ U z (h hz) a • TopCat.Presheaf.germ H.val.presheaf U' z hz ξ := by
  refine Eq.trans (PresheafOfModules.germ_smul H.val z U' hz _ ξ) ?_
  congr 1
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) z hz a

/-- Restriction of a section of `ℋ` scaled by a restricted section of `𝒪_X`. -/
private lemma resF_smul_res (H : X.Modules) {U U' U'' : X.Opens} (h : U' ≤ U) (h' : U'' ≤ U')
    (a : Γ(X, U)) (ξ : Γ(H, U')) :
    resF H h' (X.presheaf.map (homOfLE h).op a • ξ) =
      X.presheaf.map (homOfLE (h'.trans h)).op a • resF H h' ξ := by
  refine Eq.trans (PresheafOfModules.map_smul H.val (homOfLE h').op _ ξ) ?_
  congr 1
  exact res_res U U' U'' h h' a

/-! ### The hypothesis as bijectivity of restriction -/

variable (V : X.Opens) (H : X.Modules)

/-- The unit of the restriction adjunction is invertible as soon as the unit of the
pullback--pushforward adjunction is. -/
private theorem isIso_restrictAdjunction_unit_of_pullbackPushforward
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H)) :
    IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app H) := by
  have hcomp : (Scheme.Modules.restrictAdjunction V.ι).unit.app H ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app H) =
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ H
  have h1 : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app H ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app H)) := by
    rw [hcomp]; exact hunit
  have h2 : IsIso ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app H)) := inferInstance
  exact IsIso.of_isIso_comp_right ((Scheme.Modules.restrictAdjunction V.ι).unit.app H)
    ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app H))

/-- **Restriction to `V ⊓ W` is bijective on sections.** This is the hypothesis
`ℋ ≅ j_*(ℋ|_V)` in the form used below: a section of `ℋ` on an open `W` is determined by, and
may be prescribed as, a section on `V ⊓ W`. -/
public theorem bijective_resF_inf_of_isIso_unit
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H))
    (W : X.Opens) :
    Function.Bijective fun ξ : Γ(H, W) => resF H (inf_le_right : V ⊓ W ≤ W) ξ := by
  have hunitL := isIso_restrictAdjunction_unit_of_pullbackPushforward V H hunit
  -- the component of the unit at `W` is restriction to `V.ι ''ᵁ V.ι ⁻¹ᵁ W`
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ W = V ⊓ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  let E := Scheme.Modules.toPresheaf X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have hb : Function.Bijective (ConcreteCategory.hom
      (E.map ((Scheme.Modules.restrictAdjunction V.ι).unit.app H))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance)
  have hres : Function.Bijective fun ξ : Γ(H, W) =>
      resF H (V.ι.image_preimage_le W) ξ := hb
  -- the two opens coincide, so restriction between them is a bijection
  have hid : ∀ (U : X.Opens) (ξ : Γ(H, U)), resF H (le_refl U) ξ = ξ := fun U ξ =>
    section_ext_F H _ _ fun z hz => germ_resF H (le_refl U) ξ z hz
  have hle : V ⊓ W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := himg.ge
  have hge : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ V ⊓ W := himg.le
  have htr : Function.Bijective fun ξ : Γ(H, V.ι ''ᵁ V.ι ⁻¹ᵁ W) => resF H hle ξ := by
    constructor
    · intro ξ₁ ξ₂ hξ
      have h : resF H hge (resF H hle ξ₁) = resF H hge (resF H hle ξ₂) := congrArg _ hξ
      rwa [resF_resF H hle hge, resF_resF H hle hge, hid, hid] at h
    · intro ζ
      refine ⟨resF H hge ζ, ?_⟩
      show resF H hle (resF H hge ζ) = ζ
      rw [resF_resF H hge hle, hid]
  -- and the composite is restriction to `V ⊓ W`
  have hcomp : (fun ξ : Γ(H, W) => resF H (inf_le_right : V ⊓ W ≤ W) ξ) =
      (fun ξ : Γ(H, V.ι ''ᵁ V.ι ⁻¹ᵁ W) => resF H hle ξ) ∘
        fun ξ : Γ(H, W) => resF H (V.ι.image_preimage_le W) ξ := by
    funext ξ
    exact (resF_resF H (V.ι.image_preimage_le W) hle ξ).symm
  rw [hcomp]
  exact htr.comp hres

/-! ### The cover of `V ⊓ W` by the basic opens of a generating set -/

/-- **The cover.** Let `y ∉ V` and let `W₀ ∋ y` be an affine open on which the prime `𝔭` of `y`
is generated by a finite set `s`. Then every point of `V ⊓ W₀` lies in the basic open of some
member of `s`.

This is where `y ∉ V` is used, and it replaces the source's base change to `Spec 𝒪_{X,y}`: a
point `x` of `V` has a basic open neighbourhood inside `V`, and if no generator were invertible
at `x` then the defining section of that neighbourhood would avoid `𝔭`, hence be invertible at
`y`, putting `y` into `V`. -/
private theorem exists_mem_basicOpen_of_notMem (W₀ : X.Opens)
    (hW₀ : IsAffineOpen W₀) (y : X) (hyW₀ : y ∈ W₀) (hyV : y ∉ (V : Set X))
    (s : Finset Γ(X, W₀))
    (hs : Ideal.span (s : Set Γ(X, W₀)) = (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal)
    (x : X) (hxV : x ∈ (V : Set X)) (hxW : x ∈ W₀) :
    ∃ a ∈ s, x ∈ X.basicOpen a := by
  by_contra hcon
  have hcon' : ∀ a ∈ s, x ∉ X.basicOpen a := fun a ha hxa => hcon ⟨a, ha, hxa⟩
  -- the sections that are not invertible at `x` form an ideal
  set qx : Ideal Γ(X, W₀) :=
    Ideal.comap (X.presheaf.germ W₀ x hxW).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    with hqx
  have hmem : ∀ b : Γ(X, W₀), b ∈ qx ↔ x ∉ X.basicOpen b := by
    intro b
    rw [hqx, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      X.mem_basicOpen b x hxW]
  have hpq : (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal ≤ qx := by
    rw [← hs]
    exact Ideal.span_le.mpr fun a ha => (hmem a).mpr (hcon' a ha)
  -- a basic open between `x` and `V`
  obtain ⟨b, hbV, hxb⟩ := hW₀.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hxW
  have hbp : b ∉ (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal := fun hb =>
    (hmem b).mp (hpq hb) hxb
  -- hence `b` is invertible at `y`, so `y ∈ V`
  have hby : y ∈ X.basicOpen b := by
    let _ : Algebra Γ(X, W₀) (X.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (U := W₀) ⟨y, hyW₀⟩
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y)
        (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal := hW₀.isLocalization_stalk ⟨y, hyW₀⟩
    rw [X.mem_basicOpen b y hyW₀]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal b).mpr hbp
  exact hyV (hbV hby)

/-! ### The injectivity half -/

/-- **Injectivity.** A germ at `y` annihilated by the germs of a generating set of the prime of
`y` is zero.

Some generator is invertible at every point of `V ⊓ W₂`, by the cover, so a representative of
the germ vanishes there; the hypothesis then carries that back to `W₂`. -/
private theorem eq_zero_of_germ_smul_eq_zero
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H))
    (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (y : X) (hyW₀ : y ∈ W₀)
    (hyV : y ∉ (V : Set X)) (s : Finset Γ(X, W₀))
    (hs : Ideal.span (s : Set Γ(X, W₀)) = (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y)
    (hm : ∀ a ∈ s, X.presheaf.germ W₀ y hyW₀ a • m = 0) :
    m = 0 := by
  classical
  obtain ⟨W₁, hW₁, hyW₁, ξ', hξ'⟩ :=
    exists_nbhd_germ_repr H W₀ y hyW₀ ({()} : Finset Unit) fun _ => m
  have hξ : TopCat.Presheaf.germ H.val.presheaf W₁ y hyW₁ (ξ' ()) = m :=
    hξ' () (Finset.mem_singleton_self ())
  -- the generators annihilate a representative of `m` on a smaller open
  obtain ⟨W₂, hW₂, hyW₂, hz⟩ := exists_nbhd_resF_eq_zero H W₁ y hyW₁ s
    (fun a => X.presheaf.map (homOfLE hW₁).op a • ξ' ()) (by
      intro a ha
      rw [germ_smul_res H hW₁ a (ξ' ()) y hyW₁, hξ]
      exact hm a ha)
  have hW₂W₀ : W₂ ≤ W₀ := hW₂.trans hW₁
  -- each generator still annihilates the restriction of the representative
  have hzη : ∀ a ∈ s, X.presheaf.map (homOfLE hW₂W₀).op a • resF H hW₂ (ξ' ()) = 0 := by
    intro a ha
    rw [← resF_smul_res H hW₁ hW₂ a (ξ' ())]
    exact hz a ha
  -- it vanishes on `V ⊓ W₂`, because every point there has an invertible generator
  have hzero : resF H (inf_le_right : V ⊓ W₂ ≤ W₂) (resF H hW₂ (ξ' ())) = 0 := by
    refine section_ext_F H _ _ fun z hzm => ?_
    obtain ⟨a, has, hza⟩ := exists_mem_basicOpen_of_notMem V W₀ hW₀ y hyW₀ hyV s hs z
      hzm.1 (hW₂W₀ hzm.2)
    have hu : IsUnit (X.presheaf.germ W₀ z (hW₂W₀ hzm.2) a) :=
      (X.mem_basicOpen a z (hW₂W₀ hzm.2)).mp hza
    have hgz : X.presheaf.germ W₀ z (hW₂W₀ hzm.2) a •
        TopCat.Presheaf.germ H.val.presheaf W₂ z hzm.2 (resF H hW₂ (ξ' ())) = 0 := by
      rw [← germ_smul_res H hW₂W₀ a (resF H hW₂ (ξ' ())) z hzm.2, hzη a has]
      exact germF_zero H z hzm.2
    rw [germ_resF H (inf_le_right : V ⊓ W₂ ≤ W₂) _ z hzm, germF_zero H z hzm]
    exact hu.smul_eq_zero.mp hgz
  -- the hypothesis transports that back to `W₂`
  have hη0 : resF H hW₂ (ξ' ()) = 0 :=
    (bijective_resF_inf_of_isIso_unit V H hunit W₂).1
      (hzero.trans (resF_zero H (inf_le_right : V ⊓ W₂ ≤ W₂)).symm)
  rw [← hξ, ← germ_resF H hW₂ (ξ' ()) y hyW₂, hη0]
  exact germF_zero H y hyW₂

/-- If `c` is a unit, `c • x = p` and `d • p = c • q`, then `d • x = q`. -/
private lemma smul_eq_of_smul_eq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {c : R} (hc : IsUnit c) (d : R) {x p q : M} (hx : c • x = p) (h : d • p = c • q) :
    d • x = q := by
  refine hc.smul_left_cancel.mp ?_
  rw [smul_comm, hx, h]

/-! ### The surjectivity half -/

/-- **Surjectivity.** Values prescribed on a generating set of the prime of `y`, compatible in
the sense that `a' · n a = a · n a'`, are the multiples of a single germ.

On the basic open of a generator the value is divided by that generator; the quotients agree on
overlaps because of the compatibility, so they glue to a section on `V ⊓ W₂`, which the
hypothesis lifts to `W₂`. -/
private theorem exists_germ_smul_eq
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H))
    (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (y : X) (hyW₀ : y ∈ W₀)
    (hyV : y ∉ (V : Set X)) (s : Finset Γ(X, W₀))
    (hs : Ideal.span (s : Set Γ(X, W₀)) = (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal)
    (n : Γ(X, W₀) → TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y)
    (hn : ∀ a ∈ s, ∀ a' ∈ s, X.presheaf.germ W₀ y hyW₀ a' • n a =
      X.presheaf.germ W₀ y hyW₀ a • n a') :
    ∃ m, ∀ a ∈ s, X.presheaf.germ W₀ y hyW₀ a • m = n a := by
  classical
  obtain ⟨W₁, hW₁, hyW₁, ξ, hξ⟩ := exists_nbhd_germ_repr H W₀ y hyW₀ s n
  -- the compatibilities hold on a smaller open
  obtain ⟨W₂, hW₂, hyW₂, hrel⟩ := exists_nbhd_resF_eq_zero H W₁ y hyW₁ (s ×ˢ s)
    (fun q => X.presheaf.map (homOfLE hW₁).op q.2 • ξ q.1 -
      X.presheaf.map (homOfLE hW₁).op q.1 • ξ q.2) (by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
      rw [germF_sub H y hyW₁, germ_smul_res H hW₁ q.2 (ξ q.1) y hyW₁,
        germ_smul_res H hW₁ q.1 (ξ q.2) y hyW₁, hξ q.1 hq1, hξ q.2 hq2,
        hn q.1 hq1 q.2 hq2, sub_self])
  have hW₂W₀ : W₂ ≤ W₀ := hW₂.trans hW₁
  -- the compatibilities as equations of sections on `W₂`
  have hrel₂ : ∀ a ∈ s, ∀ a' ∈ s,
      X.presheaf.map (homOfLE hW₂W₀).op a' • resF H hW₂ (ξ a) =
        X.presheaf.map (homOfLE hW₂W₀).op a • resF H hW₂ (ξ a') := by
    intro a ha a' ha'
    have h := hrel (a, a') (Finset.mem_product.mpr ⟨ha, ha'⟩)
    rw [resF_sub H hW₂, resF_smul_res H hW₁ hW₂ a' (ξ a), resF_smul_res H hW₁ hW₂ a (ξ a'),
      sub_eq_zero] at h
    exact h
  -- the same, as equations of germs
  have hrelg : ∀ a ∈ s, ∀ a' ∈ s, ∀ (z : X) (hz : z ∈ W₂),
      X.presheaf.germ W₀ z (hW₂W₀ hz) a' • TopCat.Presheaf.germ H.val.presheaf W₁ z (hW₂ hz)
          (ξ a) =
        X.presheaf.germ W₀ z (hW₂W₀ hz) a • TopCat.Presheaf.germ H.val.presheaf W₁ z (hW₂ hz)
          (ξ a') := by
    intro a ha a' ha' z hz
    have h := congrArg (TopCat.Presheaf.germ H.val.presheaf W₂ z hz) (hrel₂ a ha a' ha')
    rw [germ_smul_res H hW₂W₀ a' (resF H hW₂ (ξ a)) z hz,
      germ_smul_res H hW₂W₀ a (resF H hW₂ (ξ a')) z hz,
      germ_resF H hW₂ (ξ a) z hz, germ_resF H hW₂ (ξ a') z hz] at h
    exact h
  -- the cover of `V ⊓ W₂` by the basic opens of the generators
  set ι := {a : Γ(X, W₀) // a ∈ s} with hι
  set U : ι → X.Opens := fun i => (V ⊓ W₂) ⊓ X.basicOpen i.1 with hU
  have hUW : ∀ i, U i ≤ V ⊓ W₂ := fun _ => inf_le_left
  have hUW₂ : ∀ i, U i ≤ W₂ := fun i => (hUW i).trans inf_le_right
  have hUW₀ : ∀ i, U i ≤ W₀ := fun i => (hUW₂ i).trans hW₂W₀
  have hcover : V ⊓ W₂ ≤ ⨆ i, U i := by
    intro z hz
    obtain ⟨a, has, hza⟩ := exists_mem_basicOpen_of_notMem V W₀ hW₀ y hyW₀ hyV s hs z
      hz.1 (hW₂W₀ hz.2)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, has⟩, ⟨hz, hza⟩⟩
  -- each generator is invertible on its own basic open
  have hgu : ∀ i : ι, IsUnit (X.presheaf.map (homOfLE (hUW₀ i)).op i.1) := by
    intro i
    have hb : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le i.1)).op i.1) :=
      RingedSpace.isUnit_res_basicOpen _ i.1
    have hm := hb.map (X.presheaf.map (homOfLE (inf_le_right : U i ≤ X.basicOpen i.1)).op).hom
    rwa [res_res W₀ (X.basicOpen i.1) (U i) (X.basicOpen_le i.1) inf_le_right i.1] at hm
  -- divide the representative by the generator on its basic open
  have hdiv : ∀ i : ι, ∃ ζ : Γ(H, U i),
      X.presheaf.map (homOfLE (hUW₀ i)).op i.1 • ζ = resF H (hUW₂ i) (resF H hW₂ (ξ i.1)) := by
    intro i
    obtain ⟨v, hv⟩ := hgu i
    refine ⟨(↑v⁻¹ : Γ(X, U i)) • resF H (hUW₂ i) (resF H hW₂ (ξ i.1)), ?_⟩
    rw [smul_smul, ← hv, Units.mul_inv, one_smul]
  choose ζ hζ using hdiv
  -- the germ of the defining equation of `ζ i`
  have hkey : ∀ (i : ι) (z : X) (hz : z ∈ U i),
      X.presheaf.germ W₀ z (hUW₀ i hz) i.1 •
          TopCat.Presheaf.germ H.val.presheaf (U i) z hz (ζ i) =
        TopCat.Presheaf.germ H.val.presheaf W₁ z (hW₂ (hUW₂ i hz)) (ξ i.1) := by
    intro i z hz
    have h := congrArg (TopCat.Presheaf.germ H.val.presheaf (U i) z hz) (hζ i)
    rw [germ_smul_res H (hUW₀ i) i.1 (ζ i) z hz, germ_resF H (hUW₂ i) _ z hz,
      germ_resF H hW₂ (ξ i.1) z (hUW₂ i hz)] at h
    exact h
  -- the quotients agree on overlaps
  have hcompat : ∀ i j : ι, resF H (inf_le_left : U i ⊓ U j ≤ U i) (ζ i) =
      resF H (inf_le_right : U i ⊓ U j ≤ U j) (ζ j) := by
    intro i j
    refine section_ext_F H _ _ fun z hz => ?_
    have hzi : z ∈ U i := hz.1
    have hzj : z ∈ U j := hz.2
    have hzW₀ : z ∈ W₀ := hUW₀ i hzi
    have hui : IsUnit (X.presheaf.germ W₀ z hzW₀ i.1) := (X.mem_basicOpen i.1 z hzW₀).mp hzi.2
    have huj : IsUnit (X.presheaf.germ W₀ z hzW₀ j.1) := (X.mem_basicOpen j.1 z hzW₀).mp hzj.2
    have e1 : TopCat.Presheaf.germ H.val.presheaf (U i ⊓ U j) z hz
          (resF H (inf_le_left : U i ⊓ U j ≤ U i) (ζ i)) =
        TopCat.Presheaf.germ H.val.presheaf (U i) z hzi (ζ i) :=
      germ_resF H (inf_le_left : U i ⊓ U j ≤ U i) (ζ i) z hz
    have e2 : TopCat.Presheaf.germ H.val.presheaf (U i ⊓ U j) z hz
          (resF H (inf_le_right : U i ⊓ U j ≤ U j) (ζ j)) =
        TopCat.Presheaf.germ H.val.presheaf (U j) z hzj (ζ j) :=
      germ_resF H (inf_le_right : U i ⊓ U j ≤ U j) (ζ j) z hz
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact huj.smul_left_cancel.mp ((smul_eq_of_smul_eq_smul hui
      (X.presheaf.germ W₀ z hzW₀ j.1) (hkey i z hzi)
      (hrelg i.1 i.2 j.1 j.2 z (hUW₂ i hzi))).trans (hkey j z hzj).symm)
  -- glue, then lift to `W₂`
  obtain ⟨ζ₀, hζ₀⟩ := exists_glue H (V ⊓ W₂) U hcover hUW ζ hcompat
  obtain ⟨η, hη⟩ := (bijective_resF_inf_of_isIso_unit V H hunit W₂).2 ζ₀
  have hη' : resF H (inf_le_right : V ⊓ W₂ ≤ W₂) η = ζ₀ := hη
  refine ⟨TopCat.Presheaf.germ H.val.presheaf W₂ y hyW₂ η, fun a ha => ?_⟩
  -- the defining property of `η`, as an equation of sections on `W₂`
  have hmain : X.presheaf.map (homOfLE hW₂W₀).op a • η = resF H hW₂ (ξ a) := by
    refine (bijective_resF_inf_of_isIso_unit V H hunit W₂).1 ?_
    refine section_ext_F H _ _ fun z hz => ?_
    have hzW₀ : z ∈ W₀ := hW₂W₀ hz.2
    obtain ⟨i, hzi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover hz)
    have hui : IsUnit (X.presheaf.germ W₀ z hzW₀ i.1) := (X.mem_basicOpen i.1 z hzW₀).mp hzi.2
    have f1 : TopCat.Presheaf.germ H.val.presheaf (V ⊓ W₂) z hz
          (resF H (inf_le_right : V ⊓ W₂ ≤ W₂)
            (X.presheaf.map (homOfLE hW₂W₀).op a • η)) =
        X.presheaf.germ W₀ z hzW₀ a • TopCat.Presheaf.germ H.val.presheaf W₂ z hz.2 η :=
      (germ_resF H (inf_le_right : V ⊓ W₂ ≤ W₂) _ z hz).trans
        (germ_smul_res H hW₂W₀ a η z hz.2)
    have f2 : TopCat.Presheaf.germ H.val.presheaf (V ⊓ W₂) z hz
          (resF H (inf_le_right : V ⊓ W₂ ≤ W₂) (resF H hW₂ (ξ a))) =
        TopCat.Presheaf.germ H.val.presheaf W₁ z (hW₂ hz.2) (ξ a) :=
      (germ_resF H (inf_le_right : V ⊓ W₂ ≤ W₂) _ z hz).trans
        (germ_resF H hW₂ (ξ a) z hz.2)
    refine f1.trans (Eq.trans ?_ f2.symm)
    have hζi : TopCat.Presheaf.germ H.val.presheaf W₂ z hz.2 η =
        TopCat.Presheaf.germ H.val.presheaf (U i) z hzi (ζ i) := by
      have t1 : TopCat.Presheaf.germ H.val.presheaf (U i) z hzi (ζ i) =
          TopCat.Presheaf.germ H.val.presheaf (V ⊓ W₂) z (hUW i hzi) ζ₀ := by
        rw [← hζ₀ i]
        exact germ_resF H (hUW i) ζ₀ z hzi
      have t2 : TopCat.Presheaf.germ H.val.presheaf (V ⊓ W₂) z (hUW i hzi) ζ₀ =
          TopCat.Presheaf.germ H.val.presheaf W₂ z hz.2 η := by
        rw [← hη']
        exact germ_resF H (inf_le_right : V ⊓ W₂ ≤ W₂) η z (hUW i hzi)
      exact (t1.trans t2).symm
    rw [hζi]
    exact smul_eq_of_smul_eq_smul hui (X.presheaf.germ W₀ z hzW₀ a) (hkey i z hzi)
      (hrelg a ha i.1 i.2 z hz.2).symm
  have h := congrArg (TopCat.Presheaf.germ H.val.presheaf W₂ y hyW₂) hmain
  rw [germ_smul_res H hW₂W₀ a η y hyW₂, germ_resF H hW₂ (ξ a) y hyW₂] at h
  rw [h]
  exact hξ a ha

/-! ### Tag 0EY0, part (3), for an open immersion -/

/-- **Stacks Project, Tag 0EY0, part (3), for an open immersion.** Let `X` be a locally
Noetherian scheme, let `V ⊆ X` be open and let `ℋ` be an `𝒪_X`-module of finite type which is
canonically the pushforward of its restriction to `V`. Then the stalk of `ℋ` at a point outside
`V` has depth at least two.

Restriction `Hom(𝒪_{X,y}, ℋ_y) → Hom(𝔪_y, ℋ_y)` is bijective, which is the criterion
`Module.two_le_depth_of_bijective_restrict_maximalIdeal`; its two halves are
`eq_zero_of_germ_smul_eq_zero` and `exists_germ_smul_eq`. -/
@[stacks 0EY0 "part (3), for an open immersion rather than a general quasi-compact \
quasi-separated morphism, and with S locally Noetherian in place of the tag's Noetherian \
𝒪_{S,s} — which is the form both consumers of hdepthOutside use"]
public theorem two_le_depth_stalk_of_isIso_unit_of_notMem [IsLocallyNoetherian X]
    [H.IsFiniteType]
    (hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app H))
    (y : X) (hy : y ∉ (V : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) := by
  classical
  by_cases htriv : Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y)
  · rw [Module.depth_eq_top_of_subsingleton]
    exact le_top
  have hnt : Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
    not_subsingleton_iff_nontrivial.mp htriv
  have hfin : Module.Finite (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y) :=
    Stacks.StalkFiniteType.finite_stalk H y
  -- an affine neighbourhood of `y`, with Noetherian sections
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hyW₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hW₀' : IsAffineOpen W₀ := hW₀
  have _ : IsNoetherianRing Γ(X, W₀) :=
    IsLocallyNoetherian.component_noetherian ⟨W₀, hW₀⟩
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (hW₀'.primeIdealOf ⟨y, hyW₀⟩).asIdeal
  -- the stalk is the localization of the sections at the prime of `y`
  let _ : Algebra Γ(X, W₀) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := W₀) ⟨y, hyW₀⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk y)
      (hW₀'.primeIdealOf ⟨y, hyW₀⟩).asIdeal := hW₀'.isLocalization_stalk ⟨y, hyW₀⟩
  -- the germs of the generators lie in, and span, the maximal ideal
  have hmemM : ∀ a ∈ s, X.presheaf.germ W₀ y hyW₀ a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    intro a ha
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk y)
      (hW₀'.primeIdealOf ⟨y, hyW₀⟩).asIdeal a).mpr ?_
    rw [← hs]
    exact Ideal.subset_span ha
  have hs' : Ideal.span (↑s : Set Γ(X, W₀)) = (hW₀'.primeIdealOf ⟨y, hyW₀⟩).asIdeal := hs
  have hspan : IsLocalRing.maximalIdeal (X.presheaf.stalk y) =
      Ideal.span ((algebraMap Γ(X, W₀) (X.presheaf.stalk y)) '' (↑s : Set Γ(X, W₀))) := by
    rw [← Ideal.map_span, hs']
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal
      (hW₀'.primeIdealOf ⟨y, hyW₀⟩).asIdeal (X.presheaf.stalk y)).symm
  refine Module.two_le_depth_of_bijective_restrict_maximalIdeal _ ⟨?_, ?_⟩
  · -- injectivity
    intro g₁ g₂ hg
    refine LinearMap.ext_ring ?_
    have hsub : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y),
        a • (g₁ 1 - g₂ 1) = 0 := by
      intro a ha
      have h : g₁ a = g₂ a := by
        simpa only [LinearMap.comp_apply, Submodule.coe_subtype] using
          LinearMap.congr_fun hg ⟨a, ha⟩
      have hone : ∀ g : X.presheaf.stalk y →ₗ[X.presheaf.stalk y]
          TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y, g a = a • g 1 := by
        intro g
        conv_lhs => rw [← mul_one a, ← smul_eq_mul]
        exact map_smul g a 1
      rw [smul_sub, ← hone g₁, ← hone g₂, h, sub_self]
    have := eq_zero_of_germ_smul_eq_zero V H hunit W₀ hW₀' y hyW₀ hy s hs
      (g₁ 1 - g₂ 1) fun a ha => hsub _ (hmemM a ha)
    rwa [sub_eq_zero] at this
  · -- surjectivity
    intro φ
    obtain ⟨m, hm⟩ := exists_germ_smul_eq V H hunit W₀ hW₀' y hyW₀ hy s hs
      (fun a => if ha : a ∈ s then φ ⟨X.presheaf.germ W₀ y hyW₀ a, hmemM a ha⟩
        else 0) (by
        intro a ha a' ha'
        rw [dite_eq_left ha, dite_eq_left ha', ← map_smul, ← map_smul]
        congr 1
        refine Subtype.ext ?_
        simpa only [SetLike.val_smul, smul_eq_mul] using mul_comm _ _)
    set d : ↥(IsLocalRing.maximalIdeal (X.presheaf.stalk y)) →ₗ[X.presheaf.stalk y]
        TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf y :=
      (LinearMap.toSpanSingleton (X.presheaf.stalk y) _ m).comp
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).subtype - φ with hd
    have hdgen : ∀ a (ha : a ∈ s),
        (⟨X.presheaf.germ W₀ y hyW₀ a, hmemM a ha⟩ :
          ↥(IsLocalRing.maximalIdeal (X.presheaf.stalk y))) ∈ LinearMap.ker d := by
      intro a ha
      have hval : X.presheaf.germ W₀ y hyW₀ a • m =
          φ ⟨X.presheaf.germ W₀ y hyW₀ a, hmemM a ha⟩ := by
        rw [hm a ha, dite_eq_left ha]
      simp only [LinearMap.mem_ker, hd, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.coe_subtype, sub_eq_zero]
      exact hval
    have hmap : Submodule.map (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).subtype
        (LinearMap.ker d) = IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
      refine le_antisymm (Submodule.map_subtype_le _ _) fun z hz => ?_
      rw [hspan] at hz
      refine Submodule.span_le.mpr (fun w hw => ?_) hz
      obtain ⟨a, ha, rfl⟩ := hw
      exact Submodule.mem_map.mpr ⟨⟨_, hmemM a ha⟩, hdgen a ha, rfl⟩
    have hkertop : LinearMap.ker d = ⊤ :=
      Submodule.map_injective_of_injective
        (Subtype.val_injective (p := fun x => x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)))
        (by rw [hmap, Submodule.map_subtype_top])
    refine ⟨LinearMap.toSpanSingleton (X.presheaf.stalk y) _ m, LinearMap.ext fun x => ?_⟩
    have hx : d x = 0 := by
      rw [← LinearMap.mem_ker, hkertop]
      exact Submodule.mem_top
    have hx' : (x : X.presheaf.stalk y) • m = φ x := by
      simp only [hd, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        sub_eq_zero] at hx
      exact hx
    exact hx'

end Stacks.AlgebraicGeometry.PushforwardRegularity

end
