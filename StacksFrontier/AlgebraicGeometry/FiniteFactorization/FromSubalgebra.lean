module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic

/-! # scratch -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.FiniteFactorization

/-- A compact open of an affine open is a finite union of basic opens. -/
theorem exists_basicOpen_image_eq {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    (K : W.toScheme.Opens) (hK : IsCompact (K : Set W.toScheme)) :
    ∃ (ι : Type u) (_ : Finite ι) (a : ι → Γ(Y, W)), W.ι ''ᵁ K = ⨆ i, Y.basicOpen (a i) := by
  have : IsAffine W.toScheme := hW
  obtain ⟨s, hsfin, hs⟩ :=
    (AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
      (X := W.toScheme) (U := (K : Set W.toScheme))).mp ⟨hK, K.2⟩
  refine ⟨(s : Type u), hsfin, fun i => W.topIso.hom i.1, ?_⟩
  have hK' : K = ⨆ i : (s : Type u), W.toScheme.basicOpen i.1 := by
    refine TopologicalSpace.Opens.ext ?_
    rw [hs]
    simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_coe_set]
  rw [hK', Scheme.Hom.image_iSup]
  refine iSup_congr fun i => ?_
  have htop : ∀ x : Γ(W.toScheme, ⊤), W.topIso.inv (W.topIso.hom x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, W.topIso.hom_inv_id, ConcreteCategory.id_apply]
  have h := Scheme.Opens.ι_image_basicOpen_topIso_inv (X := Y) (U := W) (W.topIso.hom i.1)
  rw [htop] at h
  exact h


/-- `Scheme.Hom.appLE` only depends on the morphism, not on the proof of the inclusion. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (W : X.Opens)
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

/-- A compact open contained in an affine open is a finite union of basic opens of sections
over that affine open. -/
theorem exists_basicOpen_eq {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W)
    {K : Y.Opens} (hKW : K ≤ W) (hK : IsCompact (K : Set Y)) :
    ∃ (ι : Type u) (_ : Finite ι) (a : ι → Γ(Y, W)), K = ⨆ i, Y.basicOpen (a i) := by
  have hsub : (K : Set Y) ⊆ Set.range W.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
    exact hKW
  have hK' : IsCompact ((W.ι ⁻¹ᵁ K : W.toScheme.Opens) : Set W.toScheme) :=
    W.isOpenEmbedding.isEmbedding.isInducing.isCompact_preimage' hK hsub
  obtain ⟨ι, hι, a, ha⟩ := exists_basicOpen_image_eq hW (W.ι ⁻¹ᵁ K) hK'
  refine ⟨ι, hι, a, ?_⟩
  rw [← ha, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hKW]

/-- The preimage of a basic open, computed through `Scheme.Hom.appLE` for an open that is
exactly the preimage. -/
theorem preimage_basicOpen_appLE {Y Z : Scheme.{u}} (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    (h : V ≤ g ⁻¹ᵁ U) (h' : g ⁻¹ᵁ U ≤ V) (r : Γ(Z, U)) :
    g ⁻¹ᵁ Z.basicOpen r = Y.basicOpen (g.appLE U V h r) := by
  have : IsIso (homOfLE h) := ⟨homOfLE h', Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, Scheme.basicOpen_res_eq,
    Scheme.preimage_basicOpen]

/-- Surjectivity passes to a composite of ring maps. -/
theorem surjective_comp {R₁ R₂ R₃ : CommRingCat.{u}} {p : R₁ ⟶ R₂} {q : R₂ ⟶ R₃}
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    Function.Surjective (p ≫ q) := fun z => by
  obtain ⟨y, hy⟩ := hq z
  obtain ⟨x, hx⟩ := hp y
  exact ⟨x, by rw [ConcreteCategory.comp_apply, hx, hy]⟩


/-- Surjectivity of a composite whose second factor is an isomorphism gives surjectivity of the
first factor. -/
theorem surjective_of_comp_isIso {R₁ R₂ R₃ : CommRingCat.{u}} {p : R₁ ⟶ R₂} (q : R₂ ⟶ R₃)
    [IsIso q] (h : Function.Surjective (p ≫ q)) : Function.Surjective p := by
  intro y
  obtain ⟨x, hx⟩ := h (q.hom y)
  exact ⟨x, (ConcreteCategory.bijective_of_isIso q).1 hx⟩

/-- `Scheme.Hom.appLE` commutes with restricting both the open of the target and the open of the
source. -/
theorem appLE_restrict {Y Z : Scheme.{u}} (g : Y ⟶ Z) {P P' : Z.Opens} {W W' : Y.Opens}
    (hPP' : P' ≤ P) (hWW' : W' ≤ W) (e : W ≤ g ⁻¹ᵁ P) (e' : W' ≤ g ⁻¹ᵁ P') (x : Γ(Z, P)) :
    (g.appLE P' W' e').hom ((Z.presheaf.map (homOfLE hPP').op).hom x) =
      (Y.presheaf.map (homOfLE hWW').op).hom ((g.appLE P W e).hom x) := by
  have h1 : Z.presheaf.map (homOfLE hPP').op ≫ g.appLE P' W' e'
      = g.appLE P W' (hWW'.trans e) := Scheme.Hom.map_appLE _ _ _
  have h2 : g.appLE P W e ≫ Y.presheaf.map (homOfLE hWW').op
      = g.appLE P W' (hWW'.trans e) := Scheme.Hom.appLE_map _ _ _
  exact congrArg (fun k : Γ(Z, P) ⟶ Γ(Y, W') => k.hom x) (h1.trans h2.symm)

/-- A morphism restricted to an affine open of the target, over which its source is affine and
the map on sections is surjective, is a closed immersion. -/
theorem isClosedImmersion_morphismRestrict {X Y : Scheme.{u}} (h : X ⟶ Y) (Z : Y.Opens)
    (hZ : IsAffineOpen Z) (hXZ : IsAffineOpen (h ⁻¹ᵁ Z))
    (hs : Function.Surjective (h.app Z)) : IsClosedImmersion (h ∣_ Z) := by
  have : IsAffine Z.toScheme := hZ
  have : IsAffine (h ⁻¹ᵁ Z).toScheme := hXZ
  have hs' : Function.Surjective (h.app (Z.ι ''ᵁ ⊤)) := by
    rw [Scheme.Opens.ι_image_top]; exact hs
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  rw [morphismRestrict_appTop]
  exact surjective_comp hs' (ConcreteCategory.bijective_of_isIso
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage h Z ⊤)).op)).2



/-- **Step 6, the key surjectivity.**  Let `g : S' ⟶ T₀` be a morphism over `S`, let `V` be an
open of `S` whose preimages in `S'` and in `T₀` are affine, let `ab` be a section over the
preimage in `T₀` whose image in `S'` is `a`, and suppose that the sections of `S'` over `D(a)`
are generated over `Γ(S, V)` by elements `t` whose numerators `c` are reached by `g`.  Then `g`
is surjective on sections from `D(ab)` to `D(a)`. -/
theorem surjective_appLE_basicOpen {S S' T₀ : Scheme.{u}} (ν : S' ⟶ S) (π₀ : T₀ ⟶ S)
    (g : S' ⟶ T₀) (hgν : g ≫ π₀ = ν) {V : S.Opens}
    (ab : Γ(T₀, π₀ ⁻¹ᵁ V)) (hP : IsAffineOpen (π₀ ⁻¹ᵁ V))
    (a : Γ(S', ν ⁻¹ᵁ V)) (hgp : ν ⁻¹ᵁ V = g ⁻¹ᵁ (π₀ ⁻¹ᵁ V))
    (haa : (g.appLE (π₀ ⁻¹ᵁ V) (ν ⁻¹ᵁ V) (le_of_eq hgp)).hom ab = a)
    (hZ : g ⁻¹ᵁ T₀.basicOpen ab = S'.basicOpen a)
    {κ : Type u} (c : κ → Γ(S', ν ⁻¹ᵁ V)) (n : κ → ℕ) (t : κ → Γ(S', S'.basicOpen a))
    (hc : ∀ l, ∃ cb : Γ(T₀, π₀ ⁻¹ᵁ V),
      (g.appLE (π₀ ⁻¹ᵁ V) (ν ⁻¹ᵁ V) (le_of_eq hgp)).hom cb = c l)
    (hnum : ∀ l, (algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) a) ^ n l * t l =
      algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) (c l))
    (hgen : Subring.closure (Set.range (ν.appLE V (S'.basicOpen a) (S'.basicOpen_le a))
      ∪ Set.range t) = ⊤) :
    Function.Surjective
      (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)) := by
  classical
  have hloc : IsLocalization.Away ab Γ(T₀, T₀.basicOpen ab) := hP.isLocalization_basicOpen ab
  have halgS : (algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a)) =
      (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom := rfl
  have halgT : (algebraMap Γ(T₀, π₀ ⁻¹ᵁ V) Γ(T₀, T₀.basicOpen ab)) =
      (T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom := rfl
  have hkey : ∀ z : Γ(T₀, π₀ ⁻¹ᵁ V),
      (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom
          ((T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom z) =
        (S'.presheaf.map (homOfLE (S'.basicOpen_le a)).op).hom
          ((g.appLE (π₀ ⁻¹ᵁ V) (ν ⁻¹ᵁ V) (le_of_eq hgp)).hom z) :=
    fun z => appLE_restrict g (T₀.basicOpen_le ab) (S'.basicOpen_le a) (le_of_eq hgp)
      (le_of_eq hZ.symm) z
  rw [← RingHom.range_eq_top]
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine Subring.closure_le.mpr ?_
  rintro y (⟨x, rfl⟩ | ⟨l, rfl⟩)
  · refine RingHom.mem_range.mpr
      ⟨(π₀.appLE V (T₀.basicOpen ab) (T₀.basicOpen_le ab)).hom x, ?_⟩
    have h1 := Scheme.Hom.appLE_comp_appLE g π₀ V (T₀.basicOpen ab) (S'.basicOpen a)
      (T₀.basicOpen_le ab) (le_of_eq hZ.symm)
    have h2 := appLE_congr_hom hgν V (S'.basicOpen a)
      (by rw [hgν]; exact S'.basicOpen_le a) (S'.basicOpen_le a)
    rw [← (h1.trans h2), ConcreteCategory.comp_apply]
  · obtain ⟨cb, hcb⟩ := hc l
    have hwu : IsUnit ((T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom ab) := by
      rw [← halgT]
      exact IsLocalization.map_units Γ(T₀, T₀.basicOpen ab) ⟨ab, Submonoid.mem_powers ab⟩
    obtain ⟨w', hw'⟩ := hwu.exists_right_inv
    have hρa : (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom
        ((T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom ab) =
        algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) a := by
      rw [hkey ab, haa, halgS]
    have hρ1 : (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom
        (((T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom ab) * w') = 1 := by
      rw [hw', map_one]
    rw [map_mul, hρa] at hρ1
    have hdmem : (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom w'
        ∈ RingHom.range
          (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom :=
      RingHom.mem_range_self _ _
    have hcmem : algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) (c l)
        ∈ RingHom.range
          (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom := by
      refine RingHom.mem_range.mpr
        ⟨(T₀.presheaf.map (homOfLE (T₀.basicOpen_le ab)).op).hom cb, ?_⟩
      rw [hkey cb, hcb, halgS]
    have hdinv : (g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom w' *
        algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) a = 1 := by
      rw [mul_comm]; exact hρ1
    have ht : t l = ((g.appLE (T₀.basicOpen ab) (S'.basicOpen a) (le_of_eq hZ.symm)).hom w') ^ n l
        * algebraMap Γ(S', ν ⁻¹ᵁ V) Γ(S', S'.basicOpen a) (c l) := by
      rw [← hnum l, ← mul_assoc, ← mul_pow, hdinv, one_pow, one_mul]
    rw [ht]
    exact Subring.mul_mem _ (Subring.pow_mem _ hdmem _) hcmem

section Normalization

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Steps 1 and 2.**  The open range of `f.toNormalization` is covered by finitely many
basic opens `D(a)` of sections `a` over the preimages of affine opens of `S`, each of which is
contained in that range. -/
theorem exists_basicOpen_cover_opensRange [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [QuasiCompact f] [CompactSpace S] :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Opens) (_ : ∀ i, IsAffineOpen (V i))
      (a : ∀ i, Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V i)),
      (∀ i, f.normalization.basicOpen (a i) ≤ f.toNormalization.opensRange) ∧
      f.toNormalization.opensRange ≤ ⨆ i, f.normalization.basicOpen (a i) := by
  classical
  have hcomp : f.toNormalization ≫ f.fromNormalization = f := f.toNormalization_fromNormalization
  have hpre : ∀ U : S.Opens, f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ U) = f ⁻¹ᵁ U := by
    intro U
    rw [← Scheme.Hom.comp_preimage, hcomp]
  have key : ∀ U : S.affineOpens, ∃ (ιU : Type u) (_ : Finite ιU)
      (aU : ιU → Γ(f.normalization, f.fromNormalization ⁻¹ᵁ (U : S.Opens))),
      f.toNormalization.opensRange ⊓ (f.fromNormalization ⁻¹ᵁ (U : S.Opens))
        = ⨆ i, f.normalization.basicOpen (aU i) := by
    intro U
    have hW : IsAffineOpen (f.fromNormalization ⁻¹ᵁ (U : S.Opens)) := U.2.preimage _
    have himg : f.toNormalization ''ᵁ (f ⁻¹ᵁ (U : S.Opens)) =
        f.toNormalization.opensRange ⊓ (f.fromNormalization ⁻¹ᵁ (U : S.Opens)) := by
      rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf]
    have hXc : IsCompact ((f ⁻¹ᵁ (U : S.Opens) : X.Opens) : Set X) :=
      f.isCompact_preimage U.2.isCompact
    have hKc : IsCompact ((f.toNormalization.opensRange ⊓
        (f.fromNormalization ⁻¹ᵁ (U : S.Opens)) : f.normalization.Opens) :
        Set f.normalization) := by
      rw [← himg]
      exact hXc.image (by fun_prop)
    obtain ⟨ιU, hιU, aU, haU⟩ := exists_basicOpen_eq hW inf_le_right hKc
    exact ⟨ιU, hιU, aU, haU⟩
  choose ιU hιU aU haU using key
  have hcover : (Set.univ : Set S) ⊆ ⋃ U : S.affineOpens, ((U : S.Opens) : Set S) := by
    intro x _
    have hx : x ∈ (⊤ : S.Opens) := trivial
    rw [← iSup_affineOpens_eq_top S, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨U, hU⟩ := hx
    exact Set.mem_iUnion.mpr ⟨U, hU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens => ((U : S.Opens) : Set S)) (fun U => (U : S.Opens).2) hcover
  refine ⟨Σ U : (t : Finset S.affineOpens), ιU U.1, inferInstance,
    fun p => (p.1.1 : S.Opens), fun p => p.1.1.2, fun p => aU p.1.1 p.2, ?_, ?_⟩
  · intro p
    have : f.normalization.basicOpen (aU p.1.1 p.2) ≤
        f.toNormalization.opensRange ⊓ (f.fromNormalization ⁻¹ᵁ (p.1.1 : S.Opens)) := by
      rw [haU p.1.1]
      exact le_iSup (fun i => f.normalization.basicOpen (aU p.1.1 i)) p.2
    exact le_trans this inf_le_left
  · intro x hx
    have hmem := ht (Set.mem_univ (f.fromNormalization x))
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmem
    obtain ⟨U, hUt, hxU⟩ := hmem
    have hxK : x ∈ f.toNormalization.opensRange ⊓
        (f.fromNormalization ⁻¹ᵁ (U : S.Opens)) := ⟨hx, hxU⟩
    rw [haU U, TopologicalSpace.Opens.mem_iSup] at hxK
    obtain ⟨i, hi⟩ := hxK
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hUt⟩, i⟩, hi⟩



/-- The preimage under `f.toNormalization` of a basic open contained in its range is affine. -/
theorem isAffineOpen_preimage_basicOpen [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [QuasiCompact f] {V : S.Opens} (hV : IsAffineOpen V)
    (a : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V))
    (hle : f.normalization.basicOpen a ≤ f.toNormalization.opensRange) :
    IsAffineOpen (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen a) := by
  have hD : IsAffineOpen (f.normalization.basicOpen a) :=
    (hV.preimage f.fromNormalization).basicOpen a
  have himg : f.toNormalization ''ᵁ (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen a)
      = f.normalization.basicOpen a := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]
  rw [← f.toNormalization.isAffineOpen_iff_of_isOpenImmersion, himg]
  exact hD

/-- **Step 3.**  The sections of the relative normalization over a basic open contained in the
range of `f.toNormalization` form an algebra of finite type over the base. -/
theorem finiteType_appLE_basicOpen [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [QuasiCompact f] {V : S.Opens} (hV : IsAffineOpen V)
    (a : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V))
    (hle : f.normalization.basicOpen a ≤ f.toNormalization.opensRange) :
    RingHom.FiniteType (f.fromNormalization.appLE V (f.normalization.basicOpen a)
      (f.normalization.basicOpen_le a)).hom := by
  have hcomp : f.toNormalization ≫ f.fromNormalization = f := f.toNormalization_fromNormalization
  have hpre : f.toNormalization ⁻¹ᵁ (f.fromNormalization ⁻¹ᵁ V) = f ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hcomp]
  have hD' := isAffineOpen_preimage_basicOpen f hV a hle
  have e : f.toNormalization ⁻¹ᵁ (f.normalization.basicOpen a) ≤ f ⁻¹ᵁ V := by
    rw [← hpre]
    exact Scheme.Hom.preimage_mono _ (f.normalization.basicOpen_le a)
  have e' : f.toNormalization ⁻¹ᵁ (f.normalization.basicOpen a)
      ≤ (f.toNormalization ≫ f.fromNormalization) ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ (f.normalization.basicOpen_le a)
  have hiso : IsIso (f.toNormalization.appLE (f.normalization.basicOpen a)
      (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen a) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.Hom.isIso_app _ _ hle
  have hft : RingHom.FiniteType
      (f.appLE V (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen a) e).hom :=
    f.finiteType_appLE hV hD' e
  rw [appLE_congr_hom hcomp.symm V _ e e'] at hft
  rw [← Scheme.Hom.appLE_comp_appLE f.toNormalization f.fromNormalization V
    (f.normalization.basicOpen a) _ (f.normalization.basicOpen_le a) le_rfl] at hft
  exact (RingHom.finiteType_respectsIso.cancel_right_isIso _ _).mp hft


/-- **Step 3, continued.**  Generators of the sections over a basic open `D(a)` contained in the
range of `f.toNormalization`, each written with a numerator that is a section over the whole
preimage of the affine open. -/
theorem exists_generators_basicOpen [IsSeparated f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] [QuasiCompact f] {V : S.Opens} (hV : IsAffineOpen V)
    (a : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V))
    (hle : f.normalization.basicOpen a ≤ f.toNormalization.opensRange) :
    ∃ (κ : Type u) (_ : Finite κ) (c : κ → Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V))
      (n : κ → ℕ) (t : κ → Γ(f.normalization, f.normalization.basicOpen a)),
      (∀ l, (algebraMap Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)
          Γ(f.normalization, f.normalization.basicOpen a) a) ^ n l * t l =
        algebraMap Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)
          Γ(f.normalization, f.normalization.basicOpen a) (c l)) ∧
      Subring.closure (Set.range (f.fromNormalization.appLE V (f.normalization.basicOpen a)
        (f.normalization.basicOpen_le a)) ∪ Set.range t) = ⊤ := by
  classical
  have hW : IsAffineOpen (f.fromNormalization ⁻¹ᵁ V) := hV.preimage _
  have hloc : IsLocalization.Away a Γ(f.normalization, f.normalization.basicOpen a) :=
    hW.isLocalization_basicOpen a
  have hft := finiteType_appLE_basicOpen f hV a hle
  let _ : Algebra Γ(S, V) Γ(f.normalization, f.normalization.basicOpen a) :=
    (f.fromNormalization.appLE V (f.normalization.basicOpen a)
      (f.normalization.basicOpen_le a)).hom.toAlgebra
  have hft' : Algebra.FiniteType Γ(S, V) Γ(f.normalization, f.normalization.basicOpen a) := hft
  obtain ⟨σ, hσ⟩ := hft'.out
  have hrep : ∀ s : Γ(f.normalization, f.normalization.basicOpen a),
      ∃ (c : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)) (n : ℕ),
        (algebraMap Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)
          Γ(f.normalization, f.normalization.basicOpen a) a) ^ n * s =
        algebraMap Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)
          Γ(f.normalization, f.normalization.basicOpen a) c := by
    intro s
    obtain ⟨⟨c, m⟩, hm⟩ := IsLocalization.surj (M := Submonoid.powers a) s
    obtain ⟨n, hn⟩ := m.2
    have hn' : a ^ n = (m : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ V)) := hn
    refine ⟨c, n, ?_⟩
    rw [← map_pow, hn', mul_comm]
    exact hm
  choose cc nn hcc using hrep
  refine ⟨(σ : Type u), inferInstance, fun l => cc l.1, fun l => nn l.1, fun l => l.1,
    fun l => hcc l.1, ?_⟩
  have hclos := Algebra.adjoin_eq_ring_closure (R := Γ(S, V))
    (A := Γ(f.normalization, f.normalization.basicOpen a)) (σ : Set _)
  rw [hσ] at hclos
  have hrange : Set.range (fun l : (σ : Type u) => (l : Γ(f.normalization,
      f.normalization.basicOpen a))) = (σ : Set _) := Subtype.range_coe
  rw [hrange]
  rw [show (Set.range (f.fromNormalization.appLE V (f.normalization.basicOpen a)
      (f.normalization.basicOpen_le a))) =
      Set.range (algebraMap Γ(S, V) Γ(f.normalization, f.normalization.basicOpen a)) from rfl,
    ← hclos]
  rfl

end Normalization


section RelativeSpec

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

/-- The relative spectrum of a finite quasi-coherent algebra sheaf is finite over the base. -/
theorem isFinite_relativeSpecToBase {S : Scheme.{u}} (B : AlgebraSheaf S)
    [AlgebraSheaf.IsQuasicoherent B] (hB : AlgebraSheaf.IsFinite B) :
    IsFinite (relativeSpecToBase B) := by
  have h : AlgebraSheaf.IsFinite (pushforwardAlgebra (relativeSpecToBase B)) :=
    AlgebraSheaf.isFinite_of_iso (pushforwardAlgebraIso B).symm hB
  exact { finite_app := fun U hU => h U hU }

/-- **Step 5.**  The comparison morphism to the relative spectrum of a subalgebra of
`ν_* 𝒪`, and the sections of `ν_* 𝒪` it reaches. -/
theorem exists_comparison {S S' : Scheme.{u}} (ν : S' ⟶ S) (B : AlgebraSheaf S)
    [AlgebraSheaf.IsQuasicoherent B] (φ : B ⟶ pushforwardAlgebra ν) :
    ∃ g : S' ⟶ relativeSpec B, g ≫ relativeSpecToBase B = ν ∧
      ∀ (V : S.Opens) (hle : ν ⁻¹ᵁ V ≤ g ⁻¹ᵁ (relativeSpecToBase B ⁻¹ᵁ V))
        (a : (pushforwardAlgebra ν).right.obj.obj (op V)),
        (∃ b, (φ.right.hom.app (op V)).hom b = a) →
        ∃ ab, (g.appLE (relativeSpecToBase B ⁻¹ᵁ V) (ν ⁻¹ᵁ V) hle).hom ab = a := by
  have : IsAffineHom (Over.mk (relativeSpecToBase B)).hom := isAffineHom_relativeSpecToBase B
  obtain ⟨u, hu⟩ : ∃ u : Over.mk ν ⟶ Over.mk (relativeSpecToBase B),
      pushforwardAlgebraMap u = (pushforwardAlgebraIso B).hom ≫ φ := by
    refine ⟨(overHomEquivAlgebraHom (Over.mk ν) (Over.mk (relativeSpecToBase B))).symm
      ((pushforwardAlgebraIso B).hom ≫ φ), ?_⟩
    rw [← overHomEquivAlgebraHom_apply]
    exact (overHomEquivAlgebraHom (Over.mk ν) (Over.mk (relativeSpecToBase B))).apply_symm_apply _
  refine ⟨u.left, Over.w u, ?_⟩
  rintro V hle a ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := AlgebraSheaf.surjective_app_of_iso (pushforwardAlgebraIso B) V b
  refine ⟨b', ?_⟩
  have happ : (pushforwardAlgebraMap u).right.hom.app (op V) =
      u.left.appLE (relativeSpecToBase B ⁻¹ᵁ V) (ν ⁻¹ᵁ V) hle :=
    pushforwardAlgebraMap_app u V hle
  rw [← happ, hu]
  have hcomp : ((pushforwardAlgebraIso B).hom ≫ φ).right.hom.app (op V) =
      (pushforwardAlgebraIso B).hom.right.hom.app (op V) ≫ φ.right.hom.app (op V) := rfl
  rw [hcomp]
  exact (congrArg (φ.right.hom.app (op V)).hom hb').trans hb

end RelativeSpec


section Main

open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

/-- **Zariski's Main Theorem, given the finite subalgebra approximation of [Stacks, Tag 0817].**
A quasi-finite separated morphism onto a quasi-compact base factors as a quasi-compact open
immersion followed by a finite morphism, provided that every finite family of sections of
`ν_* 𝒪` over opens of the base is reached by a finite quasi-coherent subalgebra, where `ν` is
the structure morphism of the relative normalization. -/
theorem exists_isOpenImmersion_isFinite_factorization_of_exists_finiteSubalgebra
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace S]
    (hsub : ∀ (Ξ : Type u) (_ : Finite Ξ) (W : Ξ → S.Opens) (_ : ∀ x, IsAffineOpen (W x))
        (s : ∀ x, (pushforwardAlgebra f.fromNormalization).right.obj.obj (op (W x))),
      ∃ (B : AlgebraSheaf S) (_ : AlgebraSheaf.IsQuasicoherent B)
        (_ : AlgebraSheaf.IsFinite B) (φ : B ⟶ pushforwardAlgebra f.fromNormalization),
        ∀ x, ∃ y, (φ.right.hom.app (op (W x))).hom y = s x) :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
      IsOpenImmersion j ∧ QuasiCompact j ∧ IsFinite π ∧ f = j ≫ π := by
  classical
  have hcomp : f.toNormalization ≫ f.fromNormalization = f := f.toNormalization_fromNormalization
  obtain ⟨ι, hι, V, hV, a, hbo, hcov⟩ := exists_basicOpen_cover_opensRange f
  have hgenall := fun i => exists_generators_basicOpen f (hV i) (a i) (hbo i)
  choose κ hκ c n t hnum hgen using hgenall
  obtain ⟨B, hBqc, hBfin, φ, hreach⟩ := hsub (Σ i : ι, Option (κ i)) inferInstance
    (fun x => V x.1) (fun x => hV x.1) (fun x => x.2.elim (a x.1) fun l => c x.1 l)
  have hBqc' := hBqc
  obtain ⟨g, hgν, hab⟩ := exists_comparison f.fromNormalization B φ
  have hπ₀ : IsFinite (relativeSpecToBase B) := isFinite_relativeSpecToBase B hBfin
  have hgp : ∀ i, f.fromNormalization ⁻¹ᵁ V i
      = g ⁻¹ᵁ (relativeSpecToBase B ⁻¹ᵁ V i) := fun i => by
    rw [← Scheme.Hom.comp_preimage, hgν]
  have hexab : ∀ i, ∃ ab : Γ(relativeSpec B, relativeSpecToBase B ⁻¹ᵁ V i),
      (g.appLE (relativeSpecToBase B ⁻¹ᵁ V i) (f.fromNormalization ⁻¹ᵁ V i)
        (le_of_eq (hgp i))).hom ab = a i :=
    fun i => hab (V i) (le_of_eq (hgp i)) (a i) (hreach ⟨i, none⟩)
  choose ab hab' using hexab
  have hP : ∀ i, IsAffineOpen (relativeSpecToBase B ⁻¹ᵁ V i) := fun i =>
    isAffineOpen_preimage_relativeSpecToBase B ⟨V i, hV i⟩
  have hgZ : ∀ i, g ⁻¹ᵁ ((relativeSpec B).basicOpen (ab i)) = f.normalization.basicOpen (a i) :=
    fun i => by
      rw [preimage_basicOpen_appLE g (le_of_eq (hgp i)) (ge_of_eq (hgp i)) (ab i), hab' i]
  have hsurj : ∀ i, Function.Surjective ((f.toNormalization ≫ g).app
      ((relativeSpec B).basicOpen (ab i))) := by
    intro i
    have hc : ∀ l, ∃ cb, (g.appLE (relativeSpecToBase B ⁻¹ᵁ V i)
        (f.fromNormalization ⁻¹ᵁ V i) (le_of_eq (hgp i))).hom cb = c i l :=
      fun l => hab (V i) (le_of_eq (hgp i)) (c i l) (hreach ⟨i, some l⟩)
    have hρ := surjective_appLE_basicOpen f.fromNormalization (relativeSpecToBase B) g hgν
      (ab i) (hP i) (a i) (hgp i) (hab' i) (hgZ i) (c i) (n i) (t i) hc (hnum i) (hgen i)
    rw [Scheme.Hom.appLE] at hρ
    have hiso : IsIso (f.normalization.presheaf.map
        (homOfLE (le_of_eq (hgZ i).symm)).op) :=
      Stacks.AffineAlgebraEquivalence.isIso_map_homOfLE _ (le_of_eq (hgZ i))
    have hgapp : Function.Surjective (g.app ((relativeSpec B).basicOpen (ab i))) :=
      surjective_of_comp_isIso _ hρ
    have hiso2 : IsIso (f.toNormalization.app (g ⁻¹ᵁ ((relativeSpec B).basicOpen (ab i)))) := by
      refine Scheme.Hom.isIso_app _ _ ?_
      rw [hgZ i]
      exact hbo i
    rw [Scheme.Hom.comp_app]
    exact surjective_comp hgapp (ConcreteCategory.bijective_of_isIso
      (f.toNormalization.app (g ⁻¹ᵁ ((relativeSpec B).basicOpen (ab i))))).2
  have hci : ∀ i, IsClosedImmersion ((f.toNormalization ≫ g) ∣_
      ((relativeSpec B).basicOpen (ab i))) := by
    intro i
    refine isClosedImmersion_morphismRestrict _ _ ((hP i).basicOpen (ab i)) ?_ (hsurj i)
    rw [Scheme.Hom.comp_preimage, hgZ i]
    exact isAffineOpen_preimage_basicOpen f (hV i) (a i) (hbo i)
  have hrange : Set.range (f.toNormalization ≫ g) ⊆
      ((⨆ i, (relativeSpec B).basicOpen (ab i) : (relativeSpec B).Opens) :
        Set (relativeSpec B)) := by
    rintro y ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ⟨x, rfl⟩)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [Scheme.Hom.comp_apply]
    have h5 : f.toNormalization x ∈ g ⁻¹ᵁ ((relativeSpec B).basicOpen (ab i)) := by
      rw [hgZ i]
      exact hi
    exact h5
  have hrr : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi fe hfe => by
      have h1 : IsOpenImmersion i := hi
      have h2 : IsImmersion fe := hfe
      infer_instance⟩
  have himm : IsImmersion (f.toNormalization ≫ g) := by
    refine IsZariskiLocalAtTarget.of_range_subset_iSup
      (fun i => (relativeSpec B).basicOpen (ab i)) hrange fun i => ?_
    have := hci i
    infer_instance
  have hqc : QuasiCompact (f.toNormalization ≫ g) := by
    have h6 : QuasiCompact ((f.toNormalization ≫ g) ≫ relativeSpecToBase B) := by
      rw [Category.assoc, hgν, hcomp]
      infer_instance
    exact QuasiCompact.of_comp _ (relativeSpecToBase B)
  obtain ⟨T, j, k, hj, hk, hjk⟩ := (IsImmersion.isImmersion_iff_exists_of_quasiCompact
    (f := f.toNormalization ≫ g)).mp himm
  have hjk' : QuasiCompact (j ≫ k) := by rw [hjk]; exact hqc
  have hk' := hk
  refine ⟨T, j, k ≫ relativeSpecToBase B, hj, QuasiCompact.of_comp j k, inferInstance, ?_⟩
  rw [← Category.assoc, hjk, Category.assoc, hgν, hcomp]

end Main

end Stacks.FiniteFactorization

end
