module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection

/-!
# Base point free pencils and lifting along a zero scheme

Let `k` be a field, `X` an integral scheme over `k` with `H¹(X, 𝒪_X) = 0`, `ℒ` an invertible
`𝒪_X`-module and `s` a nonzero global section of `ℒ` with zero scheme `i : D ⟶ X`. The sequence
`0 ⟶ 𝒪_X ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` of [Stacks, Tag 0C6K] and the vanishing of `H¹(X, 𝒪_X)` make
`Γ(X, ℒ) ⟶ Γ(X, i_* i^* ℒ)` surjective. This file draws the two consequences that the proof of
[Stacks, Tag 0C6T] uses.

## Main results

* `AlgebraicGeometry.exists_eq_add_smul_of_sup_nvOpen_eq_top`: for an open `V` with
  `V ∪ X_s = X`, every section of `ℒ` over `V` agrees, up to a multiple of `s`, with a global
  section of `ℒ`.
* `AlgebraicGeometry.exists_sup_nvOpen_eq_top`: on a proper integral scheme of dimension at most
  one over `k`, there is a second global section `t` with no common zero with `s`, i.e.
  `X_s ∪ X_t = X`. The section `t` is a lift of a trivialization of `ℒ|_D`.
* `AlgebraicGeometry.nvOpen_ne_top_of_invertibleCurveDegree_pos`: a global section of an
  invertible module of positive degree vanishes somewhere.

## Implementation notes

Surjectivity on global sections is read off the long exact cohomology sequence
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence` and transported from `H⁰` to
`Γ(-, ⊤)` along `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso`. Left exactness of sections
over an open is `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` for the right
adjoint `AlgebraicGeometry.Scheme.Modules.toPresheafOfModules` followed by evaluation.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingLocus sectionsOfTop)
open Stacks.ProjectiveFromSections (nvOpen resT)

universe u

namespace AlgebraicGeometry

/-! ### Generalities on modules over a scheme -/

section General

variable {X : Scheme.{u}}

/-- **Two sections of an `𝒪_X`-module agreeing on the overlap of two opens covering `X` glue
to a global section.** -/
theorem exists_glue_of_sup_eq_top (M : X.Modules) {U₁ U₂ : X.Opens} (h : U₁ ⊔ U₂ = ⊤)
    (a : Γ(M, U₁)) (b : Γ(M, U₂))
    (hab : M.presheaf.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op a =
      M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op b) :
    ∃ c : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : U₁ ≤ ⊤)).op c = a ∧
      M.presheaf.map (homOfLE (le_top : U₂ ≤ ⊤)).op c = b := by
  let U : Bool → X.Opens := fun i => cond i U₁ U₂
  let sf : ∀ i : Bool, ToType (M.presheaf.obj (op (U i))) := fun i =>
    match i with
    | true => a
    | false => b
  have hba : M.presheaf.map (homOfLE (inf_le_left : U₂ ⊓ U₁ ≤ U₂)).op b =
      M.presheaf.map (homOfLE (inf_le_right : U₂ ⊓ U₁ ≤ U₁)).op a := by
    have h' := congrArg (M.presheaf.map (homOfLE (le_of_eq (inf_comm U₂ U₁))).op) hab
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp] at h'
    exact h'.symm
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf U sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · exact hba
    · exact hab
    · rfl
  obtain ⟨g, hg, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing M.isSheaf U sf hcompat
  have htop : (⊤ : X.Opens) ≤ iSup U := by
    rw [← h]
    exact sup_le (le_iSup U true) (le_iSup U false)
  refine ⟨M.presheaf.map (homOfLE htop).op g, ?_, ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hg true
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact hg false

end General

/-! ### Sections of positive degree vanish somewhere -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A global section of an invertible module of positive degree vanishes somewhere.** A
nowhere vanishing section `s` makes multiplication `𝒪_X ⟶ ℒ` by `s` an isomorphism, and an
invertible module isomorphic to `𝒪_X` has degree zero. -/
theorem nvOpen_ne_top_of_invertibleCurveDegree_pos [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hpos : 0 < invertibleCurveDegree k f hdim L) (s : Γ(L, ⊤)) :
    nvOpen L s ≠ ⊤ := by
  intro htop
  have hlocus : nonvanishingLocus (X := X.toRingedSpace) L (sectionsOfTop L s) = Set.univ := by
    rw [nonvanishingLocus_sectionsOfTop_eq]
    exact congrArg (fun U : X.Opens => (U : Set X)) htop
  have hiso := isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ L (sectionsOfTop L s) hlocus
  have h0 := invertibleCurveDegree_eq_zero_of_iso_unit k f hdim L
    (asIso (L.unitHomEquiv.symm (sectionsOfTop L s))).symm
  omega

/-! ### Surjectivity onto the sections along the zero scheme -/

/-- **Global sections of `ℒ` surject onto the global sections of `ℒ` along the zero scheme**, for
a nonzero section `s` of an invertible module on an integral scheme with `H¹(X, 𝒪_X) = 0`. The
sequence `0 ⟶ 𝒪_X ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` of [Stacks, Tag 0C6K] is short exact because `s` is
regular, and the next term of its long exact cohomology sequence is `H¹(X, 𝒪_X) = 0`. -/
theorem surjective_unit_app_top_zeroScheme [IsIntegral X]
    (hH1 : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (sL : L.sections) (hsL : sL.eval (op ⊤) ≠ 0) :
    Function.Surjective (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
      (zeroScheme X L (sL.eval (op ⊤))).subschemeι).unit.app L) ⊤) := by
  have hreg := isRegularSection_of_eval_top_ne_zero L sL hsL
  obtain ⟨hfg, hSE⟩ := shortExact_zeroScheme_of_isRegularSection X L sL hreg
  obtain ⟨d, -, -, hex, -⟩ := exists_cohomologyOverField_longExactSequence k f hSE
  intro q
  let g := (Scheme.Modules.pullbackPushforwardAdjunction
    (zeroScheme X L (sL.eval (op ⊤))).subschemeι).unit.app L
  let eQ := cohomologyOverFieldZeroLinearIso k f
    ((Scheme.Modules.pushforward (zeroScheme X L (sL.eval (op ⊤))).subschemeι).obj
      ((Scheme.Modules.pullback (zeroScheme X L (sL.eval (op ⊤))).subschemeι).obj L))
  have hsub : Subsingleton
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) (0 + 1)) :=
    ModuleCat.subsingleton_of_isZero hH1
  obtain ⟨x, hx⟩ := (hex 0 (eQ.inv q)).mp (Subsingleton.elim _ _)
  refine ⟨(cohomologyOverFieldZeroLinearIso k f L).hom x, ?_⟩
  have key := cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f g x
  refine key.symm.trans ?_
  show eQ.hom _ = q
  rw [hx]
  exact eQ.inv_hom_id_apply q

/-! ### A base point free pencil -/

/-- **Every global section of an invertible module is the evaluation of a section `sL`**, whose
nonvanishing locus is that of the global section. -/
private theorem exists_sections_eval_eq (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (s : Γ(L, ⊤)) :
    ∃ sL : (Stacks.NonvanishingSpelling.toSheafOfModules X L).sections,
      sL.eval (op ⊤) = s ∧ (nvOpen L s : Set X) = nonvanishingLocus (X := X.toRingedSpace) L sL :=
  ⟨_, (Stacks.NonvanishingSpelling.sectionsEquiv X L).apply_symm_apply s,
    (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X L s).symm⟩

/-- **A second section without common zeros.** Let `X` be a proper integral scheme of dimension
at most one over `k` with `H¹(X, 𝒪_X) = 0`, and let `s` be a nonzero global section of an
invertible module `ℒ`. Then there is a global section `t` of `ℒ` such that `s` and `t` have no
common zero: `X_s ∪ X_t = X`.

With `i : D ⟶ X` the zero scheme of `s`, the restriction `i^* ℒ` is trivial
(`AlgebraicGeometry.nonempty_pullback_zeroScheme_iso_unit`), and `t` is a lift, along the
surjection `Γ(X, ℒ) ⟶ Γ(D, i^* ℒ)`, of a nowhere vanishing section of `i^* ℒ`. So `t` vanishes
at no point of `D`, and `D` is exactly where `s` vanishes. -/
theorem exists_sup_nvOpen_eq_top [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hH1 : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    ∃ t : Γ(L, ⊤), nvOpen L s ⊔ nvOpen L t = ⊤ := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  obtain ⟨sL, hsLs, hnv⟩ := exists_sections_eval_eq L s
  have hsL : sL.eval (op ⊤) ≠ 0 := hsLs ▸ hs
  set i := (zeroScheme X L (sL.eval (op ⊤))).subschemeι with hi
  let D := (zeroScheme X L (sL.eval (op ⊤))).subscheme
  obtain ⟨e⟩ := nonempty_pullback_zeroScheme_iso_unit k f hdim L sL hsL
  let one₀ : Γ(SheafOfModules.unit D.ringCatSheaf, ⊤) := (1 : Γ(D, ⊤))
  let q₀ : Γ((Scheme.Modules.pullback i).obj L, ⊤) := e.inv.app ⊤ one₀
  obtain ⟨t, ht⟩ := surjective_unit_app_top_zeroScheme f hH1 L sL hsL q₀
  refine ⟨t, ?_⟩
  have hpull : pullbackGlobalSections i L t = q₀ := by
    show ((Scheme.Modules.pullback i).obj L).presheaf.map
      (eqToHom (show i ⁻¹ᵁ (⊤ : X.Opens) = ⊤ from rfl)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) ⊤
        t) = q₀
    rw [ht]
    exact Functor.map_id_apply _ _ _
  have _ : ∀ x : D.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk D.toRingedSpace x) :=
    fun x => D.isLocalRing x
  have hunit : Stacks.Ample.nonvanishingLocus (SheafOfModules.unit D.ringCatSheaf)
      one₀ = Set.univ := by
    refine (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq D
      (SheafOfModules.unit D.ringCatSheaf) one₀).symm.trans ?_
    refine (Stacks.SheafOfModules.nonvanishingLocus_unit_eq_basicOpen D.toRingedSpace
      ((Stacks.NonvanishingSpelling.sectionsEquiv D (SheafOfModules.unit D.ringCatSheaf)).symm
        one₀)).trans ?_
    have h1 : ((Stacks.NonvanishingSpelling.sectionsEquiv D
        (SheafOfModules.unit D.ringCatSheaf)).symm one₀).eval (op ⊤) = (1 : Γ(D, ⊤)) :=
      (Stacks.NonvanishingSpelling.sectionsEquiv D
        (SheafOfModules.unit D.ringCatSheaf)).apply_symm_apply one₀
    show ((D.basicOpen _ : D.Opens) : Set D) = Set.univ
    rw [h1, Scheme.basicOpen_one]
    rfl
  have hD : Set.range i ⊆ Stacks.Ample.nonvanishingLocus L t := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ i.base ⁻¹' Stacks.Ample.nonvanishingLocus L t := by
      have hc := Stacks.Ample.nonvanishingLocus_congr e.symm one₀
      rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, hpull,
        show q₀ = e.symm.hom.app ⊤ one₀ from rfl, hc, hunit]
      exact Set.mem_univ z
    exact hz
  have hs' : (nvOpen L s : Set X) = (zeroScheme X L (sL.eval (op ⊤))).supportSetᶜ := by
    rw [hnv, nonvanishingLocus_eq_compl_supportSet_zeroScheme L sL hsL]
  refine eq_top_iff.mpr fun x _ => ?_
  by_cases hx : x ∈ nvOpen L s
  · exact Opens.mem_sup.mpr (Or.inl hx)
  · refine Opens.mem_sup.mpr (Or.inr ?_)
    have hxD : x ∈ (zeroScheme X L (sL.eval (op ⊤))).supportSet := by
      by_contra hc
      exact hx (show x ∈ (nvOpen L s : Set X) by rw [hs']; exact hc)
    have hxr : x ∈ Set.range i := by
      rw [hi, Scheme.IdealSheafData.range_subschemeι]; exact hxD
    exact hD hxr

/-! ### Lifting a section along an open containing the zero scheme -/

/-- **A section of `ℒ` over an open containing the zero locus of `s` is, up to a multiple of `s`,
the restriction of a global section.** Let `X` be integral with `H¹(X, 𝒪_X) = 0`, `s` a nonzero
global section of an invertible `ℒ`, and `V` an open with `V ∪ X_s = X`. For every `β ∈ Γ(V, ℒ)`
there are `σ ∈ Γ(X, ℒ)` and `c ∈ Γ(V, 𝒪_X)` with `σ|_V = β + c · s|_V`.

The section of `i_* i^* ℒ` equal to the image of `β` over `V` and to zero over `X_s` is well
defined, because over `V ∩ X_s` the section `β` is a multiple of `s`; it lifts to a global
section `σ` of `ℒ`, and `σ|_V - β` is killed by `ℒ ⟶ i_* i^* ℒ`, hence is a multiple of `s` by
left exactness of sections over `V`. -/
theorem exists_eq_add_smul_of_sup_nvOpen_eq_top [IsIntegral X]
    (hH1 : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (V : X.Opens) (hV : V ⊔ nvOpen L s = ⊤) (β : Γ(L, V)) :
    ∃ (σ : Γ(L, ⊤)) (c : Γ(X, V)), resT V σ = β + c • resT V s := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  obtain ⟨sL, hsLs, hnv⟩ := exists_sections_eval_eq L s
  have hsL : sL.eval (op ⊤) ≠ 0 := hsLs ▸ hs
  have hreg := isRegularSection_of_eval_top_ne_zero L sL hsL
  obtain ⟨hfg, hSE⟩ := shortExact_zeroScheme_of_isRegularSection X L sL hreg
  set i := (zeroScheme X L (sL.eval (op ⊤))).subschemeι with hi
  set g := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L with hg
  set Q := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) with hQ
  -- multiplication by `s` on sections over `W`
  have hφ : ∀ (W : X.Opens) (c : Γ(X, W)),
      Scheme.Modules.Hom.app (L.unitHomEquiv.symm sL) W c = c • resT W s := by
    intro W c
    have h := Scheme.Modules.unitHomEquiv_symm_app_apply L sL W c
    rw [hsLs] at h
    exact h
  -- `g` kills multiples of `s`
  have hgs : ∀ (W : X.Opens) (c : Γ(X, W)), g.app W (c • resT W s) = 0 := by
    intro W c
    rw [← hφ]
    have h := congrArg (fun φ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ Q =>
      ConcreteCategory.hom (Scheme.Modules.Hom.app φ W)
        (show Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), W) from c)) hfg
    exact h
  -- naturality of `g`
  have hnat : ∀ {W W' : X.Opens} (h : W' ≤ W) (m : Γ(L, W)),
      Q.presheaf.map (homOfLE h).op (g.app W m) = g.app W' (L.presheaf.map (homOfLE h).op m) :=
    fun h m => (CategoryTheory.congr_fun ((Scheme.Modules.Hom.mapPresheaf g).naturality
      (homOfLE h).op) m).symm
  have hW : V ⊓ nvOpen L s ≤ nvOpen L s := inf_le_right
  obtain ⟨q, hqV, -⟩ := exists_glue_of_sup_eq_top Q hV (g.app V β) 0 (by
    rw [hnat, map_zero]
    rw [show L.presheaf.map (homOfLE (inf_le_left : V ⊓ nvOpen L s ≤ V)).op β =
        Stacks.ProjectiveFromSections.div s hW
          (L.presheaf.map (homOfLE (inf_le_left : V ⊓ nvOpen L s ≤ V)).op β) •
          resT (V ⊓ nvOpen L s) s from
      (Stacks.ProjectiveFromSections.div_smul s hW _).symm]
    exact hgs _ _)
  obtain ⟨σ₀, hσ⟩ := surjective_unit_app_top_zeroScheme f hH1 L sL hsL q
  let σ : Γ(L, ⊤) := σ₀
  have hker : g.app V (resT V σ - β) = 0 := by
    rw [map_sub, resT, ← hnat, hσ, hqV, sub_self]
  obtain ⟨c, hc⟩ := Stacks.Algebraization.exists_app_eq_of_shortExact _ hSE V
    (show Γ(L, V) from resT V σ - β) hker
  let c' : Γ(X, V) := c
  refine ⟨σ, c', ?_⟩
  have hc' : c' • resT V s = resT V σ - β := (hφ V c').symm.trans hc
  rw [hc']
  abel

end AlgebraicGeometry

end
