module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Topology.Sets.OpenCover
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01PY: affine nonvanishing opens force separatedness

Let `X` be a scheme and `L` an invertible sheaf of `𝒪_X`-modules.  Suppose every point of `X`
lies in a nonvanishing open `X_s` of a global section `s` of some positive tensor power
`L^{⊗ n}`, and that each such `X_s` is *affine*.  Then `X` is separated
([Stacks, Tag 01PY]).

## Main results

* `AlgebraicGeometry.Scheme.Modules.isSeparated_of_affine_nonvanishingOpen_cover`: a scheme
  covered by affine nonvanishing opens of global sections of positive tensor powers of an
  invertible sheaf is separated (Tag 01PY).
* `Stacks.SheafOfModules.exists_section_ratio`: two global sections of an invertible sheaf are
  proportional over the nonvanishing open of the first.
* `Stacks.SheafOfModules.basicOpen_le_nonvanishingOpen_of_smul_eq`: a section obtained by
  multiplying by a function is nonvanishing wherever that function is invertible.

## The argument

Separatedness is checked with Mathlib's valuative criterion
(`AlgebraicGeometry.IsSeparated.of_valuativeCriterion`), which needs `X` quasi-separated and
needs any two morphisms `Spec A ⟶ X`, from a local domain `A` with fraction field `K`, agreeing
on `Spec K`, to be equal.

Quasi-separatedness is `Scheme.quasiSeparatedSpace_of_isOpenCover` applied to the family of
affine nonvanishing opens: they cover `X` by hypothesis, each is affine, and a pairwise
intersection `X_s ∩ X_t` is affine — hence compact — by Tag 01PV
(`AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`), which is exactly the
statement that an affine open meets a nonvanishing open in an affine open.

For the lifting half, the closed point of `Spec A` goes into some `X_s` under `f` and into some
`X_t` under `g`, for sections of two possibly different powers `L^{⊗ n}` and `L^{⊗ m}`.  Both are
replaced by sections of the single power `L^{⊗ nm}` with the same nonvanishing opens, using
`AlgebraicGeometry.exists_section_power_nonvanishingOpen_eq` and the reindexing isomorphism
`Stacks.SheafOfModules.Invertible.tensorPowerReindex` (whose effect on nonvanishing loci is
`Stacks.SheafOfModules.nonvanishingLocus_sectionsMap`).  Since `Spec A` is local, each morphism
then maps *all* of `Spec A` into the corresponding nonvanishing open.  The heart of the proof,
`image_nonvanishing_of_generic_eq`, shows that the image of `g` lies in `X_s` as well: the two
sections are proportional on `X_s ∩ X_t` with mutually inverse factors, and the pullback of one
factor along `g` becomes invertible on `Y` because `Γ` of the dominant morphism `Spec K ⟶ Spec A`
is injective.  Both morphisms then land in the single affine open `X_s`, where they lift through
its open immersion and are equal by `ext_of_isDominant_of_isSeparated`.

## Implementation notes

Everything about sections and nonvanishing opens is stated for a ringed space `X` and a sheaf of
modules over `structureSheafRing X`, not for a scheme and `X.Modules`.  This is forced:
`structureSheafRing` is a `@[reducible] def` whose underlying ring presheaf is syntactically
`X.presheaf ⋙ forget₂ CommRingCat RingCat`, whereas `Scheme.ringCatSheaf` is semireducible.  With
`L : X.Modules`, the scalar action of `Γ(X, U)` on `L.val.obj (op U)` is therefore not found by
instance search at all — the whole `•` vocabulary of the proof fails to elaborate.  Stating the
lemmas over a ringed space makes every such instance available, and the scheme-level statements
apply them at `X.toRingedSpace`, where unification discharges the identification once, at default
transparency.  No transparency option is used, in particular no file-scope
`backward.isDefEq.respectTransparency false`.

`Scheme.Hom.appLE` takes the inclusion of opens as a proof argument, so rewriting the *morphism*
inside an `appLE` has an ill-typed motive; `appLE_congr_hom` replaces that rewrite.

## References

* [EGA II, Proposition 4.5.6]
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpStalk grpGerm)

universe u

namespace Stacks.SheafOfModules

section Ratio

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  {L : _root_.SheafOfModules.{u} (structureSheafRing X)}
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- **Two global sections of an invertible sheaf differ by a function on the nonvanishing
locus of the first.**  There is `r ∈ 𝒪_X(X_s)` with `t = r • s` over every open contained
in `X_s`. -/
theorem exists_section_ratio (s t : L.sections) :
    ∃ r : X.presheaf.obj (op (nonvanishingOpen L s)),
      ∀ (W : Opens X.carrier) (hW : W ≤ nonvanishingOpen L s),
        X.presheaf.map (homOfLE hW).op r • s.eval (op W) = t.eval (op W) := by
  obtain ⟨r, hr0⟩ := (bijective_smul_eval_of_le_nonvanishingOpen L s
    (nonvanishingOpen L s) le_rfl).surjective (t.eval (op (nonvanishingOpen L s)))
  have hr : r • s.eval (op (nonvanishingOpen L s)) =
    t.eval (op (nonvanishingOpen L s)) := hr0
  refine ⟨r, fun W hW => ?_⟩
  have h1 : X.presheaf.map (homOfLE hW).op r • s.eval (op W) =
      L.val.map (homOfLE hW).op (r • s.eval (op (nonvanishingOpen L s))) := by
    rw [L.val.map_smul, PresheafOfModules.sections_property s (homOfLE hW).op]
    rfl
  rw [h1, hr, PresheafOfModules.sections_property t (homOfLE hW).op]

/-- **If `t = r • s` over an open inside `X_s`, then `t` is nonvanishing wherever `r` is a
unit.**  That is, the basic open `X_r` is contained in `X_t`. -/
theorem basicOpen_le_nonvanishingOpen_of_smul_eq (s t : L.sections) (U : Opens X.carrier)
    (hU : U ≤ nonvanishingOpen L s) (r : X.presheaf.obj (op U))
    (hr : r • s.eval (op U) = t.eval (op U)) :
    X.basicOpen r ≤ nonvanishingOpen L t := by
  intro x hx
  have hxU : x ∈ U := X.basicOpen_le r hx
  have hs : grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) ∉
      IsLocalRing.maximalIdeal (ringStalk X x) •
        (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x)) := hU hxU
  obtain ⟨v, hv⟩ := (X.mem_basicOpen r x hxU).mp hx
  have key : grpGerm X L.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) =
      ringGerm X x U hxU r • grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) := by
    rw [← grpGerm_eval t x U hxU, ← hr,
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul, grpGerm_eval]
  have hv' : ringGerm X x U hxU r = (↑v : ringStalk X x) := hv.symm
  change grpGerm X L.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) ∉ _
  intro hmem
  refine hs ?_
  have hback : grpGerm X L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) =
      (↑v⁻¹ : ringStalk X x) •
        grpGerm X L.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) := by
    rw [key, hv', smul_smul, Units.inv_mul, one_smul]
  rw [hback]
  exact Submodule.smul_mem _ _ hmem

end Ratio

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- The global-sections map of `Spec K ⟶ Spec A`, for `K` the fraction field of a domain `A`,
is injective. -/
public theorem fraction_appTop_injective (A K : Type u)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Function.Injective (Spec.map (CommRingCat.ofHom (algebraMap A K))).appTop := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).injective
  apply FaithfulSMul.algebraMap_injective A K
  have H := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A K))
  exact (congrArg (fun e => e a) H).symm.trans
    ((congrArg (Scheme.ΓSpecIso (.of K)).hom hab).trans (congrArg (fun e => e b) H))

/-- Two equal morphisms of schemes have the same `appLE` map, for any two proofs of the
inclusion of opens. -/
private theorem appLE_congr_hom {X Z : Scheme.{u}} {k₁ k₂ : Z ⟶ X} (hk : k₁ = k₂)
    (V : X.Opens) (W : Z.Opens) (p : W ≤ k₁ ⁻¹ᵁ V) (q : W ≤ k₂ ⁻¹ᵁ V) :
    k₁.appLE V W p = k₂.appLE V W q := by
  subst hk
  rfl

/-- **The key step of Tag 01PY.**  Let `f, g : Y ⟶ X` agree after precomposition with a
morphism `i : Z ⟶ Y` whose global-sections map is injective, and suppose the image of `f` lies
in `X_s` and the image of `g` in `X_t`.  Then the image of `g` lies in `X_s` as well. -/
private theorem image_nonvanishing_of_generic_eq {X Y Z : Scheme.{u}}
    (i : Z ⟶ Y) (hi : Function.Injective i.appTop) (f g : Y ⟶ X)
    (hfg : i ≫ f = i ≫ g)
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s t : L.sections)
    (hf : ∀ y, f y ∈ nonvanishingOpen (X := X.toRingedSpace) L s)
    (hg : ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) L t) :
    ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) L s := by
  have _ : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  set U := nonvanishingOpen (X := X.toRingedSpace) L s
  set V := nonvanishingOpen (X := X.toRingedSpace) L t
  obtain ⟨a, ha⟩ := exists_section_ratio s t
  obtain ⟨b, hb⟩ := exists_section_ratio t s
  set W := U ⊓ V
  set aW := X.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op a
  set bW := X.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op b
  have hab : bW * aW = 1 := by
    apply (bijective_smul_eval_of_le_nonvanishingOpen L s W inf_le_left).injective
    change (bW * aW) • s.eval (op W) = 1 • s.eval (op W)
    calc
      _ = bW • (aW • s.eval (op W)) := mul_smul _ _ _
      _ = bW • t.eval (op W) := congrArg (bW • ·) (ha W inf_le_left)
      _ = s.eval (op W) := hb W inf_le_right
      _ = _ := (one_smul _ _).symm
  have hfU : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U := fun y _ => hf y
  have hgV : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ V := fun y _ => hg y
  have hkU : (⊤ : Z.Opens) ≤ (i ≫ f) ⁻¹ᵁ U := fun z _ => hf (i z)
  have hkV : (⊤ : Z.Opens) ≤ (i ≫ f) ⁻¹ᵁ V := by
    rw [hfg]
    exact fun z _ => hg (i z)
  have hkW : (⊤ : Z.Opens) ≤ (i ≫ f) ⁻¹ᵁ W := fun z hz => ⟨hkU hz, hkV hz⟩
  set aY := f.appLE U ⊤ hfU a
  set bY := g.appLE V ⊤ hgV b
  have hitop : i.appLE ⊤ ⊤ (by simp) = i.appTop := by
    simp [Scheme.Hom.appLE]
    rfl
  have hiapp : ∀ (h : Y ⟶ X) (O : X.Opens) (h1 : (⊤ : Y.Opens) ≤ h ⁻¹ᵁ O)
      (h2 : (⊤ : Z.Opens) ≤ (i ≫ h) ⁻¹ᵁ O) (c : Γ(X, O)),
      i.appTop (h.appLE O ⊤ h1 c) = (i ≫ h).appLE O ⊤ h2 c := by
    intro h O h1 h2 c
    rw [← hitop]
    exact congrArg (fun e => e c) (Scheme.Hom.appLE_comp_appLE i h O ⊤ ⊤ h1 (by simp))
  have hib : i.appTop bY = (i ≫ f).appLE V ⊤ hkV b :=
    (hiapp g V hgV (hfg ▸ hkV) b).trans
      (congrArg (fun e => e b) (appLE_congr_hom hfg.symm V ⊤ _ hkV))
  have hWa : (i ≫ f).appLE W ⊤ hkW aW = (i ≫ f).appLE U ⊤ hkU a :=
    congrArg (fun e => e a) ((i ≫ f).map_appLE hkW (homOfLE inf_le_left).op)
  have hWb : (i ≫ f).appLE W ⊤ hkW bW = (i ≫ f).appLE V ⊤ hkV b :=
    congrArg (fun e => e b) ((i ≫ f).map_appLE hkW (homOfLE inf_le_right).op)
  have hbaY : bY * aY = 1 := by
    apply hi
    rw [map_mul, map_one, hiapp f U hfU hkU, hib, ← hWa, ← hWb, ← map_mul, hab, map_one]
  have hbasic : g ⁻¹ᵁ X.basicOpen b = ⊤ := by
    have H := Scheme.basicOpen_appLE g ⊤ V hgV b
    rw [Y.basicOpen_of_isUnit (isUnit_iff_exists_inv.mpr ⟨aY, hbaY⟩), top_inf_eq] at H
    exact H.symm
  have hbs := basicOpen_le_nonvanishingOpen_of_smul_eq t s V le_rfl b
    ((show X.presheaf.map (homOfLE (le_refl V)).op b = b from
      ConcreteCategory.congr_hom (X.presheaf.map_id (op V)) b) ▸ hb V le_rfl)
  exact fun y => hbs (hbasic.ge (Opens.mem_top y))

/-- `Spec K ⟶ Spec A` is dominant for `K` the fraction field of a domain `A`. -/
public theorem specMap_fraction_isDominant (A K : Type u)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap A K))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  exact ((RingHom.injective_iff_ker_eq_bot _).mp
    (FaithfulSMul.algebraMap_injective A K)).trans_le bot_le

/-- **Two morphisms `Spec A ⟶ X` landing in one affine open and agreeing on `Spec K` are
equal.**  Here `A` is a domain with fraction field `K`. -/
private theorem specHom_eq_of_fraction_eq_of_affineOpen
    (A K : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (f g : Spec (.of A) ⟶ X)
    (hf : ∀ x : Spec (.of A), f x ∈ U) (hg : ∀ x : Spec (.of A), g x ∈ U)
    (hfg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g) : f = g := by
  have hfr : Set.range f.base ⊆ Set.range U.ι.base := by
    simpa [Set.range_subset_iff, Scheme.Opens.range_ι] using hf
  have hgr : Set.range g.base ⊆ Set.range U.ι.base := by
    simpa [Set.range_subset_iff, Scheme.Opens.range_ι] using hg
  have hfg' : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
        IsOpenImmersion.lift U.ι f hfr =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ IsOpenImmersion.lift U.ι g hgr := by
    apply (cancel_mono U.ι).mp
    simpa [Category.assoc, IsOpenImmersion.lift_fac] using hfg
  have _ : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    specMap_fraction_isDominant A K
  have _ : IsAffine U.toScheme := hU
  have hfgg : IsOpenImmersion.lift U.ι f hfr = IsOpenImmersion.lift U.ι g hgr :=
    ext_of_isDominant_of_isSeparated (terminal.from U.toScheme) (by simp)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) hfg'
  rw [← IsOpenImmersion.lift_fac U.ι f hfr, ← IsOpenImmersion.lift_fac U.ι g hgr, hfgg]

/-- A morphism out of the spectrum of a local ring lands in any open containing the image of
the closed point. -/
private theorem specMap_image_subset_of_closedPoint_mem
    (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : Spec (.of A) ⟶ X) (U : X.Opens)
    (hx : f (IsLocalRing.closedPoint A) ∈ U) : ∀ x : Spec (.of A), f x ∈ U :=
  fun x => (Scheme.preimage_eq_top_of_closedPoint_mem f hx).ge (Opens.mem_top x)

/-- **The valuative-criterion step of Tag 01PY, for a single invertible sheaf.**  Two
morphisms `Spec A ⟶ X` from the spectrum of a local domain that agree over its fraction field,
with the closed point landing in `X_u` for one and in `X_v` for the other and `X_u` affine, are
equal. -/
private theorem spec_eq_of_affine_nonvanishing {X : Scheme.{u}} (A K : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (M : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (f g : Spec (.of A) ⟶ X)
    (hfg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g)
    (u v : M.sections)
    (hfu : f (IsLocalRing.closedPoint A) ∈
      nonvanishingOpen (X := X.toRingedSpace) M u)
    (hgv : g (IsLocalRing.closedPoint A) ∈
      nonvanishingOpen (X := X.toRingedSpace) M v)
    (hUaff : IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace) M u)) : f = g := by
  have hf : ∀ y, f y ∈ nonvanishingOpen (X := X.toRingedSpace) M u :=
    specMap_image_subset_of_closedPoint_mem A f _ hfu
  have hg : ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) M v :=
    specMap_image_subset_of_closedPoint_mem A g _ hgv
  have hg' := image_nonvanishing_of_generic_eq
    (Spec.map (CommRingCat.ofHom (algebraMap A K)))
    (fraction_appTop_injective A K) f g hfg M u v hf hg
  exact specHom_eq_of_fraction_eq_of_affineOpen A K
    (nonvanishingOpen (X := X.toRingedSpace) M u) hUaff f g hf hg' hfg

variable (X : Scheme.{u}) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **A scheme covered by affine nonvanishing opens is quasi-separated.**  If every point of `X`
lies in an affine nonvanishing open of a global section of some positive tensor power of `L`,
then `X` is quasi-separated. -/
private theorem quasiSeparatedSpace_of_affine_nonvanishingOpen_cover
    (h : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen (nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    QuasiSeparatedSpace X := by
  let I := {p : Σ n : ℕ, (tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections //
      1 ≤ p.1 ∧ IsAffineOpen (nonvanishingOpen
        (X := X.toLocallyRingedSpace.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (p.1 : ℤ)) p.2)}
  let U : I → X.Opens := fun i => nonvanishingOpen
    (X := X.toLocallyRingedSpace.toRingedSpace)
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (i.1.1 : ℤ)) i.1.2
  have hcov : IsOpenCover U := by
    apply IsOpenCover.mk
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨n, hn, s, hxs, ha⟩ := h x
    exact Opens.mem_iSup.mpr ⟨⟨⟨n, s⟩, hn, ha⟩, hxs⟩
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U hcov (fun i => i.2.2) fun i j => ?_
  have hij : IsAffineOpen (U i ⊓ U j) := by
    rw [inf_comm]
    exact isAffineOpen_inf_nonvanishingOpen _ i.1.2 (U j) j.2.2
  exact hij.isCompact

/-- **Stacks Project, Tag 01PY.** A scheme carrying an invertible sheaf of modules such that
every point lies in an *affine* nonvanishing open of a global section of some positive tensor
power is separated. -/
@[stacks 01PY]
public theorem isSeparated_of_affine_nonvanishingOpen_cover
    (h : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen (nonvanishingOpen (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    Scheme.IsSeparated X := by
  have _ : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_affine_nonvanishingOpen_cover X L h
  apply Scheme.IsSeparated.mk
  apply IsSeparated.of_valuativeCriterion
  intro S
  constructor
  rintro ⟨f, hf₁, hf₂⟩ ⟨g, hg₁, hg₂⟩
  ext : 1
  have hfg : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ g := hf₁.trans hg₁.symm
  obtain ⟨n, hn, s, hfs, hUs⟩ := h (f (IsLocalRing.closedPoint S.R))
  obtain ⟨m, hm, t, hgt, hVt⟩ := h (g (IsLocalRing.closedPoint S.R))
  obtain ⟨s', hs'⟩ := exists_section_power_nonvanishingOpen_eq L n s m hm
  obtain ⟨t', ht'⟩ := exists_section_power_nonvanishingOpen_eq L m t n hn
  have hcomm : ((m * n : ℕ) : ℤ) = ((n * m : ℕ) : ℤ) := by rw [Nat.mul_comm]
  have ht'' : nonvanishingOpen (X := X.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ))
        (SheafOfModules.sectionsMap (tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L hcomm).hom t') =
      nonvanishingOpen (X := X.toRingedSpace)
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (m : ℤ)) t :=
    (Opens.ext (nonvanishingLocus_sectionsMap (X := X.toRingedSpace)
      (tensorPowerReindex X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L hcomm) t')).trans ht'
  exact spec_eq_of_affine_nonvanishing S.R S.K
    (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ)) f g hfg s'
    (SheafOfModules.sectionsMap (tensorPowerReindex X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L hcomm).hom t')
    (by rwa [hs']) (by rwa [ht'']) (by rwa [hs'])

end AlgebraicGeometry.Scheme.Modules

end
