module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Topology.Sets.OpenCover
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Separated
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower

/-!
# Separatedness from affine nonvanishing opens

Let `L` be an invertible sheaf of modules on a scheme `X` and assume that every point of `X`
lies in the nonvanishing open of a global section of some positive tensor power of `L`, and that
this nonvanishing open is affine. Then `X` is separated. In particular a scheme carrying an
ample invertible sheaf is separated.

## Main results

* `AlgebraicGeometry.isSeparated_of_exists_affine_nonvanishingOpen`: the separatedness criterion.
* `AlgebraicGeometry.Scheme.Modules.IsAmple.isSeparated`: a scheme with an ample invertible
  sheaf is separated.
* `AlgebraicGeometry.quasiSeparatedSpace_of_exists_affine_nonvanishingOpen`: the
  quasi-separatedness half of the criterion.

## Implementation notes

Quasi-separatedness comes from the cover by the affine nonvanishing opens together with Tag
01PV, `AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen`, which makes every
pairwise intersection affine, hence compact.

Separatedness itself is the uniqueness half of the valuative criterion. Given a valuation ring
`R` with fraction field `K` and two morphisms `f, g : Spec R ⟶ X` agreeing on `Spec K`, the
closed point of `Spec R` lands in an affine nonvanishing open for `f` and in one for `g`; after
replacing the two exponents by their product — which does not change the nonvanishing opens, by
`AlgebraicGeometry.exists_sections_tensorPower_nonvanishingOpen_eq` — the two sections live in
the same tensor power, and the ratio of two sections of an invertible sheaf on the nonvanishing
open of either is a function whose basic open is where the other is nonvanishing. That ratio is
a unit after pulling back along `g`, because it is one after pulling back further to `Spec K` and
`Spec K ⟶ Spec R` is injective on global sections. So the image of `g` also lies in the
nonvanishing open of the first section, and two morphisms into an affine open which agree on a
dominant subscheme agree.

The ratio of two sections is extracted from
`Stacks.SheafOfModules.bijective_smul_eval_of_le_nonvanishingOpen`: on an open inside the
nonvanishing open of `s`, multiplication by `s` is a bijection from functions to sections.

## References

* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (ringStalk ringGerm grpGerm grpStalk stalkModule stalkModule_germ_smul)

universe v₁ u₁ w₁ u

namespace AlgebraicGeometry

/-- Presheaves of abelian groups on the opens of a scheme admit sheafification. -/
noncomputable local instance (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- For presheaves of abelian groups on the opens of a scheme, the morphisms inverted by
sheafification are exactly the locally bijective ones. -/
noncomputable local instance (X : Scheme.{u}) :
    (Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

/-- The stalk of a sheaf of modules on a scheme, as a module over the stalk of the structure
sheaf, in the spelling typeclass search needs for the sheaves of modules of a scheme. -/
noncomputable local instance stalkModuleOfSchemeModules' {X : Scheme.{u}} (F : X.Modules)
    (x : X) : Module (ringStalk X.toRingedSpace x) (grpStalk X.toRingedSpace F.val x) :=
  stalkModule X.toRingedSpace F.val x

section Ratios

variable {X : Scheme.{u}} (L : X.Modules)
  [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-! ### The germ of a global section -/

omit [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
  (structureSheafRing X.toRingedSpace).property L] in
/-- The germ of a global section at a point can be computed over any neighbourhood. -/
private theorem grpGerm_eval_eq (s : L.sections) (U : X.Opens) (x : X) (hx : x ∈ U) :
    grpGerm X.toRingedSpace L.val x U hx (s.eval (op U)) =
      grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) := by
  have h : L.val.map (homOfLE (le_top : U ≤ ⊤)).op (s.eval (op ⊤)) = s.eval (op U) :=
    PresheafOfModules.sections_property s (homOfLE (le_top : U ≤ ⊤)).op
  calc grpGerm X.toRingedSpace L.val x U hx (s.eval (op U))
      = grpGerm X.toRingedSpace L.val x U hx
          (L.val.map (homOfLE (le_top : U ≤ ⊤)).op (s.eval (op ⊤))) := congrArg _ h.symm
    _ = grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) :=
        TopCat.Presheaf.germ_res_apply L.val.presheaf (homOfLE (le_top : U ≤ ⊤)) x hx _

/-! ### Ratios of global sections -/

/-- On the nonvanishing open of `s`, every other global section is a function times `s`. -/
private theorem exists_section_ratio (s t : L.sections) :
    ∃ r : Γ(X, nonvanishingOpen (X := X.toRingedSpace) L s),
      ∀ (W : X.Opens) (hW : W ≤ nonvanishingOpen (X := X.toRingedSpace) L s),
        X.presheaf.map (homOfLE hW).op r • (show Γ(L, W) from s.eval (op W)) =
          (show Γ(L, W) from t.eval (op W)) := by
  set U := nonvanishingOpen (X := X.toRingedSpace) L s with hUdef
  obtain ⟨r, hr⟩ := (bijective_smul_eval_of_le_nonvanishingOpen (X := X.toRingedSpace) L s
    U le_rfl).surjective (t.eval (op U))
  refine ⟨r, fun W hW => ?_⟩
  have hrU : r • (show Γ(L, U) from s.eval (op U)) = (show Γ(L, U) from t.eval (op U)) := hr
  have hsec (u : L.sections) : L.presheaf.map (homOfLE hW).op (show Γ(L, U) from u.eval (op U)) =
      (show Γ(L, W) from u.eval (op W)) := PresheafOfModules.sections_property u (homOfLE hW).op
  rw [← hsec s, ← hsec t, ← hrU]
  exact (Scheme.Modules.map_smul (M := L) (homOfLE hW) r _).symm

/-- If `t` is `r` times `s` on an open inside the nonvanishing open of `s`, then `t` is
nonvanishing exactly on the basic open of `r`. -/
private theorem basicOpen_le_nonvanishingOpen_of_smul_eq (s t : L.sections) (U : X.Opens)
    (hU : U ≤ nonvanishingOpen (X := X.toRingedSpace) L s) (r : Γ(X, U))
    (hr : r • (show Γ(L, U) from s.eval (op U)) = (show Γ(L, U) from t.eval (op U))) :
    X.basicOpen r ≤ nonvanishingOpen (X := X.toRingedSpace) L t := by
  intro x hx
  have hxU := X.basicOpen_le r hx
  have hs := hU hxU
  obtain ⟨u, hu⟩ := (X.toLocallyRingedSpace.toRingedSpace.mem_basicOpen r x hxU).mp hx
  have key : grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) =
      X.toRingedSpace.presheaf.germ U x hxU r •
        grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) := by
    rw [← grpGerm_eval_eq L t U x hxU, ← grpGerm_eval_eq L s U x hxU]
    exact (congrArg (grpGerm X.toRingedSpace L.val x U hxU) hr).symm.trans
      (stalkModule_germ_smul X.toRingedSpace L.val x U hxU r _)
  show grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (t.eval (op ⊤)) ∉ _
  change grpGerm X.toRingedSpace L.val x ⊤ (Opens.mem_top x) (s.eval (op ⊤)) ∉ _ at hs
  intro hm
  refine hs ?_
  rw [key, ← hu] at hm
  have hm' := (IsLocalRing.maximalIdeal (ringStalk X.toRingedSpace x) •
    (⊤ : Submodule (ringStalk X.toRingedSpace x)
      (grpStalk X.toRingedSpace L.val x))).smul_mem (↑u⁻¹ : ringStalk X.toRingedSpace x) hm
  simpa only [smul_smul, Units.inv_mul, one_smul] using hm'

/-! ### Comparing the images of two morphisms -/

/-- A morphism out of the spectrum of a local ring lands inside any open containing the image of
the closed point. -/
private theorem forall_mem_of_closedPoint_mem (A : Type u) [CommRing A] [IsLocalRing A]
    (f : Spec (.of A) ⟶ X) (U : X.Opens) (hx : f (IsLocalRing.closedPoint A) ∈ U) :
    ∀ x : Spec (.of A), f x ∈ U := fun x =>
  show x ∈ f ⁻¹ᵁ U by rw [Scheme.preimage_eq_top_of_closedPoint_mem f hx]; trivial

/-- If `f` and `g` agree after composing with a morphism injective on global sections, and the
image of `f` lies in the nonvanishing open of `s` while the image of `g` lies in that of `t`,
then the image of `g` lies in the nonvanishing open of `s` as well.

The ratio of `t` and `s` is a unit after pulling back along `g`, because its inverse is the
ratio of `s` and `t`, and that identity can be checked after the further composition. -/
private theorem forall_mem_nonvanishingOpen_of_appTop_injective {Y Z : Scheme.{u}} (k : Z ⟶ Y)
    (hk : Function.Injective k.appTop) (f g : Y ⟶ X) (hfg : k ≫ f = k ≫ g) (s t : L.sections)
    (hf : ∀ y, f y ∈ nonvanishingOpen (X := X.toRingedSpace) L s)
    (hg : ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) L t) :
    ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) L s := by
  set U := nonvanishingOpen (X := X.toRingedSpace) L s with hUdef
  set V := nonvanishingOpen (X := X.toRingedSpace) L t with hVdef
  obtain ⟨a, ha⟩ := exists_section_ratio L s t
  obtain ⟨b, hb⟩ := exists_section_ratio L t s
  let aW := X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a
  let bW := X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b
  have hab : bW * aW = 1 := by
    refine (bijective_smul_eval_of_le_nonvanishingOpen (X := X.toRingedSpace) L s (U ⊓ V)
      inf_le_left).injective ?_
    show (bW * aW) • (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V))) =
      (1 : Γ(X, U ⊓ V)) • (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V)))
    calc (bW * aW) • (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V)))
        = bW • (aW • (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V)))) := mul_smul _ _ _
      _ = bW • (show Γ(L, U ⊓ V) from t.eval (op (U ⊓ V))) :=
          congrArg (bW • ·) (ha (U ⊓ V) inf_le_left)
      _ = (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V))) := hb (U ⊓ V) inf_le_right
      _ = (1 : Γ(X, U ⊓ V)) • (show Γ(L, U ⊓ V) from s.eval (op (U ⊓ V))) :=
          (one_smul _ _).symm
  have hfU : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ U := fun y _ => hf y
  have hgV : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ V := fun y _ => hg y
  have hkU : (⊤ : Z.Opens) ≤ (k ≫ f) ⁻¹ᵁ U := fun z _ => hf (k z)
  have hkV : (⊤ : Z.Opens) ≤ (k ≫ f) ⁻¹ᵁ V := by
    intro z _
    show (k ≫ f) z ∈ V
    rw [hfg]
    exact hg (k z)
  have hkW : (⊤ : Z.Opens) ≤ (k ≫ f) ⁻¹ᵁ (U ⊓ V) := fun z hz => ⟨hkU hz, hkV hz⟩
  have hktop : k.appLE ⊤ ⊤ (by simp) = k.appTop :=
    (congrArg (k.appTop ≫ ·) (Z.presheaf.map_id (op ⊤))).trans (Category.comp_id _)
  have key : ∀ (h : Y ⟶ X) (e : Z ⟶ X), k ≫ h = e → ∀ (W : X.Opens) (hW : ⊤ ≤ h ⁻¹ᵁ W)
      (hle : U ⊓ V ≤ W) (hkW : ⊤ ≤ e ⁻¹ᵁ (U ⊓ V)) (c : Γ(X, W)),
      k.appTop (h.appLE W ⊤ hW c) = e.appLE (U ⊓ V) ⊤ hkW (X.presheaf.map (homOfLE hle).op c) := by
    rintro h _ rfl W hW hle hkW c
    have H := Scheme.Hom.appLE_comp_appLE k h W ⊤ ⊤ hW (by simp)
    rw [hktop] at H
    exact (congrArg (fun e => e c) H).trans
      (congrArg (fun e => e c) ((k ≫ h).map_appLE hkW (homOfLE hle).op)).symm
  have hbaY : g.appLE V ⊤ hgV b * f.appLE U ⊤ hfU a = 1 := by
    refine hk ?_
    rw [map_mul, map_one, key g _ hfg.symm V hgV inf_le_right hkW,
      key f _ rfl U hfU inf_le_left hkW, ← map_mul, hab, map_one]
  have hbasic : g ⁻¹ᵁ X.basicOpen b = ⊤ := by
    have H := Scheme.basicOpen_appLE g ⊤ V hgV b
    rw [Y.basicOpen_of_isUnit (isUnit_iff_exists_inv.mpr ⟨_, hbaY⟩), top_inf_eq] at H
    exact H.symm
  have hbs := basicOpen_le_nonvanishingOpen_of_smul_eq L t s V le_rfl b (by
    have H := hb V le_rfl
    rwa [show (homOfLE (le_refl V)).op = 𝟙 (op V) from Subsingleton.elim _ _,
      X.presheaf.map_id] at H)
  exact fun y => hbs (show y ∈ g ⁻¹ᵁ X.basicOpen b by rw [hbasic]; trivial)

/-! ### The fraction field of a valuation ring -/

/-- Two morphisms from the spectrum of a domain into an affine open which agree after passing to
the fraction field are equal. -/
private theorem eq_of_specMap_algebraMap_comp_eq (A K : Type u) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (U : X.Opens) (hU : IsAffineOpen U)
    (f g : Spec (.of A) ⟶ X) (hf : ∀ x : Spec (.of A), f x ∈ U) (hg : ∀ x : Spec (.of A), g x ∈ U)
    (hfg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g) : f = g := by
  have hr : ∀ h : Spec (.of A) ⟶ X, (∀ x, h x ∈ U) → Set.range h.base ⊆ Set.range U.ι.base :=
    fun h hh => by simpa [Set.range_subset_iff, Scheme.Opens.range_ι] using hh
  have hfr := hr f hf
  have hgr := hr g hg
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    AlgebraicGeometry.Scheme.Modules.specMap_fraction_isDominant A K
  have : IsAffine U.toScheme := hU
  have hlift : IsOpenImmersion.lift U.ι f hfr = IsOpenImmersion.lift U.ι g hgr := by
    refine ext_of_isDominant_of_isSeparated (terminal.from U.toScheme) (by simp)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) ?_
    refine (cancel_mono U.ι).mp ?_
    simpa [Category.assoc, IsOpenImmersion.lift_fac] using hfg
  calc f = IsOpenImmersion.lift U.ι f hfr ≫ U.ι := (IsOpenImmersion.lift_fac U.ι f hfr).symm
    _ = IsOpenImmersion.lift U.ι g hgr ≫ U.ι := by rw [hlift]
    _ = g := IsOpenImmersion.lift_fac U.ι g hgr

end Ratios

section Criterion

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-! ### The criterion -/

/-- **A scheme covered by affine nonvanishing opens of sections of positive tensor powers of an
invertible sheaf is quasi-separated.** -/
theorem quasiSeparatedSpace_of_exists_affine_nonvanishingOpen
    (h : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace)
            (Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
            (Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    QuasiSeparatedSpace X := by
  let I := {p : Σ n : ℕ, (Invertible.tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections //
      1 ≤ p.1 ∧ IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (p.1 : ℤ)) p.2)}
  let U : I → X.Opens := fun j => nonvanishingOpen (X := X.toRingedSpace)
    (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (j.1.1 : ℤ)) j.1.2
  have hcov : IsOpenCover U := by
    refine IsOpenCover.mk ?_
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨n, hn, s, hxs, haff⟩ := h x
    exact Opens.mem_iSup.mpr ⟨⟨⟨n, s⟩, hn, haff⟩, hxs⟩
  refine Scheme.quasiSeparatedSpace_of_isOpenCover U hcov (fun j => j.2.2) fun j j' => ?_
  have hjj' : IsAffineOpen (U j ⊓ U j') := by
    rw [inf_comm]
    exact Scheme.Modules.isAffineOpen_inf_nonvanishingOpen _ j.1.2 (U j') j'.2.2
  exact hjj'.isCompact

/-- A scheme is separated as soon as every point lies in an affine nonvanishing open of a global
section of some positive tensor power of an invertible sheaf. -/
@[stacks 01PY]
theorem isSeparated_of_exists_affine_nonvanishingOpen
    (h : ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧
      ∃ s : (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        x ∈ nonvanishingOpen (X := X.toRingedSpace)
            (Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
          IsAffineOpen (nonvanishingOpen (X := X.toRingedSpace)
            (Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s)) :
    Scheme.IsSeparated X := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_exists_affine_nonvanishingOpen L h
  refine Scheme.IsSeparated.mk ?_
  refine IsSeparated.of_valuativeCriterion _ fun S => ?_
  constructor
  rintro ⟨f, hf₁, _⟩ ⟨g, hg₁, _⟩
  ext : 1
  have hfg : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ g := hf₁.trans hg₁.symm
  obtain ⟨n, hn, s, hfs, hUs⟩ := h (f (IsLocalRing.closedPoint S.R))
  obtain ⟨m, hm, t, hgt, _⟩ := h (g (IsLocalRing.closedPoint S.R))
  obtain ⟨s', hs'⟩ := exists_sections_tensorPower_nonvanishingOpen_eq X L n s m hm
  obtain ⟨t', ht'⟩ := exists_sections_tensorPower_nonvanishingOpen_eq X L m t n hn
  let P := Invertible.tensorPower X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ)
  let e : Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((m * n : ℕ) : ℤ) ≅ P :=
    Invertible.tensorPowerReindex X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (by rw [Nat.mul_comm])
  let t'' : P.sections := _root_.SheafOfModules.sectionsMap e.hom t'
  have ht'' : nonvanishingOpen (X := X.toRingedSpace) P t'' =
      nonvanishingOpen (X := X.toRingedSpace) _ t :=
    (Opens.ext (nonvanishingLocus_sectionsMap X.toRingedSpace e t')).trans ht'
  have hf : ∀ y, f y ∈ nonvanishingOpen (X := X.toRingedSpace) P s' := by
    rw [hs']
    exact forall_mem_of_closedPoint_mem S.R f _ hfs
  have hg : ∀ y, g y ∈ nonvanishingOpen (X := X.toRingedSpace) P t'' := by
    rw [ht'']
    exact forall_mem_of_closedPoint_mem S.R g _ hgt
  have hg' := forall_mem_nonvanishingOpen_of_appTop_injective P
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
    (AlgebraicGeometry.Scheme.Modules.fraction_appTop_injective S.R S.K) f g hfg s' t'' hf hg
  exact eq_of_specMap_algebraMap_comp_eq S.R S.K
    (nonvanishingOpen (X := X.toRingedSpace) P s') (by rw [hs']; exact hUs) f g hf hg' hfg

/-- **A scheme carrying an ample invertible sheaf is separated.** -/
@[stacks 09MP]
theorem Scheme.Modules.IsAmple.isSeparated (hL : Scheme.Modules.IsAmple X L) :
    Scheme.IsSeparated X :=
  isSeparated_of_exists_affine_nonvanishingOpen L hL.2

end Criterion

end AlgebraicGeometry

end
