module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplay
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.ArtinRees

/-!
# Injectivity of `colim_n Hom(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

Let `X` be a Noetherian scheme, let `I` be a quasi-coherent sheaf of ideals, let `U = X \ V(I)`,
let `G` be a coherent `𝒪_X`-module and let `F` be a quasi-coherent `𝒪_X`-module. This file proves
that the canonical map `canonicalMapToHomRestrict`

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

is injective.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.smulHomSections`: a morphism `Iⁿ G ⟶ F` read as a
  linear map on the sections over an open.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.toSmulSection`: for a section `g` of `G` over an
  affine open `V`, the linear map `I(V)ⁿ → Γ(Iⁿ G, V)` sending `a` to `a g`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.smulGenHom`: the composite linear map
  `I(V)ⁿ → Γ(F, V)`, `a ↦ φ(a g)`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.smulKill`: the submodule of sections of `G` over
  an affine open that lie in `Iⁿ G` and are annihilated by the morphism.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.app_eq_zero_of_homRestrict_eq_zero`: a morphism
  out of `Iⁿ G` whose restriction to `U` vanishes annihilates every section over an open
  contained in `U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowSections_le_smulKill`: the affine
  case — on one affine open `V` the morphism annihilates `I(V)^{n+N} Γ(G, V)` for some `N`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSections_le_smulKill_of_le`: that
  conclusion descends to a smaller affine open.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_homRestrict_eq_zero`: the
  concrete form of injectivity — a morphism `Iⁿ G ⟶ F` restricting to zero on `U` already dies
  on `I^{n+N} G`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_injective`:
  **injectivity of the first display of [Stacks, Tag 01YB]**.

## Implementation notes

`smulKill` is a submodule of `Γ(G, V)` rather than of `Γ(Iⁿ G, V)`, so that one object records the
bound for every exponent `m ≥ n` at once: the inclusions `I^m G ⟶ Iⁿ G` do not change the value of
a section.

The module structure over `Γ(X, V)` is attached to the notation `Γ(Iⁿ G, V)`, not to the bare
coercion `↥((idealPowerMultiple I n G).toSubmodule.obj (op V))` of the submodule of sections. So
`toSmulSection` is a linear map into `Γ(Iⁿ G, V)` and `smulGenHom` is a composite.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}} {I : X.IdealSheafData} {n : ℕ} {G F : X.Modules}

/-! ### A morphism vanishing away from the support of `I` -/

/-- A morphism `Iⁿ G ⟶ F` restricting to zero on `U` annihilates every section over an open
contained in `U`. -/
public theorem app_eq_zero_of_homRestrict_eq_zero (I : X.IdealSheafData) {n : ℕ}
    {G F : X.Modules} {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X))
    {φ : idealPowSmul I n G ⟶ F} (hφ : homRestrict I hU φ = 0)
    {W : X.Opens} (hW : W ≤ U) (z : Γ(idealPowSmul I n G, W)) :
    φ.app W z = 0 := by
  have h := val_homRestrict_app I hU φ (op (Over.mk (homOfLE hW))) (z.1 : Γ(G, W))
  rw [hφ] at h
  exact h.symm

/-! ### A morphism out of `Iⁿ G`, read off on sections -/

/-- A morphism `Iⁿ G ⟶ F`, as a linear map on the sections over an open. -/
public noncomputable def smulHomSections (φ : idealPowSmul I n G ⟶ F) (V : X.Opens) :
    Γ(idealPowSmul I n G, V) →ₗ[Γ(X, V)] Γ(F, V) where
  toFun z := φ.app V z
  map_add' z w := map_add (ConcreteCategory.hom (φ.app V)) z w
  map_smul' r z := Scheme.Modules.Hom.app_smul φ r z

/-- `smulHomSections φ V` is `φ.app V` on sections. -/
@[simp] public theorem smulHomSections_apply (φ : idealPowSmul I n G ⟶ F) (V : X.Opens)
    (z : Γ(idealPowSmul I n G, V)) : smulHomSections φ V z = φ.app V z := rfl

/-- The inclusion `Iⁿ G ⟶ G`, as a linear map on the sections over an open. -/
public noncomputable def subValSections (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    (V : X.Opens) : Γ(idealPowSmul I n G, V) →ₗ[Γ(X, V)] Γ(G, V) :=
  smulHomSections (idealPowerMultiple I n G).ι V

/-- `subValSections I n G V` sends a section of `Iⁿ G` to its value in `G`. -/
@[simp] public theorem subValSections_apply (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    (V : X.Opens) (z : Γ(idealPowSmul I n G, V)) :
    subValSections I n G V z = (z.1 : Γ(G, V)) := rfl

/-- The submodule of sections of `G` over an affine open which lie in `Iⁿ G` and are annihilated
by `φ`. -/
public noncomputable def smulKill (φ : idealPowSmul I n G ⟶ F) (V : X.affineOpens) :
    Submodule Γ(X, V.1) Γ(G, V.1) :=
  Submodule.map (subValSections I n G V.1) (LinearMap.ker (smulHomSections φ V.1))

/-- A section `t` of `G` over an affine open lies in `smulKill φ V` iff it is a section of `Iⁿ G`
annihilated by `φ`. -/
public theorem mem_smulKill_iff {φ : idealPowSmul I n G ⟶ F} {V : X.affineOpens}
    {t : Γ(G, V.1)} :
    t ∈ smulKill φ V ↔
      ∃ ht : t ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V.1),
        φ.app V.1 ⟨t, ht⟩ = 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨ht, h⟩
    exact ⟨⟨t, ht⟩, h, rfl⟩

/-- A section of `Iⁿ G` whose value lies in the kill submodule is annihilated. -/
public theorem app_eq_zero_of_val_mem_smulKill {φ : idealPowSmul I n G ⟶ F}
    (V : X.affineOpens) (z : Γ(idealPowSmul I n G, V.1))
    (hz : (z.1 : Γ(G, V.1)) ∈ smulKill φ V) :
    φ.app V.1 z = 0 := by
  obtain ⟨ht, h⟩ := mem_smulKill_iff.mp hz
  exact h

/-! ### Multiplying one section of `G` by the sections of `Iⁿ` -/

/-- For a section `g` of `G` over an affine open `V`, the linear map `I(V)ⁿ → Γ(Iⁿ G, V)` sending
`a` to `a g`. -/
public noncomputable def toSmulSection (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    (V : X.affineOpens) (g : Γ(G, V.1)) :
    ↥(I.ideal V ^ n : Ideal Γ(X, V.1)) →ₗ[Γ(X, V.1)] Γ(idealPowSmul I n G, V.1) where
  toFun a := ⟨(a : Γ(X, V.1)) • g,
    le_idealPowerMultiple_obj I n G V (Submodule.smul_mem_smul a.2 Submodule.mem_top)⟩
  map_add' a b := Subtype.ext (by
    change ((a + b : ↥(I.ideal V ^ n : Ideal Γ(X, V.1))) : Γ(X, V.1)) • g
      = (a : Γ(X, V.1)) • g + (b : Γ(X, V.1)) • g
    rw [Submodule.coe_add, add_smul])
  map_smul' r a := Subtype.ext (by
    change ((r • a : ↥(I.ideal V ^ n : Ideal Γ(X, V.1))) : Γ(X, V.1)) • g
      = r • ((a : Γ(X, V.1)) • g)
    rw [SetLike.val_smul, smul_eq_mul, mul_smul])

/-- For a section `g` of `G` over an affine open `V`, the linear map `I(V)ⁿ → Γ(F, V)` sending `a`
to `φ(a g)`. -/
public noncomputable def smulGenHom (φ : idealPowSmul I n G ⟶ F) (V : X.affineOpens)
    (g : Γ(G, V.1)) :
    ↥(I.ideal V ^ n : Ideal Γ(X, V.1)) →ₗ[Γ(X, V.1)] Γ(F, V.1) :=
  (smulHomSections φ V.1).comp (toSmulSection I n G V g)

/-- `smulGenHom φ V g` sends `a` to `φ(a g)`. -/
public theorem smulGenHom_apply (φ : idealPowSmul I n G ⟶ F) (V : X.affineOpens)
    (g : Γ(G, V.1)) (a : Γ(X, V.1)) (ha : a ∈ (I.ideal V ^ n : Ideal Γ(X, V.1)))
    (ha' : a • g ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V.1)) :
    smulGenHom φ V g ⟨a, ha⟩ = φ.app V.1 ⟨a • g, ha'⟩ := rfl

/-! ### The affine case -/

/-- For `f` a section of `I` over an affine open, the section `φ(fⁿ g)` of `F` restricts to zero on
the basic open `D(f)`. -/
public theorem res_basicOpen_smulGenHom_eq_zero {φ : idealPowSmul I n G ⟶ F}
    (hφ : homRestrict I (disjoint_supportCompl_support I) φ = 0) (V : X.affineOpens)
    {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) (g : Γ(G, V.1)) :
    F.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (smulGenHom φ V g ⟨f ^ n, Ideal.pow_mem_pow hf n⟩) = 0 := by
  exact (app_naturality φ (X.basicOpen_le f) (toSmulSection I n G V g _)).trans
    (app_eq_zero_of_homRestrict_eq_zero I _ hφ (basicOpen_le_compl_support I V hf) _)

/-- For `F` quasi-coherent and `f` a section of `I` over an affine open, a power of `f` annihilates
`φ(fⁿ g)`. -/
public theorem exists_pow_smul_smulGenHom_eq_zero [F.IsQuasicoherent]
    {φ : idealPowSmul I n G ⟶ F}
    (hφ : homRestrict I (disjoint_supportCompl_support I) φ = 0) (V : X.affineOpens)
    {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) (g : Γ(G, V.1)) :
    ∃ k : ℕ, f ^ k • smulGenHom φ V g ⟨f ^ n, Ideal.pow_mem_pow hf n⟩ = 0 :=
  Stacks.AlgebraicGeometry.QcqsLocalization.exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact
    F V.2.isCompact f rfl (X.basicOpen_le f) _
    (res_basicOpen_smulGenHom_eq_zero hφ V hf g)

/-- On an affine open `V` with `I(V)` finitely generated, `φ` annihilates `I(V)^(n+N) g` for some
`N`. -/
public theorem exists_pow_smul_mem_smulKill [F.IsQuasicoherent]
    {φ : idealPowSmul I n G ⟶ F}
    (hφ : homRestrict I (disjoint_supportCompl_support I) φ = 0) (V : X.affineOpens)
    (hFG : (I.ideal V).FG) (g : Γ(G, V.1)) :
    ∃ N : ℕ, ∀ a ∈ (I.ideal V ^ (n + N) : Ideal Γ(X, V.1)), a • g ∈ smulKill φ V := by
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.IdealPowerSections.exists_comp_inclusion_eq_zero
      Γ(X, V.1) (I.ideal V) Γ(F, V.1) hFG n (smulGenHom φ V g)
      (fun f hf ↦ exists_pow_smul_smulGenHom_eq_zero hφ V hf g)
  exact ⟨N, fun a ha ↦ mem_smulKill_iff.mpr
    ⟨(toSmulSection I n G V g ⟨a, Ideal.pow_le_pow_right (Nat.le_add_right n N) ha⟩).2,
      LinearMap.congr_fun hN ⟨a, ha⟩⟩⟩

/-- On an affine open `V` of a locally Noetherian scheme, with `G` coherent, `φ` annihilates all of
`I(V)^(n+N) Γ(G, V)` for some `N`. -/
public theorem exists_idealPowSections_le_smulKill [AlgebraicGeometry.IsLocallyNoetherian X]
    [G.IsCoherent] [F.IsQuasicoherent] {φ : idealPowSmul I n G ⟶ F}
    (hφ : homRestrict I (disjoint_supportCompl_support I) φ = 0) (V : X.affineOpens) :
    ∃ N : ℕ, idealPowSections I (n + N) G V ≤ smulKill φ V := by
  classical
  obtain ⟨sgen, hsgen⟩ := (moduleFinite_sections G V).fg_top
  choose Nf hNf using fun g : Γ(G, V.1) ↦
    exists_pow_smul_mem_smulKill hφ V (idealSheafData_ideal_fg I V) g
  refine ⟨sgen.sup Nf, Submodule.smul_le.mpr fun a ha m hmtop ↦ ?_⟩
  clear hmtop
  have hm : m ∈ Submodule.span Γ(X, V.1) (sgen : Set Γ(G, V.1)) := hsgen ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem g hg =>
      exact hNf g a (Ideal.pow_le_pow_right (Nat.add_le_add_left (Finset.le_sup hg) n) ha)
  | zero => simp
  | add p q _ _ hp hq => rw [smul_add]; exact Submodule.add_mem _ hp hq
  | smul r p _ hp => rw [smul_comm]; exact Submodule.smul_mem _ _ hp

/-! ### Descent to a smaller affine open -/

/-- For `G` quasi-coherent, if `φ` annihilates the sections of `I^m G` over an affine open `W`, it
annihilates those over every smaller affine open `V`. -/
public theorem idealPowSections_le_smulKill_of_le [G.IsQuasicoherent]
    {φ : idealPowSmul I n G ⟶ F} {V W : X.affineOpens} (hVW : V.1 ≤ W.1) {m : ℕ}
    (h : idealPowSections I m G W ≤ smulKill φ W) :
    idealPowSections I m G V ≤ smulKill φ V := by
  rw [isCompatible_idealPowSections I m G W V hVW, Submodule.span_le]
  rintro y ⟨t, ht, rfl⟩
  obtain ⟨ht', hzero⟩ := mem_smulKill_iff.mp (h ht)
  refine mem_smulKill_iff.mpr
    ⟨(idealPowerMultiple I n G).toSubmodule.map (homOfLE hVW).op ht', ?_⟩
  have hres : (⟨G.presheaf.map (homOfLE hVW).op t,
        (idealPowerMultiple I n G).toSubmodule.map (homOfLE hVW).op ht'⟩ :
      Γ(idealPowSmul I n G, V.1))
      = (idealPowSmul I n G).presheaf.map (homOfLE hVW).op ⟨t, ht'⟩ := Subtype.ext rfl
  rw [hres, ← app_naturality φ hVW (⟨t, ht'⟩ : Γ(idealPowSmul I n G, W.1)), hzero, map_zero]

/-! ### Globalisation over a finite affine cover -/

/-- The inclusion `I^m G ⟶ Iⁿ G` does not change the value of a section. -/
public theorem val_idealPowSmulMap_app (I : X.IdealSheafData) (G : X.Modules) {n m : ℕ}
    (h : n ≤ m) (V : X.Opens) (t : Γ(idealPowSmul I m G, V)) :
    (((idealPowSmulMap I G h).app V t).1 : Γ(G, V)) = (t.1 : Γ(G, V)) :=
  val_subInclusion_app (idealPowerMultiple_antitone I G h) V t

/-- Given a cover by affine opens on each of which `φ` annihilates `I^(n+N) G`, the composite
`I^(n+N) G ⟶ Iⁿ G ⟶ F` vanishes on every section. -/
public theorem app_idealPowSmulMap_eq_zero [G.IsQuasicoherent]
    (φ : idealPowSmul I n G ⟶ F) {N : ℕ} {s : Set X.affineOpens}
    (hcov : (Set.univ : Set X) = ⋃ i ∈ s, ((i : X.affineOpens) : Set X))
    (hmem : ∀ W ∈ s, idealPowSections I (n + N) G W ≤ smulKill φ W)
    (V₀ : X.Opens) (t : Γ(idealPowSmul I (n + N) G, V₀)) :
    φ.app V₀ ((idealPowSmulMap I G (Nat.le_add_right n N)).app V₀ t) = 0 := by
  refine eq_zero_of_locally_zero _ fun x hx ↦ ?_
  obtain ⟨W, hWs, hxW⟩ : ∃ W ∈ s, x ∈ (W : X.affineOpens).1 := by
    simpa using (hcov ▸ Set.mem_univ x : x ∈ ⋃ i ∈ s, ((i : X.affineOpens) : Set X))
  obtain ⟨-, ⟨V', hV'aff, rfl⟩, hxV', hV'sub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₀ ⊓ (W : X.affineOpens).1 : X.Opens) : Set X) from ⟨hx, hxW⟩)
      (V₀ ⊓ (W : X.affineOpens).1).isOpen
  have hV'V₀ : V' ≤ V₀ := fun y hy ↦ (hV'sub hy).1
  refine ⟨V', hV'V₀, hxV', (app_naturality φ hV'V₀
    ((idealPowSmulMap I G (Nat.le_add_right n N)).app V₀ t)).trans
    (app_eq_zero_of_val_mem_smulKill ⟨V', hV'aff⟩ _
      (idealPowSections_le_smulKill_of_le (V := ⟨V', hV'aff⟩) (W := W)
        (fun y hy ↦ (hV'sub hy).2) (hmem W hWs) ?_))⟩
  rw [app_naturality (idealPowSmulMap I G (Nat.le_add_right n N)) hV'V₀ t,
    val_idealPowSmulMap_app, idealPowSections_def,
    ← idealPowerMultiple_obj_affineOpen I (n + N) G ⟨V', hV'aff⟩]
  exact ((idealPowSmul I (n + N) G).presheaf.map (homOfLE hV'V₀).op t).2

/-- For `X` Noetherian, `G` coherent and `F` quasi-coherent, a morphism `φ : Iⁿ G ⟶ F` whose
restriction to `U = X \ V(I)` vanishes already vanishes on `I^(n+N) G` for some `N`. -/
public theorem exists_comp_eq_zero_of_homRestrict_eq_zero [AlgebraicGeometry.IsNoetherian X]
    [G.IsCoherent] [F.IsQuasicoherent] {φ : idealPowSmul I n G ⟶ F}
    (hφ : homRestrict I (disjoint_supportCompl_support I) φ = 0) :
    ∃ N : ℕ, (idealPowSmulMap I G (Nat.le_add_right n N) ≫ φ :
      idealPowSmul I (n + N) G ⟶ F) = 0 := by
  classical
  have hGqc : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  obtain ⟨s, hsfin, hcov⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      (⟨isCompact_univ, isOpen_univ⟩ :
        IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X))
  choose Nf hNf using fun V : X.affineOpens ↦ exists_idealPowSections_le_smulKill hφ V
  refine ⟨hsfin.toFinset.sup Nf, ?_⟩
  ext V₀ t
  refine app_idealPowSmulMap_eq_zero φ hcov (fun W hW ↦ ?_) V₀ t
  exact le_trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right
    (Nat.add_le_add_left (Finset.le_sup (hsfin.mem_toFinset.mpr hW)) n))) (hNf W)

/-- **Injectivity of the first display of [Stacks, Tag 01YB].**  For a Noetherian scheme `X`, a
quasi-coherent sheaf of ideals `I` with complement `U = X \ V(I)`, a coherent `𝒪_X`-module `G`
and a quasi-coherent `𝒪_X`-module `F`, the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

is injective. -/
public theorem canonicalMapToHomRestrict_injective [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent] :
    Function.Injective (canonicalMapToHomRestrict I G F) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  refine (injective_iff_map_eq_zero
    (AddCommGrpCat.Hom.hom (canonicalMapToHomRestrict I G F))).mpr fun z hz ↦ ?_
  obtain ⟨m, φ, rfl⟩ := Limits.Concrete.colimit_exists_rep (idealPowSmulHomSystem I G F) z
  obtain ⟨N, hN⟩ := exists_comp_eq_zero_of_homRestrict_eq_zero
    (φ := φ) ((canonicalMapToHomRestrict_ι I G F m φ).symm.trans hz)
  calc Limits.colimit.ι (idealPowSmulHomSystem I G F) m φ
      = Limits.colimit.ι (idealPowSmulHomSystem I G F) (m + N)
          ((idealPowSmulHomSystem I G F).map (homOfLE (Nat.le_add_right m N)) φ) := by
        rw [← ConcreteCategory.comp_apply, Limits.colimit.w]
    _ = Limits.colimit.ι (idealPowSmulHomSystem I G F) (m + N) 0 :=
        congrArg (ConcreteCategory.hom
          (Limits.colimit.ι (idealPowSmulHomSystem I G F) (m + N)))
          (show (idealPowSmulHomSystem I G F).map (homOfLE (Nat.le_add_right m N)) φ = 0
            from hN)
    _ = 0 := map_zero _

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

end
