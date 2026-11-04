module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent

/-!
# Pullback and ideal-power multiples

Let `f : X ⟶ Y` be a morphism of schemes, `𝒥` a quasi-coherent sheaf of ideals on `Y` and
`ℐ = f^{-1}𝒥 𝒪_X` its inverse image, which is `AlgebraicGeometry.Scheme.IdealSheafData.comap`.
For an `𝒪_Y`-module `M` the two subsheaves of `f^*M`

* the image of `f^*(𝒥 ⁿ M) ⟶ f^*M`, and
* `ℐ ⁿ (f^*M)`

agree. The statement proved here is the form in which that agreement is used: a morphism out of
`f^*M` kills the first exactly when it kills the second.

Both directions are affine-local, and `Stacks.IdealSheaf.ideal_comap_appLE` supplies the
affine-local description of `ℐ`: over an affine open `V` of `X` inside the preimage of an affine
open `U` of `Y`, the ideal of `ℐ` on `V` is the image of the ideal of `𝒥` on `U`. One direction
then needs only that the unit of `f^* ⊣ f_*` is `𝒪_Y`-linear; the other needs that the germs of
the unit images generate the stalks of `f^*M`, which is
`Stacks.Algebraization.smul_stalkMap_eq_zero`.

## Main results

* `Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff` — **termwise pullback is
  compatible with ideal-power multiples.**
* `Stacks.Algebraization.appLE_mem_comap_pow` — a pulled-back section of `𝒥 ⁿ` lies in `ℐ ⁿ`.
* `Stacks.Algebraization.submodule_ι_comp_eq_zero_iff` — a morphism kills a subsheaf exactly when
  the subsheaf is contained in its kernel.

## References

* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X Y : Scheme.{u}}

/-- The zero morphism out of the sheaf of modules underlying a subsheaf. Instance search does not
see through `AlgebraicGeometry.Scheme.Modules`, a semireducible definition, to find the zero
morphisms of `X.Modules` for a source presented as a bare `SheafOfModules X.ringCatSheaf`. -/
local instance zeroHomOfSheafOfModules
    (A : SheafOfModules.{u} X.ringCatSheaf) (B : X.Modules) : Zero (A ⟶ B) :=
  HasZeroMorphisms.zero (C := X.Modules) A B

/-! ### Kernels of morphisms of sheaves of modules -/

/-- A morphism of sheaves of modules kills a subsheaf exactly when that subsheaf is contained in
its kernel. -/
public theorem submodule_ι_comp_eq_zero_iff {M N : X.Modules} (P : M.Submodule) (h : M ⟶ N) :
    P.ι ≫ h = 0 ↔ P ≤ Scheme.Modules.kernelSubmodule h := by
  constructor
  · intro hh U x hx
    exact congrArg (fun k => k.val.app U ⟨x, hx⟩) hh
  · intro hh
    ext U x
    exact hh U x.property

/-- A subsheaf is zero exactly when its inclusion vanishes. -/
public theorem submodule_ι_eq_zero_iff {M : X.Modules} (P : M.Submodule) :
    P.ι = 0 ↔ P = ⊥ := by
  constructor
  · intro h
    refine le_antisymm (fun U z hz => ?_) bot_le
    have hz0 : z = 0 := by
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun φ : P.toSheafOfModules ⟶ M => φ.val.app U) h) (⟨z, hz⟩ : P.obj U)
      exact hh
    rw [hz0]
    exact (⊥ : M.Submodule).obj U |>.zero_mem
  · rintro rfl
    ext U z
    exact (bot_le : (⊥ : M.Submodule) ≤ Scheme.Modules.kernelSubmodule (𝟙 M)) U z.property

/-! ### Sections and germs -/

/-- A section of a sheaf of modules all of whose germs vanish is zero. -/
public theorem eq_zero_of_germ_eq_zero (N : X.Modules) (V : X.Opens) (s : Γ(N, V))
    (h : ∀ (x : X) (hx : x ∈ V), (N.presheaf.germ V x hx).hom s = 0) : s = 0 :=
  TopCat.Presheaf.section_ext (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X) V s 0
    (fun x hx => by rw [h x hx, map_zero])

/-- A section of a sheaf of modules vanishing on a neighbourhood of each of its points
vanishes. -/
public theorem eq_zero_of_locally_eq_zero (N : X.Modules) (V : X.Opens) (s : Γ(N, V))
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
      N.presheaf.map (homOfLE hW).op s = 0) : s = 0 := by
  refine eq_zero_of_germ_eq_zero N V s fun x hx => ?_
  obtain ⟨W, hW, hxW, hres⟩ := h x hx
  rw [← N.presheaf.germ_res_apply (homOfLE hW) x hxW s, hres, map_zero]

/-- Naturality of a morphism of sheaves of modules, read on sections. -/
public theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ≤ U)
    (s : Γ(M, U)) :
    N.presheaf.map (homOfLE i).op (φ.app U s) = φ.app V (M.presheaf.map (homOfLE i).op s) :=
  (PresheafOfModules.naturality_apply (f := φ.val) (homOfLE i).op s).symm

/-! ### The inverse-image ideal sheaf -/

/-- A pulled-back section of a power of an ideal sheaf lies in the corresponding power of the
inverse-image ideal sheaf. -/
public theorem appLE_mem_comap_pow (f : X ⟶ Y) (J : Y.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (hVU : (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens))
    {b : Γ(Y, (U : Y.Opens))} (hb : b ∈ J.ideal U ^ n) :
    (f.appLE U V hVU).hom b ∈ (J.comap f).ideal V ^ n := by
  rw [Stacks.IdealSheaf.ideal_comap_appLE J f U V hVU, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

/-! ### The pullback adjunction on sections -/

/-- Scalars act on the sections of a pushforward through the structure map of the morphism. -/
public theorem pushforward_smul (f : X ⟶ Y) (N : X.Modules) (W : Y.Opens)
    (b : Γ(Y, W)) (t : Γ(N, f ⁻¹ᵁ W)) :
    (b • (show Γ((Scheme.Modules.pushforward f).obj N, W) from t) :
        Γ((Scheme.Modules.pushforward f).obj N, W)) =
      (show Γ((Scheme.Modules.pushforward f).obj N, W) from (f.app W).hom b • t) := rfl

/-- On sections, the morphism corresponding to `g` under the pullback adjunction is `g` applied to
the image of the adjunction unit. -/
public theorem homEquiv_app (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (g : (Scheme.Modules.pullback f).obj M ⟶ N) (W : Y.Opens) (s : Γ(M, W)) :
    ((schemeModuleAdjunction f).homEquiv M N g).app W s =
      (show Γ((Scheme.Modules.pushforward f).obj N, W) from
        g.app (f ⁻¹ᵁ W) (((schemeModuleAdjunction f).unit.app M).app W s)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The pullback adjunction unit is linear over the structure map of `f`. -/
private theorem unit_app_smul (f : X ⟶ Y) (M : Y.Modules) (W : Y.Opens) (b : Γ(Y, W))
    (s : Γ(M, W)) :
    ((schemeModuleAdjunction f).unit.app M).app W (b • s) =
      (show Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ W) from
        (f.app W).hom b •
          (show Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ W) from
            ((schemeModuleAdjunction f).unit.app M).app W s)) :=
  (Scheme.Modules.Hom.app_smul ((schemeModuleAdjunction f).unit.app M) b s).trans
    (pushforward_smul f ((Scheme.Modules.pullback f).obj M) W b _)

/-- Restriction to a smaller affine open maps a power of the ideal into the corresponding power. -/
private theorem ideal_pow_map_mem (J : Y.IdealSheafData) (n : ℕ) {U V : Y.affineOpens}
    (h : V ≤ U) {b : Γ(Y, (U : Y.Opens))} (hb : b ∈ J.ideal U ^ n) :
    Y.presheaf.map (homOfLE h).op b ∈ J.ideal V ^ n := by
  rw [← Scheme.IdealSheafData.map_ideal J h, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

/-! ### The annihilation statement at a stalk -/

/-- The germ of a pulled-back section of `𝒥 ⁿ` annihilates the image under `g` of every germ
coming from the pullback adjunction unit, as soon as `𝒥 ⁿ` annihilates the morphism `M ⟶ f_*N`
corresponding to `g`. Shrinking to an affine open of `Y` inside the given one turns the statement
into the hypothesis. -/
public theorem germ_appLE_smul_unitGerm_eq_zero (f : X ⟶ Y) (J : Y.IdealSheafData) (n : ℕ)
    (M : Y.Modules) {N : X.Modules} (g : (Scheme.Modules.pullback f).obj M ⟶ N)
    (hP : ∀ U : Y.affineOpens,
      J.ideal U ^ n • (⊤ : Submodule Γ(Y, (U : Y.Opens)) Γ(M, (U : Y.Opens))) ≤
        (Scheme.Modules.kernelSubmodule
          ((schemeModuleAdjunction f).homEquiv M N g)).toSubmodule.obj (op (U : Y.Opens)))
    (x : X) (U1 : Y.affineOpens) (V1 : X.Opens) (hV1 : V1 ≤ f ⁻¹ᵁ (U1 : Y.Opens))
    (hxV1 : x ∈ V1) {b : Γ(Y, (U1 : Y.Opens))} (hb : b ∈ J.ideal U1 ^ n)
    (W : Y.Opens) (hw : f x ∈ W) (s : Γ(M, W)) :
    (X.presheaf.germ V1 x hxV1).hom ((f.appLE (U1 : Y.Opens) V1 hV1).hom b) •
        ((modulesStalkFunctor X x).map g).hom (unitGerm f x M W hw s) = 0 := by
  obtain ⟨_, ⟨W1, hW1, rfl⟩, hxW1, hW1sub⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ (W ⊓ (U1 : Y.Opens) : Y.Opens) from ⟨hw, hV1 hxV1⟩)
      (W ⊓ (U1 : Y.Opens) : Y.Opens).isOpen
  have hW1W : W1 ≤ W := fun z hz => (hW1sub hz).1
  have hW1U : (⟨W1, hW1⟩ : Y.affineOpens) ≤ U1 := fun z hz => (hW1sub hz).2
  set b1 : Γ(Y, W1) := Y.presheaf.map (homOfLE hW1U).op b
  set s1 : Γ(M, W1) := M.presheaf.map (homOfLE hW1W).op s
  have hb1 : b1 ∈ J.ideal ⟨W1, hW1⟩ ^ n := ideal_pow_map_mem J n hW1U hb
  set V2 : X.Opens := V1 ⊓ f ⁻¹ᵁ W1
  have hxV2 : x ∈ V2 := ⟨hxV1, hxW1⟩
  have hV2V1 : V2 ≤ V1 := inf_le_left
  have hV2W1 : V2 ≤ f ⁻¹ᵁ W1 := inf_le_right
  have hug : unitGerm f x M W1 hxW1 s1 = unitGerm f x M W hw s :=
    (congrArg (((Scheme.Modules.pullback f).obj M).presheaf.germ (f ⁻¹ᵁ W1) x hxW1)
      (app_naturality ((schemeModuleAdjunction f).unit.app M) hW1W s).symm).trans
      ((((Scheme.Modules.pullback f).obj M).presheaf.germ_res_apply
        (homOfLE (show f ⁻¹ᵁ W1 ≤ f ⁻¹ᵁ W from fun z hz => hW1W hz)) x hxW1 _))
  have h1 : (f.appLE W1 V2 hV2W1).hom b1 =
      (f.appLE (U1 : Y.Opens) V2 (hV2V1.trans hV1)).hom b :=
    congrArg (fun φ : Γ(Y, (U1 : Y.Opens)) ⟶ Γ(X, V2) => φ.hom b)
      (Scheme.Hom.map_appLE f hV2W1 (homOfLE hW1U).op)
  have h2 : X.presheaf.map (homOfLE hV2V1).op ((f.appLE (U1 : Y.Opens) V1 hV1).hom b) =
      (f.appLE (U1 : Y.Opens) V2 (hV2V1.trans hV1)).hom b :=
    congrArg (fun φ : Γ(Y, (U1 : Y.Opens)) ⟶ Γ(X, V2) => φ.hom b)
      (Scheme.Hom.appLE_map f hV1 (homOfLE hV2V1).op)
  have hgerm_b : (X.presheaf.germ V1 x hxV1).hom ((f.appLE (U1 : Y.Opens) V1 hV1).hom b) =
      (X.presheaf.germ V2 x hxV2).hom ((f.appLE W1 V2 hV2W1).hom b1) := by
    rw [h1, ← h2]
    exact (X.presheaf.germ_res_apply (homOfLE hV2V1) x hxV2 _).symm
  set t : Γ(N, f ⁻¹ᵁ W1) :=
    g.app (f ⁻¹ᵁ W1) (((schemeModuleAdjunction f).unit.app M).app W1 s1)
  have ht : (f.app W1).hom b1 • t = 0 := by
    have h0 := hP ⟨W1, hW1⟩ (Submodule.smul_mem_smul hb1 (Submodule.mem_top (x := s1)))
    have h3 : ((schemeModuleAdjunction f).homEquiv M N g).app W1 (b1 • s1) = 0 := h0
    refine Eq.trans ?_ h3
    rw [homEquiv_app f M N g W1 (b1 • s1), unit_app_smul, Scheme.Modules.Hom.app_smul]
  have h5 : ((modulesStalkFunctor X x).map g).hom (unitGerm f x M W1 hxW1 s1) =
      (N.presheaf.germ (f ⁻¹ᵁ W1) x hxW1).hom t :=
    modulesStalkFunctor_map_germ g x (f ⁻¹ᵁ W1) hxW1 _
  have h4 : (f.appLE W1 V2 hV2W1).hom b1 • N.presheaf.map (homOfLE hV2W1).op t =
      N.presheaf.map (homOfLE hV2W1).op ((f.app W1).hom b1 • t) :=
    (Scheme.Modules.map_smul N (homOfLE hV2W1) _ t).symm
  rw [hgerm_b, ← hug, h5, ← N.presheaf.germ_res_apply (homOfLE hV2W1) x hxV2 t]
  refine Eq.trans (germ_smul (M := N) x V2 hxV2 _ _).symm ?_
  rw [h4, ht, map_zero, map_zero]
  rfl

/-! ### Pullback and ideal-power multiples -/

/-- **Termwise pullback is compatible with ideal-power multiples.** A morphism out of `f^*M` kills
the image of `f^*(𝒥 ⁿ M)` exactly when it kills `ℐ ⁿ (f^*M)` for `ℐ = f^{-1}𝒥 𝒪_X`; equivalently,
those two subobjects of `f^*M` agree.

Both directions are affine-local. One of them only needs that the adjunction unit is
`𝒪_Y`-linear; the other needs that the stalks of `f^*M` are generated by the germs of the unit,
which is the stalk formula of Tag 0098. -/
public theorem pullback_idealPowerMultiple_comp_eq_zero_iff (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) (M : Y.Modules) {N : X.Modules}
    (g : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.pullback f).map (idealPowerMultiple J n M).ι ≫ g = 0 ↔
      (idealPowerMultiple (J.comap f) n ((Scheme.Modules.pullback f).obj M)).ι ≫ g = 0 := by
  set adj := schemeModuleAdjunction f
  have hzero : ∀ V : Y.Modules, adj.homEquiv V N 0 = 0 := fun V => by
    simp [Adjunction.homEquiv_unit]
  have hL : ((Scheme.Modules.pullback f).map (idealPowerMultiple J n M).ι ≫ g = 0) ↔
      ((idealPowerMultiple J n M).ι ≫ adj.homEquiv M N g = 0) :=
    ⟨fun hh => (adj.homEquiv_naturality_left _ g).symm.trans
        ((congrArg (adj.homEquiv _ N) hh).trans (hzero _)),
      fun hh => (adj.homEquiv _ _).injective
        (((adj.homEquiv_naturality_left _ g).trans hh).trans (hzero _).symm)⟩
  rw [hL, submodule_ι_comp_eq_zero_iff, submodule_ι_comp_eq_zero_iff,
    idealPowerMultiple_le_iff, idealPowerMultiple_le_iff]
  constructor
  · intro hP V
    refine Submodule.smul_le.mpr fun a ha w _ => ?_
    show g.app (V : X.Opens) (a • w) = 0
    refine eq_zero_of_germ_eq_zero N (V : X.Opens) _ fun x hxV => ?_
    refine (modulesStalkFunctor_map_germ g x (V : X.Opens) hxV (a • w)).symm.trans ?_
    refine (congrArg (fun y => ((modulesStalkFunctor X x).map g).hom y)
      (germ_smul x (V : X.Opens) hxV a w)).trans ?_
    refine (map_smul ((modulesStalkFunctor X x).map g).hom
      ((X.presheaf.germ (V : X.Opens) x hxV).hom a) _).trans ?_
    set Ann : Ideal ↑(X.presheaf.stalk x) :=
      { carrier := {ρ | ∀ (W : Y.Opens) (hw : f x ∈ W) (s : Γ(M, W)),
          ρ • ((modulesStalkFunctor X x).map g).hom (unitGerm f x M W hw s) = 0}
        add_mem' := fun {p q} hp hq W hw s => by
          rw [add_smul, hp W hw s, hq W hw s, add_zero]
        zero_mem' := fun W hw s => zero_smul _ _
        smul_mem' := fun c p hp W hw s => by
          rw [smul_eq_mul, mul_smul, hp W hw s, smul_zero] }
    suffices hmem : (X.presheaf.germ (V : X.Opens) x hxV).hom a ∈ Ann from
      smul_stalkMap_eq_zero f x M g _ hmem _
    obtain ⟨_, ⟨U0, hU0, rfl⟩, hxU0, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V0, hV0, rfl⟩, hxV0, hV0sub⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((V : X.Opens) ⊓ f ⁻¹ᵁ U0 : X.Opens) from ⟨hxV, hxU0⟩)
        ((V : X.Opens) ⊓ f ⁻¹ᵁ U0 : X.Opens).isOpen
    have hV0V : (⟨V0, hV0⟩ : X.affineOpens) ≤ V := fun z hz => (hV0sub hz).1
    have hV0U : V0 ≤ f ⁻¹ᵁ U0 := fun z hz => (hV0sub hz).2
    have hcomap : Ideal.map (f.appLE U0 V0 hV0U).hom (J.ideal ⟨U0, hU0⟩ ^ n) ≤
        Ann.comap (X.presheaf.germ V0 x hxV0).hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb W hw s
      exact germ_appLE_smul_unitGerm_eq_zero f J n M g hP x ⟨U0, hU0⟩ V0 hV0U hxV0 hb W hw s
    have hres : X.presheaf.map (homOfLE hV0V).op a ∈
        Ideal.map (f.appLE U0 V0 hV0U).hom (J.ideal ⟨U0, hU0⟩ ^ n) := by
      rw [Ideal.map_pow, ← Stacks.IdealSheaf.ideal_comap_appLE J f ⟨U0, hU0⟩ ⟨V0, hV0⟩ hV0U]
      exact ideal_pow_map_mem (J.comap f) n hV0V ha
    rw [← X.presheaf.germ_res_apply (homOfLE hV0V) x hxV0 a]
    exact hcomap hres
  · intro hQ U
    refine Submodule.smul_le.mpr fun b hb s _ => ?_
    show (adj.homEquiv M N g).app (U : Y.Opens) (b • s) = 0
    refine (homEquiv_app f M N g (U : Y.Opens) (b • s)).trans ?_
    refine (congrArg (fun y => g.app (f ⁻¹ᵁ (U : Y.Opens)) y)
      (unit_app_smul f M (U : Y.Opens) b s)).trans ?_
    refine (Scheme.Modules.Hom.app_smul g ((f.app (U : Y.Opens)).hom b) _).trans ?_
    refine eq_zero_of_locally_eq_zero N (f ⁻¹ᵁ (U : Y.Opens)) _ fun x hx => ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ (U : Y.Opens)).isOpen
    refine ⟨V, hVU, hxV, ?_⟩
    refine (Scheme.Modules.map_smul N (homOfLE hVU) _ _).trans ?_
    refine (congrArg (fun y => (f.appLE (U : Y.Opens) V hVU).hom b • y)
      (app_naturality g hVU _)).trans ?_
    refine (Scheme.Modules.Hom.app_smul g ((f.appLE (U : Y.Opens) V hVU).hom b) _).symm.trans ?_
    exact hQ ⟨V, hV⟩ (Submodule.smul_mem_smul
      (appLE_mem_comap_pow f J n U ⟨V, hV⟩ hVU hb) Submodule.mem_top)

end Stacks.Algebraization

end
