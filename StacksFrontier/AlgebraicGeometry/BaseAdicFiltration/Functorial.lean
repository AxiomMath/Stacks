module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.FiltrationSequence
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.SheafPushforward.Basic

/-!
# Functoriality of the base-adic filtration along a morphism over the base

Let `A` be a commutative ring, `I ⊆ A` an ideal, and let `g : U ⟶ V` be a morphism of schemes
over `Spec A`, that is `g ≫ p_V = p_U` for `p_V : V ⟶ Spec A` and `p_U : U ⟶ Spec A`.  This file
records that the `I`-adic apparatus of `StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/` is
functorial along `g` in the direction the direct image goes: a morphism `φ : ℱ_V ⟶ g_* ℱ_U` of
`𝒪_V`-modules induces compatible maps

```
ℱ_V / Iⁿ ℱ_V  ⟶  g_* (ℱ_U / Iⁿ ℱ_U)
```

for every `n`.  This is what lets the filtration argument of [Stacks, Tag 0E3X] compare the
filtration of `𝒪_V` with the direct image of the filtration of `𝒪_U`.

## What has to be proved, and what it rests on

**The ideal sheaf is functorial on the nose.**  `Stacks.BaseAdicFiltration.baseIdeal` is by
definition the inverse image along `p` of an ideal sheaf on `Spec A`, so
`Stacks.BaseAdicFiltration.baseIdeal_comap` is `Scheme.IdealSheafData.comap_comp` and nothing
else.

**The ideal multiple of a direct image.**  `Iⁿ(g_*𝒩) ⊆ g_*(Iⁿ𝒩)`.  Only this inclusion is
proved, and only this one is available for an arbitrary `g`: the reverse inclusion is
[Stacks, Tag 01YP], proved as
`Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf.idealPowSmul_pushforward_eq`, which holds for
exponent `1` and an **affine** morphism — a hypothesis a family deforming a morphism of schemes
has no reason to satisfy.  The inclusion proved here needs neither.  It says that a section of
`𝒪_V` coming from `Iⁿ` acts on the sections of `g_*𝒩` over `W`, which are the sections of `𝒩`
over `g ⁻¹ᵁ W`, as the section of `𝒪_U` coming from the same element of `Iⁿ`
(`Stacks.AlgebraicGeometry.SectionsColimit.pushforward_app_smul` for the action, and
`g ≫ p_V = p_U` for the element), and that such a section carries all of `𝒩` into `Iⁿ𝒩`.  That
last step is `Stacks.Algebraization.top_le_comap_sectionSmul`, and the reason it is the right
input is that it is a statement about *subsheaves*, hence about sections over every open: it
applies over `g ⁻¹ᵁ W` even though that open is not affine, which is what makes the argument go
through for an arbitrary `g`.

**The comparison maps come from `cokernel.desc`.**  `ℱ_V / Iⁿ ℱ_V` is a cokernel, so a map out of
it is a map out of `ℱ_V` killing `Iⁿ ℱ_V`; the map is `φ` followed by the direct image of the
projection, and what kills `Iⁿ ℱ_V` is that `Iⁿ` annihilates `g_*(ℱ_U/Iⁿℱ_U)`, which is the
inclusion above.

## Main definitions

* `Stacks.BaseAdicFiltration.adicQuotientComparison` — the map
  `ℱ_V/Iⁿℱ_V ⟶ g_*(ℱ_U/Iⁿℱ_U)` induced by `φ : ℱ_V ⟶ g_* ℱ_U`.

## Main results

* `Stacks.BaseAdicFiltration.baseIdeal_comap` — `(I 𝒪_V).comap g = I 𝒪_U`.
* `Stacks.BaseAdicFiltration.idealPowerMultiple_le_pushforwardSubmodule` and
  `idealPowerMultiple_pushforward_eq_bot` — the inclusion `Iⁿ(g_*𝒩) ⊆ g_*(Iⁿ𝒩)` and the
  vanishing it gives.
* `Stacks.BaseAdicFiltration.adicProj_comp_adicQuotientComparison` — the defining property of
  the comparison map.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf
open Stacks.AlgebraicGeometry.SectionsColimit
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-! The scalar action on `Γ(M, U)` is declared over `X.ringCatSheaf.obj.obj U` and instance search
does not cross the `TopCat.Sheaf` definition to recognize that as `Γ(X, U)`.  The bridges are the
`local instance`s of `Completion.IdealPowerQuasicoherent`, re-enabled here rather than restated,
as `FormalGeometry.AdicInverseSystem.IdealPowers` does; they are enabled at file scope because
the statements needing them are in `Stacks.BaseAdicFiltration`. -/

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsModuleRingCatSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ Stacks.Algebraization.monoSubmoduleι

namespace Stacks.Algebraization

/-- **If `ℐⁿ 𝒩 = 0` then every morphism `ℳ ⟶ 𝒩` kills `ℐⁿ ℳ`.**  A morphism carries `ℐⁿ ℳ` into
`ℐⁿ 𝒩` (`Stacks.Algebraization.idealPowerMultiple_le_sheafSubmoduleComap`) and that subsheaf is
zero, so the composite factors through the zero subsheaf
(`Stacks.Algebraization.comp_sheafBot_ι_eq_zero`).

This is the hypothesis `cokernel.desc` asks for when a map out of `ℳ` is to be descended to
`ℳ / ℐⁿ ℳ`.  The variant whose hypothesis is affine-local rather than the vanishing of the
subsheaf is `Stacks.Examples.NonAdicLimit.ι_comp_eq_zero_of_affine`. -/
public theorem idealPowerMultiple_ι_comp_eq_zero_of_eq_bot {X : Scheme.{u}}
    (J : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (ψ : M ⟶ N)
    (hbot : idealPowerMultiple J n N = ⊥) :
    ((idealPowerMultiple J n M).ι :
        ((idealPowerMultiple J n M).toSheafOfModules : X.Modules) ⟶ M) ≫ ψ =
      (0 : ((idealPowerMultiple J n M).toSheafOfModules : X.Modules) ⟶ _) := by
  have hle : idealPowerMultiple J n M ≤
      AlgebraicGeometry.sheafSubmoduleComap ψ (⊥ : N.Submodule) :=
    idealPowerMultiple_le_sheafSubmoduleComap J n ψ _ (le_of_eq hbot)
  refine Eq.trans (submoduleMapOfComap_comp_ι ψ _ _ hle).symm ?_
  exact comp_sheafBot_ι_eq_zero (submoduleMapOfComap ψ _ _ hle)

end Stacks.Algebraization

namespace Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf

/-- The direct image of the zero subsheaf is the zero subsheaf: its sections over `W` are the
sections of the zero subsheaf over `g ⁻¹ᵁ W`, and those vanish. -/
public theorem pushforwardSubmodule_bot {U V : Scheme.{u}} (g : U ⟶ V) (M : U.Modules) :
    pushforwardSubmodule g (⊥ : M.Submodule) =
      (⊥ : ((Scheme.Modules.pushforward g).obj M).Submodule) := by
  refine le_antisymm (SheafOfModules.Submodule.le_iff.mpr fun W x hx => ?_) bot_le
  have hx' : (show M.val.obj (op (g ⁻¹ᵁ W.unop)) from x) ∈
      (⊥ : M.Submodule).toSubmodule.obj (op (g ⁻¹ᵁ W.unop)) := hx
  have h0 : (show M.val.obj (op (g ⁻¹ᵁ W.unop)) from x) = 0 :=
    (Submodule.mem_bot _).mp ((SheafOfModules.Submodule.bot_obj M (op (g ⁻¹ᵁ W.unop))).le hx')
  exact (SheafOfModules.Submodule.bot_obj ((Scheme.Modules.pushforward g).obj M) W).ge
    ((Submodule.mem_bot _).mpr h0)

end Stacks.AlgebraicGeometry.PushforwardIdealSubsheaf

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U V : Scheme.{u}}
  (pV : V ⟶ Spec (CommRingCat.of A)) {pU : U ⟶ Spec (CommRingCat.of A)} {g : U ⟶ V}
  (hg : g ≫ pV = pU)

/-! ### The ideal sheaf is functorial -/

include hg in
/-- **The ideal sheaf `I 𝒪` is functorial along a morphism over the base.** For `g : U ⟶ V` with
`g ≫ p_V = p_U`, the inverse image of `I 𝒪_V` is `I 𝒪_U`.

`Stacks.BaseAdicFiltration.baseIdeal` is by construction the inverse image along `p` of one fixed
ideal sheaf on `Spec A`, so this is `Scheme.IdealSheafData.comap_comp` with no computation. -/
theorem baseIdeal_comap (I : Ideal A) : (baseIdeal pV I).comap g = baseIdeal pU I := by
  subst hg
  exact (Scheme.IdealSheafData.comap_comp _ g pV).symm

include hg in
/-- **The global function determined by `a : A` is compatible with `g`**: the one on `U`
restricts, over `g ⁻¹ᵁ W`, to the image under `g` of the restriction to `W` of the one on `V`.

The ring-map half is `AlgebraicGeometry.Scheme.Hom.app_eq_appLE` together with
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, which is also how the standalone
`Stacks.AlgebraicGeometry.appLE_comp_app` is proved; it is used here through those two Mathlib
lemmas rather than through that wrapper, so as to add no second copy of it and not to import the
regular-immersion tree it lives in. -/
theorem app_map_baseScalarMap (W : V.Opens) (a : A) :
    (g.app W).hom ((V.presheaf.map (homOfLE (le_top (a := W))).op).hom (baseScalarMap pV a)) =
      (U.presheaf.map (homOfLE (le_top (a := g ⁻¹ᵁ W))).op).hom (baseScalarMap pU a) := by
  subst hg
  rw [map_baseScalarMap, map_baseScalarMap]
  have h : pV.appLE ⊤ W le_top ≫ g.app W = (g ≫ pV).appLE ⊤ (g ⁻¹ᵁ W) le_top := by
    refine Eq.trans (congrArg (fun ψ : Γ(V, W) ⟶ Γ(U, g ⁻¹ᵁ W) => pV.appLE ⊤ W le_top ≫ ψ)
      (g.app_eq_appLE (U := W))) ?_
    exact Scheme.Hom.appLE_comp_appLE g pV ⊤ W (g ⁻¹ᵁ W) le_top le_rfl
  exact congrArg (fun φ : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(U, g ⁻¹ᵁ W) =>
    φ.hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) h

/-! ### The ideal multiple of a direct image -/

include hg in
/-- **`Iⁿ (g_* 𝒩) ⊆ g_* (Iⁿ 𝒩)`.**  A section of `𝒪_V` over an affine open `W` coming from `Iⁿ`
acts on the sections of `g_* 𝒩` over `W` — that is, on the sections of `𝒩` over `g ⁻¹ᵁ W` —
through `g`, hence as the section of `𝒪_U` coming from the same element of `Iⁿ`; and that section
carries all of `𝒩` into `Iⁿ 𝒩`.

Only this inclusion holds in general; see the discussion at the head of this file. -/
theorem idealPowerMultiple_le_pushforwardSubmodule (I : Ideal A) (n : ℕ) (N : U.Modules) :
    idealPowerMultiple (baseIdeal pV I) n ((Scheme.Modules.pushforward g).obj N) ≤
      pushforwardSubmodule g (idealPowerMultiple (baseIdeal pU I) n N) := by
  refine (idealPowerMultiple_le_iff _ n _ _).2 fun W => ?_
  -- A global function on `U` coming from `Iⁿ` carries every section of `𝒩` over `g ⁻¹ᵁ W` into
  -- `Iⁿ𝒩`.  This is the step for which a statement about subsheaves is needed rather than one
  -- about sections over affine opens: `g ⁻¹ᵁ W` is not affine.
  have hsmulU : ∀ a ∈ I ^ n, ∀ t : Γ(N, g ⁻¹ᵁ W.1),
      (U.presheaf.map (homOfLE (le_top (a := g ⁻¹ᵁ W.1))).op).hom (baseScalarMap pU a) • t ∈
        (idealPowerMultiple (baseIdeal pU I) n N).toSubmodule.obj (op (g ⁻¹ᵁ W.1)) := by
    intro a ha t
    have hb : RestrictMemIdealPow (baseIdeal pU I) n (baseScalarMap pU a) := fun W' =>
      restrictMemIdealPow_baseScalarMap pU n ha W'
    exact SheafOfModules.Submodule.le_iff.mp
      (top_le_comap_sectionSmul (J := baseIdeal pU I) N (le_refl n) hb) (op (g ⁻¹ᵁ W.1))
      ((AlgebraicGeometry.sheafTop_obj (M := N) (op (g ⁻¹ᵁ W.1))).ge Submodule.mem_top)
  -- Read on `V`: the scalar action on a direct image is the one along `g`, and `g ⪼ p_V = p_U`.
  have hsmul : ∀ a ∈ I ^ n, ∀ s : Γ((Scheme.Modules.pushforward g).obj N, W.1),
      ((pV.appLE ⊤ W.1 le_top).hom ((Scheme.ΓSpecIso (.of A)).inv.hom a)) • s ∈
        (pushforwardSubmodule g
          (idealPowerMultiple (baseIdeal pU I) n N)).toSubmodule.obj (op W.1) := by
    intro a ha s
    have h := hsmulU a ha s
    rw [← app_map_baseScalarMap pV hg W.1 a, map_baseScalarMap] at h
    exact (mem_pushforwardSubmodule g _ W.1 _).mpr h
  -- The `n`-th power of the ideal of `I 𝒪_V` on `W` is the image of `Iⁿ`, hence generated by
  -- exactly those functions; the elements of `Γ(V, W)` that act into the target form an ideal.
  have hQ : ∀ r ∈ Ideal.map ((pV.appLE ⊤ W.1 le_top).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom) (I ^ n),
      ∀ s : Γ((Scheme.Modules.pushforward g).obj N, W.1), r • s ∈
        (pushforwardSubmodule g
          (idealPowerMultiple (baseIdeal pU I) n N)).toSubmodule.obj (op W.1) := by
    intro r hr
    exact (Ideal.map_le_iff_le_comap.2 (fun a ha => Ideal.mem_comap.mpr (hsmul a ha)) :
      Ideal.map ((pV.appLE ⊤ W.1 le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom) (I ^ n) ≤
        { carrier := {r | ∀ s : Γ((Scheme.Modules.pushforward g).obj N, W.1), r • s ∈
            (pushforwardSubmodule g
              (idealPowerMultiple (baseIdeal pU I) n N)).toSubmodule.obj (op W.1)}
          add_mem' := fun {x y} hx hy s => by
            rw [add_smul]; exact Submodule.add_mem _ (hx s) (hy s)
          zero_mem' := fun s => by rw [zero_smul]; exact Submodule.zero_mem _
          smul_mem' := fun c x hx s => by
            rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c (hx s) }) hr
  rw [baseIdeal_ideal, ← Ideal.map_pow]
  exact Submodule.smul_le.2 fun r hr s _ => hQ r hr s

include hg in
/-- **`Iⁿ` annihilates `g_* 𝒩` as soon as it annihilates `𝒩`.**  This is the exponent-`n`,
no-affineness statement the comparison maps below need; it is
`Stacks.BaseAdicFiltration.idealPowerMultiple_le_pushforwardSubmodule` followed by the direct
image of the zero subsheaf being zero. -/
theorem idealPowerMultiple_pushforward_eq_bot (I : Ideal A) (n : ℕ) {N : U.Modules}
    (hbot : idealPowerMultiple (baseIdeal pU I) n N = ⊥) :
    idealPowerMultiple (baseIdeal pV I) n ((Scheme.Modules.pushforward g).obj N) = ⊥ := by
  refine le_antisymm ?_ bot_le
  refine (idealPowerMultiple_le_pushforwardSubmodule pV hg I n N).trans ?_
  rw [hbot, pushforwardSubmodule_bot]

/-! ### The comparison maps -/

section Comparison

variable (I : Ideal A) (n : ℕ) {FV : V.Modules} {FU : U.Modules} [FU.IsQuasicoherent]
  (φ : FV ⟶ (Scheme.Modules.pushforward g).obj FU)

include hg in
/-- **The comparison map `ℱ_V/Iⁿℱ_V ⟶ g_*(ℱ_U/Iⁿℱ_U)`** induced by a morphism
`φ : ℱ_V ⟶ g_* ℱ_U`.

The source is a cokernel, so the map is `φ` followed by the direct image of the projection,
descended through it; what makes the descent possible is that `Iⁿ` annihilates
`g_*(ℱ_U/Iⁿℱ_U)` (`Stacks.BaseAdicFiltration.idealPowerMultiple_pushforward_eq_bot`). -/
def adicQuotientComparison :
    adicQuotient pV I n FV ⟶ (Scheme.Modules.pushforward g).obj (adicQuotient pU I n FU) :=
  cokernel.desc (C := V.Modules) (adicFiltration pV I n FV).ι
    (φ ≫ (Scheme.Modules.pushforward g).map (adicProj pU I n FU))
    (idealPowerMultiple_ι_comp_eq_zero_of_eq_bot (baseIdeal pV I) n _
      (idealPowerMultiple_pushforward_eq_bot pV hg I n
        (idealPowerMultiple_idealPowerQuotient_eq_bot (baseIdeal pU I) n FU)))

include hg in
/-- **The defining property of the comparison map**: it turns the projection on `V` into `φ`
followed by the direct image of the projection on `U`. -/
@[reassoc]
theorem adicProj_comp_adicQuotientComparison :
    adicProj pV I n FV ≫ adicQuotientComparison pV hg I n φ =
      φ ≫ (Scheme.Modules.pushforward g).map (adicProj pU I n FU) :=
  cokernel.π_desc _ _ _

end Comparison

end Stacks.BaseAdicFiltration

end
