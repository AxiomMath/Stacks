module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.SectionExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Shrinking the open in a direct image of the structure sheaf

Let `j' : U ⟶ V` be a nonempty open immersion into an integral Noetherian scheme, and suppose
`j'_*𝒪_U` is coherent. If `f` is a nonzero global function on `V` whose principal open `D(f)` is
contained in the image of `j'`, then multiplication by a power of `f` extends to an *injective*
morphism `j'_*𝒪_U ⟶ 𝒪_V`.

This is the inductive step of [Stacks, Tag 0BK1]: there `V` is the punctured spectrum of a
Noetherian local domain, `U` is the open whose coherence is being proved, and `f` is a nonzero
function vanishing on the complement of `U`. Pushing the injection forward to the ambient scheme
turns coherence of the direct image of the structure sheaf of the *punctured spectrum* — which is
proved in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumCoherentPushforward` — into
coherence of the direct image of the structure sheaf of `U`.

## Main definitions

* `Stacks.LocalCohomology.structureSheafToPushforward`: the canonical morphism
  `𝒪_V ⟶ j'_*𝒪_U`, which on sections over an open `T` is the restriction map `j'.app T`.

## Main results

* `Stacks.LocalCohomology.isIso_over_structureSheafToPushforward`: over an open contained in the
  image of `j'` that canonical morphism becomes an isomorphism, because `j'.app T` is an
  isomorphism for every open `T` inside the image.
* `Stacks.LocalCohomology.exists_mono_pushforward_structureSheaf_of_basicOpen_le`: the injection
  `j'_*𝒪_U ⟶ 𝒪_V` driven by [Stacks, Tag 01YB].
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le`: the inductive
  step itself — coherence of `(j' ≫ j'')_*𝒪_U` from coherence of `j'_*𝒪_U` on `V` and of
  `j''_*𝒪_V` on the ambient scheme.

## Implementation notes

The morphism `θ : (j'_*𝒪_U)|_{D(f)} ⟶ 𝒪_V|_{D(f)}` that [Stacks, Tag 01YB] consumes is the
*inverse* of the canonical `𝒪_V|_{D(f)} ⟶ (j'_*𝒪_U)|_{D(f)}`. Both are morphisms of sheaves of
modules on the slice site over `D(f)`, where the canonical one is invertible because each of its
components is `j'.app T` for an open `T ⊆ D(f) ⊆ im j'`.

Injectivity of the resulting `ψ : j'_*𝒪_U ⟶ 𝒪_V` is checked on the sections over an arbitrary
open `T`: restricting to `T ⊓ D(f)` turns `ψ` into `θ` applied to `fᵏ • ·`, and there `f` is a
unit, so a section killed by `ψ` restricts to zero on `T ⊓ D(f)`; since `V` is integral and `D(f)`
is a nonempty open, `T ⊓ D(f)` is nonempty whenever `T` is, and restriction between nonempty
opens of an integral scheme is injective.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.LocalCohomology

variable {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]

/-! ### The canonical morphism to the direct image, and its local invertibility -/

/-- **The canonical morphism `𝒪_V ⟶ j_*𝒪_U`.** On the sections over an open `T` of `V` it is the
restriction map `j.app T : Γ(V, T) ⟶ Γ(U, j ⁻¹ᵁ T)`. -/
def structureSheafToPushforward :
    SheafOfModules.unit.{u} V.ringCatSheaf ⟶
      (Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} U.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom

omit [IsOpenImmersion j] in
/-- The canonical morphism `𝒪_V ⟶ j_*𝒪_U` is `j.app T` on the sections over `T`. -/
theorem structureSheafToPushforward_val_app_apply (T : V.Opens) (r : Γ(V, T)) :
    (structureSheafToPushforward j).val.app (op T) r = (j.app T).hom r :=
  SheafOfModules.unitToPushforwardObjUnit_val_app_apply j.toRingCatSheafHom r

/-- **Over an open contained in the image of `j` the canonical morphism `𝒪_V ⟶ j_*𝒪_U` is an
isomorphism.** Each of its components on the slice site over `W` is `j.app T` for an open
`T ≤ W ≤ im j`, and those are isomorphisms by
`AlgebraicGeometry.Scheme.Hom.isIso_app`. -/
theorem isIso_over_structureSheafToPushforward {W : V.Opens} (hW : W ≤ j.opensRange) :
    IsIso ((structureSheafToPushforward j).over W) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun Wop => ?_
  have hle : Wop.unop.left ≤ W := leOfHom Wop.unop.hom
  have hring : IsIso (j.app Wop.unop.left) := j.isIso_app _ (hle.trans hW)
  change IsIso ((structureSheafToPushforward j).val.app (op Wop.unop.left))
  rw [ConcreteCategory.isIso_iff_bijective]
  have hcoe : (ConcreteCategory.hom
        ((structureSheafToPushforward j).val.app (op Wop.unop.left)) :
        ToType Γ(V, Wop.unop.left) → _) =
      fun r => (j.app Wop.unop.left).hom r :=
    funext (structureSheafToPushforward_val_app_apply j Wop.unop.left)
  rw [hcoe]
  exact ConcreteCategory.bijective_of_isIso (j.app Wop.unop.left)

/-! ### The injection driven by [Stacks, Tag 01YB] -/

open Stacks.AlgebraicGeometry.IdealPowerColimit in
/-- An isomorphism `G|_W ⟶ F|_W` is injective on the sections over every open inside `W`. -/
theorem injective_overApp_of_isIso {X : Scheme.{u}} {G F : X.Modules} {W : X.Opens}
    (θ : G.over W ⟶ F.over W) [IsIso θ] {T : X.Opens} (hT : T ≤ W) :
    Function.Injective (overApp θ hT) :=
  have := Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app θ (op (Over.mk (homOfLE hT)))
  (ConcreteCategory.bijective_of_isIso (θ.val.app (op (Over.mk (homOfLE hT))))).1

open Stacks.AlgebraicGeometry.PrincipalIdealExtension in
/-- The restriction of `f` to an open inside `D(f)` is a unit. -/
theorem isUnit_restrictTop_of_le_basicOpen (f : Γ(V, ⊤)) {T : V.Opens}
    (hT : T ≤ V.basicOpen f) : IsUnit (restrictTop f T) := by
  have h1 : V.presheaf.map (homOfLE hT).op
      (V.presheaf.map (homOfLE (V.basicOpen_le f)).op f) = restrictTop f T := by
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl
  exact h1 ▸ (V.toRingedSpace.isUnit_res_basicOpen f).map (V.presheaf.map (homOfLE hT).op).hom

open Stacks.AlgebraicGeometry.PrincipalIdealExtension
  Stacks.AlgebraicGeometry.IdealPowerColimit in
/-- **Multiplication by a power of `f` injects `j_*𝒪_U` into `𝒪_V`.** Let `j : U ⟶ V` be a
nonempty open immersion into an integral Noetherian scheme with `j_*𝒪_U` coherent, and let `f` be
a nonzero global function on `V` whose principal open is contained in the image of `j`. Then there
is a monomorphism `j_*𝒪_U ⟶ 𝒪_V`.

[Stacks, Tag 01YB] extends the identification `(j_*𝒪_U)|_{D(f)} ≅ 𝒪_V|_{D(f)}` of
`isIso_over_structureSheafToPushforward` to a morphism `ψ : j_*𝒪_U ⟶ 𝒪_V` which on the sections
over an open inside `D(f)` is that identification applied to `fᵏ • ·`. On an open `T` inside
`D(f)` the function `f` is a unit, so `ψ` is injective there; on an arbitrary `T` a section killed
by `ψ` restricts to zero on `T ⊓ D(f)`, which is a nonempty open of the integral `V` as soon as
`T` is nonempty, and restriction between nonempty opens of an integral scheme is injective
(`AlgebraicGeometry.map_injective_of_isIntegral`). -/
theorem exists_mono_pushforward_structureSheaf_of_basicOpen_le
    [AlgebraicGeometry.IsNoetherian V] [IsIntegral V] [Nonempty U]
    (hG : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent)
    (f : Γ(V, ⊤)) (hf0 : f ≠ 0) (hf : V.basicOpen f ≤ j.opensRange) :
    ∃ ψ : (Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} U.ringCatSheaf) ⟶
      SheafOfModules.unit.{u} V.ringCatSheaf, Mono ψ := by
  have hUint : IsIntegral U := isIntegral_of_isOpenImmersion j
  have hiso := isIso_over_structureSheafToPushforward j hf
  set G := (Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} U.ringCatSheaf)
  set θ : G.over (V.basicOpen f) ⟶ (SheafOfModules.unit.{u} V.ringCatSheaf).over
      (V.basicOpen f) := inv ((structureSheafToPushforward j).over (V.basicOpen f))
  obtain ⟨k, ψ, hψ⟩ := exists_hom_app_eq_overApp_smul_pow_basicOpen f G
    (SheafOfModules.unit.{u} V.ringCatSheaf) θ
  -- On an open inside `D(f)` the morphism `ψ` has trivial kernel.
  have key : ∀ (T : V.Opens) (hT : T ≤ V.basicOpen f) (y : Γ(G, T)),
      ψ.app T y = 0 → y = 0 := by
    intro T hT y hy
    have h0 : overApp θ hT (0 : Γ(G, T)) = 0 := map_zero _
    exact ((isUnit_restrictTop_of_le_basicOpen f hT).pow k).smul_eq_zero.mp
      (injective_overApp_of_isIso θ hT (((hψ hT y).symm.trans hy).trans h0.symm))
  refine ⟨ψ, Scheme.Modules.mono_of_app_eq_zero ψ fun T y hy => ?_⟩
  by_cases hTne : (T : Set V).Nonempty
  · -- shrink to `T ⊓ D(f)`, which is nonempty because `V` is irreducible
    have hbas : (V.basicOpen f : Set V).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hc
      exact hf0 (basicOpen_eq_bot_iff f |>.mp (Opens.ext (hc.trans Opens.coe_bot.symm)))
    obtain ⟨x, hxT, hxf⟩ := nonempty_preirreducible_inter T.isOpen (V.basicOpen f).isOpen
      hTne hbas
    obtain ⟨w, hw⟩ := hf hxf
    have hwmem : w ∈ j ⁻¹ᵁ (T ⊓ V.basicOpen f) := by
      change j.base w ∈ (T ⊓ V.basicOpen f : V.Opens)
      rw [hw]
      exact ⟨hxT, hxf⟩
    have : Nonempty (j ⁻¹ᵁ (T ⊓ V.basicOpen f)) := ⟨⟨w, hwmem⟩⟩
    have hres : G.val.map (homOfLE (inf_le_left : T ⊓ V.basicOpen f ≤ T)).op y = 0 := by
      refine key _ inf_le_right _ ?_
      change ψ.val.app (op (T ⊓ V.basicOpen f))
        (G.val.map (homOfLE (inf_le_left : T ⊓ V.basicOpen f ≤ T)).op y) = 0
      rw [PresheafOfModules.naturality_apply ψ.val
        (homOfLE (inf_le_left : T ⊓ V.basicOpen f ≤ T)).op y]
      change (SheafOfModules.unit.{u} V.ringCatSheaf).val.map
        (homOfLE (inf_le_left : T ⊓ V.basicOpen f ≤ T)).op (ψ.val.app (op T) y) = 0
      rw [hy, map_zero]
    have hinj : Function.Injective ((SheafOfModules.unit.{u} U.ringCatSheaf).val.map
        ((Opens.map j.base).map
          (homOfLE (inf_le_left : T ⊓ V.basicOpen f ≤ T))).op) :=
      map_injective_of_isIntegral U _
    exact hinj (hres.trans (map_zero _).symm)
  · rw [Opens.not_nonempty_iff_eq_bot] at hTne
    exact key T (hTne.le.trans bot_le) y hy

/-! ### The inductive step of [Stacks, Tag 0BK1] -/

/-- **The inductive step of [Stacks, Tag 0BK1].** Let `j' : U ⟶ V` and `j'' : V ⟶ X` be open
immersions with `U` nonempty, `V` integral and Noetherian, and `X` locally Noetherian. Assume
that `j'_*𝒪_U` is coherent on `V`, that `j''_*𝒪_V` is coherent on `X`, and that some nonzero
global function `f` on `V` has its principal open inside the image of `j'`. Then
`(j' ≫ j'')_*𝒪_U` is coherent on `X`.

In the source `X = Spec A` for a Noetherian local domain `A`, `V` is the punctured spectrum —
whose local rings have strictly smaller dimension, so that coherence of `j'_*𝒪_U` is the
induction hypothesis — and `f` is a nonzero function vanishing on the complement of `U`, which
makes `D(f)` a subset of `U`. Coherence of `j''_*𝒪_V` is the punctured-spectrum case of the tag,
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum`.

The injection of `exists_mono_pushforward_structureSheaf_of_basicOpen_le` is pushed forward along
`j''`, which preserves monomorphisms because it is a right adjoint, and [Stacks, Tag 01Y1] then
makes the quasi-coherent source coherent. -/
theorem isCoherent_pushforward_structureSheaf_of_basicOpen_le {X : Scheme.{u}}
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian V] [IsIntegral V] [Nonempty U]
    (j'' : V ⟶ X) [IsOpenImmersion j'']
    (hG : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent)
    (hV : ((Scheme.Modules.pushforward j'').obj
      (SheafOfModules.unit.{u} V.ringCatSheaf)).IsCoherent)
    (f : Γ(V, ⊤)) (hf0 : f ≠ 0) (hf : V.basicOpen f ≤ j.opensRange) :
    ((Scheme.Modules.pushforward (j ≫ j'')).obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent := by
  obtain ⟨ψ, hψ⟩ := exists_mono_pushforward_structureSheaf_of_basicOpen_le j hG f hf0 hf
  have : CategoryTheory.Limits.PreservesFiniteLimits (Scheme.Modules.pushforward j'') :=
    inferInstance
  have : (Scheme.Modules.pushforward j'').PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have : TopologicalSpace.NoetherianSpace V := IsNoetherian.noetherianSpace
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : QuasiCompact j'' := ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : QuasiSeparated j := inferInstance
  have : QuasiSeparated j'' := inferInstance
  have hq1 : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j (SheafOfModules.unit.{u} U.ringCatSheaf)
  have hq2 : ((Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward j'').obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j''
      ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit.{u} U.ringCatSheaf))
  have : Mono ((Scheme.Modules.pushforward j'').map ψ) :=
    CategoryTheory.Functor.map_mono (Scheme.Modules.pushforward j'') ψ
  have hcoh : ((Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward j'').obj
      (SheafOfModules.unit.{u} U.ringCatSheaf)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent hV
      ((Scheme.Modules.pushforward j'').map ψ)
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((Scheme.Modules.pushforwardComp j j'').app
      (SheafOfModules.unit.{u} U.ringCatSheaf)).symm

end Stacks.LocalCohomology

end

end
