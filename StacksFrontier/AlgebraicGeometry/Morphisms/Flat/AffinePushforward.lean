module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria

/-!
# Flatness over a base is unchanged by an affine direct image

Let `f : X ⟶ Y` be an affine morphism of schemes and let `g : Y ⟶ S`. A quasi-coherent
`𝒪_X`-module `F` is flat over `S` if and only if its direct image `f_* F` is flat over `S`.

Both sides are checked on sections over compatible affine opens (Tag 01U4), and the sections of
`f_* F` over an open `W` of `Y` are by construction the sections of `F` over `f ⁻¹ᵁ W`, with
scalars restricted along `f`. Restricting those scalars further along `g` is restricting them
along `f ≫ g`, so the two flatness conditions are the same condition on the same module. That
`f` is affine enters twice: it makes `f ⁻¹ᵁ W` affine for `W` affine, so the affine-open criterion
for `f ≫ g` is reachable from the one for `g`, and it makes `f_* F` quasi-coherent.

## Main results

* `AlgebraicGeometry.isFlatOver_pushforward_iff` is the equivalence.

## Implementation notes

The structure morphism of `X` is the composite `f ≫ g`, and flatness over the base is the
stalkwise predicate `AlgebraicGeometry.IsFlatOver` of Tag 08KT.

## References

* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The two `Γ(S, V)`-module structures on the sections of `f_* F` over `W` — restriction of
scalars along `g` of the canonical `Γ(Y, W)`-structure, and restriction of scalars along `f ≫ g`
of the `Γ(X, f ⁻¹ᵁ W)`-structure on the sections of `F` — coincide, since the composite of the
two restriction maps is the restriction map of the composite. -/
private theorem module_compHom_appLE_pushforward {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (F : X.Modules) (W : Y.Opens) (V : S.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    Module.compHom Γ((Scheme.Modules.pushforward f).obj F, W) (g.appLE V W hWV).hom =
      Module.compHom Γ(F, f ⁻¹ᵁ W) ((f ≫ g).appLE V (f ⁻¹ᵁ W) fun _ hx => hWV hx).hom := by
  refine Module.ext' _ _ fun a m => ?_
  change (f.app W ((g.appLE V W hWV).hom a)) • (show Γ(F, f ⁻¹ᵁ W) from m) = _
  rw [← Scheme.Hom.appLE_eq_app, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- Flatness over `S` of the sections of `F` on `f ⁻¹ᵁ W` is flatness over `S` of the sections of
`f_* F` on `W`. -/
private theorem flat_pushforward_sections_iff {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (F : X.Modules) (W : Y.Opens) (V : S.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    @Module.Flat Γ(S, V) Γ((Scheme.Modules.pushforward f).obj F, W) _ _
        (Module.compHom _ (g.appLE V W hWV).hom) ↔
      @Module.Flat Γ(S, V) Γ(F, f ⁻¹ᵁ W) _ _
        (Module.compHom _ ((f ≫ g).appLE V (f ⁻¹ᵁ W) fun _ hx => hWV hx).hom) :=
  Iff.of_eq (congrArg (fun m : Module Γ(S, V) Γ(F, f ⁻¹ᵁ W) => @Module.Flat _ _ _ _ m)
    (module_compHom_appLE_pushforward f g F W V hWV))

/-- **Stacks Project, Tag 0FLM.** A quasi-coherent module on the source of an affine morphism is
flat over a base scheme if and only if its direct image is. -/
@[stacks 0FLM]
public theorem isFlatOver_pushforward_iff {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver (f ≫ g).toLRSHom.toShHom F ↔
      IsFlatOver g.toLRSHom.toShHom ((Scheme.Modules.pushforward f).obj F) := by
  refine ⟨fun hflat => ?_, fun hflat => ?_⟩
  · have hcrit := ((isFlatOver_tfae (f ≫ g) F).out 1 2).mp hflat
    refine ((isFlatOver_tfae g ((Scheme.Modules.pushforward f).obj F)).out 1 2).mpr ?_
    intro W hW V hV hWV
    exact (flat_pushforward_sections_iff f g F W V hWV).2
      (hcrit (f ⁻¹ᵁ W) (hW.preimage f) V hV fun _ hx => hWV hx)
  · have hcrit := ((isFlatOver_tfae g ((Scheme.Modules.pushforward f).obj F)).out 1 4).mp hflat
    refine ((isFlatOver_tfae (f ≫ g) F).out 1 4).mpr ?_
    obtain ⟨J, V, hVcover, hVaff, hcrit⟩ := hcrit
    refine ⟨J, V, hVcover, hVaff, fun j => ?_⟩
    obtain ⟨I, W, hWcover, hWaff, hWflat⟩ := hcrit j
    refine ⟨I, fun i => f ⁻¹ᵁ W i, ?_, fun i => (hWaff i).preimage f, fun i => ?_⟩
    · calc (⨆ i, f ⁻¹ᵁ W i) = f ⁻¹ᵁ (⨆ i, W i) := by ext x; simp
        _ = f ⁻¹ᵁ (g ⁻¹ᵁ V j) := congrArg (fun Z : Y.Opens => f ⁻¹ᵁ Z) hWcover
        _ = (f ≫ g) ⁻¹ᵁ V j := rfl
    · have hWV : W i ≤ g ⁻¹ᵁ V j := (le_iSup W i).trans hWcover.le
      exact (flat_pushforward_sections_iff f g F (W i) (V j) hWV).1
        (hWflat i)

end AlgebraicGeometry

end
