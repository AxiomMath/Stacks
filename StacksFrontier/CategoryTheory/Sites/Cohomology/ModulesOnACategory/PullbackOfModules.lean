module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of modules along a morphism of ringed topoi on chaotic sites

Let `C` and `C'` be categories viewed as sites with the chaotic topology, let `O : Cᵒᵖ ⥤ RingCat`
and `O' : C'ᵒᵖ ⥤ RingCat` be sheaves of rings on them, and let a functor `F : C' ⥤ C` together
with a map of sheaves of rings `φ : F⁻¹O ⟶ O'` be the datum of a morphism of ringed topoi
`g : (Sh(C'), O') → (Sh(C), O)`. The pullback `g^* : Mod(O) ⥤ Mod(O')` of modules is the
inverse image of presheaves, which on a chaotic site is precomposition with `F.op`, followed by
the objectwise extension of scalars along `φ`: the sections of `g^*M` over an object `U'` of `C'`
are `M(F U') ⊗_{O(F U')} O'(U')`.

Both factors are computed objectwise. The first is exact, since limits and colimits of presheaves
of modules are detected on sections; the second is right exact, being a left adjoint. So `g^*` is
additive and right exact.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.modulePullback`: the pullback functor
  `g^* : Mod(O) ⥤ Mod(O')`.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.modulePullback_comp_evaluation`: the
  sections of `g^*M` over `U'` are the extension of scalars of the sections of `M` over `F U'`
  along the structure map `O(F U') ⟶ O'(U')`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.modulePullback_map_objTmul`: the
  restriction maps of `g^*M`, computed on pure tensors.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.pushforward₀_preservesFiniteLimits`
  and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.pushforward₀_preservesFiniteColimits`:
  the inverse image of presheaves of modules is exact.
* `modulePullback_additive` and `modulePullback_preservesFiniteColimits`: the pullback of modules
  is additive and right exact. It is not left exact: already over a point, extension of scalars is
  not.

## References

* [Stacks Project, Tag 0GZ1](https://stacks.math.columbia.edu/tag/0GZ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r v u v' u' t

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')

/-! ### The inverse image of presheaves of modules -/

/-- **The inverse image of presheaves of modules is additive.** It leaves the sections unchanged,
reindexing them along `F.op`, and addition of morphisms is objectwise. -/
instance pushforward₀_additive : (PresheafOfModules.pushforward₀.{t} F O).Additive where
  map_add := by intros; rfl

/-- The sections of the inverse image over `U'` are the sections over `F U'`. -/
lemma pushforward₀_comp_evaluation (U' : C'ᵒᵖ) :
    PresheafOfModules.pushforward₀.{max u v u' v' r} F O ⋙
        PresheafOfModules.evaluation (F.op ⋙ O) U' =
      PresheafOfModules.evaluation O (F.op.obj U') := rfl

/-- **The inverse image of presheaves of modules is left exact.** A cone of presheaves of modules
is limit as soon as it is limit on sections over every object, and on sections the inverse image
is the identity up to reindexing. -/
instance pushforward₀_preservesFiniteLimits :
    PreservesFiniteLimits (PresheafOfModules.pushforward₀.{t} F O) where
  preservesFiniteLimits _ _ _ :=
    ⟨fun {_} => ⟨fun _ {hc} => ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun U' =>
      isLimitOfPreserves (PresheafOfModules.evaluation O (F.op.obj U')) hc⟩⟩⟩

/-- **The inverse image of presheaves of modules is right exact**, by the colimit counterpart of
the argument for `pushforward₀_preservesFiniteLimits`. -/
@[sga "4 IV 13.6" "special case"]
instance pushforward₀_preservesFiniteColimits :
    PreservesFiniteColimits (PresheafOfModules.pushforward₀.{t} F O) where
  preservesFiniteColimits _ _ _ :=
    ⟨fun {_} => ⟨fun _ {hc} => ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ fun U' =>
      isColimitOfPreserves (PresheafOfModules.evaluation O (F.op.obj U')) hc⟩⟩⟩

/-! ### Extension of scalars along the structure map -/

/-- **Objectwise extension of scalars of presheaves of modules is right exact**, being a left
adjoint. It is not left exact: already over a point, extension of scalars is not. -/
instance extendScalars_preservesFiniteColimits :
    PreservesFiniteColimits
      (Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ) where

/-- **Objectwise extension of scalars of presheaves of modules is additive.** Being a left
adjoint it preserves the zero object and binary coproducts, hence binary biproducts. -/
instance extendScalars_additive :
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-! ### The pullback -/

/-- **The pullback of modules along a morphism of ringed topoi on chaotic sites.** For a functor
`F : C' ⥤ C` and a map of sheaves of rings `φ : F⁻¹O ⟶ O'`, this is the inverse image of
presheaves of modules followed by the objectwise extension of scalars along `φ`; its sections
over `U'` are `M(F U') ⊗_{O(F U')} O'(U')`. -/
@[sga "4 IV 13.2.2" "special case"]
noncomputable def modulePullback :
    PresheafOfModules.{max u v u' v' r} O ⥤ PresheafOfModules.{max u v u' v' r} O' :=
  PresheafOfModules.pushforward₀.{max u v u' v' r} F O ⋙
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ

/-- The sections of the pullback over `U'` are the extension of scalars along the structure map
of the sections over `F U'`. -/
theorem modulePullback_comp_evaluation (U' : C'ᵒᵖ) :
    modulePullback F O O' φ ⋙ PresheafOfModules.evaluation O' U' =
      PresheafOfModules.evaluation O (F.op.obj U') ⋙
        Stacks.NoncommChangeOfRings.extendScalars.{max u v u' v' r} (φ.app U').hom := rfl

/-- The restriction maps of the pullback, on pure tensors: the pure tensor `b ⊗ m` over `V'`
restricts along `a' : V' ⟶ U'` to the pure tensor of the restriction of `b` in `O'` with the
restriction of `m` along `F a'`. -/
lemma modulePullback_map_objTmul (M : PresheafOfModules.{max u v u' v' r} O) {V' U' : C'ᵒᵖ}
    (a' : V' ⟶ U') (b : O'.obj V') (m : M.obj (F.op.obj V')) :
    Stacks.NoncommChangeOfRings.ofRestrict.{max u v u' v' r, r, r} (O'.map a').hom
        (((modulePullback F O O' φ).obj M).map a')
        (Stacks.NoncommChangeOfRings.objTmul.{max u v u' v', r, r} (φ.app V').hom b m) =
      Stacks.NoncommChangeOfRings.objTmul.{max u v u' v', r, r} (φ.app U').hom
        ((O'.map a').hom b) (M.map (F.op.map a') m) := rfl

/-- **The pullback of modules is additive**, being a composite of additive functors. -/
instance modulePullback_additive : (modulePullback F O O' φ).Additive :=
  inferInstanceAs (PresheafOfModules.pushforward₀.{max u v u' v' r} F O ⋙
    Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ).Additive

/-- **The pullback of modules is right exact.** The inverse image of presheaves is exact and
extension of scalars is a left adjoint. It is not left exact: already over a point, extension of
scalars is not. -/
instance modulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (modulePullback F O O' φ) :=
  comp_preservesFiniteColimits (PresheafOfModules.pushforward₀.{max u v u' v' r} F O)
    (Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{max u v u' v'} φ)

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
