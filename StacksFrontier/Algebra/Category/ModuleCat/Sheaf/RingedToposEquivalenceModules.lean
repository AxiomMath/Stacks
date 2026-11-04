module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp

/-!
# Sheaves of modules along an equivalence of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi whose direct image of
sheaves of sets is an equivalence and whose structure map `f♯ : 𝒪_D ⟶ f_*𝒪_C` is an
isomorphism. Then the direct image `f_*` and the pullback `f^*` of sheaves of modules are
equivalences of categories.

## Main results

In the namespace `AlgebraicGeometry.RingedToposHom`:

* `isEquivalence_pushforwardModules_of_isEquivalence_ringedToposEquivalenceModules`: `f_*`
  is an equivalence: it is fully faithful (`fullyFaithfulPushforwardModules`) and every module
  `N` is `f_*` of the direct image of `N` along the inverse of `f`.
* `isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules`: `f^*` is
  an equivalence, being left adjoint to `f_*` (Stacks 03D7).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]

/-- Along an equivalence of ringed topoi every sheaf of modules on the target is a direct
image: `N ≅ f_*(f⁻¹_* N)`, the direct image along the round trip `Y ⟶ X ⟶ Y` being the
identity. -/
instance essSurj_pushforwardModules_of_isEquivalence_ringedToposEquivalenceModules :
    (pushforwardModules f).EssSurj where
  mem_essImage N := ⟨(pushforwardModules (inverse f)).obj N,
    ⟨((pushforwardModulesCompIso (inverse f) f).app N).symm ≪≫
      ((pushforwardModulesIsoId (f.comp (inverse f)) (inverseImageCompPushforwardIsoId f)
        (forgetRing_map_comp_inverse_fSharp f)).app N).symm⟩⟩

/-- **The direct image of sheaves of modules along an equivalence of ringed topoi is an
equivalence.** -/
instance isEquivalence_pushforwardModules_of_isEquivalence_ringedToposEquivalenceModules :
    (pushforwardModules f).IsEquivalence :=
  have := f.fullyFaithfulPushforwardModules.full
  have := f.fullyFaithfulPushforwardModules.faithful
  { }

/-- **The pullback of sheaves of modules along an equivalence of ringed topoi is an
equivalence**, being left adjoint to the direct image (Stacks 03D7). -/
instance isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    f.toModulesHom.pullbackModules.IsEquivalence :=
  (pullbackAdjPushforwardModules f).isEquivalence_left_of_isEquivalence_right

end AlgebraicGeometry.RingedToposHom
