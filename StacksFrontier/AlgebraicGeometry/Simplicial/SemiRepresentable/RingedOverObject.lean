module

public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The ringed total site of a simplicial semi-representable object over an object

Let `(C, O_C)` be a ringed site, let `U` be an object of `C` and write `O_U = O_C|_{C/U}` for the
restricted structure sheaf, so that `(C/U, O_U)` is again a ringed site. A semi-representable
object over `U` is one of the slice site, `SR(C, U) = SR(C/U)`, and the constructions attached to
a simplicial semi-representable object of a ringed site apply verbatim to the ringed site
`(C/U, O_U)`. For a simplicial object `K` of `SR(C, U)` they give

1. the total ringed site `((C/K)_total, O)`, with `O = a⁻¹O_U`;
2. the augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C/U), O_U)`, a morphism of ringed topoi;
3. the degreewise augmentations `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/U), O_U)`;
4. a functor `a_! : Mod(O) ⥤ Mod(O_U)` left adjoint to the pullback `a^*` of sheaves of modules.

The other assertions made for a simplicial semi-representable object of a ringed site hold here
as well: `a` and every `a_n` are flat; `a_n^*` has an exact left adjoint `a_{n!}`; for a simplex
map `φ : [m] ⟶ [n]` the transition morphism `f_φ : (Sh(C/K_n), O_n) ⟶ (Sh(C/K_m), O_m)` is flat
and `f_φ^*` has an exact left adjoint `f_{φ!}`; and the morphism
`g_n : (Sh(C/K_n), O_n) ⟶ (Sh((C/K)_total), O)` is flat and `g_n^*` has an exact left adjoint
`g_{n!}`.

## Main definitions

* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedSiteOver`: the ringed site
  `((C/K)_total, O)` of a simplicial object of `SR(C, U)`.
* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedAugmentationOver`: the augmentation
  `a : (Sh((C/K)_total), O) ⟶ (Sh(C/U), O_U)`.
* `CategoryTheory.SemiRepresentable.Simplicial.degreewiseRingedAugmentationOver`: the degreewise
  augmentations `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/U), O_U)`.
* `CategoryTheory.SemiRepresentable.Simplicial.totalLowerShriekOver` and
  `.totalLowerShriekOverAdjunction`: the functor `a_! : Mod(O) ⥤ Mod(O_U)` and the adjunction
  `a_! ⊣ a^*`.
* `CategoryTheory.SemiRepresentable.Simplicial.degreewiseLowerShriekOverAdjunction`,
  `.transitionLowerShriekOverAdjunction` and `.componentLowerShriekOverAdjunction`: the
  adjunctions `a_{n!} ⊣ a_n^*`, `f_{φ!} ⊣ f_φ^*` and `g_{n!} ⊣ g_n^*`.

## Main results

* `…Simplicial.totalRingedAugmentation_isRightAdjoint_pullbackModules`:
  for any ringed site, the pullback of sheaves of modules along the total augmentation has a left
  adjoint; this is what produces `a_!`.
* `CategoryTheory.SemiRepresentable.Simplicial.totalRingedAugmentationOver_isFlat` and
  `.degreewiseRingedAugmentationOver_isFlat`: `a` and `a_n` are flat.
* `CategoryTheory.SemiRepresentable.Simplicial.ringedTransitionMorphismOver_isFlat` and
  `.componentRingedMorphismOver_isFlat`: `f_φ` and `g_n` are flat.
* `CategoryTheory.SemiRepresentable.Simplicial.exactFunctor_degreewiseLowerShriekOver`,
  `.exactFunctor_transitionLowerShriekOver` and `.exactFunctor_componentLowerShriekOver`: the
  functors `a_{n!}`, `f_{φ!}` and `g_{n!}` are exact.

## Implementation notes

Every construction is the one for a simplicial semi-representable object of a ringed site, taken
at the ringed site `AlgebraicGeometry.RingedSite.over X U`, whose underlying site is the slice
`Over U` with the topology `J.over U` and whose structure sheaf is the restriction `O.over U`. A
simplicial object of `SR(C, U)` is accordingly a simplicial object of formal coproducts of
objects of `Over U`, and the site `C/K_n` is the componentwise localization of the slice site at
`K_n`. This is the substitution of `C/U` for `C` by which the source obtains the remark. The
object the source calls `X` is `U` here, the name `X` being taken by the ringed site.

The morphisms of ringed topoi have their structure sheaves in a universe large enough for the
right adjoint of restriction along the localization functors, which forms products over the
fibres of the component index. Accordingly items (2) to (4) and the further results are stated
for `O_U` with its sections lifted into that universe,
`AlgebraicGeometry.RingedSite.liftedRingedSite`, which changes neither the site nor the sections
up to the universe lift; the ringed site of item (1) needs no lift.

The functor `a_!` of item (4) is the left adjoint of the pullback `a^*` of sheaves of modules
along the morphism of ringed topoi `a` itself. It exists because the structure map of `a` is an
isomorphism, `O` being `a⁻¹O_U`, and the inverse image of sheaves of modules along `a` is
restriction along the continuous functor `j_total` out of an essentially small site.

## References

* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D8C](https://stacks.math.columbia.edu/tag/0D8C)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentable

universe x u v w

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

namespace CategoryTheory.SemiRepresentable.Simplicial

/-! ### The module pullback along the total augmentation has a left adjoint -/

/-- The structure map of the total augmentation, in inverse-image form, is an isomorphism: it is
the identification of `a⁻¹O_C` with the structure sheaf `O` of the total ringed site. -/
instance isIso_totalRingedAugmentationAtLargeUniverse_fSharpInverseImage
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    IsIso (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K).fSharpInverseImage := by
  rw [totalRingedAugmentationAtLargeUniverse_fSharpInverseImage]
  exact (totalAugmentationInverseImageCommRingIso.{x, u, v, w} X K).isIso_hom

/-- The pullback `a^*` of sheaves of modules along the total augmentation
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` has a left adjoint: the structure map of `a` is an
isomorphism, and the inverse image of sheaves of modules along `a` is restriction along the
continuous functor `j_total` out of an essentially small site. -/
instance totalRingedAugmentationAtLargeUniverse_isRightAdjoint_pullbackModules
    (X : AlgebraicGeometry.RingedSite.{u, v, max x u v w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    Functor.IsRightAdjoint
      (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K).toModulesHom.pullbackModules :=
  (totalRingedAugmentationAtLargeUniverse.{x, u, v, w} X K).isRightAdjoint_pullbackModules
    (Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction.{max x u v w,
        v, max u v x, v, u}
      (totalLocalizationTopology K X.J) X.J (totalLocalizationFunctor K) _)

/-- The pullback `a^*` of sheaves of modules along the total augmentation of an arbitrary ringed
site has a left adjoint. -/
instance totalRingedAugmentation_isRightAdjoint_pullbackModules
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (K : SimplicialObject (FormalCoproduct.{x} X.C)) :
    (totalRingedAugmentation.{x, u, v, w} X K).toModulesHom.pullbackModules.IsRightAdjoint :=
  totalRingedAugmentationAtLargeUniverse_isRightAdjoint_pullbackModules.{x, u, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x, u, v, w} X) K

/-! ### The constructions over an object -/

variable (X : AlgebraicGeometry.RingedSite.{u, v, w}) (U : X.C)
  (K : SimplicialObject (FormalCoproduct.{x} (Over U)))

/-- For a ringed site `(C, O_C)`, an object `U` of `C` and a simplicial object `K` of
`SR(C, U) = SR(C/U)`, the total localization site `(C/K)_total` of `K` over the slice site `C/U`,
with the structure sheaf `O = a⁻¹O_U` pulled back from `O_U = O_C|_{C/U}`. -/
@[stacks 0D9X "item (1): the ringed site ((C/K)_total, O)"]
abbrev totalRingedSiteOver : AlgebraicGeometry.RingedSite :=
  totalRingedSite (X.over U) K

/-- The structure sheaf of the total ringed site over `U` is the restriction of
`O_U = O_C|_{C/U}` along the localization functor `j_total : (C/K)_total ⥤ C/U`. -/
theorem totalRingedSiteOver_O :
    (totalRingedSiteOver.{x, u, v, w} X U K).O =
      ((totalLocalizationFunctor K).sheafPushforwardContinuous CommRingCat.{w}
        (totalLocalizationTopology K (X.J.over U)) (X.J.over U)).obj (X.O.over U) :=
  rfl

/-- The augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C/U), O_U)` of the total ringed site of a
simplicial object `K` of `SR(C, U)`, as a morphism of ringed topoi. -/
@[stacks 0D9X "item (2): the morphism of ringed topoi a"]
def totalRingedAugmentationOver :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v x, v, w}
        (totalRingedSite (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K))
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v, v, max x w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U))) :=
  totalRingedAugmentation (X.over U) K

/-- The morphism of topoi underlying the augmentation over `U` is the localization augmentation
of `K` over the slice site `C/U`. -/
@[simp]
theorem totalRingedAugmentationOver_toToposHom :
    (totalRingedAugmentationOver.{x, u, v, w} X U K).toToposHom =
      localizationAugmentation.{x, v, max u v, w} K (X.J.over U) :=
  rfl

/-- The degreewise augmentations `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/U), O_U)` of a simplicial
object `K` of `SR(C, U)`, as morphisms of ringed topoi. -/
@[stacks 0D9X "item (3): the morphisms of ringed topoi a_n"]
def degreewiseRingedAugmentationOver (n : SimplexCategory) :
    AlgebraicGeometry.RingedToposHom
      (AlgebraicGeometry.RingedSite.localizationRingedTopos
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) (K.obj (op n)))
      (AlgebraicGeometry.RingedSite.ringedTopos.{max u v, v, max x w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U))) :=
  degreewiseRingedAugmentation.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- The pullback `a^*` of sheaves of modules along the augmentation over `U` has a left adjoint. -/
instance totalRingedAugmentationOver_isRightAdjoint_pullbackModules :
    (totalRingedAugmentationOver.{x, u, v, w} X U K).toModulesHom.pullbackModules.IsRightAdjoint :=
  totalRingedAugmentation_isRightAdjoint_pullbackModules.{x, max u v, v, w} (X.over U) K

/-- The functor `a_! : Mod(O) ⥤ Mod(O_U)`: the left adjoint of the pullback `a^*` of sheaves of
modules along the augmentation `a` of the total ringed site over `U`. -/
def totalLowerShriekOver :=
  (totalRingedAugmentationOver.{x, u, v, w} X U K).lowerShriekModules

/-- For a simplicial object `K` of `SR(C, U)`, the functor `a_! : Mod(O) ⥤ Mod(O_U)` is left
adjoint to the pullback `a^*` of sheaves of modules along the augmentation
`a : (Sh((C/K)_total), O) ⟶ (Sh(C/U), O_U)`. -/
@[stacks 0D9X "item (4): a_! is left adjoint to a^*"]
def totalLowerShriekOverAdjunction :
    totalLowerShriekOver.{x, u, v, w} X U K ⊣
      (totalRingedAugmentationOver.{x, u, v, w} X U K).toModulesHom.pullbackModules :=
  (totalRingedAugmentationOver.{x, u, v, w} X U K).lowerShriekAdjPullbackModules

/-! ### The results of Stacks 0D9W over an object -/

/-- The augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C/U), O_U)` of a simplicial object `K` of
`SR(C, U)` is flat. -/
@[stacks 0D9X "the results of 0D9W: a is flat"]
theorem totalRingedAugmentationOver_isFlat :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{v, max u v x,
        max x u v w, v, max u v, max x u v w}
      (totalRingedAugmentationOver.{x, u, v, w} X U K) :=
  totalRingedAugmentation_isFlat.{x, max u v, v, w} (X.over U) K

/-- Every degreewise augmentation `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/U), O_U)` of a simplicial
object `K` of `SR(C, U)` is flat. -/
@[stacks 0D9X "the results of 0D9W: a_n is flat"]
theorem degreewiseRingedAugmentationOver_isFlat (n : SimplexCategory) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v x, max u v x,
        max x u v w, v, max u v, max x u v w}
      (degreewiseRingedAugmentationOver.{x, u, v, w} X U K n) :=
  degreewiseRingedAugmentation_isFlat.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- For a simplicial object `K` of `SR(C, U)`, the inverse image `a_n^*` of sheaves of modules
along the degreewise augmentation `a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/U), O_U)` has the left adjoint
`a_{n!} : Mod(O_n) ⥤ Mod(O_U)`. -/
@[stacks 0D9X "the results of 0D9W: a_{n!} is left adjoint to a_n^*"]
def degreewiseLowerShriekOverAdjunction (n : SimplexCategory) :
    degreewiseLowerShriek.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n ⊣
      degreewiseInverseImageModules.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n :=
  degreewiseLowerShriekAdjunction.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- For a simplicial object `K` of `SR(C, U)`, the functor `a_{n!} : Mod(O_n) ⥤ Mod(O_U)` is
exact. -/
@[stacks 0D9X "the results of 0D9W: a_{n!} is exact"]
theorem exactFunctor_degreewiseLowerShriekOver (n : SimplexCategory) :
    exactFunctor _ _ (degreewiseLowerShriek.{x, max u v, v, w}
      (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n) :=
  exactFunctor_degreewiseLowerShriek.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- For a simplicial object `K` of `SR(C, U)` and a simplex map `φ : [m] ⟶ [n]`, the morphism of
ringed topoi `f_φ : (Sh(C/K_n), O_n) ⟶ (Sh(C/K_m), O_m)` is flat. -/
@[stacks 0D9X "the results of 0D9W: f_φ is flat"]
theorem ringedTransitionMorphismOver_isFlat {m n : SimplexCategory} (φ : m ⟶ n) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max u v x, max u v x,
        max x u v w, max u v x, max u v x, max x u v w}
      (ringedTransitionMorphism.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ).val :=
  ringedTransitionMorphism_isFlat.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ

/-- For a simplicial object `K` of `SR(C, U)` and a simplex map `φ : [m] ⟶ [n]`, the inverse image
`f_φ^*` of sheaves of modules has the left adjoint `f_{φ!} : Mod(O_n) ⥤ Mod(O_m)`. -/
@[stacks 0D9X "the results of 0D9W: f_{φ!} is left adjoint to f_φ^*"]
def transitionLowerShriekOverAdjunction {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionLowerShriek.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ ⊣
      transitionInverseImageModules.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ :=
  transitionLowerShriekAdjunction.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ

/-- For a simplicial object `K` of `SR(C, U)` and a simplex map `φ : [m] ⟶ [n]`, the functor
`f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` is exact. -/
@[stacks 0D9X "the results of 0D9W: f_{φ!} is exact"]
theorem exactFunctor_transitionLowerShriekOver {m n : SimplexCategory} (φ : m ⟶ n) :
    exactFunctor _ _ (transitionLowerShriek.{x, max u v, v, w}
      (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ) :=
  exactFunctor_transitionLowerShriek.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K φ

/-- For a simplicial object `K` of `SR(C, U)`, the morphism of ringed topoi
`g_n : (Sh(C/K_n), O_n) ⟶ (Sh((C/K)_total), O)` is flat. -/
@[stacks 0D9X "the results of 0D9W: g_n is flat"]
theorem componentRingedMorphismOver_isFlat (n : SimplexCategory) :
    Stacks.Sheaf.RingedToposFlat.RingedToposHom.IsFlat.{max x u v, max x u v,
        max x u v w, v, max u v x, max x u v w}
      (componentRingedMorphism.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n) :=
  componentRingedMorphism_isFlat.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- For a simplicial object `K` of `SR(C, U)`, the inverse image `g_n^*` of sheaves of modules
along `g_n` has the left adjoint `g_{n!} : Mod(O_n) ⥤ Mod(O)`. -/
@[stacks 0D9X "the results of 0D9W: g_{n!} is left adjoint to g_n^*"]
def componentLowerShriekOverAdjunction (n : SimplexCategory) :
    componentLowerShriek.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n ⊣
      componentInverseImageModules.{x, max u v, v, w}
        (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n :=
  componentLowerShriekAdjunction.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

/-- For a simplicial object `K` of `SR(C, U)`, the functor `g_{n!} : Mod(O_n) ⥤ Mod(O)` is
exact. -/
@[stacks 0D9X "the results of 0D9W: g_{n!} is exact"]
theorem exactFunctor_componentLowerShriekOver (n : SimplexCategory) :
    exactFunctor _ _ (componentLowerShriek.{x, max u v, v, w}
      (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n) :=
  exactFunctor_componentLowerShriek.{x, max u v, v, w}
    (AlgebraicGeometry.RingedSite.liftedRingedSite.{x} (X.over U)) K n

end CategoryTheory.SemiRepresentable.Simplicial
