module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.Torsor
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.ExistenceObstruction
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.MonoActionPresentation

/-!
# Extensions with a fixed first-order action on a ringed topos

Fix a first order thickening `i : (Sh(C), O') ⟶ (Sh(D), O)` of ringed topoi with square-zero
ideal `I`, and two modules `F` and `K` over the direct image `i_*O'` of the structure sheaf of
the source. An *extension* of `F` by `K` over the thickening is a short exact sequence of
`O`-modules whose end terms are `F` and `K` restricted along the structure map; such an
extension carries a canonical *action map* `I ⊗ F ⟶ K`
(`Deformation.ToposThickening.extensionActionMap`, Stacks 08MB).

This file shows that, for a prescribed action map `c`, the isomorphism classes of extensions
inducing `c` form — when there is one at all — a principal homogeneous space under
`Ext¹_{i_*O'}(F, K)`, and that whether there is one at all is governed by a class in
`Ext²_{i_*O'}(F, K)`.

The argument is: the action map depends only on the `Ext¹_O` class of the extension
(`actionOfExt`), and it does so additively (`actionExtAddHom`); the classes on which it vanishes
are exactly those pulled back from `Ext¹_{i_*O'}(F, K)` (`actionExtAddHom_eq_zero_iff`), because
an extension with vanishing action map is annihilated by `I`, hence descends along the structure
map; and restriction of scalars along the structure map is fully faithful and exact, so the
pullback map on `Ext¹` is injective. A fibre of an injective additive map is therefore a torsor
under its domain.

## Main definitions

* `Deformation.ToposThickening.extensionClass`: the `Ext¹_O` class of an extension over the
  thickening.
* `Deformation.ToposThickening.idealTensorHom`: the map on the tensor products with the
  square-zero ideal induced by a map of quotient modules.
* `Deformation.ToposThickening.FixedActionExtensionClass`: the isomorphism classes of extensions
  inducing a prescribed action of the square-zero ideal.
* `Deformation.ToposThickening.existenceObstructionClass` (**Stacks 08MF**): the obstruction to
  the existence of an extension inducing a prescribed action of the square-zero ideal.
* `Deformation.ToposThickening.MonoActionPresentation`: a presentation of the obstruction class,
  built on an extension whose action map is injective.
* `Deformation.ToposThickening.MonoActionPresentation.universalClass` and
  `Deformation.ToposThickening.MonoActionPresentation.obstruction`: the class in
  `Ext²_{i_*O'}(F, I ⊗ F)` attached to a presentation, and its pushforward along a prescribed
  action.

## Main results

* `Deformation.ToposThickening.FirstOrderThickening.essImage_restrictScalars_iff`: a sheaf of
  `O`-modules is restricted from an `i_*O'`-module exactly when the square-zero ideal
  annihilates it.
* `Deformation.ToposThickening.exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom`: the
  classes realized by an extension with a prescribed action are the translates of one of them by
  the classes pulled back from `Ext¹_{i_*O'}(F, K)`.
* `Deformation.ToposThickening.fixedActionExtensionClass_torsor` (**Stacks 08ME**): the
  principal homogeneous structure on the isomorphism classes with a fixed action.
* `Deformation.ToposThickening.existenceObstructionClass_eq_zero_iff` (**Stacks 08MF**): the
  obstruction class vanishes exactly when an extension with the prescribed action exists.
* `Deformation.ToposThickening.MonoActionPresentation.universalClass_eq`: the universal class of
  a presentation does not depend on the presentation.
* `Deformation.ToposThickening.existenceObstructionClass_eq_obstruction` (**Stacks 08MF**): the
  obstruction class is computed by any presentation.

## Implementation notes

An isomorphism class of extensions is represented by its `Ext¹_O` class: by Stacks 06XV two
short exact sequences have the same class exactly when their middle terms are isomorphic over
the end terms, so the subtype of classes realized by an extension with the prescribed action
*is* the set of isomorphism classes. The torsor structure is asserted to exist rather than
chosen, as in the source.

`FirstOrderThickening.essImage_restrictScalars_iff` replaces what would otherwise be a detour
through the direct image of modules: the essential-image criterion of Stacks 08M3 concerns the
direct image `Mod(O') ⥤ Mod(O)`, which factors as a direct image on modules followed by this
restriction of scalars, and only the second factor is needed here. It is
`Deformation.ToposThickening.essImage_restrictScalars_iff` with the kernel of the structure map
rewritten as the square-zero ideal through `FirstOrderThickening.kernel`.

`FirstOrderThickening.structureMap_locallySurjective` generalizes
`Deformation.ToposThickening.structureMap_locallySurjective`
(`StacksFrontier/Deformation/ToposThickening/ExtensionDifference.lean`), which asks for a whole
`Deformation.ToposThickening.TwoExtensions` where only the thickening is used; likewise
`idealTensorHom` generalizes `Deformation.ToposThickening.idealTensorMap`, and
`idealTensorMap_eq_idealTensorHom` records that the two agree.

The obstruction class is not built the way the source builds it. The source embeds `K` in an
injective `O`-module and realizes `c` there; instead a flat `O'`-module covering `F` is used to
produce one extension `E` of `F` whose action map `d` is *injective*, and the class is the Yoneda
product of the class of the descent of the pushout of `E` along `coker d` with the class of the
pushout of `0 → I ⊗ F → Q → coker d → 0` along `c`. Injectivity of `d` replaces injectivity of
the module, and no injective hull is needed.

The *presentation* API is what makes the class usable: `existenceObstructionClass_eq_zero_iff`
is a vanishing criterion and cannot give an identity between two classes. A
`MonoActionPresentation` records an extension with injective action map together with the
cokernel sequence of the action map and the descended extension of `F` by that cokernel; its
universal class is the Yoneda product of the two, and `MonoActionPresentation.universalClass_eq`
shows the product does not depend on any of the choices. Two presentations are compared through
a common refinement of their extensions, obtained by realizing the sum of the two `Ext¹` classes
pushed into the biproduct of the two kernel modules.

`obstructionFromMonoAction` returns the class bundled with its vanishing criterion, so that
`existenceObstructionClass_eq_zero_iff` is the second component of a single construction rather
than a statement about an opaque definition. `existenceObstructionClass` is `@[no_expose]`: its
body names the private machinery of this file, which an exposed body may not do.

## References

* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/
