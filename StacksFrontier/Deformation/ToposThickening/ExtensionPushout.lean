module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.SqZeroExt
public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.PushoutModule
public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.TwistedDescent

/-!
# Modules on first order thickenings: pushout along a morphism of thickenings

Let `(Sh(C), O)` be a ringed topos with two first order thickenings `O'₁` and `O'₂` presented on
one site, let `h^♯ : O'₂ ⟶ O'₁` be a morphism of thickenings over it, and let `I₂ ⟶ I₁` be the
induced map of defining ideals. Given an `O`-module `F`, modules `K₁`, `K₂` with action maps
`cₖ : Iₖ ⊗_O F ⟶ Kₖ` and a map `κ : K₂ ⟶ K₁` making the square with `I₂ ⟶ I₁` commute, an
extension of `F` by `K₂` over the second thickening is carried to one of `F` by `K₁` over the
first, with middle term the pushout `F'₂ ⊔_{K₂} K₁`, and the action map of the new extension is
`c₁`.

The content is the `O'₁`-module structure on that pushout, which the source omits. Write
`T := O'₂ ⋉ I₁` for the trivial square-zero extension and `q : T ⟶ O'₁` for
`(a, m) ↦ h^♯(a) - m`, a locally surjective map of sheaves of rings whose kernel is
`{(a, m) : a ∈ I₂, m = (I₂ ⟶ I₁)(a)}` and is square zero. The pushout is a `T`-module through
`T ↠ O'₂` once its action is twisted by `(a, m) ⊛ p := a · p - c₁(m ⊗ p̄)`, the Leibniz rule for
`(a, m) ↦ m` being exactly module associativity, and the kernel of `q` annihilates the twisted
module, so it descends along `q`.

## Main definitions

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.sqZeroExt`: the sheaf of rings
  `T = O'₂ ⋉ I₁`.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.sqZeroProj`: the map
  `q : T ⟶ O'₁`, which is `(a, m) ↦ h^♯(a) - m`.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`: the data
  `F`, `K₁`, `K₂`, `c₁`, `c₂`, `κ` of the remark with its commuting square.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.twist` and `.twistedModule`: the twisting term `c₁(m ⊗ p̄)` and the resulting `T`-module
  structure on the local sections of the pushout.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.descendedModule`:
  the `O'₁`-module obtained from the twisted `T`-module by descent along `q`, together with the
  identification of its restriction along `q` with the pushout.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.extensionOne`:
  the resulting extension of `F` by `K₁` over the first thickening.

## Main results

* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.sqZeroProj_locallySurjective`:
  `q` is locally surjective, because `O'₂ ⟶ O` is and `I₁` is the kernel of `O'₁ ⟶ O`.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.exists_ideal_of_sqZeroProj_eq_zero`
  and `.sqZeroProj_eq_zero_of_ideal`: a section of `T` is killed by `q` exactly when its ring
  component lies in `I₂` and its ideal component is the image of that section under the induced
  map of defining ideals.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.pushout_shortExact` and `.extOne_shortExact`: the pushout sequence
  `0 → K₁ → F'₂ ⊔_{K₂} K₁ → F → 0` is short exact over the second thickening, and its descent is
  short exact over the first.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.inclTwo_smul_eq`:
  multiplication on the pushout by a section of `I₂` is the twisting term by its image in `I₁`.
  This is what makes the kernel of `q` annihilate the twisted action, and it is where the
  commuting square of the two action maps is used.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData`
  `.extensionOne_actionMap`:
  the canonical action map of the new extension is the prescribed `c₁`.

## Implementation notes

The ring of local sections of `T` is Mathlib's `TrivSqZeroExt`, whose commutative ring structure
needs a right action of the base agreeing with the left one; over a commutative ring that action
is canonical, and `PresheafOfModules.moduleMulOpposite` and
`PresheafOfModules.isCentralScalar_of_commRing` supply it as local instances.

The sheaf condition for `T` is read off from its two components through the forgetful functor to
types, by `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`. That lemma asks the target
category to have hom-sets in the universe `max v u` of the site, so the thickened ringed topos
is taken to be `AlgebraicGeometry.RingedTopos.{v₂, u₂, max v₂ u₂}` here: the sections of the
sheaves of rings on the thickened site live in `max v₂ u₂`. This is a genuine narrowing and not
a cosmetic one; the base ringed topos `X : RingedTopos.{v, u, w}` is unconstrained. The
alternative was to repeat `Deformation.ToposThickening.descendModule` at the level of presheaves
of rings, where no sheaf condition for `T` is needed, and that would have been a third copy of
that descent (the second is private at
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatSquareZeroThickening.lean`), so the universe
constraint was preferred over the duplication.

Sections of a sheaf of modules over the sheaf of rings underlying a sheaf of commutative rings
are a module over the *commutative* ring of sections, while the pairings and tensor products
below are stated over that commutative ring; `sectionsModuleOverTwo`,
`sectionsModuleOverSqZero`, `sectionsModuleOfSqZeroExt` and
`Deformation.ToposThickening.sectionsModuleOfCommRing` are the bridging instances, local to this
file. `tensorMk` names the image of a pure tensor so that the tensor-product rewrites below act
in a position that is type-correct at the transparency `rw` uses; without it the sheafification
unit's domain and the objectwise tensor product are only definitionally equal and no rewrite
applies there.

## References

* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/
