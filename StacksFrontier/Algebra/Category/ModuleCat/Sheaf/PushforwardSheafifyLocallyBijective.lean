module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the exterior and symmetric algebras of a quasi-coherent module sheaf

Let `(X, 𝒪_X)` be a ringed space and `F` a quasi-coherent sheaf of `𝒪_X`-modules. Stacks Tag
01CL asserts that the tensor, exterior and symmetric algebras of `F` are again quasi-coherent.
This file proves the exterior and the symmetric assertion:

`Stacks.SheafOfModules.isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent` and
`isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent`.

## The shape of the proof

Tag 01CL's proof opens by warning that an infinite direct sum of quasi-coherent modules need
*not* be quasi-coherent: the opens on which the summands are presented may intersect in no
neighbourhood of a point. What rescues the lemma is that a *single* open presents every
homogeneous piece simultaneously. That formal step is
`SheafOfModules.TensorExteriorSymmetricAlgebras.isQuasicoherent_symmetricAlgebraSheaf` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod`, whose hypothesis is
exactly a presentation of `(Symⁿ F)|_U` for one covering family and all `n`. This file supplies
that hypothesis, and the only mathematics it needs is Tag 01CJ, which is already proved:
`Stacks.SheafOfModules.exists_free_symmetricPower_presentation` turns an exact presentation of
`F` by free module sheaves into one of every positive symmetric power, *over the same space*.

Three things stand between that and the hypothesis, and they are what this file does.

**The site has to change, and that is the one non-trivial step.** Tag 01CJ is proved stalkwise
on a topological space, so `exists_free_symmetricPower_presentation` is stated for a
`AlgebraicGeometry.RingedSpace`, whereas `SheafOfModules.QuasicoherentData` demands a
presentation of `F.over U` on the *slice site* `(Over U, J.over U)`. Mathlib's
`TopologicalSpace.Opens.overEquivalence : Over U ≌ Opens ↥U` and
`TopologicalSpace.Opens.sheafOfModulesEquivOver` move module sheaves between the two, but say
nothing about symmetric powers. So the comparison
`(Symⁿ_{Over U}(F|_U))|^{Opens ↥U} ≅ Symⁿ_{Opens ↥U}(F|_U)` has to be proved, and it is proved
here in the generality in which it is natural: for the pushforward along *any* continuous and
cocontinuous functor of sites.

**The degree-zero piece is not covered by Tag 01CJ**, which needs `1 ≤ n`. For the exterior
algebra the degree-zero identification with the structure sheaf is a field of the bundle
(`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit`); for the symmetric
algebra it is not, and `SheafOfModules.sectionwiseSymmetricPieceZeroIso` below supplies it from
`SymmetricAlgebra.symmetricPowerZeroEquiv`, exactly as `sheafifyExtPowZeroIso` does in the
exterior case.

**A free module sheaf has to be given a presentation**, with no relations, so that the
structure sheaf has one. That is `Stacks.SheafOfModules.presentationFree` and
`presentationUnit`.

## Main definitions

* `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso`:
  **sheafification of presheaves of modules commutes with pushforward along a continuous and
  cocontinuous functor of sites.**
* `PresheafOfModules.symPowPushforwardIso` and `extPowPushforwardIso`: the presheaves of
  sectionwise symmetric and exterior powers commute with pushforward along an arbitrary
  functor, on the nose.
* `PresheafOfModules.symPowZeroIso`, `SheafOfModules.sheafifySymPowZeroIso` and
  `SheafOfModules.sectionwiseSymmetricPieceZeroIso`: the degree-zero symmetric power is the
  structure sheaf.
* `Stacks.SheafOfModules.presentationFree` and `presentationUnit`: a free module sheaf, and in
  particular the structure sheaf, has a presentation with no relations.
* `Stacks.SheafOfModules.openSubspace`: an open of a ringed space as a ringed space. This is
  `AlgebraicGeometry.SheafedSpace.restrict`, recorded as a reducible abbreviation; see the
  implementation notes.

## Main results

* `Stacks.SheafOfModules.symmetricPowerPushforwardIso` and `exteriorPowerPushforwardIso`:
  **pushforward along a continuous and cocontinuous functor of sites commutes with the
  symmetric, respectively exterior, power**, for an arbitrary choice of the two algebras.
* `Stacks.SheafOfModules.nonempty_presentation_symmetricPower` and
  `nonempty_presentation_exteriorPower`: on a ringed space, a presentation of `F` presents
  every symmetric, respectively exterior, power of `F`. This is where Tag 01CJ is used, and the
  degree-zero case is included.
* `Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over` and
  `nonempty_presentation_exteriorPower_over`: the same conclusion on the slice site over an
  open, which is the hypothesis the coproduct builder wants.
* `Stacks.SheafOfModules.isQuasicoherent_symmetricPower`: **clause (5) of Tag 01CK for the
  symmetric powers** — each `Symⁿ F` of a quasi-coherent `F` is quasi-coherent.
* `Stacks.SheafOfModules.isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent` and
  `isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent`: **clause (1) of Tag 01CL for the
  symmetric and the exterior algebra.**

## Implementation notes

**The tensor algebra is not treated here, and the reason is the shape of the input.** What is
used below is the three-term exact sequence of Tag 01CJ, which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences` builds for the
exterior and the symmetric quotient only. The tensor power of a presented module sheaf is not
presented by a three-term sequence at all — already `T²` needs
`(M₂ ⊗ M₁) ⊕ (M₁ ⊗ M₂) ⟶ M₁ ⊗ M₁ ⟶ M ⊗ M ⟶ 0`. The tensor assertion therefore goes by induction
on the degree instead, and it is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation`
(`Stacks.SheafOfModules.isQuasicoherent_tensorPower` and
`isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent`). Correspondingly `@[stacks 01CL]` here
is placed on the two results proved, with clause strings naming which algebra each covers.

**Why `openSubspace` is an `abbrev` and not a `def`.** `Stacks.SheafOfModules.openSubspace U`
is definitionally `X.restrict U.isOpenEmbedding` — that is recorded as
`openSubspace_eq_restrict`, proved by `rfl`, so no second notion of open subspace is
introduced. What the abbreviation buys is that its structure sheaf is *reducibly* the
pushforward of the slice structure sheaf along `Opens.overEquivalence`. The comparison
isomorphisms below are stated for the pushforward, and the algebra bundles on the open subspace
are stated for `openSubspace U`; unifying the two through a non-reducible `def` makes the
elaborator unfold a tactic-produced equivalence and exhausts the heartbeat budget. With the
abbreviation each such identification is an iota reduction.

**Three implicit arguments must be named at the application site**, and this is the same
discipline as in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction`. The
sheaf of commutative rings `Osharp` of `Stacks.SheafOfModules.symmetricPowerPushforwardIso` is
implicit and determined by its module argument through
`CategoryTheory.Sheaf.toRingCat Jt Osharp`; with the module argument `F.over U`, whose ring
sheaf is spelled `(structureSheafRing X).over U`, inferring it is the higher-order problem
`toRingCat Jt ?Osharp =?= (structureSheafRing X).over U`, which does not resolve at the default
heartbeat budget. Supplying `(Jt := _)` and `(Osharp := X.sheaf.over U)` makes it a check rather
than a search.

**Transport of a presentation along an isomorphism goes through
`Stacks.SheafOfModules.presentationOfIso`**, which takes an `Iso` rather than a morphism with
an `IsIso` instance. `SheafOfModules.Presentation.ofIsIso` cannot be applied directly to the
comparison isomorphisms below: typeclass resolution unfolds at reducible transparency only, and
the `IsIso` instance for the `hom` of an isomorphism whose type mentions the sectionwise
symmetric algebra is not found. The same remedy, for the same reason, is
`Stacks.Modules.presentationOfIso` in
`StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal`, which is the scheme-level twin of
this file's `presentationOfOpenSubspaceIso`; a dedup is owed once one of the two is generalized
to cover the other's site.

**The dedup owed against the slice-only statements.**
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso` and
`PresheafOfModules.symPowOverIso`/`extPowOverIso` are the special cases of
`pushforwardSheafifyIso` and `symPowPushforwardIso`/`extPowPushforwardIso` at
`G := Over.forget U`, and `Stacks.SheafOfModules.symmetricPowerOverIso`/`exteriorPowerOverIso`
are the special cases of `symmetricPowerPushforwardIso`/`exteriorPowerPushforwardIso` there.
The proofs here are those proofs with the functor freed; nothing about `Over.forget U` beyond
cocontinuity was used, which is already visible in the slice file, where the only input is
`CategoryTheory.Presheaf.isLocallySurjective_whisker`. The slice statements are still consumed
below — `symmetricPowerOverIso` is the last step of the assembly — so they are not dead, but
restating them as corollaries of these is owed.

**Universes.** `pushforwardSheafifyIso` keeps four independent parameters: the two sites at
`Type u`/`Type u'` with `Category.{v}`/`Category.{v'}`, the sheaf of rings at `RingCat.{t}` and
the modules at `PresheafOfModules.{w}`, with `t` and `w` independent. The power comparisons tie
the ring universe to the module universe because `SheafOfModules.symmetricPieceIso` does. The
ringed-space results are at `RingedSpace.{u, u}` with modules in `SheafOfModules.{u}`, which is
forced by Tag 01CJ and recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerPresentation`. The covering family's
index type is free: `isQuasicoherent_symmetricAlgebraSheaf` takes it in any `Type w`.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
  AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe w t v u v' u'

/-! ### Sheafification commutes with pushforward along a cocontinuous functor -/

namespace Stacks.SheafOfModules.PushforwardSheafification

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D} (G : C ⥤ D)
  [G.IsContinuous J K] (R : Sheaf K RingCat.{t})

variable [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [G.IsCocontinuous J K] (P : PresheafOfModules.{w} R.obj)

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [G.IsCocontinuous J K] in
include J in
/-- The comparison of the sheafification of a pushforward with the pushforward of the
sheafification is invertible as soon as the pushed-forward sheafification unit is locally
bijective. Under cocontinuity of `G` that is automatic
(`Stacks.SheafOfModules.PushforwardSheafification.isIso_pushforwardSheafifyHom`); a closed
embedding of topological spaces, which is not cocontinuous, still satisfies it. -/
theorem isIso_pushforwardSheafifyHom_of_isLocallyBijective
    (hinj : Presheaf.IsLocallyInjective J (pushforwardToSheafify.{w} J G R P))
    (hsurj : Presheaf.IsLocallySurjective J (pushforwardToSheafify.{w} J G R P)) :
    IsIso (pushforwardSheafifyHom.{w} J G R P) :=
  SliceSheafification.isIso_sheafificationHomEquiv_symm.{w}
    (R₀ := (pushforwardRingSheaf J G R).obj) (Rs := pushforwardRingSheaf J G R)
    (P := (presheafPushforwardFunctor.{w} J G R).obj P)
    (T := (sheafPushforwardFunctor.{w} J G R).obj
      ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P))
    (𝟙 (pushforwardRingSheaf J G R).obj) (pushforwardUnit.{w} J G R P) hinj hsurj

end Stacks.SheafOfModules.PushforwardSheafification

/-! ### The sectionwise powers commute with pushforward -/

namespace PresheafOfModules

section SitePushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
  {O : Dᵒᵖ ⥤ CommRingCat.{w}} (n : ℕ)
  (P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-! #### Symmetric powers -/

/-! #### Exterior powers -/

end SitePushforward

/-! ### The degree-zero symmetric power -/

section SymPowZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

end SymPowZero

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

end SheafOfModules

/-! ### The power comparisons for a pushforward -/

namespace Stacks.SheafOfModules

open _root_.PresheafOfModules Stacks.SheafOfModules.PushforwardSheafification

variable {Cs : Type u} [Category.{v} Cs] {Ct : Type u'} [Category.{v'} Ct]
  (Js : GrothendieckTopology Cs) {Jt : GrothendieckTopology Ct} (G : Cs ⥤ Ct)
  [G.IsContinuous Js Jt] [G.IsCocontinuous Js Jt]
  {Osharp : Sheaf Jt CommRingCat.{w}}
  [Jt.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Js.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Jt.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Jt AddCommGrpCat.{w}]
  [Js.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Js AddCommGrpCat.{w}]
  (M : _root_.SheafOfModules.{w} (toRingCat Jt Osharp)) (n : ℕ)

section Symmetric

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra B gen')

end Symmetric

section Exterior

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')

end Exterior

end Stacks.SheafOfModules

/-! ### Presentations of a free sheaf of modules -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

end Stacks.SheafOfModules

/-! ### Tag 01CL -/

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.PushforwardSheafification

/-! #### Every power of a presented module sheaf on a ringed space is presented -/

/-! #### The open subspace, and transport to the slice site -/

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

variable (F : _root_.SheafOfModules.{u} (structureSheafRing X))

variable (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-! #### The conclusions -/

section Conclusions

variable {X : RingedSpace.{u, u}} (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  [F.IsQuasicoherent]
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

end Conclusions

end Stacks.SheafOfModules

end
