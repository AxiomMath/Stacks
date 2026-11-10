module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedModuleDirectSum
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.ProperAlgebraBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism

/-!
# The ungraded realisation of `𝓑` is `π_* 𝒪_{X'}`

Let `X` be a scheme and `𝓑` a sheaf of graded `𝒪_X`-algebras with commutative homogeneous
multiplication. `StacksFrontier/AlgebraicGeometry/Constructions/GradedAlgebraToAlgebraSheaf.lean`
reads its ungraded realisation `SheafOfModules.GradedAlgebra.ungradedSheaf` as an algebra sheaf
in the sense of [Stacks, Tag 01LM] — `Stacks.RelativeSpec.gradedAlgebraSheaf` — whose sheaf of
rings is the realisation *itself*, not a copy of it. This file identifies that sheaf of rings
with the pushforward of the structure sheaf along the affine projection from a relative spectrum,
which is what lets a module over the ungraded realisation be read as a module over `π_* 𝒪_{X'}`
and hence, by [Stacks, Tag 01SB], as a module on `X'`.

Two forms are given. The first takes `X'` to be the relative spectrum of `𝓑` itself and is
unconditional given quasi-coherence: it is [Stacks, Tag 01LX] part (3). The second takes `X'` to
be the base change `X ×_{Spec A} Spec B` of
`StacksFrontier/AlgebraicGeometry/ProperAlgebraBaseChange/Basic.lean` and needs the source's own
identification `𝓑 = f^* B̃` as a hypothesis — as an isomorphism of algebra sheaves, which is the
only thing the identification is used through.

## Main definitions

* `Stacks.ProperAlgebraBaseChange.ungradedSheafIsoPushforwardRelativeSpec`: **`π_* 𝒪_{X'} ≅` the
  ungraded realisation of `𝓑`**, for `X'` the relative spectrum of `𝓑` and `π` its structure
  morphism, which is affine.
* `Stacks.ProperAlgebraBaseChange.ungradedSheafIsoPushforwardProj`: the same for the projection
  `π : X ×_{Spec A} Spec B ⟶ X`, given `𝓑 = f^* B̃`.
* `Stacks.ProperAlgebraBaseChange.ungradedModuleOverPushforwardRelativeSpec` and
  `ungradedModuleOverPushforwardProj`: **the ungraded realisation `⨁ₙ Fₙ` of a graded
  `𝓑`-module, as a sheaf of modules over `π_* 𝒪_{X'}`** — scalars restricted along the
  identification. This is the object [Stacks, Tag 01SB] consumes.

## Main results

* `Stacks.ProperAlgebraBaseChange.isAffineHom_relativeSpecProj`: the projection from the relative
  spectrum of `𝓑` is affine, so [Stacks, Tag 01SB] applies to it.
* `Stacks.ProperAlgebraBaseChange.ringSheaf_pushforwardAlgebra_eq`: **the two spellings of
  `π_* 𝒪_{X'}` as a sheaf of rings in the tree — pushing forward in `CommRingCat` and then
  forgetting commutativity, and the other way round — are equal**, so the module built here is
  literally a module over the sheaf of rings [Stacks, Tag 01SB] is stated with.
* `Stacks.ProperAlgebraBaseChange.isQuasicoherent_restrictScalars_ungradedSheafModule`: **the
  underlying `𝒪_X`-module of the ungraded realisation is quasi-coherent as soon as every
  homogeneous piece is.**
* `Stacks.ProperAlgebraBaseChange.isQuasicoherent_ungradedModuleOverPushforwardProj` and
  `isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces`: **`⨁ₙ Fₙ` is quasi-coherent
  over `π_* 𝒪_{X'}`**, the second assuming only quasi-coherence of the pieces. This is the
  complete input of [Stacks, Tag 01SB].

## Implementation notes

**Nothing is glued by hand and no comparison map is introduced.**
`Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf` says that the sheaf of rings of the algebra
sheaf built from `𝓑` is `SheafOfModules.GradedAlgebra.ungradedSheaf` on the nose, so the
isomorphisms below are [Stacks, Tag 01LX] part (3)
(`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`) and
`Stacks.ProperAlgebraBaseChange.pushforwardProjIso` with the forgetful functor to sheaves of
rings applied to them — `Stacks.RelativeSpec.AlgebraSheaf.ringSheafIso`, which the tree already
has — and nothing else.

**Quasi-coherence of `𝓑`'s algebra sheaf is a hypothesis.**
`Stacks.RelativeSpec.gradedAlgebraSheaf` deliberately does not assert it — the realisation of an
arbitrary sheaf of graded algebras is not quasi-coherent, and the relative spectrum of
[Stacks, Tag 01LM] is only defined for a quasi-coherent algebra sheaf. In the setting of
[Stacks, Tag 0897] it holds because `𝓑 = f^* B̃` is a pullback of a quasi-coherent algebra; in the
second form below it is not needed at all, since there `X'` is the base change and quasi-coherence
enters only through `pushforwardProjIso`, which already has it.

**The input of [Stacks, Tag 01SB] is complete here.** With `ungradedModuleOverPushforwardProj`
the graded module `F` has become a single sheaf of modules over the sheaf of rings `π_* 𝒪_{X'}`,
which is the source of [Stacks, Tag 01SB]'s equivalence, and
`isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces` supplies the quasi-coherence the
equivalence is between. The route is the one the *algebra* case takes in
`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/Quasicoherent.lean`: the underlying
`𝒪_X`-module of the realisation is the sheaf coproduct `∐ₙ Fₙ`
(`SheafOfModules.GradedModule.coprodIsoUngradedSheafModule`, out of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafifiedDirectSum.lean` with
`Stacks.RightGradedModule.act_structureMap` as its input), and on a *scheme* a coproduct of
quasi-coherent modules is quasi-coherent
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`) — so, unlike in the
algebra case, no uniformity of the covering family across the degrees has to be supplied by
hand.

**What is still missing for `F'`.** `F'` is the image of `⨁ₙ Fₙ` under the quasi-inverse of
`isEquivalence_pushforward_proj`, which is now applicable; what [Stacks, Tag 0897] part (1) asks
of `F'` beyond that is *coherence*, which is quasi-coherence plus finite type
([Stacks, Tag 01XZ], `Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae`, `X'` being
Noetherian), and the finite type has to come from the graded module's own finiteness hypothesis
`Stacks.Coherent.IsFiniteTypeOnAffine`. That transport is not written.

**No `@[stacks]` attribute is placed here.** Each statement is an instance of a tag already
carried in its own generality: [Stacks, Tag 01LX] part (3) is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` and [Stacks, Tag 01SB] is
`Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward`. Tagging a
specialisation would weaken the tag.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.ProperAlgebraBaseChange

open Stacks.RelativeSpec

variable {X : Scheme.{u}} (𝓑 : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (𝓑.piece i).val.obj W) (b : (𝓑.piece j).val.obj W),
    HEq ((𝓑.mul i j).app W a b) ((𝓑.mul j i).app W b a))

/-! ### The underlying `𝒪_X`-module of the realisation -/

/-- **The sheaf coproduct `∐ₙ Fₙ` of the homogeneous pieces of a graded module on a scheme is
quasi-coherent as soon as every piece is.** On a scheme no uniformity across the degrees has to
be supplied: quasi-coherence of modules on a scheme is closed under colimits of every shape,
which is `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit`, and a
coproduct is a colimit over a discrete category. -/
theorem isQuasicoherent_coprod_piece (F : SheafOfModules.GradedModule 𝓑)
    (hqc : ∀ n : ℤ, (F.piece n).IsQuasicoherent) : (∐ F.piece).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit
    (Discrete.functor F.piece) fun n => hqc n.as

/-- **The underlying `𝒪_X`-module of the ungraded realisation `⨁ₙ Fₙ` of a graded `𝓑`-module is
quasi-coherent**, as soon as every homogeneous piece is.

This is the statement that stood between
`Stacks.ProperAlgebraBaseChange.ungradedModuleOverPushforwardProj` and the input of
[Stacks, Tag 01SB]. It is `SheafOfModules.GradedModule.coprodIsoUngradedSheafModule`, which
identifies the underlying `𝒪_X`-module of the realisation with `∐ₙ Fₙ` exactly as the *algebra*
case of [Stacks, Tag 01CL] does in
`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/Quasicoherent.lean`, together with
`isQuasicoherent_coprod_piece`. -/
theorem isQuasicoherent_restrictScalars_ungradedSheafModule
    (F : SheafOfModules.GradedModule 𝓑) (hqc : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (F.ungradedSheafModule hc)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (F.coprodIsoUngradedSheafModule hc) (isQuasicoherent_coprod_piece 𝓑 F hqc)

/-! ### `X'` the relative spectrum of `𝓑` -/

section RelativeSpectrum

variable [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X 𝓑 hc)]

/-- The relative spectrum of a sheaf of graded algebras with commutative homogeneous
multiplication: the scheme `X'` of [Stacks, Tag 0897]'s proof, built from `𝓑` alone. -/
abbrev relativeSpecScheme : Scheme.{u} := relativeSpec (gradedAlgebraSheaf X 𝓑 hc)

/-- The projection `π : X' ⟶ X` from the relative spectrum of `𝓑`. -/
abbrev relativeSpecProj : relativeSpecScheme 𝓑 hc ⟶ X :=
  relativeSpecToBase (gradedAlgebraSheaf X 𝓑 hc)

/-- **The projection from the relative spectrum of `𝓑` is affine**, so [Stacks, Tag 01SB]
applies to it. -/
instance isAffineHom_relativeSpecProj : IsAffineHom (relativeSpecProj 𝓑 hc) :=
  isAffineHom_relativeSpecToBase _

/-- **`π_* 𝒪_{X'}` is the ungraded realisation of `𝓑`**, for `X'` the relative spectrum of `𝓑`.

This is [Stacks, Tag 01LX] part (3) (`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`)
read on the underlying sheaves of rings, together with
`Stacks.RelativeSpec.ringSheaf_gradedAlgebraSheaf`, which says that the sheaf of rings of the
algebra sheaf of `𝓑` is the ungraded realisation itself. -/
def ungradedSheafIsoPushforwardRelativeSpec :
    AlgebraSheaf.ringSheaf (pushforwardAlgebra (relativeSpecProj 𝓑 hc)) ≅ 𝓑.ungradedSheaf :=
  AlgebraSheaf.ringSheafIso (pushforwardAlgebraIso (gradedAlgebraSheaf X 𝓑 hc))

/-- **The ungraded realisation `⨁ₙ Fₙ` of a graded `𝓑`-module, as a sheaf of modules over
`π_* 𝒪_{X'}`** for `X'` the relative spectrum of `𝓑`: the module structure of
`SheafOfModules.GradedModule.ungradedSheafModule` with its scalars restricted along
`ungradedSheafIsoPushforwardRelativeSpec`.

This is the shape [Stacks, Tag 01SB] consumes; what it does not assert is quasi-coherence, which
is what the equivalence is between. -/
def ungradedModuleOverPushforwardRelativeSpec (F : SheafOfModules.GradedModule 𝓑) :
    SheafOfModules.{u} (AlgebraSheaf.ringSheaf (pushforwardAlgebra (relativeSpecProj 𝓑 hc))) :=
  (SheafOfModules.restrictScalars
    (ungradedSheafIsoPushforwardRelativeSpec 𝓑 hc).hom).obj (F.ungradedSheafModule hc)

end RelativeSpectrum

/-! ### `X'` the base change `X ×_{Spec A} Spec B` -/

section BaseChange

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (f : X ⟶ Spec (.of A))

/-- **`π_* 𝒪_{X'}` is the ungraded realisation of `𝓑`** for the projection
`π : X ×_{Spec A} Spec B ⟶ X`, given the source's identification `𝓑 = f^* B̃` as an isomorphism
of algebra sheaves.

`Stacks.ProperAlgebraBaseChange.pushforwardProjIso` is `π_* 𝒪_{X'} ≅ f^* B̃`; composing it with
`e` and reading the result on the underlying sheaves of rings gives the identification, because
the sheaf of rings of the algebra sheaf of `𝓑` is the ungraded realisation itself. -/
def ungradedSheafIsoPushforwardProj
    (e : gradedAlgebraSheaf X 𝓑 hc ≅ (algebraPullback f).obj (specAlgebraSheaf A B)) :
    AlgebraSheaf.ringSheaf (pushforwardAlgebra (proj A B f)) ≅ 𝓑.ungradedSheaf :=
  AlgebraSheaf.ringSheafIso (pushforwardProjIso A B f ≪≫ e.symm)

/-- **The ungraded realisation `⨁ₙ Fₙ` of a graded `𝓑`-module, as a sheaf of modules over
`π_* 𝒪_{X'}`** for `X' = X ×_{Spec A} Spec B`, given `𝓑 = f^* B̃`. -/
def ungradedModuleOverPushforwardProj (F : SheafOfModules.GradedModule 𝓑)
    (e : gradedAlgebraSheaf X 𝓑 hc ≅ (algebraPullback f).obj (specAlgebraSheaf A B)) :
    SheafOfModules.{u} (AlgebraSheaf.ringSheaf (pushforwardAlgebra (proj A B f))) :=
  (SheafOfModules.restrictScalars
    (ungradedSheafIsoPushforwardProj 𝓑 hc A B f e).hom).obj (F.ungradedSheafModule hc)

/-- **The two spellings of `π_* 𝒪_{X'}` as a sheaf of rings agree on the nose.** The algebra
sheaf `Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` pushes the structure sheaf forward in
`CommRingCat` and then forgets commutativity; [Stacks, Tag 01SB] is stated with
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`, which forgets commutativity
and then pushes forward. Both are precomposition with `Opens.map`, so they are equal, and a
module over either is a module over the other with no transport. -/
theorem ringSheaf_pushforwardAlgebra_eq {X' Y : Scheme.{u}} (π : X' ⟶ Y) :
    AlgebraSheaf.ringSheaf (pushforwardAlgebra π) =
      Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing π.base X'.ringCatSheaf :=
  rfl

/-- The structure morphism of the algebra sheaf `π_* 𝒪_{X'}` is the morphism of sheaves of rings
induced by `π`, which is the one [Stacks, Tag 01SB] restricts scalars along. -/
theorem structureMap_pushforwardAlgebra_eq {X' Y : Scheme.{u}} (π : X' ⟶ Y) :
    AlgebraSheaf.structureMap (pushforwardAlgebra π) = π.toRingCatSheafHom :=
  rfl

/-- Quasi-coherence of a restriction of scalars transports along an equality of the morphism of
sheaves of rings the scalars are restricted along.

This is a lemma with the two morphisms as variables rather than a `rw`: the type of
`SheafOfModules.restrictScalars α` mentions `α`, so rewriting `α` inside it is not type-correct
at `implicit` transparency — the defeq-spelling discipline recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedRealization.lean`. With variables, `subst`
does the work. -/
theorem isQuasicoherent_restrictScalars_of_eq {Y : Scheme.{u}}
    {R S : Sheaf (Opens.grothendieckTopology ↥Y) RingCat.{u}} {α β : R ⟶ S} (h : α = β)
    (M : SheafOfModules.{u} S)
    (hM : ((SheafOfModules.restrictScalars β).obj M).IsQuasicoherent) :
    ((SheafOfModules.restrictScalars α).obj M).IsQuasicoherent := by
  subst h
  exact hM

/-- **Quasi-coherence over `π_* 𝒪_{X'}` is a statement about `𝒪_X`-modules.** The module
`ungradedModuleOverPushforwardProj` is quasi-coherent over `π_* 𝒪_{X'}` as soon as the ungraded
realisation `⨁ₙ Fₙ`, read as an `𝒪_X`-module through the structure map of `𝓑`, is
quasi-coherent — `π` is affine, so [Stacks, Tag 01SB]'s
`Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff` identifies the
two, and the composite of the two restrictions of scalars is the structure map of `𝓑` because
the isomorphism used is one of *algebra* sheaves.

The hypothesis is discharged from quasi-coherence of the homogeneous pieces by
`isQuasicoherent_restrictScalars_ungradedSheafModule`; the two together are
`isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces`. -/
theorem isQuasicoherent_ungradedModuleOverPushforwardProj (F : SheafOfModules.GradedModule 𝓑)
    (e : gradedAlgebraSheaf X 𝓑 hc ≅ (algebraPullback f).obj (specAlgebraSheaf A B))
    (hqc : ((SheafOfModules.restrictScalars 𝓑.ungradedStructureMap).obj
      (F.ungradedSheafModule hc)).IsQuasicoherent) :
    (ungradedModuleOverPushforwardProj 𝓑 hc A B f F e).IsQuasicoherent := by
  have hcomp : (proj A B f).toRingCatSheafHom ≫
      (ungradedSheafIsoPushforwardProj 𝓑 hc A B f e).hom = 𝓑.ungradedStructureMap :=
    AlgebraSheaf.structureMap_comp_ringSheafMap (pushforwardProjIso A B f ≪≫ e.symm).hom
  refine (Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff
    (proj A B f) _).1 ?_
  change ((SheafOfModules.restrictScalars ((proj A B f).toRingCatSheafHom ≫
    (ungradedSheafIsoPushforwardProj 𝓑 hc A B f e).hom)).obj
      (F.ungradedSheafModule hc)).IsQuasicoherent
  exact isQuasicoherent_restrictScalars_of_eq hcomp _ hqc

/-- **`⨁ₙ Fₙ` is a quasi-coherent module over `π_* 𝒪_{X'}`**, assuming only that each
homogeneous piece `Fₙ` is quasi-coherent. This is the object [Stacks, Tag 01SB] takes as input,
together with the property the equivalence is between, so it is what produces the module `F'` on
the base change. -/
theorem isQuasicoherent_ungradedModuleOverPushforwardProj_of_pieces
    (F : SheafOfModules.GradedModule 𝓑)
    (e : gradedAlgebraSheaf X 𝓑 hc ≅ (algebraPullback f).obj (specAlgebraSheaf A B))
    (hqc : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    (ungradedModuleOverPushforwardProj 𝓑 hc A B f F e).IsQuasicoherent :=
  isQuasicoherent_ungradedModuleOverPushforwardProj 𝓑 hc A B f F e
    (isQuasicoherent_restrictScalars_ungradedSheafModule 𝓑 hc F hqc)

end BaseChange

end Stacks.ProperAlgebraBaseChange

end
