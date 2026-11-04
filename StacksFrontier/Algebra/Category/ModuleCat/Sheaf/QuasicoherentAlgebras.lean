module

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

/-- The pushforward of a sheaf of rings along a continuous functor. -/
noncomputable abbrev pushforwardRingSheaf : Sheaf J RingCat.{t} :=
  (G.sheafPushforwardContinuous RingCat.{t} J K).obj R

/-- Pushforward of presheaves of modules along `G`, with no change of scalars. -/
noncomputable abbrev presheafPushforwardFunctor :
    PresheafOfModules.{w} R.obj ⥤ PresheafOfModules.{w} (pushforwardRingSheaf J G R).obj :=
  PresheafOfModules.pushforward.{w} (F := G) (𝟙 (pushforwardRingSheaf J G R).obj)

/-- Pushforward of sheaves of modules along `G`, with no change of scalars. -/
noncomputable abbrev sheafPushforwardFunctor :
    _root_.SheafOfModules.{w} R ⥤ _root_.SheafOfModules.{w} (pushforwardRingSheaf J G R) :=
  _root_.SheafOfModules.pushforward.{w} (𝟙 (pushforwardRingSheaf J G R))

variable [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [G.IsCocontinuous J K] (P : PresheafOfModules.{w} R.obj)

/-- The sheafification unit of `P`, pushed forward along `G`: its component at `V` is the
component of the unit at `G V`. -/
noncomputable def pushforwardUnit :
    (presheafPushforwardFunctor.{w} J G R).obj P ⟶
      (PresheafOfModules.restrictScalars (𝟙 (pushforwardRingSheaf J G R).obj)).obj
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P)).val where
  app V := ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.app P).app
    (G.op.obj V)
  naturality f :=
    ((PresheafOfModules.sheafificationAdjunction.{w} (𝟙 R.obj)).unit.app P).naturality
      (G.op.map f)

/-- `Stacks.SheafOfModules.PushforwardSheafification.pushforwardUnit` at the level of the
underlying presheaves of abelian groups. The type is ascribed so that the target is spelled
through `PresheafOfModules.toPresheaf`, which is the spelling the local-bijectivity statements
need. -/
noncomputable def pushforwardToSheafify :
    ((presheafPushforwardFunctor.{w} J G R).obj P).presheaf ⟶
      (PresheafOfModules.toPresheaf (pushforwardRingSheaf J G R).obj).obj
        ((sheafPushforwardFunctor.{w} J G R).obj
          ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P)).val :=
  (PresheafOfModules.toPresheaf (pushforwardRingSheaf J G R).obj).map
    (pushforwardUnit.{w} J G R P)

omit [G.IsCocontinuous J K] in
/-- The pushed-forward sheafification unit is the whiskering of the sheafification unit along
`G`. -/
theorem pushforwardToSheafify_eq : pushforwardToSheafify.{w} J G R P =
    Functor.whiskerLeft G.op (CategoryTheory.toSheafify K P.presheaf) := rfl

/-- The pushed-forward sheafification unit is locally surjective: `G` is cocontinuous, so local
surjectivity is inherited by the whiskering. -/
theorem isLocallySurjective_pushforwardToSheafify :
    Presheaf.IsLocallySurjective J (pushforwardToSheafify.{w} J G R P) := by
  rw [pushforwardToSheafify_eq]
  exact Presheaf.isLocallySurjective_whisker J K G _

/-- The pushed-forward sheafification unit is locally injective. -/
theorem isLocallyInjective_pushforwardToSheafify :
    Presheaf.IsLocallyInjective J (pushforwardToSheafify.{w} J G R P) := by
  rw [pushforwardToSheafify_eq]
  exact Presheaf.isLocallyInjective_whisker J K G _

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The comparison morphism from the sheafification of the pushforward of `P` to the pushforward
of the sheafification: the morphism adjoint to the pushed-forward sheafification unit. -/
noncomputable def pushforwardSheafifyHom :
    (PresheafOfModules.sheafification.{w} (𝟙 (pushforwardRingSheaf J G R).obj)).obj
        ((presheafPushforwardFunctor.{w} J G R).obj P) ⟶
      (sheafPushforwardFunctor.{w} J G R).obj
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (pushforwardRingSheaf J G R).obj)).symm
    (pushforwardUnit.{w} J G R P)

/-- The comparison morphism `pushforwardSheafifyHom` is an isomorphism: the pushed-forward
sheafification unit it is adjoint to is locally injective and locally surjective. -/
instance isIso_pushforwardSheafifyHom : IsIso (pushforwardSheafifyHom.{w} J G R P) :=
  SliceSheafification.isIso_sheafificationHomEquiv_symm.{w}
    (R₀ := (pushforwardRingSheaf J G R).obj) (Rs := pushforwardRingSheaf J G R)
    (P := (presheafPushforwardFunctor.{w} J G R).obj P)
    (T := (sheafPushforwardFunctor.{w} J G R).obj
      ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P))
    (𝟙 (pushforwardRingSheaf J G R).obj) (pushforwardUnit.{w} J G R P)
    (isLocallyInjective_pushforwardToSheafify.{w} J G R P)
    (isLocallySurjective_pushforwardToSheafify.{w} J G R P)

/-- **Sheafification of presheaves of modules commutes with pushforward along a continuous and
cocontinuous functor of sites.** This is
`Stacks.SheafOfModules.SliceSheafification.sheafifyOverIso` with the functor freed from
`Over.forget U`; see the implementation notes of this file. -/
noncomputable def pushforwardSheafifyIso :
    (PresheafOfModules.sheafification.{w} (𝟙 (pushforwardRingSheaf J G R).obj)).obj
        ((presheafPushforwardFunctor.{w} J G R).obj P) ≅
      (sheafPushforwardFunctor.{w} J G R).obj
        ((PresheafOfModules.sheafification.{w} (𝟙 R.obj)).obj P) :=
  asIso (pushforwardSheafifyHom.{w} J G R P)

end Stacks.SheafOfModules.PushforwardSheafification

/-! ### The sectionwise powers commute with pushforward -/

namespace PresheafOfModules

section SitePushforward

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (G : C ⥤ D)
  {O : Dᵒᵖ ⥤ CommRingCat.{w}} (n : ℕ)
  (P : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- Pushforward of presheaves of modules along `G`, with no change of scalars. This is
`PresheafOfModules.pushforward₀`, which is the `PresheafOfModules.pushforward` at the identity
used by `Stacks.SheafOfModules.PushforwardSheafification.presheafPushforwardFunctor`. -/
noncomputable abbrev sitePushforward :
    PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⥤
      PresheafOfModules.{w} (G.op ⋙ (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :=
  pushforward₀.{w} G (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})

/-! #### Symmetric powers -/

/-- The identity map of underlying presheaves of abelian groups, from the pushforward of the
presheaf of sectionwise symmetric powers to the presheaf of sectionwise symmetric powers of the
pushforward. -/
noncomputable def symPowPushforwardAb :
    ((sitePushforward G (O := O)).obj (symPow n P)).presheaf ⟶
      (symPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf where
  app X := 𝟙 (((sitePushforward G (O := O)).obj (symPow n P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- The inverse of `PresheafOfModules.symPowPushforwardAb`, again the identity on sections. -/
noncomputable def symPowPushforwardAbInv :
    (symPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf ⟶
      ((sitePushforward G (O := O)).obj (symPow n P)).presheaf where
  app X := 𝟙 ((symPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- **The presheaf of sectionwise symmetric powers commutes with pushforward along an arbitrary
functor.** The comparison is the identity on sections. -/
noncomputable def symPowPushforwardIso :
    (sitePushforward G (O := O)).obj (symPow n P) ≅
      symPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P) where
  hom := homMk (symPowPushforwardAb G n P) (fun _ _ _ => rfl)
  inv := homMk (symPowPushforwardAbInv G n P) (fun _ _ _ => rfl)
  hom_inv_id := by ext X x; rfl
  inv_hom_id := by ext X x; rfl

/-- The comparison of sectionwise symmetric powers is the identity on sections. -/
@[simp]
theorem symPowPushforwardAb_app (X : Cᵒᵖ) : (symPowPushforwardAb G n P).app X =
    𝟙 (((sitePushforward G (O := O)).obj (symPow n P)).presheaf.obj X) := rfl

/-! #### Exterior powers -/

/-- The identity map of underlying presheaves of abelian groups, from the pushforward of the
presheaf of sectionwise exterior powers to the presheaf of sectionwise exterior powers of the
pushforward. -/
noncomputable def extPowPushforwardAb :
    ((sitePushforward G (O := O)).obj (extPow n P)).presheaf ⟶
      (extPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf where
  app X := 𝟙 (((sitePushforward G (O := O)).obj (extPow n P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- The inverse of `PresheafOfModules.extPowPushforwardAb`, again the identity on sections. -/
noncomputable def extPowPushforwardAbInv :
    (extPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf ⟶
      ((sitePushforward G (O := O)).obj (extPow n P)).presheaf where
  app X := 𝟙 ((extPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P)).presheaf.obj X)
  naturality _ _ _ := by ext x; rfl

/-- **The presheaf of sectionwise exterior powers commutes with pushforward along an arbitrary
functor.** The comparison is the identity on sections.

As in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction`, this is built from
`PresheafOfModules.homMk` on the underlying presheaves of abelian groups rather than from
`PresheafOfModules.isoMk`: the latter asks for isomorphisms of the `ModuleCat` objects, whose
`Module` instance is reached through `exteriorPower`, a submodule of a quotient algebra, and the
resulting `isDefEq` query exhausts the heartbeat budget. -/
noncomputable def extPowPushforwardIso :
    (sitePushforward G (O := O)).obj (extPow n P) ≅
      extPow (O := G.op ⋙ O) n ((sitePushforward G (O := O)).obj P) where
  hom := homMk (extPowPushforwardAb G n P) (fun _ _ _ => rfl)
  inv := homMk (extPowPushforwardAbInv G n P) (fun _ _ _ => rfl)
  hom_inv_id := by ext X x; rfl
  inv_hom_id := by ext X x; rfl

/-- The comparison of sectionwise exterior powers is the identity on sections. -/
@[simp]
theorem extPowPushforwardAb_app (X : Cᵒᵖ) : (extPowPushforwardAb G n P).app X =
    𝟙 (((sitePushforward G (O := O)).obj (extPow n P)).presheaf.obj X) := rfl

end SitePushforward

/-! ### The degree-zero symmetric power -/

section SymPowZero

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat))

/-- `SymmetricAlgebra.symmetricPowerZeroEquiv` with its type spelled at the sections of
`PresheafOfModules.unit` and of `PresheafOfModules.symPow`. -/
noncomputable def symPowZeroApp (X : Cᵒᵖ) :
    (PresheafOfModules.unit (O ⋙ forget₂ _ RingCat)).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      (symPow 0 F).obj X :=
  SymmetricAlgebra.symmetricPowerZeroEquiv _ _

/-- **The zeroth sectionwise symmetric power is the free presheaf of modules of rank one.**
The symmetric analogue of `PresheafOfModules.extPowZeroIso`. -/
noncomputable def symPowZeroIso :
    PresheafOfModules.unit (O ⋙ forget₂ _ RingCat) ≅ symPow 0 F :=
  PresheafOfModules.isoMk (fun X => (symPowZeroApp F X).toModuleIso) fun {X Y} f => by
    refine ModuleCat.hom_ext (LinearMap.ext fun r => Subtype.ext ?_)
    exact (SymmetricAlgebra.mapₛₗ_algebraMap ((O ⋙ forget₂ _ RingCat).map f).hom
      (F.restrictₛₗ f) r).symm

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

/-- The sheafification of the zeroth sectionwise symmetric power is the structure sheaf. The
symmetric analogue of `SheafOfModules.sheafifyExtPowZeroIso`. -/
noncomputable def sheafifySymPowZeroIso :
    (moduleSheafification J a).obj (symPow 0 F) ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  (moduleSheafification J a).mapIso (symPowZeroIso F).symm ≪≫
    sheafificationObjUnitIso (toRingCatMap J a)

/-- **The degree-zero piece of the sheafified sectionwise symmetric algebra is the structure
sheaf.** This is what Tag 01CJ does not supply: it presents only the powers of degree at least
one. -/
noncomputable def sectionwiseSymmetricPieceZeroIso :
    (sectionwiseSymmetricAlgebra J a F).piece 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  sheafifySymPowZeroIso J a F

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

/-- The pushforward of the sheaf of commutative rings along `G`. Composing it with the forgetful
functor to `RingCat` gives
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardRingSheaf` of the composite, on the
nose. -/
noncomputable abbrev pushforwardCommRingSheaf : Sheaf Js CommRingCat.{w} :=
  (G.sheafPushforwardContinuous CommRingCat.{w} Js Jt).obj Osharp

/-- **The sheafified sectionwise symmetric power commutes with pushforward.** -/
noncomputable def sectionwiseSymmetricPowerPushforwardIso :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        ((_root_.SheafOfModules.sectionwiseSymmetricAlgebra Jt (𝟙 Osharp.obj) M.val).piece
          (n : ℤ)) ≅
      (_root_.SheafOfModules.sectionwiseSymmetricAlgebra Js
        (𝟙 (pushforwardCommRingSheaf Js G (Osharp := Osharp)).obj)
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M).val).piece (n : ℤ) :=
  (pushforwardSheafifyIso.{w} Js G (toRingCat Jt Osharp) (symPow n M.val)).symm ≪≫
    (sheafification.{w} (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)).mapIso
      (symPowPushforwardIso G n M.val)

/-- **The sheafified sectionwise exterior power commutes with pushforward.** -/
noncomputable def sectionwiseExteriorPowerPushforwardIso :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj
        ((_root_.SheafOfModules.sectionwiseExteriorAlgebra Jt (𝟙 Osharp.obj) M.val).piece
          (n : ℤ)) ≅
      (_root_.SheafOfModules.sectionwiseExteriorAlgebra Js
        (𝟙 (pushforwardCommRingSheaf Js G (Osharp := Osharp)).obj)
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M).val).piece (n : ℤ) :=
  (pushforwardSheafifyIso.{w} Js G (toRingCat Jt Osharp) (extPow n M.val)).symm ≪≫
    (sheafification.{w} (𝟙 (pushforwardRingSheaf Js G (toRingCat Jt Osharp)).obj)).mapIso
      (extPowPushforwardIso G n M.val)

section Symmetric

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra B gen')

/-- **Pushforward along a continuous and cocontinuous functor of sites commutes with the
symmetric power**, for an arbitrary symmetric algebra `A` of `M` on the target site and an
arbitrary symmetric algebra `B` of its pushforward on the source site.

Section 17.21 pins the symmetric algebra only up to canonical isomorphism, so a statement about
"the" symmetric power has to quantify over the choices; that is what makes `A`, `B` and their
universal properties arguments. `B` may always be taken to be the source site's own sectionwise
symmetric algebra, whose universal property is
`SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val`. -/
noncomputable def symmetricPowerPushforwardIso :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj (A.piece (n : ℤ)) ≅
      B.piece (n : ℤ) :=
  (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).mapIso
      (_root_.SheafOfModules.symmetricPieceIso M A gen hA (n : ℤ)).symm ≪≫
    sectionwiseSymmetricPowerPushforwardIso Js G M n ≪≫
      _root_.SheafOfModules.symmetricPieceIso (J := Js)
        (Osharp := pushforwardCommRingSheaf Js G (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M) B gen' hB (n : ℤ)

end Symmetric

section Exterior

variable (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (toRingCat Jt Osharp))
  (gen : M ⟶ A.piece 1)
  (hA : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A gen)
  (B : _root_.SheafOfModules.GradedAlgebra.{w, w}
    (toRingCat Js (pushforwardCommRingSheaf Js G (Osharp := Osharp))))
  (gen' : (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M ⟶ B.piece 1)
  (hB : _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra B gen')

/-- **Pushforward along a continuous and cocontinuous functor of sites commutes with the
exterior power**, for an arbitrary pair of exterior algebras. -/
noncomputable def exteriorPowerPushforwardIso :
    (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj (A.piece (n : ℤ)) ≅
      B.piece (n : ℤ) :=
  (sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).mapIso
      (_root_.SheafOfModules.exteriorPieceIso M A gen hA (n : ℤ)).symm ≪≫
    sectionwiseExteriorPowerPushforwardIso Js G M n ≪≫
      _root_.SheafOfModules.exteriorPieceIso (J := Js)
        (Osharp := pushforwardCommRingSheaf Js G (Osharp := Osharp))
        ((sheafPushforwardFunctor.{w} Js G (toRingCat Jt Osharp)).obj M) B gen' hB (n : ℤ)

end Exterior

end Stacks.SheafOfModules

/-! ### Presentations of a free sheaf of modules -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The identity exhibits an object as the cokernel of the zero morphism into it. -/
noncomputable def isColimitCokernelCoforkId {D : Type u'} [Category.{v'} D]
    [Limits.HasZeroMorphisms D] {A B : D} :
    IsColimit (CokernelCofork.ofπ (f := (0 : A ⟶ B)) (𝟙 B) (by simp)) :=
  Cofork.IsColimit.mk _ (fun s => Cofork.π s) (fun s => by simp)
    (fun s m hm => by simpa using hm)

/-- Transport a presentation along an isomorphism of sheaves of modules.

This is `SheafOfModules.Presentation.ofIsIso` packaged to take an isomorphism rather than a
morphism with an `IsIso` instance; stating it with binders literally `SheafOfModules.{w} R`
means the instance is resolved here rather than at the application site, where typeclass
resolution cannot see through the comparison isomorphisms of this file. -/
noncomputable def presentationOfIso {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation :=
  _root_.SheafOfModules.Presentation.ofIsIso e.hom P

/-- **A free sheaf of modules has a presentation**, with its index type as generators and no
relations. -/
noncomputable def presentationFree (σ : Type w) :
    (_root_.SheafOfModules.free (R := R) σ).Presentation :=
  _root_.SheafOfModules.presentationOfIsCokernelFree (ι := PEmpty.{w + 1}) 0 (𝟙 _) (by simp)
    isColimitCokernelCoforkId

/-- **The structure sheaf has a presentation**: it is the free sheaf of modules of rank one. -/
noncomputable def presentationUnit : (_root_.SheafOfModules.unit R).Presentation :=
  presentationOfIso
    (Limits.coproductUniqueIso (fun _ : PUnit.{w + 1} => _root_.SheafOfModules.unit R))
    (presentationFree PUnit.{w + 1})

end Stacks.SheafOfModules

/-! ### Tag 01CL -/

namespace Stacks.SheafOfModules

open Stacks.SheafOfModules.PushforwardSheafification

/-! #### Every power of a presented module sheaf on a ringed space is presented -/

/-- The target of an exact short complex of free sheaves of modules, with epimorphic second map,
has a presentation. -/
private theorem nonempty_presentation_of_exact_free {Y : RingedSpace.{u, u}}
    {T : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing Y))} {I₁ I₂ : Type u}
    (hex : T.Exact) (hepi : Epi T.g) (e₁ : T.X₁ ≅ _root_.SheafOfModules.free I₁)
    (e₂ : T.X₂ ≅ _root_.SheafOfModules.free I₂) : Nonempty T.X₃.Presentation := by
  have := hepi
  exact ⟨_root_.SheafOfModules.presentationOfIsCokernelFree
    (e₁.inv ≫ T.f ≫ e₂.hom) (e₂.inv ≫ T.g) (by simp [T.zero])
    (IsCokernel.ofIso _ hex.gIsCokernel _ e₁ e₂ (Iso.refl _) (by simp) (by simp))⟩

/-- **From a presentation of `M` on a ringed space, every symmetric power of `M` has a
presentation.** This is Tag 01CJ for the degrees at least one, through
`Stacks.SheafOfModules.exists_free_symmetricPower_presentation`, together with the degree-zero
identification of the symmetric algebra with the structure sheaf. -/
theorem nonempty_presentation_symmetricPower {Y : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing Y)} (q : M.Presentation)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Y.carrier) M) (n : ℕ) :
    Nonempty (A.symmetricPower n).Presentation := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨presentationOfIso
      ((_root_.SheafOfModules.symmetricPieceIso M A.symmetric A.symmetricGenerator
        A.symmetric_isSymmetricAlgebra 0).symm ≪≫
        _root_.SheafOfModules.sectionwiseSymmetricPieceZeroIso
          (Opens.grothendieckTopology Y.carrier) (𝟙 Y.sheaf.obj) M.val).symm presentationUnit⟩
  · obtain ⟨T, ι₂, ι₁, -, -, -, -, hT₃, hex, hepi, ⟨e₁⟩, ⟨e₂⟩⟩ :=
      exists_free_symmetricPower_presentation
        (S := ShortComplex.mk q.relationsHom q.generators.π q.relationsHom_comp_π)
        (ShortComplex.exact_of_g_is_cokernel _ q.isColimitRelationsHom) q.generators.epi
        (_root_.SheafOfModules.ringedSpaceAlgebras Y _) A
        q.relations.I q.generators.I (Iso.refl _) (Iso.refl _) n hn
    rw [← hT₃]
    exact nonempty_presentation_of_exact_free hex hepi e₁ e₂

/-- **From a presentation of `M` on a ringed space, every exterior power of `M` has a
presentation.** The exterior half of
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower`; here the degree-zero
identification is the field
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPieceZeroIsoUnit` of the bundle. -/
theorem nonempty_presentation_exteriorPower {Y : RingedSpace.{u, u}}
    {M : _root_.SheafOfModules.{u} (structureSheafRing Y)} (q : M.Presentation)
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Y.carrier) M) (n : ℕ) :
    Nonempty (A.exteriorPower n).Presentation := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨presentationOfIso A.exteriorPieceZeroIsoUnit.symm presentationUnit⟩
  · obtain ⟨T, ι₂, ι₁, -, -, -, -, hT₃, hex, hepi, ⟨e₁⟩, ⟨e₂⟩⟩ :=
      exists_free_exteriorPower_presentation
        (S := ShortComplex.mk q.relationsHom q.generators.π q.relationsHom_comp_π)
        (ShortComplex.exact_of_g_is_cokernel _ q.isColimitRelationsHom) q.generators.epi
        (_root_.SheafOfModules.ringedSpaceAlgebras Y _) A
        q.relations.I q.generators.I (Iso.refl _) (Iso.refl _) n hn
    rw [← hT₃]
    exact nonempty_presentation_of_exact_free hex hepi e₁ e₂

/-! #### The open subspace, and transport to the slice site -/

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- The site functor `Opens ↥U ⥤ Over U` of Mathlib's `TopologicalSpace.Opens.overEquivalence`.
It is a dense subsite in both directions, hence continuous and cocontinuous. -/
noncomputable abbrev openSubspaceSiteFunctor : Opens ↥U ⥤ Over U := U.overEquivalence.inverse

/-- The structure sheaf of the open subspace `U`: the pushforward of the slice structure sheaf
along `Stacks.SheafOfModules.openSubspaceSiteFunctor`. -/
noncomputable abbrev openSubspaceStructureSheaf :
    Sheaf (Opens.grothendieckTopology ↥U) CommRingCat.{u} :=
  pushforwardCommRingSheaf (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
    (Osharp := X.sheaf.over U)

/-- **An open of a ringed space, as a ringed space.** This is `X.restrict U.isOpenEmbedding`,
recorded as a reducible abbreviation; see `Stacks.SheafOfModules.openSubspace_eq_restrict` and
the implementation notes. -/
noncomputable abbrev openSubspace : RingedSpace.{u, u} where
  carrier := TopCat.of ↥U
  presheaf := (openSubspaceStructureSheaf U).obj
  IsSheaf := (openSubspaceStructureSheaf U).property

/-- `Stacks.SheafOfModules.openSubspace` introduces no new notion of open subspace: it is
Mathlib's restriction of a sheafed space along the inclusion of an open. -/
theorem openSubspace_eq_restrict : openSubspace U = X.restrict U.isOpenEmbedding := rfl

/-- The equivalence between sheaves of modules on the slice site over `U` and sheaves of modules
on the open subspace `U`, which is Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver`. Its forward functor is the pushforward along
`Stacks.SheafOfModules.openSubspaceSiteFunctor` with no change of scalars. -/
noncomputable abbrev openSubspaceEquiv :
    _root_.SheafOfModules.{u} ((structureSheafRing X).over U) ≌
      _root_.SheafOfModules.{u} (structureSheafRing (openSubspace U)) :=
  U.sheafOfModulesEquivOver (structureSheafRing X)

/-- The forward functor of `Stacks.SheafOfModules.openSubspaceEquiv` is the pushforward along
the site functor, so the comparison isomorphisms of this file apply to it. -/
theorem openSubspaceEquiv_functor : (openSubspaceEquiv U).functor =
    sheafPushforwardFunctor.{u} (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
      ((structureSheafRing X).over U) := rfl

/-- Transport a presentation from the open subspace back to the slice site, along the
equivalence and an identification of the forward image. The inverse of the equivalence preserves
colimits because it is a left adjoint, and
`TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit` says it takes the structure sheaf of
the open subspace to the structure sheaf of the slice site; those are the two hypotheses of
`SheafOfModules.Presentation.map`. -/
noncomputable def presentationOfOpenSubspaceIso
    {M : _root_.SheafOfModules.{u} ((structureSheafRing X).over U)}
    {N : _root_.SheafOfModules.{u} (structureSheafRing (openSubspace U))}
    (e : (openSubspaceEquiv U).functor.obj M ≅ N) (P : N.Presentation) : M.Presentation :=
  presentationOfIso
    ((openSubspaceEquiv U).unitIso.app M ≪≫ (openSubspaceEquiv U).inverse.mapIso e).symm
    (P.map (openSubspaceEquiv U).inverse
      (U.sheafOfModulesEquivOverInverseUnit (structureSheafRing X)).symm)

variable (F : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- The chosen package of algebras of the restriction of `F` to the open subspace `U`. -/
noncomputable abbrev openSubspaceAlgebras :
    _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology (openSubspace U).carrier)
      ((openSubspaceEquiv U).functor.obj (F.over U)) :=
  _root_.SheafOfModules.ringedSpaceAlgebras (openSubspace U)
    ((openSubspaceEquiv U).functor.obj (F.over U))

variable (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **A presentation of `F` over an open presents every symmetric power of `F` over that same
open.** The uniformity in `n` — one open presenting every degree — is the content of Tag 01CL,
and this is where it is established: the open is the one over which `F` is presented, and no
further shrinking happens in any degree. -/
theorem nonempty_presentation_symmetricPower_over
    (p : (F.over U).Presentation) (n : ℕ) :
    Nonempty ((A.symmetricPower n).over U).Presentation := by
  have hB := _root_.SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val
    (J := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U) (F.over U)
  obtain ⟨q⟩ := nonempty_presentation_symmetricPower
    (p.map (openSubspaceEquiv U).functor
      (U.sheafOfModulesEquivOverUnit (structureSheafRing X)).symm)
    (openSubspaceAlgebras U F) n
  exact ⟨presentationOfIso
    (symmetricPowerOverIso F U n A.symmetric A.symmetricGenerator
      A.symmetric_isSymmetricAlgebra _ _ hB).symm
    (presentationOfOpenSubspaceIso U (symmetricPowerPushforwardIso
      (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
      (Jt := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U)
      (F.over U) n _ _ hB (openSubspaceAlgebras U F).symmetric
      (openSubspaceAlgebras U F).symmetricGenerator
      (openSubspaceAlgebras U F).symmetric_isSymmetricAlgebra) q)⟩

/-- **A presentation of `F` over an open presents every exterior power of `F` over that same
open.** -/
theorem nonempty_presentation_exteriorPower_over
    (p : (F.over U).Presentation) (n : ℕ) :
    Nonempty ((A.exteriorPower n).over U).Presentation := by
  have hB := _root_.SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra_val
    (J := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U) (F.over U)
  obtain ⟨q⟩ := nonempty_presentation_exteriorPower
    (p.map (openSubspaceEquiv U).functor
      (U.sheafOfModulesEquivOverUnit (structureSheafRing X)).symm)
    (openSubspaceAlgebras U F) n
  exact ⟨presentationOfIso
    (exteriorPowerOverIso F U n A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra _ _ hB).symm
    (presentationOfOpenSubspaceIso U (exteriorPowerPushforwardIso
      (Opens.grothendieckTopology ↥U) (openSubspaceSiteFunctor U)
      (Jt := (Opens.grothendieckTopology X.carrier).over U) (Osharp := X.sheaf.over U)
      (F.over U) n _ _ hB (openSubspaceAlgebras U F).exterior
      (openSubspaceAlgebras U F).exteriorGenerator
      (openSubspaceAlgebras U F).exterior_isExteriorAlgebra) q)⟩

/-! #### The conclusions -/

section Conclusions

variable {X : RingedSpace.{u, u}} (F : _root_.SheafOfModules.{u} (structureSheafRing X))
  [F.IsQuasicoherent]
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **Each symmetric power of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** A presentation of the module over an open presents every symmetric power of it
over that same open, by `Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over`, so the
covering family which presents the module presents the symmetric power too. -/
@[stacks 01CK "symmetric powers of a quasi-coherent module"]
theorem isQuasicoherent_symmetricPower (n : ℕ) : (A.symmetricPower n).IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  have q : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} (A.symmetricPower n) :=
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i =>
        (nonempty_presentation_symmetricPower_over (c.X i) F A (c.presentation i) n).some }
  exact q.isQuasicoherent

/-- **The symmetric algebra of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** The covering family is the one that presents `F`; no degree needs a smaller
open, because
`Stacks.SheafOfModules.nonempty_presentation_symmetricPower_over` presents every degree over
that same open. -/
@[stacks 01CL "the symmetric algebra of a quasi-coherent module sheaf is quasi-coherent"]
theorem isQuasicoherent_symmetricAlgebraSheaf_of_isQuasicoherent :
    A.symmetricAlgebraSheaf.IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  exact A.isQuasicoherent_symmetricAlgebraSheaf c.X c.coversTop
    fun i n => (nonempty_presentation_symmetricPower_over (c.X i) F A (c.presentation i) n).some

/-- **The exterior algebra of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** -/
@[stacks 01CL "the exterior algebra of a quasi-coherent module sheaf is quasi-coherent"]
theorem isQuasicoherent_exteriorAlgebraSheaf_of_isQuasicoherent :
    A.exteriorAlgebraSheaf.IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  exact A.isQuasicoherent_exteriorAlgebraSheaf c.X c.coversTop
    fun i n => (nonempty_presentation_exteriorPower_over (c.X i) F A (c.presentation i) n).some

end Conclusions

end Stacks.SheafOfModules

end
