module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoherence
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of sheaves of modules to a slice site is a monoidal functor

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and let `U : C`. Restriction of
sheaves of `𝒪`-modules to the slice site `(Over U, J.over U)` is Mathlib's
`SheafOfModules.overFunctor`, which is `SheafOfModules.pushforward (𝟙 _)` along `Over.forget U`.
This file equips it with a `CategoryTheory.Functor.Monoidal` structure for the monoidal
structure of Tag 01CA on each side — `Stacks.SheafOfModules.Strict.monoidalCategory`, whose
tensor product *is* the tensor product sheaf
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on the nose.

That instance is one of the two hypotheses
`CategoryTheory.ExactPairing.ofJointlyFaithful` of
`StacksFrontier.CategoryTheory.Monoidal.RigidJointlyFaithful` consumes about the family of
restrictions, and it is a named blocker of
[Stacks, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV): the proof there is local on a
covering `{V i → U}`, and "local" is the statement that the restrictions `-|_{V i}` form a
jointly faithful family of **monoidal** functors. The second hypothesis, joint faithfulness
itself, is `overFunctor_map_injective` below; it was equally unavailable, so this file discharges
both. What Tag 0FNV still needs after this file is the local exact pairing, which is a statement
about the canonical coevaluation and not about restriction; see the implementation notes.

The argument has two halves, and neither reproves a monoidal axiom.

* **At the presheaf level it is free.** Mathlib's
  `PresheafOfModules.pushforward₀OfCommRingCat` — precomposition with `(Over.forget U).op`, with
  no change of scalars — carries a `Functor.Monoidal` instance, whose tensorator is objectwise
  the identity. This is the functor `StacksDraft.Algebra.Category.ModuleCat.Sheaf
  .InvertibleSummandSheafify` already uses, for the same reason.
* **The lift to sheaves is one application of
  `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`,** following the pattern of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf`: the monoidal structure
  on sheaves of modules is the localization of the objectwise one on presheaves of modules along
  sheafification, so a functor out of it is monoidal as soon as its composite with sheafification
  is. The missing input, built here, is the `CategoryTheory.Localization.Lifting` isomorphism
  "sheafification commutes with restriction to a slice site",
  `sheafifyFunctor 𝒪 ⋙ overFunctor ≅ sliceFunctor ⋙ sliceSheafify`. Mathlib's
  `SheafOfModules.sheafificationCompPullback` is the analogous statement for the **pullback**;
  there is none for restriction to a slice site, and
  `Stacks.TensorCoherence.tensorSheafOverIso` is only its tensor-specific instance.

Finally the localized structure is transported to the strict one of Tag 01CA. That needs the
identity functor to be monoidal in *both* directions between the two spellings;
`CategoryTheory.Monoidal.induced` supplies only one, and the other is
`CategoryTheory.Equivalence.inverseMonoidal` applied to the identity equivalence. This is the
step recorded as "considered and not done" in the implementation notes of
`...PullbackMonoidalSheaf`.

## Main definitions

* `Stacks.SheafOfModules.SliceRestriction.sliceFunctor` and `sliceSheafify`: restriction of
  presheaves of modules to the slice site, and sheafification there.
* `Stacks.SheafOfModules.SliceRestriction.overFunctor`: Mathlib's `SheafOfModules.overFunctor`,
  retyped so that its target ring sheaf is spelled
    `Stacks.SheafOfModules.TensorSheafification.structureSheaf`; see the
  implementation notes for why the retyping is forced.
* `Stacks.SheafOfModules.SliceRestriction.sliceUnit` and `sliceComparison`: the sheafification
  unit restricted to the slice site, and the morphism adjoint to it.
* `Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidal` and `localizedEquivalence`: the
  identity functor out of `CategoryTheory.Monoidal.LocalizedMonoidal`, and the identity
  equivalence it belongs to.

## Main results

* `Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`: **restriction to the
  members of a family of objects covering the final object is a jointly faithful family of
  functors.** This is the *other* hypothesis of
  `CategoryTheory.ExactPairing.ofJointlyFaithful`, and it
  was likewise not available: the only related library results are the sectionwise statements
  `Stacks.SheafOfModules.eq_zero_of_locally_zero'` and
    `Stacks.Injectives.DualEvaluation.hom_zero_of_evaluation`,
  neither of which is about slice restriction along a covering family.
* `Stacks.SheafOfModules.SliceRestriction.sliceSheafifyIso`: **sheafification of presheaves of
  modules commutes with restriction to a slice site.** The restricted sheafification unit is
  still locally bijective, because `Over.forget U` is cocontinuous, so it exhibits the
  restriction of `P^#` as the sheafification of the restriction of `P`.
* `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalLocalized`: restriction is monoidal
  for the localized monoidal structure `Stacks.SheafOfModules.monoidalCategory`.
* `Stacks.SheafOfModules.SliceRestriction.fromLocalizedMonoidalMonoidal`: **the identity functor
  from the localized spelling to sheaves of modules is monoidal**, i.e. the comparison of
  `Stacks.SheafOfModules.monoidalCategory` with
  `Stacks.SheafOfModules.Strict.monoidalCategory` is monoidal in the direction
  `CategoryTheory.Monoidal.induced` does not give.
* `Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal` and
  `overFunctorStrictMonoidal`: **restriction of sheaves of modules to a slice site is a monoidal
  functor for the monoidal structure of Tag 01CA.** The second is the first with both monoidal
  structures named explicitly, stated outside the scope of any local instance, so that it is a
  check and not a restatement.
* `Stacks.SheafOfModules.SliceRestriction.tensorSheafOver`: **the tensor product sheaf of Tag
  01CA commutes with restriction to a slice site**, `ℱ|_U ⊗ 𝒢|_U ≅ (ℱ ⊗ 𝒢)|_U`. This is the
  tensorator of the previous result, which is a comparison of tensor product sheaves on the nose
  because the tensor product of the strict structure is
    `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`.

## Implementation notes

**What is forced and what is chosen.** Nothing here is a choice of monoidal structure: both
monoidal structures used already exist (`PresheafOfModules.monoidalCategory` at the presheaf
level, `Stacks.SheafOfModules.monoidalCategory` and
`Stacks.SheafOfModules.Strict.monoidalCategory` at the sheaf level) and the functor is Mathlib's
`SheafOfModules.overFunctor`. What is *chosen* is the spelling discipline described next, and the
construction of the lifting isomorphism: it is built here as the morphism **adjoint to the
restricted sheafification unit**, shown to be an isomorphism because that unit is still locally
bijective. Mathlib proves the pullback analogue `SheafOfModules.sheafificationCompPullback` by
`CategoryTheory.Adjunction.leftAdjointUniq` instead; that route is not ruled out here —
restriction to a slice site is a left adjoint as well as a right one
(`Stacks.SheafOfModules.isLeftAdjoint_overFunctor`, from Mathlib's
`SheafOfModules.overPushforwardOverAdj`) — but it would require identifying the two composite
right adjoints, whereas the route taken reuses the local-bijectivity transfer that
`Over.forget U`'s cocontinuity already gives.

**Why the retyping is forced.** `Stacks.SheafOfModules.Strict.monoidalCategory` and its
companions are indexed by a presheaf of commutative rings together with a sheaf condition, and
mention the sheaf of rings in the spelling
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`. Mathlib's
`SheafOfModules.overFunctor R U` lands in `SheafOfModules (R.over U)` instead. The two ring
sheaves are equal by `rfl` (`sliceStructureSheaf_eq`) but not syntactically, and the
discrimination-tree key of an instance built at one spelling does not match a goal written in the
other: with the monoidal structure a local instance at the `structureSheaf` spelling, the goal
`MonoidalCategory (SheafOfModules ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).over U))` fails to
synthesize. Naming the functor once, with its target ascribed at the `structureSheaf` spelling,
and letting the defeq check of `:=` cross the boundary, is what makes the chain elaborate. This
is the discipline of `...PullbackMonoidalSheaf` and `...PullbackAlgebraIso`; no limit is raised
anywhere.

For the same reason `overFunctorLocalized` and `fromLocalizedMonoidal` carry **ascribed** types
naming `CategoryTheory.Monoidal.LocalizedMonoidal`. That type is a plain definition whose body is
the category of sheaves of modules, so it is definitionally equal to it but nominally distinct,
which is exactly what keeps the localized and the strict monoidal structures from clashing during
the transport.

**Where the structure maps are, and are not, pinned.** `tensorSheafOver` *is* the tensorator, so
the comparison of tensor products is identified; what is not computed here is its action on local
sections. It is not proved here because the snake identities of Tag 0FNV are statements about
morphisms, not sections, and do not need it. Nothing else consumes it either: every
occurrence of `tensorSheafOver` outside its own definition is prose.

**What the sectionwise formula actually needs.** A sectionwise formula of the kind obtained from
`Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap`
and the Tag 05NA comparisons, in the manner of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections`, is available, but for a
*different* comparison.
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafOverSlice.lean`) is
`ℱ|_{C'} ⊗ 𝒢|_{C'} ≅ (ℱ ⊗ 𝒢)|_{C'}` for restriction along any continuous cocontinuous functor of
sites — `overTensorSheafIso` is its slice instance, the same statement as `tensorSheafOver` — and
it is *not* built as a tensorator: it is `iso_of_locallyBijective` applied to the presheaf-level
tensorator, so `whiskerTensorSheafIso_hom` pins it on the sheafification unit of the objectwise
tensor product, which is a formula on local pure tensors. So the sectionwise formula for the
comparison **exists**; what is missing is the identification
`tensorSheafOver = overTensorSheafIso`, i.e. that the tensorator is that comparison.

**Where that identification can be stated.** It can be stated outside
`TensorSheafOverSlice.lean`, without recognising `whiskerTensorSheafIso` as an
`iso_of_locallyBijective` by a defeq check: the equation
`overTensorSheafIso 𝒪 h𝒪 U A B = (tensorSheafOver 𝒪 h𝒪 U A B).symm`
elaborates in a module that merely imports this file and `TensorSheafOverSlice.lean` — the two
types agree with no coercion — and `whiskerTensorSheafIso_hom` together with
`iso_ext_of_locallyBijective` reduce it there, with no option override, to the single equation

`whiskerTensorUnit ≫ (tensorSheafOver 𝒪 h𝒪 U A B).inv.val =
  (whiskerPresheafTensorIso _).hom ≫ whiskerTensorUnit'`

on the restricted sheafification unit. No defeq through the monoidal instances is involved, the
only care needed being that the four local-bijectivity facts are passed explicitly.

**What blocks that one equation is the localization tensorator, and it is the same gap
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingComparison.lean` already names.**
The left-hand side is the oplax tensorator of `overFunctorMonoidal`, and `Strict` transport sends
it through `Stacks.SheafOfModules.tensorObjIso`, whose second factor is
`Stacks.SheafOfModules.sheafifyTensorIso`, i.e. `CategoryTheory.Localization.Monoidal.μ` — a
component of a `CategoryTheory.Localization.Lifting₂.iso`, produced by the universal property,
with no formula on sections and none on the sheafification unit. The `ε` technique does not
transfer: `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε` reduces `ε` to `η` of
the localization functor, which is the *hom of the chosen unit comparison* and here `Iso.refl _`,
whereas `functorMonoidalOfComp_μ` reduces `μ` to a `δ` that is chosen by nobody.

What this file adds to that analysis is that for `tensorSheafOver` the opaque factor occurs
**twice with opposite orientation** — once as `sheafifyTensorIso` inside the `tensorObjIso`
conjugation of `Strict.monoidalCategoryStruct`, and once as the `δ` of
`functorMonoidalOfComp_μ` — and likewise for the slice site, so a cancellation is available in
principle and the surviving data would be `sliceSheafifyIso` together with the presheaf-level
tensorator, both explicit. That is a route and not a theorem; carrying it out needs the `μ`
formulas of `CategoryTheory.Monoidal.fromInducedCoreMonoidal` (its `μIso` is the chosen
`InducingFunctorData.μIso`) and of `CategoryTheory.Equivalence.inverseMonoidal` (through
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal_μ`), plus transport of
`functorMonoidalOfComp_μ` off the objects `L.obj P` by naturality.

**It would not serve the twisted-section development.** `tensorSheafOver`
is the tensorator of `Stacks.SheafOfModules.Strict.monoidalCategory`, for which
`Strict.tensorObj_eq` makes `A ⊗ B` be
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 A B` on the nose. The
twisted-section machinery is stated over `Stacks.SheafInternalHom.monoidalCategory` — the
*localized* structure, `CategoryTheory.Monoidal.LocalizedMonoidal` — and for that structure the
same `rfl` fails: `A ⊗ B` is the value of a `CategoryTheory.Localization.lift₂` and is not
definitionally a tensor product sheaf. The bridge between the two is `tensorObjIso` again, so an
identification of the `Strict` tensorator with `overTensorSheafIso` leaves the opaque factor
exactly where it was for those consumers.

**Nothing in this file is tagged.** The content of Tag 0FNV is the two snake identities for the
canonical coevaluation and evaluation, and this file proves neither; what it removes are two of
the three hypotheses that blocked them. (Tag 0FNV itself is carried elsewhere — by `dualSheaf`
and `evaluation` in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom`, and by four
declarations in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualEndomorphism`.)

The third hypothesis was an exact pairing of `ℱ|_V` with `ℱ^∨|_V` whose evaluation and
coevaluation are the restrictions of the *canonical* ones. A finite-free retract gives an exact
pairing of `ℱ|_V` with the dual built from the retract (`CategoryTheory.hasRightDualOfRetract`,
Tag 0FFU), and identifying the two needed a local formula for the canonical coevaluation.

**That formula is no longer unproved**, as the sentence here previously said: it is
`Stacks.SheafOfModules.coevaluation_app_one_eq_sum_of_dualBasis` in `TensorDualEndomorphism`,
which evaluates the canonical coevaluation at `1` as `∑ i, eᵢ ⊗ λᵢ` for a finite dual basis.
What is still owed for the identification is `FiniteDualBasis.ofRetract`, turning a finite-free
retract into a dual basis; that is blocked on the `restrictScalars` surgery recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections`, because the scalar *action*
cannot be respelled between the slice and base sites even though elements can.

**Hypotheses.** Beyond the site and the sheaf of commutative rings, the hypotheses are
`J.WEqualsLocallyBijective AddCommGrpCat` and `HasWeakSheafify J AddCommGrpCat` on `J` and on
`J.over U`, which is what the two sheafification functors need. No
`GrothendieckTopology.HasSheafCompose` instance is required, on either topology — the monoidal
structures of `...Monoidal` and `...MonoidalStrict` do not depend on one, and neither does the
localizing class being monoidal.

**Universes.** The site `C : Type u` with `Category.{v} C` is arbitrary and `u`, `v` are
independent. The ring sheaf and the modules share the single universe `w`; that is forced, not
chosen, by Mathlib's monoidal structure on presheaves of modules, which is declared only for
`PresheafOfModules.{u}` over a ring presheaf of the shape `R ⋙ forget₂ CommRingCat RingCat` with
`R : Cᵒᵖ ⥤ CommRingCat.{u}`. Nothing is narrowed relative to the imported files. Note that the
slice site `Over U` lives in `Type (max u v)`, so the restricted statements are at site
universes `(max u v, v)` with the module universe `w` unchanged; this is a change of site, not a
narrowing of a universe parameter.

## References

* [The Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [The Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB) — the localized
  site `C/U`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization

universe v u w

namespace Stacks.SheafOfModules.SliceRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  (U : C)

/-- The structure presheaf restricted to the slice site over `U`. -/
abbrev sliceRingPresheaf : (Over U)ᵒᵖ ⥤ CommRingCat.{w} := (Over.forget U).op ⋙ 𝒪

/-- Restriction of presheaves of modules to the slice site over `U`, spelled as
`PresheafOfModules.pushforward₀OfCommRingCat` so that Mathlib's monoidal structure on it is
available. -/
noncomputable abbrev sliceFunctor :
    PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪) ⥤
      PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (sliceRingPresheaf 𝒪 U)) :=
  PresheafOfModules.pushforward₀OfCommRingCat.{w} (Over.forget U) 𝒪

section JointlyFaithful

variable {R : Sheaf J RingCat.{w}} {ι : Type*} {V : ι → C}

/-- **Restriction to the members of a family of objects which covers the final object is a
jointly faithful family of functors.** Two morphisms of sheaves of modules whose restrictions
to every `V i` agree already agree, because the underlying presheaf of the target is separated
and every object of the site is covered by objects admitting a morphism to some `V i`.

Together with `overFunctorMonoidal` this is what
`CategoryTheory.ExactPairing.ofJointlyFaithful` asks of the family of restrictions: it is the
formal content of "this is a local question". It is the `map_injective` field of
`CategoryTheory.JointlyFaithful` for the family `fun i => SheafOfModules.overFunctor R (V i)`. -/
theorem overFunctor_map_injective (hV : J.CoversTop V)
    {A B : SheafOfModules.{w} R} (f g : A ⟶ B)
    (h : ∀ i, (SheafOfModules.overFunctor.{w} R (V i)).map f =
      (SheafOfModules.overFunctor.{w} R (V i)).map g) :
    f = g := by
  have key : ∀ (i : ι) (W : C) (_ : W ⟶ V i),
      ((PresheafOfModules.toPresheaf R.obj).map f.val).app (Opposite.op W) =
        ((PresheafOfModules.toPresheaf R.obj).map g.val).app (Opposite.op W) := fun i W b =>
    congrArg (fun t : A.over (V i) ⟶ B.over (V i) =>
      ((PresheafOfModules.toPresheaf (R.over (V i)).obj).map t.val).app
        (Opposite.op (Over.mk b))) (h i)
  refine (SheafOfModules.forget R).map_injective
    ((PresheafOfModules.toPresheaf R.obj).map_injective (NatTrans.ext (funext fun X => ?_)))
  refine B.isSheaf.hom_ext (hV.cover X.unop) _ _ ?_
  rintro ⟨W, a, ⟨i, ⟨b⟩⟩⟩
  exact (((PresheafOfModules.toPresheaf R.obj).map f.val).naturality a.op).symm.trans
    ((congrArg (fun t => ((PresheafOfModules.toPresheaf R.obj).obj A.val).map a.op ≫ t)
      (key i W b)).trans
        (((PresheafOfModules.toPresheaf R.obj).map g.val).naturality a.op))

end JointlyFaithful

include h𝒪

/-- The restriction of the structure presheaf to the slice site is a sheaf for the induced
topology. -/
theorem isSheaf_sliceRingPresheaf :
    Presheaf.IsSheaf (J.over U)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (sliceRingPresheaf 𝒪 U)) :=
  ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U).property

/-- The structure sheaf of the slice site. -/
noncomputable abbrev sliceStructureSheaf : Sheaf (J.over U) RingCat.{w} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)

/-- The two spellings of the slice structure sheaf agree on the nose. -/
theorem sliceStructureSheaf_eq :
    sliceStructureSheaf 𝒪 h𝒪 U = (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).over U :=
  rfl

/-- Restriction of sheaves of modules to the slice site over `U`. -/
noncomputable abbrev overFunctor :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
      SheafOfModules.{w} (sliceStructureSheaf 𝒪 h𝒪 U) :=
  SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) U

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- Sheafification of presheaves of modules on the slice site. -/
noncomputable abbrev sliceSheafify :
    PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (sliceRingPresheaf 𝒪 U)) ⥤
      SheafOfModules.{w} (sliceStructureSheaf 𝒪 h𝒪 U) :=
  Stacks.SheafOfModules.sheafifyFunctor (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)

/-- The sheafification unit of `P`, restricted to the slice site over `U`, read as a morphism
into the underlying presheaf of modules of the restriction of `P^#`. -/
noncomputable def sliceUnit (P : PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)) :
    (sliceFunctor 𝒪 U).obj P ⟶
      (SheafOfModules.forget (sliceStructureSheaf 𝒪 h𝒪 U) ⋙
          PresheafOfModules.restrictScalars (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)).obj
        ((overFunctor 𝒪 h𝒪 U).obj ((sheafifyFunctor 𝒪 h𝒪).obj P)) :=
  (sliceFunctor 𝒪 U).map (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P)

/-- `sliceUnit` is natural in `P`. -/
noncomputable def sliceUnitNatTrans :
    sliceFunctor 𝒪 U ⟶
      (sheafifyFunctor 𝒪 h𝒪 ⋙ overFunctor 𝒪 h𝒪 U) ⋙
        (SheafOfModules.forget (sliceStructureSheaf 𝒪 h𝒪 U) ⋙
          PresheafOfModules.restrictScalars (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)) where
  app P := sliceUnit 𝒪 h𝒪 U P
  naturality P Q g :=
    ((sliceFunctor 𝒪 U).map_comp g (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
      Q)).symm.trans
      (((sliceFunctor 𝒪 U).congr_map
        ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).unit.naturality
          g)).trans
          ((sliceFunctor 𝒪 U).map_comp (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
            P) _))

/-- The comparison morphism: the sheafification on the slice site of the restriction of `P`
maps to the restriction of the sheafification of `P`. -/
noncomputable def sliceComparison :
    sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U ⟶
      sheafifyFunctor 𝒪 h𝒪 ⋙ overFunctor 𝒪 h𝒪 U :=
  Functor.whiskerRight (sliceUnitNatTrans 𝒪 h𝒪 U) (sliceSheafify 𝒪 h𝒪 U) ≫
    Functor.whiskerLeft (sheafifyFunctor 𝒪 h𝒪 ⋙ overFunctor 𝒪 h𝒪 U)
      (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction (sliceRingPresheaf 𝒪 U)
        (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)).counit

/-- The component of `sliceComparison` at `P` is the morphism adjoint to the restricted
sheafification unit. -/
theorem sliceComparison_app (P : PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)) :
    (sliceComparison 𝒪 h𝒪 U).app P =
      (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)).symm (sliceUnit 𝒪 h𝒪 U P) := by
  have key : (sliceComparison 𝒪 h𝒪 U).app P =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)).homEquiv ((sliceFunctor 𝒪 U).obj P)
        ((overFunctor 𝒪 h𝒪 U).obj ((sheafifyFunctor 𝒪 h𝒪).obj P))).symm
          (sliceUnit 𝒪 h𝒪 U P) := rfl
  have he : (PresheafOfModules.sheafificationAdjunction
        (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)).homEquiv ((sliceFunctor 𝒪 U).obj P)
      ((overFunctor 𝒪 h𝒪 U).obj ((sheafifyFunctor 𝒪 h𝒪).obj P)) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj) :=
    Equiv.coe_fn_injective rfl
  rw [key, he]

omit [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The restricted sheafification unit is locally injective: `Over.forget U` is cocontinuous,
so local injectivity restricts to the slice site. -/
theorem isLocallyInjective_sliceUnit
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
      :
    Presheaf.IsLocallyInjective (J.over U)
      ((PresheafOfModules.toPresheaf
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (sliceRingPresheaf 𝒪
          U))).map
          (sliceUnit 𝒪 h𝒪 U P)) :=
  have : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P)) :=
    PresheafOfModules.isLocallyInjective_sheafificationAdjunction_unit_app
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj) P
  Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U)
    ((PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P))

omit [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The restricted sheafification unit is locally surjective. -/
theorem isLocallySurjective_sliceUnit
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
      :
    Presheaf.IsLocallySurjective (J.over U)
      ((PresheafOfModules.toPresheaf
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (sliceRingPresheaf 𝒪
          U))).map
          (sliceUnit 𝒪 h𝒪 U P)) :=
  have : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P)) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
    (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj) P
  Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
    ((PresheafOfModules.toPresheaf _).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪 P))

/-- The component of `sliceComparison` at each presheaf of modules is an isomorphism. -/
instance isIso_sliceComparison_app
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
      :
    IsIso ((sliceComparison 𝒪 h𝒪 U).app P) := by
  rw [sliceComparison_app]
  exact Stacks.TensorCoherence.isIso_sheafificationHomEquiv_symm
    (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj) _
    (isLocallyInjective_sliceUnit 𝒪 h𝒪 U P) (isLocallySurjective_sliceUnit 𝒪 h𝒪 U P)

/-- The comparison morphism `sliceComparison` is a natural isomorphism. -/
instance isIso_sliceComparison : IsIso (sliceComparison 𝒪 h𝒪 U) :=
  NatIso.isIso_of_isIso_app _

/-- **Sheafification commutes with restriction to a slice site.** -/
noncomputable def sliceSheafifyIso :
    sheafifyFunctor 𝒪 h𝒪 ⋙ overFunctor 𝒪 h𝒪 U ≅
      sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U :=
  (asIso (sliceComparison 𝒪 h𝒪 U)).symm

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- The presheaf-level restriction to the slice site, followed by sheafification there, is
monoidal: the first is Mathlib's `PresheafOfModules.pushforward₀OfCommRingCat`, the second is
the monoidal localization functor. -/
@[instance_reducible]
noncomputable def sliceCompSheafifyMonoidal :
    (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
  inferInstance

/-- Restriction of sheaves of modules to the slice site lifts the presheaf-level restriction
followed by sheafification, along sheafification. -/
noncomputable instance lifting :
    Localization.Lifting (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
      (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) (overFunctor 𝒪 h𝒪 U) :=
  ⟨sliceSheafifyIso 𝒪 h𝒪 U⟩

/-- **Restriction of sheaves of modules to a slice site is a monoidal functor**, for the
localized monoidal structure on each side. -/
@[instance_reducible]
noncomputable def overFunctorMonoidalLocalized : (overFunctor 𝒪 h𝒪 U).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal 𝒪 h𝒪
  letI := sliceCompSheafifyMonoidal 𝒪 h𝒪 U
  Localization.Monoidal.functorMonoidalOfComp (sheafifyFunctor 𝒪 h𝒪) (localIso (J := J) 𝒪)
    (overFunctor 𝒪 h𝒪 U) (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U)

/-- The localized monoidal structure lives on this type synonym for sheaves of modules. -/
abbrev localizedSrc : Type _ :=
  LocalizedMonoidal (L := sheafifyFunctor 𝒪 h𝒪) (W := localIso (J := J) 𝒪)
    (sheafifyUnitIso 𝒪 h𝒪)

/-- The localized monoidal structure on sheaves of modules on the slice site. -/
abbrev localizedTgt : Type _ :=
  LocalizedMonoidal (L := sliceSheafify 𝒪 h𝒪 U)
    (W := localIso (J := J.over U) (sliceRingPresheaf 𝒪 U))
    (sheafifyUnitIso (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U))

/-- `overFunctor`, retyped between the two type synonyms carrying the localized monoidal
structures. -/
noncomputable abbrev overFunctorLocalized :
    localizedSrc 𝒪 h𝒪 ⥤ localizedTgt 𝒪 h𝒪 U :=
  overFunctor 𝒪 h𝒪 U

/-- `overFunctorMonoidalLocalized`, read at the type-synonym spelling. -/
@[instance_reducible]
noncomputable def overFunctorLocalizedMonoidal :
    (overFunctorLocalized 𝒪 h𝒪 U).Monoidal :=
  overFunctorMonoidalLocalized 𝒪 h𝒪 U

end Monoidal

section Strict

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- The identity functor from the type synonym carrying the localized monoidal structure back
to sheaves of modules, where the strict monoidal structure of Tag 01CA lives. -/
noncomputable def fromLocalizedMonoidal :
    localizedSrc 𝒪 h𝒪 ⥤ SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  𝟭 _

/-- `Strict.toLocalizedMonoidal` and `fromLocalizedMonoidal` are an equivalence: both are the
identity functor. -/
noncomputable def localizedEquivalence :
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ≌
      localizedSrc 𝒪 h𝒪 where
  functor := Stacks.SheafOfModules.Strict.toLocalizedMonoidal 𝒪 h𝒪
  inverse := fromLocalizedMonoidal 𝒪 h𝒪
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The identity functor into the localized spelling is monoidal: that is what
`CategoryTheory.Monoidal.induced` produces, and it is the half of the comparison that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict` already uses. -/
@[instance_reducible]
noncomputable def toLocalizedMonoidalMonoidal :
    (Stacks.SheafOfModules.Strict.toLocalizedMonoidal 𝒪 h𝒪).Monoidal :=
  letI := Stacks.SheafOfModules.Strict.monoidalCategoryStruct 𝒪 h𝒪
  (CategoryTheory.Monoidal.fromInducedCoreMonoidal
    (Stacks.SheafOfModules.Strict.toLocalizedMonoidal 𝒪 h𝒪)
    (Stacks.SheafOfModules.Strict.inducingFunctorData 𝒪 h𝒪)).toMonoidal

/-- **The identity functor out of the localized spelling is monoidal.** This is the direction
`CategoryTheory.Monoidal.induced` does not supply, and the one a monoidal functor between
strict structures has to be composed with. -/
@[instance_reducible]
noncomputable def fromLocalizedMonoidalMonoidal :
    (fromLocalizedMonoidal 𝒪 h𝒪).Monoidal :=
  @CategoryTheory.Equivalence.inverseMonoidal _ _ _ _ _ _ (localizedEquivalence 𝒪 h𝒪)
    (toLocalizedMonoidalMonoidal 𝒪 h𝒪)

/-- **Restriction of sheaves of modules to a slice site is a monoidal functor for the monoidal
structure of Tag 01CA**, whose tensor product is the tensor product sheaf on the nose. -/
@[instance_reducible]
noncomputable def overFunctorMonoidal : (overFunctor 𝒪 h𝒪 U).Monoidal :=
  letI := overFunctorLocalizedMonoidal 𝒪 h𝒪 U
  letI := toLocalizedMonoidalMonoidal 𝒪 h𝒪
  letI := fromLocalizedMonoidalMonoidal (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
  inferInstanceAs ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal 𝒪 h𝒪 ⋙
    overFunctorLocalized 𝒪 h𝒪 U ⋙
      fromLocalizedMonoidal (sliceRingPresheaf 𝒪 U)
        (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)).Monoidal)

end Strict

/-- `overFunctorMonoidal` with both monoidal structures named explicitly, outside the scope of
any local instance: **restriction to the slice site over `U` is a monoidal functor from
`Stacks.SheafOfModules.Strict.monoidalCategory` on `C` to
`Stacks.SheafOfModules.Strict.monoidalCategory` on `Over U`.** This is the hypothesis
`CategoryTheory.ExactPairing.ofJointlyFaithful` consumes. -/
@[instance_reducible]
noncomputable def overFunctorStrictMonoidal :
    letI := Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪
    letI := Stacks.SheafOfModules.Strict.monoidalCategory (sliceRingPresheaf 𝒪 U)
      (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
    (overFunctor 𝒪 h𝒪 U).Monoidal :=
  overFunctorMonoidal 𝒪 h𝒪 U

/-- **The tensor product sheaf of Tag 01CA commutes with restriction to a slice site.** This is
the tensorator of `overFunctorMonoidal`, read through
`Stacks.SheafOfModules.Strict.tensorObj_eq`: the tensor product of the strict monoidal structure
*is* `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, so its tensorator is literally a
  comparison of tensor product
sheaves.

This is the Tag 01CA analogue of `Stacks.TensorCoherence.tensorSheafOverIso`, which is the same
statement for the third spelling `Stacks.sheafTensorRight` of the tensor product of sheaves of
modules on this branch. -/
noncomputable def tensorSheafOver
    (A B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(sliceRingPresheaf 𝒪 U),
          Presheaf.isSheaf_of_isSheaf_comp _ ((sliceRingPresheaf 𝒪 U)) (forget₂ CommRingCat RingCat)
            ((isSheaf_sliceRingPresheaf 𝒪 h𝒪 U))⟩).obj
        (((overFunctor 𝒪 h𝒪 U).obj A))).obj (((overFunctor 𝒪 h𝒪 U).obj B))) ≅
      (overFunctor 𝒪 h𝒪 U).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
            (A)).obj (B))) :=
  letI := Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪
  letI := Stacks.SheafOfModules.Strict.monoidalCategory (sliceRingPresheaf 𝒪 U)
    (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
  letI := overFunctorMonoidal 𝒪 h𝒪 U
  Functor.Monoidal.μIso (overFunctor 𝒪 h𝒪 U) A B

end Sheafify

end Stacks.SheafOfModules.SliceRestriction

end
