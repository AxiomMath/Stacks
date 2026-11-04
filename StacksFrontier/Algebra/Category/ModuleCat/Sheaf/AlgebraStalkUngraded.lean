module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01CH, ungraded symmetric assertion: the stalk of the symmetric algebra of a sheaf of modules

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `M` a sheaf of
`O♯`-modules and `A` a symmetric algebra of `M` in the sense of Stacks Section 17.21. Stacks Tag
01CH asserts canonical isomorphisms of `O_x`-modules between the stalk at `x` of each of `T(M)`,
`Sym(M)`, `⋀(M)` and the corresponding construction applied to the stalk `M_x`. This file proves
the **ungraded** symmetric assertion

`Sym(M)_x ≅ Sym_{O_x}(M_x)`,

together with the formula that pins the isomorphism down: for every `n`, it carries the germ at
`x` of the degree-`n` local section `s₀ ⋯ sₙ₋₁` of `Sym(M)` to the product of the germs of the
`sᵢ`.

Here `Sym(M)` is the sheaf of modules underlying the symmetric algebra, that is the coproduct
`∐ n, Symⁿ M` of its homogeneous pieces, as in
`SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraSheaf`.

The proof has two halves. The first, which is the content of this file and is independent of
symmetric algebras, is that **the stalk of a coproduct of sheaves of modules is the direct sum of
the stalks** (`SheafOfModules.stalkCoprodEquiv`), with the comparison prescribed on the image of
each coproduct injection. The second is the degreewise statement
`SheafOfModules.symmetricPowerStalkEquiv` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf`, which is Tag 01CH in a fixed
graded degree; `SymmetricAlgebra.directSumSymmetricPowerEquiv` reassembles `⨁ n, Symⁿ(M_x)` into
`Sym(M_x)`.

## Main definitions

* `SheafOfModules.stalkCoprodComparison` : the canonical `O_x`-linear map
  `⨁ i, (Pᵢ)_x ⟶ (∐ i, Pᵢ)_x`, for a family indexed by an arbitrary type `ι : Type u`, assembled
  by `DirectSum.toModule` from the stalk maps of the coproduct injections.
* `SheafOfModules.isColimitStalkObjCofan` and `SheafOfModules.stalkObjCoprodDirectSumIso` : the
  image of the coproduct cofan under
  `AlgebraicGeometry.SheafOfModules.stalkFunctor` is a colimit cofan — this is Tag 01AH, that is
  `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` — and the resulting
  identification of the stalk of the coproduct with the direct sum, in
  `ModuleCat (O_x)` for the `RingCat`-valued stalk `O_x`.
* `SheafOfModules.stalkCoprodAddHom` : the inverse of that identification, read as an additive map
  whose codomain is spelled `↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x)`.
* `SheafOfModules.stalkCoprodEquiv` : **the stalk of a coproduct is the direct sum of the
  stalks**, as a linear equivalence over the `CommRingCat`-valued stalk of `O♯`.
* `SheafOfModules.hasCoproduct` : a shortcut instance recording that `Type u`-indexed coproducts
  of sheaves of modules on `Opens X` exist.
* `SheafOfModules.natStalkCoprodComparison`, `natIsColimitStalkObjCofan`,
  `natStalkObjCoprodDirectSumIso`, `natStalkCoprodAddHom` and `natStalkCoprodEquiv` : the same
  chain for an `ℕ`-indexed family. See the implementation note on the index universe for why this
  is a separate chain and not an instance of the one above.
* `SheafOfModules.symmetricAlgebraStalkEquiv` : **the comparison isomorphism of the ungraded
  symmetric assertion of Tag 01CH**. Its hypotheses are those of
  `SheafOfModules.symmetricPowerStalkEquiv`: a sheaf of graded algebras `A`, a degree-one
  generator `gen : M ⟶ A.piece 1`, and the universal property making `A` a symmetric algebra
  of `M`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraStalkEquiv` and
  `SheafOfModules.ringedSpaceSymmetricAlgebraStalkEquiv` : the same comparison for the symmetric
  algebra supplied by a package of the three algebras of Section 17.21, and for the chosen
  package on a ringed space, which is the form Section 17.21 states its lemmas in.

## Main results

* `SheafOfModules.stalkCoprodEquiv_of` : the comparison of `stalkCoprodEquiv` on the `i`-th
  summand is the stalk map of the `i`-th coproduct injection. Since the summands generate the
  direct sum this determines the comparison. `SheafOfModules.natStalkCoprodEquiv_of` is the
  `ℕ`-indexed form.
* `SheafOfModules.symmetricAlgebraStalkEquiv_germ_homogeneousProd` : **the comparison on a
  product of local sections.** The germ at `x` of the image, under the degree-`n` coproduct
  injection, of the ordered product in `A` of the images of `s₀, …, sₙ₋₁` under the degree-one
  generator goes to the product of the germs of the `sᵢ`.
* `SheafOfModules.symmetricAlgebra_stalk` : **Tag 01CH, ungraded symmetric assertion** — the
  isomorphism and that formula assembled into the single assertion that a comparison isomorphism
  with that behaviour on germs of products exists. This is the declaration carrying the tag.

## Implementation notes

**Which clause of Tag 01CH is proved, and which are open.** Tag 01CH makes three assertions. The
symmetric one is proved: in each graded degree by `SheafOfModules.symmetricPower_stalk`, and
ungraded by `SheafOfModules.symmetricAlgebra_stalk` here. The tensor one is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk`, which consumes
`SheafOfModules.natStalkCoprodEquiv` below for exactly the graded-to-ungraded passage this file
supplies: degreewise it is `SheafOfModules.tensorPower_stalk` and ungraded
`SheafOfModules.tensorAlgebra_stalk`, both pinned on germs of ordered tensors of local sections.
The exterior one is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, which likewise consumes
`SheafOfModules.natStalkCoprodEquiv` below for the graded-to-ungraded passage: degreewise it is
`PresheafOfModules.extPowStalkEquivOfStalkIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`, bundled for a sheaf of graded
algebras as `SheafOfModules.exteriorPowerStalkEquiv`, and ungraded it is
`SheafOfModules.exteriorAlgebra_stalk`. So all three ungraded assertions of the tag are now
proved, and the coproduct chain below is what two of the three rest on.

**Two spellings of the stalk of the sheaf of rings, and why the comparison is built twice.**
`AlgebraicGeometry.SheafOfModules.stalkFunctor O x` takes values in
`ModuleCat (TopCat.Presheaf.stalk O.obj x)` for a sheaf of `RingCat`-valued rings `O`, so for
`O = toRingCat J O♯` the scalars are the stalk of `O♯.obj ⋙ forget₂ CommRingCat RingCat`
computed in `RingCat`. The symmetric algebra, however, can only be formed over the
`CommRingCat`-valued stalk of `O♯` itself, which is a different type: the colimit over the
neighbourhoods of `x` taken in `CommRingCat`. The two module structures are on the same abelian
group and the two stalk maps are the same function, so the crossing is confined to
`bijective_stalkCoprodComparison`, which transports bijectivity — a property of the underlying
function — from the `RingCat` side to the `CommRingCat` side using
`DirectSum.addHom_ext`. This crossing is also what pins the index universe down; see the next
note. `stalkCoprodAddHom` exists for the same reason: the codomain of
`stalkObjCoprodDirectSumIso.inv` is spelled
`AlgebraicGeometry.SheafOfModules.stalkObj O x (∐ P)` rather than
`↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x)`, and although the two are definitionally equal a
goal mixing them is not type-correct at `implicit` transparency, so `rw` and `simp` refuse it.
Giving the map a `def` with the ascribed type and reaching it with `exact`, which is
defeq-tolerant, is what avoids that.

**The index universe is `Type u`, and that is forced.** The coproduct statements are stated for a
family indexed by an arbitrary `ι : Type u`, with `u` the common universe of the space, the sheaf
of rings and the sheaf of modules. Two strictly more general forms were tried and neither is
available.

* An index type in a *free* universe, `ι : Type w` with the space still in `Type u`, is not
  merely hard but ill-typed: `stalkObjCoprodDirectSumIso` identifies the stalk of the coproduct
  with `ModuleCat.of _ (⨁ (i : ι), ↑(TopCat.Presheaf.stalk (P i).val.presheaf x))`, and that
  direct sum is an object of `ModuleCat.{max w u}` while the stalk is an object of
  `ModuleCat.{u}`; an isomorphism between them exists only when `max w u = u`. Independently,
  `HasCoproduct P` does not hold for `ι : Type w`, as a coproduct of that size does not exist in
  `SheafOfModules.{u}`.
* Parameterising the solution of `max w u = u`, that is taking `ι : Type w` with the space in
  `TopCat.{max w u}`, *does* let every statement in this file elaborate, and instantiates
  correctly at `ι = ℕ` with `w := 0`. It fails in the proofs: with the universes written as
  `max w u`, the crossing between the two spellings of the stalk ring described above exceeds the
  `isDefEq` budget. Concretely `Function.Bijective ((stalkCoprodComparison P x).toAddMonoidHom)`
  does not elaborate within 200000 heartbeats, and the kernel likewise rejects
  `stalkCoprodEquiv_of`, whereas the byte-identical file with `max w u` replaced by `u` and
  `Type w` by `Type u` compiles in five seconds. Raising `maxHeartbeats` is not available here.

Since `ℕ : Type 0` is not a `Type u`, the `ℕ`-indexed family that Tag 01CH needs is not an
instance of the `Type u`-indexed statements, and the chain is given a second time under the
`nat` prefix, where `CategoryTheory.Limits.preservesColimitsOfSize_shrink` moves Tag 01AH from
shapes in `Type u` to `Discrete ℕ : Type 0` (nothing is narrowed, since `max 0 u = u`). The
duplication would be removed by a reindexing bridge — `DirectSum.lequivCongrLeft` along
`Equiv.ulift` together with `CategoryTheory.Limits.Sigma.whiskerEquiv` and a stalk linear
equivalence from `PresheafOfModules.stalkLinearEquiv` — which is not built here.

**Every degree is a variable.** No statement below instantiates a numeral degree.
`SymmetricAlgebra R N` is a reducible abbreviation for a `RingCon` quotient of
`TensorAlgebra R N`, so with a numeral degree `whnf` unfolds `SymPow.symmetricPower (1 + 1)`
through `Submodule.mul` and `Submodule.span` into that quotient, which is fatal while elaborating
a *statement* and not only in a proof. The one numeral that appears, in `gen : M ⟶ A.piece 1`, is
the degree of a piece of an *abstract* sheaf of graded algebras, where there is nothing to
unfold.

**Universes.** The space, the ring and the module universe are all `u`. That is forced, not
chosen: Mathlib's instance `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` in
`Mathlib/Algebra/Category/ModuleCat/Stalk.lean` exists at no other combination, and
`AlgebraicGeometry.SheafOfModules.stalkFunctor` is likewise stated for `X : TopCat.{u}` and a
sheaf of `RingCat.{u}`-valued rings. The same constraint is already recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk`. Tag 01CH is stated in the
equal-universe case and nothing the source says is narrowed.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf
open DirectSum

-- The structure sheaf of rings of a ringed space is now a single definition whose body
-- stops at an explicit-constructor projection, so the module structures on stalks below
-- need these two Mathlib definitions unfolded to be found by instance search.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe u

namespace SheafOfModules

/-! ### The stalk of a coproduct of sheaves of modules -/

section Coproduct

variable {X : TopCat.{u}}
  {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- Coproducts of `Type w`-indexed families of sheaves of modules on `Opens X` exist. This is
already an instance, through
`SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf`, but
only reachable by a search that exceeds the default `synthInstance` budget once the index type is
a variable rather than `ℕ`; recording the conclusion at this shape makes the search immediate for
every statement below. -/
instance hasCoproduct {ι : Type u}
    (P : ι → SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    HasCoproduct P :=
  inferInstance

variable {ι : Type u} [DecidableEq ι]
  (P : ι → SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (x : ↥X)

/-- **The comparison map from the direct sum of the stalks to the stalk of the coproduct.** On
the `i`-th summand it is the stalk map of the `i`-th coproduct injection. -/
noncomputable def stalkCoprodComparison :
    (⨁ (i : ι), ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) →ₗ[
        ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x) :=
  DirectSum.toModule _ ι _ fun i => PresheafOfModules.stalkMapL x (Sigma.ι P i).val

/-- `stalkCoprodComparison` on the `i`-th summand is the stalk map of the `i`-th coproduct
injection. -/
theorem stalkCoprodComparison_of (i : ι) (t : ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) :
    stalkCoprodComparison P x (DirectSum.of _ i t) =
      PresheafOfModules.stalkMapL x (Sigma.ι P i).val t := by
  exact DirectSum.toModule_lof
    (M := fun i => ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) _ i t

/-- **The stalk of the coproduct is a colimit of the stalks.** This is Tag 01AH, that is
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, applied to the coproduct
cofan. With the index type in `Type u` the shape `Discrete ι` is already of the size Tag 01AH is
stated at, so no size change is needed. -/
noncomputable def isColimitStalkObjCofan :
    IsColimit ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x).mapCocone
        (Cofan.mk (∐ P) (Sigma.ι P))) := by
  letI : PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits _ _
  exact isColimitOfPreserves _ (coproductIsCoproduct P)

/-- The stalk of the coproduct, identified with the direct sum of the stalks in
`ModuleCat` over the `RingCat`-valued stalk of the sheaf of rings. Both cofans being colimiting —
`isColimitStalkObjCofan` and `ModuleCat.coproductCoconeIsColimit` — their points agree, and
`CategoryTheory.Discrete.natIso` reconciles the two spellings of the diagram of stalks. -/
noncomputable def stalkObjCoprodDirectSumIso :
    AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (∐ P) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj x)
        (⨁ (i : ι), ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) :=
  IsColimit.coconePointsIsoOfNatIso (isColimitStalkObjCofan P x)
    (ModuleCat.coproductCoconeIsColimit
      (fun i : ι => AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (P i)))
    (Discrete.natIso fun _ => Iso.refl _)

/-- The inverse of `stalkObjCoprodDirectSumIso` on the `i`-th summand is the stalk map of the
`i`-th coproduct injection. -/
theorem stalkObjCoprodDirectSumIso_inv_of (i : ι)
    (t : ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) :
    (stalkObjCoprodDirectSumIso P x).inv.hom (DirectSum.of _ i t) =
      PresheafOfModules.stalkMapL x (Sigma.ι P i).val t := by
  have h := IsColimit.comp_coconePointsIsoOfNatIso_inv (isColimitStalkObjCofan P x)
    (ModuleCat.coproductCoconeIsColimit
      (fun i : ι => AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (P i)))
    (Discrete.natIso fun _ => Iso.refl _) ⟨i⟩
  exact congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f t) h

/-- The inverse of `stalkObjCoprodDirectSumIso`, as an additive map whose codomain is spelled
`↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x)` rather than
`AlgebraicGeometry.SheafOfModules.stalkObj _ x (∐ P)`. The ascribed type is the point of this
declaration: the two spellings are definitionally equal but a goal mixing them is not
type-correct at `implicit` transparency, so neither `rw` nor `simp` will accept it. -/
noncomputable def stalkCoprodAddHom :
    (⨁ (i : ι), ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) →+
      ↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x) :=
  (stalkObjCoprodDirectSumIso P x).inv.hom.toAddMonoidHom

/-- `stalkCoprodAddHom` on the `i`-th summand is the stalk map of the `i`-th coproduct
injection. -/
theorem stalkCoprodAddHom_of (i : ι) (t : ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) :
    stalkCoprodAddHom P x (DirectSum.of _ i t) =
      PresheafOfModules.stalkMapL x (Sigma.ι P i).val t :=
  stalkObjCoprodDirectSumIso_inv_of P x i t

/-- `stalkCoprodAddHom` is bijective. -/
theorem bijective_stalkCoprodAddHom : Function.Bijective (stalkCoprodAddHom P x) :=
  ConcreteCategory.bijective_of_isIso (stalkObjCoprodDirectSumIso P x).inv

/-- A linear map out of a direct sum that agrees on each summand with a bijective additive map is
bijective. -/
private theorem bijective_of_addHom_of {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R]
    {β : ι → Type*} [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] {N : Type*}
    [AddCommMonoid N] [Module R N] (f : (⨁ i, β i) →ₗ[R] N) (g : (⨁ i, β i) →+ N)
    (h : ∀ i y, f (DirectSum.of β i y) = g (DirectSum.of β i y)) (hg : Function.Bijective g) :
    Function.Bijective f := by
  have key : f.toAddMonoidHom = g := DirectSum.addHom_ext h
  have h' : Function.Bijective f.toAddMonoidHom := key ▸ hg
  exact h'

/-- The comparison map is bijective. Bijectivity is a property of the underlying function, so it
transports from `stalkCoprodAddHom` — which is linear over the `RingCat`-valued stalk of the
sheaf of rings — to `stalkCoprodComparison`, which is linear over the `CommRingCat`-valued one.
The two maps agree because they agree on each summand. -/
theorem bijective_stalkCoprodComparison :
    Function.Bijective (stalkCoprodComparison P x) :=
  bijective_of_addHom_of _ _
    (fun i y => (stalkCoprodComparison_of P x i y).trans (stalkCoprodAddHom_of P x i y).symm)
    (bijective_stalkCoprodAddHom P x)

/-- **The stalk of a coproduct of sheaves of modules is the direct sum of the stalks**, as a
linear equivalence over the stalk of the sheaf of commutative rings. -/
noncomputable def stalkCoprodEquiv :
    (⨁ (i : ι), ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) ≃ₗ[
        ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (∐ P).val.presheaf x) :=
  LinearEquiv.ofBijective _ (bijective_stalkCoprodComparison P x)

/-- **The comparison of `stalkCoprodEquiv` on the `i`-th summand** is the stalk map of the `i`-th
coproduct injection. The summands generate the direct sum, so this determines the
comparison. -/
theorem stalkCoprodEquiv_of (i : ι) (t : ↑(TopCat.Presheaf.stalk (P i).val.presheaf x)) :
    stalkCoprodEquiv P x (DirectSum.of _ i t) =
      PresheafOfModules.stalkMapL x (Sigma.ι P i).val t :=
  stalkCoprodComparison_of P x i t

end Coproduct

/-! ### The stalk of an `ℕ`-indexed coproduct of sheaves of modules -/

section NatCoproduct

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
variable (Q : ℕ → SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (x : ↥X)

/-- `SheafOfModules.stalkCoprodComparison` for an `ℕ`-indexed family. -/
noncomputable def natStalkCoprodComparison :
    (⨁ (n : ℕ), ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) →ₗ[
        ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (∐ Q).val.presheaf x) :=
  DirectSum.toModule _ ℕ _ fun n => PresheafOfModules.stalkMapL x (Sigma.ι Q n).val

/-- `SheafOfModules.stalkCoprodComparison_of` for an `ℕ`-indexed family. -/
theorem natStalkCoprodComparison_of (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) :
    natStalkCoprodComparison Q x (DirectSum.of _ n t) =
      PresheafOfModules.stalkMapL x (Sigma.ι Q n).val t := by
  exact DirectSum.toModule_lof
    (M := fun n => ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) _ n t

/-- `SheafOfModules.isColimitStalkObjCofan` for an `ℕ`-indexed family. Here
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` is needed, because `Discrete ℕ` lives in
`Type 0` while Tag 01AH is stated for shapes in `Type u`; nothing is narrowed, since
`max 0 u = u`. -/
noncomputable def natIsColimitStalkObjCofan :
    IsColimit ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x).mapCocone
        (Cofan.mk (∐ Q) (Sigma.ι Q))) := by
  letI : PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits _ _
  letI : PreservesColimitsOfSize.{0, 0} (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact isColimitOfPreserves _ (coproductIsCoproduct Q)

/-- `SheafOfModules.stalkObjCoprodDirectSumIso` for an `ℕ`-indexed family. -/
noncomputable def natStalkObjCoprodDirectSumIso :
    AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (∐ Q) ≅
      ModuleCat.of ↑(TopCat.Presheaf.stalk
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj x)
        (⨁ (n : ℕ), ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) :=
  IsColimit.coconePointsIsoOfNatIso (natIsColimitStalkObjCofan Q x)
    (ModuleCat.coproductCoconeIsColimit
      (fun n : ℕ => AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (Q n)))
    (Discrete.natIso fun _ => Iso.refl _)

/-- `SheafOfModules.stalkObjCoprodDirectSumIso_inv_of` for an `ℕ`-indexed family. -/
theorem natStalkObjCoprodDirectSumIso_inv_of (n : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) :
    (natStalkObjCoprodDirectSumIso Q x).inv.hom (DirectSum.of _ n t) =
      PresheafOfModules.stalkMapL x (Sigma.ι Q n).val t := by
  have h := IsColimit.comp_coconePointsIsoOfNatIso_inv (natIsColimitStalkObjCofan Q x)
    (ModuleCat.coproductCoconeIsColimit
      (fun n : ℕ => AlgebraicGeometry.SheafOfModules.stalkObj
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x (Q n)))
    (Discrete.natIso fun _ => Iso.refl _) ⟨n⟩
  exact congrArg (fun f : _ ⟶ _ => ModuleCat.Hom.hom f t) h

/-- `SheafOfModules.stalkCoprodAddHom` for an `ℕ`-indexed family. -/
noncomputable def natStalkCoprodAddHom :
    (⨁ (n : ℕ), ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) →+
      ↑(TopCat.Presheaf.stalk (∐ Q).val.presheaf x) :=
  (natStalkObjCoprodDirectSumIso Q x).inv.hom.toAddMonoidHom

/-- `SheafOfModules.stalkCoprodAddHom_of` for an `ℕ`-indexed family. -/
theorem natStalkCoprodAddHom_of (n : ℕ) (t : ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) :
    natStalkCoprodAddHom Q x (DirectSum.of _ n t) =
      PresheafOfModules.stalkMapL x (Sigma.ι Q n).val t :=
  natStalkObjCoprodDirectSumIso_inv_of Q x n t

/-- `SheafOfModules.bijective_stalkCoprodAddHom` for an `ℕ`-indexed family. -/
theorem bijective_natStalkCoprodAddHom : Function.Bijective (natStalkCoprodAddHom Q x) :=
  ConcreteCategory.bijective_of_isIso (natStalkObjCoprodDirectSumIso Q x).inv

/-- `SheafOfModules.bijective_stalkCoprodComparison` for an `ℕ`-indexed family. -/
theorem bijective_natStalkCoprodComparison :
    Function.Bijective (natStalkCoprodComparison Q x) :=
  bijective_of_addHom_of _ _
    (fun n y => (natStalkCoprodComparison_of Q x n y).trans (natStalkCoprodAddHom_of Q x n y).symm)
    (bijective_natStalkCoprodAddHom Q x)

/-- **The stalk of an `ℕ`-indexed coproduct of sheaves of modules is the direct sum of the
stalks.** This is `SheafOfModules.stalkCoprodEquiv` for an `ℕ`-indexed family. -/
noncomputable def natStalkCoprodEquiv :
    (⨁ (n : ℕ), ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) ≃ₗ[
        ↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk (∐ Q).val.presheaf x) :=
  LinearEquiv.ofBijective _ (bijective_natStalkCoprodComparison Q x)

/-- **The comparison of `natStalkCoprodEquiv` on the `n`-th summand** is the stalk map of the
`n`-th coproduct injection. -/
theorem natStalkCoprodEquiv_of (n : ℕ) (t : ↑(TopCat.Presheaf.stalk (Q n).val.presheaf x)) :
    natStalkCoprodEquiv Q x (DirectSum.of _ n t) =
      PresheafOfModules.stalkMapL x (Sigma.ι Q n).val t :=
  natStalkCoprodComparison_of Q x n t

end NatCoproduct

/-! ### Tag 01CH for the ungraded symmetric algebra of a sheaf of modules -/

section Symmetric

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsSymmetricAlgebra A gen)

/-- **The comparison isomorphism of the ungraded symmetric assertion of Tag 01CH**: for a
symmetric algebra `A` of a sheaf of modules `M`, the stalk at `x` of the sheaf of modules
`∐ n, Symⁿ M` underlying `Sym(M)` is the symmetric algebra of the stalk `M_x` over the stalk ring
`O_x`.

It is the composition of three identifications: the stalk of the coproduct is the direct sum of
the stalks (`natStalkCoprodEquiv`); in each degree the stalk of `Symⁿ M` is `Symⁿ(M_x)`
(`SheafOfModules.symmetricPowerStalkEquiv`, which is Tag 01CH in degree `n`); and `Sym(M_x)` is
the direct sum of its symmetric powers
(`SymmetricAlgebra.directSumSymmetricPowerEquiv`). -/
@[ega "II 1.7.4" "(S(E))_s = S(E_s)"]
noncomputable def symmetricAlgebraStalkEquiv (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  ((natStalkCoprodEquiv (fun n : ℕ => A.piece (n : ℤ)) x).symm.trans
      (DirectSum.congrLinearEquiv fun n : ℕ => symmetricPowerStalkEquiv A gen hA n x)).trans
    (SymmetricAlgebra.directSumSymmetricPowerEquiv ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- **The comparison isomorphism on a product of local sections.** The germ at `x` of the image
under the degree-`n` coproduct injection of the ordered product, in `A`, of the images of
`s₀, …, sₙ₋₁` under the degree-one generator goes to the product of the germs of the `sᵢ`.

Products of degree-one generators span each symmetric power
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`) and the symmetric powers span the symmetric
algebra, so this formula determines `symmetricAlgebraStalkEquiv` and is what makes it the
*canonical* isomorphism of Tag 01CH rather than merely one. -/
theorem symmetricAlgebraStalkEquiv_germ_homogeneousProd (x : ↥X) (n : ℕ) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin n → M.val.obj (op U)) :
    symmetricAlgebraStalkEquiv A gen hA x
        (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
          ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
              fun i => gen.val.app (op U) (s i)))) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x)
        (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) := by
  have h1 : TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
        ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i))) =
      natStalkCoprodEquiv (fun m : ℕ => A.piece (m : ℤ)) x (DirectSum.of _ n
        (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i)))) := by
    rw [natStalkCoprodEquiv_of]
    exact (PresheafOfModules.stalkMapL_germ x
      (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val U hx _).symm
  rw [h1]
  simp only [symmetricAlgebraStalkEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, DirectSum.coe_congrLinearEquiv,
    ← DirectSum.lof_eq_of ↑(TopCat.Presheaf.stalk Osharp.obj x), DirectSum.lmap_lof,
    LinearEquiv.coe_coe, SymmetricAlgebra.directSumSymmetricPowerEquiv_lof]
  exact symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA n x U hx s

include hA in
/-- **Tag 01CH, ungraded symmetric assertion.** For a sheaf of modules `M` on a topological space
with a sheaf of commutative rings `O♯`, a symmetric algebra `A` of `M` in the sense of Section
17.21, and a point `x`, there is a canonical isomorphism of `O_x`-modules

`Sym(M)_x ≅ Sym_{O_x}(M_x)`,

where `Sym(M)` is the coproduct `∐ n, Symⁿ M` of the homogeneous pieces of `A`.

It is canonical in the sense Tag 01CH means: its value is prescribed on the germ of every local
section of the form `s₀ ⋯ sₙ₋₁`, in every degree `n`, namely the product of the germs of the
`sᵢ`; such products span each symmetric power of the stalk
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`) and the symmetric powers span `Sym(M_x)`
(`SymmetricAlgebra.directSumSymmetricPowerEquiv`), so no other linear map has that behaviour.

The symmetric algebra is a hypothesis rather than a chosen term because Section 17.21 pins it
only up to canonical isomorphism;
`SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val` shows the hypothesis is
satisfiable for every `M`, and
`SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraStalkEquiv` discharges it from a
package of the three algebras of Section 17.21.

The tag carries a clause comment: this declaration carries the ungraded symmetric assertion
alone. The two tensor assertions are `SheafOfModules.tensorPower_stalk` and
`SheafOfModules.tensorAlgebra_stalk` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk`. The ungraded *exterior*
assertion `⋀(M)ₓ ≅ ⋀(Mₓ)` for a sheaf is `SheafOfModules.exteriorAlgebra_stalk` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, which is built from
`SheafOfModules.natStalkCoprodEquiv` below exactly as this declaration is; the ungraded statement
for a **presheaf** of modules, `(⋀ F)ₓ ≅ ⋀(Fₓ)`, is `PresheafOfModules.extAlgStalkRingEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk` and the degreewise sheaf
statement is `PresheafOfModules.extPowStalkEquivOfStalkIso` there. -/
@[stacks 01CH "the ungraded symmetric assertion `Sym(M)ₓ ≅ Sym(Mₓ)`, with the isomorphism \
pinned down by its values on germs of products of local sections in every degree. The tensor \
assertions are `SheafOfModules.tensorPower_stalk` and `SheafOfModules.tensorAlgebra_stalk`; the \
ungraded exterior assertion `⋀(M)ₓ ≅ ⋀(Mₓ)` for a sheaf is \
`SheafOfModules.exteriorAlgebra_stalk` in \
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, and the degreewise \
exterior assertion is `PresheafOfModules.extPowStalkEquivOfStalkIso`. With those the three \
ungraded isomorphisms the source asserts are all proved", ega "II 1.7.4" "(S(E))_s = S(E_s)"]
theorem symmetricAlgebra_stalk (x : ↥X) :
    ∃ cmp : ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      ∀ (n : ℕ) (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
        cmp (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
            ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
              (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
                fun i => gen.val.app (op U) (s i)))) =
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)
            (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) :=
  ⟨symmetricAlgebraStalkEquiv A gen hA x,
    fun n U hx s => symmetricAlgebraStalkEquiv_germ_homogeneousProd A gen hA x n U hx s⟩

end Symmetric

end SheafOfModules

/-! ### The comparison for a package of the three algebras, and on a ringed space -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **Tag 01CH, ungraded symmetric assertion, for a package of the three algebras of Section
17.21.** The stalk of the sheaf of modules `symmetricAlgebraSheaf` underlying `Sym(G)` is the
symmetric algebra of the stalk of `G`. -/
@[ega "II 1.7.4" "(S(E))_s = S(E_s)"]
noncomputable def symmetricAlgebraStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk A.symmetricAlgebraSheaf.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.symmetricAlgebraStalkEquiv A.symmetric A.symmetricGenerator
    A.symmetric_isSymmetricAlgebra x

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **Tag 01CH, ungraded symmetric assertion, on a ringed space**, for the chosen package
`SheafOfModules.ringedSpaceAlgebras` of the three algebras of Section 17.21: the stalk of the
symmetric algebra of a sheaf of modules on a ringed space is the symmetric algebra of the stalk.
This is the form Section 17.21 states its lemmas in. -/
noncomputable def ringedSpaceSymmetricAlgebraStalkEquiv (Y : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf))
    (x : ↥Y.carrier) :
    ↑(TopCat.Presheaf.stalk (ringedSpaceAlgebras Y G).symmetricAlgebraSheaf.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)]
      SymmetricAlgebra ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  TensorExteriorSymmetricAlgebras.symmetricAlgebraStalkEquiv (ringedSpaceAlgebras Y G) x

end SheafOfModules

end
