module

public import StacksFrontier.AlgebraicGeometry.SheafDescent.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Geometry.RingedSpace.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An invertible sheaf of modules is finite locally free of rank one when the stalks are local

Stacks Tag 0B8M has three clauses: a locally free module of rank one on a ringed space is
invertible; the converse holds when all stalks `𝒪_{X, x}` are local rings; and the converse fails
without that hypothesis, as a one-point space whose ring has nontrivial Picard group shows. **This
file is about clause 2 only.** Clause 1 is
`StacksFrontier/AlgebraicGeometry/SheafDescent/Basic.lean`; clause 3 is untouched everywhere.

The point of this file is the *hypothesis*. The sibling file
`StacksFrontier/AlgebraicGeometry/InvertibleRankOne/Basic.lean` proves clause 2 for a **presheaf**
of modules `L` with `(MonoidalCategory.tensorLeft L).IsEquivalence`, and that hypothesis is not the
one the repository's consumers have: they carry
`AlgebraicGeometry.SheafOfModules.IsInvertible`, equivalently
`((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, _⟩).obj L).IsEquivalence`, whose tensor product
is the **sheafified** one. The two are genuinely different, the sheaf form does not imply the
presheaf form, and so the earlier theorem does not apply. Everything here is proved from the sheaf
form.

## The route

Not the source's route, and not through stalks of `L`. The sheaf hypothesis is used only through
*essential surjectivity* of the tensor functor: there are a presheaf of modules `N` and a morphism
of presheaves of modules `η : L.val ⊗ N ⟶ 𝒪` which is a **local isomorphism**, i.e. lies in `J.W`
(`exists_localIso_of_isInvertible`). That is all the invertibility that is consumed; neither
fullness nor faithfulness of the tensor functor is used, and no monoidal or closed structure on
`SheafOfModules` is needed, so this file does not depend on
`StacksFrontier/AlgebraicGeometry/SheafInternalHom/Basic.lean`.

Write `contract η U n` for the contraction `l ↦ η_U(l ⊗ n)`, a map `L(U) → 𝒪(U)`. The whole file
is the statement that contraction against a well-chosen `n` is an isomorphism:

* **Surjective** (`surjective_contract`): if `η_U(m ⊗ n)` is a unit then its image contains a unit,
  so the image is the unit ideal. This is sectionwise and needs nothing local.
* **Injective** (`eq_zero_of_contract_eq_zero`): this is the one new argument, and it replaces the
  step where the presheaf proof used invertibility of the module of sections — which is *false*
  here, since the sections of an invertible sheaf over a non-trivializing open need not form an
  invertible module. Instead: if `η_V(l ⊗ n) = 0`, then *local injectivity* of `η` makes
  `l ⊗ n` vanish in `L(W) ⊗ N(W)` for all `W` in a covering of `V`; applying the linear map
  `pairLeft η`, `l' ⊗ n' ↦ η(m ⊗ n') • l'`, to the vanishing pure tensor gives
  `η(m ⊗ n) • l|_W = 0`, and `η(m ⊗ n)` restricts to a unit, so `l|_W = 0`; `L` being a sheaf, it
  is separated, so `l = 0`.

Local injectivity and local surjectivity of `η` come from `J.W` by
`CategoryTheory.GrothendieckTopology.W_iff_isLocallyBijective`, and separatedness of `L` from
`CategoryTheory.Presheaf.IsSheaf.isSeparated` (`isSeparated_val`).

## Where the stalk hypothesis is used

Exactly once, and only to choose the pair `(m, n)`, in `exists_isUnit_contract`. Local
surjectivity of `η` applied to the global section `1` gives an open `V₀ ∋ x` and a finite sum
`1 = ∑ᵢ η(mᵢ ⊗ nᵢ)` in `𝒪(V₀)`. Passing to germs at `x`, locality of `𝒪_{X, x}` forces a
**single** index `j` whose germ `η(mⱼ ⊗ nⱼ)_x` is a unit (`IsLocalRing.exists_of_isUnit_sum`), and
a unit germ is a unit on a smaller open
(`AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ`). Nothing else in the file mentions a
stalk. In particular the stalk of a tensor product is never identified with the tensor product of
the stalks (Stacks Tag 01CB), no module structure on a stalk is used,
`Mathlib.RingTheory.PicardGroup` is not used and not imported, and finite presentation of `L`
(which the source takes from Tag 0B8K) is never needed.

## Main definitions

* `Stacks.SheafRankOne.contract`: contraction of `L` against a section `n` of `N` along a morphism
  `η : L ⊗ N ⟶ 𝒪` of presheaves of modules, the linear map `L(U) → 𝒪(U)`, `l ↦ η_U(l ⊗ n)`.
* `Stacks.SheafRankOne.pairLeft`: the linear map `L(U) ⊗ N(U) → L(U)`, `l ⊗ n ↦ η_U(m ⊗ n) • l`,
  for a fixed `m`. The engine of the injectivity argument.
* `Stacks.SheafRankOne.contractEquiv`: contraction promoted to a linear equivalence where it is
  bijective.
* `Stacks.SheafRankOne.trivialization`: the resulting `Stacks.SheafDescent.Trivialization`, a
  restriction-compatible family of isomorphisms `L(W) ≃ 𝒪(W)` for `W` over a fixed object.
* `Stacks.SheafRankOne.overIso`: a sectionwise trivialization over `V`, read as an isomorphism
  `M.over V ≅ SheafOfModules.unit (𝒪.over V)` of sheaves of modules on the slice site. This is the
  converse of `Stacks.SheafDescent.Trivialization.ofIso`.

## Main results

* `Stacks.SheafRankOne.exists_localIso_of_isInvertible`: an invertible sheaf of modules has a
  presheaf-level partner `N` and a local isomorphism `L.val ⊗ N ⟶ 𝒪`. This is the only place the
  library invertibility predicate is unfolded.
* `Stacks.SheafRankOne.eq_zero_of_contract_eq_zero` and
  `Stacks.SheafRankOne.bijective_contract`: contraction against a section whose contraction with
  some `m` is a unit is bijective, over every further restriction, as soon as `η` is locally
  injective and `L` is separated.
* `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_trivialization`: a sheaf of modules
  sectionwise trivial on a family covering the terminal object is finite locally free of rank one.
  This is the packaging step, through `Stacks.SheafOfModules.Invertible.IsLocallyTrivial`.
* `Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible`: **clause 2 of Tag 0B8M in
  trivialization form.** On a ringed space all of whose stalks are local rings, an invertible sheaf
  of modules is sectionwise trivial on an open cover.
* `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible`: **clause 2 of Tag 0B8M.** On
  a ringed space all of whose stalks `𝒪_{X, x}` are local rings, a sheaf of modules `M` with
  `AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 M` satisfies
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M 1`.
* `Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme`: the same on a scheme,
  with **no hypothesis on the stalks**, since those of a scheme are local rings, and with the
  structure sheaf spelled `X.ringCatSheaf` as the consumers spell it.

The target class is `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`, the rank-indexed copy in a library
namespace; `StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean` bridges it to the
draft copy, so the choice is lossless.

Both spellings of the structure sheaf of a scheme are served, which matters because instance
search is syntactic even where the two are definitionally equal. The scheme corollary gives the
conclusion at `R := X.ringCatSheaf`, the spelling of `AlgebraicGeometry.Scheme.Modules` and of the
tagged statements; applying the ringed-space theorem to `X.toRingedSpace` with `h𝒪 := X.ringCatSheaf.2` gives
it at `R := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf X.ringCatSheaf.2`,
  the spelling in which the
`InvertibleLocallyFree` bridges to Stacks Tag 05P2's consequences are stated.

## Implementation notes

**Transparency.** No compiler option is set anywhere in this file; the three frictions below are
handled with ordinary tactics.

* `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a `def`, so `(structureSheaf 𝒪
  h𝒪).obj` reduces to
  `structureRingPresheaf 𝒪` only at default transparency. Everything is therefore indexed by
  `𝒪` itself — `PresheafOfModulesOfCommRing 𝒪`, which is an `abbrev` for
  `PresheafOfModules (structureRingPresheaf 𝒪)` — and a sheaf of modules `M` enters as `M.val`,
  accepted by the defeq check at application time, exactly as the sibling `SheafDescent` file does
  it. The monoidal structure is brought in as `AlgebraicGeometry.SheafOfModules`'s own
  `local instance`.
* In `exists_localIso_of_isInvertible` the composite
  `(tensorLeftFunctorUniversal …).ι.app M ≫ e.hom.val` is type-correct only at default
  transparency, because `(F ⋙ G).obj M` and `G.obj (F.obj M)` are not interchangeable at
  `implicit` transparency. Consequently `rw [Functor.map_comp]` on it fails. The fix is to avoid
  functoriality of the composite altogether and use multiplicativity of the morphism property:
  `MorphismProperty.comp_mem` matches the goal syntactically and never re-checks the composite.
  The sheafification unit is written `(tensorLeftFunctorUniversal …).ι.app M` rather than
  `Stacks.SheafOfModules.TensorSheafification.toSheafify …` — the same term, but stated at the type
    that composes with `e.hom.val`.
* `(𝟙_ (PresheafOfModulesOfCommRing 𝒪)).obj U` has the carrier of `𝒪.obj U` but is not it
  syntactically, so the numeral `1` does not elaborate at that type; the unit section is written
  `(1 : 𝒪.obj U)` with an explicit ascription.

**Universes.** The sectionwise sections are polymorphic: site universes `u v` and module universe
`w`, unrelated. The `Trivializations` section is not: `Stacks.SheafDescent.Trivialization` forces
the module universe to be `max u v w`, because its dual quantifies over objects and morphisms of
the site. That is why the geometric sections are stated for `RingedSpace.{u, u}` — carrier and
rings in one universe — which is what `Scheme.{u}` provides and what collapses `max u v w` to `u`.
`RingedSpace` has two universe parameters, so `RingedSpace.{u}` leaves the second free. Whether
that is fatal depends on how the structure sheaf is then written. At the `Stacks.SheafOfModules.TensorSheafification.structureSheaf
  X.presheaf h𝒪` spelling used here the
carrier universe is never mentioned, nothing collapses it, and the sheafification instances for the
site are indeed not found. At the one-universe `structureSheaf` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact`, which sends a
`TopCat.Sheaf CommRingCat.{v} Y` to a `TopCat.Sheaf RingCat.{v} Y`, writing
`structureSheaf X.sheaf` forces the collapse: it elaborates
as `RingedSpace.{u, u}`, and the instances are found. That is the spelling
`StacksFrontier/AlgebraicGeometry/InvertibleRankOneIff/Basic.lean` uses to state the clauses at the
generality of Tag 0B8M's own statement.

**Duplicate vocabulary.** `Stacks.SheafRankOne.contract` repeats the shape of
`Stacks.InvertibleRankOne.contract`, which is defined from an *isomorphism* `L ⊗ N ≅ 𝒪` rather than
a morphism and so is not applicable here. The version here is the more general one; unifying them
means re-indexing the sibling file on a morphism, which is outside this directory.

**No Stacks attribute.** No Stacks attribute is attached anywhere in this file. Two of Tag 0B8M's
three labels are proved, but at the ringed-space spelling, and they carry the tag in
`StacksFrontier/AlgebraicGeometry/InvertibleRankOneIff/Basic.lean`; this file supplies the forward
implication they are assembled from. Clause 3 is not formalized at all.

## What is not done

* **Clause 3** — the one-point counterexample showing the converse fails in general — is not
  formalized, here or anywhere in the repository. Accordingly nothing here is stated as an
  unconditional biconditional, and the stalk hypothesis is never dropped except on a scheme, where
  it holds.
* **Clause 1** is not reproved; it is
  `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`.
* The ringed-space results are stated for a space all of whose stalks are local rings, not for
  `AlgebraicGeometry.LocallyRingedSpace`; the scheme corollary is the only instance of them
  provided.
* The sibling presheaf-level clause 2
  (`Stacks.InvertibleRankOne.exists_cover_trivialization_of_tensorLeft`) is neither used nor
  compared with: the two hypotheses remain incomparable at this Mathlib pin, and nothing here
  bears on that.
* No statement about stalks of `L` is proved. In particular `L_x ≅ 𝒪_{X, x}`, which is how the
  source phrases the heart of clause 2, is nowhere asserted, and Stacks Tag 01CB is still absent
  from the repository.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite TensorProduct TopologicalSpace
  Stacks.SheafOfModules.TensorSheafification
open AlgebraicGeometry.SheafOfModules (IsInvertible IsFiniteLocallyFreeOfRank
  tensorLeftFunctorUniversal)

universe v u w

namespace Stacks.SheafRankOne

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}} {L N : PresheafOfModulesOfCommRing.{w} 𝒪}

/-- Contraction of `L` against a section `n` of `N` over `U`, along a morphism `η : L ⊗ N ⟶ 𝒪` of
presheaves of modules: the `𝒪(U)`-linear map `l ↦ η_U(l ⊗ n)`. Unlike the sibling file's
contraction this takes a plain morphism, not an isomorphism, which is what the sheaf-level
hypothesis supplies. The object `U` is explicit on purpose: with it implicit the term
`contract η (N.map f n)` does not elaborate, since `N.map f n` has type
`↑((ModuleCat.restrictScalars _).obj (N.obj V))` and unification cannot read the object off it. -/
noncomputable def contract (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (U : Cᵒᵖ) (n : N.obj U) : L.obj U →ₗ[𝒪.obj U] 𝒪.obj U :=
  (η.app U).hom ∘ₗ (TensorProduct.mk (𝒪.obj U) (L.obj U) (N.obj U)).flip n

/-- `contract` computed on a section, by definition. -/
theorem contract_apply (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (U : Cᵒᵖ) (n : N.obj U) (l : L.obj U) :
    contract η U n l = (η.app U).hom (l ⊗ₜ n) :=
  rfl

/-- Contraction commutes with restriction: restricting the value of a contraction is the
contraction of the restrictions. This is the naturality of `η`, and it is what makes the
trivializations produced below restriction-compatible. -/
theorem map_contract (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (l : L.obj U) :
    𝒪.map f (contract η U n l) = contract η V (N.map f n) (L.map f l) :=
  (PresheafOfModules.naturality_apply η f (l ⊗ₜ[𝒪.obj U] n)).symm

/-- A unit value of a contraction stays a unit after restriction: ring maps preserve units, and
`map_contract` identifies the restricted value with the contraction of the restrictions. -/
theorem isUnit_contract_map (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract η U n m)) :
    IsUnit (contract η V (N.map f n) (L.map f m)) :=
  map_contract η f n m ▸ hu.map (𝒪.map f).hom

/-- Pairing against a fixed section `m` of `L`: the `𝒪(U)`-linear map
`L(U) ⊗ N(U) → L(U)`, `l ⊗ n ↦ η_U(m ⊗ n) • l`. Written as `L ⊗ N → L ⊗ 𝒪 → L` so that
well-definedness is nothing but functoriality of the tensor product. This is the engine of the
injectivity argument: applied to a pure tensor known to vanish, it produces `η(m ⊗ n) • l = 0`. -/
noncomputable def pairLeft (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (U : Cᵒᵖ) (m : L.obj U) :
    (L.obj U) ⊗[𝒪.obj U] (N.obj U) →ₗ[𝒪.obj U] L.obj U :=
  (TensorProduct.rid (𝒪.obj U) (L.obj U)).toLinearMap ∘ₗ
    LinearMap.lTensor (L.obj U)
      ((η.app U).hom ∘ₗ TensorProduct.mk (𝒪.obj U) (L.obj U) (N.obj U) m)

/-- `pairLeft` computed on a pure tensor. -/
theorem pairLeft_tmul (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (U : Cᵒᵖ) (m : L.obj U) (l : L.obj U) (n : N.obj U) :
    pairLeft η U m (l ⊗ₜ n) = contract η U n m • l := by
  simp only [pairLeft, contract, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rfl

/-- **Contraction against a section with a unit value is surjective, stably under restriction.**
If contracting `n : N(U)` against some `m : L(U)` gives a unit of `𝒪(U)`, then over every `V`
receiving a map from `U` the contraction against `n|_V` is surjective: its image contains the
restricted unit, hence is the unit ideal. Sectionwise; no locality and no sheaf condition. -/
theorem surjective_contract (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract η U n m)) :
    Function.Surjective (contract η V (N.map f n)) :=
  LinearMap.range_eq_top.mp (Ideal.eq_top_of_isUnit_mem _
    (LinearMap.mem_range.mpr ⟨L.map f m, (map_contract η f n m).symm⟩)
    (hu.map (𝒪.map f).hom))

/-- **Contraction against a section with a unit value is injective, stably under restriction.**
This is the step that replaces the sibling file's appeal to invertibility of the module of
sections, which is unavailable at the sheaf level. Suppose `η` is locally injective and `L` is
separated. If `η_V(l ⊗ n|_V) = 0` then `l ⊗ n|_V` vanishes locally on `V`; applying `pairLeft` to
that vanishing pure tensor gives `η(m ⊗ n) • l = 0` locally, where `η(m ⊗ n)` is a unit, so `l`
vanishes locally; separatedness of `L` then gives `l = 0`. -/
theorem eq_zero_of_contract_eq_zero
    (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map η))
    (hsep : Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj L))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract η U n m))
    (l : L.obj V) (hl : contract η V (N.map f n) l = 0) : l = 0 := by
  have hS := hinj.equalizerSieve_mem (l ⊗ₜ[𝒪.obj V] (N.map f n)) 0 (by
    rw [map_zero]
    exact hl)
  refine hsep V.unop _ hS l 0 fun W g hg ↦ ?_
  have hg' : (L ⊗ N).map g.op (l ⊗ₜ[𝒪.obj V] (N.map f n))
      = (L ⊗ N).map g.op (0 : (L ⊗ N).obj V) := hg
  have h0 : (L ⊗ N).map g.op (l ⊗ₜ[𝒪.obj V] (N.map f n)) = 0 := by
    rw [hg', map_zero]
  have hum : IsUnit (contract η (op W) (N.map g.op (N.map f n)) (L.map g.op (L.map f m))) :=
    isUnit_contract_map η g.op (N.map f n) (L.map f m) (isUnit_contract_map η f n m hu)
  have h1 : contract η (op W) (N.map g.op (N.map f n)) (L.map g.op (L.map f m)) •
      L.map g.op l = 0 :=
    (pairLeft_tmul η (op W) (L.map g.op (L.map f m)) (L.map g.op l)
        (N.map g.op (N.map f n))).symm.trans
      ((congrArg (pairLeft η (op W) (L.map g.op (L.map f m))) h0).trans
        (map_zero (pairLeft η (op W) (L.map g.op (L.map f m)))))
  rw [map_zero]
  show L.map g.op l = 0
  exact hum.smul_left_cancel.mp (h1.trans (smul_zero _).symm)

/-- Contraction against a section with a unit value is bijective, over every restriction: the
two halves are `surjective_contract` and `eq_zero_of_contract_eq_zero`. -/
theorem bijective_contract
    (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map η))
    (hsep : Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj L))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract η U n m)) :
    Function.Bijective (contract η V (N.map f n)) :=
  ⟨fun a b hab ↦ sub_eq_zero.mp (eq_zero_of_contract_eq_zero η hinj hsep f n m hu (a - b)
      (by rw [map_sub, hab, sub_self])),
    surjective_contract η f n m hu⟩

/-- The contraction of `bijective_contract`, promoted to a linear equivalence
`L(V) ≃ₗ 𝒪(V)`. -/
noncomputable def contractEquiv
    (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map η))
    (hsep : Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj L))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract η U n m)) :
    L.obj V ≃ₗ[𝒪.obj V] 𝒪.obj V :=
  .ofBijective _ (bijective_contract η hinj hsep f n m hu)

end Sections

section Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-- The underlying presheaf of abelian groups of a sheaf of modules is separated: two sections
agreeing on a covering are equal. This is the input that `eq_zero_of_contract_eq_zero` uses to
pass from local vanishing to vanishing. -/
@[sga "2 XIV 1.8.2.1" "special case"]
theorem isSeparated_val (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj L.val) :=
  L.isSheaf.isSeparated

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **What sheaf-level invertibility supplies.** An invertible sheaf of modules `L` carries a
presheaf of modules `N` and a morphism of presheaves of modules `η : L.val ⊗ N ⟶ 𝒪` which is a
local isomorphism. Only essential surjectivity of the tensor functor is used: `N` is the underlying
presheaf of a preimage of the structure sheaf, and `η` is the sheafification unit followed by the
comparison isomorphism, which sheafification inverts. This is the single place where the library
predicate `AlgebraicGeometry.SheafOfModules.IsInvertible` is unfolded, and it is the whole of the
hypothesis that the rest of the file consumes. -/
theorem exists_localIso_of_isInvertible (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    [IsInvertible 𝒪 h𝒪 L] :
    ∃ (N : PresheafOfModulesOfCommRing.{w} 𝒪)
      (η : (L.val : PresheafOfModulesOfCommRing.{w} 𝒪) ⊗ N ⟶
        𝟙_ (PresheafOfModulesOfCommRing.{w} 𝒪)),
      J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map η) := by
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w}
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj L
  have hF : F.IsEquivalence := inferInstance
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty (F.obj M ≅ SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) :=
    ⟨_, ⟨F.objObjPreimageIso _⟩⟩
  have h1 : IsIso ((sheafify 𝒪 h𝒪).map ((tensorLeftFunctorUniversal 𝒪 h𝒪 L).ι.app M)) :=
    isIso_sheafify_map_toSheafify 𝒪 h𝒪 (L.val ⊗ M.val)
  have h3 : IsIso ((sheafify 𝒪 h𝒪).map e.hom.val) :=
    inferInstanceAs (IsIso ((sheafify 𝒪 h𝒪).mapIso
      ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪)).mapIso e)).hom)
  have hEq := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := J) (𝟙 (structureSheaf 𝒪 h𝒪).obj)
  refine ⟨M.val, (tensorLeftFunctorUniversal 𝒪 h𝒪 L).ι.app M ≫ e.hom.val, ?_⟩
  refine (MorphismProperty.inverseImage_iff J.W
    (PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)) _).1 ?_
  show J.W.inverseImage (PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj) _
  refine MorphismProperty.comp_mem _ _ _ ?_ ?_
  all_goals rw [hEq]
  exacts [h1, h3]

end Invertible

section Trivializations

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {L N : PresheafOfModulesOfCommRing.{max u v w} 𝒪}

/-- **The sectionwise trivialization.** Over an object `V` carrying sections `n` of `N` and `m` of
`L` whose contraction is a unit, contraction against `n` is a restriction-compatible family of
isomorphisms `L(W) ≃ 𝒪(W)`, one for each object `W` lying over `V` — that is, a
`Stacks.SheafDescent.Trivialization`. Compatibility with restriction is `map_contract`, after
rewriting `N.map (h' ≫ h).op n` with `PresheafOfModules.map_comp_apply`. -/
noncomputable def trivialization
    (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{max u v w} 𝒪))
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map η))
    (hsep : Presheaf.IsSeparated J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).obj L))
    {V : C} (n : N.obj (op V)) (m : L.obj (op V)) (hu : IsUnit (contract η (op V) n m)) :
    Stacks.SheafDescent.Trivialization 𝒪 L V where
  θ W h := contractEquiv η hinj hsep h.op n m hu
  θ_naturality {W W'} h h' x := by
    change contract η (op W') (N.map (h' ≫ h).op n) (L.map h'.op x)
      = 𝒪.map h'.op (contract η (op W) (N.map h.op n) x)
    rw [op_comp, PresheafOfModules.map_comp_apply]
    exact (map_contract η h'.op (N.map h.op n) x).symm

/-- **A sectionwise trivialization over `V` is an isomorphism of sheaves of modules on the slice
site.** This is the converse of `Stacks.SheafDescent.Trivialization.ofIso`, and it is what turns
the sectionwise statement of clause 2 into the shape that
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` is phrased in. The components are the
trivialization's linear equivalences read as `ModuleCat` isomorphisms; naturality is
`θ_naturality` after rewriting with `CategoryTheory.Over.w`, and the result is lifted from
presheaves of modules to sheaves of modules because `SheafOfModules.forget` is fully faithful. -/
noncomputable def overIso (M : SheafOfModules.{max u v w} (structureSheaf 𝒪 h𝒪)) {V : C}
    (t : Stacks.SheafDescent.Trivialization 𝒪 M.val V) :
    M.over V ≅ SheafOfModules.unit ((structureSheaf 𝒪 h𝒪).over V) :=
  (SheafOfModules.forget _).preimageIso
    (PresheafOfModules.isoMk (fun Y ↦ (t.θ Y.unop.left Y.unop.hom).toModuleIso)
      (fun {Y _} f ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
        have h := t.θ_naturality (unop Y).hom f.unop.left x
        rw [Over.w f.unop] at h
        exact h)))

/-- A sheaf of modules sectionwise trivial on a family of objects covering the terminal object is
locally trivial in the sense of `Stacks.SheafOfModules.Invertible.IsLocallyTrivial`. -/
theorem isLocallyTrivial_of_trivialization
    (M : SheafOfModules.{max u v w} (structureSheaf 𝒪 h𝒪)) {I : Type u} {Y : I → C}
    (hY : J.CoversTop Y) (t : ∀ i, Stacks.SheafDescent.Trivialization 𝒪 M.val (Y i)) :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial M :=
  ⟨I, Y, hY, fun i ↦ ⟨overIso 𝒪 h𝒪 M (t i)⟩⟩

variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **A sheaf of modules sectionwise trivial on a family covering the terminal object is finite
locally free of rank one.** The packaging step: a trivialization is a one-element local basis, and
the draft class is bridged to the library class by
`Stacks.InvertibleLocallyFree.isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank`,
so this lands on the rank-indexed class in the library namespace. -/
theorem isFiniteLocallyFreeOfRank_one_of_trivialization
    (M : SheafOfModules.{max u v w} (structureSheaf 𝒪 h𝒪)) {I : Type u} {Y : I → C}
    (hY : J.CoversTop Y) (t : ∀ i, Stacks.SheafDescent.Trivialization 𝒪 M.val (Y i)) :
    IsFiniteLocallyFreeOfRank M 1 :=
  have := isLocallyTrivial_of_trivialization 𝒪 h𝒪 M hY t
  (Stacks.InvertibleLocallyFree.isFiniteLocallyFreeOfRank_iff_invertible_isFiniteLocallyFreeOfRank
      𝒪 h𝒪 M 1).mpr
    (Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial M)

end Trivializations

section RingedSpace

open AlgebraicGeometry

variable {X : RingedSpace.{u, u}} {L N : PresheafOfModulesOfCommRing.{u} X.presheaf}

/-- **The one place the stalk hypothesis is used.** Let `η : L ⊗ N ⟶ 𝒪` be locally surjective on
a ringed space and let `x` be a point whose stalk `𝒪_{X, x}` is a local ring. Then on some open
neighbourhood of `x` there are sections `n` of `N` and `m` of `L` whose contraction is a unit.
Local surjectivity at the global section `1` gives an open `V₀ ∋ x` and a finite sum
`1 = ∑ᵢ η(mᵢ ⊗ nᵢ)` in `𝒪(V₀)`; locality of the stalk forces a single summand to have unit germ at
`x` (`IsLocalRing.exists_of_isUnit_sum`), and a unit germ is a unit on a smaller open
(`AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ`). -/
theorem exists_isUnit_contract
    (η : L ⊗ N ⟶ 𝟙_ (PresheafOfModulesOfCommRing.{u} X.presheaf))
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (structureRingPresheaf X.presheaf)).map η))
    (x : X) [IsLocalRing (X.presheaf.stalk x)] :
    ∃ (V : Opens X) (_ : x ∈ V) (n : N.obj (op V)) (m : L.obj (op V)),
      IsUnit (contract η (op V) n m) := by
  obtain ⟨V₀, f, ⟨t, ht⟩, hxV₀⟩ := (Opens.mem_grothendieckTopology _).1
    (hsurj.imageSieve_mem (1 : (structureRingPresheaf X.presheaf).obj (op ⊤))) x (Opens.mem_top x)
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  have ht'' : (η.app (op V₀)).hom t = (1 : X.presheaf.obj (op V₀)) :=
    ht.trans (PresheafOfModules.unit_map_one _ f.op)
  have ht' : (1 : X.presheaf.obj (op V₀)) = ∑ i ∈ S, contract η (op V₀) i.2 i.1 := by
    rw [← ht'', hS]
    exact map_sum (η.app (op V₀)).hom _ S
  have hsum : IsUnit (∑ i ∈ S, X.presheaf.germ V₀ x hxV₀ (contract η (op V₀) i.2 i.1)) := by
    rw [← map_sum, ← ht', map_one]
    exact isUnit_one
  obtain ⟨⟨m, n⟩, -, hu⟩ := IsLocalRing.exists_of_isUnit_sum hsum
  obtain ⟨V, i, hxV, hu'⟩ := X.isUnit_res_of_isUnit_germ V₀ _ x hxV₀ hu
  exact ⟨V, hxV, N.map i.op n, L.map i.op m, map_contract η i.op n m ▸ hu'⟩

/-- **Clause 2 of Stacks Tag 0B8M, in trivialization form.** On a ringed space all of whose stalks
`𝒪_{X, x}` are local rings, a sheaf of modules `M` that is invertible in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible` is sectionwise trivial on a family of opens
covering the space: for each point an open containing it, carrying a restriction-compatible family
of isomorphisms `M(W) ≃ 𝒪(W)` for every open `W` inside it. The trivialization is contraction
against a section of the partner module `N` of `exists_localIso_of_isInvertible`. -/
theorem exists_cover_trivialization_of_isInvertible
    (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology X) (structureRingPresheaf X.presheaf))
    (M : SheafOfModules.{u} (structureSheaf X.presheaf h𝒪)) [IsInvertible X.presheaf h𝒪 M]
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    ∃ V : X → Opens X, iSup V = ⊤ ∧
      ∀ x, Nonempty (Stacks.SheafDescent.Trivialization X.presheaf M.val (V x)) := by
  obtain ⟨N', η, hW⟩ := exists_localIso_of_isInvertible X.presheaf h𝒪 M
  obtain ⟨hinj, hsurj⟩ := ((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 hW
  choose V hxV n m hu using fun x : X ↦ exists_isUnit_contract η hsurj x
  exact ⟨V, eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩, fun x ↦
    ⟨trivialization X.presheaf η hinj (isSeparated_val X.presheaf h𝒪 M) (n x) (m x) (hu x)⟩⟩

/-- **Clause 2 of Stacks Tag 0B8M.** On a ringed space all of whose stalks `𝒪_{X, x}` are local
rings, a sheaf of modules invertible in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible` is finite locally free of rank one. The hypothesis
is the sheaf-level invertibility predicate that this repository's consumers carry, and the
conclusion is the rank-indexed class in the library namespace. The stalk hypothesis cannot be
dropped: clause 3 of the tag is a counterexample, and it is not formalized here. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    (h𝒪 : Presheaf.IsSheaf (Opens.grothendieckTopology X) (structureRingPresheaf X.presheaf))
    (M : SheafOfModules.{u} (structureSheaf X.presheaf h𝒪)) [IsInvertible X.presheaf h𝒪 M]
    [∀ x : X, IsLocalRing (X.presheaf.stalk x)] :
    IsFiniteLocallyFreeOfRank (R := structureSheaf X.presheaf h𝒪) M 1 := by
  obtain ⟨V, hV, t⟩ := exists_cover_trivialization_of_isInvertible h𝒪 M
  exact isFiniteLocallyFreeOfRank_one_of_trivialization X.presheaf h𝒪 M
    ((Opens.coversTop_iff _ V).mpr (TopologicalSpace.IsOpenCover.mk hV)) fun x ↦ (t x).some

end RingedSpace

section Scheme

open AlgebraicGeometry

/-- **Clause 2 of Stacks Tag 0B8M on a scheme, with no hypothesis on the stalks.** An invertible
sheaf of modules on a scheme is finite locally free of rank one; the stalks of a scheme are local
rings, so the hypothesis of the ringed-space statement is automatic. The structure sheaf is spelled
`X.ringCatSheaf`, which is how `AlgebraicGeometry.SheafOfModules.IsInvertible` is applied elsewhere
in this repository. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme (X : Scheme.{u})
    (M : SheafOfModules.{u} X.ringCatSheaf) [IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1 :=
  isFiniteLocallyFreeOfRank_one_of_isInvertible (X := X.toRingedSpace) X.ringCatSheaf.2 M

end Scheme

end Stacks.SheafRankOne

end
