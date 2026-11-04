module

public import StacksFrontier.AlgebraicGeometry.InternalHom.Basic
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.PicardGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An invertible module is locally free of rank one when the stalks are local

Stacks Tag 0B8M has three clauses: a locally free module of rank one on a ringed space is
invertible; the converse holds when all stalks `𝒪_{X, x}` are local rings; and the converse
fails without that hypothesis, as a one-point space whose ring has nontrivial Picard group
shows. **This file is about clause 2 only**, the converse under stalk-locality. Clause 1,
modulo a descent step, is
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean`; clause 3 is untouched
everywhere.

The invertibility hypothesis used here is that tensoring on the left by `L` is an equivalence
of the category of **presheaves** of modules, `(MonoidalCategory.tensorLeft L).IsEquivalence`.
See "What is not done" for why this is not the same hypothesis as
`AlgebraicGeometry.SheafOfModules.IsInvertible`.

## The route, and where the stalk hypothesis enters

The tensor product of presheaves of modules is computed sectionwise, so the evaluation
isomorphism `L ⊗ L* ≅ 𝒪` of `Stacks.InternalHom.dualIso` gives, over **every** open `U` at
once, an `𝒪(U)`-linear isomorphism `L(U) ⊗_{𝒪(U)} L*(U) ≅ 𝒪(U)`. Hence `L(U)` is an invertible
`𝒪(U)`-module in Mathlib's sense, `Module.Invertible`, and so finite, projective and of finite
presentation over `𝒪(U)`. That already supplies the finite-presentation input that the source's
proof of Tag 0B8M takes from Tag 0B8K, and it is unconditional: no stalk hypothesis, no local
ring, no sheaf condition.

The stalk hypothesis is used exactly once, and only to choose a trivializing section. Writing
`1 ∈ 𝒪(U)` as a finite sum `∑ᵢ e(mᵢ ⊗ nᵢ)` of contractions of pure tensors and passing to
germs at a point `x`, locality of `𝒪_{X, x}` forces a **single** index `j` whose germ
`e(mⱼ ⊗ nⱼ)_x` is a unit; a unit germ is a unit on some smaller open `V ∋ x`
(`AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ`). On that `V` the contraction
`l ↦ e(l ⊗ nⱼ|_V)` hits a unit, so its image is the unit ideal, so it is surjective — and a
surjective endomorphism-like map out of an invertible module is bijective
(`Module.Invertible.bijective_of_surjective`). Since the restriction of a unit is a unit, the
same section `nⱼ|_V` works simultaneously over every open `W ≤ V`, and `map_contract` records
that these isomorphisms commute with restriction. So `L` is trivialized on a neighbourhood of
every point, which is the "upgrade to a neighbourhood" of the source's final step.

Note what this route does **not** need: the stalk of a tensor product is never identified with
the tensor product of the stalks (Tag 01CB), and no module structure on a stalk is used. Only
the ring `𝒪_{X, x}` and its locality appear.

## Main definitions

* `Stacks.InvertibleRankOne.tensorEquiv`: an isomorphism `L ⊗ N ≅ 𝒪` of presheaves of modules,
  read over a single object of the site as a linear equivalence
  `L(U) ⊗_{𝒪(U)} N(U) ≃ₗ 𝒪(U)`.
* `Stacks.InvertibleRankOne.contract`: contraction against a section `n` of `N`, the linear map
  `L(U) → 𝒪(U)`, `l ↦ tensorEquiv e U (l ⊗ₜ n)`.
* `Stacks.InvertibleRankOne.contractEquiv`: that contraction promoted to a linear equivalence
  where it is bijective.

## Main results

* `Stacks.InvertibleRankOne.module_invertible_obj` and
  `Stacks.InvertibleRankOne.module_invertible_obj_of_tensorLeft`: the sections of an invertible
  presheaf of modules form an invertible module over the sections of the structure presheaf.
  Unconditional; this is the sectionwise content of Tag 0B8K.
* `Stacks.InvertibleRankOne.module_finitePresentation_obj_of_tensorLeft`: those sections are of
  finite presentation — the input Tag 0B8M's proof takes from Tag 0B8K.
* `Stacks.InvertibleRankOne.nonempty_linearEquiv_obj_of_tensorLeft` and
  `Stacks.InvertibleRankOne.finrank_obj_eq_one_of_tensorLeft`: over an object whose ring of
  sections is local, those sections are free of rank one. This is the algebraic crux of clause
  2, in the form in which Stacks cites Section 0AFW.
* `Stacks.InvertibleRankOne.bijective_contract`: contraction against a section whose
  contraction with some `m` is a unit is bijective, over every further restriction.
* `Stacks.InvertibleRankOne.exists_trivialization_of_tensorLeft`: on a ringed space, at a point
  whose stalk is a local ring, an invertible presheaf of modules is trivialized — by one
  explicit contraction, compatibly over all smaller opens — on some open neighbourhood inside
  any given open.
* `Stacks.InvertibleRankOne.exists_cover_trivialization_of_tensorLeft`: **clause 2 of Tag 0B8M
  in presheaf form.** On a ringed space all of whose stalks are local rings, an invertible
  presheaf of modules has a family of opens covering the space, each carrying a section of the
  dual whose contraction is an isomorphism over that open and over every smaller one.

## Implementation notes

**Transparency gotchas.** Three, all handled with ordinary tactics; no compiler option is set
anywhere in this file.

* `contract` takes the site object as an **explicit** argument. With it implicit, the term
  `contract e (N.map f n)` does not elaborate: `N.map f n` has type
  `↑((ModuleCat.restrictScalars _).obj (N.obj V))`, which is `↑(N.obj V)` only up to unfolding
  `restrictScalars`, so unification cannot read the object off the argument's type.
* For the same reason `rw [map_tensorEquiv_tmul]` fails in any goal that already mentions a
  restricted section: the rewritten application is not type-correct at `implicit`
  transparency. Every restriction-compatibility step is therefore term-mode —
  `map_contract` is literally `map_tensorEquiv_tmul`, and the final step of
  `exists_trivialization` transports the unit hypothesis with `▸` rather than `rw`.
* The internal hom instance of `Stacks.InternalHom` **is** found by instance search for
  `PresheafOfModulesOfCommRing X.presheaf` on a ringed space, with no bridging definition:
  `TopologicalSpace.Opens ↑↑X.toPresheafedSpace` is a `SmallCategory` in the universe of the
  sections, which is precisely the constraint that instance imposes. This is unlike the
  `AlgebraicGeometry.Scheme.PresheafOfModules` spelling, which needs
  `Stacks.InternalHom.schemeMonoidalClosed`.

**Why `RingedSpace` and not an arbitrary site.** The sectionwise half of the file is stated for
an arbitrary category, with no sheaf condition. Only the passage from a unit germ to a unit on a
smaller open needs a topological space, and Mathlib packages that step as
`AlgebraicGeometry.RingedSpace.isUnit_res_of_isUnit_germ`; it is a filtered-colimit statement
and would hold for a bare presheaf of rings, but restating it that way would duplicate a
Mathlib lemma for no gain. Stacks Tag 0B8M is itself stated for a ringed space.

**No Stacks attribute.** None of the three clauses of Tag 0B8M is closed unconditionally in
this repository, so no Stacks attribute for Tag 0B8M is attached anywhere in this file.

## What is not done

* **The hypothesis is presheaf-level invertibility.** `(tensorLeft L).IsEquivalence` is about
  the monoidal category `PresheafOfModulesOfCommRing R`. The repository's
  `AlgebraicGeometry.SheafOfModules.IsInvertible` is instead equivalent to
  `(tensorLeftFunctor O hO L).IsEquivalence`, and that functor is
  `forget ⋙ tensorLeft L.val ⋙ sheafify` — the **sheafified** tensor product. Nothing at this
  Mathlib pin compares the two, in either direction, and nothing here does either. So clause 2
  is **not** available starting from the library predicate. Closing that gap needs a monoidal
  structure on `SheafOfModules` and the comparison of the two tensor functors, which is the
  same missing input that `Stacks.InternalHom.sheafOfModulesMonoidalClosed` isolates.
* **The conclusion is not `IsFiniteLocallyFreeOfRank L 1`.** What is produced is a cover
  together with contractions that are isomorphisms sectionwise and compatibly with restriction.
  Turning that into `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1` needs a
  restriction functor for presheaves of modules along `Over V ⥤ Opens X` (or along
  `Opens V ⥤ Opens X`) together with the `SheafOfModules.LocalGeneratorsData` packaging; none
  of that is built here.
* Clause 1 of Tag 0B8M is not reproved here, and clause 3 — the one-point counterexample — is
  not formalized anywhere in the repository.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TensorProduct TopologicalSpace

universe u v₁ u₁

namespace Stacks.InvertibleRankOne

section Sections

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {L N : PresheafOfModulesOfCommRing.{u} R}

/-- An isomorphism `L ⊗ N ≅ 𝒪` of presheaves of modules, evaluated at one object of the site.
The tensor product of presheaves of modules is computed sectionwise, so this is an honest
linear equivalence `L(U) ⊗_{𝒪(U)} N(U) ≃ₗ 𝒪(U)`. -/
noncomputable def tensorEquiv
    (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R)) (U : Cᵒᵖ) :
    (L.obj U) ⊗[R.obj U] (N.obj U) ≃ₗ[R.obj U] R.obj U :=
  ((PresheafOfModules.evaluation _ U).mapIso e).toLinearEquiv

/-- `tensorEquiv` commutes with restriction, on pure tensors. This is the naturality of the
underlying morphism of presheaves of modules. -/
theorem map_tensorEquiv_tmul
    (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R)) {U V : Cᵒᵖ} (f : U ⟶ V)
    (l : L.obj U) (n : N.obj U) :
    R.map f (tensorEquiv e U (l ⊗ₜ n)) = tensorEquiv e V (L.map f l ⊗ₜ N.map f n) :=
  (PresheafOfModules.naturality_apply e.hom f (l ⊗ₜ[R.obj U] n)).symm

/-- **The sections of an invertible presheaf of modules are an invertible module.** Given an
isomorphism `L ⊗ N ≅ 𝒪`, the `𝒪(U)`-module `L(U)` is invertible in the sense of
`Module.Invertible`, for every object `U`. No locality and no sheaf condition are used. -/
theorem module_invertible_obj (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R)) (U : Cᵒᵖ) :
    Module.Invertible (R.obj U) (L.obj U) :=
  .left (tensorEquiv e U)

/-- The sections of an invertible presheaf of modules are of finite presentation over the
sections of the structure presheaf: an invertible module is finite and projective. -/
theorem module_finitePresentation_obj
    (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R)) (U : Cᵒᵖ) :
    Module.FinitePresentation (R.obj U) (L.obj U) :=
  have := module_invertible_obj e U
  Module.finitePresentation_of_projective ..

/-- **The algebraic crux of clause 2 of Tag 0B8M.** Over an object whose ring of sections is
local, the sections of an invertible presheaf of modules are free of rank one: an invertible
module over a local ring is isomorphic to the ring, the Picard group of a local ring being
trivial. -/
@[ega "I 2.4.8" "partial"]
theorem nonempty_linearEquiv_obj (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    (U : Cᵒᵖ) [IsLocalRing (R.obj U)] : Nonempty (L.obj U ≃ₗ[R.obj U] R.obj U) :=
  have := module_invertible_obj e U
  Module.Invertible.free_iff_linearEquiv.mp inferInstance

/-- The rank in `nonempty_linearEquiv_obj`, read off as a `finrank`. -/
theorem finrank_obj_eq_one (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    (U : Cᵒᵖ) [IsLocalRing (R.obj U)] : Module.finrank (R.obj U) (L.obj U) = 1 :=
  have := module_invertible_obj e U
  have : Module.Free (R.obj U) (L.obj U) := inferInstance
  Module.Invertible.finrank_eq_one _ _

/-- Contraction of `L` against a section `n` of `N` over `U`, along an isomorphism
`L ⊗ N ≅ 𝒪`. -/
noncomputable def contract (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    (U : Cᵒᵖ) (n : N.obj U) : L.obj U →ₗ[R.obj U] R.obj U :=
  (tensorEquiv e U).toLinearMap ∘ₗ (TensorProduct.mk (R.obj U) (L.obj U) (N.obj U)).flip n

/-- The contraction against `n` sends `l` to the image of `l ⊗ₜ n` under `tensorEquiv e U`. -/
theorem contract_apply (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    (U : Cᵒᵖ) (n : N.obj U) (l : L.obj U) :
    contract e U n l = tensorEquiv e U (l ⊗ₜ n) :=
  rfl

/-- Contraction commutes with restriction: restricting the value of a contraction is the
contraction of the restrictions. -/
theorem map_contract (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (l : L.obj U) :
    R.map f (contract e U n l) = contract e V (N.map f n) (L.map f l) :=
  map_tensorEquiv_tmul e f l n

/-- **Contraction against a section with a unit value is an isomorphism, stably under
restriction.** If contracting `n : N(U)` against some `m : L(U)` gives a unit of `𝒪(U)`, then
over every `V` receiving a map from `U` the contraction against `n|_V` is bijective: its image
contains the restricted unit, hence is the unit ideal, and a surjection out of an invertible
module is bijective. -/
theorem bijective_contract (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract e U n m)) :
    Function.Bijective (contract e V (N.map f n)) :=
  have := module_invertible_obj e V
  Module.Invertible.bijective_of_surjective (LinearMap.range_eq_top.mp
    (Ideal.eq_top_of_isUnit_mem _
      (LinearMap.mem_range.mpr ⟨L.map f m, (map_contract e f n m).symm⟩)
      (hu.map (R.map f).hom)))

/-- The contraction of `bijective_contract`, promoted to a linear equivalence
`L(V) ≃ₗ 𝒪(V)`. -/
noncomputable def contractEquiv (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} R))
    {U V : Cᵒᵖ} (f : U ⟶ V) (n : N.obj U) (m : L.obj U) (hu : IsUnit (contract e U n m)) :
    L.obj V ≃ₗ[R.obj V] R.obj V :=
  .ofBijective _ (bijective_contract e f n m hu)

end Sections

section Invertible

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (L : PresheafOfModulesOfCommRing.{u} R) [(tensorLeft L).IsEquivalence]

/-- The evaluation isomorphism of an invertible presheaf of modules, read over one object of the
site: `L(U) ⊗_{𝒪(U)} (L*)(U) ≃ₗ 𝒪(U)`. -/
noncomputable def dualTensorEquiv (U : Cᵒᵖ) :
    (L.obj U) ⊗[R.obj U] ((Stacks.InternalHom.dual L).obj U) ≃ₗ[R.obj U] R.obj U :=
  tensorEquiv (Stacks.InternalHom.dualIso L) U

/-- The sections of a presheaf of modules whose left tensoring is an equivalence form an
invertible module over the sections of the structure presheaf. -/
theorem module_invertible_obj_of_tensorLeft (U : Cᵒᵖ) :
    Module.Invertible (R.obj U) (L.obj U) :=
  module_invertible_obj (Stacks.InternalHom.dualIso L) U

/-- **Finite presentation of an invertible presheaf of modules, sectionwise.** This is the input
that the source's proof of Tag 0B8M takes from Tag 0B8K. -/
theorem module_finitePresentation_obj_of_tensorLeft (U : Cᵒᵖ) :
    Module.FinitePresentation (R.obj U) (L.obj U) :=
  module_finitePresentation_obj (Stacks.InternalHom.dualIso L) U

/-- Over an object whose ring of sections is local, an invertible presheaf of modules is free of
rank one. -/
theorem nonempty_linearEquiv_obj_of_tensorLeft (U : Cᵒᵖ) [IsLocalRing (R.obj U)] :
    Nonempty (L.obj U ≃ₗ[R.obj U] R.obj U) :=
  nonempty_linearEquiv_obj (Stacks.InternalHom.dualIso L) U

/-- The rank in `nonempty_linearEquiv_obj_of_tensorLeft`, read off as a `finrank`. -/
theorem finrank_obj_eq_one_of_tensorLeft (U : Cᵒᵖ) [IsLocalRing (R.obj U)] :
    Module.finrank (R.obj U) (L.obj U) = 1 :=
  finrank_obj_eq_one (Stacks.InternalHom.dualIso L) U

end Invertible

section RingedSpace

open AlgebraicGeometry

variable {X : RingedSpace.{u}} {L N : PresheafOfModulesOfCommRing.{u} X.presheaf}

/-- **Trivialization on a neighbourhood of a point whose stalk is a local ring.** Let
`L ⊗ N ≅ 𝒪` on a ringed space and let `x` lie in an open `U`. If `𝒪_{X, x}` is a local ring
then there are an open `V` with `x ∈ V ≤ U` and a section `n` of `N` over `V` such that
contraction against `n` is an isomorphism `L(W) ≃ 𝒪(W)` for every open `W ≤ V` — the one place
where locality of the stalk is used, and the step that upgrades the pointwise statement to a
neighbourhood. By `map_contract` these isomorphisms commute with restriction. -/
theorem exists_trivialization
    (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} X.presheaf))
    (U : Opens ↑↑X.toPresheafedSpace) (x : ↑↑X.toPresheafedSpace) (hx : x ∈ U)
    [IsLocalRing (X.presheaf.stalk x)] :
    ∃ (V : Opens ↑↑X.toPresheafedSpace) (_ : V ⟶ U) (_ : x ∈ V) (n : N.obj (op V)),
      ∀ (W : Opens ↑↑X.toPresheafedSpace) (j : W ⟶ V),
        Function.Bijective (contract e (op W) (N.map j.op n)) := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset ((tensorEquiv e (op U)).symm 1)
  have h1 : (1 : X.presheaf.obj (op U)) = ∑ i ∈ S, contract e (op U) i.2 i.1 := by
    conv_lhs => rw [← (tensorEquiv e (op U)).apply_symm_apply 1, hS]
    exact map_sum ..
  have h2 : IsUnit (∑ i ∈ S, X.presheaf.germ U x hx (contract e (op U) i.2 i.1)) := by
    rw [← map_sum, ← h1, map_one]
    exact isUnit_one
  obtain ⟨⟨m, n⟩, _, hu⟩ := IsLocalRing.exists_of_isUnit_sum h2
  obtain ⟨V, i, hxV, hu'⟩ := X.isUnit_res_of_isUnit_germ U _ x hx hu
  exact ⟨V, i, hxV, N.map i.op n, fun W j ↦
    bijective_contract e j.op (N.map i.op n) (L.map i.op m) (map_contract e i.op n m ▸ hu')⟩

/-- **Trivialization on a cover.** If every stalk of a ringed space is a local ring, an
isomorphism `L ⊗ N ≅ 𝒪` trivializes `L` on a family of opens covering the space: for each point
an open containing it, carrying a section of `N` whose contraction is an isomorphism over that
open and over every smaller one. -/
theorem exists_cover_trivialization
    (e : L ⊗ N ≅ 𝟙_ (PresheafOfModulesOfCommRing.{u} X.presheaf))
    [∀ x : ↑↑X.toPresheafedSpace, IsLocalRing (X.presheaf.stalk x)] :
    ∃ (V : ↑↑X.toPresheafedSpace → Opens ↑↑X.toPresheafedSpace)
      (n : ∀ x, N.obj (op (V x))), iSup V = ⊤ ∧
      ∀ (x : ↑↑X.toPresheafedSpace) (W : Opens ↑↑X.toPresheafedSpace) (j : W ⟶ V x),
        Function.Bijective (contract e (op W) (N.map j.op (n x))) := by
  choose V _ hxV n hn using fun x : ↑↑X.toPresheafedSpace ↦
    exists_trivialization e ⊤ x (Opens.mem_top x)
  exact ⟨V, n, eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩, hn⟩

variable (L) in
/-- `exists_trivialization` for an invertible presheaf of modules, the isomorphism being the
evaluation `L ⊗ L* ≅ 𝒪` of `Stacks.InternalHom.dualIso`. -/
theorem exists_trivialization_of_tensorLeft [(tensorLeft L).IsEquivalence]
    (U : Opens ↑↑X.toPresheafedSpace) (x : ↑↑X.toPresheafedSpace) (hx : x ∈ U)
    [IsLocalRing (X.presheaf.stalk x)] :
    ∃ (V : Opens ↑↑X.toPresheafedSpace) (_ : V ⟶ U) (_ : x ∈ V)
      (n : (Stacks.InternalHom.dual L).obj (op V)),
      ∀ (W : Opens ↑↑X.toPresheafedSpace) (j : W ⟶ V),
        Function.Bijective
          (contract (Stacks.InternalHom.dualIso L) (op W)
            ((Stacks.InternalHom.dual L).map j.op n)) :=
  exists_trivialization (Stacks.InternalHom.dualIso L) U x hx

variable (L) in
/-- **Clause 2 of Stacks Tag 0B8M, in presheaf form.** On a ringed space all of whose stalks
`𝒪_{X, x}` are local rings, a presheaf of modules `L` whose left tensoring is an equivalence is
trivial on each member of a family of opens covering the space: the trivialization is
contraction against a section of the dual `L*`, it is an isomorphism `L(W) ≃ 𝒪(W)` over every
open `W` inside a member of the cover, and by `map_contract` these isomorphisms commute with
restriction. The hypothesis is presheaf-level invertibility and the conclusion is not phrased as
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1`; see "What is not done". -/
theorem exists_cover_trivialization_of_tensorLeft [(tensorLeft L).IsEquivalence]
    [∀ x : ↑↑X.toPresheafedSpace, IsLocalRing (X.presheaf.stalk x)] :
    ∃ (V : ↑↑X.toPresheafedSpace → Opens ↑↑X.toPresheafedSpace)
      (n : ∀ x, (Stacks.InternalHom.dual L).obj (op (V x))), iSup V = ⊤ ∧
      ∀ (x : ↑↑X.toPresheafedSpace) (W : Opens ↑↑X.toPresheafedSpace) (j : W ⟶ V x),
        Function.Bijective
          (contract (Stacks.InternalHom.dualIso L) (op W)
            ((Stacks.InternalHom.dual L).map j.op (n x))) :=
  exists_cover_trivialization (Stacks.InternalHom.dualIso L)

end RingedSpace

end Stacks.InvertibleRankOne

end
