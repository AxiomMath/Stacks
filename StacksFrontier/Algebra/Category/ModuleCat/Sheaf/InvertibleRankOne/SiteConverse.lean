module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs

/-!
# An invertible module on a locally ringed site is finite locally free of rank one

Let `(C, J, 𝒪)` be a ringed site which is *locally ringed* in the sense of
[Stacks, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU), and let `L` be an invertible sheaf
of `𝒪`-modules. This file proves that `L` is finite locally free of rank one, which is the
converse clause of [Stacks, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q): *"Any locally
free `𝒪`-module of rank `1` is invertible. If `(C, 𝒪)` is locally ringed, then the converse holds
as well (but in general this is not the case)."*

## The argument

Invertibility of `L` produces a presheaf of modules `N` and a pairing

`ψ : L ⊗_𝒪 N ⟶ 𝒪`

of *presheaves* of modules which is locally surjective and locally injective
(`Stacks.SheafOfModules.exists_locallyBijective_pairing`, the engine of Tag 0B8N (b)). Local
surjectivity applied to the unit section of `𝒪` over an object `U` produces, on a covering of
`U`, an element `z` of `L(V) ⊗_{𝒪(V)} N(V)` with `ψ(z) = 1`; writing `z = ∑_j s_j ⊗ t_j` as a
finite sum of pure tensors gives finitely many sections
`a_j = ψ(s_j ⊗ t_j)` of `𝒪(V)` with `∑_j a_j = 1`.

This is where local ringedness enters, and it is the only place it is used. The local-unit
condition says that every section of `𝒪` is, on a covering, either a unit or has unit
complement; an induction on the number of summands upgrades that to: finitely many sections
summing to `1` admit a covering on each member of which *one of them* is a unit
(`AlgebraicGeometry.RingedSite.locallyOnCovering_exists_isUnit_of_sum_eq_one`, the content of
[Stacks, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES) (1) ⟹ (2)). So after refining the
covering once more, some `a_j` is a unit.

Rescaling, `ψ(s ⊗ t) = 1` for a single pure tensor over some object `W`. Two consequences of
that identity finish the proof. Pairing against `t` is a left inverse of `r ↦ r • s`, which gives
injectivity, and surjectivity holds because for any section `x` the two sections `ψ(x ⊗ t) • s`
and `x` have the same image under `ψ(· ⊗ t)`, hence agree locally — and `L` is a sheaf, so they
agree. Thus `r ↦ r • s|_{V}` is bijective for *every* object `V` of the slice site `C/W`
(`Stacks.SheafOfModules.bijective_smul_of_pairing_eq_one`), which is exactly a trivialization
`L|_W ≅ 𝒪|_W` read on sections (`Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul`).

## Main results

* `AlgebraicGeometry.RingedSite.locallyOnCovering_exists_isUnit_of_sum_eq_one`: on a site whose
  structure sheaf satisfies the local-unit condition, finitely many sections summing to `1` admit
  a covering on each member of which one of them restricts to a unit.
* `Stacks.SheafOfModules.overIsoUnitOfBijectiveSmul`: a section of `L` over `U` by which
  multiplication is bijective over every object of `C/U` trivializes `L` on `U`.
* `Stacks.SheafOfModules.bijective_smul_of_pairing_eq_one` and
  `Stacks.SheafOfModules.exists_bijective_smul_of_isUnit_pairing`: a pure tensor whose pairing is
  `1`, respectively a unit, produces such a section.
* `Stacks.SheafOfModules.exists_cover_over_iso_unit`: **the local form of the converse clause.**
  Every object of the site has a covering family on each member of which `L` is isomorphic to the
  structure sheaf.
* `Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_locallyEitherUnit` and
  `Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_locallyEitherUnit`:
  the same conclusion in the two predicates of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Invertible.lean`, which are stated over a
  covering of the final object.
* `AlgebraicGeometry.RingedSite.isLocallyTrivial_of_isInvertible` and
  `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible`: the converse
  clause of Tag 0B8Q for a locally ringed site, with no hypothesis beyond local ringedness and
  with the morphism universe of the site left free.
  `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'` is the same
  statement with the universe of the sections of the structure sheaf left free as well; it is
  the form that applies to a site whose objects live above its morphisms, such as the small
  étale site of an algebraic space.

## Implementation notes

**Why the ringed-space proof does not transport, and what replaces it.** The converse clause for
a ringed space is `Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible`
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne/Converse.lean`. Its proof is
about *stalks*: the stalk of `L` at a point is an invertible module over the local ring
`𝒪_{X, x}`, hence free of rank one, and the trivializing pure tensor is spread out from the
stalk to a neighbourhood. Both halves of that argument are unavailable on a site. A general site
has no points, so there is no stalk to be invertible over and nothing to spread out from; and
local ringedness of a site is *not* a condition on stalks — it is
`AlgebraicGeometry.RingedSite.IsLocallyRinged`, whose second conjunct
`AlgebraicGeometry.RingedSite.LocallyEitherUnit` is a condition on sections over a covering. The
two agree only on a site with a conservative family of points
(`AlgebraicGeometry.RingedSite.locallyUnitOrOneSubUnit_iff_stalksAreZeroOrLocal`). What replaces
the stalk-theoretic step is the pair of refinements described above: the finite sum of pure
tensors supplied by Tag 0B8N (b) plays the role of the finite sum representing `1` in the stalk,
and the induction on the local-unit condition plays the role of "a sum of non-units in a local
ring is a non-unit".

**Only one conjunct of local ringedness is used.** `IsLocallyRinged` is the conjunction of
`IsIso (oneIsNeverZero X)` — the sheaf-theoretic form of `1 ≠ 0` — with `LocallyEitherUnit X.O`,
and only the second is needed. The reason is the padding in
`Stacks.SheafOfModules.locallyOnCovering_nonempty_over_iso_unit`: the finite family of pure
tensors is extended by a zero tensor, so that the family of sections summing to `1` is never
empty and the unit-ideal induction never has to decide the degenerate case `0 = 1`. If `0 = 1`
on an object then `𝒪|_V` is the zero sheaf of rings and `L|_V` is the zero module, which *is*
free of rank one over it; so the degenerate case needs no exclusion and the results below assume
only `LocallyEitherUnit`. The forms carrying `IsLocallyRinged` are stated for the reader who has
the source's hypothesis to hand.

**Why the local-unit induction is redone here.** `Stacks.Sheaves.LocallyRingedSite.Condition2` of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/LocalUnitConditions.lean` is exactly
the statement proved here, and `condition1_imp_condition2` is exactly this induction — but that
development is written for `O : Sheaf J CommRingCat.{v}` on a site `C : Type u` with
`Category.{v} C`, i.e. with the universe of the sections of the structure sheaf identified with
the universe of the *morphisms* of the site. A ringed site has three independent universes, so
`Condition2` is inapplicable to `X.O` unless `w = v`. The induction here is over
`AlgebraicGeometry.RingedSite.LocallyEitherUnit`, the universe-independent spelling of the same
condition, and it is the only part of the 04ES development that this file needs.

**Which rank predicate.** Two different predicates in this library are called "finite locally
free of rank `r`". `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` is the rank clause of
[Stacks, Tag 0409](https://stacks.math.columbia.edu/tag/0409): a covering family of *every*
object of the site. `Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank` asks for local
generators over a covering of the *final* object. The per-object statement
`Stacks.SheafOfModules.exists_cover_over_iso_unit` yields both: the first directly, and the
second because the objects on which `L` is trivial are themselves a family covering the final
object, by the argument of `Stacks.SheafOfModules.coversTop_invertibleSummandObj`.

**Universes.** `Stacks.SheafOfModules.exists_locallyBijective_pairing` leaves the universe `w` of
the sections free, but it assumes `HasWeakSheafify J AddCommGrpCat.{w}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{w}`, which are not available for an arbitrary `w`. For
`w = max u v` they are instances for every site, because `C` is then essentially small relative
to the values; so the statements with no hypothesis at all are the ones at
`RingedSite.{u, v, max u v}`, and the free-`w` statement
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'` carries those two
instances as hypotheses. The Stacks attribute is attached only to the hypothesis-free forms.

**Relation to the ringed-site development.** All three sentences of Tag 0B8Q are already proved
in `StacksFrontier/CategoryTheory/Sites/Modules/InvertibleRankOne.lean`, where
`AlgebraicGeometry.RingedSite.isInvertible_iff_isFiniteLocallyFreeOfRank_one` carries the
characterization for locally ringed sites. That statement identifies the universe of the
morphisms of the site with the universe of the sections of the structure sheaf, which a site
whose objects live one universe above its morphisms does not satisfy. What this file adds is the
same converse with those universes independent, so nothing here claims a clause of Tag 0B8Q
afresh.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N) — an invertible module is
  locally a direct summand of a finite free module.
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K) — invertibility from a
  trivializing pairing.
* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES) — the local-unit
  conditions.
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU) — locally ringed sites.
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409) — finite locally free
  modules of a fixed rank on a ringed site.
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace AlgebraicGeometry.RingedSite

/-! ### Finitely many sections summing to one -/

section UnitIdeal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Locally, one of finitely many sections summing to `1` is a unit.** If every section of a
sheaf of commutative rings `O` is, on a covering, either a unit or has unit complement, and
sections `a 0, …, a n` of `O` over `U` satisfy `∑ i, a i = 1`, then `U` has a covering on each
member of which some `a i` restricts to a unit.

This is the implication (1) ⟹ (2) of [Stacks, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
with the universe of the sections independent of the universes of the site; see the implementation
notes. The index type is `Fin (n + 1)`, never empty: the statement is false for the empty family
unless `U` is covered by the empty sieve, and the consumer below pads its family with a zero
section rather than exclude that case.

The induction is on the number of summands. If `a 0` restricts to a unit the covering is
`U` itself; otherwise `1 - a 0 = ∑ i, a i.succ` restricts to a unit `u`, and the family
`u⁻¹ • a i.succ` sums to `1`, so the inductive hypothesis applies over the member of the
covering. -/
theorem locallyOnCovering_exists_isUnit_of_sum_eq_one {O : Sheaf J CommRingCat.{w}}
    (hO : LocallyEitherUnit O) :
    ∀ (n : ℕ) (U : C) (a : Fin (n + 1) → O.obj.obj (op U)), ∑ i, a i = 1 →
      Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering J U
        (fun {_} g ↦ ∃ i, IsUnit (O.obj.map g.op (a i))) := by
  intro n
  induction n with
  | zero =>
    intro U a ha
    refine ⟨⊤, J.top_mem U, fun V g _ ↦ ⟨0, ?_⟩⟩
    rw [show a 0 = 1 by simpa using ha, map_one]
    exact isUnit_one
  | succ n ih =>
    intro U a ha
    obtain ⟨S, hS, hSP⟩ := hO U (a 0)
    refine Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering.refine _ S hS ?_
    intro V g hg
    have hsum : ∑ i : Fin (n + 1), a i.succ = 1 - a 0 := by
      rw [Fin.sum_univ_succ] at ha
      linear_combination ha
    rcases hSP g hg with hu | hu
    · refine ⟨⊤, J.top_mem V, fun W g' _ ↦ ⟨0, ?_⟩⟩
      have hcomp : O.obj.map (g' ≫ g).op (a 0) = O.obj.map g'.op (O.obj.map g.op (a 0)) := by
        simp
      rw [hcomp]
      exact hu.map (O.obj.map g'.op).hom
    · obtain ⟨uu, huu⟩ := hu
      have hres : ∑ i : Fin (n + 1), O.obj.map g.op (a i.succ) = (uu : O.obj.obj (op V)) := by
        rw [huu, ← map_sum, hsum]
      set b : Fin (n + 1) → O.obj.obj (op V) :=
        fun i ↦ ((uu⁻¹ : (O.obj.obj (op V))ˣ) : O.obj.obj (op V)) * O.obj.map g.op (a i.succ)
        with hb
      have hbsum : ∑ i, b i = 1 := by
        rw [hb, ← Finset.mul_sum, hres]
        exact uu.inv_mul
      refine (ih V b hbsum).mono ?_
      rintro W g' ⟨i, hi⟩
      refine ⟨i.succ, ?_⟩
      have hmap : O.obj.map g'.op (b i) =
          O.obj.map g'.op ((uu⁻¹ : (O.obj.obj (op V))ˣ) : O.obj.obj (op V)) *
            O.obj.map (g' ≫ g).op (a i.succ) := by
        rw [hb]
        simp
      rw [hmap] at hi
      exact isUnit_of_mul_isUnit_right hi

end UnitIdeal

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

/-! ### A generating section trivializes the module -/

section Generator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A section by which multiplication is bijective trivializes the module.** If `s` is a
section of `L` over `U` such that `r ↦ r • s|_V` is a bijection from the sections of the
structure sheaf over `V` onto the sections of `L` over `V`, for every object `V ⟶ U` of the slice
site, then `s` is a basis of one element for `L|_U`, so `L|_U` is isomorphic to the structure
sheaf of the slice site.

The morphism `𝒪|_U ⟶ L|_U` is the one corresponding to `s` under
`PresheafOfModules.unitHomEquiv`; its component at an object `V` of `C/U` is `r ↦ r • s|_V`, so
the hypothesis says precisely that every component is bijective, and a morphism of presheaves of
modules which is bijective on every object is an isomorphism. -/
noncomputable def overIsoUnitOfBijectiveSmul (L : SheafOfModules.{w} R) (U : C)
    (s : L.val.obj (op U))
    (hs : ∀ (V : C) (f : V ⟶ U),
      Function.Bijective (fun r : R.obj.obj (op V) ↦ r • L.val.map f.op s)) :
    L.over U ≅ SheafOfModules.unit (R.over U) := by
  let sec : (L.over U).val.sections :=
    PresheafOfModules.sectionsMk (fun W ↦ L.val.map W.unop.hom.op s) (by
      intro W W' f
      change L.val.map f.unop.left.op (L.val.map W.unop.hom.op s) = _
      rw [← L.val.map_comp_apply]
      change L.val.map (f.unop.left ≫ W.unop.hom).op s = _
      rw [f.unop.w])
  let φ : SheafOfModules.unit (R.over U) ⟶ L.over U :=
    ⟨(L.over U).val.unitHomEquiv.symm sec⟩
  have hφ (W : (Over U)ᵒᵖ) : IsIso (φ.val.app W) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hs W.unop.left W.unop.hom)
  have ψ : (SheafOfModules.unit (R.over U)).val ≅ (L.over U).val :=
    PresheafOfModules.isoMk (fun W ↦ @asIso _ _ _ _ (φ.val.app W) (hφ W))
      (fun _ _ f ↦ φ.val.naturality f)
  exact ((SheafOfModules.fullyFaithfulForget (R.over U)).preimageIso
    (X := SheafOfModules.unit (R.over U)) (Y := L.over U) ψ).symm

end Generator

/-! ### Pure tensors pairing to a unit -/

section Pairing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Lp Np : PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)}

/-- A pairing `Lp ⊗ Np ⟶ 𝒪` of presheaves of modules, read over a single object as an
`𝒪(U)`-linear map out of the tensor product of the modules of sections. -/
noncomputable abbrev pairingMap
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    (U : C) :
    TensorProduct (O.obj (op U)) (Lp.obj (op U)) (Np.obj (op U)) →ₗ[O.obj (op U)]
      O.obj (op U) :=
  (ψ.app (op U)).hom

/-- A pairing commutes with restriction: it is a morphism of presheaves of modules, and the
restriction of a pure tensor is the pure tensor of the restrictions. -/
theorem pairingMap_map
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    {U V : C} (f : V ⟶ U) (s : Lp.obj (op U)) (t : Np.obj (op U)) :
    pairingMap ψ V (Lp.map f.op s ⊗ₜ Np.map f.op t) =
      O.map f.op (pairingMap ψ U (s ⊗ₜ t)) :=
  PresheafOfModules.naturality_apply ψ f.op (s ⊗ₜ t)

/-- Scalars pull out of the first factor of a pure tensor under a pairing. -/
private theorem pairingMap_smul_tmul
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    (U : C) (r : O.obj (op U)) (s : Lp.obj (op U)) (t : Np.obj (op U)) :
    pairingMap ψ U ((r • s) ⊗ₜ t) = r * pairingMap ψ U (s ⊗ₜ t) := by
  rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]

/-- **A pure tensor pairing to `1` makes tensoring by its second factor injective.** Contracting
`x ⊗ t` against `s` through the pairing recovers `x`, because `B (s ⊗ t) = 1`. -/
private theorem injective_tmul_of_pairing_eq_one {Rg M N : Type*} [CommRing Rg]
    [AddCommGroup M] [Module Rg M] [AddCommGroup N] [Module Rg N]
    (B : TensorProduct Rg M N →ₗ[Rg] Rg) (s : M) (t : N) (h : B (s ⊗ₜ t) = 1) :
    Function.Injective (fun x : M ↦ x ⊗ₜ[Rg] t) := by
  let c := (TensorProduct.rid Rg M).toLinearMap.comp
    (TensorProduct.map LinearMap.id (B.comp (TensorProduct.mk Rg M N s)))
  intro x y hxy
  simpa [c, h] using congrArg c hxy

/-- **A pure tensor pairing to the unit section makes its first factor a basis.** If `Lp` is a
sheaf, the pairing `ψ` is locally injective and `ψ (s ⊗ t) = 1` over `U`, then multiplication by
`s` is a bijection from the sections of `𝒪` over `U` onto the sections of `Lp` over `U`.

Injectivity is contraction against `t`. For surjectivity, a section `x` and the section
`ψ (x ⊗ t) • s` have equal images under `ψ (· ⊗ t)`, so local injectivity of `ψ` makes
`x ⊗ t` and `(ψ (x ⊗ t) • s) ⊗ t` agree on a covering; on each member of that covering the
restricted pairing still takes the value `1`, so `injective_tmul_of_pairing_eq_one` cancels `t`
and the two sections of `Lp` agree there. They therefore agree on `U`, because `Lp` is a
separated presheaf. -/
theorem bijective_smul_of_pairing_eq_one (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallyInjective J ψ]
    (U : C) (s : Lp.obj (op U)) (t : Np.obj (op U))
    (hst : pairingMap ψ U (s ⊗ₜ t) = 1) :
    Function.Bijective (fun r : O.obj (op U) ↦ r • s) := by
  refine ⟨fun r q hrq ↦ ?_, fun x ↦ ⟨pairingMap ψ U (x ⊗ₜ t), ?_⟩⟩
  · simpa only [pairingMap_smul_tmul, hst, mul_one] using
      congrArg (fun x ↦ pairingMap ψ U (x ⊗ₜ t)) hrq
  · set y := pairingMap ψ U (x ⊗ₜ t) • s
    set ψ' := (PresheafOfModules.toPresheaf
      (TensorSheafification.structureRingPresheaf O)).map ψ
    have he : ψ'.app (op U) (y ⊗ₜ t) = ψ'.app (op U) (x ⊗ₜ t) := by
      show pairingMap ψ U ((pairingMap ψ U (x ⊗ₜ t) • s) ⊗ₜ t) = pairingMap ψ U (x ⊗ₜ t)
      rw [pairingMap_smul_tmul, hst, mul_one]
    have hS : Presheaf.equalizerSieve (F := (Lp ⊗ Np).presheaf) (y ⊗ₜ t) (x ⊗ₜ t) ∈ J U :=
      Presheaf.equalizerSieve_mem J ψ' _ _ he
    have hsep := Presheaf.isSheaf_comp_of_isSheaf J Lp.presheaf (forget AddCommGrpCat) hLp
    refine (hsep.isSheafFor _ hS).isSeparatedFor.ext fun V f hf ↦ ?_
    have hst' : pairingMap ψ V (Lp.map f.op s ⊗ₜ Np.map f.op t) = 1 := by
      rw [pairingMap_map, hst, map_one]
    exact injective_tmul_of_pairing_eq_one (pairingMap ψ V)
      (Lp.map f.op s) (Np.map f.op t) hst' hf

/-- **A pure tensor pairing to a unit produces a generating section over the whole slice site.**
Rescaling the first factor by the inverse of the unit makes the pairing equal to `1`, and that
identity restricts along every arrow into `U`, so `bijective_smul_of_pairing_eq_one` applies over
each object of `C/U` at once. -/
theorem exists_bijective_smul_of_isUnit_pairing (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallyInjective J ψ]
    (U : C) (s : Lp.obj (op U)) (t : Np.obj (op U))
    (hst : IsUnit (pairingMap ψ U (s ⊗ₜ t))) :
    ∃ e : Lp.obj (op U), ∀ (V : C) (f : V ⟶ U),
      Function.Bijective (fun r : O.obj (op V) ↦ r • Lp.map f.op e) := by
  obtain ⟨a, ha⟩ := hst
  refine ⟨((a⁻¹ : (O.obj (op U))ˣ) : O.obj (op U)) • s, fun V f ↦ ?_⟩
  have hs' : pairingMap ψ U ((((a⁻¹ : (O.obj (op U))ˣ) : O.obj (op U)) • s) ⊗ₜ t) = 1 := by
    rw [pairingMap_smul_tmul, ← ha, Units.inv_mul]
  refine bijective_smul_of_pairing_eq_one hLp ψ V _ (Np.map f.op t) ?_
  rw [pairingMap_map, hs', map_one]

end Pairing

/-! ### The converse clause of Tag 0B8Q -/

section Main

open AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (Osh : Sheaf J CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf Osh.obj))
  (L : SheafOfModules.{w} (TensorSheafification.structureSheaf Osh.obj hO))

/-- **An invertible module on a site with the local-unit condition is locally trivial over every
object.** Each object of the site has a covering sieve on every member of which `L` is isomorphic
to the structure sheaf.

Invertibility supplies a locally bijective pairing `ψ : L ⊗ N ⟶ 𝒪` of presheaves of modules
(Tag 0B8N (b)). Local surjectivity at the unit section gives, on a covering of the given object,
a preimage of `1`, which is a finite sum of pure tensors; padding that finite family by a zero
tensor makes it nonempty, so the local-unit induction refines the covering to one on which some
summand pairs to a unit. `exists_bijective_smul_of_isUnit_pairing` and
`overIsoUnitOfBijectiveSmul` turn that into a trivialization. -/
theorem locallyOnCovering_nonempty_over_iso_unit
    (hOloc : RingedSite.LocallyEitherUnit Osh) [IsInvertible Osh.obj hO L] (U : C) :
    Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering J U
      (fun {V} _ ↦ Nonempty (L.over V ≅ SheafOfModules.unit
        ((TensorSheafification.structureSheaf Osh.obj hO).over V))) := by
  classical
  obtain ⟨Np, ψ, hsurj, hinj⟩ :=
    exists_locallyBijective_pairing L.isSheaf ‹IsInvertible Osh.obj hO L›
  have := hsurj
  have := hinj
  refine Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering.refine _
    (Presheaf.imageSieve ((PresheafOfModules.toPresheaf
      (TensorSheafification.structureRingPresheaf Osh.obj)).map ψ) (1 : Osh.obj.obj (op U)))
    (Presheaf.imageSieve_mem J _ _) ?_
  rintro V g ⟨z, hz⟩
  have hz1 : pairingMap ψ V z = 1 := by
    change pairingMap ψ V z = (Osh.obj.map g.op).hom 1 at hz
    simpa only [map_one] using hz
  obtain ⟨n, x, y, hxy⟩ := exists_fin_tmul_eq z
  have pad : ∀ {M : Type w} [Zero M] (x : Fin n → M), ∃ x' : Fin (n + 1) → M,
      (∀ j : Fin n, x' j.castSucc = x j) ∧ x' (Fin.last n) = 0 :=
    fun x ↦ ⟨Fin.snoc x 0, fun j ↦ Fin.snoc_castSucc _ _ _, Fin.snoc_last _ _⟩
  obtain ⟨x', hx'c, hx'l⟩ := pad x
  obtain ⟨y', hy'c, hy'l⟩ := pad y
  have hasum : ∑ j, pairingMap ψ V (x' j ⊗ₜ y' j) = 1 := by
    rw [Fin.sum_univ_castSucc, hx'l, hy'l, TensorProduct.zero_tmul, map_zero, add_zero]
    simp only [hx'c, hy'c]
    rw [← map_sum]
    exact (congrArg (fun t ↦ pairingMap ψ V t) hxy).trans hz1
  refine (RingedSite.locallyOnCovering_exists_isUnit_of_sum_eq_one hOloc n V _ hasum).mono ?_
  rintro W g' ⟨j, hj⟩
  rw [← pairingMap_map ψ g'] at hj
  obtain ⟨e, he⟩ := exists_bijective_smul_of_isUnit_pairing L.isSheaf ψ W _ _ hj
  exact ⟨overIsoUnitOfBijectiveSmul L W e he⟩

/-- **The local form of the converse clause of Tag 0B8Q.** On a site whose structure sheaf
satisfies the local-unit condition, an invertible sheaf of modules is trivial on a covering
*family* of every object. This is the previous result with the covering sieve presented by a
family of arrows, which is the shape the rank predicates of Tag 0409 and of Tag 01C6 consume. -/
theorem exists_cover_over_iso_unit
    (hOloc : RingedSite.LocallyEitherUnit Osh) [IsInvertible Osh.obj hO L] (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i, Nonempty (L.over (V i) ≅ SheafOfModules.unit
          ((TensorSheafification.structureSheaf Osh.obj hO).over (V i))) := by
  obtain ⟨S, hS, hSP⟩ := locallyOnCovering_nonempty_over_iso_unit Osh hO L hOloc U
  obtain ⟨I, V, f, hVf⟩ := S.exists_eq_ofArrows
  refine ⟨I, V, f, hVf ▸ hS, fun i ↦ hSP (f i) ?_⟩
  rw [hVf]
  exact ⟨V i, 𝟙 _, f i, Presieve.ofArrows.mk i, Category.id_comp _⟩

/-- **An invertible module on a site with the local-unit condition is locally trivial.** The
objects on which `L` becomes isomorphic to the structure sheaf cover the final object: by
`exists_cover_over_iso_unit` every object has a covering family whose members are among them, so
the covering sieve it generates is contained in the sieve of objects of that family. This is the
argument of `Stacks.SheafOfModules.coversTop_invertibleSummandObj`, and as there it needs no
refinement of sieves and no choice. -/
theorem Invertible.isLocallyTrivial_of_locallyEitherUnit
    (hOloc : RingedSite.LocallyEitherUnit Osh) [IsInvertible Osh.obj hO L] :
    Invertible.IsLocallyTrivial L := by
  refine ⟨{W : C // Nonempty (L.over W ≅ SheafOfModules.unit
      ((TensorSheafification.structureSheaf Osh.obj hO).over W))}, Subtype.val, ?_, fun i ↦ i.2⟩
  intro W
  obtain ⟨I, V, f, hcov, hiso⟩ := exists_cover_over_iso_unit Osh hO L hOloc W
  refine J.superset_covering ((Sieve.ofArrows_le_ofObjects V f).trans
    (Sieve.ofObjects_mono ?_)) hcov
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨V i, hiso i⟩, rfl⟩

section Slice

variable [∀ A : C, HasWeakSheafify (J.over A) AddCommGrpCat.{w}]
  [∀ A : C, (J.over A).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The converse clause of Tag 0B8Q for the final-object rank predicate.** An invertible sheaf
of modules on a site whose structure sheaf satisfies the local-unit condition is finite locally
free of rank one in the sense of
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank`, by local triviality and
`Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial`. -/
theorem Invertible.isFiniteLocallyFreeOfRank_one_of_locallyEitherUnit
    (hOloc : RingedSite.LocallyEitherUnit Osh) [IsInvertible Osh.obj hO L] :
    Invertible.IsFiniteLocallyFreeOfRank L 1 :=
  have := Invertible.isLocallyTrivial_of_locallyEitherUnit Osh hO L hOloc
  Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial L

end Slice

end Main

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

/-! ### The converse clause for a locally ringed site -/

/-- **The converse clause of Tag 0B8Q, with the universe of the sections free.** On a ringed site
which is locally ringed, an invertible sheaf of `𝒪`-modules is finite locally free of rank one in
the sense of the rank clause of [Stacks, Tag 0409](https://stacks.math.columbia.edu/tag/0409): on
a covering family of every object it is a coproduct of one copy of the structure sheaf.

The trivializations of `Stacks.SheafOfModules.exists_cover_over_iso_unit` are exactly such
coproduct presentations: a single morphism `𝒪|_V ⟶ L|_V` which is an isomorphism is a colimit
cofan indexed by `Fin 1`.

Only the local-unit conjunct of local ringedness is used; see the implementation notes. No Stacks
attribute is attached here because of the two sheafification instances in the statement —
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible` is the form that
carries it. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible' (X : RingedSite.{u, v, w})
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : IsLocallyRinged X)
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    IsFiniteLocallyFreeOfRank X L 1 := by
  intro U
  obtain ⟨I, V, f, hcov, hiso⟩ :=
    Stacks.SheafOfModules.exists_cover_over_iso_unit X.O
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L hX.2 U
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨e⟩ : Nonempty (L.over (V i) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i))) := hiso i
  refine ⟨fun _ ↦ e.inv, ⟨Limits.Cofan.IsColimit.mk _ (fun s ↦ e.hom ≫ s.inj 0) ?_ ?_⟩⟩
  · intro s j
    fin_cases j
    show e.inv ≫ e.hom ≫ s.inj 0 = s.inj 0
    rw [Iso.inv_hom_id_assoc]
  · intro s m hm
    have h0 : e.inv ≫ m = s.inj 0 := hm 0
    rw [← h0, Iso.hom_inv_id_assoc]

/-- **The converse clause of Tag 0B8Q.** On a ringed site which is locally ringed, an invertible
sheaf of `𝒪`-modules is finite locally free of rank one.

This is `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'` with the
universe of the sections of the structure sheaf specialized to `max u v`, where the two
sheafification hypotheses of that statement hold for every site and so disappear. Local
ringedness is the only hypothesis.

The morphism universe of the site is left free here, whereas
`AlgebraicGeometry.RingedSite.isInvertible_iff_isFiniteLocallyFreeOfRank_one` identifies it with
the universe of the sections. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible (X : RingedSite.{u, v, max u v})
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : IsLocallyRinged X)
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    IsFiniteLocallyFreeOfRank X L 1 :=
  isFiniteLocallyFreeOfRank_one_of_isInvertible' X L hX

/-- **The converse clause of Tag 0B8Q, as local triviality.** On a ringed site which is locally
ringed, an invertible sheaf of `𝒪`-modules becomes isomorphic to the structure sheaf on a family
of objects covering the final object. This is the same content as
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible` read through
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_iff_isFiniteLocallyFreeOfRank_one`, in the
predicate that quantifies over a covering of the final object rather than over every object. -/
theorem isLocallyTrivial_of_isInvertible (X : RingedSite.{u, v, max u v})
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : IsLocallyRinged X)
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
  Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_locallyEitherUnit
    X.O (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L hX.2

end AlgebraicGeometry.RingedSite

end
