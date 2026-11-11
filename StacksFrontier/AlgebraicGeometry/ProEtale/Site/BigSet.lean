module

public import Mathlib.CategoryTheory.Countable
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big
public import StacksCore.Tactic.StacksAttribute

/-!
# Big pro-étale sites (Stacks 098G)

A big pro-étale site (Stacks 098G) is built from a set `S₀` of schemes and a set `Cov₀` of
pro-étale coverings among them: the underlying category is a set of schemes `Sch_α` as in
Stacks 000J for `S₀` and the enlarged function `Cardinal.proetaleBound`, and the coverings are a
set of pro-étale coverings of `Sch_α` as in Stacks 000X containing `Cov₀`.

## Main definitions

* `Covering.map` is the image of a covering family under a functor.
* `CategoryTheory.SmallCoveringSystem` is a set of coverings as produced by Stacks 000X.
* `AlgebraicGeometry.SchemeCategoryOfBound` is a set of schemes, viewed as a full subcategory,
  with the properties produced by Stacks 000J for a given initial set and bound function.
* `AlgebraicGeometry.ProEtale.IsProetaleFamily` is the pro-étale covering condition on a family
  in a full subcategory of schemes.
* `AlgebraicGeometry.ProEtale.SetBigProetaleSite` is a big pro-étale site in the sense of
  Stacks 098G, with its covering precoverage `SetBigProetaleSite.precoverage` and Grothendieck
  topology `SetBigProetaleSite.topology`.

The cardinal-cutoff model `AlgebraicGeometry.ProEtale.BigProetaleSite`, on which the pro-étale
sheaf theory of this library is developed, is in `StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big`.

## References

* [Stacks Project, Tag 098G](https://stacks.math.columbia.edu/tag/098G)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u w u₁ v₁ u₂ v₂

/-- The image of a covering family `{Uᵢ ⟶ U}` under a functor `F`: the family `{F Uᵢ ⟶ F U}`. -/
def Covering.map {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (U : Covering.{u₁, v₁, w} C) : Covering.{u₂, v₂, w} D :=
  ⟨F.obj U.1, U.2.map F⟩

namespace CategoryTheory

/-- **A set of coverings as in Stacks 000X.** Let `IsCov` be a class of coverings of `C` and
`Cov₀` a collection of coverings in it. A set of coverings as in Stacks 000X is a set
`Cov(C)_{κ, α}` of coverings in `IsCov`, all of whose index sets have cardinality at most a
cardinal `κ`, such that
1. `Cov₀ ⊆ Cov(C)_{κ, α}`,
2. `(C, Cov(C)_{κ, α})` is a site: the isomorphism, composition and base change axioms of
   Stacks 00VH hold,
3. every covering in `IsCov` is combinatorially equivalent (Stacks 00VU) to a member of
   `Cov(C)_{κ, α}`.

Stacks obtains such a set as the members of `IsCov ∩ V_α` with index set of cardinality at most
`κ`, the role of the stage `V_α` of the cumulative hierarchy being to make it a set. A Lean
covering carries no ZFC rank, so the set is recorded directly as a collection `coverings`
together with the fact `small_coverings` that it is a set. -/
structure SmallCoveringSystem {C : Type u₁} [Category.{v₁} C]
    (IsCov : Covering.{u₁, v₁, w} C → Prop)
    (Cov₀ : Set (Covering.{u₁, v₁, w} C)) where
  /-- The chosen coverings `Cov(C)_{κ, α}`. -/
  coverings : Set (Covering.{u₁, v₁, w} C)
  /-- The chosen coverings form a set. -/
  small_coverings : Small.{max v₁ w} coverings
  /-- The cardinal `κ` bounding the index sets of the chosen coverings. -/
  indexBound : Cardinal.{w}
  /-- Every chosen covering has index set of cardinality at most `κ`. -/
  mk_le_indexBound : ∀ U ∈ coverings, #U.2.I₀ ≤ indexBound
  /-- Every chosen covering belongs to the class `IsCov`. -/
  isCov_of_mem : ∀ U ∈ coverings, IsCov U
  /-- Stacks 000X (1): the chosen coverings contain `Cov₀`. -/
  subset_coverings : Cov₀ ⊆ coverings
  /-- Stacks 000X (2): the chosen coverings satisfy the axioms of a site. -/
  isSite : IsSite (· ∈ coverings)
  /-- Stacks 000X (3): every covering in `IsCov` is combinatorially equivalent to a chosen one. -/
  exists_combEquiv : ∀ U, IsCov U → ∃ U' ∈ coverings, Covering.CombEquiv U U'

end CategoryTheory

namespace AlgebraicGeometry

/-- **A category of schemes as in Stacks 000J.** Given a set `S₀` of schemes and a function
`bound` on cardinals (the function `Bound` of Stacks 046U, or a variant of it), this is a
*set* `obj` of schemes, viewed as the full subcategory `Sch_α` of the category of schemes, such
that
1. `S₀ ⊆ Ob(Sch_α)`,
2. for every `S ∈ Ob(Sch_α)` and every scheme `T` with `size(T) ≤ bound(size(S))` there is a
   scheme `S' ∈ Ob(Sch_α)` with `T ≅ S'`,
3. for every countable category `I` (countably many objects, countable morphism sets) and every
   functor `F : I ⥤ Sch_α`, the limit of `F` exists in `Sch_α` exactly when the limit of `F`
   exists in `Sch`, and in this case the natural morphism between them is an isomorphism,
4. the same holds for colimits.

In Stacks `Ob(Sch_α)` is the set of schemes lying in the stage `V_α` of the cumulative
hierarchy, for a limit ordinal `α`; the role of `α` is to make `Ob(Sch_α)` a set. A Lean scheme
carries no ZFC rank, so the set of objects is recorded directly as `obj` together with the fact
`small_obj` that it is a set. Countable index categories are taken in `Type u`, which reaches
every countable category up to isomorphism. -/
structure SchemeCategoryOfBound (S₀ : Set Scheme.{u}) (bound : Cardinal.{u} → Cardinal.{u}) where
  /-- The set of objects of `Sch_α`. -/
  obj : ObjectProperty Scheme.{u}
  /-- The objects of `Sch_α` form a set. -/
  small_obj : Small.{u} (Subtype obj)
  /-- Stacks 000J (1): `S₀ ⊆ Ob(Sch_α)`. -/
  mem_obj : ∀ S ∈ S₀, obj S
  /-- Stacks 000J (2): a scheme of size at most `bound(size(S))` for some `S ∈ Ob(Sch_α)` is
  isomorphic to an object of `Sch_α`. -/
  exists_iso_of_size_le : ∀ S : Scheme.{u}, obj S → ∀ T : Scheme.{u},
    T.size ≤ bound S.size → ∃ S' : Scheme.{u}, obj S' ∧ Nonempty (T ≅ S')
  /-- Stacks 000J (3), existence: a countable limit exists in `Sch_α` exactly when it exists
  in `Sch`. -/
  hasLimit_iff : ∀ (I : Type u) [Category.{u} I] [CountableCategory I]
    (F : I ⥤ obj.FullSubcategory), HasLimit F ↔ HasLimit (F ⋙ obj.ι)
  /-- Stacks 000J (3), comparison: when both exist, the natural morphism from the limit in
  `Sch_α` to the limit in `Sch` is an isomorphism. -/
  isIso_limit_post : ∀ (I : Type u) [Category.{u} I] [CountableCategory I]
    (F : I ⥤ obj.FullSubcategory) [HasLimit F] [HasLimit (F ⋙ obj.ι)],
    IsIso (limit.post F obj.ι)
  /-- Stacks 000J (4), existence: a countable colimit exists in `Sch_α` exactly when it
  exists in `Sch`. -/
  hasColimit_iff : ∀ (I : Type u) [Category.{u} I] [CountableCategory I]
    (F : I ⥤ obj.FullSubcategory), HasColimit F ↔ HasColimit (F ⋙ obj.ι)
  /-- Stacks 000J (4), comparison: when both exist, the natural morphism from the colimit in
  `Sch` to the colimit in `Sch_α` is an isomorphism. -/
  isIso_colimit_post : ∀ (I : Type u) [Category.{u} I] [CountableCategory I]
    (F : I ⥤ obj.FullSubcategory) [HasColimit F] [HasColimit (F ⋙ obj.ι)],
    IsIso (colimit.post F obj.ι)

namespace ProEtale

/-- A covering family in a full subcategory of schemes is *pro-étale* when its image in the
category of schemes is a pro-étale covering (Stacks 0989), that is, a covering for Mathlib's
pro-étale precoverage. -/
def IsProetaleFamily (P : ObjectProperty Scheme.{u})
    (U : Covering.{u + 1, u, w} P.FullSubcategory) : Prop :=
  (U.map P.ι).2.presieve₀ ∈ Scheme.proetalePrecoverage.coverings (U.map P.ι).1

/-- **A big pro-étale site** (Stacks 098G): a site `Sch_proétale` in the sense of Stacks 00VH
constructed as follows.
1. Choose a set `S₀` of schemes and a set `Cov₀` of pro-étale coverings among these schemes.
2. Change the function `Bound` of Stacks 046U into
   `Bound(κ) = max {κ ^ (2 ^ (2 ^ (2 ^ κ))), κ ^ ℵ₀, κ⁺}`, which is `Cardinal.proetaleBound`.
3. As underlying category take a category `Sch_α` as in Stacks 000J, starting with `S₀` and
   this `Bound`: the field `category`.
4. Choose a set of coverings as in Stacks 000X, starting with `Sch_α`, the class of pro-étale
   coverings and `Cov₀`: the field `coveringSet`. A member of `Cov₀` is a family in `Sch`; its
   counterpart in `Sch_α` is any family of `Sch_α` whose image in `Sch` it is, and these
   counterparts are the initial coverings fed to Stacks 000X.

The coverings are indexed by types in `Type u`, the universe of the sets underlying the schemes
in `Scheme.{u}`. -/
@[stacks 098G]
structure SetBigProetaleSite where
  /-- The initially chosen set of schemes `S₀`. -/
  S₀ : Set Scheme.{u}
  /-- `S₀` is a set. -/
  small_S₀ : Small.{u} S₀
  /-- The initially chosen set of pro-étale coverings `Cov₀`. -/
  Cov₀ : Set (Covering.{u + 1, u, u} Scheme.{u})
  /-- `Cov₀` is a set. -/
  small_Cov₀ : Small.{u} Cov₀
  /-- The coverings in `Cov₀` are coverings among the schemes of `S₀`. -/
  mem_S₀_of_mem_Cov₀ : ∀ U ∈ Cov₀, U.1 ∈ S₀ ∧ ∀ i, U.2.X i ∈ S₀
  /-- The coverings in `Cov₀` are pro-étale coverings. -/
  proetale_of_mem_Cov₀ : ∀ U ∈ Cov₀, U.2.presieve₀ ∈ Scheme.proetalePrecoverage.coverings U.1
  /-- The underlying category `Sch_α`, as in Stacks 000J for `S₀` and the modified bound. -/
  category : SchemeCategoryOfBound S₀ Cardinal.proetaleBound
  /-- The set of coverings, as in Stacks 000X for `Sch_α`, the pro-étale coverings and the
  counterparts of `Cov₀` in `Sch_α`. -/
  coveringSet : SmallCoveringSystem (IsProetaleFamily category.obj)
    (Covering.map category.obj.ι ⁻¹' Cov₀)

namespace SetBigProetaleSite

variable (B : SetBigProetaleSite.{u})

/-- The underlying category `Sch_α` of a big pro-étale site. -/
abbrev Category : Type (u + 1) := B.category.obj.FullSubcategory

/-- The objects of the underlying category of a big pro-étale site form a set. -/
instance : Small.{u} (Subtype B.category.obj) := B.category.small_obj

/-- The covering presieves of a big pro-étale site: the presieves of its chosen coverings. -/
def precoverage : Precoverage B.Category where
  coverings X :=
    {R | ∃ E : PreZeroHypercover.{u} X, E.presieve₀ = R ∧ ⟨X, E⟩ ∈ B.coveringSet.coverings}

/-- The Grothendieck topology generated by the chosen coverings of a big pro-étale site. -/
abbrev topology : GrothendieckTopology B.Category :=
  B.precoverage.toGrothendieck

/-- The chosen coverings of a big pro-étale site satisfy the axioms of a site. -/
theorem isSite : IsSite (· ∈ B.coveringSet.coverings) :=
  B.coveringSet.isSite

/-- The chosen coverings of a big pro-étale site form a set. -/
theorem small_coverings : Small.{u} B.coveringSet.coverings :=
  B.coveringSet.small_coverings

/-- Every chosen covering of a big pro-étale site is a pro-étale covering. -/
theorem isProetaleFamily_of_mem {U : Covering.{u + 1, u, u} B.Category}
    (hU : U ∈ B.coveringSet.coverings) : IsProetaleFamily B.category.obj U :=
  B.coveringSet.isCov_of_mem U hU

end SetBigProetaleSite

end ProEtale

end AlgebraicGeometry
