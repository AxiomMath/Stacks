module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayModuleOverDerived
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.DerivedIsomorphismLocality
public import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf condition for the vanishing locus of a ringed site

Let `(𝒞, 𝒪)` be a ringed site and let `K ∈ D(𝒪)`. [Stacks, Tag 0998] asserts that the sections
`f` of `𝒪` with `T(K|_U, f) = 0` form a sheaf of ideals in `𝒪`, and the source says of the last
of the four things that assertion contains — the sheaf condition — only "we omit the
verification". This file proves it: **membership in the vanishing locus is local on a covering
of the object.**

The locus is defined by the vanishing of an *object of a derived category*,
`R𝑆heafHom_𝒪(𝒪_f, K) = 0`, and such a vanishing is local
because invertibility in the derived category of sheaves of modules is local
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`): applied to the zero morphism
`K ⟶ 0` that gives the vanishing of an object of `D(𝒪)` from the vanishing of its restrictions
to the slices over a family of objects covering the final object. Restriction stability
(`AlgebraicGeometry.RingedSite.memVanishingIdeal_over_of_memVanishingIdeal`) is the converse
implication, and the comparison of derived internal Hom with restriction to a slice —
[Stacks, Tag 08JB], `AlgebraicGeometry.RingedSite.derivedHomRestriction` — is what turns the one
into the other.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_of_coversTop_overFunctor_mapDerivedCategory`: an object
  of `D(𝒪)` whose restriction to the slice over each member of a family of objects covering the
  final object vanishes is zero.
* `AlgebraicGeometry.RingedSite.coversTop_over_sieve`: the objects of a covering sieve of `U`,
  read as objects of the slice site `𝒞/U`, cover its final object. This is what turns a covering
  of `U` into the covering family the previous statement consumes.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_of_coversTop`: **[Stacks, Tag 0998], the sheaf
  condition.** A global section whose restriction to each member of a covering family lies in
  the vanishing locus of the corresponding restriction of `K` lies in the vanishing locus of
  `K`.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_over_of_locally`: the same read at a section
  over an object `U` and a covering sieve of `U`, which is the form in which the local-generation
  argument of [Stacks, Tag 099F] consumes it: a section of a finitely generated ideal sheaf over
  `U` is only *locally* an `𝒪`-combination of the generators.

## Implementation notes

Nothing here is a hypothesis on the site. The derived locality statement this is built from,
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/DerivedIsomorphismLocality.lean`, carries only
sheafification and derived-category instances, all of which hold on every
`AlgebraicGeometry.RingedSite.{u, u, u}` and on each of its slices; in particular it does **not**
carry `HasBinaryProducts`, which the superficially similar
`Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedLocality/InvertibilityOnACovering.lean` does and which would be a hypothesis on the
site that neither [Stacks, Tag 0998] nor [Stacks, Tag 099F] makes.

The covering family is indexed by the objects of the sieve together with their structure maps,
`Σ W, {g : W ⟶ U // S g}`, rather than by a presieve: the sieve is what
`AlgebraicGeometry.RingedSite.mem_generatedIdealSheaf_iff` produces, and
`CategoryTheory.Sieve.ofObjects` only needs *some* morphism into a member of the family, which
the identity of `W` supplies. An object of a derived category is not determined by a
compatible family of restrictions, but only its vanishing is needed here, and that is a
consequence of locality of invertibility.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

section Covering

variable (X : RingedSite.{u, u, u})

/-- **An object of `D(𝒪)` whose restriction to the slice over each member of a covering family
vanishes is zero.** Here a covering family is one covering the final object of the site, in the
sense of `CategoryTheory.GrothendieckTopology.CoversTop`.

The zero morphism `K ⟶ 0` restricts to a morphism between two zero objects, hence to an
isomorphism, over every member of the family; invertibility in `D(𝒪)` is local on such a family
by `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, so `K ⟶ 0` is an isomorphism
and `K` is zero. -/
theorem isZero_of_coversTop_overFunctor_mapDerivedCategory
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : ∀ i, IsZero
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (V i)).mapDerivedCategory.obj K)) :
    IsZero K := by
  have hiso : IsIso (0 : K ⟶
      (0 : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) := by
    refine Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory hV _ fun i => ?_
    have h0 : IsZero
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (V i)).mapDerivedCategory.obj
        (0 : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (V i)).mapDerivedCategory.map_isZero (isZero_zero _)
    rw [show (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (V i)).mapDerivedCategory.map
        (0 : K ⟶
          (0 : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) =
        ((hK i).iso h0).hom from (hK i).eq_of_src _ _]
    infer_instance
  exact IsZero.of_iso (isZero_zero _)
    (asIso (0 : K ⟶
      (0 : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))

/-- **The objects of a covering sieve of `U` cover the final object of the slice site `𝒞/U`.**
An object `W ⟶ U` of `𝒞/U` admitting a morphism to the final object `U ⟶ U` is an arbitrary
object of the slice, and the sieve generated there by the members of `S` contains the covering
sieve `S` read on `𝒞/U`, because an object of `S` maps to itself. -/
theorem coversTop_over_sieve (U : X.C) {S : Sieve U} (hS : S ∈ X.J U) :
    (X.J.over U).CoversTop
      (fun p : Σ W : X.C, {g : W ⟶ U // S.arrows g} => Over.mk p.2.1) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (Over.mk (𝟙 U)) Over.mkIdTerminal]
  refine (X.J.over U).superset_covering ?_
    (GrothendieckTopology.overEquiv_symm_mem_over (J := X.J) (Over.mk (𝟙 U)) S hS)
  intro Z f hf
  have hw : f.left = Z.hom := by simpa using Over.w f
  have hZ : S.arrows Z.hom := hw ▸ hf
  exact ⟨⟨Z.left, ⟨Z.hom, hZ⟩⟩, ⟨Over.homMk (𝟙 Z.left) (by simp)⟩⟩

end Covering

section SheafCondition

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **[Stacks, Tag 0998], the sheaf condition for the vanishing locus.** Let `V : ι → 𝒞` be a
family of objects covering the final object of the site. If the restriction `f|_{V i}` lies in
the vanishing locus of `K|_{V i}` for every `i`, then `f` lies in the vanishing locus of `K`.

This is the verification the source omits. Membership of `f|_{V i}` in the locus of `K|_{V i}` is
the vanishing of `R𝑆heafHom_{𝒪_{V i}}((𝒪_f)|_{V i}, K|_{V i})` by
`AlgebraicGeometry.RingedSite.memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor`, and
that object is the restriction of `R𝑆heafHom_𝒪(𝒪_f, K)` by [Stacks, Tag 08JB]. So the hypothesis
says that `R𝑆heafHom_𝒪(𝒪_f, K)` vanishes on each member of the covering family, and
`isZero_of_coversTop_overFunctor_mapDerivedCategory` concludes that it vanishes.

Nothing is assumed of `K`, of `f` or of the site. The converse implication, at a single object
and with no covering, is
`AlgebraicGeometry.RingedSite.memVanishingIdeal_over_of_memVanishingIdeal`. -/
@[stacks 0998 "the sheaf condition: membership in the vanishing locus is local on a family of
  objects covering the final object of the site"]
theorem memVanishingIdeal_of_coversTop
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hK : ∀ i, MemVanishingIdeal (X.over (V i))
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (V i)).mapDerivedCategory.obj K)
      (globalSectionOver X (V i) h)) :
    MemVanishingIdeal X K h := by
  refine isZero_of_coversTop_overFunctor_mapDerivedCategory X hV _ fun i => ?_
  exact IsZero.of_iso
    ((memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor X (V i) h K).1 (hK i))
    ((derivedHomRestriction X (V i)).iso (derivedAwayModule X h) K)

end SheafCondition

section Local

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)

omit [HasWeakSheafify X.J CommRingCat] in
/-- **[Stacks, Tag 0998], the sheaf condition at a section over an object.** A section of `𝒪`
over `U` — that is, a global section of the structure sheaf of the localized ringed site
`AlgebraicGeometry.RingedSite.over X U` — lies in the vanishing locus of `K ∈ D(𝒪_U)` as soon as
its restriction along every arrow of some covering sieve of `U` does.

This is `memVanishingIdeal_of_coversTop` at the ringed site `𝒞/U`, whose final object is
`U ⟶ U`, with the covering family produced from the sieve by `coversTop_over_sieve`. It is the
form the local-generation argument of [Stacks, Tag 099F] needs: a section of the ideal sheaf
generated by `f_1, …, f_r` over `U` is only locally an `𝒪`-combination of the generators, by
`AlgebraicGeometry.RingedSite.mem_generatedIdealSheaf_iff`. -/
theorem memVanishingIdeal_over_of_locally
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (over X U).O)))
    (h : Presheaf.globalSections ((over X U).O.obj ⋙ forget CommRingCat.{u}))
    {S : Sieve U} (hS : S ∈ X.J U)
    (hK : ∀ (W : X.C) (g : W ⟶ U) (_ : S.arrows g),
      MemVanishingIdeal ((over X U).over (Over.mk g))
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (over X U).O)
          (Over.mk g)).mapDerivedCategory.obj K)
        (globalSectionOver (over X U) (Over.mk g) h)) :
    MemVanishingIdeal (over X U) K h :=
  memVanishingIdeal_of_coversTop (over X U) h K (coversTop_over_sieve X U hS)
    fun p => hK p.1 p.2.1 p.2.2

end Local

end AlgebraicGeometry.RingedSite

end
