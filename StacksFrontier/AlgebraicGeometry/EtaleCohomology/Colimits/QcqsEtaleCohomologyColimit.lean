module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleCohomologyColimit

/-! # Cohomology of a limit of schemes with affine transitions, general levels (Stacks 09YQ)

Let `I` be a directed set, let `(X_i)` be an inverse system of schemes over `I` whose transition
morphisms are affine, and let `X = lim X_i`. Stacks 0EYL exhibits the small affine etale site of
`X` as the colimit of the small affine etale sites of the `X_i`, and the weak-system form of
Stacks 09YP computes the cohomology of a colimit of abelian sheaves on a colimit of sites over an
object of a level.

`Stacks.EtaleCohomology.AffineLimitCohomology` assembles these two for *affine* `X_i`, where `X_i`
is itself the terminal object of its own small affine etale site. This file carries the assembly
out for **arbitrary** `X_i` — only the transition morphisms are affine — and over an **arbitrary**
object `Z` of the small affine etale site of `X_i` rather than over `X_i` itself. Nothing in the
five inputs of Stacks 09YP that Stacks 0EYL supplies uses the affineness of the levels, so the
colimit statement is available in that generality; what the affineness was used for, and what is
therefore missing here, is only the identification of the object the cohomology is taken over.

For a merely quasi-compact and quasi-separated `X_i` that identification is the Cech /
Mayer-Vietoris step: `X_i` is not an object of its own small *affine* etale site, so one covers it
by a finite affine cover and descends. This file supplies the covering input of that step —
`exists_finite_jointlySurjective_smallAffineEtale` — and does not perform the descent.

What the descent step is *not* needed for is the affine opens of `X_i`: an affine open is an
object of the small affine etale site of `X_i`, an open immersion being etale, so
`etaleCohomologyColimit_isColimit_affineOpen` is the colimit statement over an affine open with
nothing descended. The object the descent has to reach is `X_i` itself, and the whole of the
affineness in the affine case of Stacks 03Q6 is the one hypothesis
`AlgebraicGeometry.hasTerminal_smallAffineEtale` carries: the small *affine* etale site of `X_i`
has a terminal object only for an affine `X_i`. By the cohomological form of Stacks 04HR
(`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.affineEtaleCohomologyFunctorIso`, which carries no
affineness hypothesis on its scheme) the etale cohomology of any `X_i` is the *global* cohomology
of that site; the affineness is only in the reading of the global cohomology as the cohomology
over an object. Two routes therefore reach the quasi-compact quasi-separated case, and each is
missing one theorem:

1. **Global cohomology.** Stacks 09YP for the global cohomology of a colimit of sites rather than
   for the cohomology over an object of a level. The degree-zero case is
   `InverseSystemOfFiniteSites.globalSections_colimit_pullback_of_colimit` in
   `StacksFrontier/CategoryTheory/Sites/InverseSystem/GlobalSectionsOfColimitOfFiniteSites.lean`,
   whose module documentation states this need in the same terms; the higher degrees are absent.
2. **A site with a terminal object.** Stacks 0EYL for the small etale sites cut down to the
   *quasi-compact quasi-separated* objects instead of the affine ones. That subsite of
   `AlgebraicGeometry.SmallEtale` contains `AlgebraicGeometry.SmallEtale.final`, which is terminal
   with no affineness hypothesis, and its objects still descend through the system — a qcqs etale
   morphism is of finite presentation, which is step (1) of the source's own proof — so the
   cohomology over its terminal object is the etale cohomology of `X_i` and Stacks 09YQ applies
   over it unchanged. The colimit-of-sites statement at that subsite is absent.

Either route still owes the two further inputs the registered affine case owes: the system of
sheaves has to be the inverse images of a single sheaf on `X`, and the comparison with etale
cohomology has to be natural in the index.

## Main results

* `objOfAffineOpen`, `structMap_objOfAffineOpen`: an affine open `U` of a scheme `S` contained in
  a big etale site is an object of the small affine etale site of `S`, with structure morphism the
  open immersion `U.ι`. No affineness of `S` is needed: an open immersion is etale.
* `exists_finite_jointlySurjective_smallAffineEtale`: **the covering input of the Cech step.** A
  quasi-compact `S` is covered by finitely many objects of its own small affine etale site.
* `etaleCohomologyCocone`: the canonical cohomology cocone over an arbitrary object of a level.
* `etaleCohomologyColimit_isColimit`: **Stacks 09YQ for arbitrary levels, over an arbitrary
  object of a level.**
* `affineOpenObject` and `etaleCohomologyColimit_isColimit_affineOpen`: **the colimit statement
  over an affine open of a level**, with no descent step at all. An affine open of a level is an
  object of that level's small affine etale site, by `objOfAffineOpen` and the small model of the
  level, so the previous result applies to it verbatim.

## Implementation notes

The abelian sheaf system `F`, the sheaf `𝒢` presenting its colimit, the legs `ι` and the
presentation `hcolim` are hypotheses, exactly as in Stacks 09YP and as in the source, where
`F = colim f_i^{-1} F_i` is given data rather than a construction. The cocone `E` is a hypothesis
for the same reason the affine case makes it one: its fields pin the diagram and the legs to the
canonical cohomology maps, and `etaleCohomologyCocone` exhibits one, so the statement is not
vacuous.

The cohomology is the right-derived `sheafSections` of the weak-system Stacks 09YP on the small
affine etale sites, not the library's mainstream etale cohomology of a scheme; the comparison
across Stacks 04HR is not performed here, and the clause string of the tag says so.

Only quasi-compactness of `S` is used in `exists_finite_jointlySurjective_smallAffineEtale`.
Quasi-separatedness enters the Cech step further on, where it makes the intersections of the
members of the cover quasi-affine; it is not needed to produce the cover itself.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology.QcqsLimitCohomology

open AlgebraicGeometry Stacks.EtaleCohomology.AffineLimitCohomology
open CategoryTheory.Sites.InverseSystem

/-! ### Affine opens as objects of the small affine etale site -/

section Opens

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine open of `S` is an object of the small affine etale site of `S`.** An open
immersion is etale, so the inclusion `U ⟶ S` of an affine open is an affine etale object over
`S`; and the source of an open immersion into a scheme of the big etale site again belongs to
that site (Stacks 000R (3)). No affineness of `S` is required, which is what makes this the
entry point for the quasi-compact case. -/
def objOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    AlgebraicGeometry.SmallAffineEtale B S hS :=
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI hc : B.Contains (U : Scheme.{u}) := Scheme.size_lt_of_isOpenImmersion U.ι hS
  ⟨⟨Over.mk (B.inclusion.preimage (X := B.obj (U : Scheme.{u}) hc) (Y := B.obj S hS) U.ι), by
      change AlgebraicGeometry.Etale (B.inclusion.map (B.inclusion.preimage _))
      rw [Functor.map_preimage]
      infer_instance⟩, by
    change AlgebraicGeometry.IsAffine (U : Scheme.{u})
    infer_instance⟩

/-- The structure morphism of the object attached to an affine open is the open immersion. -/
lemma structMap_objOfAffineOpen (U : S.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    structMap B S hS (objOfAffineOpen B S hS U hU) = U.ι :=
  B.inclusion.map_preimage _

/-- **The covering input of the Cech / Mayer-Vietoris step.** A quasi-compact scheme `S` of a big
etale site is covered by finitely many objects of its own small affine etale site: the affine
opens form a basis, so every point lies in one, and quasi-compactness extracts a finite
subfamily. This is what makes a quasi-compact and quasi-separated `S`, which is not itself an
object of that site unless it is affine, accessible from inside it. The descent of cohomology
along such a cover is not carried out in this file. -/
theorem exists_finite_jointlySurjective_smallAffineEtale [CompactSpace S] :
    ∃ (K : Type u) (_ : Finite K) (Z : K → AlgebraicGeometry.SmallAffineEtale B S hS),
      ∀ x : S, ∃ (k : K) (y : (AlgebraicGeometry.SmallAffineEtale.toScheme B S hS).obj (Z k)),
        (structMap B S hS (Z k)).base y = x := by
  classical
  have hpt : ∀ x : S, ∃ U : S.Opens, AlgebraicGeometry.IsAffineOpen U ∧ x ∈ U := by
    intro x
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose U hUaff hUmem using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S => (U x : Set S))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hUmem x⟩
  refine ⟨{x : S // x ∈ t}, inferInstance,
    fun k => objOfAffineOpen B S hS (U k.1) (hUaff k.1), fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  refine ⟨⟨y, hy⟩, ⟨x, hxy⟩, ?_⟩
  exact congrArg (fun f : (U y : Scheme.{u}) ⟶ S => f.base ⟨x, hxy⟩)
    (structMap_objOfAffineOpen B S hS (U y) (hUaff y))

end Opens

/-! ### The colimit statement for arbitrary levels -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

open Stacks.WeakSites.ColimitSiteCohomology in
/-- The canonical cohomology cocone of the system over an arbitrary object `Z` of the level `i`:
the diagram of the groups `H^p(u_a(Z), F_j)` indexed by the arrows `a : j ⟶ i`, together with its
cocone at `H^p(u_i(Z), 𝒢)`. This exhibits the hypothesis `E` of
`etaleCohomologyColimit_isColimit`. -/
def etaleCohomologyCocone
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (i : (sys D c B hD hX hc).I) (Z : (sys D c B hD hX hc).C i) (p : ℕ) :
    CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i Z p :=
  cohomologyCocone.{v, v, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc)
    F 𝒢 ι hcolim i Z p

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Stacks 09YQ for arbitrary levels, over an arbitrary object of a level.** Let `I` be a
directed set, let `(X_i)` be an inverse system of schemes over `I` whose transition morphisms are
affine, and let `X = lim X_i`. Let `F` be a system of abelian sheaves on the small affine etale
sites of the `X_i`, let `𝒢` on the small affine etale site of `X` present the colimit
`colim f_i^{-1} F_i`, let `Z` be an object of the small affine etale site of `X_i` and let `p` be
a degree. Then `H^p(Z_X, 𝒢)`, the cohomology over the image of `Z` in the site of the limit, is
the filtered colimit, over the arrows `a : j ⟶ i`, of the groups `H^p(Z_j, F_j)` over the
transition images of `Z`: the canonical cocone is a colimit cocone.

The schemes `X_i` are arbitrary here; only the transition morphisms are affine. This is Stacks
09YP, in its weak-system form, applied to the colimit of sites of Stacks 0EYL through
`mem_limitSitePrecoverage_iff` and the three descent clauses of that file, none of which uses any
affineness of the levels.

Specialized to affine `X_i` and `Z` the terminal object of the site of `X_i`, the objects carrying
the cohomology are `X_j` and `X`, which is the affine case
`Stacks.EtaleCohomology.AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine`. For a
merely quasi-compact and quasi-separated `X_i` there is no such terminal object, and the passage
from the charts `Z` to `X_i` is the Cech / Mayer-Vietoris step along a finite affine cover; this
file supplies only its covering input,
`exists_finite_jointlySurjective_smallAffineEtale`. -/
@[stacks 09YQ "the general case of the levels: the schemes `X_i` are arbitrary — only the \
transition morphisms are affine — and the cohomology is taken over an arbitrary object `Z` of the \
small affine etale site of `X_i`, whose transition images and whose image in the site of the \
limit carry the groups of the diagram and the vertex. For an affine `X_i` the terminal object of \
that site is `X_i` itself and this specializes to the affine case already recorded in \
`Stacks.EtaleCohomology.AffineLimitCohomology`; for a merely quasi-compact and quasi-separated \
`X_i`, which is NOT an object of its own small affine etale site, the identification of this \
cohomology with `H^p(X_i, F_i)` is the Cech / Mayer-Vietoris descent along a finite affine cover \
and is NOT performed here — only the covering input is, in \
`exists_finite_jointlySurjective_smallAffineEtale`. The sites are the small AFFINE etale sites \
and the cohomology is the right-derived `sheafSections` of the weak-system Stacks 09YP on them, \
not the library's mainstream etale cohomology of a scheme, the comparison across Stacks 04HR not \
being performed here. No hypothesis of this statement is an instance of its own conclusion.",
  no_expose]
def etaleCohomologyColimit_isColimit
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (i : (sys D c B hD hX hc).I) (Z : (sys D c B hD hX hc).C i) (p : ℕ)
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i Z p) :
    IsColimit E.cocone :=
  isColimitCohomologyCocone.{v, v, max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc)
    (toLimitSmall_obj_descends D c B hD hX hc)
    (toLimitSmall_hom_descends D c B hD hX hc)
    (toLimitSmall_hom_eventually_eq D c B hD hX hc)
    (limitSitePrecoverage D c B hX)
    (mem_limitSitePrecoverage_iff D c B hD hX hc)
    F 𝒢 ι hcolim i Z p E

/-! ### The colimit statement over an affine open of a level -/

section AffineOpen

variable (i : (sys D c B hD hX hc).I)

/-- The stage of `Iᵒᵖ` that the level `i` of the site system of Stacks 0EYL sits over. -/
abbrev levelStage : Iᵒᵖ :=
  (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj i

/-- **An affine open of a level is an object of that level's site.** The level `i` of the site
system of Stacks 0EYL is a small model of the small affine etale site of the scheme `X_j` it sits
over, and an affine open of `X_j` is an object of that site by `objOfAffineOpen`, an open
immersion being etale. No affineness of `X_j` is needed. -/
def affineOpenObject (U : (D.obj (levelStage D c B hD hX hc i)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) : (sys D c B hD hX hc).C i :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).inverse.obj
    (objOfAffineOpen B (D.obj (levelStage D c B hD hX hc i))
      (hD (levelStage D c B hD hX hc i)) U hU)

open Stacks.WeakSites.ColimitSiteCohomology in
/-- **Stacks 09YQ over an affine open of a level.** Let `I` be a directed set, let `(X_i)` be an
inverse system of schemes whose transition morphisms are affine, let `X = lim X_i`, let `F` be a
system of abelian sheaves on the small affine etale sites of the `X_i` and let `𝒢` present the
colimit `colim f_i^{-1}F_i`. Let `U` be an *affine open* of the scheme `X_j` the level `i` sits
over, and `p` a degree. Then the canonical cohomology cocone over the object `U` of the level is a
colimit cocone.

The levels are arbitrary here — only the transition morphisms are affine, and no affineness of
`X_j` is used — so this is the colimit statement at the affine opens of a quasi-compact
quasi-separated level, with no Cech or Mayer-Vietoris descent performed and none needed: it is
`etaleCohomologyColimit_isColimit` at `Z = affineOpenObject`, the object of the level's site that
the affine open is.

The groups the cocone is built from are the right-derived `sheafSections` of the level sites over
the transition images of that object, and those images are *not* identified here with the preimage
opens of `U` in the lower levels; `AffineEtaleSiteColimit.transition_isPullback` is the geometric
input of that identification. -/
def etaleCohomologyColimit_isColimit_affineOpen
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (𝒢 : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ j, (F.obj j).obj ⟶ (toLimitSmall D c B hD hX hc j).op ⋙ 𝒢.obj)
    (hcolim : IsColimitPresentation.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι)
    (U : (D.obj (levelStage D c B hD hX hc i)).Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) (p : ℕ)
    (E : CohomologyCocone.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) F 𝒢 ι i
      (affineOpenObject D c B hD hX hc i U hU) p :=
      etaleCohomologyCocone D c B hD hX hc F 𝒢 ι hcolim i
        (affineOpenObject D c B hD hX hc i U hU) p) :
    IsColimit E.cocone :=
  etaleCohomologyColimit_isColimit D c B hD hX hc F 𝒢 ι hcolim i
    (affineOpenObject D c B hD hX hc i U hU) p E

end AffineOpen

end Stacks.EtaleCohomology.QcqsLimitCohomology

end
