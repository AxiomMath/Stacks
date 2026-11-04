module

public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.LimitOfSheafedSpaces
public import StacksFrontier.Topology.Sheaves.Limits.DescendOpensAbelian
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change to the limit space, and abelian Stacks 01FF applied to the pullback system

The two colimit-comparison clauses of Stacks 0A37 assert that
`colim_{a : j → i} Hᑫ(f_a⁻¹U, 𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, 𝒜)` is an isomorphism, where
`𝒜 = colimⱼ p_j⁻¹𝒜ⱼ` on the limit space.  The proof of Stacks 0A37 factors that map as

1. **base change to the limit space**, `Hᑫ(f_a⁻¹U, 𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ)`, followed by
2. **the comparison of the colimit**, `colimⱼ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, colimⱼ p_j⁻¹𝒜ⱼ)`,

and this file supplies both halves of that factorization in the spelling of the tag.

Step 2 is the easy half, and it is *done here, unconditionally and in every degree*: it is
abelian Stacks 01FF on the limit space (`SpectralDiagram.isIso_colimit_post_H'functor_comapProj`,
itself unconditional since `Stacks.Cohomology.AbelianBasis.cechToCohomologyOnBasis` discharged
abelian Stacks 01EW) applied to `SpectralAbelianSheafSystem.abelianPullbackSystem`, over the
quasi-compact open `p_i⁻¹U`.

Step 1 is supplied here as an *arrow*, not yet as an isomorphism: the germ-model pullback
`p_j⁻¹𝒜ⱼ` carried by the limit space is an abelian sheafed space, and
`GermPullback.toPushforwardPresheaf` makes the projection `p_j` into a morphism of abelian
sheafed spaces out of it.  Applying `Tag0A37Uniqueness.spaceCohomologyMap` to that morphism
gives the base-change map on `Sheaf.H'` in every degree, with the functoriality laws
`spaceCohomologyMap_id` and `spaceCohomologyMap_comp` available.  That is the arrow whose
invertibility *in the colimit* is the remaining content of the two clauses; see the
implementation notes.

## Main definitions

* `SpectralAbelianSheafSystem.pullbackSpace`: the limit space carrying the germ-model pullback
  `p_j⁻¹𝒜ⱼ`, as an object of `SheafedSpace AddCommGrpCat`.
* `SpectralAbelianSheafSystem.pullbackProjection`: the projection `p_j` as a morphism of abelian
  sheafed spaces `pullbackSpace j ⟶ S.E.obj j`, with sheaf component the unit
  `𝒜ⱼ ⟶ (p_j)_* p_j⁻¹𝒜ⱼ`.

## Main results

* `SpectralAbelianSheafSystem.isIso_colimit_post_H'functor_abelianPullbackSystem`:
  **step 2, in every degree, unconditionally** —
  `colimⱼ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, colimⱼ p_j⁻¹𝒜ⱼ)` is an isomorphism for every
  quasi-compact open `U` of a stage and every degree `q`.
* `nonempty_H'functor_zero_iso_abSections`: in degree zero, native cohomology over `U` is
  sections over `U`, as functors on abelian sheaves.  This is what identifies the degree-zero
  case of the two clauses with the abelian Stacks 0A33,
  `SpectralAbelianSheafSystem.isColimitAbelianStageCocone`.
* `SheafedSpaceLimit.existsUnique_mapOut_pull_eq`: **the sheaf on the vertex of a limiting cone
  of abelian sheafed spaces is `colimⱼ pⱼ⁻¹Fⱼ`**, corepresented, with the inverse images taken in
  the germ model and the arrows out of them phrased in germ-model language.
* `SheafedSpaceLimit.isLimitWhiskerOverForget`: the cone `c.whisker (Over.forget i)` of the stage
  clause of Tag 0A37 is a limiting cone, so the vertex characterizations apply to it too.

## Implementation notes

### What is proved and what is not

The two clauses need, beyond what is here, exactly step 1 **in the colimit**:

  `colim_{a : j → i} Hᑫ(f_a⁻¹U, 𝒜ⱼ) ⟶ colimⱼ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ)` is an isomorphism.

In degree zero this is the abelian Stacks 0A33
(`isColimitAbelianStageSectionsCocone`, with `isColimitAbelianStageCocone` folding step 2 in).
In positive degrees it is *not* a formal consequence of the degree-zero case, and it is not an
instance of the fixed-space induction either: the index-wise map
`Hᑫ(f_a⁻¹U, 𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ)` is **not** an isomorphism for a single `a` — already in
degree zero `(p_j⁻¹𝒜ⱼ)(p_j⁻¹V)` is `colim_{b : k → j} (f_b⁻¹𝒜ⱼ)(f_b⁻¹V)` and not `𝒜ⱼ(V)` — so
this is a statement about a colimit of a natural transformation and not about
`Limits.colimit.post` of a functor.  `CategoryTheory.DeltaFunctor.isIso_colimit_post_of_isIso_zero`
is therefore not applicable to it, which is why step 2 comes out of the box here and step 1 does
not.

The route in Stacks 0A37 for step 1 is the injective embedding **of the system**: choose
`𝒜ⱼ ↪ ℐⱼ` into injective abelian sheaves and set `𝒢ᵢ = ∏_{b : k → i} f_{b,*}ℐₖ`, which is a
system of injectives (`Tag0A37.preservesInjectiveObjects_sheafPushforward` gives injectivity of
each factor, a product of injectives is injective), compare the two long exact sequences of
`0 → 𝒜 → 𝒢 → 𝒢/𝒜 → 0` levelwise and on the limit, and conclude by the four lemma as in Stacks
01FF.  The positive-degree vanishing needed on the limit side is Čech: by Stacks 0A30 a finite
cover of a quasi-compact open of the limit by quasi-compact opens descends to a stage, and
degree zero (abelian Stacks 0A33) then presents the Čech complex of `colimⱼ p_j⁻¹𝒢ⱼ` as the
filtered colimit of the Čech complexes of the `𝒢ⱼ`, each acyclic in positive degrees because an
injective abelian sheaf is flasque (`AbelianVanishing.isZero_cechComplex_homology_of_injective`).
None of that is in the tree.

Note that `AbelianVanishing.isZero_cechComplex_homology_colimit_of_injective` does **not** apply
to `colimⱼ p_j⁻¹𝒢ⱼ`: it requires the system to consist of injective sheaves *on the limit
space*, and `p_j⁻¹` does not preserve injectives.

### The germ model and the limit cone

`pullbackProjection` is the first morphism of abelian sheafed spaces out of a germ-model
pullback, and it exists only because `GermPullback.toPushforwardPresheaf` supplies the unit
`𝒜ⱼ ⟶ (p_j)_* p_j⁻¹𝒜ⱼ`.

`SheafedSpaceLimit.existsUnique_mapOut_pull_eq` is the abstract counterpart: for a *limiting*
cone `c` of abelian sheafed spaces it characterizes `c.pt.presheaf` as `colimⱼ pⱼ⁻¹Fⱼ` in
corepresented form and **in germ-model language**, which `existsUnique_pull_eq` alone could not
do because its input is an arrow `Fₖ ⟶ (pₖ)_* H` in Mathlib's pushforward language.  The
germ-model universal property `GermPullback.existsUnique_mapOut` supplies that translation and
shows it to be bijective.  What is still not available from it is an actual `colimit` in the
sheaf category on the abstract vertex: that needs the germ-model system over an abstract cone,
whereas the system built in `DescendOpensAbelian` is over the concrete limit `S.invLim`.  So the
remaining statements of this file are about `S.invLim` and `colimit S.abelianPullbackSystem`.

## References

* [Stacks Project, Tag 0A30](https://stacks.math.columbia.edu/tag/0A30)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology

/-! ### Degree zero: native cohomology over an open is sections over it -/

namespace AbelianColimit

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **In degree zero, native sheaf cohomology over `U` is sections over `U`**, as functors on
abelian sheaves.  Native cohomology is right-derived sections
(`nonempty_H'functor_iso_rightDerived`) and sections over `U` are left exact
(`preservesFiniteLimits_abSections`), so the degree-zero right-derived functor is the functor
itself by `Functor.rightDerivedZeroIsoSelf`.

This is the identification under which the degree-zero case of the two colimit-comparison
clauses of Stacks 0A37 becomes the abelian Stacks 0A33.  As with
`nonempty_H'functor_iso_rightDerived`, only existence is asserted: the comparison of `Sheaf.H'`
with right-derived sections is a choice. -/
theorem nonempty_H'functor_zero_iso_abSections (U : Opens X) :
    Nonempty (H'functor U 0 ≅ abSections U) :=
  ⟨(nonempty_H'functor_iso_rightDerived U 0).some ≪≫ (abSections U).rightDerivedZeroIsoSelf⟩

end AbelianColimit

/-! ### The vertex sheaf of a limiting cone, in germ-model terms -/

namespace SpectralLimit.SheafedSpaceLimit

variable {K : Type*} [Category K] {E : K ⥤ SheafedSpace.{u + 1, u, u} AddCommGrpCat.{u}}
  (c : Cone E) (H : (c.pt : TopCat.{u}).Presheaf AddCommGrpCat.{u})
  (hH : TopCat.Presheaf.IsSheaf H)

/-- **The cone of the stage clause of Tag 0A37 is a limiting cone.**  The stage clause is stated
about `c.whisker (Over.forget i)`, and `Over.forget i` is an *initial* functor when the index
category is cofiltered (`CategoryTheory.Over.initial_forget`); restricting a limiting cone along
an initial functor leaves a limiting cone.  So every statement proved about a limiting cone — in
particular `existsUnique_pull_eq` and `existsUnique_mapOut_pull_eq` — applies to the stage clause
as well as to the global one, with no further hypothesis. -/
@[sga "4 V 8.1.5" "special case"]
def isLimitWhiskerOverForget {K : Type*} [Category K] [IsCofiltered K] {D : Type*} [Category D]
    (E : K ⥤ D) {c : Cone E} (hc : IsLimit c) (i : K) :
    IsLimit (c.whisker (Over.forget i)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc

/-- **The map `Fₖ ⟶ (pₖ)_* H` adjoint to a map out of the germ-model inverse image `pₖ⁻¹Fₖ`**:
compose with the unit of the germ model.  By `GermPullback.existsUnique_mapOut` this is a
bijection onto the maps `Fₖ ⟶ (pₖ)_* H`, which are the arrows that
`SheafedSpaceLimit.existsUnique_pull_eq` takes as input. -/
def pushAdj (k : K)
    (ψ : GermPullback.abelianPresheaf
      (ConcreteCategory.hom (c.π.app k).hom.base) (E.obj k).presheaf ⟶ H) :
    (E.obj k).presheaf ⟶ (c.π.app k).hom.base _* H :=
  GermPullback.toPushforwardPresheaf (c.π.app k).hom.base (E.obj k).presheaf ≫
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (c.π.app k).hom.base).map ψ

/-- **The sheaf on the vertex of a limiting cone of abelian sheafed spaces is the colimit of the
germ-model inverse images of the sheaves at the stages**, corepresented by an arbitrary sheaf `H`
on the space underlying the vertex, and phrased entirely in germ-model language.

Given a family of maps `ψ k : pₖ⁻¹Fₖ ⟶ H` out of the germ-model inverse images, compatible with
the transition maps of `E`, there is a unique map of sheaves `g : c.pt.presheaf ⟶ H` on the vertex
whose `k`-th component — the adjoint of the `k`-th projection's sheaf map followed by `g`, i.e.
`GermPullback.mapOut` applied to `pull c H g k` — is `ψ k`.

This is `existsUnique_pull_eq` made consumable: that theorem characterizes the vertex sheaf in
corepresented form, but its input is a family `Fₖ ⟶ (pₖ)_* H` in Mathlib's pushforward language,
and the germ model offers no such arrow by itself.  The unit
`GermPullback.toPushforwardPresheaf` supplies one from each `ψ k`, and
`GermPullback.existsUnique_mapOut` says that the resulting correspondence is bijective, so the two
characterizations are the same statement.  No limits in `SheafedSpace AddCommGrpCat` are used, and
no restriction on the universes of the index category is needed. -/
theorem existsUnique_mapOut_pull_eq (hc : IsLimit c)
    (ψ : ∀ k, GermPullback.abelianPresheaf
      (ConcreteCategory.hom (c.π.app k).hom.base) (E.obj k).presheaf ⟶ H)
    (hψ : ∀ {i j : K} (a : i ⟶ j),
      leg c H hH i (pushAdj c H i (ψ i)) ≫ E.map a =
        leg c H hH j (pushAdj c H j (ψ j))) :
    ∃! g : c.pt.presheaf ⟶ H, ∀ k,
      GermPullback.mapOut (c.π.app k).hom.base (pull c H g k) hH = ψ k := by
  obtain ⟨g, hg, hgu⟩ := existsUnique_pull_eq c H hH hc (fun k ↦ pushAdj c H k (ψ k)) hψ
  have hiff : ∀ (g' : c.pt.presheaf ⟶ H) (k : K),
      GermPullback.mapOut (c.π.app k).hom.base (pull c H g' k) hH = ψ k ↔
        pull c H g' k = pushAdj c H k (ψ k) := by
    intro g' k
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [← h]
      exact (GermPullback.toPushforwardPresheaf_comp_mapOut (c.π.app k).hom.base
        (pull c H g' k) hH).symm
    · rw [h]
      exact (GermPullback.mapOut_unique (c.π.app k).hom.base
        (pushAdj c H k (ψ k)) hH rfl).symm
  exact ⟨g, fun k ↦ (hiff g k).2 (hg k), fun g' h ↦ hgu g' fun k ↦ (hiff g' k).1 (h k)⟩

end SpectralLimit.SheafedSpaceLimit

/-! ### Base change to the limit space, and the comparison of the colimit -/

namespace SpectralLimit.SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **The limit space carrying the germ-model pullback `p_j⁻¹𝒜ⱼ`**, as an abelian sheafed space.
This is the target of base change from the stage `j`: the space is `X = limⱼ Xⱼ` and the sheaf is
`GermPullback.abelianSheaf` of the stage sheaf along the projection. -/
def pullbackSpace (j : J) : SheafedSpace.{u + 1, u, u} AddCommGrpCat.{u} where
  carrier := S.invLim
  presheaf := (S.abelianPullback j).presheaf
  IsSheaf := (S.abelianPullback j).2

/-- The underlying space of `pullbackSpace` is the limit of the stages. -/
lemma pullbackSpace_carrier (j : J) : ((S.pullbackSpace j) : TopCat.{u}) = S.invLim := rfl

/-- The sheaf on `pullbackSpace j` is the germ-model pullback of the stage sheaf. -/
lemma pullbackSpace_sheaf (j : J) :
    (S.pullbackSpace j).presheaf = (S.abelianPullback j).presheaf := rfl

/-- **Base change to the limit space, as a morphism of abelian sheafed spaces.**  The projection
`p_j : X ⟶ Xⱼ` together with the unit `𝒜ⱼ ⟶ (p_j)_* p_j⁻¹𝒜ⱼ` of the germ model
(`GermPullback.toPushforwardPresheaf`) is a morphism
`(X, p_j⁻¹𝒜ⱼ) ⟶ (Xⱼ, 𝒜ⱼ)` of abelian sheafed spaces.

`Tag0A37Uniqueness.spaceCohomologyMap` applied to this morphism is the base-change map
`Hᑫ(V, 𝒜ⱼ) ⟶ Hᑫ(p_j⁻¹V, p_j⁻¹𝒜ⱼ)` in every degree, and it satisfies the functoriality laws
`spaceCohomologyMap_id` and `spaceCohomologyMap_comp`.  It is the first factor of the
factorization of the comparison of Stacks 0A37. -/
def pullbackProjection (j : J) : S.pullbackSpace j ⟶ S.E.obj j :=
  InducedCategory.homMk
    { base := S.typeSystem.diagram.proj j
      c := GermPullback.toPushforwardPresheaf (S.typeSystem.diagram.proj j)
        (S.E.obj j).presheaf }

/-- The base map of `pullbackProjection` is the projection to the stage. -/
lemma pullbackProjection_base (j : J) :
    (S.pullbackProjection j).hom.base = S.typeSystem.diagram.proj j := rfl

/-- The sheaf component of `pullbackProjection` is the unit of the germ model. -/
lemma pullbackProjection_c (j : J) :
    (S.pullbackProjection j).hom.c =
      GermPullback.toPushforwardPresheaf (S.typeSystem.diagram.proj j)
        (S.E.obj j).presheaf := rfl

section Stage

variable {i : J} (U : Opens (S.E.obj i))

/-- **The comparison of the colimit, in every degree, unconditionally** — step 2 of the
factorization of the comparison of Stacks 0A37.  For a quasi-compact open `U` of the stage `Xᵢ`
and every degree `q`, the canonical map

  `colimⱼ Hᑫ(p_i⁻¹U, p_j⁻¹𝒜ⱼ) ⟶ Hᑫ(p_i⁻¹U, colimⱼ p_j⁻¹𝒜ⱼ)`

is an isomorphism.

This is abelian Stacks 01FF on the limit space
(`SpectralDiagram.isIso_colimit_post_H'functor_comapProj`) applied to the abelian pullback
system.  The open `p_i⁻¹U` is quasi-compact because the projections are spectral maps, and the
limit of a cofiltered diagram of spectral spaces is spectral, so no hypothesis is left over; the
index `Jᵒᵖ` is filtered because `J` is cofiltered.

It is *all* of the all-degrees content that the fixed-space induction supplies: what remains for
the two clauses is step 1 in the colimit, which is the injective-embedding part of the proof of
Stacks 0A37 and is not an instance of that induction. -/
theorem isIso_colimit_post_H'functor_abelianPullbackSystem
    (hU : IsCompact (U : Set (S.E.obj i))) (q : ℕ) :
    IsIso (colimit.post S.abelianPullbackSystem
      (AbelianColimit.H'functor (S.limOpen U) q)) :=
  S.typeSystem.diagram.isIso_colimit_post_H'functor_comapProj i U hU S.abelianPullbackSystem q

/-- The degree-zero case of `isIso_colimit_post_H'functor_abelianPullbackSystem` is abelian
Stacks 009F (4) on the limit space, the second input of abelian Stacks 0A33. -/
theorem isIso_colimit_post_sheafSections_abelianPullbackSystem
    (hU : IsCompact (U : Set (S.E.obj i))) :
    IsIso (colimit.post S.abelianPullbackSystem (S.sectionsFunctor U)) :=
  S.typeSystem.diagram.isIso_colimit_post_sheafSections_comapProj i U hU S.abelianPullbackSystem

end Stage

/-! ### A spectral abelian sheaf system exists

The statements of this file, and the four clauses of Tag 0A37 itself, quantify over
`SpectralAbelianSheafSystem` and over a quasi-compact open of a stage.  A declaration can be
axiom-clean and still say nothing, if its hypotheses are jointly unsatisfiable, and
`#print axioms` cannot see that.  The witness below rules that out: a one-point space is
spectral, the constant sheaf at a terminal object of `AddCommGrpCat` is a sheaf on it, and the
constant diagram over the one-object category is a spectral abelian sheaf system whose stage
`⊤` is quasi-compact. -/

/-- A one-point space is spectral: it is `T₀`, compact, quasi-sober and quasi-separated, and
every open of a finite space is compact so it is prespectral.  The five parent instances are all
found; only their assembly is missing, and `SpectralSpace` is not otherwise known to be
inhabited anywhere in the tree. -/
instance instSpectralSpaceUnit : SpectralSpace Unit := ⟨⟩

/-- The one-point abelian sheafed space, carrying the constant sheaf at a terminal object. -/
def ptSpace : SheafedSpace.{1, 0, 0} AddCommGrpCat.{0} where
  carrier := TopCat.of Unit
  presheaf := (Functor.const _).obj (⊤_ AddCommGrpCat.{0})
  IsSheaf := SheafedSpaceLimit.isSheaf_constTerminal AddCommGrpCat.{0} (TopCat.of Unit)

/-- **A spectral abelian sheaf system exists**: the constant diagram at `ptSpace` over the
one-object category.  Every transition map is the identity, which is a spectral map. -/
def ptSystem : SpectralAbelianSheafSystem.{0, 0, 0} Unit where
  E := (Functor.const Unit).obj ptSpace
  spectralSpace _ := instSpectralSpaceUnit
  spectralMap _ := isSpectralMap_id

/-- The quasi-compactness hypothesis of the statements above is satisfiable at `ptSystem`: the
whole one-point space is quasi-compact.  So none of them is vacuous. -/
theorem isCompact_top_ptSystem :
    IsCompact ((⊤ : Opens (ptSystem.E.obj ())) : Set (ptSystem.E.obj ())) := by
  have hc : CompactSpace ((ptSystem.E.obj () : TopCat.{0}) : Type) :=
    inferInstanceAs (CompactSpace Unit)
  simp only [Opens.coe_top]
  exact isCompact_univ

/-- The identity cone on the constant diagram at `ptSpace`. -/
def ptCone : Cone ptSystem.E where
  pt := ptSpace
  π := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ rfl }

/-- **A limiting cone of abelian sheafed spaces exists.**  `SheafedSpace AddCommGrpCat` has no
limits at this Mathlib revision, so the hypothesis `IsLimit c` carried by the four clauses of
Tag 0A37 — and by `SheafedSpaceLimit.existsUnique_pull_eq` and
`SheafedSpaceLimit.existsUnique_mapOut_pull_eq` — is not known to be satisfiable from any general
theorem.  It is: the constant diagram over the one-object category has the identity cone as a
limiting cone, so none of those statements is vacuous. -/
def isLimitPtCone : IsLimit ptCone where
  lift s := s.π.app ()
  fac _ _ := Category.comp_id _
  uniq _ m h := (Category.comp_id m).symm.trans (h ())

end SpectralLimit.SpectralAbelianSheafSystem

end Stacks.Cohomology

end
