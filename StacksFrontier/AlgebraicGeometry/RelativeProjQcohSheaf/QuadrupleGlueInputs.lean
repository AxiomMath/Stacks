module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TwistingLocal
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiAmalgamation

/-!
# The inputs the glueing problem for quadruples consumes

`...RelativeProjQcohSheaf.QuadrupleGlues` is the content of step (1) of the proof of Tag 01NV
with the site, the base morphism and the quotient removed
(`...RelativeProjQcohSheaf.Fd.quadrupleGlues_iff_isSheaf`): a morphism `f : T ⟶ S`, a family of
opens covering `T`, and quadruples over the restrictions of `f` which are pairwise strictly
equivalent over the overlaps, must produce a quadruple over `f` restricting to them. This file
proves the parts of that production which need no new descent theory.

## The comparisons, and their cocycle condition, hold at every common refinement

A glueing datum of sheaves of modules compares two charts over a scheme mapping into both, not
over the intersection of the chart images: the chart modules live on different schemes, so there
is nowhere else to compare them. The hypothesis of `QuadrupleGlues` is phrased over the
intersection `W a ⊓ W b` alone, and
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalentOver_of_common` upgrades it to every
common refinement: for any `Y` with `a : Y ⟶ W i` and `b : Y ⟶ W j` satisfying
`a ≫ (W i).ι = b ≫ (W j).ι`, the two pulled-back quadruples are strictly equivalent over the
resulting equality of base morphisms. The upgrade costs nothing new — the intersection of two
opens is the fibre product of their inclusions (`AlgebraicGeometry.isPullback_opens_inf`), so
such a pair factors through it, and `...Quadruple.strictlyEquivalent_pullback_comp` absorbs the
two reassociations. It is **not** an equality of quadruples that is used here: `(P.pullback g)`
pulled back again is only *strictly equivalent* to `P.pullback (g' ≫ g)`.

Consequently the comparison isomorphism `a^*L_i ≅ b^*L_j` of the invertible modules
(`...Quadruple.chartWitness`) and its cocycle condition on a triple
(`...Quadruple.chartWitness_trans`) are available at every common refinement, with no hypothesis
beyond the pairwise equivalences — the comparisons are determined, not chosen
(`...Quadruple.witnessOver_trans`).

## The surjectivity of the degree-one component of a glued `ψ` is formal

Being an epimorphism of sheaves of modules is local on the base, and this repository has that in
the inverse-image form `Stacks.Descent.epi_of_pullback_map_epi`, whose proof is a cancellation.
So `...RelativeProjQcohSheaf.epi_of_pullbackFamily_epi_cover`: a family of homogeneous
components whose degreewise pullback along each member of a covering family of open immersions is
an epimorphism in degree `n` has an epimorphism in degree `n`. The two comparisons out of which
`...RelativeProjQcohSheaf.pullbackFamily` is built are isomorphisms, so they cancel, and
`...RelativeProjQcohSheaf.epi_of_pullbackFamily_comp_epi_cover` allows a further isomorphism on
the target — the shape in which a glueing argument meets the hypothesis, where what is known is
the surjectivity of the given local `ψ_1`, read through the comparison of the glued invertible
module with the local one.

**No stalk theory is involved**, and in particular the pointwise criteria
`Stacks.SheafOfModules.StalkEpiMono.epi_iff_stalk_surjective` and `...epi_of_exists_sections`
are not used: the locality of epimorphisms is formal in the categorical phrasing of
surjectivity.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.chartWitness`: **the comparison of
  the inverse images of the invertible modules of two members of the family over a common
  refinement of their opens.**

## Main results

* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalentOver_of_common`: **the pairwise strict
  equivalences over the intersections extend to every common refinement.**
* `...RelativeProjQcohSheaf.Quadruple.chartWitness_trans`: **the cocycle condition for those
  comparisons, over a common refinement of three of the opens.**
* `...RelativeProjQcohSheaf.epi_of_pullbackFamily_epi_cover` and
  `...epi_of_pullbackFamily_comp_epi_cover`: **the surjectivity of a homogeneous component of a
  glued `ψ` follows from the surjectivity of the local ones**, with no stalk criterion.
* `...RelativeProjQcohSheaf.iSup_opensRange_ι_eq_top`: the covering hypothesis of
  `QuadrupleGlues`, which is stated pointwise, in the form the locality statements consume.

## What is still missing

The map `ψ` in every integral degree. The glueing of the invertible module itself is no longer
missing: the comparisons and the cocycle condition produced here are carried into the vocabulary
of `Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue`, by
`...RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv` — the contraction
`AlgebraicGeometry.Scheme.Modules.pullbackComp` that
`Stacks.SheafOfModules.chartPullbackRestrict` is assembled from and the contraction
`...RelativeProjQcohSheaf.compComparison` that `...Quadruple.witnessOver_pullback` produces are
the same morphism. They are indeed *not* equal by `rfl`; the step with content is
`Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`, which identifies the comparison map
with the components of the composition isomorphism by injectivity of the hom-set bijection of the
adjunction, after which `...modulePullbackCompIso_eq_pullbackComp_symm` is `rfl`.

What the glueing of `ψ` additionally needs is for the comparisons of the glued module with the
local ones to be compatible with the comparisons produced here, which is a statement about the
glued module, not about the quadruples, and which
`...ModulesGlueData.ofChartIso` does not record.

## No tag is claimed

Nothing here states a clause of a tag; Tag 01NV's carriers are in
`...RelativeProjQcohSheaf.SmallModel` and `...RelativeProjQcohSheaf.Representable`.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace

universe v u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### The covering hypothesis -/

/-- The covering hypothesis of `...RelativeProjQcohSheaf.QuadrupleGlues`, which is stated
pointwise, in the form the locality statements for sheaves of modules consume. -/
theorem iSup_opensRange_ι_eq_top {T : Scheme.{u}} {ι : Type*} (W : ι → T.Opens)
    (hW : ∀ x : T, ∃ a, x ∈ W a) : ⨆ a, ((W a).ι).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ?_
  obtain ⟨a, ha⟩ := hW x
  exact ⟨a, by rwa [Scheme.Opens.opensRange_ι]⟩

namespace Quadruple

/-! ### The comparisons at an arbitrary common refinement -/

/-- **The pairwise strict equivalences over the intersections extend to every common
refinement.** Let `W : ι → T.Opens` and let `P a` be a quadruple over `(W a).ι ≫ f` for each `a`,
with `P i` and `P j` strictly equivalent over the intersection `W i ⊓ W j`. Then for every scheme
`Y` and every pair of morphisms `a : Y ⟶ W i`, `b : Y ⟶ W j` with
`a ≫ (W i).ι = b ≫ (W j).ι`, the quadruples `(P i).pullback a` and `(P j).pullback b` are
strictly equivalent over the resulting equality of base morphisms. -/
theorem strictlyEquivalentOver_of_common {T : Scheme.{u}} (f : T ⟶ S) {ι : Type*}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    {Y : Scheme.{u}} (i j : ι) (a : Y ⟶ (W i).toScheme) (b : Y ⟶ (W j).toScheme)
    (hab : a ≫ (W i).ι = b ≫ (W j).ι) :
    StrictlyEquivalentOver
      (show a ≫ ((W i).ι ≫ f) = b ≫ ((W j).ι ≫ f) by
        rw [← Category.assoc, ← Category.assoc, hab])
      ((P i).pullback a) ((P j).pullback b) := by
  obtain ⟨c, ha, hb⟩ : ∃ c : Y ⟶ (W i ⊓ W j).toScheme,
      c ≫ T.homOfLE (inf_le_left : W i ⊓ W j ≤ W i) = a ∧
        c ≫ T.homOfLE (inf_le_right : W i ⊓ W j ≤ W j) = b :=
    ⟨(isPullback_opens_inf (W i) (W j)).lift a b hab,
      (isPullback_opens_inf (W i) (W j)).lift_fst a b hab,
      (isPullback_opens_inf (W i) (W j)).lift_snd a b hab⟩
  subst ha
  subst hb
  have E1 : StrictlyEquivalentOver (rfl : (c ≫ T.homOfLE (inf_le_left : W i ⊓ W j ≤ W i)) ≫
        ((W i).ι ≫ f) = _)
      ((P i).pullback (c ≫ T.homOfLE (inf_le_left : W i ⊓ W j ≤ W i)))
      (((P i).pullback (T.homOfLE (inf_le_left : W i ⊓ W j ≤ W i))).pullback c) :=
    (strictlyEquivalentOver_rfl_iff _ _).mpr
      (strictlyEquivalent_equivalence.symm
        (strictlyEquivalent_pullback_comp (P i) (T.homOfLE inf_le_left) c))
  have E2 := (hP i j).pullback c
  have E3 : StrictlyEquivalentOver (rfl : (c ≫ T.homOfLE (inf_le_right : W i ⊓ W j ≤ W j)) ≫
        ((W j).ι ≫ f) = _)
      (((P j).pullback (T.homOfLE (inf_le_right : W i ⊓ W j ≤ W j))).pullback c)
      ((P j).pullback (c ≫ T.homOfLE (inf_le_right : W i ⊓ W j ≤ W j))) :=
    (strictlyEquivalentOver_rfl_iff _ _).mpr
      (strictlyEquivalent_pullback_comp (P j) (T.homOfLE inf_le_right) c)
  exact (E1.trans E2).trans E3

/-- **The comparison of the inverse images of the invertible modules of two members of the family
over a common refinement of their opens.** This is
`...RelativeProjQcohSheaf.Quadruple.pullbackWitness` of
`...Quadruple.strictlyEquivalentOver_of_common`, and it is the isomorphism a glueing datum of
sheaves of modules records: taking `Y` to be the overlap of two chart images and `a`, `b` its two
liftings gives exactly the comparison
`Stacks.SheafOfModules.ModulesGlueData.exists_modulesGlueData_of_chartPullbackIso` consumes. -/
def chartWitness {T : Scheme.{u}} (f : T ⟶ S) {ι : Type*}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    {Y : Scheme.{u}} (i j : ι) (a : Y ⟶ (W i).toScheme) (b : Y ⟶ (W j).toScheme)
    (hab : a ≫ (W i).ι = b ≫ (W j).ι) :
    (pullbackFunctor (ringedSpaceHom a)).obj (P i).L ≅
      (pullbackFunctor (ringedSpaceHom b)).obj (P j).L :=
  pullbackWitness (strictlyEquivalentOver_of_common f W P hP i j a b hab)

/-- **The cocycle condition for the comparisons, over a common refinement of three of the
opens.** It holds with no hypothesis beyond the pairwise strict equivalences: the comparisons are
not chosen but determined by the surjectivity of the degree-one components
(`...RelativeProjQcohSheaf.Quadruple.witnessOver_trans`). -/
theorem chartWitness_trans {T : Scheme.{u}} (f : T ⟶ S) {ι : Type*}
    (W : ι → T.Opens) (P : (a : ι) → Quadruple ((W a).ι ≫ f) A d)
    (hP : ∀ a b, StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))))
    {Y : Scheme.{u}} (i j k : ι) (a : Y ⟶ (W i).toScheme) (b : Y ⟶ (W j).toScheme)
    (c : Y ⟶ (W k).toScheme) (hab : a ≫ (W i).ι = b ≫ (W j).ι)
    (hbc : b ≫ (W j).ι = c ≫ (W k).ι) :
    chartWitness f W P hP i j a b hab ≪≫ chartWitness f W P hP j k b c hbc =
      chartWitness f W P hP i k a c (hab.trans hbc) :=
  pullbackWitness_trans _ _ _

end Quadruple

/-! ### The surjectivity of a homogeneous component of a glued `ψ` -/

section Epi

variable {T S' : Scheme.{u}} {f : T ⟶ S'}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **A homogeneous component of a family is an epimorphism as soon as its degreewise pullbacks
along a covering family of open immersions are.** This is the surjectivity half of the glueing of
the map `ψ` of a quadruple, and it is formal: being an epimorphism of sheaves of modules is local
on the base in the inverse-image form `Stacks.Descent.epi_of_pullback_map_epi`, whose proof is a
cancellation, and the two comparisons out of which
`...RelativeProjQcohSheaf.pullbackFamily` is built are isomorphisms.

No stalk criterion is used; in particular
`Stacks.SheafOfModules.StalkEpiMono.epi_iff_stalk_surjective` and
`...StalkEpiMono.epi_of_exists_sections` are not needed, and no identification of the stalk of an
inverse image along an open immersion with a stalk of the original sheaf is owed. -/
theorem epi_of_pullbackFamily_epi_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤) (n : ℤ)
    (h : ∀ k : I, Epi (pullbackFamily app (g k) n)) : Epi (app n) := by
  refine Stacks.Descent.epi_of_pullback_map_epi g hg (app n) fun k => ?_
  have hk := h k
  rw [pullbackFamily] at hk
  exact (epi_comp_iff_of_isIso _ (laurentPullback (g k) L n)).mp
    ((epi_comp_iff_of_epi (compComparison (g k) f (A.piece (n * d))) _).mp hk)

/-- **The surjectivity of a homogeneous component of a glued `ψ`, in the shape a glueing argument
meets it.** What a glueing argument knows over a member of the covering is the surjectivity of the
*given* local `ψ_n`, which is the degreewise pullback of the glued family read through the
comparison `u k` of the glued invertible module with the local one; `u k` is an isomorphism, so it
cancels.

This is `...RelativeProjQcohSheaf.epi_of_pullbackFamily_epi_cover` with that comparison allowed
on the target. -/
theorem epi_of_pullbackFamily_comp_epi_cover
    (app : ∀ i : ℤ,
      (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d)) ⟶ (laurent L).piece i)
    {I : Type v} {X : I → Scheme.{u}} (g : ∀ k, X k ⟶ T) [∀ k, IsOpenImmersion (g k)]
    (hg : ⨆ k, (g k).opensRange = ⊤) (n : ℤ)
    (Q : ∀ k : I, SheafOfModules.{u} (structureRingSheaf (X k).toRingedSpace))
    (u : ∀ k : I,
      (laurent ((pullbackFunctor (ringedSpaceHom (g k))).obj L)).piece n ⟶ Q k)
    [∀ k : I, IsIso (u k)]
    (h : ∀ k : I, Epi (pullbackFamily app (g k) n ≫ u k)) : Epi (app n) := by
  exact epi_of_pullbackFamily_epi_cover app g hg n fun k => (epi_comp_iff_of_isIso _ _).mp (h k)

end Epi

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
