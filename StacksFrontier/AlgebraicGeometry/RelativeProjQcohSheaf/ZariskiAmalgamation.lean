module

public import StacksFrontier.AlgebraicGeometry.OpensCoverHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleWitnessOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SmallModel

/-!
# The amalgamation half of step (1), reduced to a glueing of quadruples

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and fix an integer `d`.
Step (1) of the proof of Tag 01NV is that the functor `F_d` of Section 01NS is a **Zariski
sheaf**. Its separatedness half is proved unconditionally in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ZariskiSeparated`, and
`...RelativeProjQcohSheaf.SmallModel.Fd.isSheaf_functor_of_exists_amalgamation` reduces the whole
to the amalgamation half: compatible families on covering sieves have amalgamations.

That statement is still phrased on the big Zariski site — covering sieves, families of elements
indexed by all the arrows of a sieve, and classes whose morphism to `S` is part of the datum.
This file removes all of that, and what is left is a statement about quadruples:

`Fd.QuadrupleGlues`: for a morphism `f : T ⟶ S`, a family of opens covering `T` and quadruples
over the restrictions of `f` to the members which are pairwise strictly equivalent over the
overlaps, there is a quadruple over `f` whose restrictions are strictly equivalent to the given
ones.

`Fd.quadrupleGlues_iff_isSheaf` says that this is **equivalent** to step (1), so the reduction
loses nothing: what remains to be proved is neither more nor less than the sheaf property.

## The three things that are removed

*The sieve.* A covering sieve of the Zariski topology contains a jointly surjective family of
open immersions (`AlgebraicGeometry.Scheme.exists_cover_of_mem_grothendieckTopology`), and an
open immersion is an isomorphism onto its image, so the family may be taken to be the inclusions
of a family of opens. Recovering the value of the family at an *arbitrary* arrow `g : Y ⟶ T` of
the sieve from the amalgamation over the opens is where the already-proved separatedness is used
a second time: the opens `g ⁻¹ᵁ W a` cover `Y`, and on each of them the two sides agree by the
compatibility of the family, applied to the square `(g ⁻¹ᵁ W a).ι ≫ g = g ∣_ W a ≫ (W a).ι` of
`AlgebraicGeometry.morphismRestrict_ι`. That is `Fd.exists_amalgamation_of_opens`.

*The morphism to `S`.* A class in `F_d(T)` records a morphism `T ⟶ S`, so a compatible family
over a covering carries a family of morphisms `W a ⟶ S` agreeing on the overlaps, and the glued
class must lie over a morphism `T ⟶ S` restricting to them. That morphism is **constructed**,
not assumed: `AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover` glues morphisms of
schemes along an arbitrary covering by opens. So `Fd.exists_amalgamation_opens_of_quadrupleGlues`
asks only for a quadruple over the glued morphism.

*The quotient.* A class is a quadruple modulo strict equivalence, and the two are related here by
`Fd.exists_rep_of_fst` — a class whose recorded morphism is a given one is the class of a
quadruple over that morphism — and by `Fd.mk_eq_mk_iff_over`, which identifies equality of
classes of quadruples over two base morphisms that are only *equal* with
`...RelativeProjQcohSheaf.Quadruple.StrictlyEquivalentOver`, the relation of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleWitnessOverBase.lean`. That is what
puts the overlap data in the shape a glueing argument consumes: an isomorphism
`...Quadruple.witnessOver` of the invertible modules over each overlap, with the cocycle
condition on the triple overlaps free (`...Quadruple.witnessOver_trans`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleGlues`: **the glueing problem for
  quadruples**, the content of step (1) with the site, the base morphism and the quotient removed.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.mk_eq_mk_iff_over`: two quadruples over base
  morphisms that need not be identical have the same class in `F_d(T)` exactly when the morphisms
  are equal and the quadruples are strictly equivalent over that equality.
* `...Fd.exists_amalgamation_opens_of_quadrupleGlues`: **the morphism to `S` is glued, not
  assumed**: a compatible family of classes on a covering by opens has an amalgamation as soon as
  quadruples glue.
* `...Fd.exists_amalgamation_of_opens`: **the amalgamation half of step (1) on the big Zariski
  site follows from its open-cover form.**
* `...Fd.isSheaf_functor_of_quadrupleGlues`: **step (1) follows from the glueing problem for
  quadruples**, and `...Fd.quadrupleGlues_of_isSheaf` is the converse, so
* `...Fd.quadrupleGlues_iff_isSheaf`: **the glueing problem for quadruples is exactly step
  (1)**, which is what makes the reduction exact rather than a weakening.

## Not done here

`QuadrupleGlues` is not proved **in this file**; what is proved here is only that it is
equivalent to step (1). It is proved downstream, as
`...RelativeProjQcohSheaf.quadrupleGlues_proof` in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean`, which therefore
turns `Fd.isSheaf_functor_of_quadrupleGlues` below into the unconditional
`...RelativeProjQcohSheaf.Fd.isSheaf_functor` stated there.

The two statements of Tag 01NV in `...RelativeProjQcohSheaf.SmallModel` still **bind** the
Zariski sheaf property as the hypothesis `hsheaf`, and so do the two in
`...RelativeProjQcohSheaf.QuadrupleSmall`: all four are upstream of the proof — this file
imports `SmallModel`, and `QuadrupleGluesProof` imports this file — so the binder cannot be
removed from them without making the import graph circular. The forms of Tag 01NV that do not
bind it are stated downstream instead, as
`...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'` and
`...Fd.isRepresentable_functor_of_charts'` in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`.

Two of the three pieces that the glueing asks for are supplied in
`...RelativeProjQcohSheaf.QuadrupleGlueInputs`:

* the comparisons of the invertible modules, and their cocycle condition, at **every** common
  refinement of two or three of the opens — `...Quadruple.chartWitness` and
  `...Quadruple.chartWitness_trans`, which rest on
  `...Quadruple.strictlyEquivalentOver_of_common`. The hypothesis of `QuadrupleGlues` is phrased
  over the intersections `W a ⊓ W b` alone, whereas a glueing datum compares two charts over a
  scheme mapping into both; the upgrade costs nothing new.
* the **surjectivity of the degree-one component of the glued `ψ`**, which is formal:
  `...RelativeProjQcohSheaf.epi_of_pullbackFamily_epi_cover` and
  `...epi_of_pullbackFamily_comp_epi_cover` derive it from
  `Stacks.Descent.epi_of_pullback_map_epi`, the locality of epimorphisms in the inverse-image
  form, whose proof is a cancellation. **No stalk criterion enters**: in particular
  `Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections` and `...epi_iff_stalk_surjective`
  are not used, and no identification of the stalk of an inverse image along an open immersion
  with a stalk of the original sheaf is needed.

* the **invertible module `L` itself**, glued from the invertible modules of the given
  quadruples. This is
  `...RelativeProjQcohSheaf.exists_modulesGlueData_invertible`, in
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue`. The bridge it rests
  on is `...RelativeProjQcohSheaf.compComparison_eq_pullbackComp_inv`: the two contractions of an
  iterated inverse image — `AlgebraicGeometry.Scheme.Modules.pullbackComp`, which
  `Stacks.SheafOfModules.chartPullbackRestrict` is assembled from, and
  `...RelativeProjQcohSheaf.compComparison`, which `...Quadruple.witnessOver_pullback` produces —
  are the same morphism. They are *not* equal by `rfl`; what identifies them is
  `Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app`.

What is genuinely missing is the map `ψ` in every integral degree.
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` glues it degree by
degree and `...RelativeProjQcohSheaf.mul_of_pullbackFamily_mul_cover` and
`...one_of_pullback_map_cover` supply the two laws of a `...RelativeProjQcohSheaf.Twisting`.

It used to be recorded here that what the glueing hypothesis still needed was the compatibility
of the comparisons of the glued `L` with the local invertible modules with
`...Quadruple.chartWitness`, and that `...ModulesGlueData.ofChartIso` does not record it. That
compatibility is now `...RelativeProjQcohSheaf.quadrupleGlueData_trans_chartSectionsIso`, for the
named datum `...RelativeProjQcohSheaf.quadrupleGlueData`; at the level of a glueing datum it is
`Stacks.SheafOfModules.ModulesGlueData.trans_chartSectionsIso`, the triangle
`φ i j ∘ φ i = φ j`. The transport of the local maps `(P a).twisting.app i` into the restriction
of `(laurent G.glued).piece i` — the `i`-th integral tensor power of the chart comparison in
every degree, with its multiplicativity and its unit normalisation — is not owed either: it is
`...RelativeProjQcohSheaf.laurentPullbackCongrIso` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullbackCongr`, with
`...laurentPullbackCongrIso_mul` and `...laurentPullbackCongrIso_zero`, and the local datum is
`...RelativeProjQcohSheaf.chartLocalApp`.

All **three laws of the glued family** are available: the multiplicativity, the unit law and the
surjectivity of the degree-one component are `...RelativeProjQcohSheaf.mul_of_chartLocal_cover`,
`...one_of_chartLocal_cover` and `...epi_of_chartLocal_cover`.

What is owed is the compatibility hypothesis of `existsUnique_hom_of_restrict_cover`. It is no
longer owed *because* it is an equation of maps on sections: both halves of that passage are in
place. `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` reduces the
hypothesis for an arbitrary pair of members to an equation of **morphisms** of inverse images
over a common refinement, `...RelativeProjQcohSheaf.chartLocalApp_eq_ofPullback` puts the local
datum in the `...ModuleHomGlue.ofPullback` form that reduction consumes, and
`...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct` is
`...quadrupleGlueData_trans_chartSectionsIso` as an equation of morphisms. The **composition law
for the chart comparison** — how `...RelativeProjQcohSheaf.laurentPullbackCongrIso` along `k ≫ a`
relates to the inverse image along `k` of the one along `a` — is no longer missing either: it is
`...RelativeProjQcohSheaf.laurentPullbackCongrIso_comp`, with
`...laurentPullbackCongrIso_pullback` its form at a refinement of a single chart. It used to be
recorded here that its second half was absent, the functoriality `...LaurentCongr.congrIso` of
the Laurent algebra in its invertible module having no naturality in the base scheme; that
naturality is `...LaurentCongr.congrIso_laurentPullback` and the functoriality of the comparison
in the module itself, which the law also needs, is `...LaurentCongr.congrIso_trans`, both in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/LaurentCongrNaturality.lean`.

What is left is to assemble those with the pairwise strict equivalences, and what stands in the
way are two vocabulary crossings rather than a missing law: the identification
`a^*G.glued ≅ (P a).L` that `...RelativeProjQcohSheaf.chartLocalApp` consumes has to be read off
`Stacks.SheafOfModules.ModulesGlueData.chartIso`, which is stated for the restriction along `a`
and not the inverse image, and the relation between two such identifications over a common
refinement has to be read off
`...RelativeProjQcohSheaf.quadrupleGlueData_restrictFunctor_map_chartAdjunct`, which is an
equation of morphisms of restrictions over an open of `T` and not of inverse images along the two
morphisms out of the refinement.

## No tag is claimed

Step (1) is an ingredient of the proof of Tag 01NV, not a clause of a tag, and nothing here
proves it; the tag's carriers are in `...RelativeProjQcohSheaf.SmallModel` and
`...RelativeProjQcohSheaf.Representable`.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-! ### Classes of quadruples over base morphisms that are equal -/

/-- A class in `F_d(T)` whose recorded morphism to `S` is a given one is the class of a quadruple
over that morphism. -/
theorem Fd.exists_rep_of_fst {T : Scheme.{u}} (ζ : Fd A d T) {k : T ⟶ S} (hk : ζ.1 = k) :
    ∃ P : Quadruple k A d, Fd.mk k P = ζ := by
  obtain ⟨k', q⟩ := ζ
  subst hk
  obtain ⟨P, hP⟩ := Quotient.exists_rep q
  exact ⟨P, congrArg (fun r => (⟨k', r⟩ : Fd A d T)) hP⟩

/-- **Two quadruples over base morphisms that need not be identical have the same class in
`F_d(T)` exactly when the morphisms are equal and the quadruples are strictly equivalent over
that equality.** -/
theorem Fd.mk_eq_mk_iff_over {T : Scheme.{u}} {f f' : T ⟶ S}
    (P : Quadruple f A d) (Q : Quadruple f' A d) :
    Fd.mk f P = Fd.mk f' Q ↔ ∃ h : f = f', Quadruple.StrictlyEquivalentOver h P Q := by
  refine ⟨fun hEq => ?_, fun ⟨h, he⟩ => ?_⟩
  · have hb : f = f' := congrArg (fun ζ : Fd A d T => ζ.1) hEq
    subst hb
    exact ⟨rfl, (Quadruple.strictlyEquivalentOver_rfl_iff P Q).mpr ((Fd.mk_eq_mk_iff P Q).mp hEq)⟩
  · subst h
    exact (Fd.mk_eq_mk_iff P Q).mpr ((Quadruple.strictlyEquivalentOver_rfl_iff P Q).mp he)

/-- The two liftings of the intersection of two members of a family of opens of `T` have the same
composite with a morphism `f : T ⟶ S`. -/
theorem overlapBase_eq {T : Scheme.{u}} (f : T ⟶ S) {ι : Type*} (W : ι → T.Opens) (a b : ι) :
    T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a) ≫ ((W a).ι ≫ f) =
      T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b) ≫ ((W b).ι ≫ f) := by
  rw [← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- Two pullbacks of classes of quadruples are equal exactly when the composite base morphisms are
equal and the pulled back quadruples are strictly equivalent over that equality. -/
private theorem pullback_mk_eq_pullback_mk_iff_over {T₁ T₂ T' : Scheme.{u}} {f₁ : T₁ ⟶ S}
    {f₂ : T₂ ⟶ S} (g₁ : T' ⟶ T₁) (g₂ : T' ⟶ T₂) (P₁ : Quadruple f₁ A d) (P₂ : Quadruple f₂ A d) :
    Fd.pullback g₁ (Fd.mk f₁ P₁) = Fd.pullback g₂ (Fd.mk f₂ P₂) ↔
      ∃ h : g₁ ≫ f₁ = g₂ ≫ f₂,
        Quadruple.StrictlyEquivalentOver h (P₁.pullback g₁) (P₂.pullback g₂) := by
  rw [Fd.pullback_mk, Fd.pullback_mk]
  exact Fd.mk_eq_mk_iff_over _ _

/-! ### The glueing problem for quadruples -/

/-- **The glueing problem for quadruples**: for every morphism `f : T ⟶ S`, every family of opens
covering `T` and every family of quadruples over the restrictions of `f` to the members which are
pairwise strictly equivalent over the overlaps, there is a quadruple over `f` whose restrictions
are strictly equivalent to the given ones. -/
def QuadrupleGlues (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (d : ℤ) : Prop :=
  ∀ (T : Scheme.{u}) (f : T ⟶ S) (ι : Type u) (W : ι → T.Opens), (∀ x : T, ∃ a, x ∈ W a) →
    ∀ P : (a : ι) → Quadruple ((W a).ι ≫ f) A d,
      (∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
          ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
          ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)))) →
        ∃ Q : Quadruple f A d, ∀ a, Quadruple.StrictlyEquivalent (Q.pullback (W a).ι) (P a)

/-- **A compatible family of classes on a covering by opens has an amalgamation as soon as
quadruples glue, the morphism to `S` being glued rather than assumed.** A class in `F_d(T)`
records a morphism `T ⟶ S`, so the family carries morphisms `W a ⟶ S` agreeing on the overlaps;
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover` glues them to a morphism `f : T ⟶ S`,
`Fd.exists_rep_of_fst` presents each member of the family as the class of a quadruple over the
restriction of `f`, and `Fd.mk_eq_mk_iff_over` turns the compatibility into the strict
equivalences over the overlaps that `QuadrupleGlues` consumes. -/
theorem Fd.exists_amalgamation_opens_of_quadrupleGlues (hglue : QuadrupleGlues A d)
    (T : Scheme.{u}) (ι : Type u) (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (ξ : ∀ a, Fd A d (W a).toScheme)
    (hcompat : ∀ a b, Fd.pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)) (ξ a) =
      Fd.pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)) (ξ b)) :
    ∃ t : Fd A d T, ∀ a, Fd.pullback (W a).ι t = ξ a := by
  have hbase : ∀ a b, T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a) ≫ (ξ a).1 =
      T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b) ≫ (ξ b).1 :=
    fun a b => congrArg (fun ζ : Fd A d (W a ⊓ W b).toScheme => ζ.1) (hcompat a b)
  obtain ⟨f, hf, -⟩ :=
    Scheme.existsUnique_hom_of_opens_cover W hW (fun a => (ξ a).1) hbase
  choose P hP using fun a => Fd.exists_rep_of_fst (ξ a) (hf a).symm
  have hoverlap : ∀ a b, Quadruple.StrictlyEquivalentOver (overlapBase_eq f W a b)
      ((P a).pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)))
      ((P b).pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))) := fun a b =>
    ((pullback_mk_eq_pullback_mk_iff_over _ _ _ _).mp
      (by rw [hP a, hP b]; exact hcompat a b)).choose_spec
  obtain ⟨Q, hQ⟩ := hglue T f ι W hW P hoverlap
  refine ⟨Fd.mk f Q, fun a => ?_⟩
  rw [Fd.pullback_mk, ← hP a]
  exact (Fd.mk_eq_mk_iff _ _).mpr (hQ a)

/-! ### From a covering sieve to a covering by opens -/

/-- **The amalgamation half of step (1) on the big Zariski site follows from its open-cover
form.** A covering sieve contains a jointly surjective family of open immersions, whose images
are a covering by opens whose inclusions are again in the sieve; the amalgamation over that
covering is an amalgamation for the whole sieve because `F_d` is a separated presheaf
(`...ZariskiSeparated.Fd.eq_of_pullback_eq_of_cover`): for an arbitrary arrow `g : Y ⟶ T` of the
sieve the opens `g ⁻¹ᵁ W a` cover `Y`, and over each of them the two sides agree by the
compatibility of the family applied to `AlgebraicGeometry.morphismRestrict_ι`. -/
theorem Fd.exists_amalgamation_of_opens
    (hopens : ∀ (T : Scheme.{u}) (ι : Type u) (W : ι → T.Opens), (∀ x : T, ∃ a, x ∈ W a) →
      ∀ ξ : ∀ a, Fd A d (W a).toScheme,
        (∀ a b, Fd.pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)) (ξ a) =
          Fd.pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)) (ξ b)) →
        ∃ t : Fd A d T, ∀ a, Fd.pullback (W a).ι t = ξ a)
    (T : Scheme.{u}) (Sv : Sieve T) (hSv : Sv ∈ Scheme.zariskiTopology.{u} T)
    (x : Presieve.FamilyOfElements (Fd.functor A d) (Sv : Sieve T).arrows)
    (hx : x.Compatible) : ∃ t, x.IsAmalgamation t := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hSv
  have hmemf : ∀ i, (Sv : Sieve T).arrows (𝒰.f i) := fun i => hle _ _ (Presieve.ofArrows.mk i)
  have hmem : ∀ i, (Sv : Sieve T).arrows ((𝒰.f i).opensRange).ι := by
    intro i
    have h := Sv.downward_closed (hmemf i) (𝒰.f i).isoOpensRange.inv
    rwa [Scheme.Hom.isoOpensRange_inv_comp] at h
  have hWcov : ∀ y : T, ∃ i, y ∈ (𝒰.f i).opensRange := by
    intro y
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq y
    exact ⟨i, z, hz⟩
  obtain ⟨t, ht⟩ := hopens T 𝒰.I₀ (fun i => (𝒰.f i).opensRange) hWcov
    (fun i => x ((𝒰.f i).opensRange).ι (hmem i)) fun i j =>
      hx (T.homOfLE inf_le_left) (T.homOfLE inf_le_right) (hmem i) (hmem j)
        (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  refine ⟨t, fun Y g hg => ?_⟩
  change Fd.pullback g t = x g hg
  refine Fd.eq_of_pullback_eq_of_cover (fun i => g ⁻¹ᵁ (𝒰.f i).opensRange) (fun y => ?_) _ _
    fun i => ?_
  · exact hWcov (g.base y)
  · have h1 : Fd.pullback (g ⁻¹ᵁ (𝒰.f i).opensRange).ι (Fd.pullback g t) =
        Fd.pullback (g ∣_ (𝒰.f i).opensRange) (x ((𝒰.f i).opensRange).ι (hmem i)) := by
      rw [← Fd.pullback_comp, ← morphismRestrict_ι, Fd.pullback_comp, ht i]
    have h2 : Fd.pullback (g ⁻¹ᵁ (𝒰.f i).opensRange).ι (x g hg) =
        Fd.pullback (g ∣_ (𝒰.f i).opensRange) (x ((𝒰.f i).opensRange).ι (hmem i)) :=
      hx (g ⁻¹ᵁ (𝒰.f i).opensRange).ι (g ∣_ (𝒰.f i).opensRange) hg (hmem i)
        (morphismRestrict_ι g ((𝒰.f i).opensRange)).symm
    rw [h1, h2]

/-- **`F_d` is a Zariski sheaf as soon as quadruples glue**, which is step (1) of the proof of Tag
01NV reduced to a statement with no sieve, no base morphism and no quotient in it. The
separatedness half is `...ZariskiSeparated.Fd.isSeparated_functor`, fed in through
`...SmallModel.Fd.isSheaf_functor_of_exists_amalgamation`. -/
theorem Fd.isSheaf_functor_of_quadrupleGlues (hglue : QuadrupleGlues A d) :
    Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d) :=
  Fd.isSheaf_functor_of_exists_amalgamation A d fun T Sv hSv x hx =>
    Fd.exists_amalgamation_of_opens
      (Fd.exists_amalgamation_opens_of_quadrupleGlues hglue) T Sv hSv x hx

/-! ### The reduction is exact -/

/-- **The glueing problem for quadruples is a consequence of step (1)**, so the reduction is not a
weakening.

A family of opens covering `T` is a Zariski covering (`AlgebraicGeometry.Scheme.
openCoverOfIsOpenCover`), the classes of the given quadruples form a compatible family of
elements of that covering — the compatibility at an arbitrary pair of morphisms into two members
reduces to the compatibility over the intersection because the intersection of two opens is the
fibre product of their inclusions (`AlgebraicGeometry.isPullback_opens_inf`) — and the
amalgamation lies over `f` by the uniqueness half of
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover`. -/
theorem Fd.quadrupleGlues_of_isSheaf
    (hsheaf : Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d)) :
    QuadrupleGlues A d := by
  intro T f ι W hW P hP
  have hcov : IsOpenCover W := top_le_iff.mp fun x _ => Opens.mem_iSup.mpr (hW x)
  have hmem : Sieve.generate (Presieve.ofArrows (fun a => (W a).toScheme)
      (fun a => (W a).ι)) ∈ Scheme.zariskiTopology.{u} T :=
    Scheme.mem_grothendieckTopology_iff.mpr
      ⟨T.openCoverOfIsOpenCover W hcov, Sieve.le_generate _⟩
  have hsf : Presieve.IsSheafFor (Fd.functor A d)
      (Presieve.ofArrows (fun a => (W a).toScheme) (fun a => (W a).ι)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact (isSheaf_iff_isSheaf_of_type _ _).1 hsheaf _ hmem
  have hcompat : Presieve.Arrows.Compatible (Fd.functor A d) (fun a => (W a).ι)
      (fun a => Fd.mk ((W a).ι ≫ f) (P a)) := by
    intro a b Z ga gb hgab
    set k := (isPullback_opens_inf (W a) (W b)).lift ga gb hgab
    have hk : k ≫ T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a) = ga :=
      (isPullback_opens_inf (W a) (W b)).lift_fst ga gb hgab
    have hk' : k ≫ T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b) = gb :=
      (isPullback_opens_inf (W a) (W b)).lift_snd ga gb hgab
    have hmid : Fd.pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a))
          (Fd.mk ((W a).ι ≫ f) (P a)) =
        Fd.pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b))
          (Fd.mk ((W b).ι ≫ f) (P b)) :=
      (pullback_mk_eq_pullback_mk_iff_over _ _ _ _).mpr ⟨overlapBase_eq f W a b, hP a b⟩
    change Fd.pullback ga (Fd.mk ((W a).ι ≫ f) (P a)) =
      Fd.pullback gb (Fd.mk ((W b).ι ≫ f) (P b))
    rw [← hk, ← hk', Fd.pullback_comp, Fd.pullback_comp, hmid]
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsf _ hcompat
  have hbase : ∀ a, (W a).ι ≫ t.1 = (W a).ι ≫ f := fun a =>
    congrArg (fun ζ : Fd A d (W a).toScheme => ζ.1) (ht a)
  have hteq : t.1 = f :=
    (Scheme.existsUnique_hom_of_opens_cover W hW (fun a => (W a).ι ≫ f)
      (overlapBase_eq f W)).unique hbase fun _ => rfl
  obtain ⟨Q, hQ⟩ := Fd.exists_rep_of_fst t hteq
  refine ⟨Q, fun a => (Fd.mk_eq_mk_iff _ _).mp ?_⟩
  rw [← Fd.pullback_mk, hQ]
  exact ht a

/-- **The glueing problem for quadruples is exactly step (1) of the proof of Tag 01NV**: neither
more nor less is left to prove. -/
theorem Fd.quadrupleGlues_iff_isSheaf :
    QuadrupleGlues A d ↔ Presheaf.IsSheaf Scheme.zariskiTopology.{u} (Fd.functor A d) :=
  ⟨Fd.isSheaf_functor_of_quadrupleGlues, Fd.quadrupleGlues_of_isSheaf⟩

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
