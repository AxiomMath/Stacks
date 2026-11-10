module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The big étale site on the category of a chosen big fppf site

A big étale site may be built on the *same* category of schemes as any chosen big fppf
site: take as its covering families exactly those families selected by the fppf site which
are, in addition, étale coverings. This is the étale half of Stacks 03FF.

That these families satisfy the site axioms is proved by conjoining the fppf site's own
axioms with membership in Mathlib's étale precoverage: the isomorphism axiom holds because
a single isomorphism is an étale covering, the composition axiom because the étale
precoverage is stable under composition, and the base-change axiom because it is stable
under base change and the size-bounded category is closed under the fibre products the
axiom produces. Combinatorial cofinality is inherited from the fppf site: an étale covering
is an fppf covering, so it has a selected fppf representative, and being étale is invariant
under combinatorial equivalence because combinatorially equivalent families generate the
same presieve.

## Main definitions

* `AlgebraicGeometry.chosenPrecoverage` presents an arbitrary class of covering families on
  the underlying category of a big fppf site as a precoverage.
* `AlgebraicGeometry.etaleCovering` is the restricted collection of covering families: the
  selected fppf coverings which are étale.
* `AlgebraicGeometry.etalePrecoverage` and `AlgebraicGeometry.etaleTopology` present that
  collection as a precoverage and as the Grothendieck topology it generates.

## Main results

* `AlgebraicGeometry.etaleCovering_isSite`: the restricted collection satisfies the site
  axioms, so it really is a big étale site and not merely a family of fppf subcoverings.
* `AlgebraicGeometry.etaleCovering_has_representative`: every étale covering of the common
  category is combinatorially equivalent to a selected one.
* `AlgebraicGeometry.chosenPrecoverage_eq_comap`, `AlgebraicGeometry.etalePrecoverage_eq_comap`
  and `AlgebraicGeometry.etaleTopology_eq_comap`: a chosen collection of covering families
  presents the comap, along the inclusion into all schemes, of a precoverage of schemes; in
  particular the selected étale families present the comap of the étale precoverage.
* `AlgebraicGeometry.exists_etaleCovering_le_of_mem_etaleTopology`: a covering sieve of the big
  étale topology carried by a chosen big fppf site contains a selected étale covering family.
* `AlgebraicGeometry.isSite_and_precoverage`,
  `AlgebraicGeometry.map_mem_iff_of_combEquiv` and
  `AlgebraicGeometry.covering_has_representative`: the two statements above with the étale
  precoverage replaced by an arbitrary one, which is how the other coarse topologies on the
  same category are treated.
* `AlgebraicGeometry.schemePrecoverage_hasIsos`,
  `AlgebraicGeometry.schemePrecoverage_stableUnderComposition` and
  `AlgebraicGeometry.schemePrecoverage_stableUnderBaseChange`: the three stability properties
  that general step asks of the precoverage, for a precoverage cut out by a morphism property.

## Implementation notes

The common underlying category is `AlgebraicGeometry.BigFppfSite.Schemes` for an
arbitrarily chosen big fppf site `B`. Intersecting its selected coverings with the étale
covering predicate gives precisely the subset stipulated in the source; in particular the
size cutoff, the covering bound and all other choices made for the fppf site are retained.

The site axioms are proved once, in the general step `isSite_and_precoverage`, for the
families whose image in schemes lies in a precoverage with isomorphisms that is stable
under composition and base change; only the two stability properties of the étale
precoverage are topology-specific. The fibre products the base-change axiom needs come from
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`, which makes
the inclusion into schemes preserve cospan limits.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace AlgebraicGeometry

/-- The precoverage of jointly surjective families of `P`-morphisms is stable under
composition as soon as `P` is. -/
public lemma schemePrecoverage_stableUnderComposition
    (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsStableUnderComposition P] :
    (Scheme.precoverage P).IsStableUnderComposition := by
  unfold Scheme.precoverage
  infer_instance

/-- The precoverage of jointly surjective families of `P`-morphisms is stable under base
change as soon as `P` is. -/
public lemma schemePrecoverage_stableUnderBaseChange
    (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsStableUnderBaseChange P] :
    (Scheme.precoverage P).IsStableUnderBaseChange := by
  have : Scheme.IsJointlySurjectivePreserving P :=
    Scheme.isJointlySurjectivePreserving P
  unfold Scheme.precoverage
  infer_instance

/-- The precoverage of jointly surjective families of `P`-morphisms has isomorphisms as soon as
every isomorphism of schemes satisfies `P`, an isomorphism being surjective. -/
public lemma schemePrecoverage_hasIsos (P : MorphismProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f], P f) :
    (Scheme.precoverage P).HasIsos := by
  refine ⟨fun {S T} f hf => ?_⟩
  exact (Scheme.singleton_mem_precoverage_iff (P := P) f).mpr
    ⟨(TopCat.homeoOfIso (asIso f.base)).surjective, hP f⟩

/-- Conjoining a class of covering families satisfying the site axioms with the condition
that the image family lies in a precoverage with isomorphisms, stable under composition and
base change, again satisfies the site axioms. -/
public lemma isSite_and_precoverage {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) (P : Covering.{u, v, max u v} C → Prop)
    (Q : Precoverage D) (hP : IsSite P)
    [Precoverage.HasIsos Q] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    [PreservesLimitsOfShape WalkingCospan F] :
    IsSite (fun E : Covering.{u, v, max u v} C =>
      P E ∧ (E.2.map F).presieve₀ ∈ Q (F.obj E.1)) := by
  rcases hP with ⟨hPIso, hPComp, hPBC⟩
  refine ⟨?_, ?_, ?_⟩
  · intro U V f hf
    refine ⟨hPIso f, ?_⟩
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.map,
      PreZeroHypercover.singleton, Presieve.ofArrows_pUnit] using
      Precoverage.HasIsos.mem_coverings_of_isIso (J := Q) (F.map f)
  · intro 𝒰 h𝒰 𝒱 h𝒱 htargets
    refine ⟨hPComp 𝒰 h𝒰.1 𝒱 (fun i => (h𝒱 i).1) htargets, ?_⟩
    have hComp := Q.comp_mem_coverings
      (fun i => F.map (𝒰.2.f i))
      (by simpa [PreZeroHypercover.map] using h𝒰.2)
      (fun i j => F.map ((𝒱 i).2.f j) ≫ F.map (eqToHom (htargets i)))
      (fun i => by
        have hi := (h𝒱 i).2
        let Ei : Q.ZeroHypercover (F.obj (𝒱 i).1) := ⟨(𝒱 i).2.map F, hi⟩
        have hf : Presieve.singleton (F.map (eqToHom (htargets i))) ∈
            Q (F.obj (𝒰.2.X i)) :=
          Precoverage.HasIsos.mem_coverings_of_isIso (J := Q) _
        have hi' := (Ei.pushforward (F.map (eqToHom (htargets i))) hf).mem₀
        simpa [Ei, PreZeroHypercover.presieve₀, PreZeroHypercover.pushforward,
          Precoverage.ZeroHypercover.pushforward, PreZeroHypercover.map] using hi')
    simpa [PreZeroHypercover.map, PreZeroHypercover.bind,
      PreZeroHypercover.pushforward, Functor.map_comp, Category.assoc] using hComp
  · intro 𝒰 h𝒰 V g
    obtain ⟨P₀, p₁, p₂, hp, hPcover⟩ := hPBC 𝒰 h𝒰.1 V g
    refine ⟨P₀, p₁, p₂, hp, hPcover, ?_⟩
    have hBC := Q.mem_coverings_of_isPullback
      (fun i => F.map (𝒰.2.f i))
      (by simpa [PreZeroHypercover.map] using h𝒰.2)
      (F.map g)
      (P := fun i => F.obj (P₀ i))
      (fun i => F.map (p₂ i)) (fun i => F.map (p₁ i))
      (fun i => Functor.map_isPullback F (hp i).flip)
    simpa [PreZeroHypercover.map] using hBC

/-- Combinatorially equivalent covering families have the same image presieve, so one of
them lies in a precoverage exactly when the other does. -/
public lemma map_mem_iff_of_combEquiv {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] (G : C ⥤ D) (K : Precoverage D)
    {E F : Covering.{u, v, max u v} C} (h : Covering.CombEquiv E F) :
    ((E.2.map G).presieve₀ ∈ K (G.obj E.1)) ↔
      ((F.2.map G).presieve₀ ∈ K (G.obj F.1)) := by
  rcases E with ⟨U, E⟩
  rcases F with ⟨V, F⟩
  change (∃ hUV : U = V,
    PreZeroHypercover.CombinatoriallyEquivalent (hUV ▸ E) F) at h
  rcases h with ⟨hUV, hEquiv⟩
  cases hUV
  have hp : (E.map G).presieve₀ = (F.map G).presieve₀ := by
    simpa [PreZeroHypercover.map] using
    congrArg (fun R : Presieve U => R.map G)
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hEquiv)
  exact ⟨fun h => hp ▸ h, fun h => hp.symm ▸ h⟩

/-- Every covering of the common category whose image lies in a precoverage below the fppf
precoverage has a representative among the families selected by the fppf site. -/
public lemma covering_has_representative (B : BigFppfSite.{u})
    (Q : Precoverage Scheme.{u})
    (hQ : Q ≤ Scheme.fppfPrecoverage)
    (E : Covering B.Schemes)
    (hE : (E.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E.1)) :
    ∃ E' : Covering B.Schemes, B.IsCovering E' ∧
      (E'.2.map B.inclusion).presieve₀ ∈ Q (B.inclusion.obj E'.1) ∧
      Covering.CombEquiv E E' := by
  have hF : IsFppfCovering E := by
    change E.2.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion E.1
    rw [Precoverage.mem_comap_iff]
    simpa [PreZeroHypercover.map] using hQ _ hE
  obtain ⟨E', hB, hCE⟩ := B.fppf_has_representative E hF
  exact ⟨E', by simpa [BigFppfSite.IsCovering] using hB,
    (map_mem_iff_of_combEquiv B.inclusion Q hCE).mp hE, hCE⟩

/-- The precoverage presented by a chosen collection of covering families on the underlying
category of a big fppf site. -/
public def chosenPrecoverage (B : BigFppfSite.{u})
    (P : Covering B.Schemes → Prop) : Precoverage B.Schemes where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ P ⟨X, E⟩}

/-- The selected étale coverings on the underlying category of a chosen big fppf site: the
families selected by the fppf site which are étale coverings. -/
@[stacks 03FF "étale coverings"]
public abbrev etaleCovering (B : BigFppfSite.{u})
    (E : Covering B.Schemes) : Prop :=
  B.IsCovering E ∧ IsEtaleCovering E

/-- The étale precoverage on the underlying category of a chosen big fppf site. -/
public abbrev etalePrecoverage (B : BigFppfSite.{u}) : Precoverage B.Schemes :=
  chosenPrecoverage B (etaleCovering B)

/-- The big étale topology on the underlying category of a chosen big fppf site. -/
@[stacks 03FF "étale topology"]
public abbrev etaleTopology (B : BigFppfSite.{u}) : GrothendieckTopology B.Schemes :=
  (etalePrecoverage B).toGrothendieck

/-- The étale precoverage of all schemes has isomorphisms and is stable under composition and
base change. -/
private theorem etalePrecoverage_hasIsos_and_stable :
    Scheme.etalePrecoverage.{u}.HasIsos ∧ Scheme.etalePrecoverage.{u}.IsStableUnderComposition ∧
      Scheme.etalePrecoverage.{u}.IsStableUnderBaseChange := by
  have : MorphismProperty.IsStableUnderComposition
      (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  refine ⟨⟨fun {_ _} f hf => ?_⟩, ?_, ?_⟩
  · let _ : IsIso f := hf
    exact Scheme.etalePretopology.has_isos f
  · unfold Scheme.etalePrecoverage
    exact schemePrecoverage_stableUnderComposition _
  · unfold Scheme.etalePrecoverage
    exact schemePrecoverage_stableUnderBaseChange _

/-- **Stacks 03FF.** The étale subcollection of a chosen big fppf site satisfies the site
axioms. -/
@[stacks 03FF "étale site"]
public theorem etaleCovering_isSite (B : BigFppfSite.{u}) :
    IsSite (etaleCovering B) := by
  have ⟨_, _, _⟩ := etalePrecoverage_hasIsos_and_stable.{u}
  exact isSite_and_precoverage B.inclusion B.IsCovering
    Scheme.etalePrecoverage B.isSite

/-- **Stacks 03FF.** Every étale covering of the common category is combinatorially
equivalent to a selected étale covering. -/
@[stacks 03FF "étale covering representatives"]
public theorem etaleCovering_has_representative (B : BigFppfSite.{u})
    (E : Covering B.Schemes) (hE : IsEtaleCovering E) :
    ∃ E' : Covering B.Schemes,
      etaleCovering B E' ∧ Covering.CombEquiv E E' := by
  obtain ⟨E', hB, hEt, hCE⟩ := covering_has_representative B
    Scheme.etalePrecoverage Scheme.etalePrecoverage_le_fppfPrecoverage E hE
  exact ⟨E', ⟨hB, hEt⟩, hCE⟩

/-! ### The chosen precoverage as a comap, and the families inside a covering sieve -/

/-- A chosen collection of covering families on the underlying category of a big fppf site
presents the comap, along the site's inclusion into all schemes, of a precoverage of schemes,
provided every chosen family lies in that precoverage and every family of the precoverage has a
chosen representative. -/
public theorem chosenPrecoverage_eq_comap (B : BigFppfSite.{u}) (K : Precoverage Scheme.{u})
    (P : Covering B.Schemes → Prop)
    (hP : ∀ E : Covering B.Schemes, P E →
      (E.2.map B.inclusion).presieve₀ ∈ K (B.inclusion.obj E.1))
    (hrep : ∀ E : Covering B.Schemes,
      (E.2.map B.inclusion).presieve₀ ∈ K (B.inclusion.obj E.1) →
      ∃ E' : Covering B.Schemes, P E' ∧ Covering.CombEquiv E E') :
    chosenPrecoverage B P = K.comap B.inclusion := by
  ext X R
  rw [Precoverage.mem_comap_iff]
  change (∃ E : PreZeroHypercover.{u + 1} X, R = E.presieve₀ ∧ P ⟨X, E⟩) ↔ _
  constructor
  · rintro ⟨E, rfl, hE⟩
    rw [← PreZeroHypercover.presieve₀_map]
    exact hP ⟨X, E⟩ hE
  · intro hR
    let E : PreZeroHypercover.{u + 1} X := ⟨R.uncurry, fun i => i.1.1, fun i => i.1.2⟩
    have hE : E.presieve₀ = R := by
      funext Y g
      refine propext ⟨?_, fun hg => Presieve.ofArrows.mk (⟨⟨Y, g⟩, hg⟩ : R.uncurry)⟩
      rintro ⟨i⟩
      exact i.2
    obtain ⟨E', hE', hCE⟩ := hrep ⟨X, E⟩ (by rwa [PreZeroHypercover.presieve₀_map, hE])
    rcases hCE with ⟨hXE, hcomb⟩
    cases hXE
    exact ⟨E'.2, hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb), hE'⟩

/-- The big étale precoverage carried by a chosen big fppf site is the étale precoverage of all
schemes comapped along the site's inclusion: a selected étale family is étale, and every étale
family of the bounded category has a selected étale representative. -/
public theorem etalePrecoverage_eq_comap (B : BigFppfSite.{u}) :
    etalePrecoverage B = Scheme.etalePrecoverage.comap B.inclusion :=
  chosenPrecoverage_eq_comap B Scheme.etalePrecoverage (etaleCovering B)
    (fun _ hE => hE.2) (etaleCovering_has_representative B)

/-- The big étale topology carried by a chosen big fppf site is generated by the comap, along
the site's inclusion, of the étale precoverage of all schemes. -/
public theorem etaleTopology_eq_comap (B : BigFppfSite.{u}) :
    etaleTopology B = (Scheme.etalePrecoverage.comap B.inclusion).toGrothendieck :=
  congrArg Precoverage.toGrothendieck (etalePrecoverage_eq_comap B)

/-- The selected étale covering families present a precoverage with isomorphisms, stable under
composition and base change, and admitting the fibre products of a covering family with an
arbitrary morphism to its target. All four transport along
`AlgebraicGeometry.etalePrecoverage_eq_comap` from the corresponding properties of the étale
precoverage of all schemes, the inclusion of the bounded category preserving fibre products. -/
public theorem etalePrecoverage_hasIsos_and_isStable (B : BigFppfSite.{u}) :
    (etalePrecoverage B).HasIsos ∧ (etalePrecoverage B).IsStableUnderComposition ∧
      (etalePrecoverage B).IsStableUnderBaseChange ∧ (etalePrecoverage B).HasPullbacks := by
  have hcomap := etalePrecoverage_eq_comap B
  have ⟨_, _, _⟩ := etalePrecoverage_hasIsos_and_stable.{u}
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  refine ⟨by rw [hcomap]; infer_instance, by rw [hcomap]; infer_instance,
    by rw [hcomap]; infer_instance, by rw [hcomap]; infer_instance⟩

/-- **A covering sieve of the big étale topology contains a selected étale covering family.**
The topology is generated by the selected étale families, and those have isomorphisms and are
stable under composition and base change, so the saturation adds no sieve that is not refined by
one of them. This is the étale analogue of
`AlgebraicGeometry.exists_covering_le_of_mem_topology`. -/
public theorem exists_etaleCovering_le_of_mem_etaleTopology (B : BigFppfSite.{u})
    {X : B.Schemes} {R : Sieve X} (hR : R ∈ etaleTopology B X) :
    ∃ E : PreZeroHypercover.{u + 1} X, etaleCovering B ⟨X, E⟩ ∧ E.presieve₀ ≤ R.arrows := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := etalePrecoverage_hasIsos_and_isStable B
  rw [show etaleTopology B = (etalePrecoverage B).toGrothendieck from rfl,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨R', ⟨E, rfl, hE⟩, hle⟩ := hR
  exact ⟨E, hE, hle⟩

end AlgebraicGeometry

end
