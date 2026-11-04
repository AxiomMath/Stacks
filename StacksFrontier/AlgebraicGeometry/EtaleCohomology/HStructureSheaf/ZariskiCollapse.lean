module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpFppfCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteOpensContinuity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.PushforwardVanishingOnACover
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# h cohomology over `S` from Zariski cohomology on `S`

Let `B` be a big h site containing a scheme `S`. The small Zariski site of `S` sits inside the big
h category over `S`, an open `V` going to the open immersion `V ⟶ S`, and restriction along that
inclusion is the direct image `ε_*` of a morphism of sites `(Sch/S)_h ⟶ S_Zar`. This file proves
the Leray collapse along `ε`: for an abelian h sheaf `F` whose higher cohomology over every
affine open of `S` vanishes,

`H^i((Sch/S)_h, F) ≅ H^i(S, ε_* F)`

in every degree, the left-hand side being the cohomology over the final object of the big h
category. This is how the proof of Stacks 0EWU passes from the h topology to the scheme `S`.

## Main definitions

* `AlgebraicGeometry.BigHOver.opensToBigH`: the inclusion of the small Zariski site of `S`.
* `AlgebraicGeometry.BigHOver.zariskiRestriction`: `ε_*`, restriction of abelian h sheaves to
  the opens of `S`.
* `AlgebraicGeometry.BigHOver.rightDerivedSectionsFinalIsoZariski`: the collapse
  `H^i((Sch/S)_h, F) ≅ H^i(S, ε_* F)`.

## Main results

* `AlgebraicGeometry.BigHOver.coverPreserving_opensToBigH`: an open covering of an open of `S` is
  an h covering, so the inclusion is cover preserving; it is therefore continuous.
* `AlgebraicGeometry.BigHOver.isZero_rightDerived_zariskiRestriction`: the higher direct images
  of `F` along `ε` vanish when the higher cohomology of `F` over the affine opens of `S` does.

## Implementation notes

Cohomology is taken at the morphism universe `u` of the two sites, which is where the collapse
`Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso` is stated. The big h category is
essentially small at that universe (Stacks 000J), so sheafification, enough injectives and the
`Ext` universe are available there; they are installed as local instances.

An open covering is first shown to be an fppf covering of the site, and then an h covering by
`AlgebraicGeometry.BigHOver.fppfTopology_le_topology`; open immersions are flat and locally of
finite presentation.

## References

* [Stacks Project, Tag 0EWU](https://stacks.math.columbia.edu/tag/0EWU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The small Zariski site of `S` inside the big h category over `S`**: an open `V` of `S` goes
to the open immersion `V ⟶ S`. -/
abbrev opensToBigH : S.Opens ⥤ BigHOver B S hS :=
  Stacks.Adequate.opensBelowToOver (κ := B.cutoff) hS

/-- The family of the big h category cut out by a sieve on an open of `S`: the open immersions
of its members. -/
def opensHypercover {U : S.Opens} (R : Sieve U) :
    PreZeroHypercover.{u + 1} ((opensToBigH B S hS).obj U) where
  I₀ := ULift.{u + 1} (Σ V : S.Opens, { g : V ⟶ U // R.arrows g })
  X i := (opensToBigH B S hS).obj i.down.1
  f i := (opensToBigH B S hS).map i.down.2.1

/-- **An open covering of an open of `S` is an fppf covering of the big h category**: its members
are open immersions, hence flat and locally of finite presentation, and they are jointly
surjective. -/
theorem opensHypercover_mem_fppfPrecoverage {U : S.Opens} (R : Sieve U)
    (hR : R ∈ Opens.grothendieckTopology S U) :
    (opensHypercover B S hS R).presieve₀ ∈ fppfPrecoverage B S hS ((opensToBigH B S hS).obj U) := by
  refine ⟨opensHypercover B S hS R, rfl, ?_⟩
  rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨V, g, hg, hV⟩ := hR x.1 x.2
    refine ⟨⟨⟨V, g, hg⟩⟩, ⟨⟨x.1, hV⟩, ?_⟩⟩
    show S.homOfLE (leOfHom g) _ = x
    exact (Scheme.homOfLE_apply' (leOfHom g) x.1 hV).trans (Subtype.ext rfl)
  · have : IsOpenImmersion ((BigHOver.toScheme B S hS).map ((opensHypercover B S hS R).f i)) :=
      inferInstanceAs (IsOpenImmersion (S.homOfLE (leOfHom i.down.2.1)))
    exact ⟨inferInstance, inferInstance⟩

/-- **The small Zariski site of `S` is cover preserving into the big h site over `S`**: an open
covering of an open of `S` is an fppf covering, hence an h covering. -/
theorem coverPreserving_opensToBigH :
    CoverPreserving (Opens.grothendieckTopology S) (BigHOver.topology B S hS)
      (opensToBigH B S hS) := by
  refine ⟨fun {U R} hR ↦ ?_⟩
  refine fppfTopology_le_topology B S hS _ ?_
  refine (fppfTopology B S hS).superset_covering ?_
    ((fppfPrecoverage B S hS).generate_mem_toGrothendieck
      (opensHypercover_mem_fppfPrecoverage B S hS R hR))
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact ⟨_, i.down.2.1, 𝟙 _, i.down.2.2, (Category.id_comp _).symm⟩

/-- **The small Zariski site of `S` is continuous in the big h site over `S`**, so restriction
along it is the direct image of a morphism of sites `(Sch/S)_h ⟶ S_Zar`. -/
instance isContinuous_opensToBigH :
    (opensToBigH B S hS).IsContinuous (Opens.grothendieckTopology S) (BigHOver.topology B S hS) :=
  Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_opensToBigH B S hS)

/-- The whole of `S`, as an open, goes to a final object of the big h category over `S`. -/
def opensToBigHTopIsoFinal : (opensToBigH B S hS).obj ⊤ ≅ BigHOver.final B S hS :=
  (isTerminal_opensBelowToOver_top hS).uniqueUpToIso (BigHOver.finalIsTerminal B S hS)

/-! ### The Leray collapse at the morphism universe -/

section Collapse

attribute [local instance] Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

/-- The big h category over `S` is essentially small at the universe of its morphisms. -/
instance essentiallySmall : EssentiallySmall.{u} (BigHOver B S hS) :=
  have := essentiallySmall_schemeBelow B.cutoff
  inferInstance

/-- Abelian sheaves with values at the morphism universe can be sheafified for the h topology, the
big h category being essentially small. -/
instance hasSheafify_ab : HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite

/-- **`ε_*`**: restriction of abelian h sheaves on the big h category over `S` to the small
Zariski site of `S`. -/
abbrev zariskiRestriction :
    Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} :=
  (opensToBigH B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology S) (BigHOver.topology B S hS)

/-- **The higher direct images along `ε` vanish when cohomology over affine opens does.** If the
cohomology of an abelian h sheaf `F` vanishes in degree `p` over every affine open of `S`, then
`R^p ε_* F = 0`: the affine opens below an open of `S` cover it. -/
theorem isZero_rightDerived_zariskiRestriction (F : Sheaf (BigHOver.topology B S hS)
    AddCommGrpCat.{u}) (p : ℕ)
    (hF : ∀ V : S.Opens, IsAffineOpen V →
      IsZero ((((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
        (op ((opensToBigH B S hS).obj V))).rightDerived p).obj F)) :
    IsZero (((zariskiRestriction B S hS).rightDerived p).obj F) :=
  Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (opensToBigH B S hS) p F (fun V ↦ ⟨affineOpensPresieve S V,
      generate_affineOpensPresieve_mem S V, fun W _ hW ↦ hF W hW⟩)

/-- **Cohomology over `S` in the h topology is Zariski cohomology of the restriction**, for an
abelian h sheaf `F` whose higher cohomology over every affine open of `S` vanishes:

`H^i((Sch/S)_h, F) ≅ H^i(S, ε_* F)`.

This is the Leray collapse `Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso` along
the inclusion of the small Zariski site, at the open `⊤`, which goes to a final object. -/
def rightDerivedSectionsFinalIsoZariski (F : Sheaf (BigHOver.topology B S hS) AddCommGrpCat.{u})
    (hF : ∀ (V : S.Opens), IsAffineOpen V → ∀ p : ℕ, 0 < p →
      IsZero ((((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
        (op ((opensToBigH B S hS).obj V))).rightDerived p).obj F))
    (i : ℕ) :
    (((sheafSections (BigHOver.topology B S hS) AddCommGrpCat.{u}).obj
        (op (BigHOver.final B S hS))).rightDerived i).obj F ≅
      (((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived i).obj ((zariskiRestriction B S hS).obj F) :=
  ((Functor.rightDerivedIsoOfNatIso ((sheafSections (BigHOver.topology B S hS)
      AddCommGrpCat.{u}).mapIso (opensToBigHTopIsoFinal B S hS).op) i).app F) ≪≫
    (Stacks.Cohomology.BiggerSite.rightDerivedSectionsCollapseIso
      (Opens.grothendieckTopology S) (BigHOver.topology B S hS) (opensToBigH B S hS) F ⊤ i
      (fun q hq _ ↦ isZero_rightDerived_zariskiRestriction B S hS F q
        (fun V hV ↦ hF V hV q hq))).symm

end Collapse

end AlgebraicGeometry.BigHOver
