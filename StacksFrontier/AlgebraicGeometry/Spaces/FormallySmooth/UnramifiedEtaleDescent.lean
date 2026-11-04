module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Descent of formal unramifiedness and formal étaleness along a surjective étale transformation

Let `F ⟶ G ⟶ H` be transformations of set-valued presheaves on the big fppf site over a
scheme, with the first transformation representable, surjective and étale. Formal
unramifiedness of the composite then descends to the second transformation as soon as `G` is
separated for the étale topology, and formal étaleness descends as soon as `G` is a sheaf for
the étale topology and `H` is separated for it.

Those two are the hypotheses of the corrected parts (5) and (6) of [Stacks Project, Tag
04CY], whose own statements quantify over arbitrary set-valued functors and are false in that
generality; this is an erratum to the source.

## Main results

* `AlgebraicGeometry.Space.mem_etaleTopology_over_of_etale_of_jointlySurjective`: a jointly
  surjective family of étale morphisms into a test object generates a covering sieve for the
  étale topology on the slice.
* `AlgebraicGeometry.Space.eq_of_common_square_zero_lift`: two sections of the intermediate
  presheaf with a common lift to the source presheaf and a common image in the target presheaf
  agree.
* `AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated`: **Stacks 04CY**, the
  corrected part (5).
* `AlgebraicGeometry.Space.formallyUnramified_of_comp`: the corollary of the previous result
  that asks the intermediate presheaf for the full sheaf condition instead of separatedness
  (Stacks 04CY, `descend_formally_unramified`).
* `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`: **Stacks 04CY**, the
  corrected part (6).
* `AlgebraicGeometry.Space.formallyEtale_of_comp`: the corollary of the previous result that
  asks the target presheaf for the full sheaf condition instead of separatedness (Stacks 04CY,
  `descend_formally_etale`).

## Implementation notes

Both descents are local statements glued by the sheaf condition on the slice over the base
scheme, and the covering family in both cases is the affine étale cover of the thickening
produced by `AlgebraicGeometry.Space.exists_affine_etale_cover_lift`. The uniqueness statement
is the easier of the two: it needs only separatedness of `G`, since the two sections become
equal over each member of the cover. The existence statement glues the local sections produced
by `AlgebraicGeometry.Space.exists_etale_affine_local_lift`, which requires compatibility on
pairwise fibre products; that compatibility is exactly the uniqueness statement applied over
the fibre product, and its hypotheses are supplied by the stability of first-order thickenings
under base change.

The pairwise and triple fibre products are taken in the site, whose underlying category has
them and over which `AlgebraicGeometry.BigFppfOver.toScheme` preserves them, so the base change
of the thickening is again a square-zero closed immersion by
`Stacks.Thickenings.isFirstOrderThickening_isStableUnderBaseChange`; being a closed immersion it
is in particular affine, which is what makes the fibre products affine and so admissible test
objects for the lifting criterion.

The hypotheses on the intermediate presheaf cannot be removed. Stacks 04CY states parts (5)
and (6) for arbitrary set-valued functors, and in that generality both are false:
`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp` exhibits a
representable surjective étale `a` with `a ≫ b` formally étale and `b` not even formally
unramified. Each of the two statements here asks of a presheaf exactly what the tag's own
proof of its part uses, and nothing else — separatedness where that proof identifies two
sections which agree after pullback along an étale covering, the full sheaf condition where it
glues étale-local solutions.

A presheaf which is an algebraic space over `S` satisfies either hypothesis: it is an fppf
sheaf, hence a sheaf for the étale topology on the slice by
`AlgebraicGeometry.Space.isSheaf_etaleTopologyOver_of_isSheaf`, the étale topology over `S`
being coarser than the fppf one.

Covering families of the chosen big fppf site have their index types bounded, so the family is
transported to the index universe of the site's covering families by `ULift` before being
presented as a `CategoryTheory.PreZeroHypercover`; combinatorially equivalent families generate
the same presieve, which is what
`AlgebraicGeometry.BigFppfSite.presieve₀_mem_etalePrecoverage` supplies.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

add_to_stacks 04CY "fibre products in the big affine fppf site"
  AlgebraicGeometry.hasPullbacks_bigAffineFppf

add_to_stacks 04CY "preservation by the big affine fppf functor to schemes"
  AlgebraicGeometry.preservesPullbacks_bigAffineFppfToScheme

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A jointly surjective family of étale morphisms into an object of the big fppf site over
`S` generates a covering sieve for the étale topology on the slice over the base scheme. -/
public theorem mem_etaleTopology_over_of_etale_of_jointlySurjective
    {T' : BigFppfOver B S hS} {ι : Type (u + 1)} (U : ι → BigFppfOver B S hS)
    (j : ∀ k, U k ⟶ T')
    (hjet : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (j k)))
    (hjsurj : ∀ t' : (BigFppfOver.toScheme B S hS).obj T',
      ∃ (k : ι) (x : (BigFppfOver.toScheme B S hS).obj (U k)),
        ((BigFppfOver.toScheme B S hS).map (j k)).base x = t') :
    Sieve.ofArrows U j ∈ ((etaleTopology B).over (B.obj hS)) T' := by
  let E : PreZeroHypercover.{u + 1} T'.left :=
    { I₀ := ι, X := fun k ↦ (U k).left, f := fun k ↦ (j k).left }
  have hEt : IsEtaleCovering (⟨T'.left, E⟩ : Covering B.Schemes) := by
    show (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map, Presieve.map_ofArrows]
    show Presieve.ofArrows _ _ ∈ Scheme.precoverage @Etale _
    rw [Scheme.ofArrows_mem_precoverage_iff @Etale]
    exact ⟨hjsurj, hjet⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (B.presieve₀_mem_etalePrecoverage E hEt)

/-- Two sections of the intermediate presheaf over an affine object, with the same image in
the target presheaf and both receiving the same section of the source presheaf over an affine
square-zero closed subobject, are equal.

This is the uniqueness step of the descent half of Stacks 04CY: formal étaleness of the first
transformation turns the common section of the source presheaf into a lift over the larger
object for each of the two sections, and formal unramifiedness of the composite identifies
those two lifts. -/
public theorem eq_of_common_square_zero_lift
    (D : RepresentableSurjectiveEtaleSituation.{u})
    (ha : FormallyEtale D.a) (hba : FormallyUnramified (D.a ≫ D.b))
    (V U : BigFppfOver D.B D.S D.hS)
    (hV : IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj V))
    (hU : IsAffine ((BigFppfOver.toScheme D.B D.S D.hS).obj U))
    (j : V ⟶ U) (hj : IsSquareZeroClosedImmersion D.B D.S D.hS j)
    (x : D.F.obj (op V)) (y : D.H.obj (op U)) (z₁ z₂ : D.G.obj (op U))
    (h₁ : D.a.app (op V) x = D.G.map j.op z₁)
    (h₂ : D.a.app (op V) x = D.G.map j.op z₂)
    (hb₁ : D.b.app (op U) z₁ = y) (hb₂ : D.b.app (op U) z₂ = y) : z₁ = z₂ := by
  obtain ⟨w₁, hw₁, -⟩ := ha V U hV hU j hj x z₁ h₁
  obtain ⟨w₂, hw₂, -⟩ := ha V U hV hU j hj x z₂ h₂
  have hcomm : (D.a ≫ D.b).app (op V) x = D.H.map j.op y := by
    calc (D.a ≫ D.b).app (op V) x = D.b.app (op V) (D.G.map j.op z₁) := by
          rw [show (D.a ≫ D.b).app (op V) x = D.b.app (op V) (D.a.app (op V) x) from rfl, h₁]
      _ = D.H.map j.op (D.b.app (op U) z₁) := D.b.naturality_apply j.op z₁
      _ = D.H.map j.op y := by rw [hb₁]
  have hcomp : ∀ (w : D.F.obj (op U)) (z : D.G.obj (op U)), IsLift D.a j x z w →
      D.b.app (op U) z = y → IsLift (D.a ≫ D.b) j x y w := fun w z hw hb ↦
    ⟨hw.1, by
      rw [show (D.a ≫ D.b).app (op U) w = D.b.app (op U) (D.a.app (op U) w) from rfl, hw.2, hb]⟩
  calc z₁ = D.a.app (op U) w₁ := hw₁.2.symm
    _ = D.a.app (op U) w₂ :=
        congrArg (D.a.app (op U)) (hba V U hV hU j hj x y hcomm w₁ w₂ (hcomp w₁ z₁ hw₁ hb₁)
          (hcomp w₂ z₂ hw₂ hb₂))
    _ = z₂ := hw₂.2

/-- **Stacks 04CY**, the corrected part (5) of the tag. In a
representable, surjective, étale situation, a formally unramified composite forces the second
transformation to be formally unramified as soon as the intermediate presheaf is separated for
the étale topology.

Separatedness is the whole of what is used, and it is exactly the step the tag's own proof
takes: having identified two sections of `G` after pullback along an étale covering, that proof
concludes "hence `f = g` as `W' → T'` is an étale covering".

It cannot be dropped: the tag states this part for arbitrary set-valued functors, and in that
generality it is false. The counterexample is
`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp`, which doubles
the sections of the functor of points of the thickening that factor through neither the étale
cover nor the thickened object. This is an erratum to the source statement.

An intermediate presheaf which is an algebraic space over `S` is separated for the étale
topology, so `AlgebraicGeometry.Space.formallyUnramified_of_formallyUnramified_comp` is the
special case of this result at such a presheaf, as is
`AlgebraicGeometry.Space.formallyUnramified_of_comp`, which asks the full sheaf condition. -/
@[stacks 04CY "part (5), corrected form: G separated for the étale topology; false as written, \
see DoubledSection.Rational.not_forall_descend"]
public theorem formallyUnramified_of_comp_of_isSeparated
    (s : RepresentableSurjectiveEtaleSituation.{u})
    (hG : Presieve.IsSeparated ((etaleTopology s.B).over (s.B.obj s.hS)) s.G)
    (hba : FormallyUnramified (s.a ≫ s.b)) :
    FormallyUnramified s.b := by
  classical
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme s.B s.S s.hS
  have hpull : HasPullbacks (BigFppfOver s.B s.S s.hS) := inferInstance
  have ha : FormallyEtale s.a := formallyEtale_of_etale s.B s.S s.hS s.a s.etale_a
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  -- the representing object of the base change of `s.a` along the given section of `G`
  let g : yoneda.obj T ⟶ s.G := yonedaEquiv.symm x
  let W := s.representable_a.pullback g
  let p : W ⟶ T := s.representable_a.snd g
  let q : yoneda.obj W ⟶ s.F := s.representable_a.fst g
  have hpb : IsPullback q (yoneda.map p) s.a g := s.representable_a.isPullback g
  have hpe : Etale ((BigFppfOver.toScheme s.B s.S s.hS).map p) :=
    s.etale_a.property g q p hpb
  have hps : Function.Surjective
      ((BigFppfOver.toScheme s.B s.S s.hS).map p).base :=
    (s.surjective_a.property g q p hpb).surj
  obtain ⟨ι, U, j, hUaff, hjet, hjsurj, hlift⟩ :=
    exists_affine_etale_cover_lift s.B s.S s.hS hi hpe hps
  -- the two sections agree over each member of the cover
  have hloc : ∀ k : ι, s.G.map (j k).op z₁ = s.G.map (j k).op z₂ := by
    intro k
    have hsqS : IsPullback ((BigFppfOver.toScheme s.B s.S s.hS).map (pullback.fst i (j k)))
        ((BigFppfOver.toScheme s.B s.S s.hS).map (pullback.snd i (j k)))
        ((BigFppfOver.toScheme s.B s.S s.hS).map i)
        ((BigFppfOver.toScheme s.B s.S s.hS).map (j k)) :=
      (IsPullback.of_hasPullback i (j k)).map (BigFppfOver.toScheme s.B s.S s.hS)
    have hvThick : IsSquareZeroClosedImmersion s.B s.S s.hS (pullback.snd i (j k)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Stacks.Thickenings.IsFirstOrderThickening.{u}) hsqS hi
    have hvClosed : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme s.B s.S s.hS).map (pullback.snd i (j k))) := hvThick.1
    have hUk : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj (U k)) := hUaff k
    have hVaff : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj
        (Limits.pullback i (j k))) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme s.B s.S s.hS).map (pullback.snd i (j k)))
    obtain ⟨m, hm⟩ := hlift k (Limits.pullback i (j k)) (pullback.fst i (j k))
      (pullback.snd i (j k)) pullback.condition
    -- the section of `F` carried by the lift, and its image in `G`
    have hξa : s.a.app (op (Limits.pullback i (j k)))
        (s.F.map m.op (q.app (op W) (𝟙 W))) =
        s.G.map (pullback.fst i (j k)).op x := by
      calc s.a.app (op (Limits.pullback i (j k))) (s.F.map m.op (q.app (op W) (𝟙 W)))
          = s.G.map m.op (s.a.app (op W) (q.app (op W) (𝟙 W))) :=
            s.a.naturality_apply m.op (q.app (op W) (𝟙 W))
        _ = s.G.map m.op (s.G.map p.op x) := by
            rw [app_tautological_section_representing s.B s.S s.hS hpb]
        _ = s.G.map (m ≫ p).op x := ExtendingFunctors.map_map_apply s.G m p x
        _ = s.G.map (pullback.fst i (j k)).op x := by rw [hm]
    have hrestr : ∀ z : s.G.obj (op T'), s.G.map i.op z = x →
        s.a.app (op (Limits.pullback i (j k)))
          (s.F.map m.op (q.app (op W) (𝟙 W))) =
          s.G.map (pullback.snd i (j k)).op (s.G.map (j k).op z) := by
      intro z hz
      calc s.a.app (op (Limits.pullback i (j k))) (s.F.map m.op (q.app (op W) (𝟙 W)))
          = s.G.map (pullback.fst i (j k)).op (s.G.map i.op z) := by rw [hξa, hz]
        _ = s.G.map (pullback.fst i (j k) ≫ i).op z :=
            ExtendingFunctors.map_map_apply s.G (pullback.fst i (j k)) i z
        _ = s.G.map (pullback.snd i (j k) ≫ j k).op z := by rw [pullback.condition]
        _ = s.G.map (pullback.snd i (j k)).op (s.G.map (j k).op z) :=
            (ExtendingFunctors.map_map_apply s.G (pullback.snd i (j k)) (j k) z).symm
    have hbloc : ∀ z : s.G.obj (op T'), s.b.app (op T') z = y →
        s.b.app (op (U k)) (s.G.map (j k).op z) = s.H.map (j k).op y := by
      intro z hz
      rw [s.b.naturality_apply (j k).op z, hz]
    exact eq_of_common_square_zero_lift s ha hba (Limits.pullback i (j k)) (U k) hVaff hUk
      (pullback.snd i (j k)) hvThick (s.F.map m.op (q.app (op W) (𝟙 W)))
      (s.H.map (j k).op y) (s.G.map (j k).op z₁) (s.G.map (j k).op z₂)
      (hrestr z₁ hz₁.1) (hrestr z₂ hz₂.1) (hbloc z₁ hz₁.2) (hbloc z₂ hz₂.2)
  -- separatedness of `G` for the covering sieve generated by the family
  have hcover : Sieve.ofArrows (fun k : ULift.{u + 1} ι ↦ U k.down)
      (fun k ↦ j k.down) ∈ ((etaleTopology s.B).over (s.B.obj s.hS)) T' := by
    refine mem_etaleTopology_over_of_etale_of_jointlySurjective s.B s.S s.hS _ _
      (fun k ↦ hjet k.down) fun t' ↦ ?_
    obtain ⟨k, z, hz⟩ := hjsurj t'
    exact ⟨⟨k⟩, z, hz⟩
  refine (hG _ hcover).ext fun V₀ fv hfv ↦ ?_
  obtain ⟨Y, a₀, b₀, hb₀, hfac⟩ := hfv
  obtain ⟨k⟩ := hb₀
  rw [← hfac, ← ExtendingFunctors.map_map_apply, ← ExtendingFunctors.map_map_apply]
  exact congrArg (s.G.map a₀.op) (hloc k.down)

/-- In a representable, surjective, étale situation, a formally unramified composite forces the
second transformation to be formally unramified as soon as the intermediate presheaf is a sheaf
for the étale topology.

This is the special case of
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated` at a presheaf which
satisfies the full sheaf condition rather than merely separatedness, so it is a weaker statement
than the corrected part (5) of Stacks 04CY, whose registration as that part sits on that
result. -/
@[stacks 04CY "descend_formally_unramified"]
public theorem formallyUnramified_of_comp
    (s : RepresentableSurjectiveEtaleSituation.{u})
    (hG : Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G)
    (hba : FormallyUnramified (s.a ≫ s.b)) :
    FormallyUnramified s.b :=
  formallyUnramified_of_comp_of_isSeparated s
    ((isSheaf_iff_isSheaf_of_type _ s.G).mp hG).isSeparated hba

/-- **Stacks 04CY**, the corrected part (6) of the tag. In
a representable, surjective, étale situation, a formally étale composite forces the second
transformation to be formally étale as soon as the intermediate presheaf is a sheaf for the
étale topology and the target presheaf is separated for it.

Separatedness is all that the target presheaf contributes, and it is all the tag's own proof
asks of it: `H` enters only to compare two sections of `H` that already agree over an étale
covering. The intermediate presheaf genuinely needs the full sheaf condition, since the proof
glues the étale-local solutions produced by part (4) — "hence we may glue the local solutions
to get assertion (6)" in the tag.

The tag states this part for arbitrary set-valued functors, and in that generality it is
false: the situation of
`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp` has a formally
étale composite and a second transformation that is not formally étale. This is an erratum to
the source statement. -/
@[stacks 04CY "part (6), corrected form: G a sheaf and H separated for the étale topology; \
false as written, see DoubledSection.Rational.not_forall_descend"]
public theorem formallyEtale_of_comp_of_isSeparated
    (s : RepresentableSurjectiveEtaleSituation.{u})
    (hG : Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G)
    (hH : Presieve.IsSeparated ((etaleTopology s.B).over (s.B.obj s.hS)) s.H)
    (hba : FormallyEtale (s.a ≫ s.b)) :
    FormallyEtale s.b := by
  classical
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme s.B s.S s.hS
  have hpull : HasPullbacks (BigFppfOver s.B s.S s.hS) := inferInstance
  have hbaSmooth : FormallySmooth (s.a ≫ s.b) := fun T T' hT hT' i hi x y hxy ↦
    let ⟨z, hz⟩ := hba T T' hT hT' i hi x y hxy
    ⟨z, hz.1⟩
  have hbaUnram : FormallyUnramified (s.a ≫ s.b) := by
    intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
    obtain ⟨z, hz⟩ := hba T T' hT hT' i hi x y hxy
    exact (hz.2 z₁ hz₁).trans (hz.2 z₂ hz₂).symm
  have hbUnram : FormallyUnramified s.b := formallyUnramified_of_comp_of_isSeparated s
    ((isSheaf_iff_isSheaf_of_type _ s.G).mp hG).isSeparated hbaUnram
  intro T T' hT hT' i hi x y hxy
  have hiSurj : Function.Surjective ((BigFppfOver.toScheme s.B s.S s.hS).map i).base :=
    (Stacks.Thickenings.IsFirstOrderThickening.isThickening
      (i := (BigFppfOver.toScheme s.B s.S s.hS).map i) hi).2
  -- a local lift over an affine étale neighbourhood of every point of `T`
  choose U j z hUaff hjet hjhit hjb hcompat using
    fun t : (BigFppfOver.toScheme s.B s.S s.hS).obj T ↦
      exists_etale_affine_local_lift s T T' i hT' hi x y hxy hbaSmooth t
  have hcover : Sieve.ofArrows
      (fun k : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T) ↦ U k.down)
      (fun k ↦ j k.down) ∈ ((etaleTopology s.B).over (s.B.obj s.hS)) T' := by
    refine mem_etaleTopology_over_of_etale_of_jointlySurjective s.B s.S s.hS _ _
      (fun k ↦ hjet k.down) fun t' ↦ ?_
    obtain ⟨t, rfl⟩ := hiSurj t'
    obtain ⟨u, hu⟩ := hjhit t
    exact ⟨⟨t⟩, u, hu⟩
  have hGType : Presieve.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G :=
    (isSheaf_iff_isSheaf_of_type _ s.G).mp hG
  -- restricting a local section along `q` gives a section over the restriction of `y`
  have happ : ∀ (k : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T)) {V₀ : _}
      (q : V₀ ⟶ U k.down), s.b.app (op V₀) (s.G.map q.op (z k.down)) =
        s.H.map (q ≫ j k.down).op y := by
    intro k V₀ q
    rw [s.b.naturality_apply q.op, hjb, ExtendingFunctors.map_map_apply]
  -- the local sections are compatible on pairwise fibre products
  have hGArrows : Presieve.Arrows.Compatible s.G
      (fun k : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T) ↦ j k.down)
      (fun k ↦ z k.down) := by
    intro k l V₀ fk fl hfkl
    let Q := Limits.pullback (j k.down) (j l.down)
    let q₁ : Q ⟶ U k.down := pullback.fst (j k.down) (j l.down)
    let q₂ : Q ⟶ U l.down := pullback.snd (j k.down) (j l.down)
    have hQsq : IsPullback ((BigFppfOver.toScheme s.B s.S s.hS).map q₁)
        ((BigFppfOver.toScheme s.B s.S s.hS).map q₂)
        ((BigFppfOver.toScheme s.B s.S s.hS).map (j k.down))
        ((BigFppfOver.toScheme s.B s.S s.hS).map (j l.down)) :=
      (IsPullback.of_hasPullback (j k.down) (j l.down)).map
        (BigFppfOver.toScheme s.B s.S s.hS)
    have hUk : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj (U k.down)) := hUaff k.down
    have hUl : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj (U l.down)) := hUaff l.down
    have hjlAff : IsAffineHom ((BigFppfOver.toScheme s.B s.S s.hS).map (j l.down)) :=
      isAffineHom_of_isAffine _
    have hq₁Aff : IsAffineHom ((BigFppfOver.toScheme s.B s.S s.hS).map q₁) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsAffineHom.{u}) hQsq.flip hjlAff
    have hQaff : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj Q) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme s.B s.S s.hS).map q₁)
    -- the base change of the thickening to the pairwise fibre product
    let r : Q ⟶ T' := q₁ ≫ j k.down
    let P := Limits.pullback r i
    let pQ : P ⟶ Q := pullback.fst r i
    let pT : P ⟶ T := pullback.snd r i
    have hPsq : IsPullback ((BigFppfOver.toScheme s.B s.S s.hS).map pQ)
        ((BigFppfOver.toScheme s.B s.S s.hS).map pT)
        ((BigFppfOver.toScheme s.B s.S s.hS).map r)
        ((BigFppfOver.toScheme s.B s.S s.hS).map i) :=
      (IsPullback.of_hasPullback r i).map (BigFppfOver.toScheme s.B s.S s.hS)
    have hpQThick : IsSquareZeroClosedImmersion s.B s.S s.hS pQ :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Stacks.Thickenings.IsFirstOrderThickening.{u}) hPsq.flip hi
    have hpQClosed : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme s.B s.S s.hS).map pQ) := hpQThick.1
    have hPaff : IsAffine ((BigFppfOver.toScheme s.B s.S s.hS).obj P) :=
      isAffine_of_isAffineHom ((BigFppfOver.toScheme s.B s.S s.hS).map pQ)
    -- uniqueness of the lift over the fibre product identifies the two restrictions
    have hrestr : ∀ (c : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T))
        (q : Q ⟶ U c.down), q ≫ j c.down = r →
        s.G.map pQ.op (s.G.map q.op (z c.down)) = s.G.map pT.op x := by
      intro c q hq
      rw [ExtendingFunctors.map_map_apply]
      exact (hcompat c.down P pT (pQ ≫ q) (by
        rw [Category.assoc, hq]; exact pullback.condition.symm)).symm
    have hxyP : s.b.app (op P) (s.G.map pT.op x) = s.H.map pQ.op (s.H.map r.op y) := by
      calc s.b.app (op P) (s.G.map pT.op x) = s.H.map pT.op (s.H.map i.op y) := by
            rw [s.b.naturality_apply pT.op x, hxy]
        _ = s.H.map (pT ≫ i).op y := ExtendingFunctors.map_map_apply s.H pT i y
        _ = s.H.map (pQ ≫ r).op y := by
            rw [show pT ≫ i = pQ ≫ r from pullback.condition.symm]
        _ = s.H.map pQ.op (s.H.map r.op y) := (ExtendingFunctors.map_map_apply s.H pQ r y).symm
    have hq₂ : q₂ ≫ j l.down = r := (pullback.condition (f := j k.down) (g := j l.down)).symm
    have hb : ∀ (c : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T))
        (q : Q ⟶ U c.down), q ≫ j c.down = r →
        s.b.app (op Q) (s.G.map q.op (z c.down)) = s.H.map r.op y := fun c q hq ↦
      hq ▸ happ c q
    have hEq := hbUnram P Q hPaff hQaff pQ hpQThick (s.G.map pT.op x) (s.H.map r.op y)
      hxyP (s.G.map q₁.op (z k.down)) (s.G.map q₂.op (z l.down))
      ⟨hrestr k q₁ rfl, hb k q₁ rfl⟩ ⟨hrestr l q₂ hq₂, hb l q₂ hq₂⟩
    have hl₁ : (pullback.lift fk fl hfkl : V₀ ⟶ Q) ≫ q₁ = fk := pullback.lift_fst _ _ _
    have hl₂ : (pullback.lift fk fl hfkl : V₀ ⟶ Q) ≫ q₂ = fl := pullback.lift_snd _ _ _
    calc s.G.map fk.op (z k.down)
        = s.G.map (pullback.lift fk fl hfkl).op (s.G.map q₁.op (z k.down)) := by
          rw [ExtendingFunctors.map_map_apply, hl₁]
      _ = s.G.map (pullback.lift fk fl hfkl).op (s.G.map q₂.op (z l.down)) := by rw [hEq]
      _ = s.G.map fl.op (z l.down) := by rw [ExtendingFunctors.map_map_apply, hl₂]
  -- glue the local sections and check the two conditions
  obtain ⟨w, hwlocal, -⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := s.G)
        (π := fun k : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T) ↦
          j k.down)).mp
      ((Presieve.isSheafFor_iff_generate _).2 (hGType _ hcover)) (fun k ↦ z k.down) hGArrows
  have hwj : ∀ (k : ULift.{u + 1} ((BigFppfOver.toScheme s.B s.S s.hS).obj T)) {V₀ : _}
      (a₀ : V₀ ⟶ U k.down), s.G.map (a₀ ≫ j k.down).op w = s.G.map a₀.op (z k.down) := by
    intro k V₀ a₀
    rw [← ExtendingFunctors.map_map_apply, hwlocal]
  have hwrestrict : s.G.map i.op w = x := by
    refine (hGType _ ((((etaleTopology s.B).over (s.B.obj s.hS)).pullback_stable i
      hcover))).isSeparatedFor.ext fun V₀ fv hfv ↦ ?_
    obtain ⟨Y, a₀, b₀, hb₀, hfac⟩ := hfv
    obtain ⟨k⟩ := hb₀
    rw [ExtendingFunctors.map_map_apply, ← hfac, hwj]
    exact (hcompat k.down V₀ fv a₀ hfac.symm).symm
  have hwcomp : s.b.app (op T') w = y := by
    refine (hH _ hcover).ext fun V₀ fv hfv ↦ ?_
    obtain ⟨Y, a₀, b₀, hb₀, hfac⟩ := hfv
    obtain ⟨k⟩ := hb₀
    rw [← hfac, ← s.b.naturality_apply, hwj]
    exact happ k a₀
  exact ⟨w, ⟨hwrestrict, hwcomp⟩, fun w' hw' ↦
    (hbUnram T T' hT hT' i hi x y hxy w w' ⟨hwrestrict, hwcomp⟩ hw').symm⟩

/-- In a representable, surjective, étale situation, a formally étale composite forces the
second transformation to be formally étale as soon as the intermediate and target presheaves
are sheaves for the étale topology.

This is the corollary of `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`
obtained by strengthening separatedness of the target presheaf to the full sheaf condition, so
it states a special case of the corrected part (6) of Stacks 04CY, whose registration as that
part sits on that result. -/
@[stacks 04CY "descend_formally_etale"]
public theorem formallyEtale_of_comp
    (s : RepresentableSurjectiveEtaleSituation.{u})
    (hG : Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G)
    (hH : Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.H)
    (hba : FormallyEtale (s.a ≫ s.b)) :
    FormallyEtale s.b :=
  formallyEtale_of_comp_of_isSeparated s hG
    ((isSheaf_iff_isSheaf_of_type _ s.H).mp hH).isSeparated hba

end AlgebraicGeometry.Space

end
