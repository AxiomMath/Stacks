module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of a scheme by an étale equivalence relation

Let `B` be a big fppf site, let `S` be a scheme contained in it, let `U` be an object of the
big fppf site of `S`, and let `j : R ⟶ U ×_S U` be an étale equivalence relation on `U` with
`R` an arbitrary `S`-scheme. Stacks 0265 asserts, for `U` with affine underlying scheme, and
Stacks 02WW for an arbitrary one, that the quotient sheaf `U/R` is an algebraic space over `S`
and that the quotient map `U ⟶ U/R` is surjective and étale.

This file supplies the facts about the relation scheme which the quotient machinery of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic` needs and could not discharge, the
local form of the geometric content of Stacks 0265, and the reduction of the tag's three
conclusions about the quotient map to effective fppf descent.

**Which results here need `U` affine.** The geometric content does not: the two base-change
descriptions `AlgebraicGeometry.Space.exists_isPullback_quotientChart` and
`AlgebraicGeometry.Space.exists_isPullback_diag_quotientSheaf`, the representability of the
diagonal `AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf`, and the generic
chart statement `AlgebraicGeometry.Space.presheaf_quotientChart` all hold for an arbitrary `U`.
Affineness is used only by the three conclusions at the end of the file —
`AlgebraicGeometry.Space.surjective_toQuotientSheaf`,
`AlgebraicGeometry.Space.etale_toQuotientSheaf` and
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` — and there only because they route
the chart through the property of Stacks 02W8, whose separatedness conjunct is the one property
of the target map of the relation that asks `U` to be affine
(`Stacks.Groupoids.isSeparated_target_of_isAffine`). Routing the chart through the diagonal
instead avoids that conjunct altogether, and the resulting statements for an arbitrary `U` —
the content of Stacks 02WW — are in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal`, with the presentation
they assemble into in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleEquivalenceRelationQuotient`.

## Main results

* `Stacks.Groupoids.isSheaf_points`: the restricted functor of points of an arbitrary
  `S`-scheme is a sheaf on the big fppf site of `S`, in the `Stacks.Groupoids.points`
  spelling.
* `Stacks.Groupoids.surjective_target`, `Stacks.Groupoids.surjective_source`,
  `Stacks.Groupoids.locallyQuasiFinite_target`, `Stacks.Groupoids.locallyQuasiFinite_source`:
  the two maps of an étale equivalence relation are surjective and locally quasi-finite.
* `AlgebraicGeometry.Space.exists_isPullback_quotientChart`: the base change of the chart of
  the quotient sheaf along a point of the quotient which has been lifted to `U` is
  represented by an object of the site, that base change is the relation pulled back along the
  lift, and its projection to the base is surjective, étale, locally quasi-finite and locally
  of finite type. This is the geometric content of Stacks 0265, and none of it needs `U`
  affine.
* `AlgebraicGeometry.Space.exists_isPullback_diag_quotientSheaf`: the same for the diagonal of
  the quotient sheaf, whose base change along a pair of lifted points is the relation and whose
  projection to the base is a monomorphism, separated, locally quasi-finite and locally of
  finite type. This needs no affineness either.
* `AlgebraicGeometry.Space.presheaf_quotientChart`: the chart of the quotient sheaf is
  representable with any base-change-stable property which the target map of the relation has
  and which descends effectively along the covering sieves. For an arbitrary `U`.
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf`: the diagonal of the
  quotient sheaf is representable, for an arbitrary `U`, given effective descent at the
  monomorphisms locally of finite type.
* `AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`: effective descent along the
  covering sieves of the site, which is the one input of Stacks 0265 this library does not
  have.
* `AlgebraicGeometry.Space.surjective_toQuotientSheaf`,
  `AlgebraicGeometry.Space.etale_toQuotientSheaf` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`: the three conclusions of Stacks
  0265, each conditional on that hypothesis and on nothing else. These are the only results in
  this file which ask `U` to be affine, and the reason is the route rather than the
  mathematics; see the note above.

## Implementation notes

The containment `Stacks.Groupoids.contains_left_of_mono` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelationSize` closes a gap which was previously
recorded as open, namely that `R` need not be an object of the site, so
that the fibre products the proof of Stacks 0265 forms with `R` need not be representable. It
*is* an object of the site, and no finiteness hypothesis on `j` is needed: in particular
Stacks 02FV is not needed, the route through
`AlgebraicGeometry.Scheme.size_lt_of_mono_locallyOfFinitePresentation` having asked for `j` to
be locally of finite presentation, which does not follow from the hypotheses since
`U ×_S U ⟶ U` need not be locally of finite type.

The sheaf condition for the functor of points of the relation scheme, which the same audit
recorded as a second open gap, is
`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj`: it is continuity of
the inclusion of the big fppf site of `S` into all `S`-schemes, not subcanonicality, and it
holds for an arbitrary `R : Over S`.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

open AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restricted functor of points of an arbitrary `S`-scheme is a sheaf on the big fppf
site of `S`.** This is
`AlgebraicGeometry.BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj` in the
`Stacks.Groupoids.points` spelling, which is the shape in which the quotient machinery
consumes it.

The scheme `R` is not assumed to be an object of the site, so this is not subcanonicality of
the site; it is continuity of the inclusion of the big fppf site of `S` into all `S`-schemes
applied to the presheaf represented by `R`. -/
theorem isSheaf_points (R : Over S) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (points (Over.post B.inclusion) R) :=
  BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS R

/-! ### Surjectivity and quasi-finiteness of the two maps of an étale equivalence relation

The target and source maps of an étale equivalence relation are étale by definition, and they
are *split* epimorphisms, the splitting being the reflexivity morphism of the equivalence
relation. Together with
`Stacks.Groupoids.isSeparated_target_of_isAffine` and
`Stacks.Groupoids.isSeparated_source_of_isAffine`, which need `U` affine, this is the full list
of properties of `R ⟶ U` which the fppf descent of Stacks 02W8 consumes in the proof of Stacks
0265: separated, locally quasi-finite, locally of finite type, surjective and étale. -/

/-- A morphism of schemes with a section is surjective. -/
private theorem surjective_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : g ≫ f = 𝟙 Y) : AlgebraicGeometry.Surjective f := by
  refine ⟨fun y ↦ ⟨g.base y, ?_⟩⟩
  show (g ≫ f).base y = y
  rw [h]
  rfl

variable {S}

/-- The target map of an étale equivalence relation is surjective: the reflexivity morphism of
the equivalence relation is a section of it. -/
theorem surjective_target {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : AlgebraicGeometry.Surjective j.target.left := by
  obtain ⟨⟨e⟩⟩ := (inferInstance : IsEquivalenceRelation j.target j.source)
  exact surjective_of_section _ e.r.left
    (by rw [← Over.comp_left, e.reflexivity₁, Over.id_left])

/-- The source map of an étale equivalence relation is surjective. -/
theorem surjective_source {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : AlgebraicGeometry.Surjective j.source.left := by
  obtain ⟨⟨e⟩⟩ := (inferInstance : IsEquivalenceRelation j.target j.source)
  exact surjective_of_section _ e.r.left
    (by rw [← Over.comp_left, e.reflexivity₂, Over.id_left])

/-- The target map of an étale equivalence relation is locally quasi-finite, being étale. -/
theorem locallyQuasiFinite_target {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : LocallyQuasiFinite j.target.left :=
  (locallyQuasiFinite_of_etale j.target.left).2

/-- The source map of an étale equivalence relation is locally quasi-finite. -/
theorem locallyQuasiFinite_source {R U : Over S} (j : PreRelation R U)
    [IsEtaleEquivalenceRelation j] : LocallyQuasiFinite j.source.left :=
  (locallyQuasiFinite_of_etale j.source.left).2

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

open Stacks.Groupoids Opposite

/-! ### The chart of the quotient sheaf, locally on a point of the target

The content of Stacks 0265 is this: *after a point of the quotient sheaf has been lifted to
`U`*, the base change of the chart along that point is a scheme, and the projection to the
base is a locally quasi-finite morphism locally of finite type which is surjective and étale.
The base change is the relation, pulled back along the lift, so that separatedness of the
projection comes with the target map of the relation and is the only one of the five
properties of Stacks 02W8 which asks `U` to be affine. Everything that remains after this is
fppf descent: a point of the quotient sheaf lifts only *locally* for the topology, by
`Stacks.Groupoids.isLocallySurjective_quotientChart`, and the local descriptions have to be
glued. -/

/-- A square whose cone has a lift for every cone, with jointly monic legs, is a pullback. -/
private theorem isPullback_of_exists_lift {C : Type*} [Category C] {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (hlift : ∀ s : PullbackCone f g, ∃ l : s.pt ⟶ P, l ≫ fst = s.fst ∧ l ≫ snd = s.snd)
    (huniq : ∀ {T : C} (m m' : T ⟶ P), m ≫ fst = m' ≫ fst → m ≫ snd = m' ≫ snd → m = m') :
    IsPullback fst snd f g :=
  .of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk _ (fun s => (hlift s).choose)
    (fun s => (hlift s).choose_spec.1) (fun s => (hlift s).choose_spec.2)
    fun s _ h1 h2 => huniq _ _ (h1.trans (hlift s).choose_spec.1.symm)
      (h2.trans (hlift s).choose_spec.2.symm))

/-- Points of `U` with the same image under a map `f` out of `yoneda.obj U` have the same
composite with `f` on Yoneda. -/
private theorem yoneda_map_comp_eq_of_app_eq {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {U T : BigFppfOver B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ Y) {g g' : T ⟶ U} (h : f.app (op T) g = f.app (op T) g') :
    yoneda.map g ≫ f = yoneda.map g' ≫ f := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  exact h

/-- A point `xx` of `U` over a point of `Y` pulled back along `q` gives a factorisation of
`yoneda.map q ≫ h` through `f`. -/
private theorem yoneda_map_comp_eq_of_app_eq_map {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {U a b : BigFppfOver B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ Y) (q : b ⟶ a) (h : yoneda.obj a ⟶ Y) {xx : b ⟶ U}
    (hxx : f.app (op b) xx = Y.map q.op (yonedaEquiv h)) :
    yoneda.map q ≫ h = yoneda.map xx ≫ f := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact hxx.symm

/-- **The base change of the chart of a quotient sheaf along a lifted point.** Let `j` be an
étale equivalence relation on an object `U` of the big fppf site of `S`, let `c` be another
object of the site and let `x : c ⟶ U`. Then the base change of the chart
`yoneda.obj U ⟶ U/R` along the point `yoneda.obj c ⟶ U/R` determined by `x` is represented by
an object `d` of the site, and the projection `d ⟶ c` is surjective, étale, locally
quasi-finite and locally of finite type.

The object `d` is the fibre product `R ×_{t, U} c` of the relation along the target map, which
is an object of the site by
`AlgebraicGeometry.BigFppfSite.contains_left_of_isEtaleEquivalenceRelation` together with
closure of the site under fibre products, and the projection `d ⟶ c` is the base change of
the target map `R ⟶ U`, which carries all four properties by
`Stacks.Groupoids.surjective_target` and `Stacks.Groupoids.locallyQuasiFinite_target`. The
square itself is recorded in the second clause, so that any further property of the target map
transfers to the projection by base change; separatedness of the target map is the one such
property which needs `U` affine, and it is read off that clause rather than listed here.

That the square is Cartesian is the identification of the kernel pair of the chart with the
relation, `Stacks.Groupoids.quotientChart_app_eq_iff_rel`, whose two sheaf hypotheses are
discharged by `Stacks.Groupoids.isSheaf_points`. The universal property is checked against an
arbitrary presheaf, one section at a time: a section of the test presheaf gives a pair of
points of `U` and of `c` with the same image in the quotient sheaf, hence a *unique* point of
the relation above them, and uniqueness is what makes the resulting family natural. -/
theorem exists_isPullback_quotientChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U))
    [IsEtaleEquivalenceRelation j]
    (c : BigFppfOver B S hS) (x : c ⟶ U) :
    ∃ (d : BigFppfOver B S hS) (p₁ : d ⟶ U) (p₂ : d ⟶ c),
      IsPullback (yoneda.map p₁) (yoneda.map p₂)
        (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yoneda.map x ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) ∧
      (∃ t, IsPullback t ((BigFppfOver.toScheme B S hS).map p₂) j.target.left
        ((Over.post B.inclusion).map x).left) ∧
      AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map p₂) ∧
      Etale ((BigFppfOver.toScheme B S hS).map p₂) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map p₂) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p₂) := by
  classical
  have hmono : Mono j := mono_of_isEtaleEquivalenceRelation j
  have hR := Stacks.Groupoids.contains_left_of_isEtaleEquivalenceRelation B S hS U j
  have hW : B.Contains (pullback j.target.left
      ((Over.post B.inclusion).map x).left) :=
    Scheme.size_pullback_lt _ _ hR c.left.2
  have hx : ((Over.post B.inclusion).map x).left ≫ ((Over.post B.inclusion).obj U).hom =
      ((Over.post B.inclusion).obj c).hom := Over.w ((Over.post B.inclusion).map x)
  have hjt : j.target.left ≫ ((Over.post B.inclusion).obj U).hom = R.hom := Over.w j.target
  have hjs : j.source.left ≫ ((Over.post B.inclusion).obj U).hom = R.hom := Over.w j.source
  set ch := quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j with hch
  set d : BigFppfOver B S hS := BigFppfOver.mk B S hS hW
    (pullback.snd j.target.left ((Over.post B.inclusion).map x).left ≫
      ((Over.post B.inclusion).obj c).hom) with hd
  set p₂ : d ⟶ c := Over.homMk (ObjectProperty.homMk
      (pullback.snd j.target.left ((Over.post B.inclusion).map x).left))
      (by apply ObjectProperty.hom_ext; rfl) with hp₂
  set p₁ : d ⟶ U := Over.homMk (ObjectProperty.homMk
      (pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫ j.source.left))
      (by
        apply ObjectProperty.hom_ext
        show (pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫
            j.source.left) ≫ ((Over.post B.inclusion).obj U).hom =
          pullback.snd j.target.left ((Over.post B.inclusion).map x).left ≫
            ((Over.post B.inclusion).obj c).hom
        rw [← hx, Category.assoc, hjs, ← hjt, ← Category.assoc, pullback.condition,
          Category.assoc]) with hp₁
  have hp₂map : (BigFppfOver.toScheme B S hS).map p₂ =
      pullback.snd j.target.left ((Over.post B.inclusion).map x).left := rfl
  have hp₁map : (BigFppfOver.toScheme B S hS).map p₁ =
      pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫ j.source.left := rfl
  -- the relation point attached to `d`
  set rho : (Over.post B.inclusion).obj d ⟶ R :=
    Over.homMk (pullback.fst j.target.left ((Over.post B.inclusion).map x).left)
      (by
        show pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫ R.hom =
          pullback.snd j.target.left ((Over.post B.inclusion).map x).left ≫
            ((Over.post B.inclusion).obj c).hom
        rw [← hjt, ← Category.assoc, pullback.condition, Category.assoc, hx]) with hrho
  have hrhot : rho ≫ j.target = (Over.post B.inclusion).map (p₂ ≫ x) := by
    ext
    show pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫ j.target.left =
      ((Over.post B.inclusion).map p₂ ≫ (Over.post B.inclusion).map x).left
    show _ = (BigFppfOver.toScheme B S hS).map p₂ ≫
      ((Over.post B.inclusion).map x).left
    rw [hp₂map, pullback.condition]
    rfl
  have hrhos : rho ≫ j.source = (Over.post B.inclusion).map p₁ := by
    ext
    rfl
  -- joint monicity of the two projections of `d`
  have hjm : ∀ {T : BigFppfOver B S hS} (m m' : T ⟶ d),
      m ≫ p₁ = m' ≫ p₁ → m ≫ p₂ = m' ≫ p₂ → m = m' := by
    intro T m m' h1 h2
    apply BigFppfOver.map_toScheme_injective B S hS
    apply pullback.hom_ext
    · have hkey : (Over.post B.inclusion).map m ≫ rho =
          (Over.post B.inclusion).map m' ≫ rho := by
        refine PreRelation.ext_of_target_of_source j ?_ ?_
        · rw [Category.assoc, Category.assoc, hrhot, ← Functor.map_comp, ← Functor.map_comp,
            ← Category.assoc, ← Category.assoc, h2]
        · rw [Category.assoc, Category.assoc, hrhos, ← Functor.map_comp, ← Functor.map_comp, h1]
      exact congrArg Over.Hom.left hkey
    · have := congrArg (BigFppfOver.toScheme B S hS).map h2
      rwa [Functor.map_comp] at this
  -- the commutative square
  have hcomm : yoneda.map p₁ ≫ ch = yoneda.map p₂ ≫ yoneda.map x ≫ ch := by
    rw [← Category.assoc, ← yoneda.map_comp]
    exact yoneda_map_comp_eq_of_app_eq ch
      (quotientChart_app_eq_of_rel (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        U j ⟨rho, hrhot, hrhos⟩).symm
  -- the lifting property on representables
  have hker : ∀ (T : BigFppfOver B S hS) (a : T ⟶ U) (b : T ⟶ c),
      ch.app (op T) a = ch.app (op T) (b ≫ x) →
      ∃ m : T ⟶ d, m ≫ p₁ = a ∧ m ≫ p₂ = b := by
    intro T a b hab
    obtain ⟨r, hr1, hr2⟩ :=
      (quotientChart_app_eq_iff_rel (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j
        (isPreEquivalenceRelation_of_isEtaleEquivalenceRelation j)
        (isSheaf_points B S hS R) (isSheaf_points B S hS _) (b ≫ x) a).mp hab.symm
    have hr1' : r.left ≫ j.target.left =
        ((Over.post B.inclusion).map b).left ≫ ((Over.post B.inclusion).map x).left := by
      have := congrArg Over.Hom.left hr1
      rwa [Functor.map_comp] at this
    have hr2' : r.left ≫ j.source.left = ((Over.post B.inclusion).map a).left :=
      congrArg Over.Hom.left hr2
    refine ⟨BigFppfOver.homMk B S hS hW
      (pullback.snd j.target.left ((Over.post B.inclusion).map x).left ≫
        ((Over.post B.inclusion).obj c).hom)
      (pullback.lift r.left ((Over.post B.inclusion).map b).left hr1') ?_, ?_, ?_⟩
    · exact (pullback.lift_snd_assoc _ _ _ _).trans (Over.w ((Over.post B.inclusion).map b))
    · apply BigFppfOver.map_toScheme_injective B S hS
      show pullback.lift r.left ((Over.post B.inclusion).map b).left hr1' ≫
          (pullback.fst j.target.left ((Over.post B.inclusion).map x).left ≫
            j.source.left) = ((Over.post B.inclusion).map a).left
      exact (pullback.lift_fst_assoc _ _ _ _).trans hr2'
    · apply BigFppfOver.map_toScheme_injective B S hS
      show pullback.lift r.left ((Over.post B.inclusion).map b).left hr1' ≫
          pullback.snd j.target.left ((Over.post B.inclusion).map x).left =
        ((Over.post B.inclusion).map b).left
      exact pullback.lift_snd _ _ _
  -- the geometric properties of the second projection
  have hst : AlgebraicGeometry.Surjective j.target.left := surjective_target j
  have hlqf : LocallyQuasiFinite j.target.left := locallyQuasiFinite_target j
  refine ⟨d, p₁, p₂, ?_, ⟨_, IsPullback.of_hasPullback _ _⟩, ?_, ?_, ?_, ?_⟩
  · -- the Cartesian square
    choose lf hlf1 hlf2 using hker
    have hlift : ∀ s : PullbackCone ch (yoneda.map x ≫ ch),
        ∃ l : s.pt ⟶ yoneda.obj d,
          l ≫ yoneda.map p₁ = s.fst ∧ l ≫ yoneda.map p₂ = s.snd := by
      intro s
      have hcond : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (w : s.pt.obj T),
          ch.app (op T.unop) (s.fst.app T w) =
            ch.app (op T.unop) (s.snd.app T w ≫ x) := by
        intro T w
        have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.condition T) w
        simpa using h
      refine ⟨{ app := fun T => ↾fun w =>
                  lf T.unop (s.fst.app T w) (s.snd.app T w) (hcond T w)
                naturality := ?_ }, ?_, ?_⟩
      · intro T T' k
        ext w
        show lf (unop T') _ _ _ = k.unop ≫ lf (unop T) _ _ _
        refine hjm _ _ ?_ ?_
        · rw [hlf1, Category.assoc, hlf1]
          exact ConcreteCategory.congr_hom (s.fst.naturality k) w
        · rw [hlf2, Category.assoc, hlf2]
          exact ConcreteCategory.congr_hom (s.snd.naturality k) w
      · ext T w
        exact hlf1 _ _ _ _
      · ext T w
        exact hlf2 _ _ _ _
    refine isPullback_of_exists_lift hcomm hlift fun m m' h1 h2 => ?_
    ext T w
    refine hjm _ _ ?_ ?_
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app h1 T) w
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app h2 T) w
  · show AlgebraicGeometry.Surjective
      (pullback.snd j.target.left ((Over.post B.inclusion).map x).left)
    infer_instance
  · show Etale (pullback.snd j.target.left ((Over.post B.inclusion).map x).left)
    infer_instance
  · show LocallyQuasiFinite
      (pullback.snd j.target.left ((Over.post B.inclusion).map x).left)
    infer_instance
  · show LocallyOfFiniteType
      (pullback.snd j.target.left ((Over.post B.inclusion).map x).left)
    infer_instance

/-! ### The diagonal of the quotient sheaf, locally on a pair of points

The same analysis applies to the diagonal of the quotient sheaf: after a pair of points of
the quotient over an object `a` of the site has been lifted to `U`, the base change of the
diagonal along that pair is the relation, pulled back along the pair of lifts, and its
projection to `a` is a monomorphism which is separated, locally quasi-finite and locally of
finite type — the property of Stacks 02W8 restricted to monomorphisms. No affineness of `U`
is needed here: `j` itself is separated, locally quasi-finite and locally of finite type with
no hypothesis on `U`, by `Stacks.Groupoids.isSeparated_isEtaleEquivalenceRelation` and its two
companions. -/

/-- **The base change of the diagonal of the quotient sheaf along a lifted pair of points.**
Let `j` be an étale equivalence relation on an object `U` of the big fppf site of `S`, let `a`
be another object of the site and let `x y : a ⟶ U`. Then the base change of the diagonal of
the quotient sheaf along the pair of points of the quotient determined by `x` and `y` is
represented by an object `d` of the site, and the projection `d ⟶ a` is a monomorphism which
is separated, locally quasi-finite and locally of finite type.

The last clause says that the projection inherits from `j` *every* property stable under base
change — in particular affineness, which is what the diagonal of the quotient sheaf of an affine
relation needs. It is stated as an implication rather than taken as a hypothesis because no such
property is part of being an étale equivalence relation, and the four unconditional properties
are needed without one.

The object `d` is the fibre product `R ×_{j, U ×_S U} a` of the relation along the pair
`(x, y)`, and the projection `d ⟶ a` is the base change of `j` itself, which is where all five
properties come from. The square is Cartesian for the same reason as in
`AlgebraicGeometry.Space.exists_isPullback_quotientChart`: a section of a test presheaf gives a
point of `a` whose two images in the quotient agree, hence a unique point of the relation above
the pair, and the uniqueness is here visible as the projection `d ⟶ a` being a
monomorphism. -/
theorem exists_isPullback_diag_quotientSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U))
    [IsEtaleEquivalenceRelation j]
    (a : BigFppfOver B S hS) (x y : a ⟶ U) :
    ∃ (d : BigFppfOver B S hS) (p : d ⟶ a),
      IsPullback (yoneda.map (p ≫ x) ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yoneda.map p)
        (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)
        (prod.lift
          (yoneda.map x ≫
            quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
          (yoneda.map y ≫
            quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)) ∧
      Mono ((BigFppfOver.toScheme B S hS).map p) ∧
      AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) ∧
      LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map p) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) ∧
      ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange → P j.left →
        P ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  have hmono : Mono j := mono_of_isEtaleEquivalenceRelation j
  have hR := Stacks.Groupoids.contains_left_of_isEtaleEquivalenceRelation B S hS U j
  set xy : PreRelation ((Over.post B.inclusion).obj a) ((Over.post B.inclusion).obj U) :=
    prod.lift ((Over.post B.inclusion).map x) ((Over.post B.inclusion).map y) with hxy
  have hxyt : xy.target = (Over.post B.inclusion).map x := prod.lift_fst _ _
  have hxys : xy.source = (Over.post B.inclusion).map y := prod.lift_snd _ _
  have hW : B.Contains (pullback j.left xy.left) :=
    Scheme.size_pullback_lt _ _ hR a.left.2
  set ch := quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j with hch
  set d : BigFppfOver B S hS := BigFppfOver.mk B S hS hW
    (pullback.snd j.left xy.left ≫ ((Over.post B.inclusion).obj a).hom) with hd
  set p : d ⟶ a := Over.homMk (ObjectProperty.homMk (pullback.snd j.left xy.left))
    (by apply ObjectProperty.hom_ext; rfl) with hp
  have hpmap : (BigFppfOver.toScheme B S hS).map p = pullback.snd j.left xy.left := rfl
  have hjw : j.left ≫
      (((Over.post B.inclusion).obj U) ⨯ ((Over.post B.inclusion).obj U) : Over S).hom =
      R.hom := Over.w j
  have hxyw : xy.left ≫
      (((Over.post B.inclusion).obj U) ⨯ ((Over.post B.inclusion).obj U) : Over S).hom =
      ((Over.post B.inclusion).obj a).hom := Over.w xy
  set rho : (Over.post B.inclusion).obj d ⟶ R :=
    Over.homMk (pullback.fst j.left xy.left)
      (by
        show pullback.fst j.left xy.left ≫ R.hom =
          pullback.snd j.left xy.left ≫ ((Over.post B.inclusion).obj a).hom
        rw [← hjw, ← Category.assoc, pullback.condition, Category.assoc, hxyw]) with hrho
  have hrhoj : rho ≫ j = (Over.post B.inclusion).map p ≫ xy := by
    refine Over.OverMorphism.ext ?_
    show pullback.fst j.left xy.left ≫ j.left =
      ((Over.post B.inclusion).map p ≫ xy).left
    show _ = (BigFppfOver.toScheme B S hS).map p ≫ xy.left
    rw [hpmap, pullback.condition]
    rfl
  have hrhot : rho ≫ j.target = (Over.post B.inclusion).map (p ≫ x) := by
    show rho ≫ j ≫ prod.fst = _
    rw [← Category.assoc, hrhoj, Category.assoc]
    show (Over.post B.inclusion).map p ≫ xy.target = _
    rw [hxyt, ← Functor.map_comp]
  have hrhos : rho ≫ j.source = (Over.post B.inclusion).map (p ≫ y) := by
    show rho ≫ j ≫ prod.snd = _
    rw [← Category.assoc, hrhoj, Category.assoc]
    show (Over.post B.inclusion).map p ≫ xy.source = _
    rw [hxys, ← Functor.map_comp]
  have heq : yoneda.map (p ≫ x) ≫ ch = yoneda.map (p ≫ y) ≫ ch :=
    yoneda_map_comp_eq_of_app_eq ch
      (quotientChart_app_eq_of_rel (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        U j ⟨rho, hrhot, hrhos⟩)
  have hmp : Mono ((BigFppfOver.toScheme B S hS).map p) := by
    have : Mono j.left := inferInstance
    show Mono (pullback.snd j.left xy.left)
    infer_instance
  have hmonop : Mono p := (BigFppfOver.toScheme B S hS).mono_of_mono_map hmp
  have hker2 : ∀ (T : BigFppfOver B S hS) (g : T ⟶ a),
      ch.app (op T) (g ≫ x) = ch.app (op T) (g ≫ y) → ∃ m : T ⟶ d, m ≫ p = g := by
    intro T g hg
    obtain ⟨r, hr1, hr2⟩ :=
      (quotientChart_app_eq_iff_rel (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j
        (isPreEquivalenceRelation_of_isEtaleEquivalenceRelation j)
        (isSheaf_points B S hS R) (isSheaf_points B S hS _) (g ≫ x) (g ≫ y)).mp hg
    have hrj : r ≫ j = (Over.post B.inclusion).map g ≫ xy := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc]
        show r ≫ j.target = (Over.post B.inclusion).map g ≫ xy.target
        rw [hr1, hxyt, ← Functor.map_comp]
      · rw [Category.assoc, Category.assoc]
        show r ≫ j.source = (Over.post B.inclusion).map g ≫ xy.source
        rw [hr2, hxys, ← Functor.map_comp]
    have hrj' : r.left ≫ j.left = ((Over.post B.inclusion).map g).left ≫ xy.left :=
      congrArg Over.Hom.left hrj
    refine ⟨BigFppfOver.homMk B S hS hW
      (pullback.snd j.left xy.left ≫ ((Over.post B.inclusion).obj a).hom)
      (pullback.lift r.left ((Over.post B.inclusion).map g).left hrj') ?_, ?_⟩
    · exact (pullback.lift_snd_assoc _ _ _ _).trans (Over.w ((Over.post B.inclusion).map g))
    · apply BigFppfOver.map_toScheme_injective B S hS
      show pullback.lift r.left ((Over.post B.inclusion).map g).left hrj' ≫
          pullback.snd j.left xy.left = ((Over.post B.inclusion).map g).left
      exact pullback.lift_snd _ _ _
  have hsep : AlgebraicGeometry.IsSeparated j.left := isSeparated_isEtaleEquivalenceRelation j
  have hlqf : LocallyQuasiFinite j.left := locallyQuasiFinite_isEtaleEquivalenceRelation j
  have hloft : LocallyOfFiniteType j.left := locallyOfFiniteType_isEtaleEquivalenceRelation j
  refine ⟨d, p, ?_, hmp, ?_, ?_, ?_, ?_⟩
  · choose lf2 hlf2 using hker2
    have hcomm : (yoneda.map (p ≫ x) ≫ ch) ≫
          diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj =
        yoneda.map p ≫ prod.lift (yoneda.map x ≫ ch) (yoneda.map y ≫ ch) := by
      refine prod.hom_ext ?_ ?_
      · simp only [Category.assoc, prod.lift_fst, Category.comp_id, Functor.map_comp]
      · simp only [Category.assoc, prod.lift_snd, Category.comp_id, Functor.map_comp]
        calc yoneda.map p ≫ yoneda.map x ≫ ch
            = yoneda.map (p ≫ x) ≫ ch := by rw [Functor.map_comp, Category.assoc]
          _ = yoneda.map (p ≫ y) ≫ ch := heq
          _ = yoneda.map p ≫ yoneda.map y ≫ ch := by rw [Functor.map_comp, Category.assoc]
    have hlift : ∀ s : PullbackCone
          (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)
          (prod.lift (yoneda.map x ≫ ch) (yoneda.map y ≫ ch)),
        ∃ l : s.pt ⟶ yoneda.obj d,
          l ≫ (yoneda.map (p ≫ x) ≫ ch) = s.fst ∧ l ≫ yoneda.map p = s.snd := by
      intro s
      have hc1 : s.fst = s.snd ≫ (yoneda.map x ≫ ch) := by
        simpa using congrArg (· ≫ prod.fst) s.condition
      have hc2 : s.fst = s.snd ≫ (yoneda.map y ≫ ch) := by
        simpa using congrArg (· ≫ prod.snd) s.condition
      have hcond : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (w : s.pt.obj T),
          ch.app (op T.unop) (s.snd.app T w ≫ x) =
            ch.app (op T.unop) (s.snd.app T w ≫ y) := by
        intro T w
        simpa using ConcreteCategory.congr_hom (NatTrans.congr_app (hc1.symm.trans hc2) T) w
      set l : s.pt ⟶ yoneda.obj d :=
        { app := fun T => ↾fun w => lf2 T.unop (s.snd.app T w) (hcond T w)
          naturality := by
            intro T T' k
            ext w
            show lf2 (unop T') _ _ = k.unop ≫ lf2 (unop T) _ _
            refine (cancel_mono p).mp ?_
            rw [hlf2, Category.assoc, hlf2]
            exact ConcreteCategory.congr_hom (s.snd.naturality k) w } with hl
      have hfr : l ≫ yoneda.map p = s.snd := by
        ext T w
        exact hlf2 _ _ _
      refine ⟨l, ?_, hfr⟩
      calc l ≫ (yoneda.map (p ≫ x) ≫ ch)
          = (l ≫ yoneda.map p) ≫ (yoneda.map x ≫ ch) := by
            rw [Functor.map_comp]; simp
        _ = s.snd ≫ (yoneda.map x ≫ ch) := by rw [hfr]
        _ = s.fst := hc1.symm
    exact isPullback_of_exists_lift hcomm hlift fun m m' _ h2 =>
      (cancel_mono (yoneda.map p)).mp h2
  · show AlgebraicGeometry.IsSeparated (pullback.snd j.left xy.left)
    infer_instance
  · show LocallyQuasiFinite (pullback.snd j.left xy.left)
    infer_instance
  · show LocallyOfFiniteType (pullback.snd j.left xy.left)
    infer_instance
  · intro P hP hPj
    show P (pullback.snd j.left xy.left)
    exact hP.of_isPullback (IsPullback.of_hasPullback j.left xy.left) hPj

/-! ### The residue: effective fppf descent

A point of the quotient sheaf over an object `a` of the site lifts to `U` only *locally* for
the fppf topology — that is the content of
`Stacks.Groupoids.isLocallySurjective_quotientChart` — so the local descriptions of the
previous section have to be glued along a covering sieve of `a`. That glueing is effective
fppf descent, Stacks 02W8, and it is the one thing in Stacks 0265 which is not available in
this library.

**It is not `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`.** That
hypothesis is descent along a *single* surjective étale morphism of the site, and the
covering produced by local surjectivity of the chart is a covering sieve for the fppf
topology: its members are neither individually surjective nor étale, and replacing the
family by the coproduct of its members is not available either, because the site's size
cutoff is only known to have uncountable cofinality, so an unbounded coproduct of its
objects need not lie in it. The hypothesis below is therefore the covering-sieve form.

The property at which it is taken is the property of Stacks 02W8 — separated, locally
quasi-finite, locally of finite type — *together with* surjectivity and étaleness, which are
the two properties Stacks 0265 asserts of the quotient map. Effective descent at that smaller
property follows from Stacks 02W8 together with fppf descent for the properties "surjective"
and "étale", which is Mathlib's `CategoryTheory.MorphismProperty.DescendsAlong` and is
recorded in this library by the two theorems named
`surjective_descendsAlong_…` and `etale_descendsAlong_…` in
`StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent`;
that reduction is *not* carried out here, because
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le`, which performs it for
a single surjective étale morphism, uses surjectivity and étaleness of the covering morphism
and so has no covering-sieve analogue. -/

/-- Morphisms with property `P` *descend effectively along the covering sieves* of the big
fppf site of `S` when the following holds. Let `f : X ⟶ Y` be a morphism of presheaves with
`X` and `Y` sheaves, let `h : yoneda.obj a ⟶ Y` be a morphism from a representable presheaf
and let `T` be a covering sieve of `a`. If the base change of `f` along `yoneda.map q ≫ h` is
representable with `P` for every arrow `q` of `T`, then so is the base change of `f` along
`h`.

This is Stacks 02W8 in the form in which the proof of Stacks 0265 consumes it; see the
section introduction for why the single-morphism form
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` cannot be used instead, and
for the relation between the property this is taken at and the property Stacks 02W8 descends.

The sheaf conditions on `X` and on `Y` cannot be dropped: without them the fibre product
`X ×[Y] yoneda.obj a` need not be a sheaf, and a presheaf which is not a sheaf is not
representable. -/
def IsEffectiveDescentAlongCoveringSieve (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
    ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
      T ∈ BigFppfOver.topology B S hS a →
      (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
          (pullback.snd f (yoneda.map q ≫ h))) →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h)

/-- A base change of a morphism of presheaves which is represented by a morphism of the site
with property `P` satisfies the presheaf property attached to `P`: the chosen fibre product is
isomorphic to the representing object over the base, and the presheaf property respects
isomorphisms. -/
theorem presheaf_pullback_snd_of_isPullback {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a d : BigFppfOver B S hS}
    {k : yoneda.obj a ⟶ Y} {p₁ : yoneda.obj d ⟶ X} {p₂ : d ⟶ a}
    (sq : IsPullback p₁ (yoneda.map p₂) f k)
    (h : P ((BigFppfOver.toScheme B S hS).map p₂)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f k) := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (P.inverseImage (BigFppfOver.toScheme B S hS))
  have hri : MorphismProperty.RespectsIso
      ((P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf) := hbc.respectsIso
  have e : sq.isoPullback.inv ≫ yoneda.map p₂ = pullback.snd f k :=
    (congrArg (sq.isoPullback.inv ≫ ·) sq.isoPullback_hom_snd.symm).trans
      (Iso.inv_hom_id_assoc _ _)
  have key : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (sq.isoPullback.inv ≫ yoneda.map p₂) :=
    MorphismProperty.RespectsIso.precomp _ sq.isoPullback.inv (yoneda.map p₂)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P p₂).2 h)
  rwa [e] at key

/-- **The chart of the quotient sheaf is representable with `P`**, for any property `P` of
morphisms of schemes which is stable under base change, holds for the target map of the
relation, and descends effectively along the covering sieves of the site.

This is Stacks 0265 for the quotient map, reduced to its one geometric input, and it holds for
an arbitrary `U`: nothing is asked of the underlying scheme. The covering sieve used at an
object `a` of the site is the sieve of arrows along which the given point of the quotient sheaf
lifts to `U`, which is covering because the chart is locally surjective; over each of its
arrows the base change of the chart is described by
`AlgebraicGeometry.Space.exists_isPullback_quotientChart`.

Affineness of `U` would be needed only to supply `hP` at a property containing separatedness,
which is how the three conclusions at the end of this file use it; at
`AlgebraicGeometry.Surjective ⊓ AlgebraicGeometry.Etale` no such hypothesis arises, which is
the route taken in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal`. -/
theorem presheaf_quotientChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U))
    [IsEtaleEquivalenceRelation j]
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS P)
    (hP : P j.target.left) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
  have hri : MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
    isLocallySurjective_quotientChart _ _ _ _
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 fun a h => ?_
  refine hdesc _ (BigFppfOver.isSheaf_yoneda_obj B S hS U)
    (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).property h
    (Presheaf.imageSieve
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
      (yonedaEquiv h)) (Presheaf.imageSieve_mem _ _ _) ?_
  rintro b q ⟨xx, hxx⟩
  have hfac : yoneda.map q ≫ h =
      yoneda.map xx ≫
        quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j := by
    exact yoneda_map_comp_eq_of_app_eq_map _ q h hxx
  obtain ⟨d, p₁, p₂, sq, ⟨t, sqs⟩, -, -, -, -⟩ :=
    exists_isPullback_quotientChart B S hS U j b xx
  have sq' : IsPullback (yoneda.map p₁) (yoneda.map p₂)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
      (yoneda.map q ≫ h) := by rwa [hfac]
  exact presheaf_pullback_snd_of_isPullback sq' (MorphismProperty.of_isPullback sqs hP)

/-! ### The three conclusions of Stacks 0265 -/

section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : BigFppfOver B S hS)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {R : Over S}
  (j : PreRelation R ((Over.post B.inclusion).obj U))
  [IsEtaleEquivalenceRelation j]

/-- The property of Stacks 02W8 together with surjectivity and étaleness is stable under base
change. -/
private theorem isStableUnderBaseChange_quotientChartProperty :
    MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  have _h₁ : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite :
        MorphismProperty Scheme.{u}) := .inf
  have _h₂ : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) := .inf
  have _h₃ : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) := .inf
  .inf

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The target map of an étale equivalence relation on an affine scheme is separated, locally
quasi-finite, locally of finite type, surjective and étale. -/
private theorem quotientChartProperty_target :
    (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
      @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      j.target.left :=
  have _hA : IsAffine ((Over.post B.inclusion).obj U).left :=
    (inferInstance : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  ⟨⟨⟨⟨isSeparated_target_of_isAffine j, locallyQuasiFinite_target j⟩, inferInstance⟩,
    surjective_target j⟩, inferInstance⟩

/-- **Stacks 0265, surjectivity of the quotient map**, for the chart and conditional on
effective fppf descent. The chart of the quotient sheaf of an étale equivalence relation on an
affine scheme is representable and surjective. -/
@[sga "3 IV 4.6.6" "(iii), special case"]
theorem presheaf_surjective_quotientChart
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
  have hbc := isStableUnderBaseChange_quotientChartProperty.{u}
  refine MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) ?_) _
    (presheaf_quotientChart B S hS U j _ hdesc (quotientChartProperty_target B S hS U j))
  intro _ _ f hf
  exact hf.1.2

/-- **Stacks 0265, étaleness of the quotient map**, for the chart and conditional on effective
fppf descent. The chart of the quotient sheaf of an étale equivalence relation on an affine
scheme is representable and étale. -/
@[sga "3 IV 4.6.6" "(iii), special case"]
theorem presheaf_etale_quotientChart
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
  have hbc := isStableUnderBaseChange_quotientChartProperty.{u}
  refine MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) ?_) _
    (presheaf_quotientChart B S hS U j _ hdesc (quotientChartProperty_target B S hS U j))
  intro _ _ f hf
  exact hf.2

/-- **Stacks 0265, surjectivity of the quotient map**, in the form the source states it and
conditional on effective fppf descent: the Yoneda morphism determined by the image of the
identity of `U` under the canonical projection to the quotient sheaf is representable and
surjective.

This is `AlgebraicGeometry.Space.presheaf_surjective_quotientChart` read through
`Stacks.Groupoids.yonedaEquiv_symm_app_toQuotientSheaf`, which identifies that Yoneda morphism
with the chart. It does **not** carry `@[stacks 0265]`: the descent hypothesis is
undischarged. -/
theorem surjective_toQuotientSheaf
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) := by
  rw [yonedaEquiv_symm_app_toQuotientSheaf]
  exact presheaf_surjective_quotientChart B S hS U j hdesc

/-- **Stacks 0265, étaleness of the quotient map**, in the form the source states it and
conditional on effective fppf descent. It does **not** carry `@[stacks 0265]`: the descent
hypothesis is undischarged. -/
theorem etale_toQuotientSheaf
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) := by
  rw [yonedaEquiv_symm_app_toQuotientSheaf]
  exact presheaf_etale_quotientChart B S hS U j hdesc

end Chart

section Diagonal

/-- The product of the underlying presheaves of two sheaves is a sheaf: it is a limit of the
diagram of sheaves, and the forgetful functor to presheaves creates limits. -/
theorem isSheaf_prod {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X Y : Sheaf (BigFppfOver.topology B S hS) (Type u)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X.obj ⨯ Y.obj) := by
  apply Sheaf.isSheaf_of_isLimit (F := pair X Y)
    (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf _ (Type u))).inv).obj
      (BinaryFan.mk (prod.fst (X := X.obj) (Y := Y.obj)) prod.snd))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun (prodIsProd X.obj Y.obj)

/-- **The diagonal of the quotient sheaf is representable**, conditional on effective fppf
descent for monomorphisms locally of finite type.

That property is inside the scope of Stacks 02W8 — see the theorem
`monomorphisms_inf_locallyOfFiniteType_le_isSeparated_inf_locallyQuasiFinite` of
`StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent` — and it is the one the base
changes of the diagonal carry, being base changes of the relation `j` itself. Note that no
affineness of `U` is needed.

The covering sieve used at an object `a` of the site is the intersection of the two sieves
along which the two components of the given point of `U/R ×ₛ U/R` lift to `U`; over each of its
arrows the base change of the diagonal is described by
`AlgebraicGeometry.Space.exists_isPullback_diag_quotientSheaf`. -/
theorem relativelyRepresentable_diag_quotientSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U))
    [IsEtaleEquivalenceRelation j]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)) :
    yoneda.relativelyRepresentable
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj) := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) := .inf
  have hri : MorphismProperty.RespectsIso
      ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
        (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) :=
    isLocallySurjective_quotientChart _ _ _ _
  have key : ((MorphismProperty.monomorphisms Scheme.{u} ⊓
      @LocallyOfFiniteType).inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (diag (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj) := ?_
  · exact key.rep
  refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 fun a h => ?_
  refine hdesc _
    (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).property
    (isSheaf_prod (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j)
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j)) h
    (Presheaf.imageSieve
        (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yonedaEquiv (h ≫ prod.fst)) ⊓
      Presheaf.imageSieve
        (quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yonedaEquiv (h ≫ prod.snd)))
    ((BigFppfOver.topology B S hS).intersection_covering
      (Presheaf.imageSieve_mem _ _ _) (Presheaf.imageSieve_mem _ _ _)) ?_
  rintro b q ⟨⟨xx, hxx⟩, ⟨yy, hyy⟩⟩
  have hfac : yoneda.map q ≫ h =
      prod.lift
        (yoneda.map xx ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
        (yoneda.map yy ≫
          quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j) := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.lift_fst]
      exact yoneda_map_comp_eq_of_app_eq_map _ q _ hxx
    · rw [Category.assoc, prod.lift_snd]
      exact yoneda_map_comp_eq_of_app_eq_map _ q _ hyy
  obtain ⟨d, p, sq, hm, -, -, hloft, -⟩ :=
    exists_isPullback_diag_quotientSheaf B S hS U j b xx yy
  have sq' : IsPullback
      (yoneda.map (p ≫ xx) ≫
        quotientChart (BigFppfOver.topology B S hS) (Over.post B.inclusion) U j)
      (yoneda.map p)
      (diag (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj)
      (yoneda.map q ≫ h) := by rwa [hfac]
  exact presheaf_pullback_snd_of_isPullback sq' ⟨hm, hloft⟩

end Diagonal

/-- **Stacks 0265, the algebraic-space property**, conditional on effective fppf descent. The
quotient sheaf of an étale equivalence relation on an object of the big fppf site of `S` with
affine underlying scheme is an algebraic space over `S`.

Two instances of the descent hypothesis are used, at two different properties, and neither
implies the other. The diagonal needs it at the monomorphisms locally of finite type, which is
the property the base changes of the diagonal carry; the chart needs it at the property of
Stacks 02W8 together with surjectivity and étaleness. Both properties lie inside the scope of
Stacks 02W8, so both instances are consequences of that tag together with fppf descent for the
properties involved; see the introduction to
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`.

The affineness is an artefact of taking the chart's instance at the property of Stacks 02W8:
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafChartFromDiagonal` proves the same
conclusion for an arbitrary `U` from one descent hypothesis instead of two, which is the
algebraicity half of Stacks 02WW.

It does **not** carry `@[stacks 0265]`: the descent hypotheses are undischarged. -/
theorem isAlgebraicSpace_quotientSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U))
    [IsEtaleEquivalenceRelation j]
    (hdiag : IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (hchart : IsEffectiveDescentAlongCoveringSieve B S hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_chart B S hS U j
    (relativelyRepresentable_diag_quotientSheaf B S hS U j hdiag)
    (presheaf_surjective_quotientChart B S hS U j hchart)
    (presheaf_etale_quotientChart B S hS U j hchart)

end AlgebraicGeometry.Space

end
