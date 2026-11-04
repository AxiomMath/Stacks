module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleChartFactorization

/-!
# Affine charts of the source factoring through affine charts of the target are enough

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces over `S`.  This file proves that the étale
charts `V` of `Y'` such that

* the underlying scheme of `V` is affine, and
* the composite `V ⟶ Y' ⟶ Y` factors through an étale chart of `Y` with affine underlying
  scheme,

are enough objects of the small étale site of `Y'`: every étale chart of `Y'` is covered by such
charts.  This is the geometric content of "the question is étale local on `Y'`, so we may assume
`Y` and `Y'` affine" in the proof of **Stacks 073K**: the reduction to affine bases needs the base
of a localized square to map into an *affine chart* of `Y`, and a morphism from a scheme to an
algebraic space lifts to an étale chart of the target only locally on the source.

## Main results

* `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChartFactorsThroughAffineChart`: the
  statement above, for the property
  `AlgebraicGeometry.Space.IsAffineChartFactorsThroughAffineChart` recording the two conditions.

## Implementation notes

The covering of a chart `U` of `Y'` is the one of
`AlgebraicGeometry.Space.exists_affine_etale_chart_factorization`, read in the small étale site
of `Y'` rather than in the big fppf site: for an étale atlas `U₀ ⟶ Y`, the fibre product
`P = U₀ ×_Y U` is étale and surjective over `U`, and its affine opens mapping into affine opens of
`U₀` are étale over `U`.  Those affine opens are packaged as a family of charts over `U` with
`AlgebraicGeometry.Space.chartFamily`, and the sieve they generate is shown to be covering exactly
as in `AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`: the chosen étale covering family
tautologically equivalent to it generates a covering sieve contained in it.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of an étale chart `V` of `Y'`, relative to a morphism `g : Y' ⟶ Y` of
algebraic spaces, that `V` is affine and that the composite `V ⟶ Y' ⟶ Y` factors through an étale
chart of `Y` with affine underlying scheme. -/
def IsAffineChartFactorsThroughAffineChart {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    ObjectProperty (SmallEtale B S hS Y'.obj) :=
  fun V ↦ IsAffineChart B S hS Y'.obj V ∧
    ∃ (W : SmallEtale B S hS Y.obj) (m : V.obj.left ⟶ W.obj.left),
      IsAffineChart B S hS Y.obj W ∧ yoneda.map m ≫ W.obj.hom = V.obj.hom ≫ g.hom

/-- **The affine charts of `Y'` whose composite to `Y` factors through an affine chart of `Y` are
enough objects of the small étale site of `Y'`.**  For a morphism `g : Y' ⟶ Y` of algebraic
spaces, every étale chart of `Y'` has a covering family in the small étale topology all of whose
members are affine charts `V` of `Y'` for which `V ⟶ Y' ⟶ Y` factors through an affine étale
chart of `Y`. -/
theorem hasEnoughObjects_isAffineChartFactorsThroughAffineChart {Y' Y : AlgebraicSpaces B S hS}
    (g : Y' ⟶ Y) :
    (SmallEtale.topology B S hS Y'.obj).HasEnoughObjects
      (IsAffineChartFactorsThroughAffineChart B S hS g) := by
  classical
  intro X
  let T : BigFppfOver B S hS := X.obj.left
  let g₀ : yoneda.obj T ⟶ Y.obj := X.obj.hom ≫ g.hom
  obtain ⟨U, f, hfS, hfE⟩ := Y.property.exists_atlas
  -- The fibre product `P = U ×_Y T`, an object of the site.
  set P : BigFppfOver B S hS := hfE.rep.pullback g₀
  set a : P ⟶ U := hfE.rep.fst' g₀
  set b : P ⟶ T := hfE.rep.snd g₀
  have hsq : yoneda.map a ≫ f = yoneda.map b ≫ g₀ := (hfE.rep.isPullback' g₀).w
  have hbs : Surjective ((BigFppfOver.toScheme B S hS).map b) :=
    hfS.property g₀ (hfE.rep.fst g₀) (hfE.rep.snd g₀) (hfE.rep.isPullback g₀)
  have hbe : Etale ((BigFppfOver.toScheme B S hS).map b) :=
    hfE.property g₀ (hfE.rep.fst g₀) (hfE.rep.snd g₀) (hfE.rep.isPullback g₀)
  set α : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj U :=
    (BigFppfOver.toScheme B S hS).map a
  -- Through every point of `P` an affine open of `P` mapping into an affine open of `U`.
  have hchoice : ∀ x : (BigFppfOver.toScheme B S hS).obj P,
      ∃ (A : ((BigFppfOver.toScheme B S hS).obj U).Opens)
        (C : ((BigFppfOver.toScheme B S hS).obj P).Opens),
        IsAffineOpen A ∧ IsAffineOpen C ∧ x ∈ C ∧ C ≤ α ⁻¹ᵁ A := by
    intro x
    obtain ⟨A, hA, hAx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj U)
        (x := α.base x) (U := ⊤) trivial
    obtain ⟨C, hC, hCx, hCsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj P)
        (x := x) (U := α ⁻¹ᵁ A) hAx
    exact ⟨A, C, hA, hC, hCx, hCsub⟩
  choose A C hA hC hCx hCle using hchoice
  have hCcont : ∀ x, B.Contains (C x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (C x).ι P.left.property
  have hAcont : ∀ x, B.Contains (A x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (A x).ι U.left.property
  -- The affine opens of `P`, as schemes of `Sch_κ` over the scheme of the chart `X`.
  let Ya : (BigFppfOver.toScheme B S hS).obj P → B.Schemes := fun x => B.obj (hCcont x)
  let fa : ∀ x, Ya x ⟶ (SmallEtale.toSchemes B S hS Y'.obj).obj X := fun x =>
    ObjectProperty.homMk ((C x).ι ≫ (BigFppfOver.toScheme B S hS).map b)
  have hmapfa : ∀ x, B.inclusion.map (fa x) = (C x).ι ≫ (BigFppfOver.toScheme B S hS).map b :=
    fun _ => rfl
  have hetalefa : ∀ x, AlgebraicGeometry.Etale (B.inclusion.map (fa x)) := fun x => by
    rw [hmapfa x]
    have := hbe
    infer_instance
  let Ea := chartFamily B S hS Y'.obj Ya fa hetalefa
  -- The affine opens of `U`, as objects of the site, and the charts of `Y` they give.
  let W' : (BigFppfOver.toScheme B S hS).obj P → BigFppfOver B S hS := fun x =>
    Over.mk (ObjectProperty.homMk ((A x).ι ≫ B.inclusion.map U.hom) :
      B.obj (hAcont x) ⟶ B.obj hS)
  let κ : ∀ x, W' x ⟶ U := fun x => Over.homMk (ObjectProperty.homMk (A x).ι) rfl
  have hκmap : ∀ x, (BigFppfOver.toScheme B S hS).map (κ x) = (A x).ι := fun _ => rfl
  have hκetale : ∀ x, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (κ x)) := by
    intro x
    refine (presheaf_yoneda_map_etale_iff B S hS (κ x)).2 ?_
    rw [hκmap]
    infer_instance
  have hcomp : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) :=
    (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  let Wc : (BigFppfOver.toScheme B S hS).obj P → SmallEtale B S hS Y.obj := fun x =>
    ⟨CostructuredArrow.mk (yoneda.map (κ x) ≫ f),
      MorphismProperty.comp_mem _ _ _ (hκetale x) hfE⟩
  -- The structure morphism of `P` is the one read off `U`, and off `T`.
  have hPover : α ≫ B.inclusion.map U.hom = B.inclusion.map P.hom :=
    congrArg B.inclusion.map (Over.w a)
  have hPoverT : (BigFppfOver.toScheme B S hS).map b ≫ B.inclusion.map T.hom =
      B.inclusion.map P.hom :=
    congrArg B.inclusion.map (Over.w b)
  -- Every member of `Ea` has the property.
  have hP : ∀ x, IsAffineChartFactorsThroughAffineChart B S hS g (Ea.X x) := by
    intro x
    refine ⟨?_, Wc x, ?_⟩
    · exact hC x
    -- the member's object of the site, mapped into `P` and into `W' x`
    have hρ : ∃ ρ : (Ea.X x).obj.left ⟶ P,
        (BigFppfOver.toScheme B S hS).map ρ = (C x).ι := by
      refine BigFppfOver.exists_hom_of_comp_eq B S hS
        (show (BigFppfOver.toScheme B S hS).obj (Ea.X x).obj.left ⟶
          (BigFppfOver.toScheme B S hS).obj P from (C x).ι) ?_
      show (C x).ι ≫ B.inclusion.map P.hom =
        ((C x).ι ≫ (BigFppfOver.toScheme B S hS).map b) ≫ B.inclusion.map T.hom
      rw [Category.assoc, hPoverT]
    obtain ⟨ρ, hρmap⟩ := hρ
    have hm : ∃ m : (Ea.X x).obj.left ⟶ W' x,
        (BigFppfOver.toScheme B S hS).map m = α.resLE (A x) (C x) (hCle x) := by
      refine BigFppfOver.exists_hom_of_comp_eq B S hS _ ?_
      show α.resLE (A x) (C x) (hCle x) ≫ (A x).ι ≫ B.inclusion.map U.hom =
        ((C x).ι ≫ (BigFppfOver.toScheme B S hS).map b) ≫ B.inclusion.map T.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hPover, Category.assoc,
        hPoverT]
    obtain ⟨m, hmmap⟩ := hm
    refine ⟨m, ?_, ?_⟩
    · exact hA x
    have htri : m ≫ κ x = ρ ≫ a := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [(BigFppfOver.toScheme B S hS).map_comp m (κ x),
        (BigFppfOver.toScheme B S hS).map_comp ρ a, hmmap, hρmap]
      exact Scheme.Hom.resLE_comp_ι α (hCle x)
    have hρb : (Over.homMk (fa x) (by rfl) :
        (Over.mk (fa x ≫ X.obj.left.hom) : BigFppfOver B S hS) ⟶ X.obj.left) = ρ ≫ b := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      refine Eq.trans ?_ ((BigFppfOver.toScheme B S hS).map_comp ρ b).symm
      refine Eq.trans ?_ (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map b) hρmap).symm
      rfl
    have key : yoneda.map m ≫ yoneda.map (κ x) ≫ f = (yoneda.map (ρ ≫ b) ≫ X.obj.hom) ≫ g.hom :=
      calc yoneda.map m ≫ yoneda.map (κ x) ≫ f = yoneda.map (m ≫ κ x) ≫ f := by
            rw [yoneda.map_comp, Category.assoc]
        _ = yoneda.map (ρ ≫ a) ≫ f := by rw [htri]
        _ = yoneda.map ρ ≫ yoneda.map b ≫ g₀ := by rw [yoneda.map_comp, Category.assoc, hsq]
        _ = (yoneda.map (ρ ≫ b) ≫ X.obj.hom) ≫ g.hom := by
            simp only [yoneda.map_comp, Category.assoc, g₀]
    exact key.trans (congrArg (fun k => (yoneda.map k ≫ X.obj.hom) ≫ g.hom) hρb.symm)
  -- The same family at index universe `u + 1`, as an étale covering family of the scheme of `X`.
  let Ul :
      PreZeroHypercover.{u + 1} (B.inclusion.obj ((SmallEtale.toSchemes B S hS Y'.obj).obj X)) :=
    { I₀ := ULift.{u + 1, u} ((BigFppfOver.toScheme B S hS).obj P)
      X i := (C i.down).toScheme
      f i := (C i.down).ι ≫ (BigFppfOver.toScheme B S hS).map b }
  have hUl : Ul.presieve₀ ∈ Scheme.etalePrecoverage
      (B.inclusion.obj ((SmallEtale.toSchemes B S hS Y'.obj).obj X)) := by
    refine (Scheme.presieve₀_mem_precoverage_iff Ul).2 ⟨fun y => ?_, fun i => ?_⟩
    · have := hbs
      obtain ⟨p, hp⟩ := Scheme.Hom.surjective ((BigFppfOver.toScheme B S hS).map b) y
      exact ⟨ULift.up p, ⟨p, hCx p⟩, hp⟩
    · have := hbe
      show AlgebraicGeometry.Etale ((C i.down).ι ≫ (BigFppfOver.toScheme B S hS).map b)
      infer_instance
  obtain ⟨V, hV, hEq⟩ :=
    exists_etaleCovering_tautologicallyEquivalent B ((SmallEtale.toSchemes B S hS Y'.obj).obj X)
      Ul hUl (fun i => hCcont i.down)
  have hetaleV : ∀ i, AlgebraicGeometry.Etale (B.inclusion.map (V.f i)) := fun i =>
    ((Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).mp hV.2).2 i
  let Ev := chartFamily B S hS Y'.obj (fun i => V.X i) (fun i => V.f i) hetaleV
  have hgenEv : Ev.sieve₀ ∈ SmallEtale.topology B S hS Y'.obj X := .of X Ev.presieve₀ ⟨Ev, rfl, hV⟩
  -- every member of the chosen family factors through a member of `Ea`
  obtain ⟨β, hβ⟩ := hEq.2
  have hle : Ev.sieve₀ ≤ Ea.sieve₀ := by
    rw [show Ev.sieve₀ = Sieve.generate Ev.presieve₀ from rfl, Sieve.generate_le_iff]
    rintro Z p ⟨i⟩
    obtain ⟨e, he⟩ := hβ i
    let k : V.X i ⟶ Ya (β i).down :=
      B.inclusion.preimage
        (show B.inclusion.obj (V.X i) ⟶ B.inclusion.obj (Ya (β i).down) from e.hom)
    have hke : k ≫ fa (β i).down = V.f i := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, hmapfa]
      show B.inclusion.map k ≫ ((C (β i).down).ι ≫ (BigFppfOver.toScheme B S hS).map b) = _
      rw [show B.inclusion.map k = e.hom from B.inclusion.map_preimage _]
      exact he
    obtain ⟨φ, hφ⟩ := chartFamily_factor B S hS Y'.obj (fun i => V.X i) (fun i => V.f i) hetaleV
      Ya fa hetalefa i (β i).down k hke
    exact ⟨Ea.X (β i).down, φ, Ea.f (β i).down, ⟨(β i).down⟩, hφ⟩
  exact ⟨(BigFppfOver.toScheme B S hS).obj P, Ea.X, Ea.f,
    (SmallEtale.topology B S hS Y'.obj).superset_covering hle hgenEv, hP⟩

end AlgebraicGeometry.Space

end
