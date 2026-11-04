module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.Support.EtaleDiscreteFibres
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Specializations in the fibres of an étale chart

Let `X` be an algebraic space over a scheme `S` and let `x` be a point of `X` above which
every étale chart of `X` by an affine scheme has a finite fibre — condition (2) of
Stacks 03JS for the pair `(X, x)`. Two points of an étale scheme chart of `X` which both lie
above `x` and one of which specializes to the other are then equal: there is no nontrivial
specialization inside such a fibre. This is **Stacks 03IM**, and on a space all of whose
points satisfy that condition — in particular on a decent one — it is **Stacks 03K5**.

In the other direction specializations *lift*: if `x' ⤳ x` and the fibres above `x'` are
finite, then every point of an étale scheme chart above `x` is the specialization of a point
above `x'` (**Stacks 03K2**), and the same holds along an arbitrary flat morphism of
algebraic spaces (**Stacks 0B7W**).

## Main results

* `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq`: **Stacks 03IM**.
* `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers`:
  **Stacks 03K5**.
* `AlgebraicGeometry.Space.exists_specializes_pointsMap_eq_of_isEtale`: **Stacks 03K2**.
* `AlgebraicGeometry.Space.exists_specializes_pointsMap_eq_of_isFlat`: **Stacks 0B7W**.
* `AlgebraicGeometry.Space.exists_relationChart_of_diagonalRepresentable`: the relation
  `h_U ×_X h_U` of an étale chart, as an object of the site with two étale projections.
* `AlgebraicGeometry.Space.eq_of_specializes_of_pointsMap_yonedaMap_eq` and
  `AlgebraicGeometry.Space.exists_specializes_pointsMap_yonedaMap_eq`: the two local inputs,
  that an étale morphism of the site has discrete fibres (Stacks 03II) and that a flat one
  lifts generalizations, read on the point spaces of Stacks 03BX.
* `AlgebraicGeometry.Space.exists_isAffine_etaleChart_pointsMap_eq`: every point of a
  represented presheaf lies in the image of an étale chart by an affine scheme.

## Implementation notes

The relation `R = h_U ×_X h_U` of a chart `φ : h_U ⟶ X` is produced as an object of the site
by `AlgebraicGeometry.Space.exists_relationChart_of_diagonalRepresentable`: representability
of the diagonal of `X` makes `φ` relatively representable, so the presheaf fibre product is
represented by an object of the site and its two projections are morphisms of the site whose
underlying morphisms of schemes are étale.

Everything else happens on the point spaces of Stacks 03BX, transported to the representing
schemes along `AlgebraicGeometry.Space.schemePointsHomeomorph`, where generalizations lift
along a flat morphism (`AlgebraicGeometry.Flat.generalizingMap`) and the fibres of an étale
morphism are discrete (Stacks 03II). The tower of the proof of Stacks 03IM is built by
recursion on the subtype of points `r` of `R` whose two projections satisfy `s r ⤳ t r`;
lifting that generalization along `t` reproduces the invariant one step higher, and the
collapse argument of the source is the induction `hcollapse` inside the proof.

The source proves Stacks 03K2 directly and derives Stacks 0B7W from it, and so does this
file. The proof of Stacks 03K2 given here avoids the source's replacement of `X` by the open
subspace cut out by the image of the chart: the saturated closed set `T` built from the
finite fibre above `x'` has image disjoint from the open set `π '' Tᶜ`, whose union with it
is the open image of the chart, and that already separates `x` from the complement. It also
avoids the source's second finiteness hypothesis: only the *chart* fibre above `x'` is used,
not the fibre of the relation, so the statement asks for condition (2) of Stacks 03JS at
`x'` rather than condition (1) of Stacks 03JV.

Stacks 03IM, 03K2 and 0B7W are stated with their finiteness hypothesis written out at the
single point it concerns, as the source does. Stacks 03K5, on the other hand, is a statement
about a *decent* space, and decency is spelled here as
`AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`, condition `(α)` of Stacks 03JX,
which is weaker than condition `(γ)` — the form in which
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/Conditions.lean` reads Stacks 03I8's definition
of decency through condition (1) of Stacks 03JV — and which is all that 03K5 needs. Both are
different predicates from `AlgebraicGeometry.Space.IsDecentSpace`, which reads the same
source definition through condition (4) of Stacks 03JV; the equivalence of the three is the
content of Stacks 03JV, which is not proved in this repository.

## References

* [Stacks Project, Tag 03IM](https://stacks.math.columbia.edu/tag/03IM)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 0B7W](https://stacks.math.columbia.edu/tag/0B7W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relation of an étale chart, as an object of the site -/

/-- An étale chart of a presheaf whose diagonal is representable has a *relation*: an object
`R` of the site with two morphisms `t, s : R ⟶ U` whose underlying morphisms of schemes are
étale, such that `h_R` is the fibre product `h_U ×_X h_U`. The two conclusions recorded here
are the ones the arguments below use: `yoneda.map t` and `yoneda.map s` have the same
composite with the chart, and every pair of points of `h_U` with the same image in `X` is the
pair of images of a point of `h_R`. -/
theorem exists_relationChart_of_diagonalRepresentable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    ∃ (R : BigFppfOver B S hS) (t s : R ⟶ U),
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧
      Etale ((BigFppfOver.toScheme B S hS).map s) ∧
      yoneda.map t ≫ φ = yoneda.map s ≫ φ ∧
      ∀ a b : points B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) φ a = pointsMap B S hS (yoneda.obj U) φ b →
        ∃ r : points B S hS (yoneda.obj R),
          pointsMap B S hS (yoneda.obj R) (yoneda.map t) r = a ∧
          pointsMap B S hS (yoneda.obj R) (yoneda.map s) r = b := by
  have hrep : yoneda.relativelyRepresentable φ :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).1
      hX.diagonal_representable φ
  refine ⟨hrep.pullback φ, hrep.fst' φ, hrep.snd φ, ?_, hφ.property_snd φ,
    (hrep.isPullback' φ).w, fun a b hab ↦ ?_⟩
  · exact hφ.property φ (yoneda.map (hrep.snd φ)) (hrep.fst' φ) (hrep.isPullback' φ).flip
  · exact exists_points_of_isPullback B S hS (hrep.isPullback' φ) a b hab

/-! ### The two local inputs: discrete fibres, and lifting of generalizations -/

/-- An étale morphism of the big fppf site over `S` admits no nontrivial specialization
inside a fibre, on points: two points of the source with the same image, one a specialization
of the other, are equal.

This is the point-space form of the discreteness of the fibres of an étale morphism of
schemes, Stacks 03II. -/
theorem eq_of_specializes_of_pointsMap_yonedaMap_eq {V U : BigFppfOver B S hS} (j : V ⟶ U)
    (hj : Etale ((BigFppfOver.toScheme B S hS).map j))
    (a b : points B S hS (yoneda.obj V))
    (hab : pointsMap B S hS (yoneda.obj V) (yoneda.map j) a =
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) b)
    (hs : b ⤳ a) : a = b := by
  set f := (BigFppfOver.toScheme B S hS).map j with hf
  set e := schemePointsHomeomorph B S hS V with he
  have hab' : f (e a) = f (e b) := by
    rw [hf, he, schemePointsHomeomorph_apply, schemePointsHomeomorph_apply,
      ← pointsToScheme_pointsMap, ← pointsToScheme_pointsMap, hab]
  have hs' : e b ⤳ e a := hs.map e.continuous
  have hEtale : Etale f := hj
  have hdisc : DiscreteTopology (f.fiber (f (e a))) := discreteTopology_fiber f (f (e a))
  have hsub : (⟨e b, hab'.symm⟩ :
      (f ⁻¹' ({f (e a)} : Set ((BigFppfOver.toScheme B S hS).obj U)))) ⤳ ⟨e a, rfl⟩ :=
    (subtype_specializes_iff _ _).2 hs'
  have hfib := hsub.map (f.fiberHomeo (f (e a))).symm.continuous
  have heq := specializes_iff_eq.1 hfib
  have hval : e b = e a := by
    have := congrArg (fun z ↦ ((f.fiberHomeo (f (e a))) z).1) heq
    simpa using this
  exact (e.injective hval).symm

/-- Generalizations lift along a flat morphism of the big fppf site over `S`, on points: if
`t` sends `r` to `w` and `w'` is a generalization of `w`, then some generalization of `r` is
sent to `w'`.

This is the point-space form of the fact that generalizations lift along a flat morphism of
schemes, transported along the identification of the points of a represented presheaf with
the points of the representing scheme. -/
theorem exists_specializes_pointsMap_yonedaMap_eq {R U : BigFppfOver B S hS} (t : R ⟶ U)
    (ht : Flat ((BigFppfOver.toScheme B S hS).map t))
    (r : points B S hS (yoneda.obj R)) {w w' : points B S hS (yoneda.obj U)}
    (hrt : pointsMap B S hS (yoneda.obj R) (yoneda.map t) r = w) (hs : w' ⤳ w) :
    ∃ r' : points B S hS (yoneda.obj R), r' ⤳ r ∧
      pointsMap B S hS (yoneda.obj R) (yoneda.map t) r' = w' := by
  set eR := schemePointsHomeomorph B S hS R with heR
  set eU := schemePointsHomeomorph B S hS U with heU
  set g := (BigFppfOver.toScheme B S hS).map t with hg
  have hnat : ∀ z : points B S hS (yoneda.obj R),
      eU (pointsMap B S hS (yoneda.obj R) (yoneda.map t) z) = g (eR z) :=
    fun z ↦ pointsToScheme_pointsMap B S hS t z
  have hbase : g (eR r) = eU w := by rw [← hnat r, hrt]
  have hFlat : Flat g := ht
  have hspec : eU w' ⤳ g (eR r) := by rw [hbase]; exact hs.map eU.continuous
  obtain ⟨d, hdr, hdt⟩ := Flat.generalizingMap g hspec
  refine ⟨eR.symm d, ?_, ?_⟩
  · have := hdr.map eR.symm.continuous
    rwa [Homeomorph.symm_apply_apply] at this
  · refine eU.injective ?_
    rw [hnat, Homeomorph.apply_symm_apply, hdt]

/-- Composites of étale morphisms of presheaves, in the sense of the site, are étale. -/
private theorem presheaf_etale_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hg : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (f ≫ g) := by
  have hQEc := inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hQEpc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact MorphismProperty.comp_mem _ f g hf hg

/-- An affine open `W` of the scheme of an object `U` of the site is an object `V` of the site
with an étale chart `j : V ⟶ U` by an affine scheme, whose image on points contains the
points lying in `W`. -/
private theorem exists_etaleChart_of_isAffineOpen (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) (hW : IsAffineOpen W) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) ∧
      ∀ z : points B S hS (yoneda.obj U), schemePointsHomeomorph B S hS U z ∈ W →
        ∃ v : points B S hS (yoneda.obj V),
          pointsMap B S hS (yoneda.obj V) (yoneda.map j) v = z := by
  have hWsize : B.Contains (↑W : Scheme.{u}) :=
    (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj U) W).trans_lt U.left.property
  let hWι : B.inclusion.obj (B.obj hWsize) ⟶ B.inclusion.obj U.left := W.ι
  let ι : (B.obj hWsize : B.Schemes) ⟶ U.left := B.inclusion.preimage hWι
  let V : BigFppfOver B S hS := Over.mk (ι ≫ U.hom)
  let j : V ⟶ U := Over.homMk ι
  have hjScheme : (BigFppfOver.toScheme B S hS).map j = W.ι := by
    change B.inclusion.map (B.inclusion.preimage hWι) = W.ι
    rw [B.inclusion.map_preimage]
  refine ⟨V, j, hW, (presheaf_yoneda_map_iff B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange j).2
      (by rw [hjScheme]; infer_instance), fun z hz ↦
    ⟨(schemePointsHomeomorph B S hS V).symm ⟨schemePointsHomeomorph B S hS U z, hz⟩, ?_⟩⟩
  refine (schemePointsHomeomorph B S hS U).injective ?_
  have h1 := pointsToScheme_pointsMap B S hS j
    ((schemePointsHomeomorph B S hS V).symm ⟨schemePointsHomeomorph B S hS U z, hz⟩)
  change schemePointsHomeomorph B S hS U (pointsMap B S hS (yoneda.obj V) (yoneda.map j)
      ((schemePointsHomeomorph B S hS V).symm ⟨schemePointsHomeomorph B S hS U z, hz⟩)) =
    (BigFppfOver.toScheme B S hS).map j (schemePointsHomeomorph B S hS V
      ((schemePointsHomeomorph B S hS V).symm ⟨schemePointsHomeomorph B S hS U z, hz⟩)) at h1
  have h2 : schemePointsHomeomorph B S hS V
      ((schemePointsHomeomorph B S hS V).symm ⟨schemePointsHomeomorph B S hS U z, hz⟩) =
      ⟨schemePointsHomeomorph B S hS U z, hz⟩ :=
    (schemePointsHomeomorph B S hS V).apply_symm_apply _
  rw [h1, h2, hjScheme]
  rfl

/-! ### Stacks 03IM -/

/-- **Stacks 03IM.** Let `X` be an algebraic space over `S` and let `x` be a point of `X`
above which every étale chart of `X` by an affine scheme has a finite fibre, which is
condition (2) of Stacks 03JS for the pair `(X, x)`. If two points `u` and `u'` of an étale
scheme chart of `X` both lie above `x` and `u` is a specialization of `u'`, then `u = u'`. -/
@[stacks 03IM]
theorem eq_of_specializes_of_pointsMap_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)
    (hfinite : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ ψ : yoneda.obj V ⟶ X, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ →
      (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {x}).Finite)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (u u' : points B S hS (yoneda.obj U))
    (hu : pointsMap B S hS (yoneda.obj U) φ u = x)
    (hu' : pointsMap B S hS (yoneda.obj U) φ u' = x)
    (hs : u' ⤳ u) : u = u' := by
  classical
  by_contra hne
  -- The relation of the chart, and a point of it above the pair `(u, u')`.
  obtain ⟨R, t, s, ht, hsEt, hrel, hpair⟩ :=
    exists_relationChart_of_diagonalRepresentable B S hS hX U φ hφ
  have htFlat : Flat ((BigFppfOver.toScheme B S hS).map t) := by have := ht; infer_instance
  obtain ⟨r₀, hr₀t, hr₀s⟩ := hpair u u' (hu.trans hu'.symm)
  -- The tower of the source's proof. The invariant kept along it is that the two projections
  -- of a point of the relation are a specialization of one another; lifting that
  -- generalization along `t` reproduces the invariant one step higher.
  have hstep : ∀ r : {r : points B S hS (yoneda.obj R) //
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) r ⤳
          pointsMap B S hS (yoneda.obj R) (yoneda.map t) r},
      ∃ r' : {r : points B S hS (yoneda.obj R) //
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) r ⤳
          pointsMap B S hS (yoneda.obj R) (yoneda.map t) r},
      pointsMap B S hS (yoneda.obj R) (yoneda.map t) r'.1 =
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) r.1 ∧ r'.1 ⤳ r.1 := by
    intro r
    obtain ⟨r', hr'r, hr't⟩ := exists_specializes_pointsMap_yonedaMap_eq B S hS t htFlat r.1 rfl r.2
    refine ⟨⟨r', ?_⟩, hr't, hr'r⟩
    have hmap := hr'r.map (continuous_pointsMap B S hS (yoneda.map s))
    rw [hr't]
    exact hmap
  have hP₀ : pointsMap B S hS (yoneda.obj R) (yoneda.map s) r₀ ⤳
      pointsMap B S hS (yoneda.obj R) (yoneda.map t) r₀ := by
    rw [hr₀t, hr₀s]; exact hs
  obtain ⟨rs, hrs₀, hrst, hrsspec, hrsinv⟩ : ∃ rs : ℕ → points B S hS (yoneda.obj R),
      rs 0 = r₀ ∧
      (∀ n, pointsMap B S hS (yoneda.obj R) (yoneda.map t) (rs (n + 1)) =
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) (rs n)) ∧
      (∀ n, rs (n + 1) ⤳ rs n) ∧
      ∀ n, pointsMap B S hS (yoneda.obj R) (yoneda.map s) (rs n) ⤳
        pointsMap B S hS (yoneda.obj R) (yoneda.map t) (rs n) := by
    refine ⟨fun n ↦ (Nat.rec ⟨r₀, hP₀⟩ (fun _ r ↦ (hstep r).choose) n :
      {r : points B S hS (yoneda.obj R) //
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) r ⤳
          pointsMap B S hS (yoneda.obj R) (yoneda.map t) r}).1, rfl,
      fun n ↦ (hstep _).choose_spec.1, fun n ↦ (hstep _).choose_spec.2,
      fun n ↦ (Nat.rec ⟨r₀, hP₀⟩ (fun _ r ↦ (hstep r).choose) n :
      {r : points B S hS (yoneda.obj R) //
        pointsMap B S hS (yoneda.obj R) (yoneda.map s) r ⤳
          pointsMap B S hS (yoneda.obj R) (yoneda.map t) r}).2⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℕ → points B S hS (yoneda.obj U),
      ∀ n, w n = pointsMap B S hS (yoneda.obj R) (yoneda.map t) (rs n) :=
    ⟨_, fun _ ↦ rfl⟩
  have hsucc : ∀ n, w (n + 1) =
      pointsMap B S hS (yoneda.obj R) (yoneda.map s) (rs n) :=
    fun n ↦ (hwdef (n + 1)).trans (hrst n)
  have hw0 : w 0 = u := (hwdef 0).trans (hrs₀ ▸ hr₀t)
  have hw1 : w 1 = u' := (hsucc 0).trans (hrs₀ ▸ hr₀s)
  have hwspec : ∀ n, w (n + 1) ⤳ w n := by
    intro n
    rw [hsucc n, hwdef n]
    exact hrsinv n
  have hwimage : ∀ n, pointsMap B S hS (yoneda.obj U) φ (w n) = x := by
    intro n
    induction n with
    | zero => exact hw0 ▸ hu
    | succ n ih =>
      have h₂ := pointsMap_apply_comm B S hS hrel (rs n)
      rw [hsucc n, ← h₂, ← hwdef n]
      exact ih
  -- A collapse at one step collapses the whole tower, so the tower is injective.
  have hcollapse : ∀ n, w (n + 1) = w n → w 1 = w 0 := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
      intro hk
      refine ih ?_
      have hsEq : pointsMap B S hS (yoneda.obj R) (yoneda.map s) (rs n) =
          pointsMap B S hS (yoneda.obj R) (yoneda.map s) (rs (n + 1)) := by
        rw [← hsucc n, ← hsucc (n + 1)]
        exact hk.symm
      have hrEq : rs n = rs (n + 1) :=
        eq_of_specializes_of_pointsMap_yonedaMap_eq B S hS s hsEt _ _ hsEq (hrsspec n)
      rw [hwdef (n + 1), hwdef n, hrEq]
  have hadj : ∀ n, w (n + 1) ≠ w n := fun n h ↦
    hne (hw0.symm.trans ((hcollapse n h).symm.trans hw1))
  have hchain : ∀ i d : ℕ, w (i + d) ⤳ w i := by
    intro i d
    induction d with
    | zero => exact specializes_rfl
    | succ d ih =>
      have h₁ : w (i + d + 1) ⤳ w (i + d) := hwspec (i + d)
      have hidx : i + (d + 1) = i + d + 1 := by omega
      rw [hidx]
      exact h₁.trans ih
  have hinj : Function.Injective w := by
    have strict : ∀ i j : ℕ, i < j → w i = w j → False := by
      intro i j hij h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
      have hback : w i ⤳ w (i + 1) := h ▸ hchain (i + 1) d
      have hinsep : Inseparable (w (i + 1)) (w i) := (hwspec i).antisymm hback
      have hEq : schemePointsHomeomorph B S hS U (w (i + 1)) =
          schemePointsHomeomorph B S hS U (w i) :=
        (hinsep.map (schemePointsHomeomorph B S hS U).continuous).eq
      exact hadj i ((schemePointsHomeomorph B S hS U).injective hEq)
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact (strict i j h hij).elim
    · exact h
    · exact (strict j i h hij.symm).elim
  -- Restrict the tower to an affine open neighbourhood of `u` in the chart. The fibre of that
  -- affine chart above `x` is finite, contradicting injectivity of the tower.
  obtain ⟨W, hWaff, hWmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤)
      (Set.mem_univ (schemePointsHomeomorph B S hS U (w 0)))
  have hWall : ∀ n, schemePointsHomeomorph B S hS U (w n) ∈ W := by
    intro n
    induction n with
    | zero => exact hWmem
    | succ n ih =>
      by_contra hnot
      exact W.isOpen.not_specializes hnot ih
        ((hwspec n).map (schemePointsHomeomorph B S hS U).continuous)
  obtain ⟨V, j, hVaff, hjEtale, hjpt⟩ := exists_etaleChart_of_isAffineOpen B S hS U W hWaff
  choose v hvmap using fun n ↦ hjpt (w n) (hWall n)
  have hvinj : Function.Injective v := fun m n hmn ↦
    hinj ((hvmap m).symm.trans ((congrArg _ hmn).trans (hvmap n)))
  have hψ := presheaf_etale_comp B S hS (yoneda.map j) φ hjEtale hφ
  have hvfibre : ∀ n, pointsMap B S hS (yoneda.obj V) (yoneda.map j ≫ φ) (v n) = x := by
    intro n
    rw [pointsMap_comp_apply, hvmap n]
    exact hwimage n
  exact (Set.infinite_range_of_injective hvinj).not_finite
    ((hfinite V hVaff (yoneda.map j ≫ φ) hψ).subset
      (by rintro z ⟨n, rfl⟩; exact hvfibre n))

/-- **Stacks 03K5.** Let `X` be an algebraic space over `S` every point of which satisfies
condition (2) of Stacks 03JS — in particular, a decent one — and let `h_U ⟶ X` be an étale
chart of `X` by a scheme. Two points of the chart with the same image in `X`, one a
specialization of the other, are equal. -/
@[stacks 03K5]
theorem eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdecent : HasFiniteChartFibersAtEveryPoint B S hS X)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (u u' : points B S hS (yoneda.obj U))
    (huu' : pointsMap B S hS (yoneda.obj U) φ u = pointsMap B S hS (yoneda.obj U) φ u')
    (hs : u' ⤳ u) : u = u' :=
  eq_of_specializes_of_pointsMap_eq B S hS hX _
    (hdecent (pointsMap B S hS (yoneda.obj U) φ u)) U φ hφ u u' rfl huu'.symm hs

/-! ### Lifting a specialization to an étale chart: Stacks 03K2 -/

/-- Every point of a presheaf represented by an object of the site is in the image, on
points, of an étale chart of that object by an *affine* scheme: an affine open neighbourhood
of the corresponding point of the representing scheme is again an object of the site, and its
inclusion is an open immersion, hence étale. -/
theorem exists_isAffine_etaleChart_pointsMap_eq (U : BigFppfOver B S hS)
    (u : points B S hS (yoneda.obj U)) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U) (v : points B S hS (yoneda.obj V)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) v = u := by
  obtain ⟨W, hWaff, hWmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤)
      (Set.mem_univ (schemePointsHomeomorph B S hS U u))
  obtain ⟨V, j, hVaff, hj, hpt⟩ := exists_etaleChart_of_isAffineOpen B S hS U W hWaff
  obtain ⟨v, hv⟩ := hpt u hWmem
  exact ⟨V, j, v, hVaff, hj, hv⟩

/-- The affine case of Stacks 03K2: with the chart fibre above `x'` finite, a specialization
`x' ⤳ x` lifts to an étale chart from any prescribed point above `x`.

The chart is not assumed affine here; what the hypothesis asks for is the finiteness of the
fibre of *this* chart above `x'`, which the affine case of Stacks 03JS supplies. -/
private theorem exists_specializes_pointsMap_eq_aux
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x x' : points B S hS X} (hs : x' ⤳ x)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hfinite : (pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x'}).Finite)
    (u : points B S hS (yoneda.obj U)) (hu : pointsMap B S hS (yoneda.obj U) φ u = x) :
    ∃ u' : points B S hS (yoneda.obj U), u' ⤳ u ∧
      pointsMap B S hS (yoneda.obj U) φ u' = x' := by
  classical
  obtain ⟨R, t, s, ht, hsEt, hrel, hpair⟩ :=
    exists_relationChart_of_diagonalRepresentable B S hS hX U φ hφ
  have htFlat : Flat ((BigFppfOver.toScheme B S hS).map t) := by have := ht; infer_instance
  set π := pointsMap B S hS (yoneda.obj U) φ with hπ
  have hπrel : ∀ r : points B S hS (yoneda.obj R),
      π (pointsMap B S hS (yoneda.obj R) (yoneda.map t) r) =
        π (pointsMap B S hS (yoneda.obj R) (yoneda.map s) r) :=
    fun r ↦ pointsMap_apply_comm B S hS hrel r
  -- The union of the closures of the finitely many points above `x'`.
  set T : Set (points B S hS (yoneda.obj U)) := ⋃ a ∈ π ⁻¹' {x'}, closure {a} with hT
  have hTclosed : IsClosed T := hfinite.isClosed_biUnion fun a _ ↦ isClosed_closure
  have hmemT : ∀ a, a ∈ T ↔ ∃ c, π c = x' ∧ c ⤳ a := by
    intro a
    simp only [hT, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      ← specializes_iff_mem_closure, exists_prop]
  -- Specializations lift along the chart, through the relation.
  have hlift : ∀ a b c, π a = π b → c ⤳ b → ∃ c', c' ⤳ a ∧ π c' = π c := by
    intro a b c hab hcb
    obtain ⟨r, hrt, hrs⟩ := hpair b a hab.symm
    obtain ⟨r', hr'r, hr't⟩ :=
      exists_specializes_pointsMap_yonedaMap_eq B S hS t htFlat r hrt hcb
    refine ⟨pointsMap B S hS (yoneda.obj R) (yoneda.map s) r', ?_, ?_⟩
    · have h := hr'r.map (continuous_pointsMap B S hS (yoneda.map s))
      rwa [hrs] at h
    · rw [← hr't]
      exact (hπrel r').symm
  -- `T` is saturated for the chart: it is a union of fibres of `π`.
  have hsat : ∀ a b, π a = π b → b ∈ T → a ∈ T := by
    intro a b hab hbT
    obtain ⟨c, hcx, hcb⟩ := (hmemT b).1 hbT
    obtain ⟨c', hc'a, hc'⟩ := hlift a b c hab hcb
    exact (hmemT a).2 ⟨c', hc'.trans hcx, hc'a⟩
  -- The image of `T` is closed inside the open image of the chart, and contains `x'`.
  have hopen : IsOpenMap π := isOpenMap_pointsMap_of_presheafEtale B S hS φ hφ
  obtain ⟨a₀, ha₀⟩ : x' ∈ Set.range π := by
    by_contra hnot
    exact hopen.isOpen_range.not_specializes hnot ⟨u, hu⟩ hs
  have ha₀T : a₀ ∈ T := (hmemT a₀).2 ⟨a₀, ha₀, specializes_rfl⟩
  have hdisj : ∀ z, z ∈ π '' T → z ∉ π '' Tᶜ := by
    rintro z ⟨b, hbT, rfl⟩ ⟨a, haT, hab⟩
    exact haT (hsat a b hab hbT)
  have hxT : x ∈ π '' T := by
    by_contra hnot
    have hxO : x ∈ π '' Tᶜ := ⟨u, fun hc ↦ hnot ⟨u, hc, hu⟩, hu⟩
    have hx'O : x' ∈ π '' Tᶜ := by
      by_contra hnot'
      exact (hopen _ hTclosed.isOpen_compl).not_specializes hnot' hxO hs
    exact hdisj x' ⟨a₀, ha₀T, ha₀⟩ hx'O
  -- Transport the specialization inside `T` back to the prescribed point `u`.
  obtain ⟨u₁, hu₁T, hu₁⟩ := hxT
  obtain ⟨c, hcx, hcu₁⟩ := (hmemT u₁).1 hu₁T
  obtain ⟨c', hc'u, hc'⟩ := hlift u u₁ c (hu₁.trans hu.symm).symm hcu₁
  exact ⟨c', hc'u, hc'.trans hcx⟩

/-- **Stacks 03K2.** Let `X` be an algebraic space over `S`, let `x' ⤳ x` be a
specialization of points of `X` and assume that every étale chart of `X` by an affine scheme
has a finite fibre above `x'`, which is condition (2) of Stacks 03JS for the pair `(X, x')`.
Then for every étale chart `φ : h_U ⟶ X` of `X` by a scheme and every point `u` of the chart
above `x` there is a point `u'` of the chart above `x'` with `u' ⤳ u`. -/
@[stacks 03K2]
theorem exists_specializes_pointsMap_eq_of_isEtale
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x x' : points B S hS X} (hs : x' ⤳ x)
    (hfinite : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ ψ : yoneda.obj V ⟶ X, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ →
      (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {x'}).Finite)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (u : points B S hS (yoneda.obj U)) (hu : pointsMap B S hS (yoneda.obj U) φ u = x) :
    ∃ u' : points B S hS (yoneda.obj U), u' ⤳ u ∧
      pointsMap B S hS (yoneda.obj U) φ u' = x' := by
  -- Replace the chart by an affine one through which the given point factors.
  obtain ⟨V, j, v, hVaff, hjEt, hjv⟩ := exists_isAffine_etaleChart_pointsMap_eq B S hS U u
  have hψ := presheaf_etale_comp B S hS (yoneda.map j) φ hjEt hφ
  obtain ⟨v', hv'v, hv'⟩ := exists_specializes_pointsMap_eq_aux B S hS hX hs V
    (yoneda.map j ≫ φ) hψ (hfinite V hVaff _ hψ) v
    (by rw [pointsMap_comp_apply, hjv]; exact hu)
  refine ⟨pointsMap B S hS (yoneda.obj V) (yoneda.map j) v', ?_, ?_⟩
  · have h := hv'v.map (continuous_pointsMap B S hS (yoneda.map j))
    rwa [hjv] at h
  · rw [← pointsMap_comp_apply]
    exact hv'

/-! ### Lifting a specialization along a flat morphism: Stacks 0B7W -/

/-- **Stacks 0B7W.** Let `f : Y ⟶ X` be a flat morphism of algebraic spaces over `S`, let
`x' ⤳ x` be a specialization of points of `X` and assume that every étale chart of `X` by an
affine scheme has a finite fibre above `x'`, which is condition (2) of Stacks 03JS for the
pair `(X, x')`. Then every point `y` of `Y` above `x` is the specialization of a point of `Y`
above `x'`. -/
@[stacks 0B7W]
theorem exists_specializes_pointsMap_eq_of_isFlat
    {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X)
    (f : Y ⟶ X) (hf : IsFlat B S hS f)
    {x x' : points B S hS X} (hs : x' ⤳ x)
    (hfinite : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ ψ : yoneda.obj V ⟶ X, (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf ψ →
      (pointsMap B S hS (yoneda.obj V) ψ ⁻¹' {x'}).Finite)
    (y : points B S hS Y) (hy : pointsMap B S hS Y f y = x) :
    ∃ y' : points B S hS Y, y' ⤳ y ∧ pointsMap B S hS Y f y' = x' := by
  classical
  -- Étale atlases of `Y` and of `X`, with points above `y` and `x`.
  obtain ⟨V, aV, haVsurj, haVet⟩ := hY.exists_atlas
  obtain ⟨v, hv⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS Y hY V aV).1 haVsurj y
  obtain ⟨U, aU, haUsurj, haUet⟩ := hX.exists_atlas
  obtain ⟨u, hu⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U aU).1 haUsurj x
  -- The specialization lifts to the atlas of `X`, by Stacks 03K2.
  obtain ⟨u', hu'u, hu'⟩ :=
    exists_specializes_pointsMap_eq_of_isEtale B S hS hX hs hfinite U aU haUet u hu
  -- The fibre product `h_U ×_X h_V`, as an object of the site.
  set b : yoneda.obj V ⟶ X := aV ≫ f with hb
  have hrepU : yoneda.relativelyRepresentable aU := hX.diagonal_representable.of_diag aU
  set D : BigFppfOver B S hS := hrepU.pullback b with hD
  set iD : D ⟶ U := hrepU.fst' b with hiD
  set jD : D ⟶ V := hrepU.snd b with hjD
  have hsq : IsPullback (yoneda.map iD) (yoneda.map jD) aU b := hrepU.isPullback' b
  have hjDet : Etale ((BigFppfOver.toScheme B S hS).map jD) := haUet.property_snd b
  set aW : yoneda.obj D ⟶ Y := yoneda.map jD ≫ aV with haW
  have hjDpre : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map jD) :=
    (presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange jD).2 hjDet
  have haWet := presheaf_etale_comp B S hS (yoneda.map jD) aV hjDpre haVet
  have hcomm : yoneda.map iD ≫ aU = aW ≫ f := by
    rw [hsq.w, haW, hb, Category.assoc]
  -- Flatness of `f` is tested on the étale charts `aW` of `Y` and `aU` of `X`.
  have hiDflat : Flat ((BigFppfOver.toScheme B S hS).map iD) :=
    hf D U aW aU iD haWet haUet hcomm
  -- A point of the fibre product above `u` and `v`.
  have hcompat : pointsMap B S hS (yoneda.obj U) aU u = pointsMap B S hS (yoneda.obj V) b v := by
    rw [hb, pointsMap_comp_apply, hv, hu, hy]
  obtain ⟨z, hzU, hzV⟩ := exists_points_of_isPullback B S hS hsq u v hcompat
  -- Lift the generalization along the flat morphism `iD`.
  obtain ⟨z', hz'z, hz'⟩ :=
    exists_specializes_pointsMap_yonedaMap_eq B S hS iD hiDflat z hzU hu'u
  refine ⟨pointsMap B S hS (yoneda.obj D) aW z', ?_, ?_⟩
  · have hz : pointsMap B S hS (yoneda.obj D) aW z = y := by
      rw [haW, pointsMap_comp_apply, hzV, hv]
    have h := hz'z.map (continuous_pointsMap B S hS aW)
    rwa [hz] at h
  · rw [← pointsMap_comp_apply, ← hcomm, pointsMap_comp_apply, hz', hu']

end AlgebraicGeometry.Space

end
