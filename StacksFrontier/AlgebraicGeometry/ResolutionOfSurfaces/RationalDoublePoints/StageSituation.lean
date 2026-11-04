module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartPoint

/-!
# The rational double point situation at a closed point of the blowup of an arbitrary stage

The property `AlgebraicGeometry.PointBlowupStep.next_prop` carried by a rule for choosing the
centres of a sequence of blowups at closed points of a rational double point holds at a closed
point of the blowup of an arbitrary `AlgebraicGeometry.PointBlowupStage`, over its centre, and not
only at a closed point of the blowup of `Spec A` in the maximal ideal of `A`.

Blowing up the vanishing ideal of a closed point `p` of a scheme `X` becomes, after the flat base
change `Spec 𝒪_{X, p} ⟶ X`, the blowup of `Spec 𝒪_{X, p}` in the maximal ideal; a closed point of
the blowup of `X` over `p` has a preimage there with the same local ring; and a ring isomorphism
`A ≃+* 𝒪_{X, p}` carries this to the blowup of `Spec A` in the maximal ideal of `A`.

## Main results

* `AlgebraicGeometry.comap_fromSpecStalk_vanishingIdeal_singleton`: the inverse image of the
  vanishing ideal sheaf of a closed point `p` along `Spec 𝒪_{X, p} ⟶ X` is the ideal sheaf cut
  out by the maximal ideal of `𝒪_{X, p}`.
* `AlgebraicGeometry.comap_maximalIdealSheaf_specMap_ringEquiv`: the maximal ideal sheaf is
  carried to the maximal ideal sheaf by `Spec` of a ring isomorphism of local rings.
* `AlgebraicGeometry.exists_isClosed_ringEquiv_stalk_blowUp_comap`: along a flat preimmersion the
  blowup of the inverse image of an ideal sheaf has, over a closed point of the blowup upstairs,
  a closed point with the same local ring.
* `AlgebraicGeometry.exists_isClosed_ringEquiv_stalk_blowUp_maximalIdealSheaf`: for a local ring
  `A` isomorphic to `𝒪_{X, p}`, every closed point of the blowup of `X` in `p` lying over `p` has
  a closed point of the blowup of `Spec A` in the maximal ideal with the same local ring.
* `AlgebraicGeometry.PointBlowupStage.isRationalDoublePointAt_blowUp`:
  `AlgebraicGeometry.PointBlowupStep.next_prop` at a closed point of the blowup of an arbitrary
  stage.
* `AlgebraicGeometry.PointBlowupStage.exists_next_of_chart_isRationalDoublePointAt`: the five
  conditions a rule imposes, at a point of a standard affine chart of the blowup of a stage.
* `AlgebraicGeometry.RationalDoublePointSituation.not_forall_exists_chart`: for a Situation
  [Stacks, Tag 0BGC] with complete ring, chart data as above cannot be found at every stage.

## Implementation notes

The geometric statements above have no hypotheses beyond their setting. The statements about a
situation carry exactly what
`AlgebraicGeometry.RationalDoublePointSituation.isRationalDoublePointAt_blowUp` carries, in the
two hypotheses `hratc` and `hdata`:

* clause (1) of [Stacks, Tag 0BG7], that the completion `A^` defines a rational singularity;
* [Stacks, Tag 0BG0] in its local-ring form, that the local ring at the chosen point defines a
  rational singularity;
* a field mapping onto the residue field there and three generators of the maximal ideal;
* non-regularity of that local ring, which is a rule's *choice* of a singular point and not a
  missing result.

At a stage those two are quantified over the situations whose ring is isomorphic to the local
ring at the centre, because a stage carries the *existence* of such a situation and not a chosen
one.

Because every statement about a situation here carries `hratc` and `hdata`, no `@[stacks]` is
attached to anything in this file; in particular nothing here is a formalization of
[Stacks, Tag 0BGE]. The base change uses [Stacks, Tag 0805], registered on
`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The centre of a blowup at a closed point, seen in the local ring there -/

/-- **The inverse image of the vanishing ideal sheaf of a closed point along the canonical
morphism out of the spectrum of the local ring there is the maximal ideal sheaf.** Blowing up a
closed point `p` of `X` becomes, after the flat base change `Spec 𝒪_{X, p} ⟶ X`, blowing up the
maximal ideal of `𝒪_{X, p}`. -/
public theorem comap_fromSpecStalk_vanishingIdeal_singleton (X : Scheme.{u}) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).comap (X.fromSpecStalk x) =
      maximalIdealSheaf ↑(X.presheaf.stalk x) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ideal_comap_fromSpecStalk, IdealSheafData.stalk_vanishingIdeal_singleton x hx]
  simp only [maximalIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl,
    CategoryTheory.op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rfl

/-- **The maximal ideal sheaf is carried to the maximal ideal sheaf by `Spec` of an isomorphism
of local rings.** -/
public theorem comap_maximalIdealSheaf_specMap_ringEquiv {R A : Type u} [CommRing R]
    [IsLocalRing R] [CommRing A] [IsLocalRing A] (ε : R ≃+* A) :
    (maximalIdealSheaf R).comap (Spec.map (CommRingCat.ofHom (ε : R →+* A))) =
      maximalIdealSheaf A := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine]
  have hnat : ((Spec.map (CommRingCat.ofHom (ε : R →+* A))).appTop).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp (ε : R →+* A) :=
    congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (ε : R →+* A))).symm
  simp only [maximalIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl,
    CategoryTheory.op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  rw [Ideal.map_map, hnat, ← Ideal.map_map]
  exact congrArg _ (IsLocalRing.map_ringEquiv_maximalIdeal ε)

/-! ### Transporting a closed point of a blowup along a flat preimmersion -/

/-- **A closed point of a blowup has, over it, a closed point of the blowup of the inverse image
of the centre along a flat preimmersion, with the same local ring.** Let `g : Y ⟶ X` be a flat
preimmersion, let `I` be an ideal sheaf on `X` and let `q` be a closed point of the blowup of `X`
in `I` lying over `g y₀`. Then the blowup of `Y` in the inverse image of `I` has a point `w` over
`y₀` which is closed and at which the local ring is the local ring at `q`. -/
public theorem exists_isClosed_ringEquiv_stalk_blowUp_comap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] [IsPreimmersion g] (I : X.IdealSheafData) (y₀ : Y) (q : blowUp I)
    (hq : (blowUpToBase I).base q = g.base y₀)
    (hqc : IsClosed ({q} : Set (blowUp I))) :
    ∃ w : blowUp (I.comap g),
      (blowUpToBase (I.comap g)).base w = y₀ ∧
      IsClosed ({w} : Set (blowUp (I.comap g))) ∧
      Nonempty ((blowUp (I.comap g)).presheaf.stalk w ≃+* (blowUp I).presheaf.stalk q) := by
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUpToBase_comap g I
  have : IsPreimmersion k :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Flat k := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq ‹Flat g›
  obtain ⟨w, hw1, hw2⟩ := Scheme.exists_preimage_of_isPullback hsq y₀ q hq.symm
  have : IsIso (k.stalkMap w) := isIso_stalkMap_of_flat_isPreimmersion k w
  refine ⟨w, hw1, ?_, ?_⟩
  · convert hqc.preimage k.continuous
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ hw2, fun h => k.isEmbedding.injective (h.trans hw2.symm)⟩
  · rw [← hw2]
    exact ⟨(asIso (k.stalkMap w)).commRingCatIsoToRingEquiv.symm⟩

/-- **A closed point of the blowup of a closed point of a scheme has the local ring of a closed
point of the blowup of the spectrum of a local ring in its maximal ideal.** Let `A` be a local
ring isomorphic to the local ring of `X` at a closed point `p`, and let `q` be a closed point of
the blowup of `X` in `p` lying over `p`. Then the blowup of `Spec A` in the maximal ideal of `A`
has a closed point whose local ring is the local ring at `q`. -/
public theorem exists_isClosed_ringEquiv_stalk_blowUp_maximalIdealSheaf (A : Type u) [CommRing A]
    [IsLocalRing A] {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X))
    (e : A ≃+* ↑(X.presheaf.stalk p))
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)))
    (hq : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))).base q = p)
    (hqc : IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))))) :
    ∃ x : blowUp (maximalIdealSheaf A), IsClosed ({x} : Set (blowUp (maximalIdealSheaf A))) ∧
      Nonempty ((blowUp (maximalIdealSheaf A)).presheaf.stalk x ≃+*
        (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))).presheaf.stalk q) := by
  have : Flat (X.fromSpecStalk p) := flat_fromSpecStalk X p
  have : IsLocalHom ((CommRingCat.ofHom (e.symm : ↑(X.presheaf.stalk p) →+* A)).hom) :=
    IsLocalHom.of_surjective _ e.symm.surjective
  have : IsIso (CommRingCat.ofHom (e.symm : ↑(X.presheaf.stalk p) →+* A)) :=
    e.symm.toCommRingCatIso.isIso_hom
  set g := Spec.map (CommRingCat.ofHom (e.symm : ↑(X.presheaf.stalk p) →+* A)) ≫
    X.fromSpecStalk p with hg
  have hcomap : (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)).comap g = maximalIdealSheaf A := by
    rw [hg, Scheme.IdealSheafData.comap_comp, comap_fromSpecStalk_vanishingIdeal_singleton X p hp,
      comap_maximalIdealSheaf_specMap_ringEquiv]
  have hy : g.base (closedPoint A) = p :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun t => (X.fromSpecStalk p).base t)
        AlgebraicGeometry.Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)
  rw [← hcomap]
  obtain ⟨w, -, hwc, hwe⟩ :=
    exists_isClosed_ringEquiv_stalk_blowUp_comap g
      (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))
      (closedPoint A) q (hq.trans hy.symm) hqc
  exact ⟨w, hwc, hwe⟩

/-! ### The property a rule carries, at a closed point of the blowup of a closed point -/

namespace RationalDoublePointSituation

/-- **`AlgebraicGeometry.PointBlowupStep.next_prop` at a closed point of the blowup of a closed
point of an arbitrary scheme.** Let `S` be a Situation [Stacks, Tag 0BGC] whose ring is
isomorphic to the local ring of a scheme `X` at a closed point `p`, and let `q` be a closed point
of the blowup of `X` in `p` lying over `p`. Then the local ring at `q` is again the ring of a
Situation 0BGC, granted `hratc` and the per-point data `hdata` at the corresponding closed
point of the blowup of `Spec(S.A)` in the maximal ideal. -/
public theorem isRationalDoublePointAt_blowUp_of_ringEquiv (S : RationalDoublePointSituation.{u})
    {X : Scheme.{u}} (p : X) (hp : IsClosed ({p} : Set X))
    (e : S.A ≃+* ↑(X.presheaf.stalk p))
    (hratc :
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (hdata : ∀ x : blowUp (maximalIdealSheaf S.A),
      IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) →
        letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
          S.isNormalDomain_stalk_blowUp x
        DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
          (∃ (K : Type u) (_ : Field K)
              (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x),
              Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
                ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f)) ∧
          (∃ y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x,
              Ideal.span (Set.range y) = IsLocalRing.maximalIdeal
                ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) ∧
          ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)))
    (hq : (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))).base q = p)
    (hqc : IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)))))
    (z : (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))).presheaf.stalk q) :
    IsRationalDoublePointAt (blowUp (Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds X))) q z := by
  obtain ⟨x, hxc, ⟨φ⟩⟩ :=
    exists_isClosed_ringEquiv_stalk_blowUp_maximalIdealSheaf S.A p hp e q hq hqc
  obtain ⟨hrat, ⟨K, _, f, hf⟩, ⟨y, hy⟩, hsing⟩ := hdata x hxc
  exact ⟨S.blowUpSituation hratc x hxc hrat K f hf y hy hsing, ⟨φ⟩⟩

end RationalDoublePointSituation

/-! ### The property a rule carries, at an arbitrary stage -/

namespace PointBlowupStage

/-- **`AlgebraicGeometry.PointBlowupStep.next_prop` at an arbitrary stage of a sequence of
blowups at closed points.** At every closed point of the blowup of a stage lying over the centre
of that stage, the local ring is again the ring of a Situation [Stacks, Tag 0BGC], granted
`hratc` and the per-point data `hdata`, both quantified over the situations whose ring is
isomorphic to the local ring at the centre. -/
public theorem isRationalDoublePointAt_blowUp (d : PointBlowupStage.{u} IsRationalDoublePointAt)
    (hratc : ∀ S : RationalDoublePointSituation.{u},
      S.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (hdata : ∀ S : RationalDoublePointSituation.{u},
      S.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      ∀ x : blowUp (maximalIdealSheaf S.A),
        IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) →
          letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
            S.isNormalDomain_stalk_blowUp x
          DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
            (∃ (K : Type u) (_ : Field K)
                (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x),
                Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f)) ∧
            (∃ y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x,
                Ideal.span (Set.range y) = IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) ∧
            ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
    (q : blowUp d.centre) (hq : (blowUpToBase d.centre).base q = d.point)
    (hqc : IsClosed ({q} : Set (blowUp d.centre)))
    (z : (blowUp d.centre).presheaf.stalk q) :
    IsRationalDoublePointAt (blowUp d.centre) q z := by
  obtain ⟨S, ⟨e⟩⟩ := d.prop
  exact RationalDoublePointSituation.isRationalDoublePointAt_blowUp_of_ringEquiv S d.point
    d.point_closed e (hratc S e) (hdata S e) q hq hqc z

/-- **All five conditions a rule imposes, at a point of a standard affine chart of the blowup of
an arbitrary stage**, granted `hratc` and `hdata`: the four conditions of
`AlgebraicGeometry.PointBlowupStage.exists_next_of_chart`, and the property
`AlgebraicGeometry.IsRationalDoublePointAt` at the point. -/
public theorem exists_next_of_chart_isRationalDoublePointAt
    (d : PointBlowupStage.{u} IsRationalDoublePointAt) (U : d.scheme.affineOpens)
    (hpU : d.point ∈ U.1) (a : d.centre.ideal U)
    (hgerm : d.scheme.presheaf.germ U.1 d.point hpU (a : Γ(d.scheme, U.1)) = d.elem)
    (w : Spec (.of (blowupChartRing d.centre U a))) (hmax : w.asIdeal.IsMaximal)
    (hcontract : w.asIdeal.comap (algebraMap (d.scheme.presheaf.obj (.op U.1))
        (blowupChartRing d.centre U a)) =
      (U.2.primeIdealOf ⟨d.point, hpU⟩).asIdeal)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp
      (algebraMap (d.scheme.presheaf.obj (.op U.1)) (blowupChartRing d.centre U a))))
    (hratc : ∀ S : RationalDoublePointSituation.{u},
      S.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) :=
        S.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))
    (hdata : ∀ S : RationalDoublePointSituation.{u},
      S.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      ∀ x : blowUp (maximalIdealSheaf S.A),
        IsClosed ({x} : Set (blowUp (maximalIdealSheaf S.A))) →
          letI : IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
            S.isNormalDomain_stalk_blowUp x
          DefinesRationalSingularity ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
            (∃ (K : Type u) (_ : Field K)
                (f : K →+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x),
                Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))).comp f)) ∧
            (∃ y : Fin 3 → (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x,
                Ideal.span (Set.range y) = IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) ∧
            ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    ∃ q : blowUp d.centre, ∃ hq : blowUpToBase d.centre q = d.point,
      IsClosed ({q} : Set (blowUp d.centre)) ∧
      IsIso ((blowUpToBase d.centre).residueFieldMap q) ∧
      Ideal.map ((blowUpToBase d.centre).stalkMap q).hom
          (hq.symm ▸ IsLocalRing.maximalIdeal (d.scheme.presheaf.stalk d.point)) =
        Ideal.span {((blowUpToBase d.centre).stalkMap q).hom (hq.symm ▸ d.elem)} ∧
      IsRationalDoublePointAt (blowUp d.centre) q
        (((blowUpToBase d.centre).stalkMap q).hom (hq.symm ▸ d.elem)) := by
  obtain ⟨q, hq, hqc, hres, hexc⟩ :=
    d.exists_next_of_chart U hpU a hgerm w hmax hcontract hsurj
  exact ⟨q, hq, hqc, hres, hexc, d.isRationalDoublePointAt_blowUp hratc hdata q hq hqc _⟩

end PointBlowupStage

/-! ### The termination half of Tag 0BGE against a rule supplied by chart data -/

namespace RationalDoublePointSituation

/-- **Situation [Stacks, Tag 0BGC]: a standard affine chart of the blowup containing a suitable
maximal prime cannot be found at every stage.** This is
`AlgebraicGeometry.RationalDoublePointSituation.not_forall_exists_next` with the per-stage
existence statement replaced by what
`AlgebraicGeometry.PointBlowupStage.exists_next_of_chart_isRationalDoublePointAt` consumes: an
affine open of the stage containing its centre on which the chosen element is a section of the
centre, a maximal prime of the coordinate ring of the standard chart there which contracts to the
centre and whose quotient is generated by the sections, and `hratc` with the per-point data
`hdata`. -/
public theorem not_forall_exists_chart (S : RationalDoublePointSituation.{u})
    [IsAdicComplete (IsLocalRing.maximalIdeal S.A) S.A]
    (hchart : ∀ d : PointBlowupStage.{u} IsRationalDoublePointAt,
      ∃ (U : d.scheme.affineOpens) (hpU : d.point ∈ U.1) (a : d.centre.ideal U),
        d.scheme.presheaf.germ U.1 d.point hpU (a : Γ(d.scheme, U.1)) = d.elem ∧
        ∃ w : Spec (.of (blowupChartRing d.centre U a)), w.asIdeal.IsMaximal ∧
          w.asIdeal.comap (algebraMap (d.scheme.presheaf.obj (.op U.1))
              (blowupChartRing d.centre U a)) =
            (U.2.primeIdealOf ⟨d.point, hpU⟩).asIdeal ∧
          Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp
            (algebraMap (d.scheme.presheaf.obj (.op U.1)) (blowupChartRing d.centre U a))))
    (hratc : ∀ d : PointBlowupStage.{u} IsRationalDoublePointAt,
      ∀ T : RationalDoublePointSituation.{u},
      T.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      letI : IsNormalDomain (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A) :=
        T.completion_normalDomain
      DefinesRationalSingularity (AdicCompletion (IsLocalRing.maximalIdeal T.A) T.A))
    (hdata : ∀ d : PointBlowupStage.{u} IsRationalDoublePointAt,
      ∀ T : RationalDoublePointSituation.{u},
      T.A ≃+* ↑(d.scheme.presheaf.stalk d.point) →
      ∀ x : blowUp (maximalIdealSheaf T.A),
        IsClosed ({x} : Set (blowUp (maximalIdealSheaf T.A))) →
          letI : IsNormalDomain ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x) :=
            T.isNormalDomain_stalk_blowUp x
          DefinesRationalSingularity ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x) ∧
            (∃ (K : Type u) (_ : Field K)
                (f : K →+* (blowUp (maximalIdealSheaf T.A)).presheaf.stalk x),
                Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x))).comp f)) ∧
            (∃ y : Fin 3 → (blowUp (maximalIdealSheaf T.A)).presheaf.stalk x,
                Ideal.span (Set.range y) = IsLocalRing.maximalIdeal
                  ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x)) ∧
            ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf T.A)).presheaf.stalk x))
    (x : S.base.presheaf.stalk S.closedPoint)
    (hx : x ∈ IsLocalRing.maximalIdeal (S.base.presheaf.stalk S.closedPoint)) : False := by
  refine S.not_forall_exists_next (fun d => ?_) x hx
  obtain ⟨U, hpU, a, hgerm, w, hmax, hcontract, hsurj⟩ := hchart d
  exact d.exists_next_of_chart_isRationalDoublePointAt U hpU a hgerm w hmax hcontract hsurj
    (hratc d) (hdata d)

end RationalDoublePointSituation

end AlgebraicGeometry

end
