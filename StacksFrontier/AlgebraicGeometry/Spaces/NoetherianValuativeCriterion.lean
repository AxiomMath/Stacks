module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.DiscreteValuationSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Sober.Generization

/-!
# Reaching a point in the closure of the image of a finite-type morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is of finite type,
with `Y` locally Noetherian, and let `y` be a point of `Y` in the closure of the image of the
points of `X`. Then `y` is reached by the closed point of the spectrum of a discrete valuation
ring: there are a discrete valuation ring `A` with fraction field `K`, a `K`-valued point of `X`
and an `A`-valued point of `Y` forming a commuting square, the closed point of `Spec A` mapping
to `y`. The `K`-valued point can be chosen of codimension zero, with image different from `y`
whenever `y` is in the closure of the images of the codimension-zero points of `X` not lying
over `y`, and its field to be the residue field of a point of an étale scheme chart of `X`
whenever its image differs from `y`.

## Main definitions

* `AlgebraicGeometry.Space.valuationObject` is the spectrum of the valuation ring, as an object
  of the big fppf site over `S`.
* `AlgebraicGeometry.Space.DiscreteValuationSpecialization` packages the valuation-ring diagram
  together with the codimension-zero condition and the residue-field refinement.

## Main results

* `AlgebraicGeometry.Space.exists_discreteValuationSpecialization`: **Stacks 0CMC**.
* `AlgebraicGeometry.Space.nonempty_discreteValuationSpecialization`: the same statement,
  packaged as a `DiscreteValuationSpecialization`.
* `AlgebraicGeometry.DiscreteValuationSpecialization.not_exists_residueFieldEquiv_id`: the
  residue-field refinement can fail when the field-valued point lies over the chosen point.
  The refutation of the unconditional residue-field clause at the hypotheses of Stacks 0CMC is
  `AlgebraicGeometry.Space.not_forall_exists_discreteValuationSpecialization_residueField`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeCriterionCounterexample`.

## Implementation notes

The statement is reduced to the scheme case, Stacks 0CM2, in two steps. First the point `y` is
lifted to a point of an affine open of a locally Noetherian étale scheme chart `V` of `Y`, which
exists because local Noetherianity of `Y` is the étale-local property of Stacks 03E6 and an open
subscheme of a locally Noetherian scheme is locally Noetherian. Second the fibre product of that
chart with `f` is quasi-compact — this is where finite type is used — so it admits an affine
étale surjective chart `W` by Stacks 03H6, and the resulting morphism of schemes `W ⟶ V` is
affine, quasi-compact and locally of finite type. The point of `V` is still in the closure of
the image of `W`, because the chart of `Y` is open on points by Stacks 03IR and points of a
fibre product of algebraic spaces can be prescribed on both factors by Stacks 03H4.

Stacks 0CM2 gives a discrete valuation ring for the morphism of schemes `W ⟶ V`, but says
nothing about the size of its spectrum, whereas the diagram asked for here lives in the big
fppf site. The valuation ring is therefore replaced by one whose spectrum is an object of that
site: when the generic point already maps to `y` the local ring of the affine line over the
residue field at the origin serves, and otherwise the fraction field is the residue field at the
generic point, whose spectrum is in the site, and the valuation ring is a subring of it.

Codimension zero of the resulting point of `X` is read off the generic point of `W` through
Stacks 0BAQ: the chart `W ⟶ X` is étale, and the point of `W` is a generic point of an
irreducible component.

When `y` is in the closure of the images of the codimension-zero points of `X` not lying over
`y`, the scheme-level diagram is started from a point of `W` over one of them, as in the proof of
Stacks 0CM2. By Stacks 0BAQ the points of `W` over codimension-zero points of `X` are generic
points of irreducible components of the Noetherian scheme `W`, so there are finitely many, and
the chosen point of `V` is a specialization of the image of one of them. The generic point
produced by `AlgebraicGeometry.exists_discreteValuationSpecialization_genericPoint_specializes`
is then that point itself, which does not lie over `y`.

## References

* [Stacks Project, Tag 0CMC](https://stacks.math.columbia.edu/tag/0CMC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A point in the closure of the image of a map lifts along an open map: if `g` is open and
every pair of points with the same image lifts to the fibre product, a point of the source of
`g` over a point in the closure of the image of `f` lies in the closure of the image of the
first projection restricted to a preimage. -/
private theorem mem_closure_image_of_isOpenMap {α β γ δ : Type*} [TopologicalSpace α]
    [TopologicalSpace γ] (g : α → γ) (f : β → γ) (p : δ → α) (q : δ → β) (hopen : IsOpenMap g)
    (hlift : ∀ a b, g a = f b → ∃ z, p z = a ∧ q z = b) {s : Set β} {y : γ}
    (hy : y ∈ closure (f '' s)) {v : α} (hv : g v = y) : v ∈ closure (p '' (q ⁻¹' s)) := by
  rw [mem_closure_iff] at hy ⊢
  intro U hU hvU
  obtain ⟨z, hzImage, hzTarget⟩ := hy (g '' U) (hopen U hU) ⟨v, hvU, hv⟩
  obtain ⟨a, haU, hga⟩ := hzImage
  obtain ⟨b, hbS, hfb⟩ := hzTarget
  obtain ⟨w, hpw, hqw⟩ := hlift a b (hga.trans hfb.symm)
  exact ⟨p w, hpw ▸ haU, ⟨w, show q w ∈ s from hqw ▸ hbS, rfl⟩⟩

/-- The spectrum of a ring with a morphism to the base, as an object of the big fppf site
over `S`. -/
noncomputable abbrev valuationObject (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (A : Type u) [CommRing A] (hA : B.Contains (Spec (.of A)))
    (s : Spec (.of A) ⟶ S) : BigFppfOver B S hS :=
  Over.mk (⟨s⟩ : B.obj hA ⟶ B.obj hS)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A discrete valuation ring reaching a point of a scheme can be chosen with its spectrum and
the spectrum of its fraction field in the big fppf site: if the generic point already maps to
the point, the local ring of the affine line over the residue field at the origin does the job,
and otherwise the fraction field is that residue field and the valuation ring a subring of
it. -/
private theorem exists_contained_discreteValuationSpecialization {W V : Scheme.{u}}
    (hW : B.Contains W) (f : W ⟶ V) (y : V)
    (d : _root_.AlgebraicGeometry.DiscreteValuationSpecialization f y) :
    ∃ d' : _root_.AlgebraicGeometry.DiscreteValuationSpecialization f y,
      B.Contains (Spec (.of d'.fractionField)) ∧
        B.Contains (Spec (.of d'.valuationRing)) ∧ d'.genericPoint = d.genericPoint := by
  classical
  have hk := B.residueField_spec_contains hW d.genericPoint
  by_cases heq : f.base d.genericPoint = y
  · let k := W.residueField d.genericPoint
    let p : Ideal (Polynomial k) := Ideal.span {Polynomial.X}
    have hp : p ≠ ⊥ := by simp [p]
    have : p.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
    let A := Localization.AtPrime p
    let K := FractionRing A
    have : IsDiscreteValuationRing A :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) hp A
    let r : k →+* A := (algebraMap (Polynomial k) A).comp Polynomial.C
    let i : A →+* K := algebraMap A K
    let a : Spec (.of A) ⟶ Spec (.of k) := Scheme.Spec.map (CommRingCat.ofHom r).op
    let b : Spec (.of K) ⟶ Spec (.of k) :=
      Scheme.Spec.map (CommRingCat.ofHom (i.comp r)).op
    have hcomm : Scheme.Spec.map (CommRingCat.ofHom i).op ≫ a = b := by
      simp [a, b]
    have hPoly : B.Contains (Spec (.of (Polynomial k))) :=
      Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k
        (Polynomial k) hk
    have hA : B.Contains (Spec (.of A)) :=
      Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        p.primeCompl A hPoly
    have hK : B.Contains (Spec (.of K)) :=
      Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
        (nonZeroDivisors A) K hA
    refine ⟨{ valuationRing := A
              fractionField := K
              genericPoint := d.genericPoint
              component := d.component
              component_mem := d.component_mem
              isGenericPoint := d.isGenericPoint
              toSource := b ≫ W.fromSpecResidueField d.genericPoint
              toTarget := a ≫ W.fromSpecResidueField d.genericPoint ≫ f
              maps_genericPoint := by
                change W.fromSpecResidueField d.genericPoint (b _) = d.genericPoint
                exact Scheme.fromSpecResidueField_apply _ _
              maps_closedPoint := by
                change f (W.fromSpecResidueField d.genericPoint (a _)) = y
                rw [Scheme.fromSpecResidueField_apply]
                exact heq
              commutes := by
                simpa only [Category.assoc] using
                  congrArg (fun t ↦ t ≫ W.fromSpecResidueField d.genericPoint ≫ f) hcomm
              residueFieldEquiv := fun h ↦ (h heq).elim }, hK, hA, rfl⟩
  · obtain ⟨e, -⟩ := d.residueFieldEquiv heq
    have hK : B.Contains (Spec (.of d.fractionField)) := by
      change (Spec (.of d.fractionField)).size < B.cutoff
      change (Spec (.of (W.residueField d.genericPoint))).size < B.cutoff at hk
      rw [Scheme.size_Spec] at hk ⊢
      simpa only [Cardinal.mk_congr e.toEquiv] using hk
    exact ⟨d, hK, Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hK ((Cardinal.mk_le_of_injective (IsFractionRing.injective d.valuationRing
        d.fractionField)).trans (le_max_right _ _)), rfl⟩

/-- A discrete valuation ring reaching a point of an algebraic space over `S`: the spectrum of a
discrete valuation ring in the chosen site, mapping to the target with its closed point over the
chosen point, together with a field-valued point of the source over the fraction field forming a
commuting square, of codimension zero, not over the chosen point when the chosen point is in the
closure of the images of the codimension-zero points not over it, and, when its image differs
from the chosen point, with its field identified with a residue field on an étale scheme chart
of the source. -/
structure DiscreteValuationSpecialization {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y) where
  /-- The discrete valuation ring in the diagram. -/
  valuationRing : Type u
  [commRing : CommRing valuationRing]
  [isDomain : IsDomain valuationRing]
  [isDVR : IsDiscreteValuationRing valuationRing]
  /-- The field-valued point of the source, over the fraction field of the valuation ring. -/
  generic : FieldValuedPoint B S hS X
  [algebra : Algebra valuationRing generic.carrier]
  [isFractionRing : IsFractionRing valuationRing generic.carrier]
  /-- The spectrum of the valuation ring lies in the chosen site. -/
  valuation_contained : B.Contains (Spec (.of valuationRing))
  /-- Its structure morphism to the base. -/
  toBase : Spec (.of valuationRing) ⟶ S
  /-- The morphism of the site from the field-valued point to the valuation spectrum. -/
  genericToValuation : generic.siteObject ⟶
    valuationObject B S hS valuationRing valuation_contained toBase
  genericToValuation_spec : genericToValuation.left.1 =
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap valuationRing generic.carrier)).op
  /-- The valuation-ring-valued point of the target. -/
  toTarget : yoneda.obj (valuationObject B S hS valuationRing valuation_contained toBase) ⟶ Y
  commutes : yoneda.map genericToValuation ≫ toTarget = yonedaEquiv.symm generic.value ≫ f
  maps_closedPoint :
    pointsMap B S hS
        (yoneda.obj (valuationObject B S hS valuationRing valuation_contained toBase)) toTarget
        ((schemePointRepresentative B S hS
            (valuationObject B S hS valuationRing valuation_contained toBase)
            (⟨IsLocalRing.maximalIdeal valuationRing, inferInstance⟩ :
              PrimeSpectrum valuationRing)).class B S hS
          (yoneda.obj (valuationObject B S hS valuationRing valuation_contained toBase))) = y
  codimension_zero : localRingDimension B S hS (generic.class B S hS X) = 0
  residueFieldDescription :
    pointsMap B S hS X f (generic.class B S hS X) ≠ y →
      ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
        (u : (BigFppfOver.toScheme B S hS).obj U)
        (e : generic.carrier ≃+* ((BigFppfOver.toScheme B S hS).obj U).residueField u)
        (t : generic.siteObject ⟶ U),
        IsEtale B S hS a ∧
          t.left.1 = Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
              ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u ∧
            a.app (Opposite.op generic.siteObject) t = generic.value
  /-- The image of the field-valued point differs from the chosen point as soon as the chosen
  point is in the closure of the images of the codimension-zero points not lying over it. -/
  maps_ne_of_mem_closure :
    y ∈ closure (pointsMap B S hS X f ''
        {x' | localRingDimension B S hS x' = 0 ∧ pointsMap B S hS X f x' ≠ y}) →
      pointsMap B S hS X f (generic.class B S hS X) ≠ y

namespace DiscreteValuationSpecialization

attribute [instance] commRing isDomain isDVR algebra isFractionRing

end DiscreteValuationSpecialization

/-- A point in the closure of the image of a finite-type morphism of algebraic spaces over `S`
with locally Noetherian target is reached by a discrete valuation ring, through a
codimension-zero field-valued point of the source. -/
theorem nonempty_discreteValuationSpecialization {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hFinite : IsFiniteType B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (y : points B S hS Y) (hy : y ∈ closure (Set.range (pointsMap B S hS X f))) :
    Nonempty (DiscreteValuationSpecialization B S hS f hX hY y) := by
  classical
  obtain ⟨V, a, haSurj, haEtale, hVNoeth⟩ := hNoeth
  obtain ⟨v, hv⟩ := (surjective_iff_surjective_pointsMap B S hS Y hY V a).mp haSurj y
  -- An affine open of the chart around the chosen point.
  obtain ⟨U, hUaff, hvU, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := pointsToScheme B S hS V v) (by simp)
  let Usite : B.Schemes :=
    ⟨(U : Scheme), (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj V) U).trans_lt
      V.left.2⟩
  let i : Usite ⟶ V.left := ObjectProperty.homMk U.ι
  let Vaff : BigFppfOver B S hS := Over.mk (i ≫ V.hom)
  let j : Vaff ⟶ V := Over.homMk i
  let aaff : yoneda.obj Vaff ⟶ Y := yoneda.map j ≫ a
  have hVaff := isAlgebraicSpace_yoneda B S hS Vaff
  have hIsoJ : Etale ((BigFppfOver.toScheme B S hS).map j) := inferInstanceAs (Etale U.ι)
  have hEtaleAaff : IsEtale B S hS aaff := isEtale_comp B S hS
    ((isEtale_iff_presheaf_of_yoneda B S hS _).mpr
      ((presheaf_yoneda_map_etale_iff B S hS j).2 hIsoJ))
    ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr haEtale)
  -- The chosen point, seen on the affine open.
  let vAff := (schemePointsHomeomorph B S hS Vaff).symm
    (⟨pointsToScheme B S hS V v, hvU⟩ : (U : Scheme))
  have hvAffUnderlying : pointsToScheme B S hS Vaff vAff =
      (⟨pointsToScheme B S hS V v, hvU⟩ : (U : Scheme)) :=
    (schemePointsHomeomorph B S hS Vaff).apply_symm_apply _
  have hvAff : pointsMap B S hS (yoneda.obj Vaff) (yoneda.map j) vAff = v := by
    refine injective_pointsToScheme B S hS V ?_
    rw [pointsToScheme_pointsMap, hvAffUnderlying]
    rfl
  have hvAffY : pointsMap B S hS (yoneda.obj Vaff) aaff vAff = y := by
    rwa [show aaff = yoneda.map j ≫ a from rfl, pointsMap_comp_apply, hvAff]
  -- The fibre product of the chart with the morphism.
  let Xₛ : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Yₛ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fₛ : Xₛ ⟶ Yₛ := ObjectProperty.homMk f
  let Vaffₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj Vaff, hVaff⟩
  let aaffₛ : Vaffₛ ⟶ Yₛ := ObjectProperty.homMk aaff
  let Paff := AlgebraicSpaces.fiberProduct B S hS aaffₛ fₛ
  let paff : Paff ⟶ Vaffₛ := ObjectProperty.homMk (pullback.fst aaff f)
  let qaff : Paff ⟶ Xₛ := ObjectProperty.homMk (pullback.snd aaff f)
  have hsqaff : IsPullback paff qaff aaffₛ fₛ :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS aaffₛ fₛ
  have hclosure (s : Set (points B S hS X)) (hs : y ∈ closure (pointsMap B S hS X f '' s)) :
      vAff ∈ closure (pointsMap B S hS Paff.1 paff.hom ''
        (pointsMap B S hS Paff.1 qaff.hom ⁻¹' s)) :=
    mem_closure_image_of_isOpenMap
      (pointsMap B S hS (yoneda.obj Vaff) aaff) (pointsMap B S hS X f)
      (pointsMap B S hS Paff.1 paff.hom) (pointsMap B S hS Paff.1 qaff.hom)
      (isOpenMap_pointsMap_of_isEtale B S hS aaff hVaff hY hEtaleAaff)
      (exists_point_of_isPullback B S hS hsqaff) hs hvAffY
  have hpAffClosure : vAff ∈ closure (Set.range (pointsMap B S hS Paff.1 paff.hom)) := by
    simpa [Set.range] using hclosure Set.univ (by simpa [Set.range] using hy)
  -- A quasi-compact affine étale chart of the fibre product.
  have hid (P : MorphismProperty Scheme.{u}) (hP : ∀ ⦃X Y⦄ (g : X ⟶ Y), IsIso g → P g)
      (Z : BigFppfOver B S hS) := AlgebraicGeometry.presheaf_id_of_iso B S hS
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
    (fun {_ _} k hk ↦ hP _ (inferInstanceAs (IsIso ((BigFppfOver.toScheme B S hS).map k)))) Z
  have hVaffqc : IsQuasiCompactSpace B S hS (yoneda.obj Vaff) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Vaff) := hUaff
    refine ⟨Vaff, 𝟙 (yoneda.obj Vaff), inferInstance,
      hid @Surjective (fun _ _ _ _ ↦ inferInstance) Vaff, ?_⟩
    intro U' φ hφ
    simpa using hφ
  have hPaffqc : IsQuasiCompactSpace B S hS Paff.1 :=
    hFinite.2 (yoneda.obj Vaff) hVaff hVaffqc aaff
  obtain ⟨W, b, hWaff, hbSurj, hbEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Paff.1
      Paff.property).mp hPaffqc
  have hW := isAlgebraicSpace_yoneda B S hS W
  let g : yoneda.obj W ⟶ yoneda.obj Vaff := b ≫ paff.hom
  have hbSurjPoints : Function.Surjective (pointsMap B S hS (yoneda.obj W) b) :=
    (surjective_iff_surjective_pointsMap B S hS Paff.1 Paff.property W b).mp hbSurj
  have hrange : Set.range (pointsMap B S hS (yoneda.obj W) g) =
      Set.range (pointsMap B S hS Paff.1 paff.hom) := by
    rw [show (pointsMap B S hS (yoneda.obj W) g) =
      pointsMap B S hS Paff.1 paff.hom ∘ pointsMap B S hS (yoneda.obj W) b from
      pointsMap_comp B S hS (yoneda.obj W) b paff.hom, hbSurjPoints.range_comp]
  have hvWClosure : vAff ∈ closure (Set.range (pointsMap B S hS (yoneda.obj W) g)) := by
    rwa [hrange]
  -- The morphism of schemes underlying the two charts.
  let e : W ⟶ Vaff := yoneda.preimage g
  have he : yoneda.map e = g := yoneda.map_preimage g
  let schemeMap : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B S hS).obj Vaff :=
    (BigFppfOver.toScheme B S hS).map e
  let yV : (BigFppfOver.toScheme B S hS).obj Vaff := pointsToScheme B S hS Vaff vAff
  have hschemeMap (z : points B S hS (yoneda.obj W)) :
      schemeMap.base (pointsToScheme B S hS W z) =
        pointsToScheme B S hS Vaff (pointsMap B S hS (yoneda.obj W) g z) := by
    rw [← he, pointsToScheme_pointsMap]
  have hyScheme : yV ∈ closure (Set.range schemeMap.base) := by
    refine map_mem_closure (schemePointsHomeomorph B S hS Vaff).continuous hvWClosure ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hschemeMap z⟩
  -- The morphism of schemes is affine, quasi-compact and locally of finite type.
  let cX : yoneda.obj W ⟶ X := b ≫ qaff.hom
  have hpull : cX ≫ f = yoneda.map e ≫ aaff := by
    rw [he]
    change (b ≫ qaff.hom) ≫ f = (b ≫ paff.hom) ≫ aaff
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun t ↦ b ≫ t) pullback.condition.symm
  have hqaffEtale : IsEtale B S hS qaff.hom :=
    isEtale_of_isPullback B S hS paff qaff aaffₛ fₛ hsqaff hEtaleAaff
  have hcXEtale : IsEtale B S hS cX := isEtale_comp B S hS hbEtale hqaffEtale
  have hidEtale := hid @Etale (fun _ _ _ _ ↦ inferInstance)
  have hbEtaleChart : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf b := by
    simpa using hbEtale W (𝟙 (yoneda.obj W)) (hidEtale W)
  have hLocScheme : LocallyOfFiniteType schemeMap :=
    hFinite.1 W Vaff cX aaff e (hqaffEtale W b hbEtaleChart)
      (by simpa using hEtaleAaff Vaff (𝟙 _) (hidEtale Vaff)) hpull.symm
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Vaff) := hUaff
  have : IsAffineHom schemeMap := inferInstance
  have : QuasiCompact schemeMap := inferInstance
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVNoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Vaff) :=
    isLocallyNoetherian_of_isOpenImmersion U.ι
  -- The scheme-level discrete valuation ring. When the chosen point is in the closure of the
  -- images of the codimension-zero points not over it, its generic point is chosen above one of
  -- them: such points of the chart are generic points of the Noetherian scheme `W`, finitely
  -- many, so one of their images specializes to the chosen point of the chart.
  let s : Set (points B S hS X) :=
    {x' | localRingDimension B S hS x' = 0 ∧ pointsMap B S hS X f x' ≠ y}
  have hdvr : ∃ d : _root_.AlgebraicGeometry.DiscreteValuationSpecialization schemeMap yV,
      y ∈ closure (pointsMap B S hS X f '' s) →
        ∃ z : points B S hS (yoneda.obj W), pointsMap B S hS (yoneda.obj W) cX z ∈ s ∧
          pointsToScheme B S hS W z = d.genericPoint := by
    by_cases H : y ∈ closure (pointsMap B S hS X f '' s)
    · have hP := hclosure s H
      have hsub : pointsMap B S hS Paff.1 paff.hom '' (pointsMap B S hS Paff.1 qaff.hom ⁻¹' s) ⊆
          pointsMap B S hS (yoneda.obj W) g '' (pointsMap B S hS (yoneda.obj W) cX ⁻¹' s) := by
        rintro _ ⟨π, hπ, rfl⟩
        obtain ⟨z, rfl⟩ := hbSurjPoints π
        exact ⟨z, by rwa [Set.mem_preimage, pointsMap_comp_apply],
          pointsMap_comp_apply B S hS b paff.hom z⟩
      let T : Set ((BigFppfOver.toScheme B S hS).obj W) :=
        pointsToScheme B S hS W '' (pointsMap B S hS (yoneda.obj W) cX ⁻¹' s)
      have hT : T ⊆ genericPoints ((BigFppfOver.toScheme B S hS).obj W) := by
        rintro _ ⟨z, hz, rfl⟩
        exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).mp hz.1 W cX
          _ hcXEtale (chartPoint_pointsToScheme B S hS W cX z)
      have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
        LocallyOfFiniteType.isLocallyNoetherian schemeMap
      have : IsNoetherian ((BigFppfOver.toScheme B S hS).obj W) := {}
      have hTfin : T.Finite :=
        (genericPoints.finite finite_irreducibleComponents_of_isNoetherian).subset hT
      have hyT : yV ∈ closure (schemeMap.base '' T) := by
        refine map_mem_closure (schemePointsHomeomorph B S hS Vaff).continuous
          (closure_mono hsub hP) ?_
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨_, ⟨z, hz, rfl⟩, hschemeMap z⟩
      have hmem : yV ∈ ⋃ w ∈ T, closure {schemeMap.base w} :=
        closure_minimal (by
            rintro _ ⟨w, hw, rfl⟩
            exact Set.mem_biUnion hw (subset_closure rfl))
          (hTfin.isClosed_biUnion fun _ _ ↦ isClosed_closure) hyT
      obtain ⟨w, hwT, hwy⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hz, rfl⟩ := hwT
      obtain ⟨d, hd⟩ :=
        AlgebraicGeometry.exists_discreteValuationSpecialization_genericPoint_specializes
          schemeMap (specializes_iff_mem_closure.mpr hwy)
      exact ⟨d, fun _ ↦ ⟨z, hz,
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints (hT ⟨z, hz, rfl⟩) _ hd).symm⟩⟩
    · obtain ⟨d⟩ :=
        AlgebraicGeometry.nonempty_discreteValuationSpecialization schemeMap yV hyScheme
      exact ⟨d, fun h ↦ (H h).elim⟩
  obtain ⟨dvr₀, hdvr₀⟩ := hdvr
  -- The scheme-level discrete valuation ring, shrunk into the site.
  obtain ⟨dvr, hK, hA, hgen⟩ :=
    exists_contained_discreteValuationSpecialization B W.left.property schemeMap yV dvr₀
  -- The generic point of the component selected in the chart has codimension zero.
  set η := dvr.genericPoint
  have hηgeneric : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj W) := by
    change closure ({η} : Set ((BigFppfOver.toScheme B S hS).obj W)) ∈
      irreducibleComponents ((BigFppfOver.toScheme B S hS).obj W)
    rw [dvr.isGenericPoint.def]
    exact dvr.component_mem
  set ηrep := schemePointRepresentative B S hS W η
  set x := pointsMap B S hS (yoneda.obj W) cX (ηrep.class B S hS (yoneda.obj W)) with hxdef
  have hηpt : pointsToScheme B S hS W (ηrep.class B S hS (yoneda.obj W)) = η :=
    schemePointRepresentative_point B S hS W η
  have hchartPoint : ChartPoint B S hS W cX η x := by
    have h := chartPoint_pointsToScheme B S hS W cX (ηrep.class B S hS (yoneda.obj W))
    rwa [hηpt] at h
  have hcodim : localRingDimension B S hS x = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX x).2
      ⟨W, cX, η, hcXEtale, hchartPoint, hηgeneric⟩
  -- The valuation spectrum as an object of the site, and the field-valued points.
  let toA : Spec (.of dvr.valuationRing) ⟶ S := dvr.toTarget ≫ B.inclusion.map Vaff.hom
  let Aobj := valuationObject B S hS dvr.valuationRing hA toA
  let Kbase : Spec (.of dvr.fractionField) ⟶ S := dvr.toSource ≫ B.inclusion.map W.hom
  let Ksite : BigFppfOver B S hS := Over.mk (⟨Kbase⟩ : B.obj hK ⟶ B.obj hS)
  let KtoWover : Ksite ⟶ W := Over.homMk (⟨dvr.toSource⟩ : B.obj hK ⟶ W.left) (by rfl)
  let genericW : FieldValuedPoint B S hS (yoneda.obj W) :=
    { carrier := dvr.fractionField
      contained := hK
      toBase := Kbase
      value := yonedaEquiv (yoneda.map KtoWover) }
  let generic : FieldValuedPoint B S hS X :=
    { carrier := dvr.fractionField
      contained := hK
      toBase := Kbase
      value := cX.app (Opposite.op Ksite) (yonedaEquiv (yoneda.map KtoWover)) }
  let AtoVaff : Aobj ⟶ Vaff := Over.homMk (⟨dvr.toTarget⟩ : B.obj hA ⟶ Vaff.left) (by rfl)
  let toTarget : yoneda.obj Aobj ⟶ Y := yoneda.map AtoVaff ≫ aaff
  let genericToValuation : generic.siteObject ⟶ Aobj :=
    Over.homMk (⟨Scheme.Spec.map
        (CommRingCat.ofHom (algebraMap dvr.valuationRing dvr.fractionField)).op⟩ :
      B.obj hK ⟶ B.obj hA) (by
      apply ObjectProperty.hom_ext
      change Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap dvr.valuationRing dvr.fractionField)).op ≫
            dvr.toTarget ≫ Vaff.hom.1 = dvr.toSource ≫ W.hom.1
      rw [← Category.assoc, dvr.commutes, Category.assoc]
      exact dvr.toSource ≫= congrArg (fun t ↦ t.hom) (Over.w e))
  have hgenericClass : generic.class B S hS X = x := by
    have hw : genericW.class B S hS (yoneda.obj W) = ηrep.class B S hS (yoneda.obj W) := by
      refine injective_pointsToScheme B S hS W ?_
      rw [hηpt]
      change dvr.toSource.base (IsLocalRing.closedPoint dvr.fractionField) = η
      rw [show IsLocalRing.closedPoint dvr.fractionField =
        (⟨⊥, inferInstance⟩ : PrimeSpectrum dvr.fractionField) from Subsingleton.elim _ _]
      exact dvr.maps_genericPoint
    change (FieldValuedPoint.map B S hS (yoneda.obj W) cX genericW).class B S hS X = x
    rw [← pointsMap_class, hw]
  refine ⟨{ valuationRing := dvr.valuationRing
            generic := generic
            algebra := dvr.algebra
            isFractionRing := dvr.isFractionRing
            valuation_contained := hA
            toBase := toA
            genericToValuation := genericToValuation
            genericToValuation_spec := rfl
            toTarget := toTarget
            commutes := ?_
            maps_closedPoint := ?_
            codimension_zero := by rwa [hgenericClass]
            residueFieldDescription := ?_
            maps_ne_of_mem_closure := ?_ }⟩
  · have hdiag : KtoWover ≫ e = genericToValuation ≫ AtoVaff := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change dvr.toSource ≫ schemeMap =
        Scheme.Spec.map
          (CommRingCat.ofHom (algebraMap dvr.valuationRing dvr.fractionField)).op ≫ dvr.toTarget
      exact dvr.commutes.symm
    have hvalue : yonedaEquiv.symm generic.value = yoneda.map KtoWover ≫ cX := by
      change yonedaEquiv.symm (cX.app (Opposite.op Ksite) (yonedaEquiv (yoneda.map KtoWover))) =
        yoneda.map KtoWover ≫ cX
      rw [← yonedaEquiv_symm_naturality_right, Equiv.symm_apply_apply]
    calc yoneda.map genericToValuation ≫ toTarget
        = yoneda.map (genericToValuation ≫ AtoVaff) ≫ aaff := by
          rw [yoneda.map_comp, Category.assoc]
      _ = yoneda.map (KtoWover ≫ e) ≫ aaff := by rw [← hdiag]
      _ = yoneda.map KtoWover ≫ cX ≫ f := by
          rw [yoneda.map_comp, Category.assoc, ← hpull]
      _ = yonedaEquiv.symm generic.value ≫ f := by
          rw [hvalue]; exact (Category.assoc _ _ _).symm
  · have hmapClosed : pointsMap B S hS (yoneda.obj Aobj) (yoneda.map AtoVaff)
        ((schemePointRepresentative B S hS Aobj
            (⟨IsLocalRing.maximalIdeal dvr.valuationRing, inferInstance⟩ :
              PrimeSpectrum dvr.valuationRing)).class B S hS (yoneda.obj Aobj)) = vAff := by
      refine injective_pointsToScheme B S hS Vaff ?_
      rw [pointsToScheme_pointsMap,
        show pointsToScheme B S hS Aobj
            ((schemePointRepresentative B S hS Aobj
              (⟨IsLocalRing.maximalIdeal dvr.valuationRing, inferInstance⟩ :
                PrimeSpectrum dvr.valuationRing)).class B S hS (yoneda.obj Aobj)) =
          (⟨IsLocalRing.maximalIdeal dvr.valuationRing, inferInstance⟩ :
            PrimeSpectrum dvr.valuationRing) from
        schemePointRepresentative_point B S hS Aobj _]
      exact dvr.maps_closedPoint
    change pointsMap B S hS (yoneda.obj Aobj) (yoneda.map AtoVaff ≫ aaff) _ = y
    rwa [pointsMap_comp_apply, hmapClosed]
  · intro hneq
    have hEq : schemeMap.base η ≠ yV := by
      intro heq
      refine hneq ?_
      rw [hgenericClass]
      have hmapη : pointsMap B S hS (yoneda.obj W) (yoneda.map e)
          (ηrep.class B S hS (yoneda.obj W)) = vAff := by
        refine injective_pointsToScheme B S hS Vaff ?_
        rwa [pointsToScheme_pointsMap, hηpt]
      change pointsMap B S hS X f (pointsMap B S hS (yoneda.obj W) cX
        (ηrep.class B S hS (yoneda.obj W))) = y
      rwa [← pointsMap_comp_apply, hpull, pointsMap_comp_apply, hmapη]
    obtain ⟨eK, heK⟩ := dvr.residueFieldEquiv hEq
    exact ⟨W, cX, η, eK, KtoWover, hcXEtale, heK, rfl⟩
  · intro H
    obtain ⟨z, hz, hzη⟩ := hdvr₀ H
    have hz' : ηrep.class B S hS (yoneda.obj W) = z := by
      refine injective_pointsToScheme B S hS W ?_
      rw [hηpt, hzη, hgen]
    rw [hgenericClass, hxdef, hz']
    exact hz.2

/-- **Stacks 0CMC.** Let `f : X ⟶ Y` be a morphism of finite type of algebraic spaces over `S`,
with `Y` locally Noetherian, and let `y` be a point of `Y` in the closure of the image of the
points of `X`. Then there are a discrete valuation ring `A`, a field-valued point of `X` over its
fraction field `K`, a morphism `Spec K ⟶ Spec A` over `S` given by the inclusion `A → K`, and an
`A`-valued point of `Y` forming a commutative square with `f`, the closed point of `Spec A`
mapping to `y`. Moreover the point `x` of `X` given by `Spec K ⟶ X` is a codimension zero point;
it satisfies `f x ≠ y` as soon as `y` is in the closure of the set of `f x'` for the codimension
zero points `x'` of `X` with `f x' ≠ y`; and, when `f x ≠ y`, the morphism `Spec K ⟶ X` factors
as `Spec K ≅ Spec κ(u) ⟶ U ⟶ X` for a point `u` of a scheme `U` étale over `X`, so that `K` is
the residue field of `u`. The condition for `f x ≠ y` is also necessary: the square makes `y` a
specialization of `f x`, so an `x` with `f x ≠ y` is itself such an `x'`.

The residue-field clause is stated under `f x ≠ y` because the source's unconditional clause is
false. This is
`AlgebraicGeometry.Space.not_forall_exists_discreteValuationSpecialization_residueField`
(in `StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeCriterionCounterexample`), whose
statement is the conclusion of this theorem with the guard `f x ≠ y →` removed from the
residue-field clause (the clause guaranteeing `f x ≠ y` is left out, which only strengthens the
refutation):
```
¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X ⟶ Y), IsAlgebraicSpace B S hS X →
    IsAlgebraicSpace B S hS Y → IsFiniteType B S hS f →
    HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
    ∀ y : points B S hS Y, y ∈ closure (Set.range (pointsMap B S hS X f)) →
      ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
        (K : FieldValuedPoint B S hS X) (_ : Algebra A K.carrier)
        (_ : IsFractionRing A K.carrier) (A_contained : B.Contains (Spec (.of A)))
        (s : Spec (.of A) ⟶ S) (j : K.siteObject ⟶ valuationObject B S hS A A_contained s)
        (g : yoneda.obj (valuationObject B S hS A A_contained s) ⟶ Y),
        j.left.1 = Scheme.Spec.map (CommRingCat.ofHom (algebraMap A K.carrier)).op ∧
        yoneda.map j ≫ g = yonedaEquiv.symm K.value ≫ f ∧
        pointsMap B S hS (yoneda.obj (valuationObject B S hS A A_contained s)) g
            ((schemePointRepresentative B S hS (valuationObject B S hS A A_contained s)
                (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)).class B S hS
              (yoneda.obj (valuationObject B S hS A A_contained s))) = y ∧
        localRingDimension B S hS (K.class B S hS X) = 0 ∧
        ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
          (u : (BigFppfOver.toScheme B S hS).obj U)
          (e : K.carrier ≃+* ((BigFppfOver.toScheme B S hS).obj U).residueField u)
          (t : K.siteObject ⟶ U),
          IsEtale B S hS a ∧
            t.left.1 = Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
                ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u ∧
              a.app (Opposite.op K.siteObject) t = K.value
```
The witness is the identity of `X = Y = S = Spec k` for `k` the algebraic closure of `ℚ`: every
residue field of a scheme étale over `Spec k` is algebraically closed, being a separable
extension of `k`, while the fraction field of a discrete valuation ring is not, since a
uniformizer has no square root in it. The same proof gives the stronger
`AlgebraicGeometry.Space.not_forall_exists_etale_residueFieldEquiv`, in which `K` is only asked
to be abstractly isomorphic to such a residue field. -/
@[stacks 0CMC]
theorem exists_discreteValuationSpecialization {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (X_isAlgebraicSpace : IsAlgebraicSpace B S hS X)
    (Y_isAlgebraicSpace : IsAlgebraicSpace B S hS Y) (f_finiteType : IsFiniteType B S hS f)
    (Y_locallyNoetherian :
      HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (y : points B S hS Y) (y_mem_closure : y ∈ closure (Set.range (pointsMap B S hS X f))) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (K : FieldValuedPoint B S hS X) (_ : Algebra A K.carrier) (_ : IsFractionRing A K.carrier)
      (A_contained : B.Contains (Spec (.of A))) (s : Spec (.of A) ⟶ S)
      (j : K.siteObject ⟶ valuationObject B S hS A A_contained s)
      (g : yoneda.obj (valuationObject B S hS A A_contained s) ⟶ Y),
      j.left.1 = Scheme.Spec.map (CommRingCat.ofHom (algebraMap A K.carrier)).op ∧
      yoneda.map j ≫ g = yonedaEquiv.symm K.value ≫ f ∧
      pointsMap B S hS (yoneda.obj (valuationObject B S hS A A_contained s)) g
          ((schemePointRepresentative B S hS (valuationObject B S hS A A_contained s)
              (⟨IsLocalRing.maximalIdeal A, inferInstance⟩ : PrimeSpectrum A)).class B S hS
            (yoneda.obj (valuationObject B S hS A A_contained s))) = y ∧
      localRingDimension B S hS (K.class B S hS X) = 0 ∧
      (y ∈ closure (pointsMap B S hS X f ''
          {x' | localRingDimension B S hS x' = 0 ∧ pointsMap B S hS X f x' ≠ y}) →
        pointsMap B S hS X f (K.class B S hS X) ≠ y) ∧
      (pointsMap B S hS X f (K.class B S hS X) ≠ y →
        ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
          (u : (BigFppfOver.toScheme B S hS).obj U)
          (e : K.carrier ≃+* ((BigFppfOver.toScheme B S hS).obj U).residueField u)
          (t : K.siteObject ⟶ U),
          IsEtale B S hS a ∧
            t.left.1 = Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
                ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField u ∧
              a.app (Opposite.op K.siteObject) t = K.value) := by
  obtain ⟨d⟩ := nonempty_discreteValuationSpecialization B S hS f X_isAlgebraicSpace
    Y_isAlgebraicSpace f_finiteType Y_locallyNoetherian y y_mem_closure
  exact ⟨d.valuationRing, inferInstance, inferInstance, inferInstance, d.generic, inferInstance,
    inferInstance, d.valuation_contained, d.toBase, d.genericToValuation, d.toTarget,
    d.genericToValuation_spec, d.commutes, d.maps_closedPoint, d.codimension_zero,
    d.maps_ne_of_mem_closure, d.residueFieldDescription⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.DiscreteValuationSpecialization

/-- For the identity of the spectrum of a field `k`, the field-valued point of a
discrete-valuation-ring diagram reaching the point of `Spec k` is never the canonical point of a
residue field of `Spec k`: otherwise the valuation ring would map onto its fraction field. -/
theorem not_exists_residueFieldEquiv_id {k : Type u} [Field k] {y : Spec (.of k)}
    (d : DiscreteValuationSpecialization (𝟙 (Spec (.of k))) y) :
    ¬ ∃ e : d.fractionField ≃+* (Spec (.of k)).residueField d.genericPoint,
      d.toSource = Scheme.Spec.map (CommRingCat.ofHom e.symm.toRingHom).op ≫
        (Spec (.of k)).fromSpecResidueField d.genericPoint := by
  rintro ⟨e, he⟩
  have : d.genericPoint.asIdeal.IsPrime := d.genericPoint.isPrime
  have : d.genericPoint.asIdeal.IsMaximal := by
    rw [Ideal.eq_bot_of_prime d.genericPoint.asIdeal]
    exact Ideal.bot_isMaximal
  have hcomm := d.commutes
  rw [Category.comp_id, he, ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    ← Spec.map_preimage d.toTarget] at hcomm
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _ at hcomm
  simp only [← Spec.map_comp, Spec.map_inj] at hcomm
  have hsurj : Function.Surjective
      ((algebraMap d.valuationRing d.fractionField).comp (Spec.preimage d.toTarget).hom) := by
    have h := congrArg CommRingCat.Hom.hom hcomm
    simp only [CommRingCat.hom_comp, Quiver.Hom.unop_op, CommRingCat.hom_ofHom] at h
    rw [h]
    exact e.symm.surjective.comp
      ((Scheme.Spec.residueFieldIso _ d.genericPoint).commRingCatIsoToRingEquiv
        |>.symm.surjective.comp (Ideal.algebraMap_residueField_surjective _))
  exact IsDiscreteValuationRing.not_isField d.valuationRing
    (IsFractionRing.surjective_iff_isField.mp (Function.Surjective.of_comp hsurj))

end AlgebraicGeometry.DiscreteValuationSpecialization

end
