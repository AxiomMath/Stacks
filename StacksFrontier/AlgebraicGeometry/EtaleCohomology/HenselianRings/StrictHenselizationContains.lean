module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.StrictHenselizationImpurity
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfSmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# The strict henselization at a geometric point lies in the big étale site

Let `B` be a big étale site containing a scheme `S` and let `s` be a geometric point of `S`. The
strict henselization `Spec 𝒪^{sh}_{S,s}` is again contained in `B`, whatever the size of the
field of `s`, and so is the base change `X ×_S Spec 𝒪^{sh}_{S,s}` of any morphism `X ⟶ S` from a
scheme `X` contained in `B`.

The strict henselization is the limit of a family of affine étale neighbourhoods of `s` which is
bounded in terms of an affine open `Spec R` of `S` through which `s` factors and of the field of
`s` (`AlgebraicGeometry.strictHenselizationBoundedConeIsLimit`), so it is small as soon as that
field is. The field of `s` itself may be arbitrarily large, but the étale local ring only sees
the geometric point through its étale neighbourhoods, and these are the same for `s` and for the
geometric point `s₀` cut out by the algebraic closure, inside the field of `s`, of the image of
`R` (`AlgebraicGeometry.geometricPointFiberIsoOfExtension`): an étale scheme over `S` has
the same lifts of `s` and of `s₀`. That algebraic closure has at most `max ℵ₀ #R` elements, so
the bound applies to `s₀`, and the étale local rings at `s` and at `s₀` are isomorphic.

## Main results

* `AlgebraicGeometry.etaleLocalRingIsoOfExtension` — the étale local rings at two geometric
  points related by an extension of their fields are isomorphic.
* `AlgebraicGeometry.contains_strictHenselization_of_contains` — the strict henselization at a
  geometric point of a scheme of `B` lies in `B`.
* `AlgebraicGeometry.contains_strictHenselizationBaseChange` — so does the base change to it.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **The étale local ring only sees the étale neighbourhoods.** For geometric points `s` and `t`
of `S` and a morphism `f` from the source of `s` to the source of `t` over `S`, the étale local
rings at `s` and at `t` are isomorphic: restricting lifts along `f` identifies the étale
neighbourhoods of `t` with those of `s`. -/
def etaleLocalRingIsoOfExtension (s t : GeometricPoint S) (f : s.source ⟶ t.source)
    (hf : f ≫ t.hom = s.hom) : etaleLocalRing B S hS s ≅ etaleLocalRing B S hS t :=
  (Functor.Final.colimitIso
    (CategoryOfElements.equivalenceOfNatIso
      (geometricPointFiberIsoOfExtension B S hS s t f hf)).op.functor
    ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj)).symm

/-- A geometric point of `S` factoring through an affine open `Spec R` of `S` is induced, along an
extension of fields, from a geometric point whose field has at most `max ℵ₀ #R` elements: the
algebraic closure, inside the field of the given point, of the image of `R`. -/
theorem exists_geometricPoint_small_extension (s : GeometricPoint S) {R : CommRingCat.{u}}
    (ι₀ : Spec R ⟶ S) (s₀ : s.source ⟶ Spec R) (hs₀ : s₀ ≫ ι₀ = s.hom) :
    ∃ (t : GeometricPoint S) (f : s.source ⟶ t.source) (_ : f ≫ t.hom = s.hom)
      (t₀ : t.source ⟶ Spec R) (_ : t₀ ≫ ι₀ = t.hom), #t.residueField ≤ max ℵ₀ #R := by
  let φ : R →+* s.residueField := (Spec.preimage s₀).hom
  let K : Subfield s.residueField := Subfield.closure (Set.range φ)
  let L : IntermediateField K s.residueField := algebraicClosure K s.residueField
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let φL : R →+* L := φ.codRestrict L.toSubalgebra.toSubring fun r =>
    L.algebraMap_mem ⟨φ r, Subfield.subset_closure ⟨r, rfl⟩⟩
  let t : GeometricPoint S := ⟨L, Spec.map (CommRingCat.ofHom φL) ≫ ι₀⟩
  let incl : L →+* s.residueField := L.val.toRingHom
  have hcomp : incl.comp φL = φ := RingHom.ext fun _ => rfl
  refine ⟨t, Spec.map (CommRingCat.ofHom incl), ?_, Spec.map (CommRingCat.ofHom φL), rfl, ?_⟩
  · change Spec.map (CommRingCat.ofHom incl) ≫ Spec.map (CommRingCat.ofHom φL) ≫ ι₀ = s.hom
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp,
      CommRingCat.ofHom_hom, Spec.map_preimage, hs₀]
  · change #L ≤ max ℵ₀ #R
    have : Module.IsTorsionFree K L := DivisionSemiring.to_moduleIsTorsionFree
    exact (Algebra.IsAlgebraic.cardinalMk_le_max K L).trans
      (max_le ((Subfield.cardinalMk_closure_le_max _).trans
        (max_le (Cardinal.mk_range_le.trans (le_max_right _ _)) (le_max_left _ _)))
        (le_max_left _ _))

/-- **The strict henselization at a geometric point with a small field lies in `B`.** If the
geometric point factors through an affine open `Spec R` of `S` and its field has at most
`max ℵ₀ #R` elements, the bounded family of affine étale neighbourhoods has fewer members than
the cutoff, and its stages are no larger than `S`, so its limit is in `B`. -/
theorem contains_strictHenselization_of_small (t : GeometricPoint S) {R : CommRingCat.{u}}
    (ι₀ : Spec R ⟶ S) [IsOpenImmersion ι₀] (t₀ : t.source ⟶ Spec R) (ht₀ : t₀ ≫ ι₀ = t.hom)
    (ht : #t.residueField ≤ max ℵ₀ #R) :
    B.Contains (strictHenselization B S hS t) := by
  have hRle : max ℵ₀ #R ≤ S.size := by
    rw [← Scheme.size_Spec]
    exact Scheme.size_le_of_isOpenImmersion ι₀
  have hm : max ℵ₀ #R < B.cutoff := hRle.trans_lt hS
  have hJ : #(EtaleNeighborhoodBounded B hS t ι₀) < B.cutoff :=
    (mk_etaleNeighborhoodBoundedIndex_le t ι₀).trans_lt
      (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le (B.cutoff_isStrongPrelimit hm)
        (Space.power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
          (ht.trans_lt hm) hm))
  have := isCofiltered_etaleNeighborhoodBounded B hS t₀ ht₀
  change B.Contains (strictHenselizationBoundedCone B hS t ι₀).pt
  exact Scheme.size_lt_of_isLimit_of_isAffine_of_size_le B.aleph0_lt_cutoff
    (etaleNeighborhoodBoundedFunctor B hS t ι₀ ⋙ etaleNeighborhoodDiagram B S hS t)
    (fun j ↦ inferInstanceAs (IsAffine (Spec (boundedPresRing j.1.1))))
    hJ hS (fun j ↦ size_spec_boundedPresRing_le ι₀ j.1.1)
    (strictHenselizationBoundedConeIsLimit B hS t₀ ht₀)

/-- **The strict henselization at a geometric point of a scheme of a big étale site lies in that
site**, with no condition on the field of the geometric point. -/
theorem contains_strictHenselization_of_contains (s : GeometricPoint S) :
    B.Contains (strictHenselization B S hS s) := by
  obtain ⟨R, ι₀, hι₀, s₀, hs₀⟩ := Space.exists_affine_open_geometricPoint s
  obtain ⟨t, f, hf, t₀, ht₀, ht⟩ := exists_geometricPoint_small_extension s ι₀ s₀ hs₀
  have hsize : (strictHenselization B S hS t).size = (strictHenselization B S hS s).size :=
    Scheme.size_congr (Scheme.Spec.mapIso
      (etaleLocalRingIsoOfExtension B hS s t f hf).ringCatIsoToRingEquiv.toCommRingCatIso.op)
  exact hsize.symm.trans_lt (contains_strictHenselization_of_small B hS t ι₀ t₀ ht₀ ht)

/-- The base change `X ×_S Spec 𝒪^{sh}_{S,s}` of a morphism from a scheme of `B` to the strict
henselization at a geometric point lies in `B`. -/
theorem contains_strictHenselizationBaseChange {X : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ S)
    (s : GeometricPoint S) : B.Contains (strictHenselizationBaseChange B hS f s) :=
  Scheme.size_pullback_lt _ _ hX (contains_strictHenselization_of_contains B hS s)

end AlgebraicGeometry

end
