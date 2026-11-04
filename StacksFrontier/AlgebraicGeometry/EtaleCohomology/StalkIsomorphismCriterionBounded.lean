module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfSmallEtaleTopos

/-!
# Stalks at geometric points whose spectrum lies in the big étale site

Let `B` be a big étale site containing a scheme `X`. Every geometric point `s` of `X` factors
through a geometric point `t` whose residue field is an algebraic closure of a residue field of
`X`; the spectrum of such a field has size bounded by that of `X`, so it is again an object of
`B`. Since an étale scheme over an algebraically closed field is a disjoint union of copies of
its spectrum, the étale neighbourhoods of `s` and of `t` are the same, and so are the stalks at
`s` and at `t`. Consequently a morphism of abelian sheaves on the small étale site of `X` is an
isomorphism as soon as it is one on the stalks at the geometric points whose spectrum lies in
`B`. The identification of neighbourhoods is
`AlgebraicGeometry.geometricPointFiberIsoOfExtension`.

## Main results

* `AlgebraicGeometry.exists_bounded_geometricPoint_extension_bigEtale` — every geometric point
  of `X` factors through one whose spectrum lies in `B`.
* `AlgebraicGeometry.isIso_of_isIso_etaleStalkMap_bounded` — **Stacks 03PU**, the isomorphism
  case, testing only geometric points whose spectrum lies in `B`.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
include hX

/-- A geometric point of a scheme contained in a big étale site factors through one whose
spectrum is again contained in that site: the algebraic closure of the residue field at the
image point is no larger than the bound the site's cutoff is closed under. -/
public theorem exists_bounded_geometricPoint_extension_bigEtale (s : GeometricPoint X) :
    ∃ t : GeometricPoint X, B.Contains t.source ∧ ∃ e : s.source ⟶ t.source,
      e ≫ t.hom = s.hom := by
  obtain ⟨⟨x, a⟩, ha⟩ := (X.SpecToEquivOfField s.residueField).symm.surjective s.hom
  let K := AlgebraicClosure (X.residueField x)
  let : Algebra (X.residueField x) s.residueField := a.hom.toAlgebra
  let φ : K →ₐ[X.residueField x] s.residueField := IsAlgClosed.lift
  let t : GeometricPoint X :=
    { residueField := K
      hom := Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
        X.fromSpecResidueField x }
  have hK : Cardinal.mk K ≤ X.size ^ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max (X.residueField x) K).trans <|
      (max_le (Space.residueField_size_le X x) (Scheme.aleph0_le_size X)).trans <|
        Cardinal.self_le_power _ Cardinal.one_le_aleph0
  refine ⟨t, Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (.of K) hX hK, Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x) = s.hom
  rw [← Category.assoc, ← Spec.map_comp]
  have hφ : CommRingCat.ofHom (algebraMap (X.residueField x) K) ≫
      CommRingCat.ofHom φ.toRingHom = a := by
    ext z
    exact φ.commutes z
  rwa [hφ]

/-- **Stacks 03PU**, the isomorphism case for abelian sheaves, testing only the geometric points
whose spectrum lies in the big étale site: a morphism of abelian sheaves on the small étale site
of `X` inducing an isomorphism on the stalk at each such geometric point is an isomorphism. -/
public theorem isIso_of_isIso_etaleStalkMap_bounded [UnivLE.{u, v}]
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}} (α : F ⟶ G)
    (h : ∀ s : GeometricPoint X, B.Contains s.source →
      IsIso ((etaleStalkPresheafFunctor B X hX s AddCommGrpCat.{v}).map α.hom)) :
    IsIso α := by
  refine isIso_of_isIso_etaleStalkMap B X hX α fun s => ?_
  obtain ⟨t, ht, e, he⟩ := exists_bounded_geometricPoint_extension_bigEtale B hX s
  exact (NatIso.isIso_map_iff
    (elementColimitIso (geometricPointFiberIsoOfExtension B X hX s t e he) AddCommGrpCat.{v})
    α.hom).mp (h t ht)

end AlgebraicGeometry

end
