module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleLocalRing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse

/-!
# The strict henselization of a scheme at a geometric point

The étale local ring of a scheme `S` at a geometric point `s` is canonically the strict
henselization of the ordinary local ring at the image of `s`. This file reads the commutative
ring, local ring and algebra structures of the étale local ring off that identification, and
introduces the affine scheme it defines together with the two canonical morphisms relating it
to `S` and to the geometric point.

## Main definitions

* `AlgebraicGeometry.geometricHenselizationTower` is the henselization tower used throughout:
  the tower of the ordinary local ring at the image of `s`, over the separable closure of its
  residue field inside the residue field of `s`.
* `AlgebraicGeometry.strictHenselization` is the spectrum of the étale local ring at `s`.
* `AlgebraicGeometry.strictHenselizationToBase` is its structure morphism to `S`.
* `AlgebraicGeometry.geometricPointToStrictHenselization` is the canonical lift of `s` to the
  strict henselization, induced by evaluation of étale germs in the residue field of `s`.

## Main results

* `AlgebraicGeometry.geometricPointToStrictHenselization_comp` says the canonical lift composes
  with the structure morphism to the original geometric point.
* `AlgebraicGeometry.indEtale_etaleLocalRing` says the étale local ring is ind-étale over the
  ordinary local ring at the image of `s`.

## Implementation notes

Commutativity of the étale local ring is not available where that ring is constructed, since it
is the stalk of a sheaf of rings; it is obtained here from the canonical identification with a
strict henselization. The commutative ring instance therefore extends the ring structure already
present rather than transporting a new one, so that no two multiplications are in play.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The henselization tower attached to a geometric point `s` of `S`: the tower of the ordinary
local ring at the image of `s`, taken over the separable closure of its residue field inside the
residue field of `s`. -/
public abbrev geometricHenselizationTower :
    IsLocalRing.HenselizationTower
      ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (separableClosure
        (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
        s.residueField) :=
  IsLocalRing.henselizationTower _ _

/-- The canonical identification of the étale local ring at `s` with the strict henselization of
the ordinary local ring in the tower `geometricHenselizationTower`. -/
public abbrev etaleLocalRingEquivStrictHenselization :
    (geometricHenselizationTower S s).strictHenselization ≃+* ↥(etaleLocalRing B S hS s) :=
  (etaleLocalRing_strictHenselization_canonical B S hS s
    (geometricHenselizationTower S s)).val

/-- The étale local ring at a geometric point is commutative: it is the strict henselization of
the ordinary local ring at the image of that point. -/
public instance etaleLocalRingCommRing : CommRing ↥(etaleLocalRing B S hS s) :=
  { (inferInstance : Ring ↥(etaleLocalRing B S hS s)) with
    mul_comm := by
      intro a b
      obtain ⟨a, rfl⟩ :=
        (etaleLocalRingEquivStrictHenselization B S hS s).surjective a
      obtain ⟨b, rfl⟩ :=
        (etaleLocalRingEquivStrictHenselization B S hS s).surjective b
      rw [← map_mul, ← map_mul, mul_comm] }

/-- The étale local ring at a geometric point is a local ring. -/
public instance etaleLocalRingIsLocalRing : IsLocalRing ↥(etaleLocalRing B S hS s) :=
  (etaleLocalRingEquivStrictHenselization B S hS s).isLocalRing

/-- The étale local ring at a geometric point is an algebra over the ordinary local ring at the
image of that point, through the canonical ordinary-to-étale germ map. -/
public instance etaleLocalRingAlgebra :
    Algebra ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      ↥(etaleLocalRing B S hS s) :=
  (structureSheafStalkFromLocalRing B S hS s).toAlgebra

/-- The map from the ordinary local ring to the étale local ring is the structure map of the
algebra structure it defines. -/
public theorem algebraMap_etaleLocalRing :
    algebraMap ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
        ↥(etaleLocalRing B S hS s) = structureSheafStalkFromLocalRing B S hS s :=
  rfl

/-- The canonical identification of the étale local ring with a strict henselization is a map of
algebras over the ordinary local ring. -/
public abbrev etaleLocalRingAlgEquivStrictHenselization :
    (geometricHenselizationTower S s).strictHenselization ≃ₐ[
        ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))]
      ↥(etaleLocalRing B S hS s) :=
  { etaleLocalRingEquivStrictHenselization B S hS s with
    commutes' := (etaleLocalRing_strictHenselization_canonical B S hS s
      (geometricHenselizationTower S s)).property.1 }

/-- The map from the ordinary local ring at the image of a geometric point to the étale local
ring there is a local homomorphism. -/
public instance isLocalHom_algebraMap_etaleLocalRing :
    IsLocalHom (algebraMap ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      ↥(etaleLocalRing B S hS s)) := by
  set R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
  set T := geometricHenselizationTower S s
  have hbase : ((etaleLocalRingAlgEquivStrictHenselization B S hS s :
      T.strictHenselization →+* ↥(etaleLocalRing B S hS s)).comp
        (algebraMap R T.strictHenselization)) =
      algebraMap R ↥(etaleLocalRing B S hS s) :=
    RingHom.ext (etaleLocalRing_strictHenselization_canonical B S hS s T).property.1
  have : IsLocalHom (algebraMap R T.strictHenselization) := by
    rw [IsScalarTower.algebraMap_eq R T.henselization T.strictHenselization]
    infer_instance
  have : IsLocalHom (etaleLocalRingAlgEquivStrictHenselization B S hS s :
      T.strictHenselization →+* ↥(etaleLocalRing B S hS s)) :=
    IsLocalHom.of_surjective _
      (etaleLocalRingEquivStrictHenselization B S hS s).surjective
  rw [← hbase]
  infer_instance

/-- The étale local ring at a geometric point is ind-étale over the ordinary local ring at the
image of that point: it is a strict henselization of that local ring, and a strict henselization
is a filtered colimit of étale algebras. -/
public theorem indEtale_etaleLocalRing :
    StacksDraft.IndEtale ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      ↥(etaleLocalRing B S hS s) := by
  have hT : StacksDraft.IndEtale
      ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (geometricHenselizationTower S s).strictHenselization :=
    (IsLocalRing.HenselizationTower.instIsHenselizationStrictHenselization
      (geometricHenselizationTower S s)).ind_etale
  exact StacksDraft.indEtale_of_equiv (RingEquiv.refl _)
    (etaleLocalRingEquivStrictHenselization B S hS s)
    (etaleLocalRing_strictHenselization_canonical B S hS s
      (geometricHenselizationTower S s)).property.1 hT

/-- The strict henselization of a scheme at a geometric point: the spectrum of the étale local
ring there. -/
@[stacks 03PS "part (3)",
  sga "2 XIV 1.1",
  sga "4 VIII 4.3",
  sga "4 VIII 7.1" "partial",
  sga "4½ Arcata 2.3.3" "Ỹ = Spec(O_{Y",
  sga "4½ Arcata 5.1.1",
  sga "4½ Th_finitude 2.11",
  sga "7 I 0.0.4",
  sga "7 XIII 2.1.3" "The scheme X_(x̄)",
  sga "7 XVI 1.6" "S_(s̄) only"]
public abbrev strictHenselization : Scheme.{u} :=
  Spec (.of ↥(etaleLocalRing B S hS s))

/-- The canonical morphism from the strict henselization at a geometric point to the scheme: the
spectrum of the ordinary-to-étale germ map, followed by the canonical morphism from the local
scheme at the image of the geometric point. -/
@[sga "2 XIV 1.1",
  sga "4 VIII 7.1",
  sga "4½ Arcata 2.3.3" "partial",
  sga "4½ Th_finitude 2.11",
  sga "7 I 0.0.4" "partial"]
public def strictHenselizationToBase : strictHenselization B S hS s ⟶ S :=
  Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s)) ≫
    S.fromSpecStalk (s.hom (closedPoint s.residueField))

/-- The canonical lift of a geometric point to the strict henselization there: the spectrum of
the evaluation of étale germs in the residue field of the geometric point. -/
public def geometricPointToStrictHenselization : s.source ⟶ strictHenselization B S hS s :=
  Spec.map (CommRingCat.ofHom (structureSheafStalkToGeometricField B S hS s))

/-- Evaluating étale germs after the ordinary-to-étale germ map is evaluation of ordinary germs
in the residue field of the geometric point. -/
public theorem ofHom_toGeometricField_comp_fromLocalRing :
    CommRingCat.ofHom ((structureSheafStalkToGeometricField B S hS s).comp
        (structureSheafStalkFromLocalRing B S hS s)) =
      Scheme.stalkClosedPointTo s.hom := by
  let R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
  let κ := ResidueField R
  let κsep := separableClosure κ s.residueField
  let T := geometricHenselizationTower S s
  let c := etaleLocalRing_strictHenselization_canonical B S hS s T
  let e := c.val
  let η := structureSheafStalkFromLocalRing B S hS s
  let ε := structureSheafStalkToGeometricField B S hS s
  ext r
  calc
    ε (η r) = ε (e (algebraMap R T.strictHenselization r)) := by rw [c.property.1]
    _ = ((T.strictHenselizationResidueEquiv.symm
          (residue T.strictHenselization
            (algebraMap R T.strictHenselization r)) : κsep) : s.residueField) :=
      c.property.2 _
    _ = (algebraMap κ κsep (residue R r) : s.residueField) := by
      congr 1
      exact T.strictHenselizationResidueEquiv.injective
        ((T.strictHenselizationResidueEquiv.apply_symm_apply _).trans
          (T.strictHenselizationResidueEquiv_residue r).symm)
    _ = Scheme.stalkClosedPointTo s.hom r := by
      change (algebraMap κ s.residueField) (residue R r) = _
      exact congrArg (fun φ : S.presheaf.stalk (s.hom (closedPoint s.residueField)) ⟶
          CommRingCat.of s.residueField => φ r)
        (Scheme.residue_descResidueField (f := Scheme.stalkClosedPointTo s.hom))

/-- **Stacks Project, Tag 0993.** The canonical lift of a geometric point to its strict
henselization lies over that geometric point, so the strict henselization is a pro-étale
neighbourhood of the point. -/
@[stacks 0993 "the canonical geometric point"]
public theorem geometricPointToStrictHenselization_comp :
    geometricPointToStrictHenselization B S hS s ≫ strictHenselizationToBase B S hS s =
      s.hom := by
  rw [geometricPointToStrictHenselization, strictHenselizationToBase, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
      ((structureSheafStalkToGeometricField B S hS s).comp
        (structureSheafStalkFromLocalRing B S hS s))) ≫
      S.fromSpecStalk (s.hom (closedPoint s.residueField)) = s.hom
  rw [ofHom_toGeometricField_comp_fromLocalRing]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := s.hom)

/-- The étale local ring of a scheme at a geometric point is strictly henselian: it is the
strict henselization of the ordinary local ring at the image of that point. -/
@[sga "4 VIII 4.4" "A^hs, special case",
  sga "4 VIII 7.1" "X̄(ξ) is strictly local",
  sga "4½ Arcata 2.3.1" "special case"]
public theorem etaleLocalRing_strictHenselian (B : BigEtaleSite.{u}) (Y : Scheme.{u})
    (hY : B.Contains Y) (s : GeometricPoint Y) :
    _root_.StrictlyHenselianLocalRing ↥(etaleLocalRing B Y hY s) :=
  strictlyHenselianLocalRing_of_ringEquiv (etaleLocalRingEquivStrictHenselization B Y hY s)

/-- Evaluation of étale germs at a geometric point is a local homomorphism: a germ with
nonzero value has nonzero residue in the strict henselization, hence is a unit. -/
public theorem structureSheafStalkToGeometricField_isLocalHom (B : BigEtaleSite.{u})
    (Y : Scheme.{u}) (hY : B.Contains Y) (s : GeometricPoint Y) :
    IsLocalHom (structureSheafStalkToGeometricField B Y hY s) := by
  let R := ↥(Y.presheaf.stalk (s.hom (closedPoint s.residueField)))
  let κsep := separableClosure (ResidueField R) s.residueField
  let T := geometricHenselizationTower Y s
  let c := etaleLocalRing_strictHenselization_canonical B Y hY s T
  let e := c.val
  let ε := structureSheafStalkToGeometricField B Y hY s
  refine ⟨fun a ha => ?_⟩
  have hres : residue T.strictHenselization (e.symm a) ≠ 0 := by
    intro hz
    refine (isUnit_iff_ne_zero.mp ha) ?_
    calc
      ε a = ε (e (e.symm a)) := congrArg ε (e.apply_symm_apply a).symm
      _ = ((T.strictHenselizationResidueEquiv.symm
            (residue T.strictHenselization (e.symm a)) : κsep) : s.residueField) :=
        c.property.2 (e.symm a)
      _ = 0 := by rw [hz]; simp
  simpa only [e.apply_symm_apply] using ((residue_ne_zero_iff_isUnit _).mp hres).map e

end AlgebraicGeometry

end
