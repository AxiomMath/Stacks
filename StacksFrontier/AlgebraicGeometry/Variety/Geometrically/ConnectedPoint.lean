module

public import StacksCore.FieldTheory.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected schemes over a field with a distinguished point

A connected scheme over a field is geometrically connected if the field is algebraically closed
in the residue field of one of its points. In particular, a connected scheme with a rational
point is geometrically connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_algebraicClosure_eq_bot`
  gives geometric connectedness from a point whose residue field has no new algebraic elements
  over the base field.
* `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section` gives the
  rational-point consequence.

## Implementation notes

In the first result, the algebra structure on the residue field is the one induced by the
structure morphism: it is the composite from the base field to the residue field at the image
point, followed by the residue-field map of the morphism. The second result expresses a rational
point as a section of the structure morphism.

## References

* [Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 04KV.** A connected scheme over a field is geometrically
connected if the field is algebraically closed in the residue field of one of
its points. -/
@[stacks 04KV "point with algebraically closed base field"]
public theorem geometricallyConnected_of_connectedSpace_of_algebraicClosure_eq_bot
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] (x : X)
    (h : let : (f x).asIdeal.IsPrime := (f x).isPrime
      let := ((CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField)) ≫
        (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫
        f.residueFieldMap x).hom.toAlgebra
      IsAlgClosedIn k (X.residueField x)) :
    GeometricallyConnected f := by
  let : (f x).asIdeal.IsPrime := (f x).isPrime
  let := ((CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField)) ≫
    (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫
    f.residueFieldMap x).hom.toAlgebra
  let : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x)))) :=
    Algebra.IsGeometricallyIrreducible.of_algebraicClosure_eq_bot _ _ h
  let : GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x)))) :=
    ⟨by
      intro K _ y Z fst snd hp
      have : IrreducibleSpace Z :=
        GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd hp
      infer_instance⟩
  have halg : CommRingCat.ofHom (algebraMap k (X.residueField x)) =
      CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫
        f.residueFieldMap x := by
    ext a
    exact DFunLike.congr_fun (RingHom.algebraMap_toAlgebra _) a
  have hmaps : Spec.map
        (CommRingCat.ofHom (algebraMap k (f x).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of k) (f x)).inv ≫
          f.residueFieldMap x) =
      (Spec.map (f.residueFieldMap x) ≫
        Spec.map (Scheme.Spec.residueFieldIso (.of k) (f x)).inv) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (f x).asIdeal.ResidueField)) :=
    (Scheme.Spec.map_comp _ _).trans
      (congrArg (· ≫ Spec.map (CommRingCat.ofHom
        (algebraMap k (f x).asIdeal.ResidueField)))
        (Scheme.Spec.map_comp _ _))
  have hcomp : GeometricallyConnected
      (X.fromSpecResidueField x ≫ f) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc, ← hmaps,
      ← halg]
    infer_instance
  exact geometricallyConnected_of_comp_of_connectedSpace
    k (X.fromSpecResidueField x) f

/-- **Stacks Project, Tag 04KV, rational-point consequence.** A connected scheme
over a field with a rational point is geometrically connected. -/
@[stacks 04KV "rational-point consequence", sga "3 VIA 2.1.2" "Y = Spec of field ext"]
public theorem geometricallyConnected_of_connectedSpace_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  have hgc : GeometricallyConnected (𝟙 (Spec (.of k))) := by
    refine ⟨fun K _ y Z fst snd hp ↦ ?_⟩
    let := hp.isIso_snd_of_isIso
    exact (show ObjectProperty Scheme from fun Y ↦ ConnectedSpace Y).prop_of_iso
      (asIso snd).symm inferInstance
  let : GeometricallyConnected (s ≫ f) := hs ▸ hgc
  exact geometricallyConnected_of_comp_of_connectedSpace k s f

end AlgebraicGeometry
