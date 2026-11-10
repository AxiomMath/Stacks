module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SheafStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# The Galois action on a stalk as the action of automorphisms of the geometric point

Let `K` be a field and `sbar` a geometric point of `Spec K` with algebraically closed field `Ω`.
The absolute Galois group `Gal(K^sep/K)` at `sbar` acts on the stalk at `sbar` of every sheaf of
sets on the small étale site of `Spec K` (`AlgebraicGeometry.etaleStalkSmul`), by moving a
pointed étale neighbourhood along the Galois action on lifts. On the other hand an automorphism
`τ` of `Ω` over `K` is an automorphism `Spec τ` of the geometric point, and induces the canonical
map of stalks of Stacks 04FN (`AlgebraicGeometry.geometricPointStalkMap`). If `τ` restricts to
`σ` on the separable closure, the two maps agree.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.specIsoOfAlgEquiv` — the automorphism `Spec τ` of the source
  of a geometric point, for `τ` a field automorphism.

## Main results

* `AlgebraicGeometry.etaleStalkSmul_eq_geometricPointStalkMap` — the action of `σ` on the stalk
  at `sbar` is the canonical map of stalks along `Spec τ`, when `τ` restricts to `σ`.
* `AlgebraicGeometry.GeometricPoint.exists_lift_of_isAlgebraic` — for an algebraic geometric
  point, every element of the absolute Galois group lifts to an automorphism of the point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- **The Galois action on a stalk is the action of a lifted automorphism of the geometric
point.** If `τ ∈ Aut(Ω/κ)` restricts to `σ` on the separable closure and `a` is the automorphism
`Spec τ` of the geometric point, then `σ` acts on the stalk at `sbar` by the canonical map of
stalks along `a`. -/
theorem etaleStalkSmul_eq_geometricPointStalkMap
    (F : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (τ : Gal(sbar.residueField/(Spec (.of K)).residueField (sbar.hom default)))
    (hτ : ∀ a : GeometricPoint.separableClosure sbar,
      (σ a : sbar.residueField) = τ (a : sbar.residueField))
    (a : GeometricPoint.Hom sbar sbar) (ha : a.hom = Spec.map (CommRingCat.ofHom τ.toRingHom)) :
    etaleStalkSmul.{u, v} B K hK sbar F σ =
      (geometricPointStalkMap B (Spec (.of K)) hK a (Type (max u v))).app
        ((sheafToPresheaf _ _).obj F) := by
  refine (fieldSitePoint B K hK sbar).presheafFiber_hom_ext (fun X p ↦ ?_)
  refine (toPresheafFiber_comp_etaleStalkSmul.{u, v} B K hK sbar F σ X p).trans ?_
  have hp : galoisFiberAction B K hK sbar σ p =
      (geometricPointFiberMap B (Spec (.of K)) hK a).app X p := by
    apply Subtype.ext
    rw [coe_galoisFiberAction_of_extends B K hK sbar σ τ.toRingHom (fun x ↦ (hτ x).symm) p]
    change _ = a.hom ≫ p.1
    rw [ha]
  rw [hp]
  exact (colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B (Spec (.of K)) hK sbar)).op ⋙
    (sheafToPresheaf _ _).obj F) (neighborhoodFunctor B (Spec (.of K)) hK a).op
    (op (Functor.elementsMk _ X p))).symm

/-- An automorphism of the field of a geometric point over the residue field at its image is an
automorphism of the geometric point. -/
theorem GeometricPoint.specMap_algEquiv_comp_hom {S : Scheme.{u}} (t : GeometricPoint S)
    (τ : Gal(t.residueField/S.residueField (t.hom default))) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t.hom = t.hom := by
  have hfix : CommRingCat.ofHom (GeometricPoint.residueFieldHom t) ≫
      CommRingCat.ofHom τ.toRingHom = CommRingCat.ofHom (GeometricPoint.residueFieldHom t) := by
    ext a
    exact τ.commutes a
  have h := GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField t
  refine (congrArg (Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ ·) h.symm).trans ?_
  rw [← Category.assoc, ← Spec.map_comp, hfix, h]

/-- The automorphism `Spec τ` of the source of a geometric point, for `τ` a field automorphism. -/
def GeometricPoint.specIsoOfAlgEquiv {S : Scheme.{u}} (t : GeometricPoint S)
    (τ : Gal(t.residueField/S.residueField (t.hom default))) : t.source ≅ t.source where
  hom := Spec.map (CommRingCat.ofHom τ.toRingHom)
  inv := Spec.map (CommRingCat.ofHom τ.symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of t.residueField)
    ext x
    simp
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert Spec.map_id (CommRingCat.of t.residueField)
    ext x
    simp

/-- **Every Galois automorphism lifts to an automorphism of an algebraic geometric point.** If the
field `Ω` of `t` is an algebraic closure of the residue field `κ` at its image, every
`σ ∈ Gal(κ^sep/κ)` extends to `τ ∈ Aut(Ω/κ)`, and `Spec τ` is an automorphism of `t`. -/
theorem GeometricPoint.exists_lift_of_isAlgebraic {S : Scheme.{u}} (t : GeometricPoint S)
    (ht : t.IsAlgebraic) (σ : GeometricPoint.absoluteGaloisGroup t) :
    ∃ (τ : Gal(t.residueField / S.residueField (t.hom default)))
      (_ : ∀ a : GeometricPoint.separableClosure t,
        (σ a : t.residueField) = τ (a : t.residueField))
      (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom)),
      α.hom ≫ t.hom = t.hom := by
  have : IsAlgClosure (S.residueField (t.hom default)) t.residueField := ht
  have : Normal (S.residueField (t.hom default)) t.residueField := IsAlgClosure.normal _ _
  let τ : Gal(t.residueField / S.residueField (t.hom default)) :=
    AlgEquiv.liftNormal σ t.residueField
  exact ⟨τ, fun a => (AlgEquiv.liftNormal_commutes σ t.residueField a).symm,
    t.specIsoOfAlgEquiv τ, rfl, t.specMap_algEquiv_comp_hom τ⟩

end AlgebraicGeometry

end
