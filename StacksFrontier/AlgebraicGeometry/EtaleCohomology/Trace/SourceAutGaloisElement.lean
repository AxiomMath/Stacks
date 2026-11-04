module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GeometricPointAction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenericPoint

/-!
# Automorphisms of a geometric point as elements of the Galois group

Let `z` be a geometric point of a connected scheme, with field `Ω`. An automorphism `α` of
`Spec Ω` over the scheme acts on the fibre functor at `z` by precomposition
(`AlgebraicGeometry.GeometricPoint.sourceAutElement`). This file compares these elements with the
other ways elements of fundamental groups arise:

* they are functorial: the image under `π₁(f)` of the element of `α` is the element of `α` at
  `f(z)`;
* for a field `K`, a separable closure `L` and an algebraic closure `Ω` of `K` containing `L`,
  the canonical isomorphism `Gal(L/K) ≅ π₁(Spec K, Ω)` of Tag 0BNE sends `σ` to the element of
  `Spec τ` for any `τ ∈ Aut(Ω/K)` extending `σ`;
* consequently, for an irreducible scheme `X` with function field `K`, the canonical
  homomorphism `Gal(L/K) → π₁(X, η̄)` of Tag 0BQH sends the restriction to `L` of `τ ∈ Aut(Ω/K)`
  to the element of `Spec τ` at `η̄`.

## Main results

* `AlgebraicGeometry.etaleFundamentalGroupMap_sourceAutElement`: the elements of automorphisms
  of the source are functorial.
* `AlgebraicGeometry.galoisEquivEtaleFundamentalGroup_eq_sourceAutElement`: the isomorphism
  `Gal(L/K) ≅ π₁(Spec K, Ω)` of Tag 0BNE sends `σ` to the element of an extension of `σ` to `Ω`.
* `AlgebraicGeometry.galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement`: the
  homomorphism `Gal(L/K) → π₁(X, η̄)` of Tag 0BQH sends the restriction of `τ` to the element of
  `Spec τ`.
* `AlgebraicGeometry.GeometricPoint.exists_algEquiv_of_specMap_comp_hom` — an automorphism of
  `Ω` whose spectrum fixes the geometric point is an automorphism over the residue field at its
  image.

## References

* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)
* [Stacks Project, Tag 0BQH](https://stacks.math.columbia.edu/tag/0BQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Elements given by automorphisms of the source are functorial**: `π₁(f)` sends the element of
`α` at `z` to the element of `α` at `f(z)`. -/
theorem etaleFundamentalGroupMap_sourceAutElement {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (z : GeometricPoint X) (α : z.source ≅ z.source)
    (hα : α.hom ≫ z.hom = z.hom) :
    etaleFundamentalGroupMap f z (z.sourceAutElement α hα) =
      (z.map f).sourceAutElement α (by
        change α.hom ≫ z.hom ≫ f = z.hom ≫ f
        rw [← Category.assoc, hα]) := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  ext q
  refine Subtype.ext ?_
  change (α.hom ≫ pullback.lift q.1 z.hom q.2) ≫ pullback.fst V.hom f = α.hom ≫ q.1
  rw [Category.assoc, pullback.lift_fst]

/-- **The Galois element of Tag 0BNE is the element of an extension to `Ω`**: for `τ ∈ Aut(Ω/K)`
restricting to `σ` on `L`, the image of `σ` in `π₁(Spec K, Ω)` is precomposition with `Spec τ`. -/
theorem galoisEquivEtaleFundamentalGroup_eq_sourceAutElement
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] (σ : Gal(L/K)) (τ : Ω ≃ₐ[K] Ω)
    (hτ : ∀ l : L, τ (algebraMap L Ω l) = algebraMap L Ω (σ l))
    (hα : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op).hom ≫
      (algebraicClosureGeometricPoint K Ω).hom = (algebraicClosureGeometricPoint K Ω).hom) :
    galoisEquivEtaleFundamentalGroup K L Ω σ =
      (algebraicClosureGeometricPoint K Ω).sourceAutElement
        (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op) hα := by
  refine Iso.ext (NatTrans.ext (funext fun Y => ?_))
  ext p
  refine Subtype.ext ?_
  let y := (finiteEtaleFiberIso K L Ω).inv.app Y p
  have hy : (finiteEtaleFiberIso K L Ω).hom.app Y y = p :=
    congrArg (fun g => g p) (congrArg (fun η => η.app Y) (finiteEtaleFiberIso K L Ω).inv_hom_id)
  have hf : p.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
      (separableFiberEquiv K L Ω Y y).1 := by
    rw [← finiteEtaleFiberIso_apply K L Ω Y y, hy]
  refine (galoisEquivEtaleFundamentalGroup_apply K L Ω Y σ p _ hf).trans ?_
  change _ = Spec.map (CommRingCat.ofHom (τ.toRingEquiv : Ω →+* Ω)) ≫ p.1
  rw [hf, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext l
  exact (hτ l).symm

/-- **The canonical homomorphism `Gal(L/K) → π₁(X, η̄)` on restrictions of automorphisms of
`Ω`** (Tag 0BQH): the restriction to `L` of `τ ∈ Aut(Ω/K)` goes to the element of `Spec τ` at the
geometric generic point. -/
theorem galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement
    (X : Scheme.{u}) [IrreducibleSpace X]
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (X.residueField (genericPoint X)) L]
    [IsSepClosure (X.residueField (genericPoint X)) L]
    [Algebra L Ω] [Algebra (X.residueField (genericPoint X)) Ω]
    [IsScalarTower (X.residueField (genericPoint X)) L Ω]
    [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (X.residueField (genericPoint X)) Ω]
    (τ : Ω ≃ₐ[X.residueField (genericPoint X)] Ω)
    (hα : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op).hom ≫
      ((algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).map
        (X.fromSpecResidueField (genericPoint X))).hom =
      ((algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).map
        (X.fromSpecResidueField (genericPoint X))).hom) :
    haveI : Normal (X.residueField (genericPoint X)) L := IsGalois.to_normal
    galoisToFundamentalGroup X L Ω (τ.restrictNormal L) =
      ((algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).map
        (X.fromSpecResidueField (genericPoint X))).sourceAutElement
        (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op) hα := by
  have : Normal (X.residueField (genericPoint X)) L := IsGalois.to_normal
  have hα₀ : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op).hom ≫
      (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).hom =
      (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 2
    ext c
    exact τ.commutes c
  change etaleFundamentalGroupMap (X.fromSpecResidueField (genericPoint X))
    (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω)
      (galoisEquivEtaleFundamentalGroup (X.residueField (genericPoint X)) L Ω
        (τ.restrictNormal L)) = _
  rw [galoisEquivEtaleFundamentalGroup_eq_sourceAutElement (X.residueField (genericPoint X)) L Ω
    (τ.restrictNormal L) τ
    (fun l => (AlgEquiv.restrictNormal_commutes τ L l).symm) hα₀]
  exact etaleFundamentalGroupMap_sourceAutElement (X.fromSpecResidueField (genericPoint X))
    (algebraicClosureGeometricPoint (X.residueField (genericPoint X)) Ω)
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op) hα₀

attribute [local instance] GeometricPoint.residueFieldAlgebra in
/-- **An automorphism of `Ω` whose spectrum fixes a geometric point is an automorphism over the
residue field at its image**: if `Spec τ ≫ t = t`, then `τ` fixes the image of the residue field
`κ(t)` of `S` at the image of `t`. -/
theorem GeometricPoint.exists_algEquiv_of_specMap_comp_hom {S : Scheme.{u}} (t : GeometricPoint S)
    (τ : t.residueField ≃+* t.residueField)
    (hτ : Spec.map (CommRingCat.ofHom (τ : t.residueField →+* t.residueField)) ≫ t.hom = t.hom) :
    ∃ τ' : Gal(t.residueField / S.residueField (t.hom default)), τ'.toRingEquiv = τ := by
  have h := GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField t
  have key : CommRingCat.ofHom (GeometricPoint.residueFieldHom t) ≫
      CommRingCat.ofHom (τ : t.residueField →+* t.residueField) =
      CommRingCat.ofHom (GeometricPoint.residueFieldHom t) := by
    apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecResidueField (t.hom default)), Spec.map_comp, Category.assoc, h,
      hτ]
  exact ⟨{ τ with commutes' := fun a => congrArg (fun g => g.hom a) key }, rfl⟩

end AlgebraicGeometry

end
