module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsPadic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SourceAutGaloisElement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint

/-!
# The local geometry at a missing point of a curve

Let `jW : V ⟶ W` be an open immersion with `V` irreducible, `c ∈ W` a specialization of the image
of the generic point of `V`, and `π : Spec H ⟶ W` a morphism through `Spec 𝒪_{W,c}` (for `H` the
étale local ring at a geometric point over `c`, the strict henselization). When the base change
`V ×_W Spec H` is the spectrum of a field `K^{sh}` (a fraction field of `H`), this file computes:

* the composite `Spec Ω → Spec K^{sh} ≅ V ×_W Spec H → V` for a field embedding `K^{sh} → Ω`, as
  the geometric point through the generic point of `V` given by the induced embedding of the
  function field, once the two agree on `𝒪_{W,c}`;
* the ring endomorphism of `K^{sh}` induced by an endomorphism of `Spec H` over `W`;
* the residue map of the endomorphism of the étale local ring induced by the geometric Frobenius
  (it raises to the power `#κ(c)` to the inverse);

together with the multiplicativity of the elements of fundamental groups given by automorphisms
of the source of a geometric point, their transport along an equality of geometric points, and
the algebraicity of the geometric point `Spec Ω → Spec K^{sh}`.

## Main results

* `Stacks.EtaleCohomology.specMap_curveLocalRingToFunctionField_comp_fromSpecStalk`.
* `Stacks.EtaleCohomology.specMap_comp_inv_fst_eq_of_ringHom`.
* `Stacks.EtaleCohomology.exists_ringHom_specMap_eq_conj`.
* `Stacks.EtaleCohomology.residue_etaleLocalRingEndomorphism_pow`.
* `Stacks.EtaleCohomology.isAlgebraic_specMap_geometricPoint`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.EtaleCohomology

/-! ### The generic point and the local ring at a missing point -/

section Curve

variable {V W : Scheme.{u}} [IrreducibleSpace V] (jW : V ⟶ W)

/-- The map `𝒪_{W,y} → κ(η_V)` and the canonical morphisms from spectra of stalks and residue
fields are compatible: `Spec κ(η_V) → Spec 𝒪_{W,y} → W` is `Spec κ(η_V) → V → W`. -/
theorem specMap_curveLocalRingToFunctionField_comp_fromSpecStalk {y : W}
    (hy : jW.base (genericPoint V) ⤳ y) :
    Spec.map (curveLocalRingToFunctionField jW hy) ≫ W.fromSpecStalk y =
      V.fromSpecResidueField (genericPoint V) ≫ jW := by
  rw [curveLocalRingToFunctionField, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
  rfl

/-- **The geometric point `Spec Ω → Spec K^{sh} ≅ V ×_W Spec H → V`** is the geometric point
through the generic point of `V` given by a field embedding `κ(η_V) → Ω`, as soon as the two
composites `𝒪_{W,c} → Ω` agree. -/
theorem specMap_comp_inv_fst_eq_of_ringHom [Mono jW] {c : W}
    (hc : jW.base (genericPoint V) ⤳ c) {H : Type u} [CommRing H]
    (φ : W.presheaf.stalk c →+* H) (π : Spec (.of H) ⟶ W)
    (hπ : π = Spec.map (CommRingCat.ofHom φ) ≫ W.fromSpecStalk c)
    {Ksh : Type u} [CommRing Ksh] [Algebra H Ksh] (e : pullback jW π ≅ Spec (.of Ksh))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap H Ksh)) = pullback.snd jW π)
    {Ω : Type u} [CommRing Ω] (ι' : Ksh →+* Ω)
    (κ : V.residueField (genericPoint V) ⟶ CommRingCat.of Ω)
    (hring : ∀ r, ι' (algebraMap H Ksh (φ r)) =
      κ.hom ((curveLocalRingToFunctionField jW hc).hom r)) :
    Spec.map (CommRingCat.ofHom ι') ≫ e.inv ≫ pullback.fst jW π =
      Spec.map κ ≫ V.fromSpecResidueField (genericPoint V) := by
  rw [← cancel_mono jW]
  have h1 : e.inv ≫ pullback.snd jW π = Spec.map (CommRingCat.ofHom (algebraMap H Ksh)) := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h2 : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap H Ksh) ≫ CommRingCat.ofHom ι' =
      curveLocalRingToFunctionField jW hc ≫ κ := by
    ext r
    exact hring r
  calc (Spec.map (CommRingCat.ofHom ι') ≫ e.inv ≫ pullback.fst jW π) ≫ jW
      = Spec.map (CommRingCat.ofHom ι') ≫ (e.inv ≫ pullback.snd jW π) ≫ π := by
        simp only [Category.assoc, pullback.condition]
    _ = Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap H Ksh) ≫
          CommRingCat.ofHom ι') ≫ W.fromSpecStalk c := by
        rw [h1, hπ]
        simp only [Spec.map_comp, Category.assoc]
    _ = Spec.map κ ≫ Spec.map (curveLocalRingToFunctionField jW hc) ≫
          W.fromSpecStalk c := by
        rw [h2, Spec.map_comp, Category.assoc]
    _ = (Spec.map κ ≫ V.fromSpecResidueField (genericPoint V)) ≫ jW := by
        rw [specMap_curveLocalRingToFunctionField_comp_fromSpecStalk, Category.assoc]

end Curve

/-! ### Endomorphisms of a base change which is the spectrum of a field -/

/-- **An endomorphism of a scheme isomorphic to `Spec K^{sh}`, lying over the spectrum of a ring
endomorphism `θ` of `H`, is the spectrum of an endomorphism of `K^{sh}` extending `θ`.** -/
theorem exists_ringHom_specMap_eq_conj {X : Scheme.{u}} {H Ksh : Type u} [CommRing H]
    [CommRing Ksh] [Algebra H Ksh] (snd : X ⟶ Spec (.of H)) (e : X ≅ Spec (.of Ksh))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap H Ksh)) = snd) (b : X ⟶ X)
    (θ : H →+* H) (hb : b ≫ snd = snd ≫ Spec.map (CommRingCat.ofHom θ)) :
    ∃ c : Ksh →+* Ksh, Spec.map (CommRingCat.ofHom c) = e.inv ≫ b ≫ e.hom ∧
      ∀ h, c (algebraMap H Ksh h) = algebraMap H Ksh (θ h) := by
  refine ⟨(Spec.preimage (e.inv ≫ b ≫ e.hom)).hom, Spec.map_preimage _, fun h => ?_⟩
  have key : CommRingCat.ofHom (algebraMap H Ksh) ≫
      CommRingCat.ofHom (Spec.preimage (e.inv ≫ b ≫ e.hom)).hom =
      CommRingCat.ofHom θ ≫ CommRingCat.ofHom (algebraMap H Ksh) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage,
      Category.assoc, Category.assoc, he, hb, ← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun g => g.hom h) key

/-! ### The Frobenius on the étale local ring -/

/-- **The residue map of the endomorphism of the étale local ring induced by an endomorphism `a`
of the geometric point** is read off the action of `a` on the field of the geometric point: if
that action is inverse to the `Q`-th power map, so is the residue map. -/
theorem residue_etaleLocalRingEndomorphism_pow (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {s : GeometricPoint S} (a : GeometricPoint.Hom s s) (Q : ℕ)
    (hQ : ∀ z : s.residueField, (Spec.preimage a.hom).hom z ^ Q = z)
    (h : etaleLocalRing B S hS s) :
    residue _ ((etaleLocalRingEndomorphism B S hS a).hom h) ^ Q = residue _ h := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  by_contra hm
  apply ((IsLocalRing.notMem_maximalIdeal.mp hm).map
    (structureSheafStalkToGeometricField B S hS s)).ne_zero
  have h1 := RingHom.congr_fun
    (structureSheafStalkToGeometricField_comp_etaleLocalRingEndomorphism B S hS a) h
  rw [RingHom.comp_apply, RingHom.comp_apply] at h1
  rw [map_sub, map_pow, h1, hQ, sub_self]

/-- The geometric Frobenius at a point with finite residue field raises to the power `#κ(x)` to
the identity. -/
theorem frobeniusPointHom_preimage_pow (X : Scheme.{u}) (x : X) [Finite (X.residueField x)]
    (z : (Stacks.Frobenius.geometricPointAt X x).residueField) :
    (Spec.preimage (Stacks.Frobenius.frobeniusPointHom X x).hom).hom z ^
      Nat.card (X.residueField x) = z := by
  rw [Stacks.Frobenius.frobeniusPointHom_hom, Spec.preimage_map]
  change Stacks.Frobenius.residueGeometricFrobenius X x z ^ Nat.card (X.residueField x) = z
  rw [← Stacks.Frobenius.residueGeometricFrobenius_symm_apply, AlgEquiv.symm_apply_apply]

/-! ### Elements given by automorphisms of the source of a geometric point -/

/-- The element of an automorphism of the source depends only on its underlying morphism. -/
theorem GeometricPoint.sourceAutElement_congr {S : Scheme.{u}} [ConnectedSpace S]
    (z : GeometricPoint S) {α α' : z.source ≅ z.source} (h : α.hom = α'.hom)
    (hα : α.hom ≫ z.hom = z.hom) :
    z.sourceAutElement α hα = z.sourceAutElement α' (h ▸ hα) := by
  obtain rfl : α = α' := Iso.ext h
  rfl

/-- **The elements given by automorphisms of the source are multiplicative**: the composite
`α ≫ β` gives the product of the elements of `α` and of `β`. -/
theorem GeometricPoint.sourceAutElement_trans {S : Scheme.{u}} [ConnectedSpace S]
    (z : GeometricPoint S) (α β : z.source ≅ z.source) (hα : α.hom ≫ z.hom = z.hom)
    (hβ : β.hom ≫ z.hom = z.hom) :
    z.sourceAutElement (α ≪≫ β) (by rw [Iso.trans_hom, Category.assoc, hβ, hα]) =
      z.sourceAutElement α hα * z.sourceAutElement β hβ := by
  refine Iso.ext (NatTrans.ext (funext fun _ => ?_))
  ext q
  refine Subtype.ext ?_
  change (α.hom ≫ β.hom) ≫ q.1 = α.hom ≫ β.hom ≫ q.1
  rw [Category.assoc]

/-- **Transport of the element of an automorphism of the source along an equality of geometric
points.** -/
theorem etaleFundamentalGroupMulEquiv_eqToIso_sourceAutElement {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {f f' : Spec (.of Ω) ⟶ S} (h : f = f')
    (α : Spec (.of Ω) ≅ Spec (.of Ω)) (hα : α.hom ≫ f = f) :
    etaleFundamentalGroupMulEquiv (eqToIso (congrArg (fun f =>
        finiteEtaleFiberFunctor (⟨Ω, f⟩ : GeometricPoint S)) h))
      ((⟨Ω, f⟩ : GeometricPoint S).sourceAutElement α hα) =
      (⟨Ω, f'⟩ : GeometricPoint S).sourceAutElement α (h ▸ hα) := by
  subst h
  exact Iso.ext (NatTrans.ext (funext fun _ => rfl))

/-! ### Algebraicity of a geometric point of the spectrum of a field -/

attribute [local instance] GeometricPoint.residueFieldAlgebra in
/-- **The geometric point `Spec Ω → Spec K` given by an algebraic field extension is
algebraic.** -/
theorem isAlgebraic_specMap_geometricPoint {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]
    (ι : K →+* Ω) (halg : letI := ι.toAlgebra; Algebra.IsAlgebraic K Ω) :
    (⟨Ω, Spec.map (CommRingCat.ofHom ι)⟩ : GeometricPoint (Spec (.of K))).IsAlgebraic := by
  let t : GeometricPoint (Spec (.of K)) := ⟨Ω, Spec.map (CommRingCat.ofHom ι)⟩
  let ζ : K →+* (Spec (.of K)).residueField (t.hom default) :=
    (Spec.preimage ((Spec (.of K)).fromSpecResidueField (t.hom default))).hom
  have hζ : (GeometricPoint.residueFieldHom t).comp ζ = ι := by
    have h' : Spec.map (CommRingCat.ofHom ζ ≫ CommRingCat.ofHom (GeometricPoint.residueFieldHom t))
        = Spec.map (CommRingCat.ofHom ι) := by
      rw [Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
      exact GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField t
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  let : Algebra K Ω := ι.toAlgebra
  let : Algebra K ((Spec (.of K)).residueField (t.hom default)) := ζ.toAlgebra
  let : Algebra ((Spec (.of K)).residueField (t.hom default)) Ω :=
    GeometricPoint.residueFieldAlgebra t
  have : IsScalarTower K ((Spec (.of K)).residueField (t.hom default)) Ω :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hζ x).symm
  have := halg
  exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K)
    (L := (Spec (.of K)).residueField (t.hom default))⟩

end Stacks.EtaleCohomology

end
