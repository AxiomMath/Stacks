module

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric regularity upstairs, for an arbitrary scheme

Let `k` be a field, `X` a scheme over `k`, `k'/k` a finitely generated field extension, `x ∈ X`
and `x' ∈ X_{k'}` a point lying over `x`. Then `X` is geometrically regular at `x` over `k` if
and only if `X_{k'}` is geometrically regular at `x'` over `k'`; consequently `X` is
geometrically regular over `k` if and only if `X_{k'}` is geometrically regular over `k'`.

## Main results

* `AlgebraicGeometry.isGeometricallyRegularAt_baseChange_iff` is the pointwise equivalence.
* `AlgebraicGeometry.isGeometricallyRegular_baseChange_iff` is the equivalence for schemes.

## Implementation notes

The source states the lemma for a scheme `X` over `k`, and these results take no further
hypothesis on `X`; in particular no `IsLocallyNoetherian X` is assumed. (The equivalence
`AlgebraicGeometry.geometricallyRegularAt_baseChange_iff` is the special case for a locally
Noetherian `X`, whose proof goes through Tag 038U.)

The implication from `X` to `X_{k'}` composes the two base changes. For the converse, let `K/k`
be finitely generated and `z ∈ X_K` lie over `x`. The source chooses a common finitely generated
extension of `k'` and `K` together with a point above both `x'` and `z`. Here such a point is
found by taking a point `p` of `X_{k'} ×_X X_K` over `x'` and `z`: its residue field `Ω`
receives `k'` and `K` compatibly over `k`, and the fraction field `M` of the image of
`k' ⊗_k K` in `Ω` is a common extension finitely generated over `k'`. The point `p` then gives
a point `w` of `(X_{k'})_M` lying over `x'` and mapping to `z` under the flat comparison
morphism `(X_{k'})_M ⟶ X_K`. The local ring at `w` is regular by assumption, the local map of
stalks is flat, hence faithfully flat, so the local ring at `z` is Noetherian (Tag 033E) and
then regular (Tag 00OF).

## References

* [Stacks Project, Tag 038W](https://stacks.math.columbia.edu/tag/038W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Two extensions `k'` and `K` of a field `k`, embedded in a field `Ω` compatibly over `k`, have
a common extension `M` inside `Ω` which is finitely generated over `k'` when `K/k` is
finitely generated. -/
private lemma exists_essFiniteType_extension_into
    {k k' K Ω : Type u} [Field k] [Field k'] [Field K] [Field Ω]
    [Algebra k k'] [Algebra k K] [Algebra.EssFiniteType k K]
    (α : k' →+* Ω) (β : K →+* Ω)
    (hαβ : α.comp (algebraMap k k') = β.comp (algebraMap k K)) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra k M) (_ : Algebra k' M) (_ : Algebra K M)
      (_ : IsScalarTower k k' M) (_ : IsScalarTower k K M) (γ : M →+* Ω),
      Algebra.EssFiniteType k' M ∧ γ.comp (algebraMap k' M) = α ∧
        γ.comp (algebraMap K M) = β := by
  let : Algebra k Ω := (α.comp (algebraMap k k')).toAlgebra
  let αₐ : k' →ₐ[k] Ω := { α with commutes' := fun _ ↦ rfl }
  let βₐ : K →ₐ[k] Ω :=
    { β with commutes' := fun a ↦ (RingHom.congr_fun hαβ a).symm }
  let g : k' ⊗[k] K →+* Ω := (Algebra.TensorProduct.productMap αₐ βₐ).toRingHom
  have : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let M := FractionRing (k' ⊗[k] K ⧸ RingHom.ker g)
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, IsFractionRing.lift (RingHom.kerLift_injective g), inferInstance, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    rw [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply k' (k' ⊗[k] K ⧸ RingHom.ker g) M,
      IsFractionRing.lift_algebraMap]
    show g (algebraMap k' (k' ⊗[k] K) a) = α a
    simp [g, αₐ, βₐ, Algebra.TensorProduct.algebraMap_apply]
  · refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply K (k' ⊗[k] K ⧸ RingHom.ker g) M,
      IsFractionRing.lift_algebraMap]
    show g (1 ⊗ₜ b) = β b
    simp [g, αₐ, βₐ]

/-- The comparison morphism between two base changes along legs of one composite is compatible
with the projections to the second leg. -/
private lemma iteratedBaseChangeComparison_snd {S T U V W : Scheme.{u}}
    (f : S ⟶ T) (φ : U ⟶ T) (ψ : V ⟶ T)
    (χU : W ⟶ U) (χV : W ⟶ V) (μ : W ⟶ T)
    (hU : χU ≫ φ = μ) (hV : χV ≫ ψ = μ) :
    iteratedBaseChangeComparison f φ ψ χU χV μ hU hV ≫ pullback.snd f ψ =
      pullback.snd (pullback.snd f φ) χU ≫ χV := by
  have hinv : (iteratedBaseChangeIso f ψ χV μ hV).inv ≫
      pullback.snd (pullback.snd f ψ) χV = pullback.snd f μ := by
    rw [Iso.inv_comp_eq, iteratedBaseChangeIso_snd]
  dsimp [iteratedBaseChangeComparison]
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ _ χV,
    hinv, ← Category.assoc, iteratedBaseChangeIso_snd]

/-- Geometric regularity at a point passes to any point above it after a finitely generated
base change, for an arbitrary scheme. -/
private lemma isGeometricallyRegularAt_baseChange_of_isGeometricallyRegularAt'
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u}))
    (hx' : pullback.fst f (Spec.map (ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyRegularAt f x) :
    IsGeometricallyRegularAt
      (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x' := by
  let φ : Spec (.of k') ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k k'))
  intro L _ _ _ ψ z hz
  let : Algebra k L := RingHom.toAlgebra ((algebraMap k' L).comp (algebraMap k k'))
  let : IsScalarTower k k' L := .of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k k' L
  let μ : Spec (.of L) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k L))
  have hcomp : ψ ≫ φ = μ := specMap_algebraMap_comp k k' L
  let e := iteratedBaseChangeIso f φ ψ μ hcomp
  have he : e.hom ≫ pullback.fst f μ =
      pullback.fst (pullback.snd f φ) ψ ≫ pullback.fst f φ :=
    iteratedBaseChangeIso_fst f φ ψ μ hcomp
  have hz' : pullback.fst f μ (e.hom z) = x := by
    rw [← hx', ← hz]
    exact congrArg (fun g ↦ g.base.hom z) he
  have hzA : e.inv (e.hom z) = z := by
    show (e.hom ≫ e.inv) z = z
    rw [e.hom_inv_id]
    rfl
  have hregA : IsRegularLocalRing
      ((pullback (pullback.snd f φ) ψ).presheaf.stalk (e.inv (e.hom z))) := by
    have : IsRegularLocalRing ((pullback f μ).presheaf.stalk (e.hom z)) := h L (e.hom z) hz'
    exact IsRegularLocalRing.of_ringEquiv
      ((asIso (e.inv.stalkMap (e.hom z))).commRingCatIsoToRingEquiv.symm)
  rwa [hzA] at hregA

/-- Geometric regularity at a point of a finitely generated base change descends to the point
below it, for an arbitrary scheme. -/
private lemma isGeometricallyRegularAt_of_baseChange'
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u}))
    (hx' : pullback.fst f (Spec.map (ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyRegularAt
      (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x') :
    IsGeometricallyRegularAt f x := by
  let φ : Spec (.of k') ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k k'))
  intro K _ _ _ ψ z hz
  -- A point of `X_{k'} ×_X X_K` above `x'` and `z`, and its residue field `Ω`.
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.fst f φ) (g := pullback.fst f ψ) x' z (hx'.trans hz.symm)
  let P := pullback (pullback.fst f φ) (pullback.fst f ψ)
  let Ω := P.residueField p
  let ω' : Spec Ω ⟶ pullback f φ := P.fromSpecResidueField p ≫ pullback.fst _ _
  let ωK : Spec Ω ⟶ pullback f ψ := P.fromSpecResidueField p ≫ pullback.snd _ _
  have hω : ω' ≫ pullback.fst f φ = ωK ≫ pullback.fst f ψ := by
    simp only [ω', ωK, Category.assoc, pullback.condition]
  let α : k' →+* Ω := (Spec.preimage (ω' ≫ pullback.snd f φ)).hom
  let β : K →+* Ω := (Spec.preimage (ωK ≫ pullback.snd f ψ)).hom
  have hα : Spec.map (ofHom α) = ω' ≫ pullback.snd f φ := by simp [α]
  have hβ : Spec.map (ofHom β) = ωK ≫ pullback.snd f ψ := by simp [β]
  have hαβ : α.comp (algebraMap k k') = β.comp (algebraMap k K) := by
    have hspec : Spec.map (ofHom (α.comp (algebraMap k k'))) =
        Spec.map (ofHom (β.comp (algebraMap k K))) := by
      rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, hα, hβ,
        Category.assoc, Category.assoc]
      show ω' ≫ pullback.snd f φ ≫ φ = ωK ≫ pullback.snd f ψ ≫ ψ
      rw [← pullback.condition, ← pullback.condition, ← Category.assoc, hω, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
  -- A common extension `M` of `k'` and `K` inside `Ω`, finitely generated over `k'`.
  obtain ⟨M, _, _, _, _, _, _, γ, _, hγα, hγβ⟩ := exists_essFiniteType_extension_into α β hαβ
  let χK : Spec (.of M) ⟶ Spec (.of k') := Spec.map (ofHom (algebraMap k' M))
  let χE : Spec (.of M) ⟶ Spec (.of K) := Spec.map (ofHom (algebraMap K M))
  let μ : Spec (.of M) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k M))
  have hcompK : χK ≫ φ = μ := specMap_algebraMap_comp k k' M
  have hcompE : χE ≫ ψ = μ := specMap_algebraMap_comp k K M
  let ι : Spec Ω ⟶ Spec (.of M) := Spec.map (ofHom γ)
  have hιK : ι ≫ χK = ω' ≫ pullback.snd f φ := by
    rw [← hα, ← hγα, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  have hιE : ι ≫ χE = ωK ≫ pullback.snd f ψ := by
    rw [← hβ, ← hγβ, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  -- The point `w` of `(X_{k'})_M` above `x'` and above `z`.
  let A : Scheme.{u} := pullback (pullback.snd f φ) χK
  let l : Spec Ω ⟶ A := pullback.lift ω' ι hιK.symm
  let r : A ⟶ pullback f ψ := iteratedBaseChangeComparison f φ ψ χK χE μ hcompK hcompE
  have hlr : l ≫ r = ωK := by
    apply pullback.hom_ext
    · rw [Category.assoc, iteratedBaseChangeComparison_fst, pullback.lift_fst_assoc, hω]
    · rw [Category.assoc, iteratedBaseChangeComparison_snd, pullback.lift_snd_assoc, hιE]
  let s : Spec Ω := IsLocalRing.closedPoint Ω
  let w : A := l s
  have hw : pullback.fst (pullback.snd f φ) χK w = x' := by
    rw [← hp₁]
    show (l ≫ pullback.fst _ _) s = _
    rw [pullback.lift_fst, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hrw : r w = z := by
    rw [← hp₂]
    show (l ≫ r) s = _
    rw [hlr, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  -- Regularity descends along the flat local map of stalks.
  have hregA : IsRegularLocalRing (A.presheaf.stalk w) := h M w hw
  have hrflat : Flat r := by
    dsimp [r, iteratedBaseChangeComparison]
    infer_instance
  let R := (pullback f ψ).presheaf.stalk (r w)
  let S := A.presheaf.stalk w
  let : Algebra R S := (r.stalkMap w).hom.toAlgebra
  let : Module.Flat R S := Flat.stalkMap r w
  let : IsLocalHom (algebraMap R S) := r.toLRSHom.prop w
  have : IsRegularLocalRing S := hregA
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsNoetherianRing R :=
    Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
      (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)
  rw [← hrw]
  exact IsRegularLocalRing.of_flat_of_isLocalHom S

/-- **Stacks Project, Tag 038W, the equivalence.** Let `k` be a field, `X` a scheme over `k`,
`k'/k` a finitely generated field extension, `x ∈ X`, and `x' ∈ X_{k'}` a point lying over `x`.
Then `X` is geometrically regular at `x` over `k` if and only if `X_{k'}` is geometrically
regular at `x'` over `k'`. -/
@[stacks 038W "the equivalence of (1) and (2), for any scheme over k", ega "IV 6.7.8" "clause (iv)"]
public theorem isGeometricallyRegularAt_baseChange_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u}))
    (hx' : pullback.fst f (Spec.map (ofHom (algebraMap k k'))) x' = x) :
    IsGeometricallyRegularAt f x ↔
      IsGeometricallyRegularAt (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x' :=
  ⟨isGeometricallyRegularAt_baseChange_of_isGeometricallyRegularAt' k k' X f x x' hx',
    isGeometricallyRegularAt_of_baseChange' k k' X f x x' hx'⟩

/-- **Stacks Project, Tag 038W, the consequence for schemes.** Let `k` be a field, `X` a scheme
over `k` and `k'/k` a finitely generated field extension. Then `X` is geometrically regular
over `k` if and only if `X_{k'}` is geometrically regular over `k'`. -/
@[stacks 038W "in particular: X geometrically regular over k iff X_{k'} is over k'",
  ega "IV 7.3.10" "special case",
  ega "IV 7.3.8" "partial"]
public theorem isGeometricallyRegular_baseChange_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsGeometricallyRegular f ↔
      IsGeometricallyRegular (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) := by
  refine ⟨fun h x' ↦ (isGeometricallyRegularAt_baseChange_iff k k' X f _ x' rfl).mp (h _),
    fun h x ↦ ?_⟩
  obtain ⟨x', hx'⟩ := (pullback.fst f (Spec.map (ofHom (algebraMap k k')))).surjective x
  exact (isGeometricallyRegularAt_baseChange_iff k k' X f x x' hx').mpr (h x')

end AlgebraicGeometry
