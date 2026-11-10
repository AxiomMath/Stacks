module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Algebra
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk

/-!
# The complete-intersection fibre locus, read on the scheme-theoretic fibre

Let `f : X ⟶ S` be a morphism of schemes and `x` a point of `X`. Stacks Tag 02V3 is about the
locus where the local ring of the *scheme-theoretic fibre* `X_{f x}` at `x` is a complete
intersection over the residue field `κ(f x)`. This file states that condition on the fibre
itself, identifies it with the condition on the residue-field base change of the stalk, and
deduces that the locus it cuts out commutes with arbitrary base change.

## Main definitions

* `Stacks.Tag02V3FibreStalk.IsCompleteIntersectionFibreStalkAt`: the local ring of the
  scheme-theoretic fibre of `f` at `x` is a complete intersection over `κ(f x)`.

## Main results

* `Stacks.Tag02V3FibreStalk.isCompleteIntersectionFibreStalkAt_iff`: that condition agrees with
  `AlgebraicGeometry.IsCompleteIntersectionFibreAt`.
* `Stacks.Tag02V3FibreStalk.completeIntersectionFibreStalkLocus_eq_preimage`: for `f` locally
  of finite type, the complete-intersection fibre locus commutes with arbitrary base change.

## Implementation notes

The identification is read off the presentation of the stalk of a fibre product,
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`, which supplies a ring map
`O_{X,x} ⊗_{O_{S,s}} O_{Spec κ(s), *} ⟶ O_{X_s, x}` restricting on *both* factors to the two
stalk maps and exhibiting its target as a localization of its source. The second restriction is
what makes the `κ(s)`-algebra structures agree, and it is the reason this file does not use
`AlgebraicGeometry.quotientStalk_bridge`, which proves the same isomorphism but exposes only
the first restriction and so cannot see the field action.

The map is in fact bijective, not merely a localization: the first restriction is surjective
because `X_s ⟶ X` is a preimmersion, and the source is a local ring because it is the fibre
quotient `O_{X,x}/m_s O_{X,x}` of a local ring by a proper ideal. A localization of a local ring
whose structure map is surjective is an isomorphism, which is
`Stacks.Tag02V3FibreStalk.algEquivOfIsLocalizationOfSurjective`.

Both occurrences of the fibre point are kept in the form `f.fiberι (f x) (f.asFiber x)` while
the isomorphism is built, because that is the shape in which the base-change presentation
delivers its rings; `AlgebraicGeometry.Scheme.Hom.fiberι_asFiber` is applied once at the end, at
the level of the proposition rather than of the types, which is why no transport appears.

The two renderings of Stacks Definition 00SD are reconciled by
`Stacks.SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection`, and the
change of ground field along the isomorphism `κ(f x) ≃ κ(O_{S, f x})` by
`Stacks.SyntomicLocus.IsCompleteIntersection.of_ringEquiv`.

## References

* [Stacks 02V3](https://stacks.math.columbia.edu/tag/02V3), Lemma 29.30.12.
* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD), Definition 10.135.5.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Tag02V3FibreStalk

section Pointwise

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The canonical identification of the residue field `κ(s)` with the stalk of `Spec κ(s)` at
the image of a point of the fibre over `s`. -/
def fibreFieldIso (s : S) (z : f.fiber s) :
    CommRingCat.of (S.residueField s) ≅
      (Spec (.of (S.residueField s))).presheaf.stalk (f.fiberToSpecResidueField s z) :=
  (stalkClosedPointIso (.of (S.residueField s))).symm ≪≫
    (Spec (.of (S.residueField s))).presheaf.stalkCongr
      (.of_eq (f.fiberToSpecResidueField_apply s z).symm)

/-- The residue field `κ(f x)` acts on the local ring of the scheme-theoretic fibre through the
structure morphism `X_{f x} ⟶ Spec κ(f x)` of the fibre. -/
@[instance_reducible]
def fibreStalkAlgebra (x : X) :
    Algebra (S.residueField (f x)) ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  ((fibreFieldIso f (f x) (f.asFiber x)).hom ≫
    (f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)).hom.toAlgebra

/-- The local ring of the scheme-theoretic fibre of `f` at `x` is a complete intersection over
the residue field of `f x`. -/
def IsCompleteIntersectionFibreStalkAt (x : X) : Prop :=
  let := fibreStalkAlgebra f x
  IsCompleteIntersectionLocalRing (S.residueField (f x))
    ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- A localization `C` of a local ring `T` at a submonoid `M`, with `C` local and the structure
map `T → C` surjective, is isomorphic to `T` as a `T`-algebra. -/
noncomputable def algEquivOfIsLocalizationOfSurjective {T C : Type u} [CommRing T] [CommRing C]
    [Algebra T C] [IsLocalRing T] [IsLocalRing C] (M : Submonoid T) [IsLocalization M C]
    (h : Function.Surjective (algebraMap T C)) : T ≃ₐ[T] C := by
  have : IsLocalHom (algebraMap T C) := IsLocalHom.of_surjective _ h
  have hM : M ≤ IsUnit.submonoid T := fun t ht =>
    (isUnit_map_iff (algebraMap T C) t).mp (IsLocalization.map_units C ⟨t, ht⟩)
  let : IsLocalization M T := IsLocalization.self hM
  exact IsLocalization.algEquiv M T C

/-- A surjective algebra map from a local ring onto a field identifies its residue field with
the field. -/
noncomputable def residueFieldAlgEquivOfSurjective {R B : Type*} [CommRing R] [IsLocalRing R]
    [Field B] [Algebra R B] (h : Function.Surjective (algebraMap R B)) :
    IsLocalRing.ResidueField R ≃ₐ[R] B :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal _ h).symm).trans
    (RingHom.quotientKerEquivOfSurjective h)) fun _ => rfl

/-- For a local homomorphism of local rings `R → A`, the fibre quotient `A ⧸ m_R A` is local. -/
theorem isLocalRing_quotient_map_maximalIdeal {R A : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)] :
    IsLocalRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
  have : Nontrivial (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.nontrivial_iff.mpr ((IsLocalRing.map_maximalIdeal_le (algebraMap R A)).trans_lt
      (IsLocalRing.maximalIdeal.isMaximal A).lt_top).ne
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The local ring of the scheme-theoretic fibre of `f` at `x` is a complete intersection over
`κ(f x)` if and only if `AlgebraicGeometry.IsCompleteIntersectionFibreAt` holds at the image
`f.fiberι (f x) (f.asFiber x)` of the fibre point of `x`. -/
theorem isCompleteIntersectionFibreStalkAt_iff_fiberι (x : X) :
    IsCompleteIntersectionFibreStalkAt f x ↔
      IsCompleteIntersectionFibreAt f (f.fiberι (f x) (f.asFiber x)) := by
  classical
  let s := f x
  let g := S.fromSpecResidueField s
  let x' : (Limits.pullback f g).carrier := f.asFiber x
  let pX : Limits.pullback f g ⟶ X := Limits.pullback.fst f g
  let pY : Limits.pullback f g ⟶ Spec (S.residueField s) := Limits.pullback.snd f g
  have h : (pX ≫ f).base x' = (pY ≫ g).base x' :=
    congrArg (fun k : Limits.pullback f g ⟶ S => k.base x') Limits.pullback.condition
  let R := S.presheaf.stalk ((pX ≫ f).base x')
  let A := X.presheaf.stalk (pX.base x')
  let B := (Spec (S.residueField s)).presheaf.stalk (pY.base x')
  let C := (Limits.pullback f g).presheaf.stalk x'
  let : Algebra R A := (f.stalkMap (pX.base x')).hom.toAlgebra
  let : Algebra R B :=
    ((eqToHom (congrArg S.presheaf.stalk h)) ≫ g.stalkMap (pY.base x')).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hM⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g x'
  let e := fibreFieldIso f s (f.asFiber x)
  let eK : ↥(CommRingCat.of (S.residueField s)) ≃+* B := e.commRingCatIsoToRingEquiv
  let : Field B := (eK.symm.toMulEquiv.isField (Field.toIsField _)).toField
  let eEq : R ≃+* S.presheaf.stalk (g (pY.base x')) :=
    (eqToIso (congrArg S.presheaf.stalk h)).commRingCatIsoToRingEquiv
  have hρ : Function.Surjective (algebraMap R B) := fun b => by
    obtain ⟨c, hc⟩ := g.stalkMap_surjective (pY.base x') b
    refine ⟨eEq.symm c, ?_⟩
    change (g.stalkMap (pY.base x')).hom (eEq (eEq.symm c)) = b
    rw [eEq.apply_symm_apply, hc]
  let eRB := residueFieldAlgEquivOfSurjective hρ
  let eT : TensorProduct R (IsLocalRing.ResidueField R) A ≃ₐ[R] TensorProduct R A B :=
    (Algebra.TensorProduct.comm R _ A).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A)) eRB)
  have : IsLocalHom (algebraMap R A) := f.toLRSHom.prop (pX.base x')
  have := isLocalRing_quotient_map_maximalIdeal (R := R) (A := A)
  have : IsLocalRing (TensorProduct R A B) :=
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (IsLocalRing.maximalIdeal R)).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := A)) eRB)).toRingEquiv.isLocalRing
  let : Algebra (TensorProduct R A B) C := φ.toAlgebra
  have hφ : Function.Surjective φ := fun c => by
    obtain ⟨a, ha⟩ := pX.stalkMap_surjective x' c
    exact ⟨Algebra.TensorProduct.includeLeft (R := R) (S := A) (A := A) (B := B) a,
      (DFunLike.congr_fun hleft a).trans ha⟩
  let eφ : TensorProduct R A B ≃ₐ[TensorProduct R A B] C :=
    algEquivOfIsLocalizationOfSurjective M hφ
  have heφ : ∀ t, eφ t = φ t := eφ.commutes
  let : Algebra ↥(S.residueField s) ↥C := (e.hom ≫ pY.stalkMap x').hom.toAlgebra
  have hcard : ∀ a : ↥(S.residueField s),
      algebraMap ↥(S.residueField s) ↥C a = (pY.stalkMap x').hom (eK a) := fun a => rfl
  let ek : IsLocalRing.ResidueField R ≃+* ↥(S.residueField s) := eRB.toRingEquiv.trans eK.symm
  let Φ : TensorProduct R (IsLocalRing.ResidueField R) A ≃+* C :=
    eT.toRingEquiv.trans eφ.toRingEquiv
  have hΦ : ∀ a : IsLocalRing.ResidueField R,
      Φ (algebraMap (IsLocalRing.ResidueField R)
          (TensorProduct R (IsLocalRing.ResidueField R) A) a) =
        algebraMap ↥(S.residueField s) ↥C (ek a) := by
    intro a
    have h1 : Φ (algebraMap (IsLocalRing.ResidueField R)
        (TensorProduct R (IsLocalRing.ResidueField R) A) a)
        = φ (Algebra.TensorProduct.includeRight (eRB a)) := by
      change eφ (eT (algebraMap _ _ a)) = _
      rw [heφ]
      congr 1
    have h2 : φ (Algebra.TensorProduct.includeRight (eRB a)) = (pY.stalkMap x').hom (eRB a) :=
      DFunLike.congr_fun hright (eRB a)
    rw [h1, h2, hcard]
    exact congrArg _ (eK.apply_symm_apply (eRB a)).symm
  have hiff := SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection
    ↥(S.residueField s) ↥C
  refine ⟨fun hL => SyntomicLocus.IsCompleteIntersection.of_ringEquiv ek.symm Φ.symm
    (fun a => ?_) (hiff.mp hL), fun hR =>
      hiff.mpr (SyntomicLocus.IsCompleteIntersection.of_ringEquiv ek Φ hΦ hR)⟩
  have hcmp := hΦ (ek.symm a)
  rw [ek.apply_symm_apply] at hcmp
  exact Φ.symm_apply_eq.mpr hcmp.symm

/-- The condition read on the scheme-theoretic fibre agrees with
`AlgebraicGeometry.IsCompleteIntersectionFibreAt`, which reads it on the residue-field base
change of the stalk of `X` at `x`. -/
theorem isCompleteIntersectionFibreStalkAt_iff (x : X) :
    IsCompleteIntersectionFibreStalkAt f x ↔ IsCompleteIntersectionFibreAt f x :=
  (isCompleteIntersectionFibreStalkAt_iff_fiberι f x).trans
    (by rw [Scheme.Hom.fiberι_asFiber])

end Pointwise

/-- For a morphism locally of finite type, the locus of points where the local ring of the
scheme-theoretic fibre is a complete intersection over the residue field of the image commutes
with arbitrary base change: if the square `g'`, `f'`, `f`, `g` is cartesian then that locus for
`f'` is the `g'`-preimage of the locus for `f`. -/
theorem completeIntersectionFibreStalkLocus_eq_preimage {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    [LocallyOfFiniteType f] :
    {x' : X' | IsCompleteIntersectionFibreStalkAt f' x'} =
      g' ⁻¹' {x : X | IsCompleteIntersectionFibreStalkAt f x} := by
  ext x'
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    isCompleteIntersectionFibreStalkAt_iff f' x',
    isCompleteIntersectionFibreStalkAt_iff f (g' x')]
  exact isCompleteIntersectionFibreAt_baseChange_iff g' f' f g hpb x'

/-- For a cartesian square `g'`, `f'`, `f`, `g` with `f` locally of finite type, the set of
points of `X'` at which the local ring of the scheme-theoretic fibre of `f'` is a complete
intersection over the residue field of the image is the `g'`-preimage of the corresponding set
for `f`. -/
example {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hpb : IsPullback g' f' f g)
    [LocallyOfFiniteType f] :
    {x' : X' |
        let k := S'.residueField (f' x')
        let fs := f'.fiberToSpecResidueField (f' x')
        let xf := f'.asFiber x'
        let B := (f'.fiber (f' x')).presheaf.stalk xf
        let e : CommRingCat.of k ≅ (Spec (.of k)).presheaf.stalk (fs xf) :=
          (stalkClosedPointIso (.of k)).symm ≪≫
            (Spec (.of k)).presheaf.stalkCongr
              (.of_eq (f'.fiberToSpecResidueField_apply (f' x') xf).symm)
        letI : Algebra k B := (e.hom ≫ fs.stalkMap xf).hom.toAlgebra
        IsCompleteIntersectionLocalRing k B} =
      g' ⁻¹' {x : X |
        let k := S.residueField (f x)
        let fs := f.fiberToSpecResidueField (f x)
        let xf := f.asFiber x
        let B := (f.fiber (f x)).presheaf.stalk xf
        let e : CommRingCat.of k ≅ (Spec (.of k)).presheaf.stalk (fs xf) :=
          (stalkClosedPointIso (.of k)).symm ≪≫
            (Spec (.of k)).presheaf.stalkCongr
              (.of_eq (f.fiberToSpecResidueField_apply (f x) xf).symm)
        letI : Algebra k B := (e.hom ≫ fs.stalkMap xf).hom.toAlgebra
        IsCompleteIntersectionLocalRing k B} :=
  completeIntersectionFibreStalkLocus_eq_preimage g' f' f g hpb

end Stacks.Tag02V3FibreStalk

add_to_stacks 02V3 "complete-intersection fibre locus"
  Stacks.Tag02V3FibreStalk.completeIntersectionFibreStalkLocus_eq_preimage
add_to_ega "IV 19.3.4" Stacks.Tag02V3FibreStalk.completeIntersectionFibreStalkLocus_eq_preimage

end
