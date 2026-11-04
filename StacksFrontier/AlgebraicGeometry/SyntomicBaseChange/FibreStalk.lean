module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.SyntomicLocus.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two renderings of the closed fibre of a morphism of schemes agree

Let `f : X ⟶ S` be a morphism of schemes and `x` a point of `X`.  The local ring of the closed
fibre of `f` at `x` admits two descriptions, and the draft carries both:

* the *tensor* description `κ(f x) ⊗_{𝒪_{S, f x}} 𝒪_{X, x}`, used by
  `AlgebraicGeometry.IsCompleteIntersectionFibreAt`, which mentions only the two stalks of `f`;
* the *fibre-stalk* description `𝒪_{X_{f x}, x}`, the stalk at `f.asFiber x` of the
  scheme-theoretic fibre `f.fiber (f x)`, which is a `κ(f x)`-algebra through the structural
  morphism `f.fiberToSpecResidueField (f x)` of the fibre.

This file identifies the two *as `κ(f x)`-algebras* and deduces that the two complete-intersection
conditions they carry are the same.  The `κ(f x)`-algebra structure is the whole content: the
underlying rings are identified by `AlgebraicGeometry.quotientStalkEquivFiberStalk` together with
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, but neither of those knows about the residue
field of `S` at `f x`, and the fibre-stalk side receives its residue-field action from the
structural morphism of the fibre, not from the stalk map of `f`.

## Main definitions

* `AlgebraicGeometry.residueFieldSpecStalkIso`: for a local ring `R` and the (unique) point `p` of
  `Spec R` given by its maximal ideal, the isomorphism `R ≅ 𝒪_{Spec R, p}`.
* `AlgebraicGeometry.residueFieldToFibreStalk`: the structural morphism
  `κ(f x) ⟶ 𝒪_{X_{f x}, x}`.
* `AlgebraicGeometry.fibreStalkAlgebra`: the `κ(f x)`-algebra structure it defines on the fibre
  stalk.
* `AlgebraicGeometry.fibreStalkAlgEquiv`: the comparison
  `κ(f x) ⊗_{𝒪_{S, f x}} 𝒪_{X, x} ≃ₐ[κ(f x)] 𝒪_{X_{f x}, x}`.
* `AlgebraicGeometry.IsCompleteIntersectionFibreStalkAt`: the closed-fibre complete-intersection
  condition in the fibre-stalk rendering.

## Main results

* `AlgebraicGeometry.stalkMap_fromSpecResidueField_closedPoint`: the stalk map of
  `Spec κ(x) ⟶ X` at the closed point is the residue map.
* `AlgebraicGeometry.residue_comp_residueFieldSpecStalkIso`: the same statement transported to an
  arbitrary point of `Spec κ(x)`, which is the form the fibre needs.
* `AlgebraicGeometry.residue_comp_residueFieldToFibreStalk`: **the comparison square.** The
  residue-field action on the fibre stalk is computed by the stalk map of `f` followed by the
  stalk map of the inclusion of the fibre.
* `AlgebraicGeometry.isCompleteIntersectionFibreStalkAt_iff`: the two renderings of the
  closed-fibre complete-intersection condition agree.
* `AlgebraicGeometry.isSyntomicAt_iff_isCompleteIntersectionFibreStalkAt`: Stacks Lemma 01UE in
  the fibre-stalk rendering.

## Implementation notes

Every statement below is written in **one** spelling of the residue field, namely
`IsLocalRing.ResidueField (S.presheaf.stalk (f x))`, which is the spelling
`AlgebraicGeometry.IsCompleteIntersectionFibreAt` uses.  The bundled spelling
`S.residueField (f x) : CommRingCat` is definitionally the same type with the same ring structure,
but it is not syntactically the same, and `rw`/`simp` cannot cross the boundary.  Accordingly
`fibreStalkAlgebra` is a `def` with an **ascribed** result type rather than a direct use of
`RingHom.toAlgebra`: the ascription is what pins the spelling, and a bare type ascription on the
term would not.

For the same reason no step of `residue_comp_residueFieldSpecStalkIso` or
`residue_comp_residueFieldToFibreStalk` rewrites underneath
`IsLocalRing.closedPoint ↥(S.residueField (f x))`.  That term has type
`PrimeSpectrum ↥(S.residueField (f x))` where `↥(Spec (S.residueField (f x)))` is expected, so a
goal mentioning it is not type-correct at `implicit` transparency and `kabstract` refuses; the
relevant steps are therefore taken with `Eq.trans` and `congrArg`, which are defeq-tolerant.  This
is why no `set_option backward.isDefEq.respectTransparency` is needed anywhere in the file.

`residueFieldSpecStalkIso` takes the point `p` and a proof `closedPoint R = p` rather than being
stated at `closedPoint R` itself: at the point of use `p` is
`f.fiberToSpecResidueField (f x) (f.asFiber x)`, and `Spec` of a field is a singleton, so the
hypothesis is `(f.fiberToSpecResidueField_apply _ _).symm`.

The comparison `fibreStalkAlgEquiv` is assembled from a *ring* equivalence and upgraded by
`AlgEquiv.ofRingEquiv`; the intermediate quotient `𝒪_{X, x} / 𝔪_{S, f x} 𝒪_{X, x}` is never given
a residue-field algebra structure.  Supplying one through
`Ideal.Quotient.algebraQuotientMapQuotient` is possible but exhausts the default heartbeat budget
while unifying `Ideal.map (algebraMap _ _) _` with `Ideal.map (f.stalkMap x).hom _`, and it is not
needed: the `κ(f x)`-linearity of the composite is checked on `Ideal.Quotient.mk`-representatives.

## References

* [Stacks 02V3](https://stacks.math.columbia.edu/tag/02V3), Lemma 29.30.12.
* [Stacks 01UE](https://stacks.math.columbia.edu/tag/01UE), Lemma 29.30.11.
* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD), Definition 10.135.5.
-/

@[expose] public section

open CategoryTheory IsLocalRing TopologicalSpace

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The residue map of a scheme at a point is a local homomorphism.  This is
`IsLocalRing.isLocalHom_residue` read through `CommRingCat`; instance search does not find it
there, because the head of `(X.residue x).hom` is `CommRingCat.Hom.hom`. -/
theorem isLocalHom_residue (X : Scheme.{u}) (x : X) : IsLocalHom (X.residue x).hom :=
  inferInstanceAs (IsLocalHom (IsLocalRing.residue (X.presheaf.stalk x)))

/-- **The stalk map of `Spec κ(x) ⟶ X` at the closed point is the residue map.** -/
theorem stalkMap_fromSpecResidueField_closedPoint (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).stalkMap (closedPoint (X.residueField x)) ≫
        (stalkClosedPointIso (X.residueField x)).hom =
      (X.presheaf.stalkCongr (.of_eq
        (X.fromSpecResidueField_apply x (closedPoint (X.residueField x))))).hom ≫
        X.residue x := by
  have := isLocalHom_residue X x
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  refine (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (X.residue x) U hU).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (fun t ↦ t ≫ X.residue x) ?_
  refine Eq.trans ?_ (congrArg (fun t ↦ X.presheaf.germ U _ hU ≫ t)
    (X.presheaf.stalkCongr_hom _).symm)
  exact (TopCat.Presheaf.germ_stalkSpecializes _ hU _).symm

/-- For a local ring `R` and a point `p` of `Spec R` equal to the closed point, the canonical
isomorphism from `R` to the stalk of `Spec R` at `p`.

The point is taken as data, with the equality as a hypothesis, because the point this is applied
to is the image of a point of a scheme-theoretic fibre under the structural morphism of that
fibre, which is the closed point only propositionally. -/
noncomputable def residueFieldSpecStalkIso (R : CommRingCat.{u}) [IsLocalRing R]
    (p : Spec R) (h : closedPoint R = p) : R ≅ (Spec R).presheaf.stalk p :=
  (stalkClosedPointIso R).symm ≪≫ (Spec R).presheaf.stalkCongr (.of_eq h)

/-- **`residueFieldSpecStalkIso` computes the stalk map of `Spec κ(x) ⟶ X`.** This is
`stalkMap_fromSpecResidueField_closedPoint` transported from the closed point of `Spec κ(x)` to
an arbitrary point of it. -/
theorem residue_comp_residueFieldSpecStalkIso (X : Scheme.{u}) (x : X)
    (p : Spec (X.residueField x)) (h : closedPoint (X.residueField x) = p) :
    X.residue x ≫ (residueFieldSpecStalkIso (X.residueField x) p h).hom =
      (X.presheaf.stalkCongr (.of_eq (X.fromSpecResidueField_apply x p).symm)).hom ≫
        (X.fromSpecResidueField x).stalkMap p := by
  subst h
  have hsc : ((Spec (X.residueField x)).presheaf.stalkCongr
      (Inseparable.of_eq (rfl : closedPoint (X.residueField x) = _))).hom = 𝟙 _ :=
    ((Spec (X.residueField x)).presheaf.stalkCongr_hom _).trans
      ((Spec (X.residueField x)).presheaf.stalkSpecializes_refl _)
  have h1 : (residueFieldSpecStalkIso (X.residueField x) _ rfl).hom =
      (stalkClosedPointIso (X.residueField x)).inv :=
    (congrArg (fun t ↦ (stalkClosedPointIso (X.residueField x)).inv ≫ t) hsc).trans
      (Category.comp_id _)
  have e := (X.presheaf.stalkCongr (Inseparable.of_eq
    (X.fromSpecResidueField_apply x (closedPoint (X.residueField x))))).inv_hom_id
  rw [h1, Iso.comp_inv_eq, Category.assoc, stalkMap_fromSpecResidueField_closedPoint,
    ← Category.assoc]
  exact (Category.id_comp _).symm.trans (congrArg (fun t ↦ t ≫ X.residue x) e.symm)

/-- Two canonical identifications of stalks at propositionally equal points compose to the third.
This is `TopCat.Presheaf.stalkSpecializes_comp` read through `TopCat.Presheaf.stalkCongr`; it holds
for the given proofs by proof irrelevance. -/
theorem stalkCongr_trans {Z : Scheme.{u}} {a b c : Z}
    (h₁ : Inseparable a b) (h₂ : Inseparable b c) (h₃ : Inseparable a c) :
    (Z.presheaf.stalkCongr h₁).hom ≫ (Z.presheaf.stalkCongr h₂).hom =
      (Z.presheaf.stalkCongr h₃).hom :=
  TopCat.Presheaf.stalkSpecializes_comp Z.presheaf h₂.ge h₁.ge

variable {X S : Scheme.{u}}

/-- The structural morphism `κ(f x) ⟶ 𝒪_{X_{f x}, x}` making the local ring of the closed fibre
of `f` at `x` an algebra over the residue field of `f x`: the stalk map at `f.asFiber x` of the
structural morphism `f.fiber (f x) ⟶ Spec κ(f x)` of the fibre, read through
`residueFieldSpecStalkIso`. -/
noncomputable def residueFieldToFibreStalk (f : X ⟶ S) (x : X) :
    S.residueField (f x) ⟶ (f.fiber (f x)).presheaf.stalk (f.asFiber x) :=
  (residueFieldSpecStalkIso (S.residueField (f x)) (f.fiberToSpecResidueField (f x) (f.asFiber x))
      (f.fiberToSpecResidueField_apply (f x) (f.asFiber x)).symm).hom ≫
    (f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)

/-- **The comparison square for the residue-field action on the closed fibre.** The composite
`𝒪_{S, f x} ⟶ κ(f x) ⟶ 𝒪_{X_{f x}, x}` agrees with
`𝒪_{S, f x} ⟶ 𝒪_{X, x} ⟶ 𝒪_{X_{f x}, x}`, where the second map of the latter is the stalk map of
the inclusion of the fibre.

This is the only geometric input of the file: it says that the residue field acts on the fibre
stalk through the stalk map of `f`, which is what makes the fibre stalk and the tensor product
`κ(f x) ⊗_{𝒪_{S, f x}} 𝒪_{X, x}` isomorphic *as `κ(f x)`-algebras* and not merely as rings. -/
theorem residue_comp_residueFieldToFibreStalk (f : X ⟶ S) (x : X) :
    S.residue (f x) ≫ residueFieldToFibreStalk f x =
      f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom ≫
        (f.fiberι (f x)).stalkMap (f.asFiber x) := by
  have hA := residue_comp_residueFieldSpecStalkIso S (f x)
    (f.fiberToSpecResidueField (f x) (f.asFiber x))
    (f.fiberToSpecResidueField_apply (f x) (f.asFiber x)).symm
  have h3 := Scheme.Hom.stalkMap_congr_hom (f.fiberι (f x) ≫ f)
    (f.fiberToSpecResidueField (f x) ≫ S.fromSpecResidueField (f x)) (f.fiber_fac (f x))
    (f.asFiber x)
  rw [residueFieldToFibreStalk, ← Category.assoc, hA, Category.assoc,
    ← Scheme.Hom.stalkMap_comp (f.fiberToSpecResidueField (f x)) (S.fromSpecResidueField (f x))
      (f.asFiber x), ← Category.assoc,
    Scheme.Hom.stalkMap_congr_point f x (f.fiberι (f x) (f.asFiber x)) (f.fiberι_asFiber x).symm,
    Category.assoc, ← Scheme.Hom.stalkMap_comp (f.fiberι (f x)) f (f.asFiber x), h3]
  exact (congrArg
    (fun t ↦ t ≫ (f.fiberToSpecResidueField (f x) ≫
      S.fromSpecResidueField (f x)).stalkMap (f.asFiber x))
    (stalkCongr_trans _ _ _).symm).trans (Category.assoc _ _ _)

/-- The residue field of `S` at `f x` acts on the local ring of the closed fibre of `f` at `x`
through `AlgebraicGeometry.residueFieldToFibreStalk`.

The result type is ascribed at `IsLocalRing.ResidueField (S.presheaf.stalk (f x))`, the spelling
`AlgebraicGeometry.IsCompleteIntersectionFibreAt` uses, rather than at the bundled
`↥(S.residueField (f x))` that `RingHom.toAlgebra` would produce. -/
noncomputable instance fibreStalkAlgebra (f : X ⟶ S) (x : X) :
    Algebra (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  (residueFieldToFibreStalk f x).hom.toAlgebra

/-- `AlgebraicGeometry.fibreStalkAlgebra` acts by `AlgebraicGeometry.residueFieldToFibreStalk`. -/
theorem algebraMap_fibreStalk (f : X ⟶ S) (x : X)
    (c : IsLocalRing.ResidueField (S.presheaf.stalk (f x))) :
    algebraMap (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) c = (residueFieldToFibreStalk f x).hom c :=
  rfl

/-- The closed fibre of `f` at `x`, in its tensor rendering, and the local ring of the
scheme-theoretic fibre have the same underlying ring.

This composes `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, which identifies
`𝒪_{X, x} / 𝔪_{S, f x} 𝒪_{X, x}` with `κ(f x) ⊗_{𝒪_{S, f x}} 𝒪_{X, x}`, with
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, which identifies the same quotient with the
fibre stalk. -/
@[ega "IV 5.5.2"]
noncomputable def fibreStalkRingEquiv (f : X ⟶ S) (x : X) :
    letI : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x)) ⊗[S.presheaf.stalk (f x)]
        (X.presheaf.stalk x)) ≃+* ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  letI : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).symm.toRingEquiv.trans
    (quotientStalkEquivFiberStalk f x)

/-- **The closed fibre of `f` at `x` is the local ring of the scheme-theoretic fibre, as a
`κ(f x)`-algebra.** -/
noncomputable def fibreStalkAlgEquiv (f : X ⟶ S) (x : X) :
    letI : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x)) ⊗[S.presheaf.stalk (f x)]
          (X.presheaf.stalk x)) ≃ₐ[IsLocalRing.ResidueField (S.presheaf.stalk (f x))]
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
  letI : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := fibreStalkRingEquiv f x) (by
    intro c
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hq : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).symm
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) r) ⊗ₜ
          (1 : X.presheaf.stalk x)) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map
            (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)))
          (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x) r) := by
      rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
        ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
    -- the same equation, respelled with `(f.stalkMap x).hom` in place of `algebraMap`, which is
    -- the spelling `quotientStalkEquivFiberStalk_mk` is stated in
    have hq' : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X.presheaf.stalk x)
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).symm
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) r) ⊗ₜ
          (1 : X.presheaf.stalk x)) =
        Ideal.Quotient.mk (Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))))
          ((f.stalkMap x).hom r) := hq
    have hmaster : (residueFieldToFibreStalk f x).hom (S.residue (f x) r) =
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom
            ((f.stalkMap x).hom r)) := by
      simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using
        congrArg (fun g : S.presheaf.stalk (f x) ⟶
          (f.fiber (f x)).presheaf.stalk (f.asFiber x) ↦ g.hom r)
          (residue_comp_residueFieldToFibreStalk f x)
    change quotientStalkEquivFiberStalk f x
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor (X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))).symm
          ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) r) ⊗ₜ
            (1 : X.presheaf.stalk x))) =
      (residueFieldToFibreStalk f x).hom (S.residue (f x) r)
    rw [hq', quotientStalkEquivFiberStalk_mk, hmaster])

/-- **The closed-fibre complete-intersection condition, in the fibre-stalk rendering.** The local
ring of the scheme-theoretic fibre `X_{f x}` at `x` is a complete intersection over the residue
field of `f x`, with the residue field acting through the structural morphism of the fibre.

This is the rendering of [Stacks 02V3] that describes the fibre local ring by the fibre; see
`AlgebraicGeometry.isCompleteIntersectionFibreStalkAt_iff` for its agreement with
`AlgebraicGeometry.IsCompleteIntersectionFibreAt`, which describes it by the two stalks of `f`. -/
def IsCompleteIntersectionFibreStalkAt (f : X ⟶ S) (x : X) : Prop :=
  IsCompleteIntersectionLocalRing (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
    ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- **The two renderings of the closed-fibre complete-intersection condition agree.**

Both sides are `Definition 00SD` for the local ring of the closed fibre of `f` at `x` over the
residue field of `f x`; they differ in how that local ring and that algebra structure are
presented, and `AlgebraicGeometry.fibreStalkAlgEquiv` identifies the two presentations.  The two
renderings of Definition 00SD itself are reconciled by
`Stacks.SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection`. -/
theorem isCompleteIntersectionFibreStalkAt_iff (f : X ⟶ S) (x : X) :
    IsCompleteIntersectionFibreStalkAt f x ↔ IsCompleteIntersectionFibreAt f x := by
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have h := Stacks.SyntomicBaseChange.isCompleteIntersectionLocalRing_iff_isCompleteIntersection
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x)) ⊗[S.presheaf.stalk (f x)]
      (X.presheaf.stalk x))
  exact ⟨fun hs ↦ h.mp (IsCompleteIntersectionLocalRing.of_algEquiv hs
      (fibreStalkAlgEquiv f x).symm),
    fun hl ↦ IsCompleteIntersectionLocalRing.of_algEquiv (h.mpr hl) (fibreStalkAlgEquiv f x)⟩

/-- **Stacks Project, Tag 01UE, in the fibre-stalk rendering.**  A flat morphism locally of finite
presentation is syntomic at a point exactly when the local ring of the scheme-theoretic fibre
there is a complete intersection over the residue field of the image point. -/
@[ega "IV 19.3.6"]
theorem isSyntomicAt_iff_isCompleteIntersectionFibreStalkAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] (x : X) :
    IsSyntomicAt f x ↔ IsCompleteIntersectionFibreStalkAt f x :=
  (isSyntomicAt_iff_isCompleteIntersectionFibreAt f x).trans
    (isCompleteIntersectionFibreStalkAt_iff f x).symm

end AlgebraicGeometry

end
