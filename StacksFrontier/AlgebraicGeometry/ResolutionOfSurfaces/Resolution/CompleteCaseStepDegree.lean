module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepNormalization

/-!
# The degree of the normalization of a resolution over the resolution

In the situation of `AlgebraicGeometry.CompleteCaseStep` — `B → A` an injective map of domains
with `A` finite over `B`, `g : Y ⟶ Spec B` birational from an integral scheme, and `X` the
normalization of `Y ×_{Spec B} Spec A` in the spectrum of the function field `K` of `Spec A` —
the morphism `X ⟶ Y` has degree `[K : L] = [A : B]`, where `L` is the function field of `Y`: over
every affine open `U` of `Y` the ring `Γ(X, U)` has rank `[A : B]` over `Γ(Y, U)`. This is the
degree bound of the inductive step of the proof of [Stacks, Tag 0BGN].

## Main results

* `AlgebraicGeometry.finrank_appLE_eq_finrank_functionField`: for a dominant morphism of integral
  schemes, the rank of a ring of sections over another is the degree of the extension of function
  fields.
* `AlgebraicGeometry.CompleteCaseStep.finrank_appLE_toResolution`: the rank of `Γ(X, V)` over
  `Γ(Y, U)` is the rank of `A` over `B`.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **For a dominant morphism of integral schemes, the rank of the ring of sections over an affine
open of the source over the ring of sections over an affine open of the target is the degree of
the extension of function fields**, both rings having those function fields as fraction
fields. -/
theorem finrank_appLE_eq_finrank_functionField {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) [Nonempty U] [Nonempty V] :
    letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, V) = Module.finrank Y.functionField X.functionField := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(Y, U) X.functionField :=
    (f.appLE U V hVU ≫ X.germToFunctionField V).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, V) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    .of_algebraMap_eq fun a => (f.functionFieldMap_germToFunctionField hVU a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  exact (IsFractionRing.finrank_eq Γ(Y, U) Y.functionField Γ(X, V) X.functionField).symm

namespace CompleteCaseStep

variable {B A : Type u} [CommRing B] [CommRing A] [IsDomain B] [IsDomain A] [Algebra B A]
  [FaithfulSMul B A] {Y : Scheme.{u}} [IsIntegral Y] {g : Y ⟶ Spec (.of B)}

variable (B A) in
/-- The degree of the extension of function fields of `Spec A ⟶ Spec B` is the rank of `A` over
`B`. -/
theorem finrank_functionField_baseMap :
    letI := (baseMap B A).functionFieldMap.hom.toAlgebra
    Module.finrank (Spec (.of B)).functionField (Spec (.of A)).functionField =
      Module.finrank B A := by
  let algK := (baseMap B A).functionFieldMap.hom.toAlgebra
  have : Nonempty (⊤ : (Spec (.of B)).Opens) :=
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B), trivial⟩⟩
  have : Nonempty ((baseMap B A) ⁻¹ᵁ ⊤ : (Spec (.of A)).Opens) :=
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A), trivial⟩⟩
  let algΓ := ((baseMap B A).appLE ⊤ ((baseMap B A) ⁻¹ᵁ ⊤) le_rfl).hom.toAlgebra
  have h : Module.finrank Γ(Spec (.of B), ⊤) Γ(Spec (.of A), (baseMap B A) ⁻¹ᵁ ⊤) =
      Module.finrank (Spec (.of B)).functionField (Spec (.of A)).functionField :=
    finrank_appLE_eq_finrank_functionField (baseMap B A) (U := ⊤)
      (V := (baseMap B A) ⁻¹ᵁ ⊤) (isAffineOpen_top _) (by exact isAffineOpen_top _) le_rfl
  rw [← h]
  refine (@Algebra.finrank_eq_of_equiv_equiv B A _ _ _ Γ(Spec (.of B), ⊤)
    Γ(Spec (.of A), (baseMap B A) ⁻¹ᵁ ⊤) _ _ algΓ
    (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv ?_).symm
  ext b
  change ((baseMap B A).appLE ⊤ ((baseMap B A) ⁻¹ᵁ ⊤) le_rfl).hom
    ((Scheme.ΓSpecIso (.of B)).inv.hom b) = (Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap B A b)
  rw [Scheme.Hom.appLE_eq_app]
  exact (congrArg (fun φ => φ.hom b)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap B A)))).symm

variable (B A) in
/-- `X ⟶ Y` is dominant: `Spec K ⟶ X ⟶ Y` is `Spec K ⟶ Spec L ⟶ Y`, whose image is the generic
point of `Y`. -/
theorem isDominant_toResolution (hg : IsBirational g) : IsDominant (toResolution B A hg) := by
  let j := (liftToFibreProduct B A hg).toNormalization
  have hj : j ≫ toResolution B A hg = genericPointToResolution B A hg := by
    rw [toResolution, ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
      liftToFibreProduct, pullback.lift_fst]
  let := isDominant_fromSpecStalk_genericPoint Y
  have : Subsingleton (Spec Y.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
  have : Nonempty (Spec (fieldK A)) := inferInstanceAs (Nonempty (PrimeSpectrum (fieldK A)))
  have : IsDominant (genericPointToResolution B A hg) := by
    rw [genericPointToResolution]
    let := hg.isDominant
    let := isIso_functionFieldMap hg
    have : Surjective (Spec.map (inv g.functionFieldMap ≫ (baseMap B A).functionFieldMap)) :=
      ⟨Function.surjective_to_subsingleton _⟩
    infer_instance
  have : IsDominant (j ≫ toResolution B A hg) := by rw [hj]; infer_instance
  exact IsDominant.of_comp j _

/-- The degree of the extension of function fields of `X ⟶ Y` is the rank of `A` over `B`: the
square formed with `Spec A ⟶ Spec B` commutes, and its two other sides induce isomorphisms of
function fields. -/
theorem finrank_functionField_toResolution (hg : IsBirational g) :
    letI := isDominant_toResolution B A hg
    letI := (toResolution B A hg).functionFieldMap.hom.toAlgebra
    Module.finrank Y.functionField (liftToFibreProduct B A hg).normalization.functionField =
      Module.finrank B A := by
  let := isDominant_toResolution B A hg
  let := hg.isDominant
  let := (isBirational_toBase (B := B) (A := A) hg).isDominant
  let := (toResolution B A hg).functionFieldMap.hom.toAlgebra
  let := (baseMap B A).functionFieldMap.hom.toAlgebra
  rw [← finrank_functionField_baseMap B A]
  have hsq : (functionFieldMap (toResolution B A hg)).comp (functionFieldMap g) =
      (functionFieldMap (toBase B A hg)).comp (functionFieldMap (baseMap B A)) := by
    have hcomp : ∀ {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) [IsIntegral X₁]
        [IsIntegral X₂] [IsIntegral X₃] [IsDominant a] [IsDominant b],
        functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
      intro X₁ X₂ X₃ a b _ _ _ _ _
      suffices h : CommRingCat.ofHom (functionFieldMap (a ≫ b)) =
          CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) from
        congrArg CommRingCat.Hom.hom h
      apply Spec.map_injective
      apply (cancel_mono (X₃.fromSpecStalk (genericPoint X₃))).mp
      rw [functionFieldMap_fromSpecStalk (a ≫ b)]
      have hof : CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
          CommRingCat.ofHom (functionFieldMap b) ≫ CommRingCat.ofHom (functionFieldMap a) := rfl
      rw [hof, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk b,
        ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap a))),
        functionFieldMap_fromSpecStalk a]
      exact (Category.assoc _ _ _).symm
    rw [← hcomp, ← hcomp]
    rw! (castMode := .all) [toResolution_comp (B := B) (A := A) hg]
    rfl
  exact (Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective (functionFieldMap g)
      ⟨(functionFieldMap g).injective, hg.surjective_functionFieldMap⟩)
    (RingEquiv.ofBijective (functionFieldMap (toBase B A hg))
      ⟨(functionFieldMap _).injective,
        (isBirational_toBase (B := B) (A := A) hg).surjective_functionFieldMap⟩)
    hsq).symm

/-- **The rank of the sections of `X` over those of `Y` is the rank of `A` over `B`**, over any
nonempty affine open `U` of `Y` and its preimage in `X`. -/
theorem finrank_appLE_toResolution (hg : IsBirational g) {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (toResolution B A hg ⁻¹ᵁ U)) [Nonempty U]
    [Nonempty (toResolution B A hg ⁻¹ᵁ U)] :
    letI := ((toResolution B A hg).appLE U (toResolution B A hg ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Module.finrank Γ(Y, U)
      Γ((liftToFibreProduct B A hg).normalization, toResolution B A hg ⁻¹ᵁ U) =
        Module.finrank B A := by
  let := isDominant_toResolution B A hg
  rw [finrank_appLE_eq_finrank_functionField (toResolution B A hg) hU hV le_rfl]
  exact finrank_functionField_toResolution hg

end CompleteCaseStep

end AlgebraicGeometry

end
