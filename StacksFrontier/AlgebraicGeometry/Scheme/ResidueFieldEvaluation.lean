module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Evaluating sections in the residue field at a point

Evaluation of a section at a point of a scheme is the composite of the germ map with the
quotient map of the local ring at that point. This file shows that it is computed by pulling
back along the canonical morphism from the spectrum of the residue field, that it commutes with
the restriction maps of morphisms of schemes, and that finitely many elements of the residue
field are simultaneously values of sections over a single open neighbourhood of the point.

## Main results

* `AlgebraicGeometry.fromSpecResidueField_appTop`: pulling a global section back along
  `Spec κ(x) ⟶ X` computes evaluation at `x`.
* `AlgebraicGeometry.evaluation_appLE`: evaluation commutes with `Scheme.Hom.appLE`.
* `AlgebraicGeometry.exists_opens_evaluation_eq`: finitely many elements of the residue field
  at a point are simultaneously values at that point of sections over a single open
  neighbourhood.
* `AlgebraicGeometry.fromSpecResidueField_comp`: a morphism to an affine scheme, precomposed
  with `Spec κ(x) ⟶ X`, is the spectrum of the evaluation map of its global sections.

## References

* [Stacks Project, Tag 01J1](https://stacks.math.columbia.edu/tag/01J1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Pulling a global section back along the canonical morphism `Spec κ(x) ⟶ X` and identifying
the global sections of `Spec κ(x)` with `κ(x)` is evaluation at `x`. -/
theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact X.germ_residue (U := ⊤) x trivial

/-- Evaluation at a point is compatible with the restriction maps `Scheme.Hom.appLE` of a
morphism of schemes: evaluating the restriction of a section at a point of the source is the
image under the residue field map of its evaluation at the image point. -/
theorem evaluation_appLE (f : X ⟶ Y) {V : Y.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)
    (x : X) (hx : x ∈ U) (s : Γ(Y, V)) :
    X.evaluation U x hx (f.appLE V U e s) =
      f.residueFieldMap x (Y.evaluation V (f x) (e hx) s) := by
  rw [Scheme.evaluation_naturality_apply f x (e hx) s]
  exact congrArg (fun y => X.residue x y)
    (X.presheaf.germ_res_apply (homOfLE e) x hx (f.app V s))

/-- Finitely many elements of the residue field at a point of a scheme are simultaneously the
values at that point of sections over one open neighbourhood of it. -/
theorem exists_opens_evaluation_eq {n : Type*} [Finite n] (x : X)
    (c : n → X.residueField x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : n → Γ(X, U)),
      ∀ i, X.evaluation U x hx (a i) = c i := by
  choose t ht using fun i => X.residue_surjective x (c i)
  choose U hxU s hs using fun i => X.presheaf.exists_germ_eq (t i)
  have hx : x ∈ ⨅ i, U i := by
    simp only [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact hxU
  refine ⟨⨅ i, U i, hx, fun i => X.presheaf.map (homOfLE (iInf_le U i)).op (s i), fun i => ?_⟩
  rw [← ht i, ← hs i]
  exact congrArg (fun y => X.residue x y)
    (X.presheaf.germ_res_apply (homOfLE (iInf_le U i)) x hx (s i))

/-- A morphism from a scheme to an affine scheme, precomposed with the canonical morphism
`Spec κ(x) ⟶ X`, is the spectrum of the ring map evaluating global sections at `x`. -/
theorem fromSpecResidueField_comp (x : X) {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    X.fromSpecResidueField x ≫ g =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ X.Γevaluation x) := by
  rw [← cancel_mono (Spec R).isoSpec.hom]
  change _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
  conv_lhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ_assoc, ← AlgebraicGeometry.Spec.map_comp]
  rw [← SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp, Spec.map_inj,
    Iso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry

end
