module

public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent map of a morphism of schemes over a base

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, say with structure morphisms
`p : X ⟶ S` and `q : Y ⟶ S` satisfying `f ≫ q = p`, and let `x` be a point of `X` whose
residue field agrees with that of its image. Then `f` carries tangent arrows at `x` to tangent
arrows at `f x`, semilinearly over the inverse of the residue-field extension.

## Main definitions

* `AlgebraicGeometry.tangentDerivationMap` is the map on tangent derivations, given by
  precomposition with the stalk map followed by the residue-field identification.
* `AlgebraicGeometry.tangentMap` is the canonical semilinear map on relative tangent spaces.

## Main results

* `AlgebraicGeometry.tangentMap_apply` characterizes the tangent map geometrically: a tangent
  arrow is sent to its composition with `f`, read on the dual numbers of the target residue
  field through any ring homomorphism inducing the residue-field identification on both
  components.
* `AlgebraicGeometry.dottedToDerivation_add`, `AlgebraicGeometry.dottedToDerivation_smul`,
  `AlgebraicGeometry.derivationToDotted_add` and `AlgebraicGeometry.derivationToDotted_smul`
  record that the vector space structure on dotted tangent arrows is transported along the
  equivalence with tangent derivations.

## Implementation notes

The residue-field equality of the source is expressed as the assertion that the canonical
residue-field homomorphism `Y.residueField (f x) ⟶ X.residueField x` is an isomorphism, and
the tangent map is stated semilinearly over its inverse, which is the linear map once the two
fields are identified.

The construction is carried out on tangent derivations rather than on dotted arrows, because
the vector space structure of `AlgebraicGeometry.dottedTangentArrowModule` is transported from
the derivations along `AlgebraicGeometry.dottedDerivationEquiv`; additivity and semilinearity
are immediate there, whereas the geometric description of addition is an existential over the
square-zero pushout and carries no uniqueness statement. The geometric formula is recovered
afterwards as `AlgebraicGeometry.tangentMap_apply`.

The two module structures that `AlgebraicGeometry.tangentDerivations` carries in its type — the
stalk acting on the residue field through the residue map, and the resulting commutation — are
reintroduced in each proof exactly as in the definition, so that the instances appearing in the
goals are the ones appearing in that type.

## References

* [Stacks Project, Tag 0B2F](https://stacks.math.columbia.edu/tag/0B2F)
* [Stacks Project, Tag 0B2B](https://stacks.math.columbia.edu/tag/0B2B)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Transport

variable {X S : Scheme.{u}} (p : X ⟶ S) (x : X)

/-- The derivation attached to a sum of dotted tangent arrows is the sum of their derivations. -/
lemma dottedToDerivation_add (θ η : DottedTangentArrow p x) :
    dottedToDerivation p x (θ + η) =
      dottedToDerivation p x θ + dottedToDerivation p x η := by
  conv_lhs => rw [show θ + η = derivationToDotted p x
    (dottedToDerivation p x θ + dottedToDerivation p x η) from rfl]
  exact dottedToDerivation_derivationToDotted p x _

/-- The derivation attached to a scalar multiple of a dotted tangent arrow is the scalar multiple
of its derivation. -/
lemma dottedToDerivation_smul (r : X.residueField x) (θ : DottedTangentArrow p x) :
    dottedToDerivation p x (r • θ) = r • dottedToDerivation p x θ := by
  conv_lhs => rw [show r • θ = derivationToDotted p x (r • dottedToDerivation p x θ) from rfl]
  exact dottedToDerivation_derivationToDotted p x _

/-- The dotted tangent arrow attached to a sum of tangent derivations is the sum of their dotted
tangent arrows. -/
lemma derivationToDotted_add (D E : tangentDerivations p x) :
    derivationToDotted p x (D + E) =
      derivationToDotted p x D + derivationToDotted p x E := by
  conv_rhs => rw [show derivationToDotted p x D + derivationToDotted p x E =
    derivationToDotted p x (dottedToDerivation p x (derivationToDotted p x D) +
      dottedToDerivation p x (derivationToDotted p x E)) from rfl]
  rw [dottedToDerivation_derivationToDotted, dottedToDerivation_derivationToDotted]

/-- The dotted tangent arrow attached to a scalar multiple of a tangent derivation is the scalar
multiple of its dotted tangent arrow. -/
lemma derivationToDotted_smul (r : X.residueField x) (D : tangentDerivations p x) :
    derivationToDotted p x (r • D) = r • derivationToDotted p x D := by
  conv_rhs => rw [show r • derivationToDotted p x D =
    derivationToDotted p x (r • dottedToDerivation p x (derivationToDotted p x D)) from rfl]
  rw [dottedToDerivation_derivationToDotted]

end Transport

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S) (x : X)

/-- When the residue-field extension at `x` is an isomorphism, its inverse undoes the residue of
the stalk map. -/
lemma inv_residueFieldMap_residue [IsIso (f.residueFieldMap x)]
    (a : Y.presheaf.stalk (f x)) :
    (inv (f.residueFieldMap x)).hom (X.residue x (f.stalkMap x a)) = Y.residue (f x) a := by
  have h1 : X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    (congrArg (fun g : Y.presheaf.stalk (f x) ⟶ X.residueField x ↦ g a)
      (Scheme.residue_residueFieldMap f x)).symm
  rw [h1]
  exact congrArg (fun g : Y.residueField (f x) ⟶ Y.residueField (f x) ↦ g (Y.residue (f x) a))
    (IsIso.hom_inv_id (f.residueFieldMap x))

/-- The tangent derivation at `f x` obtained from one at `x`, by composing with the stalk map of
`f` and identifying the two residue fields. -/
noncomputable def tangentDerivationMap (h : f ≫ q = p) [IsIso (f.residueFieldMap x)]
    (D : tangentDerivations p x) : tangentDerivations q (f x) := by
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  letI : Module (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    Module.compHom _ (Y.residue (f x)).hom
  letI : SMulCommClass (Y.residueField (f x)) (Y.presheaf.stalk (f x))
      (Y.residueField (f x)) := ⟨by
        intro r a v
        change r * ((Y.residue (f x) a) * v) = (Y.residue (f x) a) * (r * v)
        ring⟩
  refine ⟨{ toFun := fun a ↦ (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x a))
            map_add' := by intro a b; simp
            map_smul' := by
              intro r a
              simp only [map_zsmul, RingHom.id_apply]
            map_one_eq_zero' := by simp
            leibniz' := ?_ }, ?_⟩
  · intro a b
    change (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x (a * b))) =
      (Y.residue (f x) a) * _ + (Y.residue (f x) b) * _
    rw [map_mul]
    have hl := D.1.leibniz (f.stalkMap x a) (f.stalkMap x b)
    change D.1 (f.stalkMap x a * f.stalkMap x b) =
      (X.residue x (f.stalkMap x a)) * D.1 (f.stalkMap x b) +
        (X.residue x (f.stalkMap x b)) * D.1 (f.stalkMap x a) at hl
    rw [hl, map_add, map_mul, map_mul, inv_residueFieldMap_residue f x a,
      inv_residueFieldMap_residue f x b]
    rfl
  · subst h
    intro s
    change (inv (f.residueFieldMap x)).hom
      (D.1 (f.stalkMap x (q.stalkMap (f x) s))) = 0
    have hc : (f ≫ q).stalkMap x s = f.stalkMap x (q.stalkMap (f x) s) := by
      rw [Scheme.Hom.stalkMap_comp]; rfl
    have he : D.1 (f.stalkMap x (q.stalkMap (f x) s)) = 0 := hc ▸ D.property s
    rw [he, map_zero]

/-- The derivation `tangentDerivationMap f p q x h D` sends `a` to the image of
`D (f.stalkMap x a)` under the inverse of the residue-field extension. -/
lemma tangentDerivationMap_val_apply (h : f ≫ q = p) [IsIso (f.residueFieldMap x)]
    (D : tangentDerivations p x) (a : Y.presheaf.stalk (f x)) :
    (tangentDerivationMap f p q x h D).1 a =
      (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x a)) := rfl

/-- The map on tangent derivations is additive. -/
lemma tangentDerivationMap_add (h : f ≫ q = p) [IsIso (f.residueFieldMap x)]
    (D E : tangentDerivations p x) :
    tangentDerivationMap f p q x h (D + E) =
      tangentDerivationMap f p q x h D + tangentDerivationMap f p q x h E := by
  let _ : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  let _ : Module (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    Module.compHom _ (Y.residue (f x)).hom
  refine Subtype.ext (Derivation.ext fun a ↦ ?_)
  rw [tangentDerivationMap_val_apply]
  change (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x a) + E.1 (f.stalkMap x a)) =
    (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x a)) +
      (inv (f.residueFieldMap x)).hom (E.1 (f.stalkMap x a))
  exact map_add _ _ _

/-- The map on tangent derivations is semilinear over the inverse of the residue-field
extension. -/
lemma tangentDerivationMap_smul (h : f ≫ q = p) [IsIso (f.residueFieldMap x)]
    (r : X.residueField x) (D : tangentDerivations p x) :
    tangentDerivationMap f p q x h (r • D) =
      (inv (f.residueFieldMap x)).hom r • tangentDerivationMap f p q x h D := by
  let _ : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  let _ : Module (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    Module.compHom _ (Y.residue (f x)).hom
  refine Subtype.ext (Derivation.ext fun a ↦ ?_)
  rw [tangentDerivationMap_val_apply]
  change (inv (f.residueFieldMap x)).hom (r * D.1 (f.stalkMap x a)) =
    (inv (f.residueFieldMap x)).hom r *
      (inv (f.residueFieldMap x)).hom (D.1 (f.stalkMap x a))
  exact map_mul _ _ _

/-- The tangent map of a morphism over `S`, with the scalar fields identified by the canonical
residue-field isomorphism. -/
@[stacks 0B2F "canonical tangent map", ega "IV 16.5.13" "(16.5.13.5)"]
noncomputable def tangentMap (h : f ≫ q = p) (x : X) [IsIso (f.residueFieldMap x)] :
    DottedTangentArrow p x →ₛₗ[(inv (f.residueFieldMap x)).hom]
      DottedTangentArrow q (f x) where
  toFun θ :=
    derivationToDotted q (f x) (tangentDerivationMap f p q x h (dottedToDerivation p x θ))
  map_add' := by
    intro θ η
    rw [dottedToDerivation_add, tangentDerivationMap_add, derivationToDotted_add]
  map_smul' := by
    intro r θ
    rw [dottedToDerivation_smul, tangentDerivationMap_smul, derivationToDotted_smul]

/-- The tangent map is induced by composition of dual-number arrows: a tangent arrow is sent to its
composite with `f`, pulled back along any ring homomorphism of dual numbers whose two components
are the residue-field identification. -/
@[stacks 0B2F "characterization by composition of dual-number arrows"]
theorem tangentMap_apply (h : f ≫ q = p) (x : X) [IsIso (f.residueFieldMap x)]
    (θ : DottedTangentArrow p x)
    (α : DualNumber (X.residueField x) →+* DualNumber (Y.residueField (f x)))
    (hα₀ : ∀ z, TrivSqZeroExt.fst (α z) =
      (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.fst z))
    (hα₁ : ∀ z, TrivSqZeroExt.snd (α z) =
      (inv (f.residueFieldMap x)).hom (TrivSqZeroExt.snd z)) :
    (tangentMap f p q h x θ).val =
      Spec.map (CommRingCat.ofHom α) ≫ θ.val ≫ f := by
  have hstalk : derivationStalkHom q (f x)
      (tangentDerivationMap f p q x h (dottedToDerivation p x θ)) =
      f.stalkMap x ≫ dottedStalkHom p x θ ≫ CommRingCat.ofHom α := by
    ext a
    · change Y.residue (f x) a =
        TrivSqZeroExt.fst (α (dottedStalkHom p x θ (f.stalkMap x a)))
      rw [hα₀, show TrivSqZeroExt.fst (dottedStalkHom p x θ (f.stalkMap x a)) =
        X.residue x (f.stalkMap x a) from congrArg
          (fun g : X.presheaf.stalk x ⟶ X.residueField x ↦ g (f.stalkMap x a))
          (dottedStalkHom_fst p x θ), inv_residueFieldMap_residue f x a]
    · change (inv (f.residueFieldMap x)).hom
          ((dottedToDerivation p x θ).1 (f.stalkMap x a)) =
        TrivSqZeroExt.snd (α (dottedStalkHom p x θ (f.stalkMap x a)))
      rw [hα₁]
      rfl
  change Spec.map (derivationStalkHom q (f x)
    (tangentDerivationMap f p q x h (dottedToDerivation p x θ))) ≫
      Y.fromSpecStalk (f x) = Spec.map (CommRingCat.ofHom α) ≫ θ.val ≫ f
  rw [hstalk, ← dottedStalkHom_spec p x θ, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk f]
  simp only [Spec.map_comp, Category.assoc]

end AlgebraicGeometry

end
