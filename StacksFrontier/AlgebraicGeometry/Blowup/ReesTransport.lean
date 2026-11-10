module

public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-!
# Transport of the affine blowup along a map of the coefficient ring

A ring map `φ : R ⟶ S` carrying an ideal `I ⊆ R` onto an ideal `J ⊆ S` carries the Rees algebra
`R[It]` into `S[Jt]` degreewise, by applying `φ` to the coefficients. When `φ` is invertible the
induced map of graded rings is invertible too, so the blowup of `Spec S` in `J` is the blowup of
`Spec R` in `I` base changed along `Spec φ`.

## Main definitions

* `Stacks.Blowup.reesAlgebraHom` is the map `R[It] ⟶ S[Jt]` applying `φ` to the coefficients.
* `Stacks.Blowup.reesGradedHom` is that map as a homomorphism of graded rings.

## Main results

* `Stacks.Blowup.reesGradedHom_comp` and `Stacks.Blowup.surjective_reesGradedHom`: a two-sided
  inverse of `φ` induces a two-sided inverse of the transport, which is therefore surjective.
* `Stacks.Blowup.isIso_map_reesGradedHom`: `Proj` of the transport along an isomorphism is an
  isomorphism.
* `Stacks.Blowup.gradedZeroRingHom_reesGradedHom` and
  `Stacks.Blowup.map_reesGradedHom_comp_toSpec`: on degree zero the transport is `φ` itself, so
  the induced morphism of blowups lies over `Spec φ`.

## Implementation notes

The hypothesis is an equality `Ideal.map φ I = J` rather than an inclusion, so that the
degreewise condition `coeff i ∈ Jⁱ` of `mem_reesAlgebra_iff` is checked by rewriting rather than
by monotonicity of ideal powers; both directions of the transport are then instances of the same
definition, with no transport of `reesGrading` along an equality of ideals.

`AlgebraicGeometry.Proj.isIso_map` wants a two-sided graded inverse, which is what
`Stacks.Blowup.reesGradedHom_comp` supplies in both orders.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Blowup

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (I : Ideal R) (J : Ideal S)

/-- The map of Rees algebras induced by a ring map carrying `I` onto `J`. -/
def reesAlgebraHom (h : Ideal.map φ I = J) : reesAlgebra I →+* reesAlgebra J where
  toFun f := ⟨Polynomial.map φ (f : Polynomial R), by
    rw [mem_reesAlgebra_iff]
    intro i
    rw [Polynomial.coeff_map, ← h, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).mp f.2 i)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

/-- The underlying polynomial of the image under `reesAlgebraHom` is obtained by applying `φ` to
the coefficients. -/
@[simp]
theorem coe_reesAlgebraHom (h : Ideal.map φ I = J) (f : reesAlgebra I) :
    ((reesAlgebraHom φ I J h f : reesAlgebra J) : Polynomial S) =
      Polynomial.map φ (f : Polynomial R) := rfl

/-- The map of Rees algebras induced by a ring map carrying `I` onto `J`, as a graded map. -/
def reesGradedHom (h : Ideal.map φ I = J) : reesGrading I →+*ᵍ reesGrading J where
  __ := reesAlgebraHom φ I J h
  map_mem := by
    intro d x hx i hi
    rw [show ((reesAlgebraHom φ I J h x : reesAlgebra J) : Polynomial S) =
      Polynomial.map φ (x : Polynomial R) from rfl, Polynomial.coeff_map,
      (mem_reesGrading_iff I).mp hx i hi, map_zero]

/-- The underlying polynomial of the image under `reesGradedHom` is obtained by applying `φ` to
the coefficients. -/
@[simp]
theorem coe_reesGradedHom (h : Ideal.map φ I = J) (f : reesAlgebra I) :
    ((reesGradedHom φ I J h f : reesAlgebra J) : Polynomial S) =
      Polynomial.map φ (f : Polynomial R) := rfl

/-- Mapping a polynomial along `f` and then `g` is the identity when `g.comp f` is. -/
private theorem map_map_eq_self {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (g : B →+* A) (hgf : g.comp f = RingHom.id A) (p : Polynomial A) :
    Polynomial.map g (Polynomial.map f p) = p := by
  rw [Polynomial.map_map, hgf, Polynomial.map_id]

/-- If `ψ.comp φ` is the identity, then the transport along `ψ` composed with the transport along
`φ` is the identity of the graded Rees algebra of `I`. -/
theorem reesGradedHom_comp (h : Ideal.map φ I = J) (ψ : S →+* R) (h' : Ideal.map ψ J = I)
    (hψφ : ψ.comp φ = RingHom.id R) :
    (reesGradedHom ψ J I h').comp (reesGradedHom φ I J h) = GradedRingHom.id (reesGrading I) := by
  refine GradedRingHom.ext fun f => Subtype.ext ?_
  exact map_map_eq_self φ ψ hψφ _

/-- If `φ` has a right inverse `ψ` carrying `J` onto `I`, then the transport along `φ` is
surjective. -/
theorem surjective_reesGradedHom (h : Ideal.map φ I = J) (ψ : S →+* R) (h' : Ideal.map ψ J = I)
    (hφψ : φ.comp ψ = RingHom.id S) : Function.Surjective (reesGradedHom φ I J h) := by
  intro g
  refine ⟨reesGradedHom ψ J I h' g, Subtype.ext ?_⟩
  exact map_map_eq_self ψ φ hφψ _

/-- **The affine blowup transported along an isomorphism of the coefficient ring.** -/
theorem isIso_map_reesGradedHom (h : Ideal.map φ I = J) (ψ : S →+* R) (h' : Ideal.map ψ J = I)
    (hψφ : ψ.comp φ = RingHom.id R) (hφψ : φ.comp ψ = RingHom.id S) :
    IsIso (Proj.map (reesGradedHom φ I J h)
      (Proj.irrelevant_le_map_of_surjective _
        (surjective_reesGradedHom φ I J h ψ h' hφψ))) :=
  Proj.isIso_map _
    (Proj.irrelevant_le_map_of_surjective _ (surjective_reesGradedHom ψ J I h' φ h hψφ))
    (reesGradedHom_comp φ I J h ψ h' hψφ) (reesGradedHom_comp ψ J I h' φ h hφψ)

/-- On the degree-zero parts the transport is the ring map itself. -/
theorem gradedZeroRingHom_reesGradedHom (h : Ideal.map φ I = J) :
    (reesGradedHom φ I J h).gradedZeroRingHom.comp (reesGradingZeroEquiv I).toRingHom =
      (reesGradingZeroEquiv J).toRingHom.comp φ := by
  refine RingHom.ext fun r => Subtype.ext (Subtype.ext ?_)
  change Polynomial.map φ ((algebraMap R (reesAlgebra I) r : Polynomial R)) =
    ((algebraMap S (reesAlgebra J) (φ r) : Polynomial S))
  simp

/-- **The transport is a morphism over the transported base.** -/
theorem map_reesGradedHom_comp_toSpec (h : Ideal.map φ I = J)
    (hle : HomogeneousIdeal.irrelevant (reesGrading J) ≤
      (HomogeneousIdeal.irrelevant (reesGrading I)).map (reesGradedHom φ I J h)) :
    Proj.map (reesGradedHom φ I J h) hle ≫ toSpec I =
      toSpec J ≫ Spec.map (CommRingCat.ofHom φ) := by
  change Proj.map (reesGradedHom φ I J h) hle ≫
      (Proj.toSpecZero (reesGrading I) ≫
        Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv I).toRingHom)) =
    (Proj.toSpecZero (reesGrading J) ≫
      Spec.map (CommRingCat.ofHom (reesGradingZeroEquiv J).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom φ)
  rw [← Category.assoc, Proj.map_toSpecZero, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    gradedZeroRingHom_reesGradedHom]

end Stacks.Blowup

end
