module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.NonemptyMember

/-!
# Universal effective epimorphic families are jointly surjective

Every point of the target of a universal effective epimorphic family lies in the image of
some member of the family, both for families of schemes and for families of affine schemes.

## Main results

* `AlgebraicGeometry.jointlySurjective_of_isUniversalEffectiveEpiFamily` is the statement
  for a family of schemes.
* `AlgebraicGeometry.exists_preimage_of_isUniversalEffectiveEpiFamily` is the statement for
  a family of affine schemes.

## Implementation notes

Joint surjectivity is expressed pointwise, without choosing a coproduct of the family, so the
index type need not be small enough for that coproduct to exist in the given universe. When
the coproduct does exist, the statement says exactly that the morphism from it is surjective.

The proof base changes the family along the morphism from the spectrum of the residue field
of the given point. The base change is again an effective epimorphic family, so some member
is nonempty, and the image of any of its points is the given point because the spectrum of a
residue field has only one point.

## References

* [Stacks Project, Lemma 35.13.3 (Tag 0EUB)](https://stacks.math.columbia.edu/tag/0EUB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-- If `p ≫ q` factors through `Spec κ(x) → X`, then `q (p z) = x` for every point `z`. -/
private theorem apply_eq_of_comp_eq_fromSpecResidueField {X Y W : Scheme.{u}} (x : X)
    (π : W ⟶ Spec (X.residueField x)) (p : W ⟶ Y) (q : Y ⟶ X)
    (h : p ≫ q = π ≫ X.fromSpecResidueField x) (z : W) : q (p z) = x := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply,
    Subsingleton.elim (π z) (IsLocalRing.closedPoint (X.residueField x))]
  exact Scheme.fromSpecResidueField_apply x _

/-- A universal effective epimorphic family of schemes is jointly surjective
on the underlying spaces. -/
@[stacks 0EUB "schemes_surjective",
  sga "3 IV 6.7.2" "univ. eff. epi ⇒ surj",
  sga "3 IV 1.3" "special case"]
theorem jointlySurjective_of_isUniversalEffectiveEpiFamily
    {I : Type w} {X : Scheme.{u}} (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    ∀ x : X, ∃ i, x ∈ Set.range (f i) := by
  intro x
  let g := X.fromSpecResidueField x
  let U' : I → Scheme := fun i => pullback g (f i)
  let π' := fun i => pullback.fst g (f i)
  obtain ⟨i, ⟨z⟩⟩ :=
    exists_nonempty_scheme_of_isEffectiveEpiFamily U' π'
      (h.2 g U' π' (fun i => pullback.snd g (f i))
        (fun i => IsPullback.of_hasPullback g (f i)))
  exact ⟨i, pullback.snd g (f i) z, apply_eq_of_comp_eq_fromSpecResidueField x
    (pullback.fst g (f i)) (pullback.snd g (f i)) (f i) pullback.condition.symm z⟩

/-- A universal effective epimorphic family of affine schemes is jointly surjective. -/
@[stacks 0EUB "affine_schemes_surjective", sga "3 IV 6.7.2" "affine case"]
theorem exists_preimage_of_isUniversalEffectiveEpiFamily
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f) :
    ∀ x : X.obj, ∃ (i : I) (y : (U i).obj),
      (AffineScheme.forgetToScheme.map (f i)) y = x := by
  intro x
  let V : AffineScheme := AffineScheme.of (Spec (CommRingCat.of (X.obj.residueField x)))
  let hx : V ⟶ X := AffineScheme.ofHom (X.obj.fromSpecResidueField x)
  let P : I → AffineScheme := fun i => pullback hx (f i)
  let π : ∀ i, P i ⟶ V := fun i => pullback.fst hx (f i)
  let p : ∀ i, P i ⟶ U i := fun i => pullback.snd hx (f i)
  obtain ⟨i, ⟨z⟩⟩ :=
    exists_nonempty_affineScheme_of_isEffectiveEpiFamily P π
      (h.2 hx P π p (fun i => IsPullback.of_hasPullback hx (f i)))
  exact ⟨i, (p i).hom z, apply_eq_of_comp_eq_fromSpecResidueField x (π i).hom (p i).hom (f i).hom
    (congrArg (·.hom) (IsPullback.of_hasPullback hx (f i)).w.symm) z⟩

end AlgebraicGeometry
