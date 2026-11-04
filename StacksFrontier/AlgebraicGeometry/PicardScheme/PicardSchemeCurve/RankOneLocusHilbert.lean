module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RigidifiedPicardFunctor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertUniversalDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.AbelMap

/-!
# The universal element of `Pic_{X/k, σ}` over a Hilbert scheme of points

This is the first layer of [Stacks, Tag 0B9X]. Let `k` be a field, `X` a smooth projective curve
over `k` with a `k`-rational point `σ`, and `H` a scheme representing `Hilb^d_{X/k}` (the data of
[Stacks, Tag 0B9I] (1), as in [Stacks, Tag 0B9J]), with universal divisor `D_univ ⊆ X ×_k H`. The
source adjusts `𝒪(D_univ)` by the pullback along `σ_H` to obtain

`ℒ_H = 𝒪(D_univ) ⊗ pr_H^* σ_H^* 𝒪(D_univ)^{⊗ -1} ∈ Pic_{X/k, σ}(H)`,

which by the Yoneda lemma is a natural transformation `h_H ⟶ Pic_{X/k, σ}`. On Picard classes the
adjustment is `c ↦ c - f_H^* σ_H^* c`, which lands in the kernel of `σ_H^*` because
`σ_H ≫ f_H = 𝟙`.

## Main definitions

* `AlgebraicGeometry.RigidifiedPicard.normalize`: `c ↦ c - f_T^* σ_T^* c`, from `Pic(X_T)` to
  `Pic_{X/k, σ}(T)`.
* `AlgebraicGeometry.RigidifiedPicard.universalClass`: **`ℒ_H`**, the normalisation of the class
  of `𝒪(D_univ)`; `D_univ` is an effective Cartier divisor by [Stacks, Tag 0B9J] (1)
  (`Stacks.Hilbert.isRelativeEffectiveCartierDivisor_universalFamily`).

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9J](https://stacks.math.columbia.edu/tag/0B9J)
* [Stacks Project, Tag 001P](https://stacks.math.columbia.edu/tag/001P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Divisors

open _root_.AlgebraicGeometry

end Stacks.Divisors

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The normalisation `c ↦ c - f_T^* σ_T^* c` of a Picard class on `X_T`, which lands in
`Pic_{X/k, σ}(T)`. -/
def normalize (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (pullback f T.hom)) :
    kernelAt f σ hσ T :=
  ⟨c - Stacks.Picard.schemePullbackClass (pullback.snd f T.hom)
      (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c), by
    change Stacks.Picard.schemePullbackClassHom (sectionAt f σ hσ T) (c - _) = 0
    rw [map_sub]
    change Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c -
      Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T)
        (Stacks.Picard.schemePullbackClass (pullback.snd f T.hom) _) = 0
    rw [Stacks.Picard.schemePullbackClass_comp]
    have : sectionAt f σ hσ T ≫ pullback.snd f T.hom = 𝟙 _ := pullback.lift_snd _ _ _
    rw [this, Stacks.Picard.schemePullbackClass_id, sub_self]⟩

/-- **The universal element `ℒ_H ∈ Pic_{X/k, σ}(H)`** attached to a scheme `H` representing
`Hilb^d_{X/k}`: the normalisation of the class of `𝒪(D_univ)`. -/
def universalClass [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    (picardFunctor f σ hσ).obj (op H) :=
  normalize f σ hσ H (@Stacks.Divisors.picardClass _ (hH.family (𝟙 H)).ideal
    (Stacks.Hilbert.isRelativeEffectiveCartierDivisor_universalFamily f hH).1)

/-- **The normalisation is natural**: restricting the normalisation of `c` along `T' ⟶ T` is the
normalisation of the pullback of `c` to `X_{T'}`. -/
theorem kernelMap_normalize {T T' : Over (Spec (.of k))} (g : T' ⟶ T)
    (c : Stacks.Picard.ofScheme (pullback f T.hom)) :
    kernelMap f σ hσ g (normalize f σ hσ T c) =
      normalize f σ hσ T' (Stacks.Picard.schemePullbackClass (baseChangeMap f g) c) := by
  apply Subtype.ext
  have hsnd : baseChangeMap f g ≫ pullback.snd f T.hom = pullback.snd f T'.hom ≫ g.left :=
    pullback.lift_snd _ _ _
  change Stacks.Picard.schemePullbackClassHom (baseChangeMap f g) (c - _) = _ - _
  rw [map_sub]
  congr 1
  change Stacks.Picard.schemePullbackClass (baseChangeMap f g)
      (Stacks.Picard.schemePullbackClass (pullback.snd f T.hom)
        (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c)) =
    Stacks.Picard.schemePullbackClass (pullback.snd f T'.hom)
      (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T')
        (Stacks.Picard.schemePullbackClass (baseChangeMap f g) c))
  rw [Stacks.Picard.schemePullbackClass_comp, hsnd, ← Stacks.Picard.schemePullbackClass_comp,
    Stacks.Picard.schemePullbackClass_comp g.left, ← sectionAt_baseChangeMap,
    ← Stacks.Picard.schemePullbackClass_comp (sectionAt f σ hσ T')]

/-- The normalisation of a class in `Pic_{X/k, σ}(T)` is the class itself. -/
theorem normalize_coe (T : Over (Spec (.of k))) (c : kernelAt f σ hσ T) :
    normalize f σ hσ T c.1 = c := by
  apply Subtype.ext
  change c.1 - Stacks.Picard.schemePullbackClass (pullback.snd f T.hom)
    (Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c.1) = c.1
  have hc : Stacks.Picard.schemePullbackClass (sectionAt f σ hσ T) c.1 = 0 := c.2
  rw [hc]
  change c.1 - Stacks.Picard.schemePullbackClassHom (pullback.snd f T.hom) 0 = c.1
  rw [map_zero, sub_zero]

/-- **The pullback of `ℒ_H` along `m : T ⟶ H` is the normalised class of `𝒪(Z_m)`**, `Z_m` the
family classified by `m`. -/
theorem map_universalClass [IsCurve k f] [Smooth f] {d : ℕ} {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d) {T : Over (Spec (.of k))}
    (m : T ⟶ H) :
    (picardFunctor f σ hσ).map m.op (universalClass f σ hσ hH) =
      normalize f σ hσ T (familyClass f (hH.family m)) := by
  change kernelMap f σ hσ m (normalize f σ hσ H (familyClass f (hH.family (𝟙 H)))) = _
  rw [kernelMap_normalize]
  congr 1
  have h := hH.naturality m (𝟙 H)
  rw [Category.comp_id] at h
  exact @Stacks.Divisors.schemePullbackClass_picardClass_of_eq_comap _ _ (baseChangeMap f m)
    (hH.family (𝟙 H)).ideal (hH.family m).ideal
    (isRelativeEffectiveCartierDivisor_hilbertFamily f (hH.family (𝟙 H))).1
    (isRelativeEffectiveCartierDivisor_hilbertFamily f (hH.family m)).1 h

end AlgebraicGeometry.RigidifiedPicard

end
