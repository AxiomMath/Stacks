module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degrees in which a mapping cone agrees with one of its two factors

Let `φ : F ⟶ G` be a morphism of cochain complexes. In degree `p` the mapping cone of `φ` is
`F^{p+1} ⊕ G^p`, so whenever one of the two summands vanishes the corresponding inclusion is an
isomorphism:

* if `F^{p+1} = 0` then `mappingCone.inr φ` is an isomorphism in degree `p`;
* if `G^{p-1} = 0` then the degree-`(p, p-1)` component of `mappingCone.inl φ` is an
  isomorphism.

## Main results

* `CochainComplex.mappingCone.isIso_inr_f`: the first statement.
* `CochainComplex.mappingCone.isIso_inl_v`: the second.

## Implementation notes

Neither statement unfolds the construction of the cone. Both are proved from the four
`inl`/`inr`/`fst`/`snd` identities and the extensionality principle
`CochainComplex.mappingCone.ext_to`, which says that a morphism into the degree-`p` term of the
cone is determined by its two components.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : CochainComplex C ℤ} (φ : F ⟶ G)
  [HasHomotopyCofiber φ]

/-- **In a degree where the source of `φ` contributes nothing, the cone is its target.** If
`F^{p+1}` is a zero object then `mappingCone.inr φ` is an isomorphism in degree `p`, with inverse
the second projection of the cone. -/
@[sga "4 XVII 1.1.1" "Clause"]
theorem isIso_inr_f (p : ℤ) (hp : IsZero (F.X (p + 1))) : IsIso ((inr φ).f p) := by
  refine ⟨(snd φ).v p p (add_zero p), inr_f_snd_v φ p, ext_to φ p (p + 1) rfl ?_ ?_⟩
  · rw [Category.assoc, inr_f_fst_v φ p (p + 1) rfl, comp_zero, Category.id_comp]
    exact (hp.eq_of_tgt _ _).symm
  · rw [Category.assoc, inr_f_snd_v φ p, Category.comp_id, Category.id_comp]

/-- **In a degree where the target of `φ` contributes nothing, the cone is a shift of its
source.** If `G^q` is a zero object, for `q = p - 1`, then the degree-`(p, q)` component of
`mappingCone.inl φ` is an isomorphism, with inverse the first projection of the cone. -/
theorem isIso_inl_v (p q : ℤ) (hpq : p + (-1) = q) (hq : IsZero (G.X q)) :
    IsIso ((inl φ).v p q hpq) := by
  have hqp : q + 1 = p := by omega
  refine ⟨(fst φ).1.v q p hqp, inl_v_fst_v φ p q hqp, ext_to φ q p hqp ?_ ?_⟩
  · rw [Category.assoc, inl_v_fst_v φ p q hqp, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, inl_v_snd_v φ p q hpq, comp_zero, Category.id_comp]
    exact (hq.eq_of_tgt _ _).symm

end CochainComplex.mappingCone

end
