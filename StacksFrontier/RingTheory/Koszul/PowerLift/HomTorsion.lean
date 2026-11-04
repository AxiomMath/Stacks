module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

@[expose] public section

/-!
# Power-torsion Hom groups in a linear triangulated category

Let `R` be a commutative ring and let `C` be an `R`-linear pretriangulated category. For `g : R`
and objects `X`, `E` of `C`, say that `Hom(X, E)` is *`g`-power torsion* when every morphism
`X ⟶ E` is annihilated by some power of `g`.

This property is the engine of the Koszul lifting lemma [Stacks, Tag 08E3]. There one is given a
complex `E` of modules over a commutative ring `A` whose cohomology modules in degrees
`-r + 1, …, 0` are `f_i`-power torsion for each entry `f_i` of a sequence `f₁, …, f_r`, and one
has to lift a class `s : A[0] ⟶ E` along the canonical map `A[0] ⟶ K(f₁^e, …, f_r^e)` into a
Koszul complex on powers of the sequence. The Koszul complex of a sequence of length `m` is an
iterated mapping cone of multiplications by its entries, starting from `A[0]`
([Stacks, Tag 062C]); so `Hom(K, E)` is `g`-power torsion as soon as `Hom(A[0]⟦j⟧, E)` is for
every `j` occurring, and `exists_factor_of_homPowerTorsion` below is exactly the inductive step
that extends a lift along one more entry of the sequence.

Nothing here is specific to derived categories of modules, and in particular no derived-category
*model* is fixed: the statements hold in any `R`-linear pretriangulated category, hence both at
`CategoryTheory.HasDerivedCategory.standard` and at a locally small model.

## Main definitions

* `Stacks.Koszul.PowerLift.HomPowerTorsion` — every morphism `X ⟶ E` is killed by a power of `g`.

## Main results

* `Stacks.Koszul.PowerLift.HomPowerTorsion.of_distTriang₂`,
  `...of_distTriang₁`, `...of_distTriang₃` — the property holds for any one vertex of a
  distinguished triangle as soon as it holds for the other two (in the shifted form the triangle
  axioms produce).
* `Stacks.Koszul.PowerLift.exists_factor_of_homPowerTorsion` — if `Hom(T.obj₁, E)` is `g`-power
  torsion then every `t : T.obj₂ ⟶ E` becomes, after multiplication by a power of `g`, the
  restriction of a morphism out of `T.obj₃`.

## Implementation notes

`HomPowerTorsion` is a `Prop`-valued predicate on a pair of objects rather than a statement about
a submodule of the Hom group, because the exponent is not uniform: the whole point of the lemma it
serves is that each individual morphism is killed by *some* power, and the power that eventually
appears in [Stacks, Tag 08E3] is produced by the induction rather than given in advance.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 062C](https://stacks.math.columbia.edu/tag/062C)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Koszul.PowerLift

universe v u

variable {R : Type*} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- `HomPowerTorsion g X E` says that every morphism `X ⟶ E` is annihilated by some power of the
scalar `g`. -/
public def HomPowerTorsion (g : R) (X E : C) : Prop :=
  ∀ φ : X ⟶ E, ∃ k : ℕ, g ^ k • φ = 0

namespace HomPowerTorsion

variable {g : R} {X E : C}

/-- Every morphism out of a zero object is already zero. -/
public theorem of_isZero (hX : IsZero X) (E : C) : HomPowerTorsion g X E :=
  fun φ => ⟨0, by rw [pow_zero, one_smul]; exact hX.eq_of_src φ 0⟩

/-- The property only depends on the isomorphism class of the source. -/
public theorem of_iso {X' : C} (e : X ≅ X') (h : HomPowerTorsion g X E) :
    HomPowerTorsion g X' E := by
  intro φ
  obtain ⟨k, hk⟩ := h (e.hom ≫ φ)
  refine ⟨k, ?_⟩
  rw [← Category.id_comp (g ^ k • φ), ← e.inv_hom_id, Category.assoc, Linear.comp_smul, hk,
    comp_zero]

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- If `Hom(T.obj₁, E)` is `g`-power torsion, a power of `g` times any `t : T.obj₂ ⟶ E` factors
through `T.mor₂`. -/
private theorem exists_factor_aux (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HomPowerTorsion g T.obj₁ E) (t : T.obj₂ ⟶ E) :
    ∃ (k : ℕ) (u : T.obj₃ ⟶ E), g ^ k • t = T.mor₂ ≫ u := by
  obtain ⟨k, hk⟩ := h₁ (T.mor₁ ≫ t)
  obtain ⟨u, hu⟩ := T.yoneda_exact₂ hT (g ^ k • t) (by rw [Linear.comp_smul, hk])
  exact ⟨k, u, hu⟩

/-- The property passes to the middle vertex of a distinguished triangle. Given
`T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃ ⟶ T.obj₁⟦1⟧`, a morphism `φ : T.obj₂ ⟶ E` restricts to `T.obj₁` to
something killed by `g ^ m`; so `g ^ m • φ` factors through `T.obj₃`, where a further power of `g`
kills it. -/
public theorem of_distTriang₂ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : HomPowerTorsion g T.obj₁ E) (h₃ : HomPowerTorsion g T.obj₃ E) :
    HomPowerTorsion g T.obj₂ E := by
  intro φ
  obtain ⟨m, ψ, hψ⟩ := exists_factor_aux T hT h₁ φ
  obtain ⟨n, hn⟩ := h₃ ψ
  refine ⟨n + m, ?_⟩
  rw [pow_add, mul_smul, hψ, ← Linear.comp_smul, hn, comp_zero]

/-- The property passes to the third vertex of a distinguished triangle. -/
public theorem of_distTriang₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : HomPowerTorsion g T.obj₂ E) (h₁ : HomPowerTorsion g (T.obj₁⟦(1 : ℤ)⟧) E) :
    HomPowerTorsion g T.obj₃ E :=
  of_distTriang₂ T.rotate (rot_of_distTriang T hT) h₂ h₁

/-- The property passes to the first vertex of a distinguished triangle. -/
public theorem of_distTriang₁ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₃ : HomPowerTorsion g (T.obj₃⟦(-1 : ℤ)⟧) E) (h₂ : HomPowerTorsion g T.obj₂ E) :
    HomPowerTorsion g T.obj₁ E :=
  of_distTriang₂ T.invRotate (inv_rot_of_distTriang T hT) h₃ h₂

end Triangulated

end HomPowerTorsion

section Triangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- **Extending a morphism along one vertex of a distinguished triangle, up to a power of a
scalar.** If every morphism `T.obj₁ ⟶ E` is killed by a power of `g`, then for every
`t : T.obj₂ ⟶ E` there are `k` and `u : T.obj₃ ⟶ E` with `g ^ k • t = T.mor₂ ≫ u`.

This is the inductive step of [Stacks, Tag 08E3]: with `T` the triangle
`K ⟶ K ⟶ K' ⟶ K⟦1⟧` exhibiting the Koszul complex `K'` of a sequence as the cone of
multiplication by the last entry on the Koszul complex `K` of the shorter sequence, it says that a
lift over `K` extends to a lift over `K'` after raising the entry to a sufficiently high power. -/
public theorem exists_factor_of_homPowerTorsion {g : R} {E : C} (T : Triangle C)
    (hT : T ∈ distTriang C) (h₁ : HomPowerTorsion g T.obj₁ E) (t : T.obj₂ ⟶ E) :
    ∃ (k : ℕ) (u : T.obj₃ ⟶ E), g ^ k • t = T.mor₂ ≫ u := by
  exact HomPowerTorsion.exists_factor_aux T hT h₁ t

end Triangulated

end Stacks.Koszul.PowerLift

end
