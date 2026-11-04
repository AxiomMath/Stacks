module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.CechModel

/-!
# The extended Čech complex depends only on the ideal

Let `R` be a commutative ring, let `M` be an `R`-module and let `f₁, …, f_r` and `g₁, …, g_s` be
two finite families of elements of `R` spanning the same ideal `I`. The extended alternating Čech
complexes
$$ M \to \bigoplus_i M_{f_i} \to \cdots \to M_{f_1 \cdots f_r},
   \qquad M \to \bigoplus_j M_{g_j} \to \cdots \to M_{g_1 \cdots g_s} $$
are then isomorphic in `D(R)`, by an isomorphism carrying one augmentation onto the other.

Both complexes have `I`-power-torsion cohomology and both augmentations are universal among
morphisms from such objects, by `derivedPowerTorsionProperty_extendedCechObject` and
`bijective_comp_extendedCechAugmentationHom`; a coreflection is unique up to a unique isomorphism
over its target.

## Main results

* `Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq` — the isomorphism
  `C^•(f₁, …, f_r; M) ≅ C^•(g₁, …, g_s; M)` in `D(R)`, compatible with the augmentations onto `M`.

## Implementation notes

The isomorphism is produced from the uniqueness of a coreflection, so it is obtained as an
existential rather than as a named map, and it is not asserted to be natural in `M`. At the level
of complexes there is a canonical candidate when one family is an ordered subfamily of the other,
namely `Cech.cechRestrict`; it is not shown here to be a quasi-isomorphism.

Tag 099D asserts the existence of a complex `K(A, I)` attached functorially to a pair of a ring
and a finitely generated ideal, identified in `D(A)` with the extended Čech complex on any finite
generating family of `I`. Since `K(A, I)` depends only on the pair, that assertion contains the
statement proved here.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
    (M : ModuleCat.{max u v} R)

/-- **The extended Čech complex depends only on the ideal spanned by the family.** Two finite
families of elements of `R` spanning the same ideal give isomorphic extended alternating Čech
complexes in `D(R)`, by an isomorphism carrying one augmentation onto `M` to the other. -/
theorem exists_extendedCechObject_iso_of_span_eq
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    ∃ e : extendedCechObject f M ≅ extendedCechObject g M,
      e.hom ≫ extendedCechAugmentationHom g M = extendedCechAugmentationHom f M := by
  have hI : (Ideal.span (Set.range f)).FG := Submodule.fg_span (Set.finite_range f)
  have hPf := derivedPowerTorsionProperty_extendedCechObject f M _ hI rfl
  have hPg := derivedPowerTorsionProperty_extendedCechObject g M _ hI hfg.symm
  have bf := bijective_comp_extendedCechAugmentationHom f M _ hI rfl
  have bg := bijective_comp_extendedCechAugmentationHom g M _ hI hfg.symm
  exact exists_iso_over_of_universal _ _ (bg _ hPf) (bf _ hPg) (bf _ hPf).1 (bg _ hPg).1

end Stacks.LocalCohomology

end
