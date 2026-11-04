module

public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective

/-!
# A total left derived functor is right `t`-exact, and so is `Lπ_!`

Let `F : A ⥤ B` be an additive functor between abelian categories, with `A` having enough
projectives, and let `LF : D(A) ⥤ D(B)` be a total left derived functor of `F`.  Then `LF`
carries `D^{≤ a}(A)` into `D^{≤ a}(B)`: it is **right `t`-exact** for the canonical
`t`-structures.

The proof is the standard one, and all three of its ingredients are already in the library.
An object of `D^{≤ a}(A)` is represented by a cochain complex which is zero above degree `a`
(`DerivedCategory.exists_iso_Q_obj_of_isLE`); such a complex receives a quasi-isomorphism from a
complex of projectives which is still zero above degree `a` ([Stacks, Tag 0646](3),
`exists_epiResolution_of_strictlyLE`); and a bounded above complex of projectives is
K-projective (`CochainComplex.isKProjective_of_projective`), where a total left derived functor
is the underived functor applied degreewise
(`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective`).  Applying `F` degreewise does not
move the bound, because `F` preserves zero objects.

Specialised to the colimit over a small category this is the right `t`-exactness of derived
lower shriek on a chaotic site, `Stacks.CategoryHomology.isLE_totalDerivedColimit_obj`: it is
the step of the proof of [Stacks, Tag 08RF] which concludes, from a map factoring through
`τ^{≤ -k}`, that `H_i(C_{B/A}, -)` of it vanishes for `i < k`.

## Main results

* `Stacks.CategoryHomology.isLE_leftDerived_obj`: a total left derived functor is right
  `t`-exact.
* `Stacks.CategoryHomology.isZero_homology_leftDerived_obj`: the same, read as the vanishing of
  the cohomology of `LF(X)` above the bound.
* `Stacks.CategoryHomology.isLE_totalDerivedColimit_obj` and
  `Stacks.CategoryHomology.isZero_homology_totalDerivedColimit_obj`: right `t`-exactness of
  `Lπ_!`.

## References

* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryHomology

section General

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughProjectives A]

/-- **A total left derived functor is right `t`-exact**: if `X` lies in `D^{≤ a}(A)` then `LF(X)`
lies in `D^{≤ a}(B)`.

`X` is the class of a cochain complex `K` which is zero above degree `a`; `K` receives a
quasi-isomorphism from a complex `P` of projectives which is also zero above degree `a`, by
[Stacks, Tag 0646](3); `P` is therefore K-projective, so `LF(X) ≅ LF(Q P)` is the class of `F`
applied to `P` degreewise; and that complex is again zero above degree `a` because `F`
preserves zero objects. -/
theorem isLE_leftDerived_obj (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (X : DerivedCategory A) (a : ℤ) [X.IsLE a] :
    (LF.obj X).IsLE a := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE a
  obtain ⟨P, -⟩ := ProjectiveResolutionLemma.exists_epiResolution_of_strictlyLE a K hK
  have : ∀ n, Projective (P.complex.X n) := P.projective
  have : P.complex.IsStrictlyLE a := P.boundedAbove
  have : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex a
  have : IsIso (DerivedCategory.Q.map P.α) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact P.quasiIso
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (LF.mapIso (e ≪≫ (asIso (DerivedCategory.Q.map P.α)).symm) ≪≫
      leftDerivedObjIsoOfIsKProjective F LF α P.complex).symm a

/-- **A total left derived functor kills the cohomology of `LF(X)` above the bound of `X`.**
This is `Stacks.CategoryHomology.isLE_leftDerived_obj` read through
`DerivedCategory.isZero_of_isLE`, which is the form in which right `t`-exactness is used. -/
theorem isZero_homology_leftDerived_obj (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (X : DerivedCategory A) (a i : ℤ) (hi : a < i) [X.IsLE a] :
    IsZero ((DerivedCategory.homologyFunctor B i).obj (LF.obj X)) :=
  have := isLE_leftDerived_obj F LF α X a
  DerivedCategory.isZero_of_isLE _ a i hi

end General

section LowerShriek

universe u uD vD

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- **Derived lower shriek on a chaotic site is right `t`-exact**: if `X` lies in
`D^{≤ a}(Cᵒᵖ ⥤ D)` then `Lπ_!(X)` lies in `D^{≤ a}(D)`.

`Lπ_!` is a total left derived functor of the colimit over `Cᵒᵖ`
(`Stacks.CategoryHomology.totalDerivedColimit_isLeftDerivedFunctor`), so this is
`Stacks.CategoryHomology.isLE_leftDerived_obj`. -/
theorem isLE_totalDerivedColimit_obj (X : DerivedCategory (Cᵒᵖ ⥤ D)) (a : ℤ) [X.IsLE a] :
    ((totalDerivedColimit C D).obj X).IsLE a :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  isLE_leftDerived_obj (colim : (Cᵒᵖ ⥤ D) ⥤ D) (totalDerivedColimit C D)
    (totalDerivedColimitCounit C D) X a

/-- **`Lπ_!` has no cohomology above the bound of its argument.** For `X` in `D^{≤ a}`,
`H^i(Lπ_!X) = 0` for `i > a`. -/
theorem isZero_homology_totalDerivedColimit_obj (X : DerivedCategory (Cᵒᵖ ⥤ D)) (a i : ℤ)
    (hi : a < i) [X.IsLE a] :
    IsZero ((DerivedCategory.homologyFunctor D i).obj ((totalDerivedColimit C D).obj X)) :=
  have := isLE_totalDerivedColimit_obj C D X a
  DerivedCategory.isZero_of_isLE _ a i hi

end LowerShriek

end Stacks.CategoryHomology

end
