module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafProjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoFromDerivedIso

/-!
# Constant complexes of projective modules over a weakly contractible final object

Let `(C, J)` be a site with a final object `T` such that every locally surjective morphism of
sheaves of sets is surjective on sections over `T` (`T` is weakly contractible, Stacks 090L), and
let `M` be a bounded above complex of projective `R`-modules. The constant complex
`\underline{M}` of sheaves of `R`-modules is a bounded above complex of projective objects
(`Stacks.ConstantSheaf.projective_constantSheaf_of_surjective_app`), hence K-projective. So
morphisms out of it in the homotopy category are insensitive to quasi-isomorphisms of the target,
and an isomorphism `Q(P) ≅ Q(\underline{M})` of the derived category is realized by a
quasi-isomorphism of complexes `\underline{M} ⟶ P`.

## Main results

* `Stacks.ModuleSheaf.isKProjective_constantSheaf_mapHomologicalComplex`: `\underline{M}` is
  K-projective.
* `Stacks.ModuleSheaf.bijective_comp_quasiIso_of_constantSheaf`: postcomposition with a
  quasi-isomorphism of the homotopy category is bijective on morphisms out of `\underline{M}`.
* `Stacks.ModuleSheaf.exists_quasiIso_of_iso_constantSheaf`: an isomorphism
  `Q(P) ≅ Q(\underline{M})` comes from a quasi-isomorphism `\underline{M} ⟶ P`.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
* [Stacks Project, Tag 0648](https://stacks.math.columbia.edu/tag/0648)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [UnivLE.{max u v, w}]
  {R : Type w} [CommRing R]

/-- Over a weakly contractible final object, the terms of the constant complex attached to a
complex of projective modules are projective sheaves of modules. -/
theorem projective_constantSheaf_mapHomologicalComplex_X {T : C} (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (M : CochainComplex (ModuleCat.{w} R) ℤ) (hM : ∀ k, Module.Projective R (M.X k)) (k : ℤ) :
    Projective ((((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M).X k) :=
  have := hM k
  Stacks.ConstantSheaf.projective_constantSheaf_of_surjective_app J R hT hW (M.X k)

/-- **A constant bounded above complex of projectives is K-projective** over a weakly
contractible final object: its terms are projective and it is bounded above. -/
theorem isKProjective_constantSheaf_mapHomologicalComplex {T : C} (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (M : CochainComplex (ModuleCat.{w} R) ℤ) (b : ℤ) [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Projective R (M.X k)) :
    CochainComplex.IsKProjective (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M) :=
  have := projective_constantSheaf_mapHomologicalComplex_X hT hW M hM
  CochainComplex.isKProjective_of_projective _ b

/-- **Morphisms out of a constant bounded above complex of projectives are insensitive to
quasi-isomorphisms of the target** in the homotopy category, over a weakly contractible final
object: postcomposition with a quasi-isomorphism `V ⟶ V'` is a bijection
`Hom_K(\underline{M}, V) → Hom_K(\underline{M}, V')`, as `\underline{M}` is K-projective
(Stacks 0648). -/
theorem bijective_comp_quasiIso_of_constantSheaf {T : C} (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (M : CochainComplex (ModuleCat.{w} R) ℤ) (b : ℤ) [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Projective R (M.X k))
    {V V' : HomotopyCategory (Sheaf J (ModuleCat.{w} R)) (ComplexShape.up ℤ)} (w : V ⟶ V')
    (hw : HomotopyCategory.quasiIso _ _ w) :
    Function.Bijective (fun ψ : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
          ⟶ V =>
      ψ ≫ w) := by
  have := isKProjective_constantSheaf_mapHomologicalComplex hT hW M b hM
  have h := CochainComplex.IsKProjective.leftOrthogonal
    (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  rw [← ObjectProperty.isColocal_trW, ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at h
  exact h w hw

/-- **An isomorphism of the derived category onto a constant bounded above complex of
projectives is realized by a quasi-isomorphism** out of it, over a weakly contractible final
object: the constant complex is K-projective. -/
theorem exists_quasiIso_of_iso_constantSheaf [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} R))]
    {T : C} (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (M : CochainComplex (ModuleCat.{w} R) ℤ) (b : ℤ) [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Projective R (M.X k)) {P : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
      (((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :
    ∃ g : ((constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ P,
      QuasiIso g :=
  have := projective_constantSheaf_mapHomologicalComplex_X hT hW M hM
  CochainComplex.exists_quasiIso_of_derived_iso _ P b e.symm

end Stacks.ModuleSheaf
