module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsomSupplement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafProjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.RowAdicTower
public import StacksFrontier.RingTheory.Module.AdicSystem.HomotopyHomReduction

/-!
# Mittag-Leffler for homotopy classes of maps into the termwise reductions of a constant complex

Let `(C, J)` be a site with a final object `T` over which sections of sheaves are exact (every
locally surjective morphism of sheaves of sets is surjective on sections over `T`), `A` a
Noetherian ring, `𝔞 ⊆ A` an ideal and `M` a bounded complex of finite projective `A`-modules,
with constant complex `\underline{M}`. The inverse system of sets

`j ↦ Hom_{K(Sh(C, A))}(\underline{M}, \underline{M} ⊗_A \underline{A/𝔞ʲ})`,

the tensor product being taken termwise (`Stacks.ModuleSheaf.rowAdicTower`), satisfies the
Mittag-Leffler condition. This is the Artin–Rees input of Stacks 09C6.

The constant sheaf functor `c` is left adjoint to sections over `T`, so the system is
`j ↦ Hom_{K(A)}(M, Γ(T, \underline{M} ⊗ \underline{A/𝔞ʲ}))`; as `c` is monoidal,
`Γ(T, \underline{V} ⊗ \underline{L}) ≅ G(V ⊗ L)` with `G = Γ(T, \underline{-})` exact and
`A`-linear, and the system is `j ↦ Hom_{K(A)}(M, G(M ⊗ A/𝔞ʲ))`, which is Mittag-Leffler by
`Stacks.AdicSystem.HomotopyHom.isMittagLeffler_coyoneda_adicQuotient_rowFunctor`.

## Main definitions

* `Stacks.ModuleSheaf.sectionsRowComplexConstantSheafIso`: the identification
  `Γ(T, \underline{M} ⊗ \underline{L}) ≅ G(M ⊗ L)` of complexes, termwise.

## Main results

* `Stacks.ModuleSheaf.isMittagLeffler_coyoneda_rowAdicTower_constantSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor Opposite

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type w} [CommRing A]
  [UnivLE.{max u v, w}]

section Sections

variable (J) (A) (T : C)

attribute [local instance] constantSheafMonoidal in
/-- **Sections of the termwise tensor product of two constant complexes**: for a complex `M` of
`A`-modules and an `A`-module `L`, sections over `T` of the termwise tensor product
`\underline{M} ⊗ \underline{L}` are `Γ(T, \underline{M ⊗ L})`, by the monoidal structure of the
constant sheaf functor. -/
def sectionsRowComplexConstantSheafIso (M : CochainComplex (ModuleCat.{w} A) ℤ)
    (L : ModuleCat.{w} A) :
    (((sheafSections J (ModuleCat.{w} A)).obj (op T)).mapHomologicalComplex _).obj
        ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj ((constantSheaf J (ModuleCat.{w} A)).obj L)) ≅
      ((constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj
          (op T)).mapHomologicalComplex _).obj
        ((rowFunctor (curriedTensor (ModuleCat.{w} A)) M).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => ((sheafSections J (ModuleCat.{w} A)).obj (op T)).mapIso
      (Functor.Monoidal.μIso (constantSheaf J (ModuleCat.{w} A)) (M.X p) L))
    (fun p q _ => by
      change ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
            (Functor.LaxMonoidal.μ (constantSheaf J (ModuleCat.{w} A)) (M.X p) L) ≫
          ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
            ((constantSheaf J (ModuleCat.{w} A)).map (M.d p q ▷ L)) =
        ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
          ((constantSheaf J (ModuleCat.{w} A)).map (M.d p q) ▷
            (constantSheaf J (ModuleCat.{w} A)).obj L) ≫
          ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
            (Functor.LaxMonoidal.μ (constantSheaf J (ModuleCat.{w} A)) (M.X q) L)
      rw [← Functor.map_comp, ← Functor.map_comp, Functor.LaxMonoidal.μ_natural_left])

attribute [local instance] constantSheafMonoidal in
/-- `sectionsRowComplexConstantSheafIso` is natural in the module `L`. -/
theorem sectionsRowComplexConstantSheafIso_hom_naturality (M : CochainComplex (ModuleCat.{w} A) ℤ)
    {L L' : ModuleCat.{w} A} (g : L ⟶ L') :
    (((sheafSections J (ModuleCat.{w} A)).obj (op T)).mapHomologicalComplex _).map
        ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).map ((constantSheaf J (ModuleCat.{w} A)).map g)) ≫
        (sectionsRowComplexConstantSheafIso J A T M L').hom =
      (sectionsRowComplexConstantSheafIso J A T M L).hom ≫
        ((constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj
          (op T)).mapHomologicalComplex _).map
            ((rowFunctor (curriedTensor (ModuleCat.{w} A)) M).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  change ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
      ((constantSheaf J (ModuleCat.{w} A)).obj (M.X p) ◁
        (constantSheaf J (ModuleCat.{w} A)).map g) ≫
      ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
        (Functor.LaxMonoidal.μ (constantSheaf J (ModuleCat.{w} A)) (M.X p) L') =
    ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
        (Functor.LaxMonoidal.μ (constantSheaf J (ModuleCat.{w} A)) (M.X p) L) ≫
      ((sheafSections J (ModuleCat.{w} A)).obj (op T)).map
        ((constantSheaf J (ModuleCat.{w} A)).map (M.X p ◁ g))
  rw [← Functor.map_comp, ← Functor.map_comp, Functor.LaxMonoidal.μ_natural_right]

end Sections

section Adjunction

variable (J) {T : C} (hT : IsTerminal T)

/-- **Homotopy classes of maps out of a constant complex into a termwise tensor product with a
constant sheaf** are homotopy classes of maps `M ⟶ G(M ⊗ L)`, `G = Γ(T, \underline{-})`: the
adjunction between the constant sheaf functor and sections over the final object `T`, followed by
`sectionsRowComplexConstantSheafIso`. -/
def homotopyHomConstantSheafEquiv (M : CochainComplex (ModuleCat.{w} A) ℤ) (L : ModuleCat.{w} A) :
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj ((constantSheaf J (ModuleCat.{w} A)).obj L))) ≃
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj
            (op T)).mapHomologicalComplex _).obj
              ((rowFunctor (curriedTensor (ModuleCat.{w} A)) M).obj L))) :=
  (((constantSheafAdj J (ModuleCat.{w} A) hT).mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) _).trans
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      (sectionsRowComplexConstantSheafIso J A T M L)).homToEquiv

/-- **Naturality of `homotopyHomConstantSheafEquiv` in the module `L`.** -/
theorem homotopyHomConstantSheafEquiv_naturality (M : CochainComplex (ModuleCat.{w} A) ℤ)
    {L L' : ModuleCat.{w} A} (g : L ⟶ L')
    (x : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).obj ((constantSheaf J (ModuleCat.{w} A)).obj L))) :
    homotopyHomConstantSheafEquiv J hT M L'
      (x ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)).map ((constantSheaf J (ModuleCat.{w} A)).map g))) =
      homotopyHomConstantSheafEquiv J hT M L x ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj
          (op T)).mapHomologicalComplex _).map
            ((rowFunctor (curriedTensor (ModuleCat.{w} A)) M).map g)) := by
  have key : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((((sheafSections J (ModuleCat.{w} A)).obj (op T)).mapHomologicalComplex _).map
          ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).map ((constantSheaf J (ModuleCat.{w} A)).map g))) ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (sectionsRowComplexConstantSheafIso J A T M L').hom =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (sectionsRowComplexConstantSheafIso J A T M L).hom ≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (((constantSheaf J (ModuleCat.{w} A) ⋙ (sheafSections J (ModuleCat.{w} A)).obj
            (op T)).mapHomologicalComplex _).map
              ((rowFunctor (curriedTensor (ModuleCat.{w} A)) M).map g)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sectionsRowComplexConstantSheafIso_hom_naturality]
  have h1 := congrArg (fun t => t ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (sectionsRowComplexConstantSheafIso J A T M L').hom)
    (((constantSheafAdj J (ModuleCat.{w} A) hT).mapHomotopyCategory
      (ComplexShape.up ℤ)).homEquiv_naturality_right x
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((rowFunctor (curriedTensor _) (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M)).map ((constantSheaf J (ModuleCat.{w} A)).map g))))
  exact h1.trans <|
    (Category.assoc _ _ _).trans ((congrArg _ key).trans (Category.assoc _ _ _).symm)

end Adjunction

/-- **Mittag-Leffler for homotopy classes of maps into the termwise reductions of a constant
complex** (the Artin–Rees core of Stacks 09C6). On a site whose final object `T` has exact
sections (`hW`), for a Noetherian ring `A`, an ideal `𝔞` and a bounded complex `M` of finite
projective `A`-modules, the inverse system of sets
`j ↦ Hom_{K(Sh(C, A))}(\underline{M}, \underline{M} ⊗_A \underline{A/𝔞ʲ})` satisfies the
Mittag-Leffler condition. -/
theorem isMittagLeffler_coyoneda_rowAdicTower_constantSheaf [IsNoetherianRing A] {T : C}
    (hT : IsTerminal T)
    (hW : ∀ {F G : Sheaf J (Type w)} (φ : F ⟶ G), Sheaf.IsLocallySurjective φ →
      Function.Surjective (φ.hom.app (op T)))
    (𝔞 : Ideal A) (M : CochainComplex (ModuleCat.{w} A) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (hM : ∀ k, Module.Finite A (M.X k) ∧ Module.Projective A (M.X k)) :
    (rowAdicTower J 𝔞 (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
      coyoneda.obj (op ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((constantSheaf J (ModuleCat.{w} A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M)))).IsMittagLeffler := by
  let c := constantSheaf J (ModuleCat.{w} A)
  let Γ := (sheafSections J (ModuleCat.{w} A)).obj (op T)
  have : J.WEqualsLocallyBijective (ModuleCat.{w} A) :=
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat_of_univLE J A
  have : PreservesFiniteColimits Γ := preservesFiniteColimits_sheafSections_of_surjective_app hW A
  have : PreservesFiniteLimits Γ := inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf J (ModuleCat.{w} A) ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} A)).obj (op T)))
  have : PreservesFiniteLimits c := preservesFiniteLimits_constantSheaf J A
  have : PreservesFiniteColimits c := preservesFiniteColimits_constantSheaf J A
  have : c.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits (c ⋙ Γ) := comp_preservesFiniteLimits c Γ
  have : PreservesFiniteColimits (c ⋙ Γ) := comp_preservesFiniteColimits c Γ
  exact Functor.IsMittagLeffler.of_equiv
    (G := AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A) ⋙
      rowFunctor (curriedTensor (ModuleCat.{w} A)) M ⋙
        (c ⋙ Γ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
          coyoneda.obj (op ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)))
    (fun j => homotopyHomConstantSheafEquiv J hT M
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A)).obj j))
    (fun _ _ f x => homotopyHomConstantSheafEquiv_naturality J hT M
      ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A 𝔞 (ModuleCat.of A A)).map f) x)
    (Stacks.AdicSystem.HomotopyHom.isMittagLeffler_coyoneda_adicQuotient_rowFunctor M a b hM
      (c ⋙ Γ) 𝔞)

end Stacks.ModuleSheaf

end
