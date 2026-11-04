module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseRingRestrictionTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionQuasiCoherent

/-!
# Changing the base ring of a derived transpose of a homomorphism of modules

Let `S → R` be a homomorphism of commutative rings, `τ : A₁ → A₀` a homomorphism of differential
graded `R`-algebras and `g : N₁ ⟶ N₀|_τ` a homomorphism of differential graded modules. Its class
`N₁ ⟶ (N₀)_{A₁}` in `D(A₁, d)` (`DifferentialGradedModule.derivedTrans`) has a transpose
`N₁ ⊗^𝐋_{A₁} A₀ ⟶ N₀` under the adjunction of Tag 0BYX. Regarding everything over `S` gives the
homomorphism `g` regarded over `S`, with its own transpose over the algebras regarded over `S`.
This file proves that **the two transposes are invertible together**, which is
`DifferentialGradedModule.isIso_homEquiv_symm_iff_restrictBase` read at the class of a
homomorphism of modules.

## Main results

* `DifferentialGradedModule.derivedRestrictionRestrictBaseIso_hom_app_Q`: the compatibility of
  regarding over `S` with derived restriction of scalars, at the class of a module.
* `DifferentialGradedModule.isIso_derivedTranspose_iff_restrictBase`: **the transpose of
  `derivedTrans τ g` is invertible exactly when the transpose of `derivedTrans` of `g` regarded
  over `S` is.**

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra S R]
  {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **The compatibility of regarding over `S` with derived restriction of scalars, at the class
of an object of the homotopy category.** -/
theorem derivedRestrictionRestrictBaseIso_hom_app_Q (φ : A.Hom B) (X : HomotopyCategory B) :
    (derivedRestrictionRestrictBaseIso S φ).hom.app ((quasiIsomorphisms' B).Q.obj X) =
      (derivedRestrictBaseEquiv S A).functor.map ((derivedRestrictionFactorization φ).hom.app X) ≫
        (derivedRestrictBaseFactorization S A).hom.app
          ((restrictScalarsHomotopyFunctor φ).obj X) ≫
        (quasiIsomorphisms' (A.restrictBase S)).Q.map
          ((restrictScalarsHomotopyRestrictBaseIso S φ).hom.app X) ≫
        (derivedRestrictionFactorization (φ.restrictBase S)).inv.app
          ((restrictBaseHomotopyFunctor S B).obj X) ≫
        (derivedRestriction (φ.restrictBase S)).map
          ((derivedRestrictBaseFactorization S B).inv.app X) := by
  unfold derivedRestrictionRestrictBaseIso baseRingLiftNatIso
  simp [Localization.liftNatIso, Localization.liftNatTrans_app]

/-- The compatibility of regarding over `S` with restriction of scalars on homotopy categories is
the identity at the class of a module. -/
theorem restrictScalarsHomotopyRestrictBaseIso_hom_app (φ : A.Hom B)
    (N : DifferentialGradedModule.{u, u, u} B) :
    (restrictScalarsHomotopyRestrictBaseIso S φ).hom.app ((toHomotopyCategory B).obj N) = 𝟙 _ := by
  simp [restrictScalarsHomotopyRestrictBaseIso, restrictScalarsHomotopyFunctorIso,
    restrictBaseHomotopyFunctorIso, restrictScalarsRestrictBaseIso]
  rfl

/-- The chase behind `DifferentialGradedModule.isIso_derivedTranspose_iff_restrictBase`, for
abstract categories and functors: the two factorizations cancel, and what remains is the
naturality of the comparison of regarding over `S` with the localizations. -/
theorem derivedTranspose_restrictBase_aux {D₁ D₂ D₃ : Type*} [Category D₁] [Category D₂]
    [Category D₃] (RB : D₁ ⥤ D₂) (R' : D₃ ⥤ D₂) {x y y' : D₁} {u v w : D₂} {p p' : D₃}
    (a : x ⟶ y) (bi : y ⟶ y') (bh : y' ⟶ y) (hb : bi ≫ bh = 𝟙 y)
    (c : RB.obj y ⟶ u) (q : u ⟶ v) (e : v ⟶ R'.obj p) (ri : p ⟶ p') (rh : p' ⟶ p)
    (hr : ri ≫ rh = 𝟙 p) (i : RB.obj x ⟶ w) (m : w ⟶ v) (hnat : RB.map a ≫ c ≫ q = i ≫ m)
    (one₁ one₂ : R'.obj p ⟶ R'.obj p) (h₁ : one₁ = 𝟙 _) (h₂ : one₂ = 𝟙 _) :
    (RB.map (a ≫ bi) ≫ (RB.map bh ≫ c ≫ q ≫ e ≫ R'.map ri)) ≫ R'.map rh =
      i ≫ (m ≫ e) ≫ (one₁ ≫ one₂) := by
  have h3 : RB.map (a ≫ bi) ≫ RB.map bh = RB.map a := by
    rw [← RB.map_comp, Category.assoc, hb, Category.comp_id]
  have h4 : R'.map ri ≫ R'.map rh = 𝟙 _ := by rw [← R'.map_comp, hr, R'.map_id]
  simp only [Category.assoc, h₁, h₂, Category.comp_id]
  rw [h4, Category.comp_id, ← Category.assoc (RB.map (a ≫ bi)), h3]
  have h5 := congrArg (· ≫ e) hnat
  simp only [Category.assoc] at h5
  exact h5

/-- `f ≫ g ≫ 𝟙 = f ≫ g`, for an abstract category: in a localized category the identity is
presented at another instance path. -/
theorem comp_comp_id_aux {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g ≫ 𝟙 Z = f ≫ g := by
  rw [Category.comp_id]

/-- **The transpose of `derivedTrans τ g` is invertible exactly when the transpose of
`derivedTrans` of `g` regarded over `S` is.** -/
theorem isIso_derivedTranspose_iff_restrictBase (τ : A.Hom B)
    {N₁ : DifferentialGradedModule.{u, u, u} A}
    {N₀ : DifferentialGradedModule.{u, u, u} B} (g : N₁ ⟶ restrictScalars τ N₀) :
    IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction τ).homEquiv
        _ _).symm (derivedTrans τ g)) ↔
      IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
        (τ.restrictBase S)).homEquiv _ _).symm
        (derivedTrans (τ.restrictBase S) (show restrictBaseObj S N₁ ⟶
          restrictScalars (τ.restrictBase S) (restrictBaseObj S N₀) from
            restrictBaseHom S g))) := by
  rw [isIso_homEquiv_symm_iff_restrictBase S τ (derivedTrans τ g)]
  refine Adjunction.isIso_homEquiv_symm_iff_of_fullyFaithful _ _ (𝟭 _) (𝟭 _)
    (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm) _ _
    ((derivedRestrictBaseFactorization S A).app ((toHomotopyCategory A).obj N₁))
    ((derivedRestrictBaseFactorization S B).app ((toHomotopyCategory B).obj N₀)) ?_
  rw [derivedRestrictionRestrictBaseIso_hom_app_Q]
  have hnat := (derivedRestrictBaseFactorization S A).hom.naturality
    ((toHomotopyCategory A).map g)
  have hid : (quasiIsomorphisms' (A.restrictBase S)).Q.map
      ((restrictScalarsHomotopyRestrictBaseIso S τ).hom.app ((toHomotopyCategory B).obj N₀)) =
      𝟙 _ := by
    rw [restrictScalarsHomotopyRestrictBaseIso_hom_app]
    exact CategoryTheory.Functor.map_id _ _
  refine derivedTranspose_restrictBase_aux (derivedRestrictBaseEquiv S A).functor
    (derivedRestriction (τ.restrictBase S)) _ _ _
    ((derivedRestrictionFactorization τ).inv_hom_id_app _) _ _ _ _ _
    ((derivedRestrictBaseFactorization S B).inv_hom_id_app _) _ _ ?_ _ _ rfl rfl
  rw [hid]
  exact (comp_comp_id_aux _ _).trans hnat

/-! ### Transposes along a square of algebras over two base rings -/

section Square

variable {A₁ A₀ : DifferentialGradedAlgebra.{u, u} R} (τ : A₁.Hom A₀)
  {BV BU : DifferentialGradedAlgebra.{u, u} S} (ρ : BV.Hom BU)
  (σV : (A₁.restrictBase S).Hom BV) (σU : (A₀.restrictBase S).Hom BU)
  (hcomm : ∀ x, ρ.toAlgebraHom (σV.toAlgebraHom x) =
    σU.toAlgebraHom ((τ.restrictBase S).toAlgebraHom x))
  {PV : DifferentialGradedModule.{u, u, u} BV} {PU : DifferentialGradedModule.{u, u, u} BU}
  (m : PV ⟶ restrictScalars ρ PU)
  (g : extendBaseObj S (restrictScalars σV PV) ⟶
    restrictScalars τ (extendBaseObj S (restrictScalars σU PU)))
  (hg : ∀ x, g.toFun x = m.toFun x)

include hcomm hg in
/-- **A square of homomorphisms of differential graded algebras over two base rings carries
transposes to transposes.** Let `τ : A₁ → A₀` be a homomorphism of differential graded
`R`-algebras, `ρ : B_V → B_U` one of differential graded `S`-algebras, and `σ_V`, `σ_U`
quasi-isomorphisms from `A₁` and `A₀` regarded over `S` to `B_V` and `B_U` forming a commutative
square. If `m : P_V ⟶ P_U|_ρ` has an invertible transpose `P_V ⊗^𝐋_{B_V} B_U ⟶ P_U`, then so does
the homomorphism `g` of the modules `P_V` and `P_U` read over `A₁` and `A₀` with `R` acting
through them, provided `g` and `m` have the same underlying map. -/
theorem isIso_derivedTranspose_of_square
    (hV : ∀ k : ℤ, Function.Bijective (σV.cohomologyMap k))
    (hU : ∀ k : ℤ, Function.Bijective (σU.cohomologyMap k))
    (hm : IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction
        ρ).homEquiv _ _).symm ((quasiIsomorphisms' BV).Q.map ((toHomotopyCategory BV).map m) ≫
          (restrictScalarsClassIso ρ PU).hom))) :
    IsIso (((DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction τ).homEquiv
        _ _).symm (derivedTrans τ g)) := by
  rw [isIso_derivedTranspose_iff_restrictBase S τ g]
  refine (isIso_homEquiv_symm_square_iff (τ.restrictBase S) ρ σV σU hcomm m
    (show restrictBaseObj S (extendBaseObj S (restrictScalars σV PV)) ⟶
      restrictScalars (τ.restrictBase S)
        (restrictBaseObj S (extendBaseObj S (restrictScalars σU PU))) from restrictBaseHom S g)
    (restrictBaseCounitIso S A₁ (restrictScalars σV PV))
    (restrictBaseCounitIso S A₀ (restrictScalars σU PU)) hV hU ?_).2 hm
  exact DifferentialGradedModule.Hom.ext (LinearMap.ext fun x => hg x)

end Square

end DifferentialGradedModule

end
