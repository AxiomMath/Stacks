module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerivedComp
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` and the composition of right derived functors

Let `r_A : 𝒜' ⥤ 𝒜`, `r_B : ℬ' ⥤ ℬ`, `r_C : 𝒞' ⥤ 𝒞` be exact functors ("restriction of scalars"),
and let `F' : 𝒜' ⥤ ℬ'`, `G' : ℬ' ⥤ 𝒞'`, `H' : 𝒜' ⥤ 𝒞'` and `F : 𝒜 ⥤ ℬ`, `G : ℬ ⥤ 𝒞`,
`H : 𝒜 ⥤ 𝒞` be additive functors with `F'`, `F` preserving injective objects, related by
`e' : F' ⋙ G' ≅ H'`, `e : F ⋙ G ≅ H` and by commutations `F' ⋙ r_B ≅ r_A ⋙ F`,
`G' ⋙ r_C ≅ r_B ⋙ G`, `H' ⋙ r_C ≅ r_A ⋙ H`. Each commutation gives a comparison of right derived
functors `CategoryTheory.Functor.rightDerivedRestrictionIso`, and `e'`, `e` give composition
comparisons `RH' ≅ RF' ⋙ RG'`, `RH ≅ RF ⋙ RG`
(`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso`). This file proves that the
comparisons are compatible as soon as the underived square commutes
(`CategoryTheory.Functor.rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso`).

For direct images followed by direct images this is
`Stacks.EtaleCohomology.restrictScalars_derivedDirectImageComp`; the case used in the Trace
Formula chapter is a direct image followed by global sections, with restriction of scalars along
`ℤ →+* Λ`: it says that the identification `Hⁱ(B, g_* N) ≅ Hⁱ(A, N)` for an integral `g` does
not depend on whether the cohomology is computed over `Λ` or over `ℤ`.

The proof is the one of `restrictScalars_derivedDirectImageComp`: both sides are
transformations out of `RH' ⋙ r_C`, which is a right derived functor of `H' ⋙ r_C`, so they are
compared after its unit, where every comparison is computed by its factorization and what is
left is the underived square, applied degreewise.

On an object placed in degree zero the comparison is computed by the underived one
(`CategoryTheory.Functor.rightDerivedPlusUnitSingle_comp_rightDerivedRestrictionIso_hom_app`):
`r_M` of the canonical map `(G'X)[0] ⟶ RG'(X[0])`, followed by the comparison, is `e` placed in
degree zero followed by the canonical map for `G` at `r_A X`.

## Main results

* `CategoryTheory.Functor.rightDerivedPlusUnitSingle_comp_rightDerivedRestrictionIso_hom_app`.
* `CategoryTheory.Functor.rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

/-- The diagram chase of `rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso`
after the unit, abstract in the objects: the morphisms it is applied to are components of
comparisons of right derived functors, whose sources and targets agree only definitionally. -/
private lemma restriction_comp_chase {𝒞 : Type*} [Category* 𝒞]
    {P₀ P₁ P₂ P₃ P₄ P₇ P₈ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ R₁ R₂ R₃ S₁ : 𝒞}
    {a₀ : P₀ ⟶ P₁} {a₁ : P₁ ⟶ P₂} {b₁ : P₂ ⟶ P₃} {d₁ : P₃ ⟶ P₈}
    {x₁ : P₀ ⟶ Q₁} {x₂ : Q₁ ⟶ Q₂} {x₃ : Q₂ ⟶ P₂} {b₂ : Q₂ ⟶ Q₃} {b₃ : Q₃ ⟶ P₃}
    {f₁ : Q₁ ⟶ Q₄} {q₁ : Q₄ ⟶ Q₅} {u₁ : Q₅ ⟶ Q₆} {c₁ : Q₆ ⟶ Q₃}
    {g₁ : Q₆ ⟶ Q₇} {g₂ : Q₇ ⟶ P₇} {g₃ : P₇ ⟶ P₈}
    {f₀ : P₀ ⟶ R₁} {y₁ : R₁ ⟶ Q₄} {q₂ : Q₅ ⟶ P₄} {u₂ : P₄ ⟶ Q₇} {z₁ : R₁ ⟶ R₂} {z₂ : R₂ ⟶ P₄}
    {r₁ : P₁ ⟶ S₁} {r₂ : S₁ ⟶ P₈} {w₁ : R₂ ⟶ R₃} {w₂ : R₃ ⟶ S₁} {r₃ : R₃ ⟶ P₇}
    (ha : a₀ ≫ a₁ = x₁ ≫ x₂ ≫ x₃) (hb : x₃ ≫ b₁ = b₂ ≫ b₃)
    (hc : x₂ ≫ b₂ = f₁ ≫ q₁ ≫ u₁ ≫ c₁) (hd : c₁ ≫ b₃ ≫ d₁ = g₁ ≫ g₂ ≫ g₃)
    (hf : x₁ ≫ f₁ = f₀ ≫ y₁) (he : q₂ ≫ u₂ = u₁ ≫ g₁) (hj : y₁ ≫ q₁ ≫ q₂ = z₁ ≫ z₂)
    (hg : a₀ ≫ r₁ = f₀ ≫ z₁ ≫ w₁ ≫ w₂) (hh : w₂ ≫ r₂ = r₃ ≫ g₃)
    (hi : w₁ ≫ r₃ = z₂ ≫ u₂ ≫ g₂) :
    a₀ ≫ a₁ ≫ b₁ ≫ d₁ = a₀ ≫ r₁ ≫ r₂ := by
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd, ← reassoc_of% he, reassoc_of% hf,
    reassoc_of% hj, reassoc_of% hg, hh, reassoc_of% hi]

/-- A functor applied to a fourfold composite, bracketed as `(a ≫ b) ≫ c ≫ d`. Stated on
variables, for morphisms whose sources and targets agree only definitionally. -/
private lemma map_comp_four {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ Z₂ Z₃ Z₄ : 𝒞} (a : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂) (c : Z₂ ⟶ Z₃) (d : Z₃ ⟶ Z₄) :
    Φ.map ((a ≫ b) ≫ c ≫ d) = Φ.map a ≫ Φ.map b ≫ Φ.map c ≫ Φ.map d := by simp

/-- A functor applied to a fourfold composite `a ≫ b ≫ c ≫ d`, on variables. -/
private lemma map_comp_four' {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ Z₂ Z₃ Z₄ : 𝒞} (a : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂) (c : Z₂ ⟶ Z₃) (d : Z₃ ⟶ Z₄) :
    Φ.map (a ≫ b ≫ c ≫ d) = Φ.map a ≫ Φ.map b ≫ Φ.map c ≫ Φ.map d := by simp

/-- A functor applied to a threefold composite, on variables. -/
private lemma map_comp_three {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ Z₂ Z₃ : 𝒞} (a : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂) (c : Z₂ ⟶ Z₃) :
    Φ.map (a ≫ b ≫ c) = Φ.map a ≫ Φ.map b ≫ Φ.map c := by simp

/-- A functor applied to both sides of an equation between threefold composites, on variables. -/
private lemma map_comp_three_congr {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ Z₂ Z₃ Y₁ Y₂ : 𝒞} {a : Z₀ ⟶ Z₁} {b : Z₁ ⟶ Z₂} {c : Z₂ ⟶ Z₃}
    {a' : Z₀ ⟶ Y₁} {b' : Y₁ ⟶ Y₂} {c' : Y₂ ⟶ Z₃}
    (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    Φ.map a ≫ Φ.map b ≫ Φ.map c = Φ.map a' ≫ Φ.map b' ≫ Φ.map c' := by
  rw [← map_comp_three, ← map_comp_three, h]

/-- A functor applied to `g ≫ f` with `g ≫ f = 𝟙`, on variables. -/
private lemma map_comp_eq_id {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Φ : 𝒞 ⥤ 𝒟)
    {Z₀ Z₁ : 𝒞} (g : Z₀ ⟶ Z₁) (f : Z₁ ⟶ Z₀) (h : g ≫ f = 𝟙 Z₀) :
    Φ.map g ≫ Φ.map f = 𝟙 (Φ.obj Z₀) := by rw [← Φ.map_comp, h, Φ.map_id]

/-- The diagram chase of `rightDerivedPlusUnitSingle_comp_rightDerivedRestrictionIso_hom_app`,
abstract in the objects. -/
private lemma single_restriction_chase {𝒞 : Type*} [Category* 𝒞]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ Q₂ Q₃ Q₅ R₁ R₂ R₃ R₄ R₅ : 𝒞}
    {u : P₀ ⟶ P₄} {r₀ : P₄ ⟶ P₅} {ρ : P₅ ⟶ P₉} {μ : P₀ ⟶ R₄} {sm : R₄ ⟶ R₅} {υ : R₅ ⟶ P₉}
    {m₁ : P₀ ⟶ P₁} {m₂ : P₁ ⟶ P₂} {m₃ : P₂ ⟶ P₃} {m₄ : P₃ ⟶ P₄}
    {n₁ : P₅ ⟶ P₆} {n₂ : P₆ ⟶ P₇} {n₃ : P₇ ⟶ P₈} {n₄ : P₈ ⟶ P₉}
    {r₁ : P₃ ⟶ P₆} {k₁ : P₆ ⟶ P₅} {f₁ : P₂ ⟶ Q₂} {p₁ : Q₂ ⟶ Q₃} {v₁ : Q₃ ⟶ P₇}
    {w₁ : P₇ ⟶ P₆} {p₂ : Q₃ ⟶ Q₅} {v₂ : Q₅ ⟶ P₈} {f₀ : P₁ ⟶ R₁} {y₁ : R₁ ⟶ Q₂}
    {z₁ : R₁ ⟶ R₂} {z₂ : R₂ ⟶ R₃} {z₃ : R₃ ⟶ Q₅} {t₁ : R₂ ⟶ R₄} {t₂ : R₄ ⟶ R₂}
    {s₁ : R₅ ⟶ R₃}
    (hU : u = m₁ ≫ m₂ ≫ m₃ ≫ m₄) (hS : ρ = n₁ ≫ n₂ ≫ n₃ ≫ n₄)
    (h₁ : m₄ ≫ r₀ = r₁ ≫ k₁) (hk : k₁ ≫ n₁ = 𝟙 _)
    (h₂ : m₃ ≫ r₁ = f₁ ≫ p₁ ≫ v₁ ≫ w₁) (hw : w₁ ≫ n₂ = 𝟙 _)
    (h₄ : p₂ ≫ v₂ = v₁ ≫ n₃) (h₃ : m₂ ≫ f₁ = f₀ ≫ y₁) (hH : y₁ ≫ p₁ ≫ p₂ = z₁ ≫ z₂ ≫ z₃)
    (hS₂ : μ = m₁ ≫ f₀ ≫ z₁ ≫ t₁) (hU₂ : υ = s₁ ≫ z₃ ≫ v₂ ≫ n₄) (h₅ : sm ≫ s₁ = t₂ ≫ z₂)
    (ht : t₁ ≫ t₂ = 𝟙 _) :
    u ≫ r₀ ≫ ρ = μ ≫ sm ≫ υ := by
  rw [hU, hS, hS₂, hU₂]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% hk, reassoc_of% h₂, reassoc_of% hw,
    ← reassoc_of% h₄, reassoc_of% h₃, reassoc_of% hH, reassoc_of% h₅, reassoc_of% ht]

section Collapse

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]

/-- The action on bounded below homotopy categories of an isomorphism `P ⋙ Q ≅ P' ⋙ Q'`, read
through the identifications of the composites, is the degreewise action of the isomorphism. -/
theorem mapHomotopyCategoryPlusCompIso_refl_natIso_hom_app {P : A ⥤ B} {Q : B ⥤ C} {P' : A ⥤ D}
    {Q' : D ⥤ C} [P.Additive] [Q.Additive] [P'.Additive] [Q'.Additive] (η : P ⋙ Q ≅ P' ⋙ Q')
    (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).hom.app K ≫
        (mapHomotopyCategoryPlusNatIso η).hom.app K ≫
        (mapHomotopyCategoryPlusCompIso (Iso.refl (P' ⋙ Q'))).inv.app K =
      (Stacks.Cohomology.BaseChange.mapPlus η.hom).app K := by
  have hc : (mapHomotopyCategoryPlusCompIso (Iso.refl (P' ⋙ Q'))).inv.app K = 𝟙 _ := by
    apply (HomotopyCategory.Plus.ι C).map_injective
    rfl
  rw [mapHomotopyCategoryPlusCompIso_refl_hom_app, hc]
  exact (Category.id_comp _).trans ((Category.comp_id _).trans
    (congrArg (fun t => NatTrans.app t K) (mapHomotopyCategoryPlusNatIso_hom η)))

end Collapse

section Single

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  {G' : A' ⥤ M'} {G : A ⥤ M} {rA : A' ⥤ A} {rM : M' ⥤ M}
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive] (e : G' ⋙ rM ≅ rA ⋙ G)

/-- The underived square `e`, applied degreewise to a complex concentrated in degree zero, read
through the identifications of an additive functor applied to such a complex. -/
private lemma single_restriction_homotopy (X : A') :
    rM.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient M').map
        ((Stacks.DerivedIndexing.mapSinglePlus G' 0).app X)) ≫
      (Stacks.Cohomology.BaseChange.mapPlus e.hom).app
        ((HomotopyCategory.Plus.singleFunctor A' 0).obj X) ≫
      G.mapHomotopyCategoryPlus.map (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom =
    (rM.mapHomotopyCategoryPlusObjSingleIso 0 (G'.obj X)).hom ≫
      (HomotopyCategory.Plus.singleFunctor M 0).map (e.hom.app X) ≫
      (HomotopyCategory.Plus.quotient M).map
        ((Stacks.DerivedIndexing.mapSinglePlus G 0).app (rA.obj X)) := by
  apply (HomotopyCategory.Plus.ι M).map_injective
  have t1 : (HomotopyCategory.Plus.ι M).map (rM.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient M').map
        ((Stacks.DerivedIndexing.mapSinglePlus G' 0).app X))) =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((rM.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℤ) 0).inv.app X)) :=
    rfl
  have t2 : (HomotopyCategory.Plus.ι M).map ((Stacks.Cohomology.BaseChange.mapPlus e.hom).app
        ((HomotopyCategory.Plus.singleFunctor A' 0).obj X)) =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj X)) := rfl
  have t3 : (HomotopyCategory.Plus.ι M).map
      (G.mapHomotopyCategoryPlus.map (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex rA (ComplexShape.up ℤ) 0).hom.app
            X)) := by
    have t3a : (HomotopyCategory.Plus.ι M).map
        (G.mapHomotopyCategoryPlus.map (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) =
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map ((HomotopyCategory.Plus.ι A).map
          (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) := rfl
    have t3b : (HomotopyCategory.Plus.ι A).map (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom =
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex rA (ComplexShape.up ℤ) 0).hom.app X) :=
      (HomotopyCategory.Plus.ι A).map_preimage _
    rw [t3a, t3b]
    rfl
  have t4 : (HomotopyCategory.Plus.ι M).map
      (rM.mapHomotopyCategoryPlusObjSingleIso 0 (G'.obj X)).hom =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex rM (ComplexShape.up ℤ) 0).hom.app
          (G'.obj X)) := (HomotopyCategory.Plus.ι M).map_preimage _
  have t5 : (HomotopyCategory.Plus.ι M).map
      ((HomotopyCategory.Plus.singleFunctor M 0).map (e.hom.app X)) =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single M (ComplexShape.up ℤ) 0).map (e.hom.app X)) := rfl
  have t6 : (HomotopyCategory.Plus.ι M).map ((HomotopyCategory.Plus.quotient M).map
        ((Stacks.DerivedIndexing.mapSinglePlus G 0).app (rA.obj X))) =
      (HomotopyCategory.quotient M (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app
          (rA.obj X)) := rfl
  have key : (rM.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℤ) 0).inv.app X) ≫
        (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj X) ≫
        (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex rA (ComplexShape.up ℤ) 0).hom.app X) =
      (HomologicalComplex.singleMapHomologicalComplex rM (ComplexShape.up ℤ) 0).hom.app
          (G'.obj X) ≫
        (HomologicalComplex.single M (ComplexShape.up ℤ) 0).map (e.hom.app X) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app
          (rA.obj X) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
      have hn := e.hom.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv
      simp only [Functor.comp_map] at hn
      rw [reassoc_of% hn, Iso.inv_hom_id_assoc]
      simp only [Functor.comp_obj, Iso.inv_hom_id_assoc]
      rw [← Functor.map_comp_assoc G, ← rA.map_comp, Iso.inv_hom_id, rA.map_id, G.map_id,
        Category.id_comp]
    · refine IsZero.eq_of_src ?_ _ _
      exact rM.map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (G'.obj X) n hn)
  let q := HomotopyCategory.quotient M (ComplexShape.up ℤ)
  exact (map_comp_three _ _ _ _).trans
    ((congrArg₂ (· ≫ ·) t1 (congrArg₂ (· ≫ ·) t2 t3)).trans
    ((map_comp_three_congr q key).trans
    ((congrArg₂ (· ≫ ·) t4 (congrArg₂ (· ≫ ·) t5 t6)).symm.trans (map_comp_three _ _ _ _).symm)))

variable [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M']
  [HasDerivedCategory M] [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rM] [PreservesFiniteColimits rM]

/-- **The comparison `RG' ⋙ r_M ≅ r_A ⋙ RG` on an object placed in degree zero.** `r_M` of the
canonical map `(G'X)[0] ⟶ RG'(X[0])` followed by the comparison is `e` placed in degree zero
followed by the canonical map `(G(r_A X))[0] ⟶ RG((r_A X)[0])`, up to the identifications
`r_M((G'X)[0]) ≅ (r_M G' X)[0]` and `r_A(X[0]) ≅ (r_A X)[0]`. -/
theorem rightDerivedPlusUnitSingle_comp_rightDerivedRestrictionIso_hom_app
    (hac : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) (X : A') :
    rM.mapDerivedCategoryPlus.map ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G').app X) ≫
        (rightDerivedRestrictionIso G' G rA rM e hac).hom.app
          ((DerivedCategory.Plus.singleFunctor A' 0).obj X) ≫
        G.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusObjSingleIso X).hom =
      (rM.mapDerivedCategoryPlusObjSingleIso (G'.obj X)).hom ≫
        (DerivedCategory.Plus.singleFunctor M 0).map (e.hom.app X) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G).app (rA.obj X) := by
  let sK' := (HomotopyCategory.Plus.singleFunctor A' 0).obj X
  have M1 := Stacks.DerivedIndexing.mapSingleFunctorCompQhIso_inv_app_eq G' X
  have hU1 : (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G').app X =
      (Functor.mapSingleFunctorCompQhIso G').inv.app X ≫
        G'.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A' 0).obj X) ≫
          G'.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := A') 0).inv.app X) := rfl
  have hU := (congrArg rM.mapDerivedCategoryPlus.map
      (hU1.trans (congrArg (· ≫ _) M1))).trans (map_comp_four _ _ _ _ _)
  have hS := (congrArg G.rightDerivedFunctorPlus.map
      (Functor.mapDerivedCategoryPlusObjSingleIso_hom rA X)).trans (map_comp_four' _ _ _ _ _)
  have h₁ := (rightDerivedRestrictionIso G' G rA rM e hac).hom.naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := A') 0).inv.app X)
  have hk := map_comp_eq_id G.rightDerivedFunctorPlus _ _
    (map_comp_eq_id rA.mapDerivedCategoryPlus _ _
      (Iso.inv_hom_id_app (Functor.singleFunctorPlusIsoCompQh (A := A') 0) X))
  have h₂ := map_unit_comp_rightDerivedRestrictionIso_hom_app G' G rA rM e hac sK'
  rw [mapHomotopyCategoryPlusCompIso_refl_natIso_hom_app] at h₂
  have hw := map_comp_eq_id G.rightDerivedFunctorPlus _ _
    (Iso.inv_hom_id_app rA.mapDerivedCategoryPlusFactorsh sK')
  have h₄ :=
    G.rightDerivedFunctorPlusUnit.naturality (rA.mapHomotopyCategoryPlusObjSingleIso 0 X).hom
  have h₃ := rM.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((HomotopyCategory.Plus.quotient M').map ((Stacks.DerivedIndexing.mapSinglePlus G' 0).app X))
  have hH := map_comp_three_congr DerivedCategory.Plus.Qh (single_restriction_homotopy e X)
  have hS₂ := Functor.mapDerivedCategoryPlusObjSingleIso_hom rM (G'.obj X)
  have hU₂a : (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G).app (rA.obj X) =
      (Functor.mapSingleFunctorCompQhIso G).inv.app (rA.obj X) ≫
        G.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj (rA.obj X)) ≫
          G.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app (rA.obj X)) := rfl
  have hU₂ := (hU₂a.trans (congrArg (· ≫ _)
    (Stacks.DerivedIndexing.mapSingleFunctorCompQhIso_inv_app_eq G (rA.obj X)))).trans
      (Category.assoc _ _ _)
  have h₅ := (Functor.singleFunctorPlusIsoCompQh (A := M) 0).hom.naturality (e.hom.app X)
  have ht := Iso.inv_hom_id_app (Functor.singleFunctorPlusIsoCompQh (A := M) 0)
    (rM.obj (G'.obj X))
  exact single_restriction_chase hU hS h₁ hk h₂ hw h₄ h₃ hH hS₂ hU₂ h₅ ht

end Single

section Composition

variable {A' B' C' A B C : Type*} [Category* A'] [Category* B'] [Category* C'] [Category* A]
  [Category* B] [Category* C] [Abelian A'] [Abelian B'] [Abelian C'] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A'] [EnoughInjectives B'] [EnoughInjectives C'] [EnoughInjectives A]
  [EnoughInjectives B]
  {F' : A' ⥤ B'} {G' : B' ⥤ C'} {H' : A' ⥤ C'} {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
  {rA : A' ⥤ A} {rB : B' ⥤ B} {rC : C' ⥤ C}
  [F'.Additive] [G'.Additive] [H'.Additive] [F.Additive] [G.Additive] [H.Additive]
  [rA.Additive] [rB.Additive] [rC.Additive]
  [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [PreservesFiniteLimits rB] [PreservesFiniteColimits rB]
  [PreservesFiniteLimits rC] [PreservesFiniteColimits rC]
  (e' : F' ⋙ G' ≅ H') (e : F ⋙ G ≅ H) (eF : F' ⋙ rB ≅ rA ⋙ F) (eG : G' ⋙ rC ≅ rB ⋙ G)
  (eH : H' ⋙ rC ≅ rA ⋙ H)

omit [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C'] [HasDerivedCategory A]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives A'] [EnoughInjectives B']
  [EnoughInjectives C'] [EnoughInjectives A] [EnoughInjectives B] [PreservesFiniteLimits rA]
  [PreservesFiniteColimits rA] [PreservesFiniteLimits rB] [PreservesFiniteColimits rB]
  [PreservesFiniteLimits rC] [PreservesFiniteColimits rC] in
/-- The underived square, applied degreewise on bounded below homotopy categories. -/
private lemma restriction_comp_homotopy
    (h : ∀ X : A', rC.map (e'.inv.app X) ≫ eG.hom.app (F'.obj X) ≫ G.map (eF.hom.app X) =
      eH.hom.app X ≫ e.inv.app (rA.obj X))
    (K : HomotopyCategory.Plus A') :
    rC.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusCompIso e').inv.app K) ≫
        (Stacks.Cohomology.BaseChange.mapPlus eG.hom).app (F'.mapHomotopyCategoryPlus.obj K) ≫
        G.mapHomotopyCategoryPlus.map ((Stacks.Cohomology.BaseChange.mapPlus eF.hom).app K) =
      (Stacks.Cohomology.BaseChange.mapPlus eH.hom).app K ≫
        (mapHomotopyCategoryPlusCompIso e).inv.app (rA.mapHomotopyCategoryPlus.obj K) := by
  have hτ : Functor.whiskerRight e'.inv rC ≫ Functor.whiskerLeft F' eG.hom ≫
      Functor.whiskerRight eF.hom G = eH.hom ≫ Functor.whiskerLeft rA e.inv := by
    ext X
    exact h X
  have hK := congrArg (fun τ => (Stacks.Cohomology.BaseChange.mapPlus τ).app K) hτ
  simp only [Stacks.Cohomology.BaseChange.mapPlus_comp, NatTrans.comp_app] at hK
  exact hK

variable [F'.PreservesInjectiveObjects] [F.PreservesInjectiveObjects]
  (hF : ∀ I : A', Injective I → F.rightAcyclic (rA.obj I))
  (hG : ∀ I : B', Injective I → G.rightAcyclic (rB.obj I))
  (hH : ∀ I : A', Injective I → H.rightAcyclic (rA.obj I))

/-- `rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso` after the unit of
`RH'` at a bounded below homotopy class `K`. -/
private lemma restriction_comp_unit
    (h : ∀ X : A', rC.map (e'.inv.app X) ≫ eG.hom.app (F'.obj X) ≫ G.map (eF.hom.app X) =
      eH.hom.app X ≫ e.inv.app (rA.obj X))
    (K : HomotopyCategory.Plus A') :
    rC.mapDerivedCategoryPlus.map (H'.rightDerivedFunctorPlusUnit.app K) ≫
        rC.mapDerivedCategoryPlus.map
          ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F' G' H' e').hom.app
            (DerivedCategory.Plus.Qh.obj K)) ≫
        (rightDerivedRestrictionIso G' G rB rC eG hG).hom.app
          (F'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        G.rightDerivedFunctorPlus.map
          ((rightDerivedRestrictionIso F' F rA rB eF hF).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      rC.mapDerivedCategoryPlus.map (H'.rightDerivedFunctorPlusUnit.app K) ≫
        (rightDerivedRestrictionIso H' H rA rC eH hH).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app
          (rA.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
  have ha := unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom_app F' G' H' e' K
  have ha' := (rC.mapDerivedCategoryPlus.map_comp _ _).symm.trans
    ((congrArg rC.mapDerivedCategoryPlus.map ha).trans
      ((rC.mapDerivedCategoryPlus.map_comp _ _).trans
        (congrArg (_ ≫ ·) (rC.mapDerivedCategoryPlus.map_comp _ _))))
  have hb := (rightDerivedRestrictionIso G' G rB rC eG hG).hom.naturality
    (F'.rightDerivedFunctorPlusUnit.app K)
  have hc := map_unit_comp_rightDerivedRestrictionIso_hom_app G' G rB rC eG hG
    (F'.mapHomotopyCategoryPlus.obj K)
  rw [mapHomotopyCategoryPlusCompIso_refl_natIso_hom_app] at hc
  have hd := map_unit_comp_rightDerivedRestrictionIso_hom_app F' F rA rB eF hF K
  rw [mapHomotopyCategoryPlusCompIso_refl_natIso_hom_app] at hd
  have hd' : rB.mapDerivedCategoryPlusFactorsh.inv.app (F'.mapHomotopyCategoryPlus.obj K) ≫
      rB.mapDerivedCategoryPlus.map (F'.rightDerivedFunctorPlusUnit.app K) ≫
      (rightDerivedRestrictionIso F' F rA rB eF hF).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((Stacks.Cohomology.BaseChange.mapPlus eF.hom).app K) ≫
        F.rightDerivedFunctorPlusUnit.app (rA.mapHomotopyCategoryPlus.obj K) ≫
        F.rightDerivedFunctorPlus.map (rA.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    rw [hd, Iso.inv_hom_id_app_assoc]
    rfl
  have hd'' := map_comp_three_congr G.rightDerivedFunctorPlus hd'
  have he := G.rightDerivedFunctorPlusUnit.naturality
    ((Stacks.Cohomology.BaseChange.mapPlus eF.hom).app K)
  have hf := rC.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((mapHomotopyCategoryPlusCompIso e').inv.app K)
  have hg := map_unit_comp_rightDerivedRestrictionIso_hom_app H' H rA rC eH hH K
  rw [mapHomotopyCategoryPlusCompIso_refl_natIso_hom_app] at hg
  have hh := (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.naturality
    (rA.mapDerivedCategoryPlusFactorsh.inv.app K)
  have hi := unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom_app F G H e
    (rA.mapHomotopyCategoryPlus.obj K)
  have hj := (map_comp_three DerivedCategory.Plus.Qh _ _ _).symm.trans
    ((congrArg DerivedCategory.Plus.Qh.map (restriction_comp_homotopy e' e eF eG eH h K)).trans
      (DerivedCategory.Plus.Qh.map_comp _ _))
  exact restriction_comp_chase ha' hb hc hd'' hf he hj hg hh hi

/-- **The comparisons `RG' ⋙ r_M ≅ r_A ⋙ RG` are compatible with composition comparisons.** If
the underived square `r_C(e'⁻¹) ≫ e_G ≫ G(e_F) = e_H ≫ e⁻¹` commutes, then for every `M` in
`D⁺(𝒜')` the two identifications of `r_C(RH'(M))` with `RG(RF(r_A M))` agree: through
`RH' ≅ RF' ⋙ RG'` and the comparisons for `G'` and `F'`, or through the comparison for `H'`
and `RH ≅ RF ⋙ RG`. -/
theorem rightDerivedRestrictionIso_comp_rightDerivedFunctorPlusCompIsoOfIso
    (h : ∀ X : A', rC.map (e'.inv.app X) ≫ eG.hom.app (F'.obj X) ≫ G.map (eF.hom.app X) =
      eH.hom.app X ≫ e.inv.app (rA.obj X))
    (M : DerivedCategory.Plus A') :
    rC.mapDerivedCategoryPlus.map
        ((Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F' G' H' e').hom.app M) ≫
        (rightDerivedRestrictionIso G' G rB rC eG hG).hom.app (F'.rightDerivedFunctorPlus.obj M) ≫
        G.rightDerivedFunctorPlus.map ((rightDerivedRestrictionIso F' F rA rB eF hF).hom.app M) =
      (rightDerivedRestrictionIso H' H rA rC eH hH).hom.app M ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app
          (rA.mapDerivedCategoryPlus.obj M) := by
  have key := rightDerivedFunctorPlus_comp_mapDerivedCategoryPlus_ext H' rC
    (Functor.whiskerRight
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F' G' H' e').hom
        rC.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F'.rightDerivedFunctorPlus
        (rightDerivedRestrictionIso G' G rB rC eG hG).hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (rightDerivedRestrictionIso F' F rA rB eF hF).hom
        G.rightDerivedFunctorPlus)
    ((rightDerivedRestrictionIso H' H rA rC eH hH).hom ≫ Functor.whiskerLeft
        rA.mapDerivedCategoryPlus
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso F G H e).hom ≫
        (Functor.associator _ _ _).inv)
    (fun K => by
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
        Category.comp_id]
      exact restriction_comp_unit e' e eF eG eH hF hG hH h K)
  have hM := NatTrans.congr_app key M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at hM
  exact hM

end Composition

end CategoryTheory.Functor

end
