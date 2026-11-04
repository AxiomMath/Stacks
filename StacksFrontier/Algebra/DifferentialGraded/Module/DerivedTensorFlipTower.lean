module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlipRegular
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainTowerCounit
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrict

/-! # Base change is computed in either variable

Let `φ : A → C` be a homomorphism of differential graded algebras, `N` a right differential
graded `A`-module, `N₀` a right differential graded `C`-module and `g : N ⟶ N₀|_φ` a semilinear
homomorphism. Its derived transpose `N ⊗^𝐋_A C ⟶ N₀` is the comparison map of quasi-coherence:
the base change is computed by resolving the module `N`. The tower of Tag 0GZJ computes the same
base change the other way round, as the derived tensor product `X ⊗^𝐋_{A^{opp}} N̂` of the flip of
`N` with the left `A`-module `X = C`, which resolves `X`. This file proves that the two agree in
the only sense the tower needs: **if the derived transpose of `g` is an isomorphism, then so is the
map `X ⊗^𝐋_{A^{opp}} N̂ ⟶ X₀ ⊗^𝐋_{C^{opp}} N̂₀` that `g` induces**, where `X₀` is `C` over itself.

The proof resolves `N` by a module `P` orthogonal on the left to the acyclic modules. For such
`P` both derived tensor products are plain — the one in the bimodule variable by
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_flip_of_leftOrthogonal` — and the
plain map is the plain transpose of `P ⟶ N ⟶ N₀|_φ` read through
`DifferentialGraded.Bimodule.quasiIso_flipTensor_of_quasiIso_plainTranspose`. The resolution is
removed on the derived side by the second assertion of Tag 09S3.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorNatTrans_app_comp_comparison`: `1 ⊗ f` read through
  the comparisons of Tag 0BZ2 is ordinary tensoring with `f`.
* `DifferentialGraded.Bimodule.leftOrthogonal_restrictedRegularOpp`: the graded opposite of `C`,
  read over itself through a homomorphism acting as the identity, is orthogonal on the left to
  the acyclic modules.
* `DifferentialGraded.Bimodule.quasiIso_plainTranspose_of_isIso_derivedTranspose`: an invertible
  derived transpose has a plain transpose which is a quasi-isomorphism after precomposition with
  a resolution by a module orthogonal on the left to the acyclic modules.
* `DifferentialGraded.Bimodule.isIso_flipTowerMap_of_isIso_derivedTranspose`: **the map of
  derived tensor products in the flipped variable is an isomorphism.**

## References

* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3),
  [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) and
  [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX).
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) and
  [Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK), where it is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- An identity in a category with a functor, in the shape of the comparison of `1 ⊗ f` with the
comparisons of Tag 0BZ2. Stated for abstract categories, since in a localized category the two
sides present the morphisms at different instance paths. -/
theorem comparison_comp_aux {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y W Z : C} {o o' : D} (a : o ⟶ o') (c' : o' ⟶ Q.obj Z) (c : o ⟶ Q.obj X) (i : X ⟶ Y)
    (m : Y ⟶ W) (j : W ⟶ Z) (j' : Z ⟶ W) (hj : j ≫ j' = 𝟙 W)
    (h : a ≫ c' = c ≫ Q.map (i ≫ m ≫ j)) :
    a ≫ c' ≫ Q.map j' = (c ≫ Q.map i) ≫ Q.map m := by
  rw [← Category.assoc, h, Category.assoc, ← Q.map_comp, Category.assoc, Category.assoc, hj,
    Category.comp_id, Q.map_comp, Category.assoc]

/-- **`1 ⊗ f`, read through the comparisons of Tag 0BZ2, is ordinary tensoring with `f`.** -/
theorem derivedTensorNatTrans_app_comp_comparison {A B : DifferentialGradedAlgebra.{u, u} R}
    {N N' : Bimodule A B} (f : N ⟶ N') (X : DifferentialGradedModule.{u, u, u} A) :
    (derivedTensorNatTrans f).app ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ≫
        derivedTensorPlainComparison N' X =
      derivedTensorPlainComparison N X ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map (tensorHomOfBimoduleHom f X)) := by
  have h := derivedTensorNatTrans_app_comp_counit f ((toHomotopyCategory A).obj X)
  rw [ordinaryTensorNatTrans_app, tensorHomotopyNatTrans_app] at h
  exact comparison_comp_aux (quasiIsomorphisms' B).Q _ _ _ _ _ _ _
    ((tensorCompFunctor_quotient N').hom_inv_id_app X) h

/-- A homomorphism of differential graded algebras acting as the identity, read on the graded
opposite, acts as the identity. -/
theorem oppHom_apply_of_forall_eq {C : DifferentialGradedAlgebra.{u, u} R} (ι : C.Hom C)
    (hι : ∀ c, ι.toAlgebraHom c = c) (a : (oppAlgebra C).A) : (oppHom ι).toAlgebraHom a = a := by
  rw [oppHom_apply, hι, LinearEquiv.symm_apply_apply]

/-- The graded opposite of `C` read over itself through a homomorphism acting as the identity is
the regular module. -/
def restrictedRegularOppIso {C : DifferentialGradedAlgebra.{u, u} R} (ι : C.Hom C)
    (hι : ∀ c, ι.toAlgebraHom c = c) :
    restrictedRegularOpp ι ≅ regularModule (oppAlgebra C) where
  hom :=
    { toFun := LinearMap.id
      map_smul x a := by
        change (show (oppAlgebra C).A from x) * (oppHom ι).toAlgebraHom a = _
        rw [oppHom_apply_of_forall_eq ι hι]
        rfl
      map_grading _ _ hx := hx
      map_d := rfl }
  inv :=
    { toFun := LinearMap.id
      map_smul x a := by
        change _ = (show (oppAlgebra C).A from x) * (oppHom ι).toAlgebraHom a
        rw [oppHom_apply_of_forall_eq ι hι]
        rfl
      map_grading _ _ hx := hx
      map_d := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **The graded opposite of `C` read over itself through a homomorphism acting as the identity
is orthogonal on the left to the acyclic modules**, being the regular module. -/
theorem leftOrthogonal_restrictedRegularOpp {C : DifferentialGradedAlgebra.{u, u} R}
    (ι : C.Hom C) (hι : ∀ c, ι.toAlgebraHom c = c) :
    (acyclic' (oppAlgebra C)).leftOrthogonal
      ((toHomotopyCategory (oppAlgebra C)).obj (restrictedRegularOpp ι)) :=
  ObjectProperty.prop_of_iso _
    ((toHomotopyCategory (oppAlgebra C)).mapIso (restrictedRegularOppIso ι hι)).symm
    (leftOrthogonal_acyclic_toHomotopyCategory_regularModule (oppAlgebra C))

/-- The plain transpose is natural in the source. -/
theorem plainTranspose_comp_left {A C : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom C)
    {P N : DifferentialGradedModule.{u, u, u} A} {N₀ : DifferentialGradedModule.{u, u, u} C}
    (p : P ⟶ N) (g : N ⟶ (restrictScalarsFunctor φ).obj N₀) :
    plainTranspose φ (p ≫ g) = (tensorCompFunctor (regular φ)).map p ≫ plainTranspose φ g :=
  (tensorRegularAdjRestrictScalars φ).homEquiv_naturality_left_symm p g

/-- Associativity, stated for an abstract category, to be applied where the two sides present the
composites at different instance paths. -/
theorem assoc_aux {C : Type*} [Category C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Category.assoc f g h

/-- **An invertible derived transpose has a quasi-isomorphic plain transpose on a resolution.**
If the transpose `N ⊗^𝐋_A C ⟶ N₀` of `g` is invertible and `p : P ⟶ N` is a quasi-isomorphism from
a module orthogonal on the left to the acyclic modules, then the plain transpose of `p ≫ g` is a
quasi-isomorphism. -/
theorem quasiIso_plainTranspose_of_isIso_derivedTranspose {A C : DifferentialGradedAlgebra.{u, u} R}
    (φ : A.Hom C) {P N : DifferentialGradedModule.{u, u, u} A}
    {N₀ : DifferentialGradedModule.{u, u, u} C} (p : P ⟶ N)
    (hp : QuasiIso ((forgetToCochainComplex A).map p))
    (hP : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P))
    (g : N ⟶ restrictScalars φ N₀)
    (hg : IsIso (((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      (derivedTrans φ g))) :
    QuasiIso ((forgetToCochainComplex C).map (plainTranspose φ (p ≫ g))) := by
  have hQp : IsIso ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map p)) :=
    (isIso_q_map_toHomotopyCategory_map_iff A p).2 hp
  have hdt : derivedTrans φ (p ≫ g) =
      (quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map p) ≫ derivedTrans φ g := by
    simp only [derivedTrans, Functor.map_comp]
    exact assoc_aux _ _ _
  have htr : ((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      (derivedTrans φ (p ≫ g)) =
      (derivedTensorFunctor (regular φ)).map
          ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map p)) ≫
        ((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
          (derivedTrans φ g) := by
    rw [hdt]
    exact Adjunction.homEquiv_naturality_left_symm _ _ _
  have hiso : IsIso (((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      (derivedTrans φ (p ≫ g))) := by
    rw [htr]
    infer_instance
  have heq' : ((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      (derivedTrans φ (p ≫ g)) =
      (derivedTensorFunctorCounit (regular φ)).app ((toHomotopyCategory A).obj P) ≫
        (quasiIsomorphisms' C).Q.map ((tensorCompFunctor_quotient (regular φ)).inv.app P) ≫
        (quasiIsomorphisms' C).Q.map ((toHomotopyCategory C).map (plainTranspose φ (p ≫ g))) :=
    Eq.trans (congrArg (fun z => ((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      ((quasiIsomorphisms' A).Q.map ((toHomotopyCategory A).map (p ≫ g)) ≫ z))
      (map_id_comp_aux (quasiIsomorphisms' A).Q _ rfl _).symm)
      (derivedTranspose_eq φ (p ≫ g))
  have hc := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal (regular φ) _ hP
  rw [heq', isIso_comp_left_iff, isIso_comp_left_iff] at hiso
  exact (isIso_q_map_toHomotopyCategory_map_iff C _).1 hiso

/-- The combination of the tower identity with the naturality of the comparisons, stated for
abstract categories. -/
theorem flipTower_combine_aux {M K D : Type*} [Category M] [Category K] [Category D]
    (G₁ : M ⥤ K) (G₂ : K ⥤ D) {a b c : D} {m m' m₀ : M} (e : a ⟶ b) (T : b ⟶ c)
    (c₀ : c ⟶ G₂.obj (G₁.obj m₀)) (cN : b ⟶ G₂.obj (G₁.obj m)) (cP : a ⟶ G₂.obj (G₁.obj m'))
    (pm : m ⟶ m₀) (tf : m' ⟶ m) (pm' : m' ⟶ m₀) (hT : T ≫ c₀ = cN ≫ G₂.map (G₁.map pm))
    (hA : e ≫ cN = cP ≫ G₂.map (G₁.map tf)) (hpm : tf ≫ pm = pm') :
    e ≫ T ≫ c₀ = cP ≫ G₂.map (G₁.map pm') := by
  rw [hT, ← Category.assoc, hA, Category.assoc, ← G₂.map_comp, ← G₁.map_comp, hpm]

/-- The square of an arrow isomorphism, from the combined identity, stated for an abstract
category. -/
theorem flipTower_square_aux {C : Type*} [Category C] {a b c d e : C} (e₁ : a ≅ b) (T : b ⟶ c)
    (c₀ : c ⟶ d) (cP : a ⟶ e) (pm : e ⟶ d) (h : e₁.hom ≫ T ≫ c₀ = cP ≫ pm) :
    (e₁.inv ≫ cP) ≫ pm = T ≫ c₀ := by
  rw [Category.assoc, ← h, Iso.inv_hom_id_assoc]

section FlipTower

variable {A C : DifferentialGradedAlgebra.{u, u} R} (φ ψ : A.Hom C) (ι : C.Hom C)
  (hψφ : ∀ a, ψ.toAlgebraHom a = φ.toAlgebraHom a) (hι : ∀ c, ι.toAlgebraHom c = c)
  {N : DifferentialGradedModule.{u, u, u} A} {N₀ : DifferentialGradedModule.{u, u, u} C}
  (g : N ⟶ restrictScalars φ N₀)
  (k : flip N ⟶ Bimodule.restrictLeft (oppHom φ) (flip N₀))
  (hk : ∀ y, k.rightHom.toFun y = g.toFun y)
  (v : restrictedRegularOpp ψ ⟶ restrictScalars (oppHom φ) (restrictedRegularOpp ι))
  (hv : ∀ x, v.toFun x = x)

include hk hv in
/-- Tensoring with a resolution and then with the map induced by `g` is tensoring with the map
induced by the composite. -/
theorem tensorHomOfBimoduleHom_comp_flipTensor {P : DifferentialGradedModule.{u, u, u} A}
    (p : P ⟶ N) :
    tensorHomOfBimoduleHom (flipMap p) (restrictedRegularOpp ψ) ≫
        ((tensorCompFunctor (flip N)).map v ≫
          (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
            (restrictedRegularOpp ι)) =
      (tensorCompFunctor (flip P)).map v ≫
        (tensorCompNatTransOfSemilinear (oppHom φ) (flip P) (flip N₀) (flipMap p ≫ k)).app
          (restrictedRegularOpp ι) := by
  refine tensorObj_hom_ext' (flip P) (restrictedRegularOpp ψ) _ _ fun x y => ?_
  have h1 := tensorHomOfBimoduleHom_pure (flipMap p) (restrictedRegularOpp ψ) x y
  have h2 := tensorCompFunctor_map_pure' (flip N) v x ((flipMap p).rightHom.toFun y)
  have h3 := tensorCompNatTransOfSemilinear_app_pure (oppHom φ) (flip N) (flip N₀) k
    (restrictedRegularOpp ι) (v.toFun x) ((flipMap p).rightHom.toFun y)
  have h4 := tensorCompFunctor_map_pure' (flip P) v x y
  have h5 := tensorCompNatTransOfSemilinear_app_pure (oppHom φ) (flip P) (flip N₀)
    (flipMap p ≫ k) (restrictedRegularOpp ι) (v.toFun x) y
  show ((tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
      (restrictedRegularOpp ι)).toFun (((tensorCompFunctor (flip N)).map v).toFun
        ((tensorHomOfBimoduleHom (flipMap p) (restrictedRegularOpp ψ)).toFun
          (((tensorDGFunctor (flip P)).pure (restrictedRegularOpp ψ)).toLinearMap x y))) =
    ((tensorCompNatTransOfSemilinear (oppHom φ) (flip P) (flip N₀) (flipMap p ≫ k)).app
      (restrictedRegularOpp ι)).toFun (((tensorCompFunctor (flip P)).map v).toFun
        (((tensorDGFunctor (flip P)).pure (restrictedRegularOpp ψ)).toLinearMap x y))
  refine (congrArg (fun z => ((tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
      (restrictedRegularOpp ι)).toFun (((tensorCompFunctor (flip N)).map v).toFun z)) h1).trans ?_
  refine (congrArg (fun z => ((tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k).app
      (restrictedRegularOpp ι)).toFun z) h2).trans ?_
  refine h3.trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((tensorCompNatTransOfSemilinear (oppHom φ) (flip P)
      (flip N₀) (flipMap p ≫ k)).app (restrictedRegularOpp ι)).toFun z) h4).symm
  exact h5.symm

include hψφ hι hk hv in
/-- **The map of derived tensor products in the flipped variable induced by `g` is an
isomorphism when the derived transpose of `g` is.** The derived transpose
`N ⊗^𝐋_A C ⟶ N₀` is the comparison map of quasi-coherence; the map in the statement is the
transition map of the tower `n ↦ X_n ⊗^𝐋_{A_n^{opp}} N̂_n` of Tag 0GZJ. -/
theorem isIso_flipTowerMap_of_isIso_derivedTranspose
    (w : (quasiIsomorphisms' (oppAlgebra A)).Q.obj
        ((toHomotopyCategory (oppAlgebra A)).obj (restrictedRegularOpp ψ)) ⟶
      (derivedRestriction (oppHom φ)).obj ((quasiIsomorphisms' (oppAlgebra C)).Q.obj
        ((toHomotopyCategory (oppAlgebra C)).obj (restrictedRegularOpp ι))))
    (hw : w = (quasiIsomorphisms' (oppAlgebra A)).Q.map
        ((toHomotopyCategory (oppAlgebra A)).map v) ≫
      (derivedRestrictionFactorization (oppHom φ)).inv.app
        ((toHomotopyCategory (oppAlgebra C)).obj (restrictedRegularOpp ι)))
    (hg : IsIso (((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv _ _).symm
      (derivedTrans φ g))) :
    IsIso ((derivedTensorFunctor (flip N)).map w ≫
      (derivedTensorRestrictTrans (oppHom φ) (flip N) (flip N₀)
        (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k)).app
          ((quasiIsomorphisms' (oppAlgebra C)).Q.obj
            ((toHomotopyCategory (oppAlgebra C)).obj (restrictedRegularOpp ι)))) := by
  obtain ⟨P, p, hp, hP⟩ := exists_quasiIso_leftOrthogonal_acyclic A N
  have hk' : ∀ y, (flipMap p ≫ k).rightHom.toFun y = (p ≫ g).toFun y := fun y => hk _
  have hpl := quasiIso_plainTranspose_of_isIso_derivedTranspose φ p hp hP g hg
  have hPi := quasiIso_flipTensor_of_quasiIso_plainTranspose φ ψ ι hψφ hι (p ≫ g) v hv
    (flipMap p ≫ k) hk' hpl
  have hT := derivedTensorRestrictTrans_towerMap_comparison (oppHom φ) (flip N) (flip N₀)
    (tensorCompNatTransOfSemilinear (oppHom φ) (flip N) (flip N₀) k) v w hw
  have hA := derivedTensorNatTrans_app_comp_comparison (flipMap p) (restrictedRegularOpp ψ)
  have hcomb := flipTower_combine_aux (toHomotopyCategory (degreeZero R R))
    (quasiIsomorphisms' (degreeZero R R)).Q _ _ _ _ _ _ _ _ hT hA
    (tensorHomOfBimoduleHom_comp_flipTensor φ ψ ι g k hk v hv p)
  have hq : QuasiIso ((forgetToCochainComplex (degreeZero R R)).map (flipMap p).rightHom) := by
    have h : @Eq (P.toCochainComplex ⟶ N.toCochainComplex)
        (restrictScalarsHom (baseHom A) p).toCochainMap p.toCochainMap :=
      restrictScalarsHom_toCochainMap (baseHom A) p
    have h' : (forgetToCochainComplex (degreeZero R R)).map (flipMap p).rightHom =
        (forgetToCochainComplex A).map p := h
    rwa [h']
  have hiso : IsIso (derivedTensorNatTrans (flipMap p)) :=
    quasiIsoInvertsDerivedTensor (oppAlgebra A) (degreeZero R R) (flipMap p) hq
  have hP' := isIso_derivedTensorFunctorCounit_flip_of_leftOrthogonal P hP
  have hX₀ := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal (flip N₀) _
    (leftOrthogonal_restrictedRegularOpp ι hι)
  let e₁ := asIso ((derivedTensorNatTrans (flipMap p)).app
    ((quasiIsomorphisms' (oppAlgebra A)).Q.obj
      ((toHomotopyCategory (oppAlgebra A)).obj (restrictedRegularOpp ψ))))
  have hsq := flipTower_square_aux e₁ _ _ _ _ hcomb
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk (e₁.symm ≪≫ derivedTensorPlainIso (flip P) (restrictedRegularOpp ψ)
        (NatIso.isIso_app_of_isIso _ _))
      (derivedTensorPlainIso (flip N₀) (restrictedRegularOpp ι) hX₀) hsq)).2
    ((isIso_q_map_toHomotopyCategory_map_iff (degreeZero R R) _).2 hPi)

end FlipTower

end DifferentialGraded.Bimodule

end
