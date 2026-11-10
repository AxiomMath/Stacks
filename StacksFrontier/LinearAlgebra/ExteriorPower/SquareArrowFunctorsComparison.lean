module

public import StacksFrontier.LinearAlgebra.ExteriorPower.SquareArrowFunctors
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareResidueField
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.MonoidalFunctors
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import StacksFrontier.Algebra.Category.FGModuleCat.Projective

/-!
# Comparisons for the derived square functors on arrows

Let `A` be a commutative ring and `X = (X₀ → X₁)` an arrow of `A`-modules with a simplicial
projective resolution `P`. For the semilinear functors on arrows of
`StacksFrontier.LinearAlgebra.ExteriorPower.SquareArrowFunctors` this file compares their derived
functors `LⱼΦ(X) = Hⱼ(s(Φ(P)))` with one another and with the derived functors of modules, and
proves finiteness and vanishing properties of them.

**Comparisons.** Evaluation at the source and at the target carry `P` to resolutions of `X₀` and
`X₁`, and, when `X₀ → X₁` is a monomorphism, the degreewise cokernel carries `P` to a resolution
of `coker X`. Hence, for `Q` the exterior or the tensor square:

* (i) a morphism of arrows which is an isomorphism on sources (targets) induces isomorphisms on
  `Lⱼ(Q ∘ left)` (`Lⱼ(Q ∘ right)`), and a morphism of monomorphisms which is an isomorphism on
  cokernels induces isomorphisms on `Lⱼ(Q ∘ coker)`;
* (ii) `Lⱼ(Q ∘ left) → Lⱼ(Q ∘ right)` is an isomorphism at an arrow which is an isomorphism;
* (iii) `Lⱼ(Q ∘ right) → Lⱼ(Q ∘ coker)` is an isomorphism at an arrow with zero source;
* (iv) the braiding gives `Lⱼ(X₀ ⊗ coker X) ≅ Lⱼ(coker X ⊗ X₀)`, and the derived functors of a
  biproduct are the biproduct of the derived functors.

In each case the map is the derived map of the morphism of arrows, or the map induced by the
morphism of functors, and it is identified with a derived map of modules between the image
resolutions.

**Modules.** `Lⱼ(Λ² ∘ right)(X)` is the derived exterior square of `X₁` and `Lⱼ(T ∘ right)(X)` is
`Torⱼ(X₁, X₁)`, so that for a regular local ring of dimension `c` and `X₁` its residue field the
Koszul computation `Σ (-1)ⁿ length Torₙ(κ, κ) - 2 Σ (-1)ⁱ length LᵢΛ²(κ) = 2^c` applies.

**Finiteness.** Over a Noetherian ring the arrows of finitely generated modules form an abelian
category with enough projectives, into which finitely generated arrows lift, so a finitely
generated arrow has a simplicial projective resolution by finitely generated arrows. The derived
functors of a functor preserving finiteness, such as all the functors above, are therefore
finitely generated.

**Vanishing.** The derived functors of `Q ∘ E` vanish in degrees `> 2d` when `E(X)` has projective
dimension `≤ d` (for the tensor square, in degrees `> d`), and the derived functors of every
functor above vanish on arrows with zero source and target.

## Main definitions

* `Stacks.SimplicialProjectiveResolution.derivedHomologyIsoOfIso`,
  `Stacks.SimplicialProjectiveResolution.derivedHomologyBiprodIso`: derived objects of isomorphic
  functors and of biproducts.
* `Stacks.SemilinearArrowFunctor.derivedHomologyCrossIso`,
  `Stacks.SemilinearArrowFunctor.derivedHomologyCrossSumIso`,
  `Stacks.SemilinearArrowFunctor.derivedHomologyExteriorSquareRightIso`,
  `Stacks.SemilinearArrowFunctor.derivedHomologyTensorRightIsoTor`: the comparison isomorphisms.
* `Stacks.SemilinearArrowFunctor.PreservesFinite`, `Stacks.SemilinearArrowFunctor.VanishesOnZero`:
  the finiteness and vanishing conditions on semilinear functors.

## Main results

* `Stacks.SemilinearArrowFunctor.isIso_derivedMap_exteriorPower_left` and its variants for the
  target, the cokernel and the tensor square: (i).
* `Stacks.SemilinearArrowFunctor.isIso_derivedHomologyMap_exteriorPowerMap_leftToRight`,
  `Stacks.SemilinearArrowFunctor.isIso_derivedHomologyMap_tensorHom_leftToRight`: (ii).
* `Stacks.SemilinearArrowFunctor.isIso_derivedHomologyMap_exteriorPowerMap_rightToCoker`,
  `Stacks.SemilinearArrowFunctor.isIso_derivedHomologyMap_tensorHom_rightToCoker`: (iii).
* `SemilinearArrowFunctor.sum_length_tensor_right_sub_two_mul_sum_length_exteriorPower_right`:
  the Koszul computation on arrows.
* `Stacks.SemilinearArrowFunctor.exists_simplicialProjectiveResolution_finite`,
  `Stacks.SemilinearArrowFunctor.finite_derivedHomology`: finiteness.
* `Stacks.SemilinearArrowFunctor.isZero_derivedHomology_exteriorSquare_left` and its variants:
  vanishing above twice the projective dimension;
  `Stacks.SemilinearArrowFunctor.isZero_derivedHomology_of_vanishesOnZero`: support.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology MonoidalCategory Simplicial Opposite
open scoped TensorProduct

universe u

namespace Stacks.SimplicialProjectiveResolution

section General

variable {C : Type*} [Category C] [Abelian C] {C' : Type*} [Category C'] [Abelian C']
  {D : Type*} [Category D] [Abelian D]

/-- **Derived maps of a composite.** If `G` carries the resolutions `P` and `Q` to resolutions,
the map `LᵢF(g)` for `F = G ⋙ H` is the map `LᵢH(G g)` computed with the images of `P` and `Q`. -/
theorem derivedMap_comp_functor (G : C ⥤ C') [G.Additive] (H : C' ⥤ D) {X Y : C} (g : X ⟶ Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hQ : ∀ n, Projective (G.obj (Q.obj _⦋n⦌))) (hπ' : QuasiIso (Q.mapπ G)) (i : ℕ) :
    derivedMap (G ⋙ H) g P Q i =
      derivedMap H (G.map g) (P.mapOfQuasiIso G hP hπ) (Q.mapOfQuasiIso G hQ hπ') i := by
  obtain ⟨f, hf⟩ := exists_isLift P Q g
  rw [hf.derivedMap_eq, (hf.mapOfQuasiIso hP hπ hQ hπ').derivedMap_eq]
  rfl

/-- The map induced on derived objects by `H` whiskered with a natural transformation
`τ : G ⟶ G'` is the derived map of `H` along `τ_X`, computed with the images of `P`. -/
theorem derivedHomologyMap_whiskerRight {G G' : C ⥤ C'} [G.Additive] [G'.Additive] (τ : G ⟶ G')
    (H : C' ⥤ D) {X : C} (P : SimplicialProjectiveResolution X)
    (hP : ∀ n, Projective (G.obj (P.obj _⦋n⦌))) (hπ : QuasiIso (P.mapπ G))
    (hP' : ∀ n, Projective (G'.obj (P.obj _⦋n⦌))) (hπ' : QuasiIso (P.mapπ G')) (i : ℕ) :
    derivedHomologyMap (Functor.whiskerRight τ H) P i =
      derivedMap H (τ.app X) (P.mapOfQuasiIso G hP hπ) (P.mapOfQuasiIso G' hP' hπ') i := by
  rw [(isLift_whiskerLeft τ P hP hπ hP' hπ').derivedMap_eq]
  rfl

/-- `derivedHomologyMap` of the identity. -/
@[simp]
lemma derivedHomologyMap_id (F : C ⥤ D) {X : C} (P : SimplicialProjectiveResolution X) (i : ℕ) :
    derivedHomologyMap (𝟙 F) P i = 𝟙 _ := by
  simp [derivedHomologyMap]

/-- `derivedHomologyMap` is functorial. -/
@[reassoc]
lemma derivedHomologyMap_comp {F F' F'' : C ⥤ D} (τ : F ⟶ F') (τ' : F' ⟶ F'') {X : C}
    (P : SimplicialProjectiveResolution X) (i : ℕ) :
    derivedHomologyMap (τ ≫ τ') P i = derivedHomologyMap τ P i ≫ derivedHomologyMap τ' P i := by
  simp [derivedHomologyMap, Functor.whiskerLeft_comp, HomologicalComplex.homologyMap_comp]

/-- An isomorphism of functors induces an isomorphism of derived objects. -/
@[simps]
def derivedHomologyIsoOfIso {F F' : C ⥤ D} (e : F ≅ F') {X : C}
    (P : SimplicialProjectiveResolution X) (i : ℕ) :
    P.derivedHomology F i ≅ P.derivedHomology F' i where
  hom := derivedHomologyMap e.hom P i
  inv := derivedHomologyMap e.inv P i
  hom_inv_id := by rw [← derivedHomologyMap_comp, e.hom_inv_id, derivedHomologyMap_id]
  inv_hom_id := by rw [← derivedHomologyMap_comp, e.inv_hom_id, derivedHomologyMap_id]

/-- The derived object `Hᵢ(s(F(P)))` as a functor of `F`. -/
def derivedHomologyFunctor {X : C} (P : SimplicialProjectiveResolution X) (i : ℕ) :
    (C ⥤ D) ⥤ D :=
  (Functor.whiskeringLeft _ _ D).obj P.obj ⋙ alternatingFaceMapComplex D ⋙
    HomologicalComplex.homologyFunctor D _ i

/-- The derived object is additive in the functor. -/
instance {X : C} (P : SimplicialProjectiveResolution X) (i : ℕ) :
    (derivedHomologyFunctor (D := D) P i).Additive := by
  unfold derivedHomologyFunctor
  infer_instance

/-- **Derived objects of a biproduct.** `Lᵢ(F ⊞ F') ≅ LᵢF ⊞ LᵢF'`, computed with one resolution. -/
def derivedHomologyBiprodIso (F F' : C ⥤ D) {X : C} (P : SimplicialProjectiveResolution X)
    (i : ℕ) : P.derivedHomology (F ⊞ F') i ≅ P.derivedHomology F i ⊞ P.derivedHomology F' i :=
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (derivedHomologyFunctor (D := D) P i)
  (derivedHomologyFunctor (D := D) P i).mapBiprod F F'

end General

end Stacks.SimplicialProjectiveResolution

namespace Stacks.SemilinearArrowFunctor

open SimplicialProjectiveResolution ComposableArrows

variable {A : CommRingCat.{u}} {X Y : ComposableArrows (ModuleCat.{u} A) 1}

/-! ### Change of resolution and change of arrow -/

/-- A morphism of arrows which is an isomorphism on the sources induces isomorphisms on the
derived functors of `H` applied to the source. -/
theorem isIso_derivedMap_comp_left (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A) (g : X ⟶ Y)
    [IsIso (g.app 0)] (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (j : ℕ) : IsIso (SimplicialProjectiveResolution.derivedMap
      ((evaluation (Fin 2) (ModuleCat.{u} A)).obj 0 ⋙ H) g P Q j) := by
  rw [derivedMap_comp_functor _ H g P Q P.leftResolution.projective P.leftResolution.quasiIso
    Q.leftResolution.projective Q.leftResolution.quasiIso]
  exact isIso_derivedMap H (g.app 0) _ _ j

/-- A morphism of arrows which is an isomorphism on the targets induces isomorphisms on the
derived functors of `H` applied to the target. -/
theorem isIso_derivedMap_comp_right (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A) (g : X ⟶ Y)
    [IsIso (g.app 1)] (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (j : ℕ) : IsIso (SimplicialProjectiveResolution.derivedMap
      ((evaluation (Fin 2) (ModuleCat.{u} A)).obj 1 ⋙ H) g P Q j) := by
  rw [derivedMap_comp_functor _ H g P Q P.rightResolution.projective P.rightResolution.quasiIso
    Q.rightResolution.projective Q.rightResolution.quasiIso]
  exact isIso_derivedMap H (g.app 1) _ _ j

/-- A morphism of monomorphisms which is an isomorphism on the cokernels induces isomorphisms on
the derived functors of `H` applied to the cokernel. -/
theorem isIso_derivedMap_comp_cokernelFunctor (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A)
    [Mono X.hom] [Mono Y.hom] (g : X ⟶ Y) [IsIso (cokernelFunctor.map g)]
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap (cokernelFunctor ⋙ H) g P Q j) := by
  rw [derivedMap_comp_functor _ H g P Q P.cokernelResolution.projective
    P.cokernelResolution.quasiIso Q.cokernelResolution.projective Q.cokernelResolution.quasiIso]
  exact isIso_derivedMap H (cokernelFunctor.map g) _ _ j

/-- **(i) for `Λⁿ ∘ left`.** A morphism of arrows which is an isomorphism on the sources induces
isomorphisms on `Lⱼ(Λⁿ ∘ left)`. -/
theorem isIso_derivedMap_exteriorPower_left (n : ℕ) (g : X ⟶ Y) [IsIso (g.app 0)]
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((exteriorPower n left).obj A) g P Q j) :=
  isIso_derivedMap_comp_left (ModuleCat.exteriorPower.functor A n) g P Q j

/-- **(i) for `T ∘ left`.** A morphism of arrows which is an isomorphism on the sources induces
isomorphisms on `Lⱼ(T ∘ left)`. -/
theorem isIso_derivedMap_tensor_left (g : X ⟶ Y) [IsIso (g.app 0)]
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((tensor left left).obj A) g P Q j) :=
  isIso_derivedMap_comp_left (ModuleCat.tensorSquareFunctor A) g P Q j

/-- If `X₀ → X₁` is an isomorphism, `H(X₀) → H(X₁)` induces isomorphisms on derived functors. -/
theorem isIso_derivedHomologyMap_whiskerRight_evaluationHom (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A)
    [IsIso X.hom] (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap (Functor.whiskerRight evaluationHom H) P j) := by
  rw [derivedHomologyMap_whiskerRight evaluationHom H P P.leftResolution.projective
    P.leftResolution.quasiIso P.rightResolution.projective P.rightResolution.quasiIso]
  exact isIso_derivedMap H X.hom _ _ j

/-- **(ii) for `Λⁿ`.** At an arrow `X₀ → X₁` which is an isomorphism,
`Lⱼ(Λⁿ ∘ left) → Lⱼ(Λⁿ ∘ right)` is an isomorphism. -/
theorem isIso_derivedHomologyMap_exteriorPowerMap_leftToRight (n : ℕ) [IsIso X.hom]
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap ((exteriorPowerMap n leftToRight).app A) P j) :=
  isIso_derivedHomologyMap_whiskerRight_evaluationHom (ModuleCat.exteriorPower.functor A n) P j

/-- **(ii) for `T`.** At an arrow `X₀ → X₁` which is an isomorphism,
`Lⱼ(T ∘ left) → Lⱼ(T ∘ right)` is an isomorphism. -/
theorem isIso_derivedHomologyMap_tensorHom_leftToRight [IsIso X.hom]
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap ((tensorHom leftToRight leftToRight).app A) P j) :=
  isIso_derivedHomologyMap_whiskerRight_evaluationHom (ModuleCat.tensorSquareFunctor A) P j

/-- **(i) for `Λⁿ ∘ right`.** A morphism of arrows which is an isomorphism on the targets induces
isomorphisms on `Lⱼ(Λⁿ ∘ right)`. -/
theorem isIso_derivedMap_exteriorPower_right (n : ℕ) (g : X ⟶ Y) [IsIso (g.app 1)]
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((exteriorPower n right).obj A) g P Q j) :=
  isIso_derivedMap_comp_right (ModuleCat.exteriorPower.functor A n) g P Q j

/-- **(i) for `T ∘ right`.** A morphism of arrows which is an isomorphism on the targets induces
isomorphisms on `Lⱼ(T ∘ right)`. -/
theorem isIso_derivedMap_tensor_right (g : X ⟶ Y) [IsIso (g.app 1)]
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((tensor right right).obj A) g P Q j) :=
  isIso_derivedMap_comp_right (ModuleCat.tensorSquareFunctor A) g P Q j

/-- **(i) for `Λⁿ ∘ coker`.** A morphism of monomorphisms which is an isomorphism on the cokernels
induces isomorphisms on `Lⱼ(Λⁿ ∘ coker)`. -/
theorem isIso_derivedMap_exteriorPower_coker (n : ℕ) [Mono X.hom] [Mono Y.hom] (g : X ⟶ Y)
    [IsIso (cokernelFunctor.map g)] (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((exteriorPower n coker).obj A) g P Q j) :=
  isIso_derivedMap_comp_cokernelFunctor (ModuleCat.exteriorPower.functor A n) g P Q j

/-- **(i) for `T ∘ coker`.** A morphism of monomorphisms which is an isomorphism on the cokernels
induces isomorphisms on `Lⱼ(T ∘ coker)`. -/
theorem isIso_derivedMap_tensor_coker [Mono X.hom] [Mono Y.hom] (g : X ⟶ Y)
    [IsIso (cokernelFunctor.map g)] (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    IsIso (SimplicialProjectiveResolution.derivedMap ((tensor coker coker).obj A) g P Q j) :=
  isIso_derivedMap_comp_cokernelFunctor (ModuleCat.tensorSquareFunctor A) g P Q j

/-- If `X₀` is zero, `H(X₁) → H(coker X)` induces isomorphisms on derived functors. -/
theorem isIso_derivedHomologyMap_whiskerRight_cokernelFunctorπ
    (H : ModuleCat.{u} A ⥤ ModuleCat.{u} A) (hX : IsZero X.left)
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap (Functor.whiskerRight cokernelFunctorπ H) P j) := by
  have : Mono X.hom := ⟨fun g h _ ↦ hX.eq_of_tgt g h⟩
  rw [derivedHomologyMap_whiskerRight cokernelFunctorπ H P P.rightResolution.projective
    P.rightResolution.quasiIso P.cokernelResolution.projective P.cokernelResolution.quasiIso]
  have : IsIso (cokernel.π X.hom) := cokernel.π_of_zero (hX.eq_of_src _ _)
  exact isIso_derivedMap H (cokernel.π X.hom) _ _ j

/-- **(iii) for `Λⁿ`.** At an arrow with `X₀ = 0`, `Lⱼ(Λⁿ ∘ right) → Lⱼ(Λⁿ ∘ coker)` is an
isomorphism. -/
theorem isIso_derivedHomologyMap_exteriorPowerMap_rightToCoker (n : ℕ) (hX : IsZero X.left)
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap ((exteriorPowerMap n rightToCoker).app A) P j) :=
  isIso_derivedHomologyMap_whiskerRight_cokernelFunctorπ (ModuleCat.exteriorPower.functor A n) hX
    P j

/-- **(iii) for `T`.** At an arrow with `X₀ = 0`, `Lⱼ(T ∘ right) → Lⱼ(T ∘ coker)` is an
isomorphism. -/
theorem isIso_derivedHomologyMap_tensorHom_rightToCoker (hX : IsZero X.left)
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (derivedHomologyMap ((tensorHom rightToCoker rightToCoker).app A) P j) :=
  isIso_derivedHomologyMap_whiskerRight_cokernelFunctorπ (ModuleCat.tensorSquareFunctor A) hX P j

/-- The component over `A` of an isomorphism of semilinear functors on arrows. -/
@[simps]
def isoApp {Φ Ψ : SemilinearArrowFunctor.{u}} (e : Φ ≅ Ψ) (A : CommRingCat.{u}) :
    Φ.obj A ≅ Ψ.obj A where
  hom := e.hom.app A
  inv := e.inv.app A
  hom_inv_id := by rw [← comp_app, e.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, e.inv_hom_id, id_app]

/-- **(iv) The braiding on derived functors.** `Lⱼ(X₀ ⊗ coker X) ≅ Lⱼ(coker X ⊗ X₀)`, induced by
the braiding. -/
def derivedHomologyCrossIso (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology (cross.obj A) j ≅ P.derivedHomology (crossRev.obj A) j :=
  derivedHomologyIsoOfIso (isoApp crossIsoCrossRev A) P j

/-- **(iv) Derived functors of the sum of the cross terms.**
`Lⱼ((X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀)) ≅ Lⱼ(X₀ ⊗ coker X) ⊞ Lⱼ(coker X ⊗ X₀)`. -/
def derivedHomologyCrossSumIso (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology ((biprod cross crossRev).obj A) j ≅
      P.derivedHomology (cross.obj A) j ⊞ P.derivedHomology (crossRev.obj A) j :=
  derivedHomologyBiprodIso (cross.obj A) (crossRev.obj A) P j

/-! ### Modules -/

/-- `Lⱼ(Λ² ∘ right)(X) ≅ LⱼΛ²(X₁)`, the latter computed with any resolution `Q` of `X₁`; for the
arrow `0 → M` this is the derived exterior square of `M`. -/
def derivedHomologyExteriorSquareRightIso (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution X.right) (j : ℕ) :
    P.derivedHomology ((exteriorPower 2 right).obj A) j ≅ DerivedSquare.homology Q j :=
  derivedIso (DerivedSquare.exteriorSquare A) P.rightResolution Q j

/-- `Lⱼ(T ∘ right)(X) ≅ Torⱼ(X₁, X₁)`. -/
def derivedHomologyTensorRightIsoTor (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology ((tensor right right).obj A) j ≅
      ((Tor' (ModuleCat.{u} A) j).obj X.right).obj X.right :=
  P.rightResolution.homologyTensorIsoTor P.rightResolution j

/-- `Lⱼ(T ∘ left)(X) ≅ Torⱼ(X₀, X₀)`. -/
def derivedHomologyTensorLeftIsoTor (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology ((tensor left left).obj A) j ≅
      ((Tor' (ModuleCat.{u} A) j).obj X.left).obj X.left :=
  P.leftResolution.homologyTensorIsoTor P.leftResolution j

/-- `Lⱼ(T ∘ coker)(X) ≅ Torⱼ(coker X, coker X)` for a monomorphism `X₀ → X₁`. -/
def derivedHomologyTensorCokerIsoTor [Mono X.hom] (P : SimplicialProjectiveResolution X)
    (j : ℕ) :
    P.derivedHomology ((tensor coker coker).obj A) j ≅
      ((Tor' (ModuleCat.{u} A) j).obj (Limits.cokernel X.hom)).obj (Limits.cokernel X.hom) :=
  P.cokernelResolution.homologyTensorIsoTor P.cokernelResolution j

/-- **The Koszul computation on arrows.** For a regular local ring `R` of dimension `c` and an
arrow `X` whose target is the residue field,
`Σ_{n ≤ c} (-1)ⁿ length Lₙ(T ∘ right)(X) - 2 Σ_{i ≤ 2c} (-1)ⁱ length Lᵢ(Λ² ∘ right)(X) = 2^c`. -/
theorem sum_length_tensor_right_sub_two_mul_sum_length_exteriorPower_right
    {R : CommRingCat.{u}} [IsRegularLocalRing R] {c : ℕ} (hc : ringKrullDim R = c)
    {X : ComposableArrows (ModuleCat.{u} R) 1}
    (e : X.right ≅ ModuleCat.of R (IsLocalRing.ResidueField R))
    (P : SimplicialProjectiveResolution X) :
    ∑ n ∈ Finset.range (c + 1), (-1 : ℤ) ^ n *
        ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((tensor right right).obj R) n)).toNat : ℤ) -
      2 * ∑ i ∈ Finset.range (2 * c + 1), (-1 : ℤ) ^ i *
        ((Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
          ((exteriorPower 2 right).obj R) i)).toNat : ℤ) =
      2 ^ c := by
  let Q : SimplicialProjectiveResolution (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
    Classical.arbitrary _
  have h₁ : ∀ n, Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
      ((tensor right right).obj R) n) =
      Module.length R (((Tor' (ModuleCat.{u} R) n).obj
        (ModuleCat.of R (IsLocalRing.ResidueField R))).obj
          (ModuleCat.of R (IsLocalRing.ResidueField R))) := fun n ↦
    (derivedHomologyTensorRightIsoTor P n ≪≫ ((Tor' (ModuleCat.{u} R) n).mapIso e).app X.right ≪≫
      ((Tor' (ModuleCat.{u} R) n).obj _).mapIso e).toLinearEquiv.length_eq
  have h₂ : ∀ i, Module.length R (P.derivedHomology (D := ModuleCat.{u} R)
      ((exteriorPower 2 right).obj R) i) =
      Module.length R (DerivedSquare.homology Q i) := fun i ↦
    DerivedSquare.length_homology_eq_of_iso e P.rightResolution Q i
  simp only [h₁, h₂]
  exact DerivedSquare.sum_tor_sub_two_mul_sum_length_homology_residueField hc Q

/-! ### Vanishing -/

/-- `Lⱼ(Λ² ∘ left)(X) = 0` for `j > 2d` if `X₀` has projective dimension `≤ d`. -/
theorem isZero_derivedHomology_exteriorSquare_left {d : ℕ}
    (hX : HasProjectiveDimensionLE X.left d) (P : SimplicialProjectiveResolution X) {j : ℕ}
    (hj : 2 * d < j) : IsZero (P.derivedHomology ((exteriorPower 2 left).obj A) j) :=
  DerivedSquare.isZero_homology_of_hasProjectiveDimensionLE hX P.leftResolution hj

/-- `Lⱼ(Λ² ∘ right)(X) = 0` for `j > 2d` if `X₁` has projective dimension `≤ d`. -/
theorem isZero_derivedHomology_exteriorSquare_right {d : ℕ}
    (hX : HasProjectiveDimensionLE X.right d) (P : SimplicialProjectiveResolution X) {j : ℕ}
    (hj : 2 * d < j) : IsZero (P.derivedHomology ((exteriorPower 2 right).obj A) j) :=
  DerivedSquare.isZero_homology_of_hasProjectiveDimensionLE hX P.rightResolution hj

/-- `Lⱼ(Λ² ∘ coker)(X) = 0` for `j > 2d` if `X₀ → X₁` is a monomorphism and its cokernel has
projective dimension `≤ d`. -/
theorem isZero_derivedHomology_exteriorSquare_coker [Mono X.hom] {d : ℕ}
    (hX : HasProjectiveDimensionLE (Limits.cokernel X.hom) d) (P : SimplicialProjectiveResolution X)
    {j : ℕ} (hj : 2 * d < j) : IsZero (P.derivedHomology ((exteriorPower 2 coker).obj A) j) :=
  DerivedSquare.isZero_homology_of_hasProjectiveDimensionLE hX P.cokernelResolution hj

/-- `Lⱼ(T ∘ left)(X) = 0` for `j > d` if `X₀` has projective dimension `≤ d`. -/
theorem isZero_derivedHomology_tensor_left {d : ℕ}
    (hX : HasProjectiveDimensionLE X.left d) (P : SimplicialProjectiveResolution X) {j : ℕ}
    (hj : d < j) : IsZero (P.derivedHomology ((tensor left left).obj A) j) :=
  (StacksDraft.ProjectiveDimension.isZero_Tor'_of_hasProjectiveDimensionLE _ _ d j hX hj).of_iso
    (derivedHomologyTensorLeftIsoTor P j)

/-- `Lⱼ(T ∘ right)(X) = 0` for `j > d` if `X₁` has projective dimension `≤ d`. -/
theorem isZero_derivedHomology_tensor_right {d : ℕ}
    (hX : HasProjectiveDimensionLE X.right d) (P : SimplicialProjectiveResolution X) {j : ℕ}
    (hj : d < j) : IsZero (P.derivedHomology ((tensor right right).obj A) j) :=
  (StacksDraft.ProjectiveDimension.isZero_Tor'_of_hasProjectiveDimensionLE _ _ d j hX hj).of_iso
    (derivedHomologyTensorRightIsoTor P j)

/-- `Lⱼ(T ∘ coker)(X) = 0` for `j > d` if `X₀ → X₁` is a monomorphism and its cokernel has
projective dimension `≤ d`. -/
theorem isZero_derivedHomology_tensor_coker [Mono X.hom] {d : ℕ}
    (hX : HasProjectiveDimensionLE (Limits.cokernel X.hom) d) (P : SimplicialProjectiveResolution X)
    {j : ℕ} (hj : d < j) : IsZero (P.derivedHomology ((tensor coker coker).obj A) j) :=
  (StacksDraft.ProjectiveDimension.isZero_Tor'_of_hasProjectiveDimensionLE _ _ d j hX hj).of_iso
    (derivedHomologyTensorCokerIsoTor P j)

/-! ### Zero arrows -/

/-- A semilinear functor on arrows *vanishes on zero arrows* if it sends every arrow with zero
source and target to a zero module. -/
def VanishesOnZero (Φ : SemilinearArrowFunctor.{u}) : Prop :=
  ∀ (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1), IsZero X.left →
    IsZero X.right → IsZero ((Φ.obj A).obj X)

variable {Φ Ψ : SemilinearArrowFunctor.{u}}

/-- The source vanishes on zero arrows. -/
lemma vanishesOnZero_left : left.{u}.VanishesOnZero := fun _ _ h _ ↦ h

/-- The target vanishes on zero arrows. -/
lemma vanishesOnZero_right : right.{u}.VanishesOnZero := fun _ _ _ h ↦ h

/-- A cokernel of a morphism into a functor vanishing on zero arrows vanishes on zero arrows. -/
lemma vanishesOnZero_cokernel (α : Φ ⟶ Ψ) (hΨ : Ψ.VanishesOnZero) :
    (cokernel α).VanishesOnZero := fun A X h₀ h₁ ↦
  IsZero.of_epi (Limits.cokernel.π ((α.app A).app X)) (hΨ A X h₀ h₁)

/-- `Φ ⊗ Ψ` vanishes on zero arrows if `Φ` does. -/
lemma vanishesOnZero_tensor_left (hΦ : Φ.VanishesOnZero) (Ψ : SemilinearArrowFunctor.{u}) :
    (tensor Φ Ψ).VanishesOnZero := fun A X h₀ h₁ ↦
  (MonoidalCategory.tensorRight ((Ψ.obj A).obj X)).map_isZero (hΦ A X h₀ h₁)

/-- `Φ ⊗ Ψ` vanishes on zero arrows if `Ψ` does. -/
lemma vanishesOnZero_tensor_right (Φ : SemilinearArrowFunctor.{u}) (hΨ : Ψ.VanishesOnZero) :
    (tensor Φ Ψ).VanishesOnZero := fun A X h₀ h₁ ↦
  (MonoidalCategory.tensorLeft ((Φ.obj A).obj X)).map_isZero (hΨ A X h₀ h₁)

/-- `Λⁿ ∘ Φ`, `n ≠ 0`, vanishes on zero arrows if `Φ` does. -/
lemma vanishesOnZero_exteriorPower {n : ℕ} (hn : n ≠ 0) (hΦ : Φ.VanishesOnZero) :
    (exteriorPower n Φ).VanishesOnZero := fun A X h₀ h₁ ↦ by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((ModuleCat.exteriorPower.functor A n).obj ((Φ.obj A).obj X)) = 0
  rw [← CategoryTheory.Functor.map_id, (hΦ A X h₀ h₁).eq_of_src (𝟙 _) 0,
    ModuleCat.exteriorPower.functor_map_zero hn]

/-- `Φ ⊞ Ψ` vanishes on zero arrows if `Φ` and `Ψ` do. -/
lemma vanishesOnZero_biprod (hΦ : Φ.VanishesOnZero) (hΨ : Ψ.VanishesOnZero) :
    (biprod Φ Ψ).VanishesOnZero := fun A X h₀ h₁ ↦ by
  rw [IsZero.iff_id_eq_zero, ← Stacks.Cohomology.AmbientMayerVietoris.biprod_total_app,
    (hΦ A X h₀ h₁).eq_of_src ((biprod.inl : Φ.obj A ⟶ _).app X) 0,
    (hΨ A X h₀ h₁).eq_of_src ((biprod.inr : Ψ.obj A ⟶ _).app X) 0, comp_zero, comp_zero,
    add_zero]

/-- **Support.** The derived functors of a functor vanishing on zero arrows vanish on every arrow
with zero source and target. -/
theorem isZero_derivedHomology_of_vanishesOnZero (hΦ : Φ.VanishesOnZero) (h₀ : IsZero X.left)
    (h₁ : IsZero X.right) (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsZero (P.derivedHomology (Φ.obj A) j) := by
  have hX : IsZero X := Functor.isZero _ fun i ↦ by
    fin_cases i
    exacts [h₀, h₁]
  have : Projective X := Projective.of_iso hX.isoZero.symm inferInstance
  exact (ShortComplex.isZero_homology_of_isZero_X₂ _ (hΦ A X h₀ h₁)).of_iso
    (derivedIso (Φ.obj A) P (const X) j)

/-! ### Finiteness -/

/-- The inclusion of arrows of finitely generated modules into arrows of modules. -/
abbrev fgArrowInclusion (A : CommRingCat.{u}) :
    ComposableArrows (FGModuleCat.{u} A) 1 ⥤ ComposableArrows (ModuleCat.{u} A) 1 :=
  (Functor.whiskeringRight (Fin 2) _ _).obj (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A))

/-- The inclusion of arrows of finitely generated modules preserves finite limits. -/
instance [IsNoetherianRing A] : PreservesFiniteLimits (fgArrowInclusion A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The inclusion of arrows of finitely generated modules preserves finite colimits. -/
instance [IsNoetherianRing A] : PreservesFiniteColimits (fgArrowInclusion A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The inclusion of arrows of finitely generated modules preserves projective objects. -/
instance [IsNoetherianRing A] : (fgArrowInclusion A).PreservesProjectiveObjects := by
  refine ⟨fun {P} hP ↦ ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := (projective_iff P).1 hP
  have : Mono ((fgArrowInclusion A).obj P).hom :=
    (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).map_mono P.hom
  have : Projective ((fgArrowInclusion A).obj P).left :=
    (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).projective_obj P.left
  have : Projective (Limits.cokernel ((fgArrowInclusion A).obj P).hom) :=
    Projective.of_iso (PreservesCokernel.iso (forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)) P.hom)
      ((forget₂ (FGModuleCat.{u} A) (ModuleCat.{u} A)).projective_obj _)
  exact projective_of_mono _

/-- **Finite resolutions.** Over a Noetherian ring, an arrow of finitely generated modules has a
simplicial projective resolution whose terms are arrows of finitely generated modules. -/
theorem exists_simplicialProjectiveResolution_finite [IsNoetherianRing A]
    (X : ComposableArrows (ModuleCat.{u} A) 1) [Module.Finite A X.left]
    [Module.Finite A X.right] :
    ∃ P : SimplicialProjectiveResolution X,
      ∀ n, Module.Finite A (P.obj _⦋n⦌).left ∧ Module.Finite A (P.obj _⦋n⦌).right := by
  let X' : ComposableArrows (FGModuleCat.{u} A) 1 := (ModuleCat.isFG A).lift X (fun i ↦ by
    fin_cases i
    · exact (inferInstance : Module.Finite A X.left)
    · exact (inferInstance : Module.Finite A X.right))
  let P' : SimplicialProjectiveResolution X' := Classical.arbitrary _
  exact ⟨P'.map (fgArrowInclusion A), fun n ↦ ⟨inferInstanceAs (Module.Finite A
    ((P'.obj.obj _).obj 0)), inferInstanceAs (Module.Finite A ((P'.obj.obj _).obj 1))⟩⟩

/-- A semilinear functor on arrows *preserves finiteness* if it sends every arrow of finitely
generated modules to a finitely generated module. -/
def PreservesFinite (Φ : SemilinearArrowFunctor.{u}) : Prop :=
  ∀ (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1), Module.Finite A X.left →
    Module.Finite A X.right → Module.Finite A ((Φ.obj A).obj X)

/-- The source preserves finiteness. -/
lemma preservesFinite_left : left.{u}.PreservesFinite := fun _ _ h _ ↦ h

/-- The target preserves finiteness. -/
lemma preservesFinite_right : right.{u}.PreservesFinite := fun _ _ _ h ↦ h

/-- A cokernel of a morphism into a functor preserving finiteness preserves finiteness. -/
lemma preservesFinite_cokernel (α : Φ ⟶ Ψ) (hΨ : Ψ.PreservesFinite) :
    (cokernel α).PreservesFinite := fun A X h₀ h₁ ↦
  have := hΨ A X h₀ h₁
  Module.Finite.of_surjective _ (ModuleCat.surjective_cokernel_π ((α.app A).app X))

/-- A tensor product of functors preserving finiteness preserves finiteness. -/
lemma preservesFinite_tensor (hΦ : Φ.PreservesFinite) (hΨ : Ψ.PreservesFinite) :
    (tensor Φ Ψ).PreservesFinite := fun A X h₀ h₁ ↦
  have := hΦ A X h₀ h₁
  have := hΨ A X h₀ h₁
  inferInstanceAs (Module.Finite A ((Φ.obj A).obj X ⊗[A] (Ψ.obj A).obj X))

/-- `Λⁿ ∘ Φ` preserves finiteness if `Φ` does. -/
lemma preservesFinite_exteriorPower (n : ℕ) (hΦ : Φ.PreservesFinite) :
    (exteriorPower n Φ).PreservesFinite := fun A X h₀ h₁ ↦
  have := hΦ A X h₀ h₁
  inferInstanceAs (Module.Finite A (⋀[A]^n ((Φ.obj A).obj X)))

/-- A biproduct of functors preserving finiteness preserves finiteness. -/
lemma preservesFinite_biprod (hΦ : Φ.PreservesFinite) (hΨ : Ψ.PreservesFinite) :
    (biprod Φ Ψ).PreservesFinite := fun A X h₀ h₁ ↦ by
  have := hΦ A X h₀ h₁
  have := hΨ A X h₀ h₁
  refine Module.Finite.of_surjective
    (((biprod.inl : Φ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app X).hom.coprod
      ((biprod.inr : Ψ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app X).hom) fun x ↦ ?_
  refine ⟨(((biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ _).app X).hom x,
    ((biprod.snd : Φ.obj A ⊞ Ψ.obj A ⟶ _).app X).hom x), ?_⟩
  simpa using congrArg (fun f ↦ f.hom x)
    (Stacks.Cohomology.AmbientMayerVietoris.biprod_total_app (Φ.obj A) (Ψ.obj A) X)

/-- **Finiteness of the derived functors.** Over a Noetherian ring, the derived functors of a
semilinear functor preserving finiteness are finitely generated on arrows of finitely generated
modules. -/
theorem finite_derivedHomology [IsNoetherianRing A] (hΦ : Φ.PreservesFinite)
    {X : ComposableArrows (ModuleCat.{u} A) 1} [Module.Finite A X.left] [Module.Finite A X.right]
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    Module.Finite A (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) := by
  obtain ⟨Q, hQ⟩ := exists_simplicialProjectiveResolution_finite X
  have : Module.Finite A ((Q.derivedComplex (Φ.obj A)).X j) := hΦ A _ (hQ j).1 (hQ j).2
  have : Module.Finite A ((Q.derivedComplex (Φ.obj A)).cycles j) :=
    Module.Finite.of_injective ((Q.derivedComplex (Φ.obj A)).iCycles j).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (Q.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :=
    Module.Finite.of_surjective ((Q.derivedComplex (Φ.obj A)).homologyπ j).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv (derivedIso (Φ.obj A) Q P j).toLinearEquiv

/-- The cokernel preserves finiteness. -/
lemma preservesFinite_coker : coker.{u}.PreservesFinite :=
  preservesFinite_cokernel _ preservesFinite_right

/-- The cross term `X₀ ⊗ coker X` preserves finiteness. -/
lemma preservesFinite_cross : cross.{u}.PreservesFinite :=
  preservesFinite_tensor preservesFinite_left preservesFinite_coker

/-- The cross term `coker X ⊗ X₀` preserves finiteness. -/
lemma preservesFinite_crossRev : crossRev.{u}.PreservesFinite :=
  preservesFinite_tensor preservesFinite_coker preservesFinite_left

/-- `D_Λ` preserves finiteness. -/
lemma preservesFinite_relExteriorSquare : relExteriorSquare.{u}.PreservesFinite :=
  preservesFinite_cokernel _ (preservesFinite_exteriorPower 2 preservesFinite_right)

/-- `D_T` preserves finiteness. -/
lemma preservesFinite_relTensorSquare : relTensorSquare.{u}.PreservesFinite :=
  preservesFinite_cokernel _ (preservesFinite_tensor preservesFinite_right preservesFinite_right)

/-- The cokernel vanishes on zero arrows. -/
lemma vanishesOnZero_coker : coker.{u}.VanishesOnZero :=
  vanishesOnZero_cokernel _ vanishesOnZero_right

/-- The cross term `X₀ ⊗ coker X` vanishes on zero arrows. -/
lemma vanishesOnZero_cross : cross.{u}.VanishesOnZero :=
  vanishesOnZero_tensor_left vanishesOnZero_left _

/-- The cross term `coker X ⊗ X₀` vanishes on zero arrows. -/
lemma vanishesOnZero_crossRev : crossRev.{u}.VanishesOnZero :=
  vanishesOnZero_tensor_left vanishesOnZero_coker _

/-- `D_Λ` vanishes on zero arrows. -/
lemma vanishesOnZero_relExteriorSquare : relExteriorSquare.{u}.VanishesOnZero :=
  vanishesOnZero_cokernel _ (vanishesOnZero_exteriorPower two_ne_zero vanishesOnZero_right)

/-- `D_T` vanishes on zero arrows. -/
lemma vanishesOnZero_relTensorSquare : relTensorSquare.{u}.VanishesOnZero :=
  vanishesOnZero_cokernel _ (vanishesOnZero_tensor_left vanishesOnZero_right _)

/-- The sum of the cross terms preserves finiteness. -/
lemma preservesFinite_crossSum : (biprod cross.{u} crossRev).PreservesFinite :=
  preservesFinite_biprod preservesFinite_cross preservesFinite_crossRev

/-- The sum of the cross terms vanishes on zero arrows. -/
lemma vanishesOnZero_crossSum : (biprod cross.{u} crossRev).VanishesOnZero :=
  vanishesOnZero_biprod vanishesOnZero_cross vanishesOnZero_crossRev

end Stacks.SemilinearArrowFunctor
