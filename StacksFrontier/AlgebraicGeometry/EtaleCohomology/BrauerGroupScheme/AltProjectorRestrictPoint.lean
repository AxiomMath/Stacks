module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeSheafPullbackMatrix
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerAlgebraPoints
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerRestrictPoint

/-!
# Restricting Saltman's point to a smaller base

Let `ρ : V ⟶ T` and `φ : T ⟶ S` be morphisms of schemes with `ρ ≫ φ = ψ`, let `B` be a sheaf of
`𝒪_S`-algebras and let `M : φ^* B ≅ Mat_{n+1}(𝒪_T)` be a trivialisation of its pullback to `T`.
`Stacks.EtaleCohomology.BrauerScheme.saltmanPoint` is the point of `φ^*(B^{⊗ (n+1)})` which `M`
attaches to Saltman's projector, and the content of this file is that **restricting it along `ρ`
gives the point attached by the restricted trivialisation**,
`Stacks.EtaleCohomology.BrauerScheme.restrictTriv`.

This is what makes the family of local Saltman points a descent datum: on the fibre product of
two members of a trivialising covering the two restrictions are the points attached by two
trivialisations of the *same* sheaf of algebras, and
`Stacks.EtaleCohomology.BrauerScheme.saltmanPoint_eq` says that two trivialisations read
Saltman's projector as the same point.

The proof runs on the normal form
`Stacks.EtaleCohomology.BrauerScheme.curry'_altProjFree_comp_natTensorPowTrivIso_inv_eq_sum`:
written as a combination of tensors of matrix units, Saltman's point mentions none of the
tensor-power identifications, and the three things restriction has to be pushed through are a
finite sum (`restrictPoint_sum`), a coefficient in `R₀ T` (`unitEndPullbackHom`, along which the
alternating projector is invariant by `Matrix.map_altProj`) and a tensor of points
(`restrictPoint_pullbackNatTensorPowPoint`) — all three elementary for a monoidal functor.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.freeEndAlgebraPullbackIso` and
  `matrixAlgebraPullbackIso`: the pullback of the endomorphism algebra of a finite free sheaf of
  modules is the endomorphism algebra of the finite free sheaf, canonically.
* `Stacks.EtaleCohomology.BrauerScheme.algebraRestrictIso`: the comparison of the two
  descriptions of the pullback along a factorisation, as sheaves of algebras.
* `Stacks.EtaleCohomology.BrauerScheme.restrictTriv`: the trivialisation of `ψ^* B` obtained by
  restricting a trivialisation of `φ^* B`.
* `Stacks.EtaleCohomology.BrauerScheme.pullbackTrivIso` and `saltmanPoint`: the trivialisation of
  `ψ^*(B^{⊗ (n+1)})` as the endomorphism algebra of the free sheaf of rank `(n+1) ^ (n+1)`
  induced by a trivialisation of `ψ^* B`, and the point of `ψ^*(B^{⊗ (n+1)})` it attaches to
  Saltman's projector.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.mapPoint_matIncl`: a pullback carries the matrix units to
  the matrix units.
* `Stacks.EtaleCohomology.BrauerScheme.saltmanPoint_eq`: **two trivialisations attach the same
  point.**
* `Stacks.EtaleCohomology.BrauerScheme.saltmanPoint_eq_sum`: Saltman's point as a combination of
  tensors of matrix units, inside the pullback.
* `Stacks.EtaleCohomology.BrauerScheme.restrictPoint_saltmanPoint`: **restricting Saltman's point
  gives Saltman's point of the restricted trivialisation.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace CategoryTheory.Mon

variable {C : Type*} {D : Type*} [Category C] [Category D] [MonoidalCategory C]
  [MonoidalCategory D] (F : C ⥤ D)

/-- **A transported point is natural in the monoid object.** -/
theorem mapPoint_comp [F.LaxMonoidal] {A B : Mon C} (p : 𝟙_ C ⟶ A.X) (g : A ⟶ B) :
    mapPoint F (C := B) (p ≫ g.hom) = mapPoint F (C := A) p ≫ (F.mapMon.map g).hom := by
  change Functor.LaxMonoidal.ε F ≫ F.map (p ≫ g.hom)
    = (Functor.LaxMonoidal.ε F ≫ F.map p) ≫ F.map g.hom
  rw [Functor.map_comp, Category.assoc]

/-- **A transported multiple of a point is the transported multiple of the transported point**:
the scalars, i.e. the endomorphisms of the monoidal unit, are transported by conjugating with the
unit comparison of the functor. -/
theorem mapPoint_unit_comp [F.Monoidal] {A : Mon C} (a : 𝟙_ C ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ A.X) :
    mapPoint F (C := A) (a ≫ p)
      = (Functor.LaxMonoidal.ε F ≫ F.map a ≫ (Functor.Monoidal.εIso F).inv) ≫
        mapPoint F (C := A) p := by
  have hh : Functor.LaxMonoidal.ε F = (Functor.Monoidal.εIso F).hom := rfl
  change Functor.LaxMonoidal.ε F ≫ F.map (a ≫ p)
    = (Functor.LaxMonoidal.ε F ≫ F.map a ≫ (Functor.Monoidal.εIso F).inv) ≫
      (Functor.LaxMonoidal.ε F ≫ F.map p)
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [hh, Iso.inv_hom_id_assoc]

end CategoryTheory.Mon

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-! ### The pullback of the endomorphism algebra of a finite free sheaf of modules -/

/-- **The pullback of the endomorphism algebra of a finite free sheaf of `𝒪_T`-modules is the
endomorphism algebra of the finite free sheaf of `𝒪_V`-modules**: the internal-hom comparison of
the braided monoidal functor `modulePullback ρ`, which is invertible because a finite free sheaf
of modules is dualizable, followed by the identification of the pullback of the free sheaf with
the free sheaf. -/
def freeEndAlgebraPullbackIso {V T : Scheme.{u}} (ρ : V ⟶ T) (I : Type u) [Finite I] :
    (algebraPullback ρ).obj (endAlgebra (freeModule T I)) ≅ endAlgebra (freeModule V I) :=
  letI : HasRightDual (freeModule T I) :=
    (nonempty_hasRightDual_of_isFiniteLocallyFree (isFiniteLocallyFree_free I)).some
  asIso (MonoidalClosed.internalEndFunctorHom (modulePullback ρ) (freeModule T I)) ≪≫
    endAlgebraCongr (modulePullbackFreeIso ρ I)

/-- **The pullback of a matrix algebra is a matrix algebra**, canonically. -/
abbrev matrixAlgebraPullbackIso {V T : Scheme.{u}} (ρ : V ⟶ T) (d : ℕ) :
    (algebraPullback ρ).obj (matrixAlgebra T d) ≅ matrixAlgebra V d :=
  freeEndAlgebraPullbackIso ρ (ULift.{u, 0} (Fin d))

/-- **A pullback carries the matrix units to the matrix units.** -/
theorem mapPoint_matIncl {V T : Scheme.{u}} (ρ : V ⟶ T) {I : Type u} [Fintype I]
    [DecidableEq I] (k : I × I) :
    Mon.mapPoint (modulePullback ρ) (C := endAlgebra (freeModule T I))
        (matIncl (S := T) k) ≫ (freeEndAlgebraPullbackIso ρ I).hom.hom
      = matIncl (S := V) k := by
  have hhom : (freeEndAlgebraPullbackIso ρ I).hom.hom
      = MonoidalClosed.ihomFunctorComparison (modulePullback ρ) (freeModule T I)
          (freeModule T I) ≫
        (MonoidalClosed.internalEndCongr (modulePullbackFreeIso ρ I)).hom.hom := rfl
  have h1 := Mon.mapPoint_curry' (modulePullback ρ)
    (MonoidalClosed.uncurry' (matIncl (S := T) k))
  rw [MonoidalClosed.curry'_uncurry'] at h1
  refine Eq.trans (congrArg (fun z => Mon.mapPoint (modulePullback ρ)
      (C := endAlgebra (freeModule T I)) (matIncl (S := T) k) ≫ z) hhom) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun z => z ≫ (MonoidalClosed.internalEndCongr (modulePullbackFreeIso ρ I)).hom.hom) h1) ?_
  refine Eq.trans (MonoidalClosed.curry'_comp_internalEndCongr_hom _ _) ?_
  refine Eq.trans (congrArg MonoidalClosed.curry'
    (conj_modulePullbackFreeIso_uncurry'_matIncl ρ k)) ?_
  exact MonoidalClosed.curry'_uncurry' _

/-! ### Restricting a trivialisation -/

/-- **The comparison of the two descriptions of a pullback along a factorisation** `ρ ≫ φ = ψ`,
as sheaves of algebras. -/
def algebraRestrictIso {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) (B : AlgebraSheaf S) :
    (algebraPullback ρ).obj ((algebraPullback φ).obj B) ≅ (algebraPullback ψ).obj B :=
  ((algebraPullbackComp ρ φ).app B).symm ≪≫
    eqToIso (congrArg (fun f : V ⟶ S => (algebraPullback f).obj B) w)

/-- **Restriction of a point is the transported point, followed by the comparison of the two
descriptions of the pullback.** -/
theorem restrictPoint_eq_mapPoint {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) (B : AlgebraSheaf S)
    (x : 𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X) :
    AlgebraicGeometry.restrictPoint ρ φ ψ w x
      = Mon.mapPoint (modulePullback ρ) (C := (algebraPullback φ).obj B) x ≫
        (algebraRestrictIso ρ φ ψ w B).hom.hom := by
  subst w
  change Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map x ≫
      ((modulePullbackComp ρ φ).hom.app B.X ≫
        𝟙 ((modulePullback (ρ ≫ φ)).obj B.X))
    = (Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map x) ≫
      ((modulePullbackComp ρ φ).hom.app B.X ≫
        𝟙 ((modulePullback (ρ ≫ φ)).obj B.X))
  simp only [Category.assoc]

/-- **Restricting a multiple of a point multiplies by the transported scalar.** -/
theorem restrictPoint_comp_left {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) (B : AlgebraSheaf S) (a : 𝟙_ (ModuleSheaf T) ⟶ 𝟙_ (ModuleSheaf T))
    (x : 𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X) :
    AlgebraicGeometry.restrictPoint ρ φ ψ w (a ≫ x)
      = unitEndPullbackHom ρ a ≫ AlgebraicGeometry.restrictPoint ρ φ ψ w x := by
  refine Eq.trans (restrictPoint_eq_mapPoint ρ φ ψ w B _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ (algebraRestrictIso ρ φ ψ w B).hom.hom)
    (Mon.mapPoint_unit_comp (modulePullback ρ) a x)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun z => unitEndPullbackHom ρ a ≫ z)
    (restrictPoint_eq_mapPoint ρ φ ψ w B x).symm

/-- **The trivialisation of `ψ^* B` obtained by restricting a trivialisation of `φ^* B`** along a
factorisation `ρ ≫ φ = ψ`: split the pullback along the composite, pull the trivialisation back
along `ρ`, and recognise the pullback of the matrix algebra as a matrix algebra. -/
def restrictTriv {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S) (w : ρ ≫ φ = ψ)
    {B : AlgebraSheaf S} {d : ℕ} (M : (algebraPullback φ).obj B ≅ matrixAlgebra T d) :
    (algebraPullback ψ).obj B ≅ matrixAlgebra V d :=
  (algebraRestrictIso ρ φ ψ w B).symm ≪≫ (algebraPullback ρ).mapIso M ≪≫
    matrixAlgebraPullbackIso ρ d

/-- **Restricting a matrix unit read through a trivialisation gives the matrix unit read through
the restricted trivialisation.** -/
theorem restrictPoint_matIncl_comp {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) {B : AlgebraSheaf S} {d : ℕ}
    (M : (algebraPullback φ).obj B ≅ matrixAlgebra T d)
    (k : ULift.{u, 0} (Fin d) × ULift.{u, 0} (Fin d)) :
    AlgebraicGeometry.restrictPoint ρ φ ψ w (matIncl (S := T) k ≫ M.inv.hom)
      = matIncl (S := V) k ≫ (restrictTriv ρ φ ψ w M).inv.hom := by
  have hmp : Mon.mapPoint (modulePullback ρ) (C := matrixAlgebra T d) (matIncl (S := T) k)
      = matIncl (S := V) k ≫ (matrixAlgebraPullbackIso ρ d).inv.hom := by
    have hid : (matrixAlgebraPullbackIso ρ d).hom.hom ≫
        (matrixAlgebraPullbackIso ρ d).inv.hom = 𝟙 _ :=
      congrArg Mon.Hom.hom (matrixAlgebraPullbackIso ρ d).hom_inv_id
    rw [← mapPoint_matIncl ρ (I := ULift.{u, 0} (Fin d)) k, Category.assoc, hid,
      Category.comp_id]
  refine Eq.trans (restrictPoint_eq_mapPoint ρ φ ψ w B _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ (algebraRestrictIso ρ φ ψ w B).hom.hom)
    (Mon.mapPoint_comp (modulePullback ρ) (matIncl (S := T) k) M.inv)) ?_
  refine Eq.trans (congrArg (fun z => (z ≫ ((algebraPullback ρ).map M.inv).hom) ≫
    (algebraRestrictIso ρ φ ψ w B).hom.hom) hmp) ?_
  change ((matIncl (S := V) k ≫ (matrixAlgebraPullbackIso ρ d).inv.hom) ≫
      ((algebraPullback ρ).map M.inv).hom) ≫ (algebraRestrictIso ρ φ ψ w B).hom.hom
    = matIncl (S := V) k ≫ ((matrixAlgebraPullbackIso ρ d).inv.hom ≫
      (((algebraPullback ρ).map M.inv).hom ≫ (algebraRestrictIso ρ φ ψ w B).hom.hom))
  simp only [Category.assoc]

/-! ### Saltman's point -/

/-- **The trivialisation of `ψ^*(B^{⊗ (n+1)})` as the endomorphism algebra of the free sheaf of
rank `(n+1) ^ (n+1)` induced by a trivialisation `N : ψ^* B ≅ Mat_{n+1}(𝒪_V)`**: the comparison
of the pullback with the tensor power, followed by
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowTrivIso`. -/
def pullbackTrivIso {V S : Scheme.{u}} (ψ : V ⟶ S) {B : AlgebraSheaf S} {n : ℕ}
    (N : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    (algebraPullback ψ).obj (Stacks.TensorPowers.natTensorPow B (n + 1)) ≅
      endAlgebra (freeModule V (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))) :=
  algebraPullbackNatTensorPowIso ψ B (n + 1) ≪≫ natTensorPowTrivIso N

/-- **The point of `ψ^*(B^{⊗ (n+1)})` which a trivialisation `N : ψ^* B ≅ Mat_{n+1}(𝒪_V)`
attaches to Saltman's projector.** -/
def saltmanPoint {V S : Scheme.{u}} (ψ : V ⟶ S) {B : AlgebraSheaf S} {n : ℕ}
    (N : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    𝟙_ (ModuleSheaf V) ⟶
      ((algebraPullback ψ).obj (Stacks.TensorPowers.natTensorPow B (n + 1))).X :=
  MonoidalClosed.curry' (altProjFree V (n + 1)) ≫ (pullbackTrivIso ψ N).inv.hom

/-- **The trivialisation reads Saltman's point back as Saltman's projector.** -/
theorem saltmanPoint_comp_pullbackTrivIso_hom {V S : Scheme.{u}} (ψ : V ⟶ S)
    {B : AlgebraSheaf S} {n : ℕ}
    (N : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    saltmanPoint ψ N ≫ (pullbackTrivIso ψ N).hom.hom
      = MonoidalClosed.curry' (altProjFree V (n + 1)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => MonoidalClosed.curry' (altProjFree V (n + 1)) ≫ z)
      (congrArg Mon.Hom.hom (pullbackTrivIso ψ N).inv_hom_id)).trans (Category.comp_id _))

/-- Saltman's point is the point read in the free sheaf, transported through the comparison of the
pullback with the tensor power. -/
private theorem saltmanPoint_eq_comp {V S : Scheme.{u}} (ψ : V ⟶ S) {B : AlgebraSheaf S}
    {n : ℕ} (N : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    saltmanPoint ψ N
      = (MonoidalClosed.curry' (altProjFree V (n + 1)) ≫ (natTensorPowTrivIso N).inv.hom) ≫
        (algebraPullbackNatTensorPowIso ψ B (n + 1)).inv.hom :=
  (Category.assoc _ _ _).symm

/-- **Two trivialisations of `ψ^* B` attach the same Saltman point to `ψ^*(B^{⊗ (n+1)})`.** This
is `Stacks.EtaleCohomology.BrauerScheme.curry'_altProjFree_comp_natTensorPowTrivIso_inv`: the two
induced trivialisations of the tensor power share the comparison of the pullback with the tensor
power, so that factor cancels out of their comparison automorphism. -/
theorem saltmanPoint_eq {V S : Scheme.{u}} (ψ : V ⟶ S) {B : AlgebraSheaf S} {n : ℕ}
    (N₁ N₂ : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    saltmanPoint ψ N₁ = saltmanPoint ψ N₂ := by
  rw [saltmanPoint_eq_comp, saltmanPoint_eq_comp,
    curry'_altProjFree_comp_natTensorPowTrivIso_inv N₁ N₂]

/-- The tensor of a family of points of a pullback, built inside the pullback, is the tensor
built outside and transported by the comparison of the pullback with the tensor power. -/
theorem pullbackNatTensorPowPoint_eq {T S : Scheme.{u}} (φ : T ⟶ S) (B : AlgebraSheaf S) :
    ∀ (m : ℕ) (ps : Fin m → (𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X)),
      pullbackNatTensorPowPoint φ B m ps
        = natTensorPowPoint m ps ≫ (algebraPullbackNatTensorPowIso φ B m).inv.hom
  | 0, ps => by
    change Functor.LaxMonoidal.ε (modulePullback φ)
      = 𝟙 (𝟙_ (ModuleSheaf T)) ≫ (algebraPullbackNatTensorPowIso φ B 0).inv.hom
    exact (Category.id_comp _).symm
  | m + 1, ps => by
    have ih := pullbackNatTensorPowPoint_eq φ B m (Fin.init ps)
    refine Eq.trans (congrArg (fun z => (λ_ (𝟙_ (ModuleSheaf T))).inv ≫
      (z ⊗ₘ ps (Fin.last m)) ≫ Functor.LaxMonoidal.μ (modulePullback φ)
        (Stacks.TensorPowers.natTensorPow B m).X B.X) ih) ?_
    refine Eq.trans (leftUnitorInv_tensorHom_comp_tensorHom_id
      (natTensorPowPoint m (Fin.init ps)) (ps (Fin.last m))
      (algebraPullbackNatTensorPowIso φ B m).inv.hom
      (Functor.LaxMonoidal.μ (modulePullback φ)
        (Stacks.TensorPowers.natTensorPow B m).X B.X)).symm ?_
    change (λ_ (𝟙_ (ModuleSheaf T))).inv ≫
        (natTensorPowPoint m (Fin.init ps) ⊗ₘ ps (Fin.last m)) ≫
        (((algebraPullbackNatTensorPowIso φ B m).inv.hom ⊗ₘ
            𝟙 (((algebraPullback φ).obj B).X)) ≫
          Functor.LaxMonoidal.μ (modulePullback φ)
            (Stacks.TensorPowers.natTensorPow B m).X B.X)
      = ((λ_ (𝟙_ (ModuleSheaf T))).inv ≫
          (natTensorPowPoint m (Fin.init ps) ⊗ₘ ps (Fin.last m))) ≫
        (((algebraPullbackNatTensorPowIso φ B m).inv.hom ⊗ₘ
            𝟙 (((algebraPullback φ).obj B).X)) ≫
          Functor.LaxMonoidal.μ (modulePullback φ)
            (Stacks.TensorPowers.natTensorPow B m).X B.X)
    simp only [Category.assoc]

/-- **Saltman's point as a combination of tensors of matrix units**, inside the pullback. -/
theorem saltmanPoint_eq_sum {V S : Scheme.{u}} (ψ : V ⟶ S) {B : AlgebraSheaf S} {n : ℕ}
    (N : (algebraPullback ψ).obj B ≅ matrixAlgebra V (n + 1)) :
    saltmanPoint ψ N
      = ∑ k : ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)) ×
            ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)),
          Matrix.altProj (R₀ V) k.1.down k.2.down ≫
            pullbackNatTensorPowPoint ψ B (n + 1) (fun j => matIncl (S := V)
              (ULift.up.{u, 0} (k.1.down j), ULift.up.{u, 0} (k.2.down j)) ≫ N.inv.hom) := by
  rw [saltmanPoint_eq_comp, curry'_altProjFree_comp_natTensorPowTrivIso_inv_eq_sum N]
  refine Eq.trans (Preadditive.sum_comp _ _ _) (Finset.sum_congr rfl fun k _ => ?_)
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun z => Matrix.altProj (R₀ V) k.1.down k.2.down ≫ z)
    (pullbackNatTensorPowPoint_eq ψ B (n + 1) _).symm

/-! ### Restriction carries Saltman's point to Saltman's point -/

/-- **RESTRICTING SALTMAN'S POINT GIVES SALTMAN'S POINT OF THE RESTRICTED TRIVIALISATION.** -/
theorem restrictPoint_saltmanPoint {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) {B : AlgebraSheaf S} {n : ℕ}
    (M : (algebraPullback φ).obj B ≅ matrixAlgebra T (n + 1)) :
    AlgebraicGeometry.restrictPoint ρ φ ψ w (saltmanPoint φ M)
      = saltmanPoint ψ (restrictTriv ρ φ ψ w M) := by
  refine Eq.trans (congrArg (AlgebraicGeometry.restrictPoint ρ φ ψ w)
    (saltmanPoint_eq_sum φ M)) ?_
  refine Eq.trans (restrictPoint_sum ρ φ ψ w _ _) ?_
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_)
    (saltmanPoint_eq_sum ψ (restrictTriv ρ φ ψ w M)).symm
  have hcoef : unitEndPullbackHom ρ (Matrix.altProj (R₀ T) k.1.down k.2.down)
      = Matrix.altProj (R₀ V) k.1.down k.2.down :=
    congrFun (congrFun (Matrix.map_altProj (n := Fin (n + 1)) (unitEndPullbackHom ρ))
      k.1.down) k.2.down
  refine Eq.trans (restrictPoint_comp_left ρ φ ψ w
    (Stacks.TensorPowers.natTensorPow B (n + 1))
    (Matrix.altProj (R₀ T) k.1.down k.2.down)
    (pullbackNatTensorPowPoint φ B (n + 1) (fun j => matIncl (S := T)
      (ULift.up.{u, 0} (k.1.down j), ULift.up.{u, 0} (k.2.down j)) ≫ M.inv.hom))) ?_
  refine Eq.trans (congrArg (fun z => z ≫ AlgebraicGeometry.restrictPoint ρ φ ψ w
    (pullbackNatTensorPowPoint φ B (n + 1) (fun j => matIncl (S := T)
      (ULift.up.{u, 0} (k.1.down j), ULift.up.{u, 0} (k.2.down j)) ≫ M.inv.hom))) hcoef) ?_
  refine congrArg (fun z => Matrix.altProj (R₀ V) k.1.down k.2.down ≫ z) ?_
  refine Eq.trans (restrictPoint_pullbackNatTensorPowPoint ρ φ ψ w B (n + 1) _) ?_
  exact congrArg (pullbackNatTensorPowPoint ψ B (n + 1))
    (funext fun j => restrictPoint_matIncl_comp ρ φ ψ w M _)

end Stacks.EtaleCohomology.BrauerScheme

end

end
