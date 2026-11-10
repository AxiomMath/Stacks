module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafDesc
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of the sheaf associated to a module, linearly and functorially

Let `(X, 𝒪_X)` be a ringed space, `α : A → Γ(X, 𝒪_X)` a ring homomorphism and `M` an `A`-module.
The stalk at a point `x` of the associated sheaf `ℱ_M` is

`(ℱ_M)_x = 𝒪_{X,x} ⊗_A M`

as `𝒪_{X,x}`-modules, naturally in `M`.

## Main definitions

* `Stacks.AssociatedSheaf.presheafStalkModuleFunctor`: the stalk at a point of a presheaf of
  `O`-modules, as a module over the stalk `O_x`, functorially in the presheaf of modules.
* `Stacks.AssociatedSheaf.associatedSheafValFunctor`: `ℱ_M` read as a presheaf of modules over
  `𝒪_X ⋙ forget₂ CommRingCat RingCat`.
* `Stacks.AssociatedSheaf.sheafificationStalkLinearEquiv`: sheafification does not change the
  stalk, as an `𝒪_{X,x}`-linear equivalence.
* `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`: the identification
  `(ℱ_M)_x ≅ 𝒪_{X,x} ⊗_A M` as an `𝒪_{X,x}`-linear equivalence.
* `Stacks.AssociatedSheaf.associatedSheafStalkFunctor` and
  `Stacks.AssociatedSheaf.stalkBaseChangeFunctor`: `M ↦ (ℱ_M)_x` and `M ↦ 𝒪_{X,x} ⊗_A M`, as
  functors from `A`-modules to `𝒪_{X,x}`-modules.
* `Stacks.AssociatedSheaf.associatedSheafStalkFunctorIso`: the two functors above identified by a
  natural isomorphism whose components are
  `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`.

## Main results

* `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv_apply`: the linear identification is the
  additive one of `Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`.
* `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv_symm_tmul_germ`: the inverse of the
  linear identification on `germ_x(s) ⊗ m`.
* `Stacks.AssociatedSheaf.stalkMap_associatedSheafStalkLinearEquiv_symm`: the naturality square of
  the linear identification in `M`.
* `Stacks.AssociatedSheaf.stalkMapLinear_germ`: the stalk map of a morphism of presheaves of
  modules on germs.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH), clause (3): the stalk of
  the sheaf associated to a module, functorially in the module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.AssociatedSheaf

/-! ### The stalk of a presheaf of modules as a functor -/

section StalkFunctor

variable {Y : TopCat.{u}} (O : Y.Presheaf CommRingCat.{u}) (y : Y)
  {P Q R : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- `AlgebraicGeometry.stalkMapLinear` on a germ: the stalk map of a morphism of presheaves of
modules carries the germ of a section to the germ of its image. -/
theorem stalkMapLinear_germ (φ : P ⟶ Q) (U : Opens Y) (hy : y ∈ U) (t : P.obj (op U)) :
    AlgebraicGeometry.stalkMapLinear P Q φ y
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) P.presheaf U y hy).hom t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) Q.presheaf U y hy).hom (φ.app (op U) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    ((PresheafOfModules.toPresheaf (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map φ) t

/-- **The stalk at `y` as a functor into `O_y`-modules.**  On a presheaf of `O`-modules it is the
stalk of the underlying presheaf of abelian groups with its `O_y`-module structure, and on a
morphism it is `AlgebraicGeometry.stalkMapLinear`. -/
def presheafStalkModuleFunctor :
    PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
      ModuleCat.{u} (O.stalk y) where
  obj P := ModuleCat.of _ (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf y))
  map {_ _} φ := ModuleCat.ofHom (AlgebraicGeometry.stalkMapLinear _ _ φ y)
  map_id P := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    obtain ⟨U, hy, t, ht⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) P.presheaf z
    exact Eq.trans (congrArg (AlgebraicGeometry.stalkMapLinear P P (𝟙 P) y) ht.symm)
      (Eq.trans (stalkMapLinear_germ O y (𝟙 P) U hy t) ht)
  map_comp {P Q R} φ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    obtain ⟨U, hy, t, ht⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) P.presheaf z
    have hcomp : (φ ≫ ψ).app (op U) t = ψ.app (op U) (φ.app (op U) t) := rfl
    refine Eq.trans (congrArg (AlgebraicGeometry.stalkMapLinear P R (φ ≫ ψ) y) ht.symm) ?_
    refine Eq.trans (stalkMapLinear_germ O y (φ ≫ ψ) U hy t) ?_
    refine Eq.trans ?_ (congrArg (AlgebraicGeometry.stalkMapLinear Q R ψ y)
      (Eq.trans (stalkMapLinear_germ O y φ U hy t).symm
        (congrArg (AlgebraicGeometry.stalkMapLinear P Q φ y) ht)))
    refine Eq.trans (congrArg
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) R.presheaf U y hy).hom hcomp) ?_
    exact (stalkMapLinear_germ O y ψ U hy (φ.app (op U) t)).symm

/-- The underlying map of `Stacks.AssociatedSheaf.presheafStalkModuleFunctor` on a morphism is
`AlgebraicGeometry.stalkMapLinear`. -/
theorem presheafStalkModuleFunctor_map_apply (φ : P ⟶ Q)
    (z : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf y)) :
    (presheafStalkModuleFunctor O y).map φ z = AlgebraicGeometry.stalkMapLinear P Q φ y z :=
  rfl

end StalkFunctor

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (α : A →+* X.presheaf.obj (op ⊤)) (M : ModuleCat.{u} A) (x : X.carrier)

/-! ### `ℱ_M` as a presheaf of modules over `𝒪_X ⋙ forget₂ CommRingCat RingCat` -/

/-- **`ℱ_M` as a presheaf of `𝒪_X`-modules**, with the presheaf of rings spelled
`𝒪_X ⋙ forget₂ CommRingCat RingCat` rather than `structureSheafRing X`. -/
def associatedSheafValFunctor : ModuleCat.{u} A ⥤
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  associatedSheafFunctor.{u, u} X α ⋙
    SheafOfModules.forget (structureSheafRing X) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (structureSheafRing X).obj)

/-! ### Sheafification does not change the stalk, `𝒪_{X,x}`-linearly -/

/-- **Sheafification does not change the stalk, as an `𝒪_{X,x}`-linear equivalence.**  The stalk
map at `x` of the sheafification unit of the presheaf associated to `M`, as an `𝒪_{X,x}`-linear
equivalence. -/
def sheafificationStalkLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (associatedPresheaf X α M).presheaf x) ≃ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((associatedSheafValFunctor X α).obj M).presheaf x) :=
  LinearEquiv.ofBijective
    (AlgebraicGeometry.stalkMapLinear (R := X.presheaf) (associatedPresheaf X α M)
      ((associatedSheafValFunctor X α).obj M) (associatedSheafUnit X α M) x)
    (sheafificationStalkAddEquiv X α M x).bijective

/-- The `𝒪_{X,x}`-linear identification of the two stalks is the additive one. -/
theorem sheafificationStalkLinearEquiv_apply
    (z : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (associatedPresheaf X α M).presheaf x)) :
    sheafificationStalkLinearEquiv X α M x z = sheafificationStalkAddEquiv X α M x z :=
  rfl

/-! ### The stalk of the associated sheaf -/

/-- If a linear equivalence agrees with an additive one, so do their inverses. -/
private theorem linearEquiv_symm_apply_eq_addEquiv_symm_apply {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) (f : M ≃+ N)
    (h : ∀ z, e z = f z) (z : N) : e.symm z = f.symm z :=
  e.symm_apply_eq.mpr ((f.apply_symm_apply z).symm.trans (h _).symm)

/-- **`(ℱ_M)_x = 𝒪_{X,x} ⊗_A M` as `𝒪_{X,x}`-modules.**  The stalk at a point `x` of the sheaf of
`𝒪_X`-modules associated to an `A`-module `M` and a ring map `α : A → Γ(X, 𝒪_X)` is the base
change of `M` to the stalk of the structure sheaf, linearly over that stalk. -/
@[stacks 01BH "the stalk of ℱ_M is 𝒪_{X,x} ⊗_R M"]
def associatedSheafStalkLinearEquiv :
    letI := stalkAlgebra X α x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((associatedSheafValFunctor X α).obj M).presheaf x) ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x ⊗[A] M) :=
  letI := stalkAlgebra X α x
  (sheafificationStalkLinearEquiv X α M x).symm.trans
    (presheafStalkLinearEquiv X α M x).symm

/-- **The linear identification is the additive one:**
`Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv` agrees pointwise with
`Stacks.AssociatedSheaf.associatedSheafStalkAddEquiv`. -/
theorem associatedSheafStalkLinearEquiv_apply
    (z : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((associatedSheafValFunctor X α).obj M).presheaf x)) :
    letI := stalkAlgebra X α x
    associatedSheafStalkLinearEquiv X α M x z = associatedSheafStalkAddEquiv X α M x z := by
  let := stalkAlgebra X α x
  have hsheaf := linearEquiv_symm_apply_eq_addEquiv_symm_apply
    (sheafificationStalkLinearEquiv X α M x) _ (sheafificationStalkLinearEquiv_apply X α M x) z
  refine Eq.trans (congrArg (presheafStalkLinearEquiv X α M x).symm hsheaf) ?_
  refine (presheafStalkLinearEquiv X α M x).symm_apply_eq.mpr ?_
  exact (presheafStalkBack_presheafStalkFwd X α M x _).symm

/-- The inverse of the linear identification is the inverse of the additive one. -/
theorem associatedSheafStalkLinearEquiv_symm_apply
    (z : letI := stalkAlgebra X α x; X.presheaf.stalk x ⊗[A] M) :
    letI := stalkAlgebra X α x
    (associatedSheafStalkLinearEquiv X α M x).symm z =
      (associatedSheafStalkAddEquiv X α M x).symm z :=
  linearEquiv_symm_apply_eq_addEquiv_symm_apply _ _
    (associatedSheafStalkLinearEquiv_apply X α M x) z

/-- **The identification `(ℱ_M)_x = 𝒪_{X,x} ⊗_A M` on pure tensors of germs**, for the linear
form of the identification: its inverse carries `germ_x(s) ⊗ m` to the germ at `x` of the
sheafified section `s ⊗ m` over `U`. -/
theorem associatedSheafStalkLinearEquiv_symm_tmul_germ (U : Opens X.carrier) (hx : x ∈ U)
    (s : X.presheaf.obj (op U)) (m : M) :
    letI := stalkAlgebra X α x
    (associatedSheafStalkLinearEquiv X α M x).symm
        ((X.presheaf.germ U x hx).hom s ⊗ₜ[A] m) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (associatedSheaf X α M).val.presheaf U x hx).hom
          ((associatedSheafUnit X α M).app (op U) (assocTmul X α M U s m)) := by
  let := stalkAlgebra X α x
  exact Eq.trans (associatedSheafStalkLinearEquiv_symm_apply X α M x _)
    (associatedSheafStalkAddEquiv_symm_tmul_germ X α M x U hx s m)

/-! ### Functoriality in the module -/

/-- `M ↦ 𝒪_{X,x} ⊗_A M`, the base change of `A`-modules along `α` followed by the germ map at
`x`, as a functor. -/
def stalkBaseChangeFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  letI := stalkAlgebra X α x
  { obj := fun M ↦ ModuleCat.of _ (X.presheaf.stalk x ⊗[A] M)
    map := fun {_ _} φ ↦ ModuleCat.ofHom (LinearMap.baseChange _ φ.hom)
    map_id := fun _ ↦ ModuleCat.hom_ext LinearMap.baseChange_id
    map_comp := fun φ ψ ↦
      ModuleCat.hom_ext (LinearMap.baseChange_comp (f := φ.hom) ψ.hom) }

/-- The base change functor on a pure tensor. -/
theorem stalkBaseChangeFunctor_map_tmul (N : ModuleCat.{u} A) (φ : M ⟶ N)
    (r : X.presheaf.stalk x) (m : M) :
    letI := stalkAlgebra X α x
    (stalkBaseChangeFunctor X α x).map φ (r ⊗ₜ[A] m) = r ⊗ₜ[A] φ m :=
  rfl

/-- `M ↦ (ℱ_M)_x`, the stalk at `x` of the sheaf associated to `M`, as a functor from `A`-modules
to `𝒪_{X,x}`-modules. -/
def associatedSheafStalkFunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  associatedSheafValFunctor X α ⋙ presheafStalkModuleFunctor X.presheaf x

/-- **The naturality square of the identification `(ℱ_M)_x = 𝒪_{X,x} ⊗_A M`.**  For an `A`-linear
map `φ : M → N` the stalk at `x` of `ℱ_φ` is, under the identification
`Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`, the base change `𝒪_{X,x} ⊗_A φ`. -/
theorem stalkMap_associatedSheafStalkLinearEquiv_symm (N : ModuleCat.{u} A) (φ : M ⟶ N)
    (z : letI := stalkAlgebra X α x; X.presheaf.stalk x ⊗[A] M) :
    letI := stalkAlgebra X α x
    AlgebraicGeometry.stalkMapLinear (R := X.presheaf) ((associatedSheafValFunctor X α).obj M)
        ((associatedSheafValFunctor X α).obj N) ((associatedSheafValFunctor X α).map φ) x
        ((associatedSheafStalkLinearEquiv X α M x).symm z) =
      (associatedSheafStalkLinearEquiv X α N x).symm
        (LinearMap.baseChange (X.presheaf.stalk x) φ.hom z) := by
  let := stalkAlgebra X α x
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | tmul r m =>
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    rw [LinearMap.baseChange_tmul,
      associatedSheafStalkLinearEquiv_symm_tmul_germ X α M x U hx s m,
      associatedSheafStalkLinearEquiv_symm_tmul_germ X α N x U hx s (φ m)]
    refine Eq.trans ?_ (associatedSheafStalkAddEquiv_symm_tmul_germ X α N x U hx s (φ m))
    refine Eq.trans ?_ (stalkMap_associatedSheafFunctor_map_germ_tmul X α M x N φ U hx s m)
    exact congrArg
      (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing X) x
        ((associatedSheafFunctor.{u, u} X α).map φ)).hom
      (associatedSheafStalkAddEquiv_symm_tmul_germ X α M x U hx s m).symm

/-- **`(ℱ_M)_x = 𝒪_{X,x} ⊗_A M`, naturally in `M`.**  The identification
`(ℱ_M)_x = 𝒪_{X,x} ⊗_A M` is a natural isomorphism of functors `ModuleCat A ⥤ ModuleCat 𝒪_{X,x}`;
its components are `Stacks.AssociatedSheaf.associatedSheafStalkLinearEquiv`. -/
@[stacks 01BH "the stalk of ℱ_M is 𝒪_{X,x} ⊗_R M, functorially in M"]
def associatedSheafStalkFunctorIso :
    stalkBaseChangeFunctor X α x ≅ associatedSheafStalkFunctor X α x :=
  letI := stalkAlgebra X α x
  NatIso.ofComponents
    (fun M ↦ LinearEquiv.toModuleIso (associatedSheafStalkLinearEquiv X α M x).symm)
    (fun {M N} φ ↦ ModuleCat.hom_ext (LinearMap.ext fun z ↦
      (stalkMap_associatedSheafStalkLinearEquiv_symm X α M x N φ z).symm))

end Stacks.AssociatedSheaf

end

end
