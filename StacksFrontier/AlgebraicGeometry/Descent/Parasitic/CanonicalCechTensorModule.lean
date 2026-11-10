module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.CechCosimplicialModule
public import StacksCore.Tactic.StacksAttribute

/-!
# The cosimplicial module of a canonical descent datum

For a commutative algebra `A` over `R`, the cosimplicial module of the canonical descent datum
of an `R`-module `M` is the Čech algebra of `R → A` tensored with `M`.

## Main definitions

* `ModuleCat.liftedBaseModule` transports `M` to the lifted base ring of the Čech algebra.
* `ModuleCat.cechTensorDegree` is the degreewise tensor product `(A/R)ₙ ⊗[R] M` and
  `ModuleCat.cechTensorGenerator` its generator `m ↦ 1 ⊗ m`.
* `ModuleCat.IsCechTensorModule` characterises the cosimplicial module by its degrees and by
  the action of each cosimplicial map on tensor generators, and `ModuleCat.cechTensorModule` is
  the resulting cosimplicial tensor module together with that characterisation.

## Main results

* `ModuleCat.canonicalDescent_cosimplicialModule` identifies the cosimplicial module of a
  canonical descent datum with the cosimplicial Čech algebra tensored with `M`.

## Implementation notes

The canonical datum is characterised by an `A`-linear equivalence from `A ⊗[R] M` whose
transition sends `(a ⊗ m) ⊗ b` to `a ⊗ (b ⊗ m)`. This is the canonical transition of Tag 023J
without requiring a particular choice of representative descent datum. The tensor cosimplicial
module is specified by its degreewise scalar extensions and its maps on generators, rather than
by a choice of an equivalent tensor-product parenthesisation; `cechTensorModule` is therefore
valued in a subtype, whose second component is that specification.

## References

* [Stacks Project, Tag 023I](https://stacks.math.columbia.edu/tag/023I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace ModuleCat


variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The algebra map `R → A`, read as a ring homomorphism `ULift R →+* ULift A` between the
canonical universe lifts over which the Čech conerve of `R → A` is formed.

This is the arrow `AlgebraicTopology.algebraMapArrow R A` of commutative algebras, retyped: its
source and target carry the `CommAlgCat` ring structures, which are the `ULift` ring structures
only after unfolding instances. Naming the retyped map makes that unfolding a fact the kernel
checks once here, rather than one the elaborator has to redo at every use. -/
private noncomputable def liftedAlgebraMap : ULift.{v} R →+* ULift.{u} A :=
  (AlgebraicTopology.algebraMapArrow R A).hom.hom.toRingHom

/-- The base module, lifted to the universe and the base ring of the Čech conerve. -/
public noncomputable abbrev liftedBaseModule (M : ModuleCat.{w} R) :
    ModuleCat.{max u v w} (ULift.{v} R) :=
  (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).obj
      (ModuleCat.of R (ULift.{max u v} M))

/-- The degree-`n` Čech algebra tensored with the base module. -/
public noncomputable abbrev cechTensorDegree (M : ModuleCat.{w} R)
    (n : SimplexCategory) :
    ModuleCat.{max u v w} ((cechCosimplicialAlgebra R A).obj n) :=
  (ModuleCat.extendScalars (cechHead R A n)).obj
    (liftedBaseModule R M)

/-- The canonical generator `m ↦ 1 ⊗ m` of a degree of the Čech tensor module. -/
public noncomputable def cechTensorGenerator (M : ModuleCat.{w} R)
    (n : SimplexCategory) :
    liftedBaseModule R M ⟶
      (ModuleCat.restrictScalars (cechHead R A n)).obj
        (cechTensorDegree R A M n) :=
  (ModuleCat.extendRestrictScalarsAdj (cechHead R A n)).unit.app
    (liftedBaseModule R M)

/-- A cosimplicial Čech module is the Čech algebra tensored with `M` if its
degrees are the scalar extensions of `M`, and every cosimplicial map takes
`1 ⊗ m` to `1 ⊗ m`. These conditions determine its maps by linearity. -/
public def IsCechTensorModule (M : ModuleCat.{w} R)
    (T : CechModule.{u, v, w} R A) : Prop :=
  ∃ h : ∀ n : SimplexCategory,
      T.obj (op (op n)) = cechTensorDegree R A M n,
    ∀ (n m : SimplexCategory) (β : n ⟶ m)
      (x : liftedBaseModule R M),
      (eqToHom (h n).symm ≫ T.map β.op.op ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (eqToHom (h m))).hom
          ((cechTensorGenerator R A M n).hom x) =
        (cechTensorGenerator R A M m).hom x

/-- The head maps of the Čech conerve are compatible with its structure maps. -/
public lemma cechHead_map {n m : SimplexCategory} (β : n ⟶ m) :
    cechHead R A m =
      (cechRingMap R A β).comp (cechHead R A n) := by
  apply RingHom.ext
  intro x
  cases x with
  | up r =>
      calc
        cechHead R A m (ULift.up r) =
            cechLeg R A m (β.toOrderHom (Fin.last n.len))
              (ULift.up (algebraMap R A r)) :=
          (cechLeg_algebraMap R A m
            (β.toOrderHom (Fin.last n.len)) r).symm
        _ = cechRingMap R A β
            (cechLeg R A n (Fin.last n.len)
              (ULift.up (algebraMap R A r))) := by
          calc
            _ = ((cechRingMap R A β).comp
                (cechLeg R A n (Fin.last n.len)))
                (ULift.up (algebraMap R A r)) :=
              (congrArg (fun f => f (ULift.up (algebraMap R A r)))
                (cechRingMap_comp_cechLeg R A β (Fin.last n.len))).symm
            _ = _ := rfl
        _ = cechRingMap R A β (cechHead R A n (ULift.up r)) :=
          congrArg (cechRingMap R A β)
            (cechLeg_algebraMap R A n (Fin.last n.len) r)

/-- The structure map of the Čech tensor module in `β : [n] → [m]`: the unique semilinear map
fixing the tensor generators. -/
public noncomputable def cechTensorStructureMap (M : ModuleCat.{w} R)
    {n m : SimplexCategory} (β : n ⟶ m) :
    cechTensorDegree R A M n ⟶
      (ModuleCat.restrictScalars (cechRingMap R A β)).obj
        (cechTensorDegree R A M m) := by
  let hhead := cechHead_map R A β
  let gen' : liftedBaseModule R M ⟶
      (ModuleCat.restrictScalars
        ((cechRingMap R A β).comp (cechHead R A n))).obj
        (cechTensorDegree R A M m) :=
    cechTensorGenerator R A M m ≫
      (ModuleCat.restrictScalarsCongr hhead).hom.app
        (cechTensorDegree R A M m)
  let gen : liftedBaseModule R M ⟶
      (ModuleCat.restrictScalars (cechHead R A n)).obj
        ((ModuleCat.restrictScalars (cechRingMap R A β)).obj
          (cechTensorDegree R A M m)) :=
    gen' ≫
      (ModuleCat.restrictScalarsComp'
        (cechHead R A n) (cechRingMap R A β)
        ((cechRingMap R A β).comp (cechHead R A n)) rfl).hom.app
        (cechTensorDegree R A M m)
  exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv
    (cechHead R A n)).symm gen

/-- The structure map of the Čech tensor module fixes the tensor generators. -/
public theorem cechTensorStructureMap_generator (M : ModuleCat.{w} R)
    {n m : SimplexCategory} (β : n ⟶ m) (x : liftedBaseModule R M) :
    (cechTensorStructureMap R A M β).hom
      ((cechTensorGenerator R A M n).hom x) =
      (cechTensorGenerator R A M m).hom x := by
  let gen' : liftedBaseModule R M ⟶
      (ModuleCat.restrictScalars
        ((cechRingMap R A β).comp (cechHead R A n))).obj
        (cechTensorDegree R A M m) :=
    cechTensorGenerator R A M m ≫
      (ModuleCat.restrictScalarsCongr (cechHead_map R A β)).hom.app
        (cechTensorDegree R A M m)
  let gen : liftedBaseModule R M ⟶
      (ModuleCat.restrictScalars (cechHead R A n)).obj
        ((ModuleCat.restrictScalars (cechRingMap R A β)).obj
          (cechTensorDegree R A M m)) :=
    gen' ≫
      (ModuleCat.restrictScalarsComp'
        (cechHead R A n) (cechRingMap R A β)
        ((cechRingMap R A β).comp (cechHead R A n)) rfl).hom.app
        (cechTensorDegree R A M m)
  let adj := ModuleCat.extendRestrictScalarsAdj (cechHead R A n)
  have h := (adj.homEquiv _ _).apply_symm_apply gen
  change (cechTensorGenerator R A M n ≫
      (ModuleCat.restrictScalars (cechHead R A n)).map
        (cechTensorStructureMap R A M β)) = gen at h
  have hx : ((cechTensorGenerator R A M n ≫
      (ModuleCat.restrictScalars (cechHead R A n)).map
        (cechTensorStructureMap R A M β)).hom x) = gen.hom x :=
    congrArg (fun f => f.hom x) h
  change ((cechTensorGenerator R A M n ≫
      (ModuleCat.restrictScalars (cechHead R A n)).map
        (cechTensorStructureMap R A M β)).hom x) =
    (cechTensorGenerator R A M m).hom x
  rw [hx]
  rfl

/-- Two maps out of a degree of the Čech tensor module agree as soon as they agree on the
tensor generators. -/
public theorem cechTensorMap_ext (M : ModuleCat.{w} R)
    {n m : SimplexCategory} (β : n ⟶ m)
    {f g : cechTensorDegree R A M n ⟶
      (ModuleCat.restrictScalars (cechRingMap R A β)).obj
        (cechTensorDegree R A M m)}
    (h : ∀ x : liftedBaseModule R M,
      f.hom ((cechTensorGenerator R A M n).hom x) =
        g.hom ((cechTensorGenerator R A M n).hom x)) : f = g := by
  apply ModuleCat.ExtendScalars.hom_ext (f := cechHead R A n)
  intro x
  convert h x using 2 <;> rfl

/-- The structure maps of the Čech conerve compose:
`(A/R)_•(β ≫ γ) = (A/R)_•(γ) ∘ (A/R)_•(β)` as ring homomorphisms. -/
public theorem cechRingMap_comp {n m l : SimplexCategory} (β : n ⟶ m) (γ : m ⟶ l) :
    cechRingMap R A (β ≫ γ) = (cechRingMap R A γ).comp (cechRingMap R A β) := by
  apply RingHom.ext
  intro z
  change (((cechCosimplicialAlgebra R A).map (β ≫ γ)).hom.toRingHom) z =
    ((cechCosimplicialAlgebra R A).map γ).hom.toRingHom
      (((cechCosimplicialAlgebra R A).map β).hom.toRingHom z)
  rw [Functor.map_comp]
  rfl

/-- The structure maps of the Čech tensor module compose. -/
public theorem cechTensorStructureMap_comp
    (M : ModuleCat.{w} R) {n m l : SimplexCategory}
    (β : n ⟶ m) (γ : m ⟶ l) :
    cechTensorStructureMap R A M (β ≫ γ) =
      cechTensorStructureMap R A M β ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (cechTensorStructureMap R A M γ) ≫
        (ModuleCat.restrictScalarsComp'
          (cechRingMap R A β) (cechRingMap R A γ)
          (cechRingMap R A (β ≫ γ))
          (cechRingMap_comp R A β γ)).inv.app
            (cechTensorDegree R A M l) := by
  apply cechTensorMap_ext R A M (β ≫ γ)
  intro x
  rw [cechTensorStructureMap_generator]
  change _ = ((ModuleCat.restrictScalarsComp' (cechRingMap R A β) (cechRingMap R A γ)
      (cechRingMap R A (β ≫ γ)) (cechRingMap_comp R A β γ)).inv.app
        (cechTensorDegree R A M l)).hom
      ((cechTensorStructureMap R A M γ).hom
        ((cechTensorStructureMap R A M β).hom ((cechTensorGenerator R A M n).hom x)))
  rw [cechTensorStructureMap_generator, cechTensorStructureMap_generator,
    ModuleCat.restrictScalarsComp'_inv_app]
  rfl

/-- The Čech cosimplicial algebra tensored with `M`, together with its
degreewise and cosimplicial-map specification. -/
@[stacks 023I "tensor cosimplicial module"]
public noncomputable def cechTensorModule (M : ModuleCat.{w} R) :
    {T : CechModule.{u, v, w} R A // IsCechTensorModule R A M T} := (by
  classical
  let T : CechModule.{u, v, w} R A :=
    PresheafOfModulesOfCommRing.mk
      (fun X => cechTensorDegree R A M (unop (unop X)))
      (fun {X Y} f => by
        exact cechTensorStructureMap R A M (unop (unop f)))
      (by
        intro X
        apply cechTensorMap_ext R A M (𝟙 (unop (unop X)))
        intro x
        rw [cechTensorStructureMap_generator]
        rfl)
      (by
        intro X Y Z f g
        exact cechTensorStructureMap_comp R A M
          (unop (unop f)) (unop (unop g)))
  refine ⟨T, ?_⟩
  refine ⟨fun n => rfl, ?_⟩
  intro n m β x
  change (cechTensorStructureMap R A M β).hom
    ((cechTensorGenerator R A M n).hom x) =
      (cechTensorGenerator R A M m).hom x
  exact cechTensorStructureMap_generator R A M β x)

private noncomputable def liftedTensorComparison
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module) :
    (ModuleCat.extendScalars
      (liftedAlgebraMap R A)).obj
        (liftedBaseModule R M) ≅
      liftedModule A D.module := by
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  letI : Module (ULift.{u} A) (A ⊗[R] M) :=
    Module.compHom _ (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom
  let source := ULift.{max u v} (A ⊗[R] M)
  let target := ULift.{u} A ⊗[ULift.{v} R] ULift.{max u v} M
  letI : Module A target := Module.compHom target
    (ULift.ringEquiv.symm : A ≃+* ULift.{u} A).toRingHom
  let tensorLift₀ := TensorProduct.AlgebraTensorModule.uliftEquiv
    (R := R) (A := A) (M := A) (N := M)
  let tensorLift : source ≃ₗ[ULift.{u} A] target := {
    toFun := tensorLift₀
    invFun := tensorLift₀.symm
    map_add' := tensorLift₀.map_add
    map_smul' := by
      intro a x
      change tensorLift₀ (a.down • x) = a • tensorLift₀ x
      rw [tensorLift₀.map_smul]
      rfl
    left_inv := tensorLift₀.left_inv
    right_inv := tensorLift₀.right_inv }
  let eLift : ULift.{max u v} (A ⊗[R] M) ≃ₗ[ULift.{u} A]
      ULift.{max u v} D.module := {
    toFun := fun x => ⟨e x.down⟩
    invFun := fun y => ⟨e.symm y.down⟩
    map_add' := by intro x y; ext; exact map_add e x.down y.down
    map_smul' := by
      intro a x
      ext
      change e (a.down • x.down) = a.down • e x.down
      exact e.map_smul a.down x.down
    left_inv := by intro x; ext; simp
    right_inv := by intro y; ext; simp }
  have hbase : liftedAlgebraMap R A =
      algebraMap (ULift.{v} R) (ULift.{u} A) := by
    apply RingHom.ext
    intro x
    cases x with
    | up r => rfl
  let hsource := congrArg (fun f : ULift.{v} R →+* ULift.{u} A =>
    (ModuleCat.extendScalars f).obj (liftedBaseModule R M)) hbase
  let fbase := ((ModuleCat.restrictScalars
      (algebraMap (ULift.{v} R) (ULift.{u} A))).obj
        (ModuleCat.of (ULift.{u} A) (ULift.{u} A)))
  letI : Module (ULift.{u} A) fbase := inferInstance
  letI : IsScalarTower (ULift.{v} R) (ULift.{u} A) fbase :=
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  let fbaseEquiv : fbase ≃ₗ[ULift.{u} A] ULift.{u} A := {
    toFun := id
    invFun := id
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  let mbaseEquiv : liftedBaseModule R M ≃ₗ[ULift.{v} R]
      ULift.{max u v} M := {
    toFun := id
    invFun := id
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  let htarget := (TensorProduct.AlgebraTensorModule.congr fbaseEquiv mbaseEquiv).toModuleIso
  exact eqToIso hsource ≪≫ htarget ≪≫ tensorLift.symm.toModuleIso ≪≫ eLift.toModuleIso

private noncomputable def liftedTensorBaseIso (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars
      (liftedAlgebraMap R A)).obj
        (liftedBaseModule R M) ≅
      ModuleCat.of (ULift.{u} A)
        (ULift.{u} A ⊗[ULift.{v} R] ULift.{max u v} M) := by
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let hbase : liftedAlgebraMap R A =
      algebraMap (ULift.{v} R) (ULift.{u} A) := by
    apply RingHom.ext
    intro x
    cases x with
    | up r => rfl
  let hsource := congrArg (fun f : ULift.{v} R →+* ULift.{u} A =>
    (ModuleCat.extendScalars f).obj (liftedBaseModule R M)) hbase
  let fbase := ((ModuleCat.restrictScalars
      (algebraMap (ULift.{v} R) (ULift.{u} A))).obj
        (ModuleCat.of (ULift.{u} A) (ULift.{u} A)))
  letI : Module (ULift.{u} A) fbase := inferInstance
  letI : IsScalarTower (ULift.{v} R) (ULift.{u} A) fbase :=
    IsScalarTower.of_algebraMap_smul fun r x => rfl
  let fbaseEquiv : fbase ≃ₗ[ULift.{u} A] ULift.{u} A := {
    toFun := id
    invFun := id
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  let mbaseEquiv : liftedBaseModule R M ≃ₗ[ULift.{v} R]
      ULift.{max u v} M := {
    toFun := id
    invFun := id
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  let htarget := (TensorProduct.AlgebraTensorModule.congr fbaseEquiv mbaseEquiv).toModuleIso
  exact eqToIso hsource ≪≫ htarget

private theorem cechLast_leg_comp_head (n : SimplexCategory) :
    (cechLeg R A n (Fin.last n.len)).comp
        (liftedAlgebraMap R A) =
      cechHead R A n := by
  apply RingHom.ext
  intro x
  cases x with
  | up r =>
      change cechLeg R A n (Fin.last n.len)
          (liftedAlgebraMap R A (ULift.up r)) =
        cechHead R A n (ULift.up r)
      rw [show liftedAlgebraMap R A (ULift.up r) =
        ULift.up (algebraMap R A r) by rfl]
      exact cechLeg_algebraMap R A n (Fin.last n.len) r

private noncomputable def canonicalDegreeComparison
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (n : SimplexCategory) :
    lastFactorModule R A D n ≅ cechTensorDegree R A M n := by
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let C := (cechCosimplicialAlgebra R A).obj n
  let head := cechHead R A n
  let baseMap := liftedAlgebraMap R A
  let leg := cechLeg R A n (Fin.last n.len)
  let hcomp := cechLast_leg_comp_head R A n
  letI : Algebra (ULift.{u} A) C := leg.toAlgebra
  letI : Algebra (ULift.{v} R) C := head.toAlgebra
  letI : IsScalarTower (ULift.{u} A) C C := inferInstance
  letI : IsScalarTower (ULift.{v} R) (ULift.{u} A)
      C := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def]
    congr 1
    have hbase : baseMap = algebraMap (ULift.{v} R) (ULift.{u} A) := by
      apply RingHom.ext
      intro z
      cases z with
      | up r => rfl
    have hc : leg (algebraMap (ULift.{v} R) (ULift.{u} A) r) = head r := by
      rw [← hbase]
      exact congrArg (fun f : ULift.{v} R →+* C => f r) hcomp
    exact hc
  let nestedIso := (ModuleCat.extendScalars leg).mapIso
    (liftedTensorComparison R A M D e)
  let nestedBaseIso := (ModuleCat.extendScalars leg).mapIso
    (liftedTensorBaseIso R A M)
  let cancel := (TensorProduct.AlgebraTensorModule.cancelBaseChange
    (R := ULift.{v} R) (A := ULift.{u} A)
    (B := C) (M := C) (N := ULift.{max u v} M)).toModuleIso
  exact nestedIso.symm ≪≫ nestedBaseIso ≪≫ cancel

private theorem canonicalDegreeComparison_inv_generator
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (n : SimplexCategory) (x : M) :
    (canonicalDegreeComparison R A M D e n).inv.hom
      ((cechTensorGenerator R A M n).hom (ULift.up x)) =
        cechGenerator R A D.module n (Fin.last n.len)
          (e (1 ⊗ₜ[R] x)) := by
  dsimp only [canonicalDegreeComparison, Iso.trans_inv, Functor.mapIso_inv]
  simp only [ModuleCat.hom_comp]
  rw [cechGenerator_eq_tmul R A D.module n (Fin.last n.len) (e (1 ⊗ₜ[R] x))]
  rfl

private theorem canonicalDegreeComparison_inv_naturality
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (he : ∀ (a b : A) (x : M),
      D.transition ((e (a ⊗ₜ[R] x)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          e (b ⊗ₜ[R] x)))
    {n m : SimplexCategory} (β : n ⟶ m) :
    (canonicalDegreeComparison R A M D e n).inv ≫ cechStructureMap D β =
      cechTensorStructureMap R A M β ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (canonicalDegreeComparison R A M D e m).inv := by
  apply ModuleCat.ExtendScalars.hom_ext (f := cechHead R A n)
  intro x
  obtain ⟨x⟩ := x
  change (cechStructureMap D β).hom
      ((canonicalDegreeComparison R A M D e n).inv.hom
        ((cechTensorGenerator R A M n).hom (ULift.up x))) =
    (canonicalDegreeComparison R A M D e m).inv.hom
      ((cechTensorStructureMap R A M β).hom
        ((cechTensorGenerator R A M n).hom (ULift.up x)))
  rw [canonicalDegreeComparison_inv_generator R A M D e n x,
    cechTensorStructureMap_generator R A M β (ULift.up x),
    canonicalDegreeComparison_inv_generator R A M D e m x]
  change (cechTransitionMap D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)).hom
      ((cechSemilinearMap R A D.module β (Fin.last n.len)).hom
        (cechGenerator R A D.module n (Fin.last n.len) (e (1 ⊗ₜ[R] x)))) = _
  rw [cechSemilinearMap_generator R A D.module β (Fin.last n.len) (e (1 ⊗ₜ[R] x)),
    cechTransitionMap_generator R A D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
      (e (1 ⊗ₜ[R] x))]
  change transitionGen D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
    (D.transition (e (1 ⊗ₜ[R] x) ⊗ₜ[R] (1 : A))) = _
  rw [he, transitionGen_tmul]
  change (cechLeg R A m (β.toOrderHom (Fin.last n.len)))
    (1 : ULift.{u} A) • _ = _
  rw [map_one, one_smul]

/-- The degreewise comparison is natural in the forward direction: it carries the structure
maps of the descent datum to those of the Čech tensor module. -/
private theorem canonicalDegreeComparison_hom_naturality
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (he : ∀ (a b : A) (x : M),
      D.transition ((e (a ⊗ₜ[R] x)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          e (b ⊗ₜ[R] x)))
    {n m : SimplexCategory} (β : n ⟶ m) :
    cechStructureMap D β ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (canonicalDegreeComparison R A M D e m).hom =
      (canonicalDegreeComparison R A M D e n).hom ≫ cechTensorStructureMap R A M β := by
  have h := canonicalDegreeComparison_inv_naturality R A M D e he β
  rw [Iso.inv_comp_eq] at h
  rw [h, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The naturality square of the degreewise comparison, with the structure map of the
cosimplicial module of the descent datum already replaced by its explicit description.  Every
restriction of scalars occurring here is spelled `cechRingMap R A β`, so the square is
type-correct at reducible transparency and rewriting inside it is reliable. -/
private theorem canonicalDegreeComparison_eqToHom_square
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (he : ∀ (a b : A) (x : M),
      D.transition ((e (a ⊗ₜ[R] x)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          e (b ⊗ₜ[R] x)))
    {n m : SimplexCategory} (β : n ⟶ m) :
    (eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫ cechStructureMap D β ≫
          eqToHom (congrArg ((ModuleCat.restrictScalars (cechRingMap R A β)).obj)
            (descentCosimplicialModuleFunctor_obj R A D m).symm)) ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (eqToHom (descentCosimplicialModuleFunctor_obj R A D m) ≫
            (canonicalDegreeComparison R A M D e m).hom) =
      (eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫
          (canonicalDegreeComparison R A M D e n).hom) ≫
        cechTensorStructureMap R A M β := by
  rw [Functor.map_comp, eqToHom_map]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    canonicalDegreeComparison_hom_naturality R A M D e he β]

/-- The naturality square of the degreewise comparison, in the terms of the cosimplicial
module of the descent datum.  Stating it separately lets the isomorphism of cosimplicial
modules be assembled from it by a single `exact`, which bridges the two spellings of the
restriction of scalars along `β`. -/
private theorem canonicalDegreeComparison_naturality_square
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (he : ∀ (a b : A) (x : M),
      D.transition ((e (a ⊗ₜ[R] x)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          e (b ⊗ₜ[R] x)))
    {n m : SimplexCategory} (β : n ⟶ m) :
    ((descentCosimplicialModuleFunctor R A).obj D).map β.op.op ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (eqToHom (descentCosimplicialModuleFunctor_obj R A D m) ≫
            (canonicalDegreeComparison R A M D e m).hom) =
      (eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫
          (canonicalDegreeComparison R A M D e n).hom) ≫
        cechTensorStructureMap R A M β := by
  rw [descentCosimplicialModuleFunctor_map R A D β]
  exact canonicalDegreeComparison_eqToHom_square R A M D e he β

/-- The cosimplicial module associated to a canonical descent datum is
isomorphic to the Čech cosimplicial algebra tensored with its base module. -/
@[stacks 023I "canonical isomorphism"]
public theorem canonicalDescent_cosimplicialModule
    (M : ModuleCat.{w} R)
    (D : DescentData.{u, v, w} R A)
    (e : (A ⊗[R] M) ≃ₗ[A] D.module)
    (he : ∀ (a b : A) (m : M),
      D.transition ((e (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
        a ⊗ₜ[R] (show restrictModule R A D.module from
          e (b ⊗ₜ[R] m))) :
    Nonempty (((descentCosimplicialModuleFunctor R A).obj D) ≅
      (cechTensorModule R A M).1) := by
  classical
  let T := (cechTensorModule R A M).1
  let S := (descentCosimplicialModuleFunctor R A).obj D
  let components : ∀ X : SimplexCategoryᵒᵖᵒᵖ, S.obj X ≅ T.obj X := fun X =>
    eqToIso (descentCosimplicialModuleFunctor_obj R A D (unop (unop X))) ≪≫
      canonicalDegreeComparison R A M D e (unop (unop X))
  refine ⟨PresheafOfModulesOfCommRing.isoMk components ?_⟩
  intro X Y f
  exact canonicalDegreeComparison_naturality_square R A M D e he (unop (unop f))


end ModuleCat

end
