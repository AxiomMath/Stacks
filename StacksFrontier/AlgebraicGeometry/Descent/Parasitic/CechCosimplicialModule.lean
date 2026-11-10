module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Amitsur
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerve
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerveDegrees
public import StacksFrontier.AlgebraicGeometry.Descent.Module.Cosimplicial
public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
public import StacksCore.Tactic.StacksAttribute

/-!
# The cosimplicial module of a descent datum

Let `A` be a commutative algebra over `R`. A descent datum `(N, φ)` for `A / R` determines a
module over the cosimplicial Čech algebra `(A / R)_•` of `R → A`, by the rules `N_n = N_{n, n}`
and `N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n}`, and the construction is functorial in the descent
datum.

## Main definitions

* `ModuleCat.cechCosimplicialAlgebra` is the cosimplicial Čech algebra of `R → A`,
  `ModuleCat.CechModule` the category of cosimplicial modules over it and
  `ModuleCat.CartesianCechModule` the full subcategory of cartesian ones.
* `ModuleCat.cechLeg` is the `i`-th leg `A → (A / R)ₙ` of the Čech conerve and
  `ModuleCat.cechRingMap` the map `(A / R)ₙ → (A / R)ₘ` of `β : [n] → [m]`.
* `ModuleCat.cechDegreeObj` is the module `N_{n, i}` obtained from the module of a descent
  datum by extension of scalars along `cechLeg`, `ModuleCat.lastFactorModule` is the diagonal
  case `N_{n, n}`, and `ModuleCat.cechGenerator` is the generator map
  `x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`.
* `ModuleCat.cechDegreeMap` extends a morphism of descent data on the module factor, leaving
  the Čech algebra factor fixed.
* `ModuleCat.cechSemilinearMap` is the semilinear map `N_{β, i}` and
  `ModuleCat.cechTransitionMap` the transition map `φⁿ_{ij} : N_{n, i} → N_{n, j}`, built from
  `ModuleCat.transitionGen` and `ModuleCat.transitionBase`.
* `ModuleCat.cechStructureMap` is the composite `φᵐ_{β(n), m} ∘ N_{β, n}`.
* `ModuleCat.IsDescentCosimplicialModuleFunctor` is the defining specification of the
  construction and `ModuleCat.descentCosimplicialModuleFunctor` the resulting functor from
  descent data to cosimplicial modules; `ModuleCat.descentCartesianModuleFunctor` is the same
  functor read into the full subcategory of cartesian cosimplicial modules.
* `ModuleCat.cechAlgebraDegZeroIso`, `ModuleCat.cechAlgebraDegOneIso` and
  `ModuleCat.cechAlgebraDegTwoIso` identify `(A / R)₀`, `(A / R)₁` and `(A / R)₂` with the
  lifted algebra and its tensor square and cube; these are the instantiations at `R → A` of
  the identifications of `StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerveDegrees`.

## Main results

* `ModuleCat.exists_descentCosimplicialModuleFunctor`: a functor satisfying both rules exists.
* `ModuleCat.descentCosimplicialModuleFunctor_obj` pins the degree-`n` module of the
  associated cosimplicial module to `N_{n, n}`.
* `ModuleCat.descentCosimplicialModuleFunctor_map` pins the structure map of `β : [n] → [m]`
  to `φᵐ_{β(n), m} ∘ N_{β, n}`.
* `ModuleCat.descentCosimplicialModuleFunctor_map_hom` pins the action on morphisms of descent
  data to extension of the underlying module map.
* `ModuleCat.cartesian_descentCosimplicialModuleFunctor_obj`: the cosimplicial module of a
  descent datum is cartesian.  It rests on `ModuleCat.isIso_cechTransitionMap`, that each
  transition map is invertible, and on `ModuleCat.isIso_cechSemilinearBaseChange`, that the
  transpose of each semilinear map is the comparison of a two-step extension of scalars, which
  is `ModuleCat.isIso_extendScalarsCompTranspose`.
* `ModuleCat.cechGenerator_eq_tmul`, `ModuleCat.cechSemilinearMap_one_tmul` and
  `ModuleCat.cechTransitionMap_one_tmul` compute the generator map, the semilinear map and the
  transition map on pure tensors; they are what determines each of these maps.
* `ModuleCat.isIso_cechLegHom_degZero`: the unique leg `A → (A / R)₀` is an isomorphism.

## Implementation notes

The functor is the witness chosen from `exists_descentCosimplicialModuleFunctor`, so the rules
of the source are proved consequences of that single existence statement rather than further
assertions, and the functor is not an opaque constant.

A cosimplicial module is `CategoryTheory.CosimplicialModule`, Mathlib's category of modules
over a presheaf of rings reindexed along the double-opposite equivalence. The Čech conerve
needs both `R` and `A` as objects of a single category of commutative algebras, so it is
formed over the canonical universe lifts `AlgebraicTopology.algebraMapArrow`; this universe
transport is internal to `CechModule`, which is indexed by `R` and `A` themselves and leaves
their universes independent.

In degree `n` the module `N_{n, i}` is the extension of scalars of `N` along the `i`-th leg
`A → (A / R)ₙ` of the Čech conerve, which is the description
`N_{n, i} = N ⊗_{(A/R)₀, (A/R)_•(τⁿ_i)} (A/R)ₙ` of the source; the module of the descent datum
is carried along the canonical lift `liftedModule` so that it lives over the lifted algebra.
The semilinear map `N_{β, i}` is the unit of the extension–restriction adjunction transported
along `(A/R)_•(β) ∘ (A/R)_•(τⁿ_i) = (A/R)_•(τᵐ_{β(i)})`, so it is the unique semilinear map
fixing the generators. The transition map `φⁿ_{ij}` is the semilinear extension of
`x ↦ φ(x ⊗ 1)` with the resulting `A`-factor placed in position `i`; this is the base change of
`φ` along `(A/R)_•(τⁿ_{ij})`, and for `i = j` it is the identity by the cocycle condition.

## References

* [Stacks Project, Tag 023H](https://stacks.math.columbia.edu/tag/023H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

universe u v w

namespace ModuleCat

section ExtendScalarsComposite

universe u₁ w₁

variable {R S T : Type u₁} [CommRing R] [CommRing S] [CommRing T]

/-- The transpose of `q` under extension–restriction of scalars sends `1 ⊗ x` to `q x`. -/
private theorem extendRestrictScalarsAdj_homEquiv_symm_one_tmul {f : R →+* S}
    {M : ModuleCat.{max u₁ w₁} R} {N : ModuleCat.{max u₁ w₁} S}
    (q : M ⟶ (ModuleCat.restrictScalars f).obj N) (x : M) :
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N).symm q).hom
      ((1 : S) ⊗ₜ[R, f] x) = q.hom x := by
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply _ x).symm.trans
    (congrArg (fun k => ModuleCat.Hom.hom k x)
      (Equiv.apply_symm_apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv M N) q))

/-- **Extension of scalars in two steps, as a comparison over the second step.**  For
`f : R ⟶ S`, `g : S ⟶ T` and `gf = g ∘ f`, the canonical `g`-semilinear map
`S ⊗_R M ⟶ T ⊗_R M` fixing the generators has an adjoint transpose
`T ⊗_S (S ⊗_R M) ⟶ T ⊗_R M`, and that transpose is an isomorphism.

The inverse is the map `1 ⊗ x ↦ 1 ⊗ (1 ⊗ x)`, built from the two units; both composites are
checked on the generators of the relevant extension of scalars. -/
public theorem isIso_extendScalarsCompTranspose
    (f : R →+* S) (g : S →+* T) (gf : R →+* T) (h : gf = g.comp f)
    (M : ModuleCat.{max u₁ w₁} R) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj g).homEquiv
          ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars gf).obj M)).symm
        (((ModuleCat.extendRestrictScalarsAdj f).homEquiv M
            ((ModuleCat.restrictScalars g).obj ((ModuleCat.extendScalars gf).obj M))).symm
          ((ModuleCat.extendRestrictScalarsAdj gf).unit.app M ≫
            (ModuleCat.restrictScalarsComp' f g gf h).hom.app
              ((ModuleCat.extendScalars gf).obj M)))) := by
  let adjf := ModuleCat.extendRestrictScalarsAdj f
  let adjg := ModuleCat.extendRestrictScalarsAdj g
  let adjgf := ModuleCat.extendRestrictScalarsAdj gf
  let E₁ := (ModuleCat.extendScalars f).obj M
  let Y := (ModuleCat.extendScalars gf).obj M
  let Z := (ModuleCat.extendScalars g).obj E₁
  let Tm : E₁ ⟶ (ModuleCat.restrictScalars g).obj Y :=
    (adjf.homEquiv M _).symm
      (adjgf.unit.app M ≫ (ModuleCat.restrictScalarsComp' f g gf h).hom.app Y)
  let Th : Z ⟶ Y := (adjg.homEquiv E₁ Y).symm Tm
  let Ti : Y ⟶ Z := (adjgf.homEquiv M Z).symm
    (adjf.unit.app M ≫ (ModuleCat.restrictScalars f).map (adjg.unit.app E₁) ≫
      (ModuleCat.restrictScalarsComp' f g gf h).inv.app Z)
  have F1 : ∀ y : E₁, Th.hom ((adjg.unit.app E₁).hom y) = Tm.hom y := fun y =>
    extendRestrictScalarsAdj_homEquiv_symm_one_tmul Tm y
  have F2 : ∀ x : M, Tm.hom ((adjf.unit.app M).hom x) = (adjgf.unit.app M).hom x := fun x =>
    extendRestrictScalarsAdj_homEquiv_symm_one_tmul _ x
  have F3 : ∀ x : M, Ti.hom ((adjgf.unit.app M).hom x)
      = (adjg.unit.app E₁).hom ((adjf.unit.app M).hom x) := fun x =>
    extendRestrictScalarsAdj_homEquiv_symm_one_tmul _ x
  have key : Tm ≫ (ModuleCat.restrictScalars g).map Ti = adjg.unit.app E₁ := by
    apply ModuleCat.ExtendScalars.hom_ext (f := f)
    intro x
    change Ti.hom (Tm.hom ((adjf.unit.app M).hom x))
      = (adjg.unit.app E₁).hom ((adjf.unit.app M).hom x)
    rw [F2 x, F3 x]
  refine ⟨Ti, ?_, ?_⟩
  · apply ModuleCat.ExtendScalars.hom_ext (f := g)
    intro y
    change Ti.hom (Th.hom ((adjg.unit.app E₁).hom y)) = (adjg.unit.app E₁).hom y
    rw [F1 y]
    exact congrArg (fun k => ModuleCat.Hom.hom k y) key
  · apply ModuleCat.ExtendScalars.hom_ext (f := gf)
    intro x
    change Th.hom (Ti.hom ((adjgf.unit.app M).hom x)) = (adjgf.unit.app M).hom x
    rw [F3 x]
    exact (F1 _).trans (F2 x)

end ExtendScalarsComposite

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- The cosimplicial Čech algebra `(A / R)ₙ` of `R → A`, formed over the canonical universe
lifts of `R` and `A`. -/
public noncomputable def cechCosimplicialAlgebra :
    CosimplicialObject (CommAlgCat.{max u v} (ULift.{v} R)) :=
  (AlgebraicTopology.algebraMapArrow R A).cechConerve

/-- A cosimplicial module over the Čech algebra `(A / R)_•` of `R → A`.  The
universe lift used to form the Čech conerve is internal to this definition, so
the notion is indexed by `R` and `A` with independent universes. -/
public abbrev CechModule :=
  CosimplicialModule.{max u v, max u v, max u v w} (cechCosimplicialAlgebra R A)

/-- The cartesian cosimplicial modules over the Čech algebra `(A / R)_•` of `R → A`, as a full
subcategory of all cosimplicial modules over it. -/
public abbrev CartesianCechModule :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (fun M : CechModule.{u, v, w} R A => CategoryTheory.CosimplicialModule.Cartesian M)

/-- The morphism of commutative algebras giving the `i`-th factor `A → (A / R)ₙ`
of the Čech conerve. -/
public noncomputable def cechLegHom (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (AlgebraicTopology.algebraMapArrow R A).right ⟶ (cechCosimplicialAlgebra R A).obj n :=
  WidePushout.ι (fun _ : Fin (n.len + 1) => (AlgebraicTopology.algebraMapArrow R A).hom) i

/-- The `i`-th leg `A → (A / R)ₙ` of the Čech conerve, as a ring homomorphism out
of the lifted algebra. -/
public noncomputable def cechLeg (n : SimplexCategory) (i : Fin (n.len + 1)) :
    ULift.{u} A →+* (cechCosimplicialAlgebra R A).obj n :=
  (cechLegHom R A n i).hom.toRingHom

/-- The ring homomorphism `(A / R)ₙ → (A / R)ₘ` induced by `β : [n] → [m]`. -/
public noncomputable def cechRingMap {n m : SimplexCategory} (β : n ⟶ m) :
    ((cechCosimplicialAlgebra R A).obj n) →+* ((cechCosimplicialAlgebra R A).obj m) :=
  ((cechCosimplicialAlgebra R A).map β).hom.toRingHom

/-- The legs of the Čech conerve are compatible with its structure maps:
`(A/R)_•(β) ∘ (A/R)_•(τⁿ_i) = (A/R)_•(τᵐ_{β(i)})`. -/
public lemma cechRingMap_comp_cechLeg {n m : SimplexCategory} (β : n ⟶ m)
    (i : Fin (n.len + 1)) :
    (cechRingMap R A β).comp (cechLeg R A n i) = cechLeg R A m (β.toOrderHom i) := by
  have h : cechLegHom R A n i ≫ (cechCosimplicialAlgebra R A).map β =
      cechLegHom R A m (β.toOrderHom i) :=
    Arrow.cechι_comp_map β i
  refine RingHom.ext fun x => ?_
  change (cechLegHom R A n i ≫ (cechCosimplicialAlgebra R A).map β).hom x =
    (cechLegHom R A m (β.toOrderHom i)).hom x
  rw [h]

/-- The structure morphism `R → (A / R)ₙ`, read off from the head of the Čech
conerve. -/
public noncomputable def cechHead (n : SimplexCategory) :
    ULift.{v} R →+* (cechCosimplicialAlgebra R A).obj n :=
  (WidePushout.head
    (fun _ : Fin (n.len + 1) => (AlgebraicTopology.algebraMapArrow R A).hom)).hom.toRingHom

/-- All legs of the Čech conerve agree on the image of the base ring. -/
public lemma cechLeg_algebraMap (n : SimplexCategory) (i : Fin (n.len + 1)) (r : R) :
    cechLeg R A n i (ULift.up (algebraMap R A r)) = cechHead R A n (ULift.up r) := by
  have h : (AlgebraicTopology.algebraMapArrow R A).hom ≫ cechLegHom R A n i =
      WidePushout.head
        (fun _ : Fin (n.len + 1) => (AlgebraicTopology.algebraMapArrow R A).hom) :=
    Arrow.hom_comp_cechι n i
  change ((AlgebraicTopology.algebraMapArrow R A).hom ≫ cechLegHom R A n i).hom (ULift.up r) =
    (WidePushout.head
      (fun _ : Fin (n.len + 1) => (AlgebraicTopology.algebraMapArrow R A).hom)).hom (ULift.up r)
  rw [h]
  rfl

/-- The `i`-th leg sends `algebraMap r * a` to the head image of `r` times the image of `a`. -/
private lemma cechLeg_algebraMap_mul (n : SimplexCategory) (i : Fin (n.len + 1)) (r : R) (a : A) :
    cechLeg R A n i (ULift.up (algebraMap R A r * a)) =
      cechHead R A n (ULift.up r) * cechLeg R A n i (ULift.up a) := by
  rw [show ULift.up (algebraMap R A r * a) = ULift.up (algebraMap R A r) * ULift.up a from rfl,
    map_mul, cechLeg_algebraMap]

/-- The module of a descent datum, lifted to the universe in which the Čech
algebra of `R → A` lives and regarded as a module over the lifted algebra. -/
public noncomputable abbrev liftedModule (N : ModuleCat.{w} A) :
    ModuleCat.{max u v w} (ULift.{u} A) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).obj
    (ModuleCat.of A (ULift.{max u v} N))

/-- The module `N_{n, i} = N ⊗_{(A/R)₀, (A/R)_•(τⁿ_i)} (A/R)ₙ`: the `(A / R)ₙ`-module
obtained from `N` by extension of scalars along the `i`-th leg of the Čech
conerve. -/
public noncomputable abbrev cechDegreeObj (N : ModuleCat.{w} A) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    ModuleCat.{max u v w} ((cechCosimplicialAlgebra R A).obj n) :=
  (ModuleCat.extendScalars (cechLeg R A n i)).obj (liftedModule A N)

/-- The degree-`n` module `N_{n,n}` of a descent datum. -/
public noncomputable abbrev lastFactorModule
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory) :=
  cechDegreeObj R A D.module n (Fin.last n.len)

private noncomputable def liftedModuleMap
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E) :
    liftedModule A D.module ⟶ liftedModule A E.module :=
  (ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).map
    ((ModuleCat.uliftFunctor.{max u v, w, v} A).map g.hom)

private theorem liftedModuleMap_id
    (D : DescentData.{u, v, w} R A) :
  liftedModuleMap R A (𝟙 D) = 𝟙 (liftedModule A D.module) := by ext x; rfl

private theorem liftedModuleMap_comp
    {D E F : DescentData.{u, v, w} R A} (g : D ⟶ E) (h : E ⟶ F) :
  liftedModuleMap R A (g ≫ h) = liftedModuleMap R A g ≫ liftedModuleMap R A h := by ext x; rfl

/-- A morphism of descent data acts on `N_{n,i}` by the identity on the
Čech-algebra factor and the underlying module map on the module factor. -/
public noncomputable def cechDegreeMap
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechDegreeObj R A D.module n i ⟶ cechDegreeObj R A E.module n i :=
  (ModuleCat.extendScalars (cechLeg R A n i)).map
    ((ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).map
      ((ModuleCat.uliftFunctor.{max u v, w, v} A).map g.hom))

private theorem cechDegreeMap_tmul
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i : Fin (n.len + 1)) (x : liftedModule A D.module) :
    (cechDegreeMap R A g n i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x) =
      (1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i]
        (liftedModuleMap R A g).hom x :=
  ModuleCat.ExtendScalars.map_tmul (cechLeg R A n i) (liftedModuleMap R A g) 1 x

private theorem cechDegreeMap_id
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechDegreeMap R A (𝟙 D) n i = 𝟙 (cechDegreeObj R A D.module n i) := by
  change (ModuleCat.extendScalars (cechLeg R A n i)).map (liftedModuleMap R A (𝟙 D)) = _
  rw [liftedModuleMap_id]
  exact (ModuleCat.extendScalars (cechLeg R A n i)).map_id _

private theorem cechDegreeMap_comp
    {D E F : DescentData.{u, v, w} R A}
    (g : D ⟶ E) (h : E ⟶ F) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechDegreeMap R A (g ≫ h) n i = cechDegreeMap R A g n i ≫ cechDegreeMap R A h n i := by
  change (ModuleCat.extendScalars (cechLeg R A n i)).map (liftedModuleMap R A (g ≫ h)) = _
  rw [liftedModuleMap_comp, Functor.map_comp]
  rfl

/-- The unit of the extension–restriction adjunction at the lifted module:
`x ↦ 1 ⊗ x`. -/
public noncomputable def cechGen (N : ModuleCat.{w} A) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    liftedModule A N ⟶
      (ModuleCat.restrictScalars (cechLeg R A n i)).obj (cechDegreeObj R A N n i) :=
  (ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).unit.app (liftedModule A N)

/-- The generator map `N → N_{n, i}`, `x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1` with `x` in position
`i`.  It is semilinear for the `i`-th leg of the Čech conerve. -/
public noncomputable def cechGenerator (N : ModuleCat.{w} A) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    restrictModule R A N →+ cechDegreeObj R A N n i where
  toFun x := (cechGen R A N n i).hom (ULift.up (x : N))
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

/-- The generator map is semilinear for the `i`-th leg of the Čech conerve. -/
public lemma cechGenerator_smul (N : ModuleCat.{w} A) (n : SimplexCategory)
    (i : Fin (n.len + 1)) (a : A) (x : restrictModule R A N) :
    cechGenerator R A N n i (a • x) =
      cechLeg R A n i (ULift.up a) • cechGenerator R A N n i x :=
  (cechGen R A N n i).hom.map_smul (ULift.up a) (ULift.up (x : N))

/-- The generator map is the pure tensor `1 ⊗ x` in the extension of scalars. -/
public theorem cechGenerator_eq_tmul (N : ModuleCat.{w} A) (n : SimplexCategory)
    (i : Fin (n.len + 1)) (x : restrictModule R A N) :
    cechGenerator R A N n i x =
      (1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i]
        (ULift.up (x : N)) :=
  ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _

private theorem cechGen_map
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i : Fin (n.len + 1)) (x : liftedModule A D.module) :
    (cechDegreeMap R A g n i).hom ((cechGen R A D.module n i).hom x) =
      (cechGen R A E.module n i).hom ((liftedModuleMap R A g).hom x) := by
  change (ModuleCat.extendScalars (cechLeg R A n i)).map (liftedModuleMap R A g)
      ((ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).unit.app
        (liftedModule A D.module) x) =
    (ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).unit.app
      (liftedModule A E.module) ((liftedModuleMap R A g).hom x)
  exact congrArg (fun f => f.hom x)
    ((ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).unit.naturality
      (liftedModuleMap R A g)).symm

private theorem cechGenerator_map
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
  (cechDegreeMap R A g n i).hom (cechGenerator R A D.module n i x) =
      cechGenerator R A E.module n i (restrictHom R A g.hom x) := by
  exact cechGen_map R A g n i (ULift.up x)

/-- The semilinear map `N_{β, i} : N_{n, i} → N_{m, β(i)}`: the unique
`(A/R)_•(β)`-semilinear map fixing the generators. -/
public noncomputable def cechSemilinearMap (N : ModuleCat.{w} A)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1)) :
    cechDegreeObj R A N n i ⟶
      (ModuleCat.restrictScalars (cechRingMap R A β)).obj
        (cechDegreeObj R A N m (β.toOrderHom i)) :=
  ((ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).homEquiv (liftedModule A N)
      ((ModuleCat.restrictScalars (cechRingMap R A β)).obj
        (cechDegreeObj R A N m (β.toOrderHom i)))).symm
    (cechGen R A N m (β.toOrderHom i) ≫
      (ModuleCat.restrictScalarsComp' (cechLeg R A n i) (cechRingMap R A β)
        (cechLeg R A m (β.toOrderHom i))
        (cechRingMap_comp_cechLeg R A β i).symm).hom.app _)

variable {R A}

/-- The additive map `A ⊗[R] N → N_{n, j}` sending `a ⊗ x` to `a` times the
generator of `x`, with the factor `a` in position `i`. -/
public noncomputable def transitionGen
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) :
    (A ⊗[R] restrictModule R A D.module) →+
      cechDegreeObj R A D.module n j :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun x =>
            cechLeg R A n i (ULift.up a) • cechGenerator R A D.module n j x
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun x y => by rw [map_add, smul_add] }
      map_zero' := by
        refine AddMonoidHom.ext fun x => ?_
        change cechLeg R A n i (ULift.up (0 : A)) • cechGenerator R A D.module n j x = 0
        rw [show cechLeg R A n i (ULift.up (0 : A)) = 0 from map_zero _, zero_smul]
      map_add' := fun a b => by
        refine AddMonoidHom.ext fun x => ?_
        change cechLeg R A n i (ULift.up (a + b)) • cechGenerator R A D.module n j x =
          cechLeg R A n i (ULift.up a) • cechGenerator R A D.module n j x +
            cechLeg R A n i (ULift.up b) • cechGenerator R A D.module n j x
        rw [show cechLeg R A n i (ULift.up (a + b)) =
          cechLeg R A n i (ULift.up a) + cechLeg R A n i (ULift.up b) from map_add _ _ _,
          add_smul] }
    (fun r a x => by
      change cechLeg R A n i (ULift.up (r • a)) • cechGenerator R A D.module n j x =
        cechLeg R A n i (ULift.up a) •
          cechGenerator R A D.module n j (algebraMap R A r • x)
      rw [Algebra.smul_def,
        show cechLeg R A n i (ULift.up (algebraMap R A r * a)) =
            cechLeg R A n i (ULift.up (algebraMap R A r)) * cechLeg R A n i (ULift.up a) from
          map_mul _ _ _,
        cechGenerator_smul, ← mul_smul, cechLeg_algebraMap, cechLeg_algebraMap,
        mul_comm (cechHead R A n (ULift.up r)) (cechLeg R A n i (ULift.up a))])

/-- The generator formula on a tensor. -/
@[simp]
public lemma transitionGen_tmul (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j : Fin (n.len + 1)) (a : A)
    (x : restrictModule R A D.module) :
    transitionGen D n i j (a ⊗ₜ[R] x) =
      cechLeg R A n i (ULift.up a) • cechGenerator R A D.module n j x :=
  rfl

/-- The generator formula is semilinear for the action of `A` through the `i`-th
leg of the Čech conerve. -/
public lemma transitionGen_smul (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j : Fin (n.len + 1)) (a : A)
    (w : A ⊗[R] restrictModule R A D.module) :
    transitionGen D n i j ((a ⊗ₜ[R] (1 : A) : A ⊗[R] A) • w) =
      cechLeg R A n i (ULift.up a) • transitionGen D n i j w := by
  induction w with
  | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]
  | tmul c x =>
    have h1 : restrictedScalarAction R A D.module 1 x = x := one_smul A x
    rw [targetTensor_smul_tmul, h1, transitionGen_tmul,
      transitionGen_tmul, ← mul_smul, ← map_mul]
    rfl

private theorem transitionGen_base_smul (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j : Fin (n.len + 1)) (r : R)
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen D n i j (r • z) =
      cechHead R A n (ULift.up r) • transitionGen D n i j z := by
  induction z with
  | add x y hx hy => simp [hx, hy, smul_add]
  | tmul a x =>
      rw [TensorProduct.smul_tmul', Algebra.smul_def, transitionGen_tmul,
        transitionGen_tmul]
      rw [cechLeg_algebraMap_mul, mul_smul]

private noncomputable def transitionGen₂ (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1)) :
    ((A ⊗[R] A) ⊗[R] restrictModule R A D.module) →+
      cechDegreeObj R A D.module n k := by
  let f : A ⊗[R] (A ⊗[R] restrictModule R A D.module) →+
      cechDegreeObj R A D.module n k :=
    TensorProduct.liftAddHom
      { toFun := fun a =>
          { toFun := fun z =>
              cechLeg R A n i (ULift.up a) • transitionGen D n j k z
            map_zero' := by simp
            map_add' := by intro x y; simp [smul_add]
          }
        map_zero' := by
          ext z
          change cechLeg R A n i (ULift.up (0 : A)) • transitionGen D n j k z = 0
          rw [show ULift.up (0 : A) = 0 from rfl, map_zero, zero_smul]
        map_add' := by
          intro a b
          ext z
          simp only [AddMonoidHom.add_apply]
          change cechLeg R A n i (ULift.up (a + b)) • transitionGen D n j k z =
            cechLeg R A n i (ULift.up a) • transitionGen D n j k z +
              cechLeg R A n i (ULift.up b) • transitionGen D n j k z
          rw [show ULift.up (a + b) = ULift.up a + ULift.up b from rfl,
            map_add, add_smul]
      }
      (fun r a z => by
        change cechLeg R A n i (ULift.up (r • a)) • transitionGen D n j k z =
          cechLeg R A n i (ULift.up a) • transitionGen D n j k (r • z)
        rw [Algebra.smul_def]
        rw [cechLeg_algebraMap_mul, transitionGen_base_smul]
        rw [smul_smul]
        congr 1
        exact mul_comm (cechHead R A n (ULift.up r))
          (cechLeg R A n i (ULift.up a)))
  exact f.comp (TensorProduct.assoc R A A
    (restrictModule R A D.module)).toAddMonoidHom

private theorem transitionGen₂_tmul
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1))
    (a b : A) (x : restrictModule R A D.module) :
    transitionGen₂ D n i j k ((a ⊗ₜ[R] b) ⊗ₜ[R] x) =
      (cechLeg R A n i (ULift.up a) * cechLeg R A n j (ULift.up b)) •
        cechGenerator R A D.module n k x := by
  change cechLeg R A n i (ULift.up a) •
    transitionGen D n j k (b ⊗ₜ[R] x) = _
  rw [transitionGen_tmul, smul_smul]

private theorem transitionGen₂_outer_tmul
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1)) (a : A)
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen₂ D n i j k
        ((TensorProduct.assoc R A A (restrictModule R A D.module)).symm
          (a ⊗ₜ[R] z)) =
      cechLeg R A n i (ULift.up a) • transitionGen D n j k z := by
  simp [transitionGen₂]

private theorem transitionGen₂_rightComm_one
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen₂ D n i j k
        ((TensorProduct.rightComm R A (restrictModule R A D.module) A)
          (z ⊗ₜ[R] (1 : A))) =
      transitionGen D n i k z := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ =>
      simp only [TensorProduct.add_tmul, LinearEquiv.map_add,
        AddMonoidHom.map_add, hz₁, hz₂]
  | tmul a x =>
      simp only [TensorProduct.rightComm_tmul, transitionGen₂_tmul, transitionGen_tmul]
      rw [show cechLeg R A n j (ULift.up (1 : A)) = 1 from map_one _, mul_one]

private theorem transitionGen_map
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i j : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    (cechDegreeMap R A g n j).hom (transitionGen D n i j z) =
      transitionGen E n i j
        ((restrictHom R A g.hom).lTensor A z) := by
  induction z with
  | add p q hp hq => simp [hp, hq]
  | tmul a x =>
      simp only [transitionGen_tmul, LinearMap.lTensor_tmul]
      rw [map_smul, cechGenerator_map]

/-- The additive map `N → N_{n, j}` sending `x` to `φ(x ⊗ 1)` with the resulting
`A`-factor in position `i`. -/
public noncomputable def transitionBase
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) :
    restrictModule R A D.module →+ cechDegreeObj R A D.module n j :=
  (transitionGen D n i j).comp
    (((D.transitionRestrictScalars R A).toLinearMap.comp
      ((TensorProduct.mk R (restrictModule R A D.module) A).flip 1)).toAddMonoidHom)

/-- `x ↦ φ(x ⊗ 1)` is semilinear for the action of `A` through the `i`-th leg of
the Čech conerve; this is where the cocycle-free part of `φ` enters. -/
public lemma transitionBase_smul (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j : Fin (n.len + 1)) (a : A)
    (x : restrictModule R A D.module) :
    transitionBase D n i j (a • x) =
      cechLeg R A n i (ULift.up a) • transitionBase D n i j x := by
  have h1 : ((a • x : restrictModule R A D.module) ⊗ₜ[R] (1 : A)) =
      (a ⊗ₜ[R] (1 : A) : A ⊗[R] A) •
        ((x : restrictModule R A D.module) ⊗ₜ[R] (1 : A)) := by
    rw [sourceTensor_smul_tmul, mul_one]
    rfl
  change transitionGen D n i j (D.transition
      ((a • x : restrictModule R A D.module) ⊗ₜ[R] (1 : A))) =
    cechLeg R A n i (ULift.up a) • transitionGen D n i j
      (D.transition ((x : restrictModule R A D.module) ⊗ₜ[R] (1 : A)))
  rw [h1, D.transition.map_smul]
  exact transitionGen_smul D n i j a _

private theorem tensorComm_smul_left
    (N : ModuleCat.{w} A) (a : A)
    (z : restrictModule R A N ⊗[R] A) :
    (TensorProduct.comm R (restrictModule R A N) A)
        (((a ⊗ₜ[R] (1 : A) : A ⊗[R] A)) • z) =
      ((1 : A) ⊗ₜ[R] a : A ⊗[R] A) •
        (TensorProduct.comm R (restrictModule R A N) A z) := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | tmul x b =>
      simp [sourceTensor_smul_tmul, targetTensor_smul_tmul]
      rfl

private theorem tensorComm_smul_right
    (N : ModuleCat.{w} A) (a : A)
    (z : restrictModule R A N ⊗[R] A) :
    (TensorProduct.comm R (restrictModule R A N) A)
        (((1 : A) ⊗ₜ[R] a : A ⊗[R] A) • z) =
      (a ⊗ₜ[R] (1 : A) : A ⊗[R] A) •
        (TensorProduct.comm R (restrictModule R A N) A z) := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | tmul x b =>
      simp [sourceTensor_smul_tmul, targetTensor_smul_tmul]

private theorem transitionGen_smul_second
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) (a : A)
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen D n i i (((1 : A) ⊗ₜ[R] a : A ⊗[R] A) • z) =
      cechLeg R A n i (ULift.up a) • transitionGen D n i i z := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂, smul_add]
  | tmul b x =>
      simp only [targetTensor_smul_tmul, transitionGen_tmul]
      rw [show restrictedScalarAction R A D.module a x = a • x from rfl,
        cechGenerator_smul]
      simp [mul_one, smul_smul, mul_comm]

private noncomputable def transitionBaseReverse
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    restrictModule R A D.module →+
      cechDegreeObj R A D.module n i :=
  (transitionGen D n i i).comp
    ((TensorProduct.comm R (restrictModule R A D.module) A).toAddMonoidHom.comp
      (D.transition.symm.toLinearMap.toAddMonoidHom.comp
        ((TensorProduct.mk R A (restrictModule R A D.module)) (1 : A)).toAddMonoidHom))

private theorem transitionBaseReverse_smul
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) (a : A)
    (x : restrictModule R A D.module) :
    transitionBaseReverse D n i (a • x) =
      cechLeg R A n i (ULift.up a) • transitionBaseReverse D n i x := by
  have h1 : (1 : A) ⊗ₜ[R] (a • x : restrictModule R A D.module) =
      ((1 : A) ⊗ₜ[R] a : A ⊗[R] A) •
        ((1 : A) ⊗ₜ[R] (x : restrictModule R A D.module)) := by
    rw [targetTensor_smul_tmul]
    simp [mul_one]
    rfl
  dsimp [transitionBaseReverse]
  change transitionGen D n i i
      ((TensorProduct.comm R (restrictModule R A D.module) A)
        (D.transition.symm (1 ⊗ₜ[R] (a • x)))) = _
  rw [h1, D.transition.symm.map_smul, tensorComm_smul_right,
    transitionGen_smul]

private theorem transitionBase_map
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i j : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
    (cechDegreeMap R A g n j).hom (transitionBase D n i j x) =
      transitionBase E n i j (restrictHom R A g.hom x) := by
  change (cechDegreeMap R A g n j).hom
      (transitionGen D n i j
        (D.transitionRestrictScalars R A (x ⊗ₜ[R] (1 : A)))) =
    transitionGen E n i j
      (E.transitionRestrictScalars R A
        (restrictHom R A g.hom x ⊗ₜ[R] (1 : A)))
  rw [transitionGen_map]
  have hc := DFunLike.congr_fun g.comm (x ⊗ₜ[R] (1 : A))
  simpa [restrictHom] using congrArg (transitionGen E n i j) hc.symm

private noncomputable def transitionBaseHom
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) :
    liftedModule A D.module ⟶ (ModuleCat.restrictScalars (cechLeg R A n i)).obj
      (cechDegreeObj R A D.module n j) :=
  ModuleCat.ofHom
    (X := liftedModule A D.module)
    (Y := (ModuleCat.restrictScalars (cechLeg R A n i)).obj
      (cechDegreeObj R A D.module n j))
    { toFun := fun x => transitionBase D n i j (ULift.down x)
      map_add' := fun _ _ => map_add (transitionBase D n i j) _ _
      map_smul' := fun α _ => transitionBase_smul D n i j α.down _ }

/-- The transition map `φⁿ_{ij} : N_{n, i} → N_{n, j}` of a descent datum: the
base change of its transition isomorphism `φ`, which moves the module factor
from position `i` to position `j`. -/
public noncomputable def cechTransitionMap
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) :
    cechDegreeObj R A D.module n i ⟶ cechDegreeObj R A D.module n j :=
  ((ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).homEquiv (liftedModule A D.module)
      (cechDegreeObj R A D.module n j)).symm
    (ModuleCat.ofHom
      (X := liftedModule A D.module)
      (Y := (ModuleCat.restrictScalars (cechLeg R A n i)).obj
        (cechDegreeObj R A D.module n j))
      { toFun := fun x => transitionBase D n i j (ULift.down x)
        map_add' := fun _ _ => map_add (transitionBase D n i j) _ _
        map_smul' := fun α _ => transitionBase_smul D n i j α.down _ })

/-- The transition map `φⁿ_{ij}` carries the pure tensor `1 ⊗ x` to `φ(x ⊗ 1)` with the
resulting `A`-factor in position `i`. -/
public theorem cechTransitionMap_one_tmul
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) (x : liftedModule A D.module) :
    (cechTransitionMap D n i j).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x) =
      transitionBase D n i j (ULift.down x) := by
  exact extendRestrictScalarsAdj_homEquiv_symm_one_tmul (transitionBaseHom D n i j) x

private theorem transitionGen₂_transition12
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    transitionGen₂ D n i j k
        ((transition12 R A D.module D.transition) (z ⊗ₜ[R] (1 : A))) =
      (cechTransitionMap D n j k).hom (transitionGen D n i j z) := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ =>
      rw [TensorProduct.add_tmul, map_add, map_add, hz₁, hz₂, map_add]
      exact ((cechTransitionMap D n j k).hom.map_add _ _).symm
  | tmul a x =>
      have htr :
          (transition12 R A D.module D.transition)
              ((a ⊗ₜ[R] x) ⊗ₜ[R] (1 : A)) =
            (TensorProduct.assoc R A A (restrictModule R A D.module)).symm
              (a ⊗ₜ[R] D.transition (x ⊗ₜ[R] (1 : A))) := by
        simp [transition12]
      rw [htr, transitionGen₂_outer_tmul]
      change cechLeg R A n i (ULift.up a) • transitionBase D n j k x =
        (cechTransitionMap D n j k).hom
          (cechLeg R A n i (ULift.up a) • cechGenerator R A D.module n j x)
      rw [map_smul]
      exact congrArg (fun y => cechLeg R A n i (ULift.up a) • y)
        ((congrArg (cechTransitionMap D n j k).hom
          (cechGenerator_eq_tmul R A D.module n j x)).trans
          (cechTransitionMap_one_tmul D n j k (ULift.up x))).symm

private theorem transitionGen₂_transition02
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
    transitionGen₂ D n i j k
        ((transition02 R A D.module D.transition)
          ((x ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) =
      transitionBase D n i k x := by
  simp only [transition02, LinearMap.comp_apply]
  change transitionGen₂ D n i j k
      ((TensorProduct.rightComm R A (restrictModule R A D.module) A)
        (D.transition (x ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) = _
  exact transitionGen₂_rightComm_one D n i j k
    (D.transition (x ⊗ₜ[R] (1 : A)))

private theorem transitionBase_cocycle
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
    (cechTransitionMap D n j k).hom (transitionBase D n i j x) =
      transitionBase D n i k x := by
  let t := ((x ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))
  have h01 : (transition01 R A D.module D.transition) t =
      D.transition (x ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) := by
    simp [transition01, t]
  have h := congrArg (transitionGen₂ D n i j k) (DFunLike.congr_fun D.cocycle t)
  simp only [LinearMap.comp_apply, h01, transitionGen₂_transition12] at h
  change _ = transitionGen₂ D n i j k
    ((transition02 R A D.module D.transition)
      ((x ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) at h
  rw [transitionGen₂_transition02] at h
  change (cechTransitionMap D n j k).hom
    (transitionGen D n i j (D.transition (x ⊗ₜ[R] (1 : A)))) =
    transitionGen D n i k (D.transition (x ⊗ₜ[R] (1 : A)))
  exact h

private noncomputable def transitionBaseReverseHom
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    liftedModule A D.module ⟶
      (ModuleCat.restrictScalars (cechLeg R A n i)).obj
        (cechDegreeObj R A D.module n i) :=
  ModuleCat.ofHom
    (X := liftedModule A D.module)
    (Y := (ModuleCat.restrictScalars (cechLeg R A n i)).obj
      (cechDegreeObj R A D.module n i))
    { toFun := fun x => transitionBaseReverse D n i (ULift.down x)
      map_add' := fun _ _ => map_add (transitionBaseReverse D n i) _ _
      map_smul' := fun α _ => transitionBaseReverse_smul D n i α.down _ }

private noncomputable def cechTransitionMapReverse
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechDegreeObj R A D.module n i ⟶ cechDegreeObj R A D.module n i :=
  ((ModuleCat.extendRestrictScalarsAdj (cechLeg R A n i)).homEquiv
      (liftedModule A D.module) (cechDegreeObj R A D.module n i)).symm
    (transitionBaseReverseHom D n i)

private theorem cechTransitionMapReverse_generator
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) (x : liftedModule A D.module) :
    (cechTransitionMapReverse D n i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x) =
      transitionBaseReverse D n i (ULift.down x) := by
  exact extendRestrictScalarsAdj_homEquiv_symm_one_tmul (transitionBaseReverseHom D n i) x

private theorem cechTransitionMapReverse_transitionGen
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    (cechTransitionMapReverse D n i).hom (transitionGen D n i i z) =
      transitionGen D n i i
        ((TensorProduct.comm R (restrictModule R A D.module) A)
          (D.transition.symm z)) := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂]
  | tmul a x =>
      have h : (a ⊗ₜ[R] (x : restrictModule R A D.module)) =
          (a ⊗ₜ[R] (1 : A) : A ⊗[R] A) •
            ((1 : A) ⊗ₜ[R] (x : restrictModule R A D.module)) := by
        rw [targetTensor_smul_tmul]
        simp
      rw [transitionGen_tmul, map_smul]
      have hg := cechTransitionMapReverse_generator D n i (ULift.up (x : D.module))
      change (cechTransitionMapReverse D n i).hom (cechGenerator R A D.module n i x) =
        transitionBaseReverse D n i x at hg
      rw [hg]
      dsimp [transitionBaseReverse]
      rw [h, D.transition.symm.map_smul, tensorComm_smul_left,
        transitionGen_smul_second]

private theorem cechTransitionMap_comp
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i j k : Fin (n.len + 1)) :
    cechTransitionMap D n i j ≫ cechTransitionMap D n j k =
      cechTransitionMap D n i k := by
  apply ModuleCat.ExtendScalars.hom_ext (f := cechLeg R A n i); intro x
  change (cechTransitionMap D n j k).hom
      ((cechTransitionMap D n i j).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)) =
    (cechTransitionMap D n i k).hom
      ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)
  rw [cechTransitionMap_one_tmul, cechTransitionMap_one_tmul]
  exact transitionBase_cocycle D n i j k (ULift.down x)

private theorem cechTransitionMap_self
    (D : DescentData.{u, v, w} R A)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    cechTransitionMap D n i i = 𝟙 _ := by
  have hinv : cechTransitionMap D n i i ≫ cechTransitionMapReverse D n i = 𝟙 _ := by
    apply ModuleCat.ExtendScalars.hom_ext (f := cechLeg R A n i)
    intro x
    change (cechTransitionMapReverse D n i).hom
        ((cechTransitionMap D n i i).hom
          ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)) =
      (1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x
    rw [cechTransitionMap_one_tmul]
    change (cechTransitionMapReverse D n i).hom
      (transitionGen D n i i (D.transition (x.down ⊗ₜ[R] (1 : A)))) = _
    rw [cechTransitionMapReverse_transitionGen, D.transition.symm_apply_apply]
    change transitionGen D n i i
      ((1 : A) ⊗ₜ[R] (x.down : restrictModule R A D.module)) = _
    rw [transitionGen_tmul D n i i 1 x.down,
      show cechLeg R A n i (ULift.up (1 : A)) = 1 from map_one _, one_smul]
    exact cechGenerator_eq_tmul R A D.module n i x.down
  have hc := congrArg (fun f => f ≫ cechTransitionMapReverse D n i)
    (cechTransitionMap_comp D n i i i)
  simpa only [Category.assoc, hinv, Category.comp_id] using hc

private theorem cechTransitionMap_natural
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    cechDegreeMap R A g n i ≫ cechTransitionMap E n i j =
      cechTransitionMap D n i j ≫ cechDegreeMap R A g n j := by
  apply ModuleCat.ExtendScalars.hom_ext (f := cechLeg R A n i); intro x
  change (cechTransitionMap E n i j).hom
      ((cechDegreeMap R A g n i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)) =
    (cechDegreeMap R A g n j).hom
      ((cechTransitionMap D n i j).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x))
  rw [cechDegreeMap_tmul]
  calc
    _ = transitionBase E n i j (ULift.down ((liftedModuleMap R A g) x)) :=
      cechTransitionMap_one_tmul E n i j ((liftedModuleMap R A g) x)
    _ = transitionBase E n i j (restrictHom R A g.hom (ULift.down x)) := by
      congr 1
    _ = (cechDegreeMap R A g n j).hom
        (transitionBase D n i j (ULift.down x)) :=
      (transitionBase_map g n i j (ULift.down x)).symm
    _ = (cechDegreeMap R A g n j).hom
        ((cechTransitionMap D n i j).hom
          ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)) :=
      (congrArg (cechDegreeMap R A g n j).hom (cechTransitionMap_one_tmul D n i j x)).symm

/-- The semilinear map `N_{β, i}` carries the pure tensor `1 ⊗ x` to the generator of `x` in
degree `m` and position `β(i)`. -/
public theorem cechSemilinearMap_one_tmul (N : ModuleCat.{w} A)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1))
    (x : liftedModule A N) :
    (cechSemilinearMap R A N β i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x) =
      (cechGen R A N m (β.toOrderHom i)).hom x := by
  exact extendRestrictScalarsAdj_homEquiv_symm_one_tmul _ x

private theorem cechSemilinearMap_natural
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1)) :
    cechDegreeMap R A g n i ≫ cechSemilinearMap R A E.module β i =
      cechSemilinearMap R A D.module β i ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (cechDegreeMap R A g m (β.toOrderHom i)) := by
  apply ModuleCat.ExtendScalars.hom_ext (f := cechLeg R A n i); intro x
  change (cechSemilinearMap R A E.module β i).hom
      ((cechDegreeMap R A g n i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x)) =
    ((ModuleCat.restrictScalars (cechRingMap R A β)).map
        (cechDegreeMap R A g m (β.toOrderHom i))).hom
      ((cechSemilinearMap R A D.module β i).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A, cechLeg R A n i] x))
  exact (congrArg ((cechSemilinearMap R A E.module β i).hom)
      (cechDegreeMap_tmul (R := R) (A := A) g n i x)).trans
    ((cechSemilinearMap_one_tmul E.module β i ((liftedModuleMap R A g).hom x)).trans
      ((cechGen_map R A g m (β.toOrderHom i) x).symm.trans
        (congrArg (fun y =>
          ((ModuleCat.restrictScalars (cechRingMap R A β)).map
            (cechDegreeMap R A g m (β.toOrderHom i))).hom y)
          (cechSemilinearMap_one_tmul D.module β i x).symm)))

private theorem transitionGen_natural (D : DescentData.{u, v, w} R A)
    {n m : SimplexCategory} (β : n ⟶ m) (i j : Fin (n.len + 1))
    (z : A ⊗[R] restrictModule R A D.module) :
    (cechSemilinearMap R A D.module β j).hom (transitionGen D n i j z) =
      transitionGen D m (β.toOrderHom i) (β.toOrderHom j) z := by
  induction z with
  | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add (transitionGen D n i j) z₁ z₂, (cechSemilinearMap R A D.module β j).hom.map_add,
        hz₁, hz₂]
      exact (map_add (transitionGen D m (β.toOrderHom i) (β.toOrderHom j)) z₁ z₂).symm
  | tmul a x =>
      have hg := (congrArg (cechSemilinearMap R A D.module β j).hom
        (cechGenerator_eq_tmul R A D.module n j x)).trans
        (cechSemilinearMap_one_tmul D.module β j (ULift.up (x : D.module)))
      rw [transitionGen_tmul, transitionGen_tmul]
      change (cechSemilinearMap R A D.module β j).hom (_ • _) = _
      rw [map_smul]
      change cechRingMap R A β (cechLeg R A n i (ULift.up a)) •
        (cechSemilinearMap R A D.module β j).hom (cechGenerator R A D.module n j x) = _
      rw [hg, show cechRingMap R A β (cechLeg R A n i (ULift.up a)) =
        cechLeg R A m (β.toOrderHom i) (ULift.up a) from
          congrArg (fun f => f (ULift.up a)) (cechRingMap_comp_cechLeg R A β i)]
      rfl

/-- The structure map `N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n} : N_{n, n} → N_{m, m}`
attached to `β : [n] → [m]`. -/
public noncomputable def cechStructureMap
    (D : DescentData.{u, v, w} R A) {n m : SimplexCategory} (β : n ⟶ m) :
    cechDegreeObj R A D.module n (Fin.last n.len) ⟶
      (ModuleCat.restrictScalars (cechRingMap R A β)).obj
        (cechDegreeObj R A D.module m (Fin.last m.len)) :=
  cechSemilinearMap R A D.module β (Fin.last n.len) ≫
    (ModuleCat.restrictScalars (cechRingMap R A β)).map
      (cechTransitionMap D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len))

private theorem cechStructureMap_natural
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    {n m : SimplexCategory} (β : n ⟶ m) :
    cechDegreeMap R A g n (Fin.last n.len) ≫ cechStructureMap E β =
      cechStructureMap D β ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (cechDegreeMap R A g m (Fin.last m.len)) := by
  dsimp [cechStructureMap]
  rw [← Category.assoc, cechSemilinearMap_natural, Category.assoc, Category.assoc,
    ← Functor.map_comp, cechTransitionMap_natural, Functor.map_comp]

private theorem cechStructureMap_one_tmul
    (D : DescentData.{u, v, w} R A)
    {n m : SimplexCategory} (β : n ⟶ m) (x : liftedModule A D.module) :
    (cechStructureMap D β).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n) ⊗ₜ[ULift.{u} A,
          cechLeg R A n (Fin.last n.len)] x) =
      transitionBase D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len) x.down := by
  change (cechTransitionMap D m _ _).hom
    ((cechSemilinearMap R A D.module β _).hom _) = _
  rw [cechSemilinearMap_one_tmul]
  exact cechTransitionMap_one_tmul D m _ _ x

private theorem cechStructureMap_transitionBase
    (D : DescentData.{u, v, w} R A)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1))
    (x : restrictModule R A D.module) :
    (cechStructureMap D β).hom (transitionBase D n i (Fin.last n.len) x) =
      transitionBase D m (β.toOrderHom i) (Fin.last m.len) x := by
  change (cechTransitionMap D m _ _).hom
    ((cechSemilinearMap R A D.module β _).hom
      (transitionGen D n i _ (D.transition (x ⊗ₜ[R] (1 : A))))) = _
  rw [transitionGen_natural]
  exact transitionBase_cocycle D m _ _ _ x

private noncomputable def cechModuleOfDatum
    (D : DescentData.{u, v, w} R A) : CechModule.{u, v, w} R A :=
  PresheafOfModulesOfCommRing.mk
    (fun n => cechDegreeObj R A D.module n.unop.unop (Fin.last n.unop.unop.len))
    (fun β => cechStructureMap D β.unop.unop)
    (by
      intro n
      apply ModuleCat.ExtendScalars.hom_ext
        (f := cechLeg R A n.unop.unop (Fin.last n.unop.unop.len))
      intro x
      change (cechStructureMap D (𝟙 n.unop.unop)).hom
        ((1 : (cechCosimplicialAlgebra R A).obj n.unop.unop) ⊗ₜ[ULift.{u} A,
            cechLeg R A n.unop.unop (Fin.last n.unop.unop.len)] x) =
          (1 : (cechCosimplicialAlgebra R A).obj n.unop.unop) ⊗ₜ[ULift.{u} A,
            cechLeg R A n.unop.unop (Fin.last n.unop.unop.len)] x
      rw [cechStructureMap_one_tmul]
      change transitionBase D n.unop.unop (Fin.last n.unop.unop.len)
        (Fin.last n.unop.unop.len) x.down = _
      rw [← cechTransitionMap_one_tmul, cechTransitionMap_self]
      rfl)
    (by
      intro n m k β γ
      apply ModuleCat.ExtendScalars.hom_ext
        (f := cechLeg R A n.unop.unop (Fin.last n.unop.unop.len))
      intro x
      change (cechStructureMap D (β ≫ γ).unop.unop).hom
          ((1 : (cechCosimplicialAlgebra R A).obj n.unop.unop) ⊗ₜ[ULift.{u} A,
            cechLeg R A n.unop.unop (Fin.last n.unop.unop.len)] x) =
        (cechStructureMap D γ.unop.unop).hom ((cechStructureMap D β.unop.unop).hom
          ((1 : (cechCosimplicialAlgebra R A).obj n.unop.unop) ⊗ₜ[ULift.{u} A,
            cechLeg R A n.unop.unop (Fin.last n.unop.unop.len)] x))
      rw [cechStructureMap_one_tmul, cechStructureMap_one_tmul]
      exact (cechStructureMap_transitionBase D γ.unop.unop _ x.down).symm)

private noncomputable def cechModuleFunctor :
    DescentData.{u, v, w} R A ⥤ CechModule.{u, v, w} R A where
  obj := cechModuleOfDatum
  map g := PresheafOfModulesOfCommRing.homMk
    (fun n => cechDegreeMap R A g n.unop.unop (Fin.last n.unop.unop.len))
    (fun β => (cechStructureMap_natural g β.unop.unop).symm)
  map_id D := by
    apply PresheafOfModules.Hom.ext
    funext n
    exact cechDegreeMap_id R A D n.unop.unop (Fin.last n.unop.unop.len)
  map_comp g h := by
    apply PresheafOfModules.Hom.ext
    funext n
    exact cechDegreeMap_comp R A g h n.unop.unop (Fin.last n.unop.unop.len)

variable (R A)

/-- The transition map `φⁿ_{ij}` carries the generator of `x` to `φ(x ⊗ 1)`. -/
public theorem cechTransitionMap_generator
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) (x : restrictModule R A D.module) :
    (cechTransitionMap D n i j).hom (cechGenerator R A D.module n i x) =
      transitionBase D n i j x :=
  (congrArg (cechTransitionMap D n i j).hom
      (cechGenerator_eq_tmul R A D.module n i x)).trans
    (cechTransitionMap_one_tmul D n i j (ULift.up (x : D.module)))

/-- The semilinear map `N_{β, i}` fixes the generators. -/
public theorem cechSemilinearMap_generator (N : ModuleCat.{w} A)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1))
    (x : restrictModule R A N) :
    (cechSemilinearMap R A N β i).hom (cechGenerator R A N n i x) =
      cechGenerator R A N m (β.toOrderHom i) x :=
  (congrArg (cechSemilinearMap R A N β i).hom
      (cechGenerator_eq_tmul R A N n i x)).trans
    (cechSemilinearMap_one_tmul N β i (ULift.up (x : N)))

/-- The structure map `N_•(β)` carries the generator of `x` in the last position to the
transition of `x` from `β(n)` to the last position in degree `m`. -/
public theorem cechStructureMap_generator
    (D : DescentData.{u, v, w} R A) {n m : SimplexCategory} (β : n ⟶ m)
    (x : restrictModule R A D.module) :
    (cechStructureMap D β).hom (cechGenerator R A D.module n (Fin.last n.len) x) =
      transitionBase D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len) x :=
  (congrArg (cechStructureMap D β).hom
      (cechGenerator_eq_tmul R A D.module n (Fin.last n.len) x)).trans
    (cechStructureMap_one_tmul D β (ULift.up (x : D.module)))

/-- The defining specification of the cosimplicial module of a descent datum: a
functor `F` satisfies it when, for every descent datum `(N, φ)`, its degree-`n`
module is `N_n = N_{n, n}` and its structure map in `β : [n] → [m]` is
`N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n}`. -/
public def IsDescentCosimplicialModuleFunctor
    (F : DescentData.{u, v, w} R A ⥤ CechModule.{u, v, w} R A) : Prop :=
  ∃ h : ∀ (D : DescentData.{u, v, w} R A) (n : SimplexCategory),
      (F.obj D).obj (op (op n)) = cechDegreeObj R A D.module n (Fin.last n.len),
    (∀ (D : DescentData.{u, v, w} R A) {n m : SimplexCategory} (β : n ⟶ m),
      (F.obj D).map β.op.op =
        eqToHom (h D n) ≫ cechStructureMap D β ≫
          eqToHom (congrArg ((ModuleCat.restrictScalars (cechRingMap R A β)).obj)
            (h D m).symm)) ∧
      (∀ {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
        (n : SimplexCategory),
        ((F.map g).app (op (op n))) =
          eqToHom (h D n) ≫ cechDegreeMap R A g n (Fin.last n.len) ≫
            eqToHom (h E n).symm)

/-- **Stacks Lemma 023H.** To a descent datum `(N, φ)` one can associate a
cosimplicial module over the Čech algebra `(A / R)_•` by the rules
`N_n = N_{n, n}` and `N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n}`, functorially in the
descent datum. -/
@[stacks 023H]
public theorem exists_descentCosimplicialModuleFunctor :
    ∃ F : DescentData.{u, v, w} R A ⥤ CechModule.{u, v, w} R A,
      IsDescentCosimplicialModuleFunctor R A F := by
  refine ⟨cechModuleFunctor, (fun _ _ => rfl), ?_, ?_⟩
  · intro D n m β
    change cechStructureMap D β = 𝟙 _ ≫ cechStructureMap D β ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro D E g n
    change cechDegreeMap R A g n (Fin.last n.len) =
      𝟙 _ ≫ cechDegreeMap R A g n (Fin.last n.len) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

/-- The functor which associates to a descent datum `(N, φ)` its cosimplicial
module over the Čech algebra `(A / R)_•`.  It is characterised by
`descentCosimplicialModuleFunctor_obj` and
`descentCosimplicialModuleFunctor_map`. -/
@[stacks 023H]
public noncomputable def descentCosimplicialModuleFunctor :
    DescentData.{u, v, w} R A ⥤ CechModule.{u, v, w} R A :=
  (exists_descentCosimplicialModuleFunctor R A).choose

/-- The degree-`n` module of the cosimplicial module of a descent datum `(N, φ)`
is `N_n = N_{n, n}`. -/
public theorem descentCosimplicialModuleFunctor_obj
    (D : DescentData.{u, v, w} R A) (n : SimplexCategory) :
    ((descentCosimplicialModuleFunctor R A).obj D).obj (op (op n)) =
      cechDegreeObj R A D.module n (Fin.last n.len) :=
  (exists_descentCosimplicialModuleFunctor R A).choose_spec.choose D n

/-- The structure map in `β : [n] → [m]` of the cosimplicial module of a descent
datum `(N, φ)` is `N_•(β) = φᵐ_{β(n), m} ∘ N_{β, n}`. -/
public theorem descentCosimplicialModuleFunctor_map
    (D : DescentData.{u, v, w} R A) {n m : SimplexCategory} (β : n ⟶ m) :
    ((descentCosimplicialModuleFunctor R A).obj D).map β.op.op =
      eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫ cechStructureMap D β ≫
        eqToHom (congrArg ((ModuleCat.restrictScalars (cechRingMap R A β)).obj)
          (descentCosimplicialModuleFunctor_obj R A D m).symm) :=
  (exists_descentCosimplicialModuleFunctor R A).choose_spec.choose_spec.1 D β

/-- In every degree a morphism of descent data acts by extension of its
underlying module map, hence by identity on the Čech-algebra factors. -/
public theorem descentCosimplicialModuleFunctor_map_hom
    {D E : DescentData.{u, v, w} R A} (g : D ⟶ E)
    (n : SimplexCategory) :
    (((descentCosimplicialModuleFunctor R A).map g).app (op (op n))) =
      eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫
        cechDegreeMap R A g n (Fin.last n.len) ≫
          eqToHom (descentCosimplicialModuleFunctor_obj R A E n).symm :=
  (exists_descentCosimplicialModuleFunctor R A).choose_spec.choose_spec.2 g n

/-- Every transition map `φⁿ_{ij}` of a descent datum is an isomorphism: `φⁿ_{ji}` is a
two-sided inverse, by the identity `φⁿ_{jk} ∘ φⁿ_{ij} = φⁿ_{ik}` and `φⁿ_{ii} = id`. -/
public theorem isIso_cechTransitionMap (D : DescentData.{u, v, w} R A) (n : SimplexCategory)
    (i j : Fin (n.len + 1)) :
    IsIso (cechTransitionMap D n i j) :=
  ⟨⟨cechTransitionMap D n j i,
    (cechTransitionMap_comp D n i j i).trans (cechTransitionMap_self D n i),
    (cechTransitionMap_comp D n j i j).trans (cechTransitionMap_self D n j)⟩⟩

/-- The adjoint transpose of the semilinear map `N_{β, i}` is an isomorphism:
`N_{β, i}` fixes the generators, so its transpose is the comparison identifying the extension
of scalars along the `i`-th leg in degree `n` followed by `(A/R)_•(β)` with the extension along
the `β(i)`-th leg in degree `m`. -/
public theorem isIso_cechSemilinearBaseChange (N : ModuleCat.{w} A)
    {n m : SimplexCategory} (β : n ⟶ m) (i : Fin (n.len + 1)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj (cechRingMap R A β)).homEquiv
          (cechDegreeObj R A N n i) (cechDegreeObj R A N m (β.toOrderHom i))).symm
        (cechSemilinearMap R A N β i)) :=
  isIso_extendScalarsCompTranspose (cechLeg R A n i) (cechRingMap R A β)
    (cechLeg R A m (β.toOrderHom i)) (cechRingMap_comp_cechLeg R A β i).symm
    (liftedModule A N)

/-- **The cosimplicial module of a descent datum is cartesian.**  For every `β : [n] → [m]`
the structure map `N_•(β)` induces an isomorphism `N_n ⊗_{(A/R)ₙ, (A/R)_•(β)} (A/R)ₘ ⟶ N_m`:
it is the transpose of `N_{β, n}`, which is the comparison of a two-step extension of scalars,
followed by the transition map `φᵐ_{β(n), m}`, which is invertible. -/
public theorem cartesian_descentCosimplicialModuleFunctor_obj
    (D : DescentData.{u, v, w} R A) :
    CategoryTheory.CosimplicialModule.Cartesian
      ((descentCosimplicialModuleFunctor R A).obj D) := by
  intro n m β
  have h1 : ((descentCosimplicialModuleFunctor R A).obj D).map β.op.op =
      eqToHom (descentCosimplicialModuleFunctor_obj R A D n) ≫
        (cechSemilinearMap R A D.module β (Fin.last n.len) ≫
          (ModuleCat.restrictScalars (cechRingMap R A β)).map
            (cechTransitionMap D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len))) ≫
        (ModuleCat.restrictScalars (cechRingMap R A β)).map
          (eqToHom (descentCosimplicialModuleFunctor_obj R A D m).symm) := by
    rw [descentCosimplicialModuleFunctor_map R A D β, eqToHom_map]
    rfl
  change IsIso (((ModuleCat.extendRestrictScalarsAdj (cechRingMap R A β)).homEquiv _ _).symm
    (((descentCosimplicialModuleFunctor R A).obj D).map β.op.op))
  rw [h1, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_right_symm]
  have := isIso_cechSemilinearBaseChange R A D.module β (Fin.last n.len)
  have := isIso_cechTransitionMap R A D m (β.toOrderHom (Fin.last n.len)) (Fin.last m.len)
  infer_instance

/-- The functor from descent data for `A / R` to **cartesian** cosimplicial modules over the
Čech algebra `(A / R)_•`: the cosimplicial module of a descent datum, carrying the cartesian
property established by `cartesian_descentCosimplicialModuleFunctor_obj`. -/
public noncomputable def descentCartesianModuleFunctor :
    DescentData.{u, v, w} R A ⥤ CartesianCechModule.{u, v, w} R A :=
  CategoryTheory.ObjectProperty.lift _ (descentCosimplicialModuleFunctor R A)
    (cartesian_descentCosimplicialModuleFunctor_obj R A)

section LowDegrees

/-- **`(A / R)₀ ≅ A`.**  The Čech algebra of `R → A` in degree `0` is the lifted algebra
itself, by `Stacks.Descent.cechDegZeroIso`. -/
public noncomputable def cechAlgebraDegZeroIso :
    (cechCosimplicialAlgebra R A).obj (SimplexCategory.mk 0) ≅
      (AlgebraicTopology.algebraMapArrow R A).right :=
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  Stacks.Descent.cechDegZeroIso (ULift.{v} R) (ULift.{u} A)

/-- **The unique leg `A → (A / R)₀` is an isomorphism.** -/
public theorem isIso_cechLegHom_degZero :
    IsIso (cechLegHom R A (SimplexCategory.mk 0) 0) :=
  let : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  ⟨⟨(Stacks.Descent.cechDegZeroIso (ULift.{v} R) (ULift.{u} A)).hom,
    (Stacks.Descent.cechDegZeroIso (ULift.{v} R) (ULift.{u} A)).inv_hom_id,
    (Stacks.Descent.cechDegZeroIso (ULift.{v} R) (ULift.{u} A)).hom_inv_id⟩⟩

/-- **`(A / R)₁ ≅ A ⊗_R A`.**  The Čech algebra of `R → A` in degree `1` is the tensor square
of the lifted algebra, by `Stacks.Descent.cechDegOneIso`. -/
public noncomputable def cechAlgebraDegOneIso :
    (cechCosimplicialAlgebra R A).obj (SimplexCategory.mk 1) ≅
      letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
      Stacks.Descent.cechSquare (ULift.{v} R) (ULift.{u} A) :=
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  Stacks.Descent.cechDegOneIso (ULift.{v} R) (ULift.{u} A)

/-- **`(A / R)₂ ≅ A ⊗_R A ⊗_R A`.**  The Čech algebra of `R → A` in degree `2` is the tensor
cube of the lifted algebra, by `Stacks.Descent.cechDegTwoIso`. -/
public noncomputable def cechAlgebraDegTwoIso :
    (cechCosimplicialAlgebra R A).obj (SimplexCategory.mk 2) ≅
      letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
      Stacks.Descent.cechCube (ULift.{v} R) (ULift.{u} A) :=
  letI : Algebra (ULift.{v} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  Stacks.Descent.cechDegTwoIso (ULift.{v} R) (ULift.{u} A)

end LowDegrees

end ModuleCat

end
