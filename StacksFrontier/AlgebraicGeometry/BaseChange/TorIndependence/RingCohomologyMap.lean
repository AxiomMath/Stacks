module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.Independence

/-!
# The base-change map on cohomology of a commutative square of rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings, `K` an
object of `D(A)` and `K'` an object of `D(A')`. The cohomology of the derived base change
`K ⊗ᴸ_R R'`, taken over `R'`, carries a canonical action of the ordinary tensor product
`A ⊗_R R'`: the right factor acts by the `R'`-structure already present and the left factor acts
through base change of scalar multiplication on `K`. A morphism
`φ : K ⊗ᴸ_A A' ⟶ K'` then induces a unique `A'`-linear map

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

whose value on `1 ⊗ m` is prescribed by the comparison of Stacks 065Z followed by `φ`. This is
the ring-level content of Stacks 0DJ7; the geometric statement reads it at the stalks of a
commutative square of schemes.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologyOverBase`: the cohomology of the derived base
  change, as an `R'`-module.
* `RingTheory.TorIndependence.baseChangeCohomology`: the same abelian group as a module over
  `A ⊗_R R'`.

## Main results

* `RingTheory.TorIndependence.exists_unique_baseChangeCohomologyModule`: the `A ⊗_R R'`-action is
  the unique one restricting to the given `R'`-action and to the given action of `A`.
* `RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul` and
  `RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`: the two restrictions.
* `RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap`: the base-change map,
  characterized by its values on pure tensors `1 ⊗ m`.

## Implementation notes

The cohomology module is not replaced by an isomorphic copy: `baseChangeCohomology` is the
*same* object as `baseChangeCohomologyOverBase` with one further action installed, so the
`R'`-module structure a consumer already has is the restriction of the `A ⊗_R R'`-structure
along `Algebra.TensorProduct.includeRight` rather than something to be transported.

Extension of scalars puts the new ring on the left of the tensor product, which interchanges the
two factors against the displayed formula of the source.

The model of the derived category is free: every statement below takes
`[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for each of the four rings as a binder rather than
fixing `HasDerivedCategory.standard`. A statement proved for one model says nothing about
another, the two derived categories being merely equivalent and not equal, and both the locally
small model with morphisms in `Type u` and the standard model with morphisms in `Type (u + 1)`
are wanted here.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

/-! ### Scalar multiplication through derived functors -/

/-- A left derived functor inherits a scalar action on identities from the functor it derives:
if `F` carries `r • 𝟙 X` to `s • 𝟙 (F X)` for every `X`, so does any left derived functor of
`F`.

The two sides are the two whiskerings of the central elements `r` and `s`, and a natural
transformation between left derived functors is determined by its restriction along `L`. -/
private lemma leftDerived_scalar
    {R S C D H : Type*} [Ring R] [Ring S]
    [Category C] [Category D] [Category H]
    [Preadditive C] [Preadditive D] [Preadditive H]
    [Linear R C] [Linear R D] [Linear S H]
    (L : C ⥤ D) [L.Linear R] (W : MorphismProperty C) [L.IsLocalization W]
    (F : C ⥤ H) (LF : D ⥤ H) (α : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor α W] (r : R) (s : S)
    (h : ∀ Z, F.map (r • 𝟙 Z) = s • 𝟙 (F.obj Z)) (Z : D) :
    LF.map (r • 𝟙 Z) = s • 𝟙 (LF.obj Z) := by
  have he : Functor.whiskerRight (Linear.toCatCenter R D r).asHom LF =
      (Functor.whiskerLeft LF (Linear.toCatCenter S H s).asHom : LF ⋙ 𝟭 H ⟶ LF ⋙ 𝟭 H) := by
    apply LF.leftDerived_ext α W LF
    ext W'
    change LF.map (r • 𝟙 (L.obj W')) ≫ α.app W' = (s • 𝟙 (LF.obj (L.obj W'))) ≫ α.app W'
    rw [← L.map_id, ← L.map_smul]
    change (L ⋙ LF).map (r • 𝟙 W') ≫ α.app W' = _
    rw [α.naturality, h]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id]
  exact congrArg (fun γ => γ.app Z) he

/-- Extension of scalars along `f` carries multiplication by `r` to multiplication by `f r`. -/
private lemma extendScalars_scalar {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).map (r • 𝟙 M) = f r • 𝟙 ((ModuleCat.extendScalars f).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  let := f.toAlgebra
  change (1 : S) ⊗ₜ[R] (r • m) = (f r * 1) ⊗ₜ[R] m
  rw [mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one]

/-- Derived extension of scalars along `f` carries multiplication by `r` to multiplication by
`f r`. -/
theorem derivedExtension_scalar {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (f : R →+* S) (r : R) (K : DerivedCategory (ModuleCat.{u} R)) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor.map
      (r • 𝟙 K) = f r • 𝟙 _ := by
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  apply leftDerived_scalar DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ T.functor T.comparison
    r (f r) _ K
  intro P
  change DerivedCategory.Q.map
    (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 P)) = _
  rw [show ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (r • 𝟙 P) = f r • 𝟙 _ from
        HomologicalComplex.hom_ext _ _ fun i => extendScalars_scalar f r (P.X i),
    Functor.map_smul, DerivedCategory.Q.map_id]
  rfl

/-- An exact additive functor between abelian categories, linear over possibly different rings,
carries multiplication by `r` on the derived category to multiplication by `s`, as soon as it
does so on the underlying categories. -/
private lemma exactFunctor_scalar
    {R S C D : Type*} [Ring R] [Ring S]
    [Category C] [Category D] [Abelian C] [Abelian D]
    [Linear R C] [Linear S D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (r : R) (s : S) (h : ∀ M, F.map (r • 𝟙 M) = s • 𝟙 (F.obj M))
    (K : DerivedCategory C) : F.mapDerivedCategory.map (r • 𝟙 K) = s • 𝟙 _ := by
  have he : Functor.whiskerRight (Linear.toCatCenter R (DerivedCategory C) r).asHom
        F.mapDerivedCategory =
      (Functor.whiskerLeft F.mapDerivedCategory (Linear.toCatCenter S (DerivedCategory D) s).asHom :
        F.mapDerivedCategory ⋙ 𝟭 _ ⟶ F.mapDerivedCategory ⋙ 𝟭 _) := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    intro P
    change F.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj P)) = s • 𝟙 _
    apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
    rw [← DerivedCategory.Q.map_id, ← DerivedCategory.Q.map_smul]
    change (DerivedCategory.Q ⋙ F.mapDerivedCategory).map (r • 𝟙 P) ≫ _ = _
    rw [F.mapDerivedCategoryFactors.hom.naturality]
    change _ ≫ DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 P)) = _
    rw [show (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (r • 𝟙 P) = s • 𝟙 _ from
      HomologicalComplex.hom_ext _ _ fun i => h (P.X i), Functor.map_smul, DerivedCategory.Q.map_id]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id]
  exact congrArg (fun γ => γ.app K) he

/-! ### The module structure over the ordinary tensor product -/

/-- In `A ⊗_R S` a pure tensor is the product of the two inclusions. -/
private lemma tmul_eq_includeLeft_mul_includeRight
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (a : A) (s : S) :
    (a ⊗ₜ[R] s : A ⊗[R] S) =
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) *
        Algebra.TensorProduct.includeRight s := by
  change a ⊗ₜ[R] s = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] s)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- An `S`-module with a compatible ring action of `A` carries exactly one `A ⊗_R S`-module
structure restricting to the two given actions. -/
private lemma tensorModule_of_scalarAction
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (H : ModuleCat.{u} S)
    (ρ : A →+* Module.End S H)
    (hρ : ∀ r : R, ρ (algebraMap R A r) = algebraMap R S r • (1 : Module.End S H)) :
    ∃! M : Module (A ⊗[R] S) H,
      letI := M
      (∀ (r : S) (m : H), (Algebra.TensorProduct.includeRight r : A ⊗[R] S) • m = r • m) ∧
      (∀ (a : A) (m : H),
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) • m = ρ a m) := by
  let : Module R H := Module.compHom H (algebraMap R S)
  let : IsScalarTower R S H := IsScalarTower.of_compHom _ _ _
  let : Module A H := Module.compHom H ρ
  let : IsScalarTower R A H := by
    constructor
    intro r a m
    change ρ (r • a) m = algebraMap R S r • ρ a m
    rw [Algebra.smul_def, map_mul, hρ]
    rfl
  let : SMulCommClass A S H := ⟨fun a r m => (ρ a).map_smul r m⟩
  let M : Module (A ⊗[R] S) H := TensorProduct.Algebra.module
  let := M
  refine ⟨M, ⟨?_, ?_⟩, ?_⟩
  · intro r m
    change (1 : A) • r • m = r • m
    exact one_smul _ _
  · intro a m
    change ρ a ((1 : S) • m) = ρ a m
    rw [one_smul]
  · intro M' hM'
    refine Module.ext' M' M fun t m => ?_
    induction t using TensorProduct.induction_on with
    | zero => exact (M'.zero_smul m).trans (M.zero_smul m).symm
    | add x y hx hy =>
      exact (M'.add_smul x y m).trans
        ((congrArg₂ (· + ·) hx hy).trans (M.add_smul x y m).symm)
    | tmul a b =>
      calc
        (letI := M'; (a ⊗ₜ[R] b) • m) =
            (letI := M';
              (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] S) •
                ((Algebra.TensorProduct.includeRight b : A ⊗[R] S) • m)) := by
                  let := M'
                  rw [tmul_eq_includeLeft_mul_includeRight a b, mul_smul]
        _ = ρ a (b • m) := by rw [hM'.1, hM'.2]
        _ = _ := rfl

/-! ### Cohomology of the derived base change -/

/-- The `n`-th cohomology of the derived base change of `K` from `R` to `R'`, as an
`R'`-module. The object of `D(A)` is first read over `R`, then base changed. -/
abbrev baseChangeCohomologyOverBase
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.{u} R' :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K))

/-- **The tensor-product action on the cohomology of a derived base change is unique.** It is
pinned by the `R'`-action already present and by the endomorphisms induced by scalar
multiplication on `K`. -/
theorem exists_unique_baseChangeCohomologyModule
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')
    ∃! M : Module (A ⊗[R] R') H,
      letI := M
      (∀ (r : R') (m : H), (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m = r • m) ∧
      (∀ (a : A) (m : H),
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            (T.functor.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
              (a • (𝟙 K))))).hom m) := by
  dsimp only
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R R')
  let G := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
    T.functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let ρ : A →+* Module.End R' H :=
    { toFun := fun a => (G.map (a • (𝟙 K))).hom
      map_one' := by
        rw [one_smul, G.map_id]
        rfl
      map_mul' := fun a b => by
        have hab : (a * b) • (𝟙 K) = (b • (𝟙 K)) ≫ (a • (𝟙 K)) := by
          simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
        rw [hab, G.map_comp]
        rfl
      map_zero' := by
        rw [zero_smul, G.map_zero]
        rfl
      map_add' := fun a b => by
        rw [add_smul, G.map_add]
        rfl }
  have hρ : ∀ r : R, ρ (algebraMap R A r) = algebraMap R R' r • (1 : Module.End R' H) := by
    intro r
    have hres := exactFunctor_scalar (ModuleCat.restrictScalars (algebraMap R A))
      (algebraMap R A r) r (fun M => by ext m; rfl) K
    let := DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} R') R' n
    change ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      (T.functor.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
        (algebraMap R A r • 𝟙 K)))).hom = _
    rw [hres, derivedExtension_scalar, Functor.map_smul,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map_id]
    rfl
  exact tensorModule_of_scalarAction H ρ hρ

/-- **The cohomology of a derived base change as a module over the ordinary tensor product.**
The underlying additive group is unchanged; only the action is new. -/
def baseChangeCohomology
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.{u} (A ⊗[R] R') :=
  letI := Classical.choose
    (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).exists
  ModuleCat.of (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n)

/-- The right tensor factor acts on `baseChangeCohomology` by the base-change scalar action it
already had. -/
theorem baseChangeCohomology_includeRight_smul
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (r : R') (m : baseChangeCohomology (R := R) (R' := R') K n) :
    (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m =
      r • (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m) := by
  let P := exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n
  let := Classical.choose P.exists
  exact (Classical.choose_spec P.exists).1 r m

/-- The left tensor factor acts on `baseChangeCohomology` by derived base change of scalar
multiplication on `K`. -/
theorem baseChangeCohomology_includeLeft_smul
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (a : A) (m : baseChangeCohomology (R := R) (R' := R') K n) :
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (T.functor.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
          (a • (𝟙 K))))).hom m := by
  let P := exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n
  let := Classical.choose P.exists
  exact (Classical.choose_spec P.exists).2 a m

/-! ### The base-change map on cohomology -/

/-- **The base-change map on cohomology, Stacks 0DJ7 at the level of rings.** For a commutative
square of commutative rings and a morphism `φ : K ⊗ᴸ_A A' ⟶ K'`, there is exactly one
`A'`-linear map

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

whose value on `1 ⊗ m` is the comparison of Stacks 065Z followed by `φ`, read through the
identification of cohomology with restriction of scalars. -/
theorem exists_unique_ringBaseChangeCohomologyMap
    {R A R' A' : Type u}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A']
    [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K')
    (n : ℤ) :
    let f : R →+* A := algebraMap R A
    let g : R →+* R' := algebraMap R R'
    let h : A →+* A' := algebraMap A A'
    let i : R' →+* A' := algebraMap R' A'
    let sq : h.comp f = i.comp g :=
      (IsScalarTower.algebraMap_eq R A A').symm.trans (IsScalarTower.algebraMap_eq R R' A')
    let B := A ⊗[R] R'
    let k : B →+* A' :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
        (IsScalarTower.toAlgHom R R' A') (fun _ _ ↦ Commute.all _ _)).toRingHom
    let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
    let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
    have _ := Tg.isLeftDerived
    have _ := Th.isLeftDerived
    let τ := (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w}
      R A R' A' _ _ _ _ _ _ _ _ f g h i sq
      Tg.functor Th.functor Tg.comparison Th.comparison
      Tg.isLeftDerived Th.isLeftDerived).2.1
    let H := baseChangeCohomology (R := R) (R' := R') K n
    let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
    let e' := ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).app K'
    ∃! b : (ModuleCat.extendScalars k).obj H ⟶ H',
      ∀ m : H,
        b.hom ((1 : A') ⊗ₜ[B, k] m) =
          e'.hom.hom (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
            (τ.app K ≫ (ModuleCat.restrictScalars i).mapDerivedCategory.map φ)).hom m) := by
  intro f g h i sq B k Tg Th _ _ τ H H' e'
  let C := (ModuleCat.restrictScalars i).mapDerivedCategory
  let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let α := τ.app K ≫ C.map φ
  let q := J.map α ≫ e'.hom
  have hqa (a : A) (m : H) :
      q.hom ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : B) • m) =
        h a • (show H' from q.hom m) := by
    have hφ : Th.functor.map (a • 𝟙 K) ≫ φ = φ ≫ (h a • 𝟙 K') := by
      rw [derivedExtension_scalar]
      change (h a • 𝟙 (Th.functor.obj K)) ≫ φ = φ ≫ (h a • 𝟙 K')
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    have hd : ((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
        (a • 𝟙 K) ≫ α = α ≫ C.map (h a • 𝟙 K') := by
      dsimp only [α]
      rw [← Category.assoc, τ.naturality]
      change (τ.app K ≫ C.map (Th.functor.map (a • 𝟙 K))) ≫ C.map φ = _
      rw [Category.assoc, ← C.map_comp, hφ, C.map_comp, Category.assoc]
    have hn := ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.naturality
      (h a • 𝟙 K')
    let _ := DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A') A' n
    have hnat : J.map (((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
        (a • 𝟙 K)) ≫ q = q ≫ (ModuleCat.restrictScalars i).map (h a • 𝟙 H') := by
      dsimp only [q]
      rw [← Category.assoc, ← J.map_comp, hd, J.map_comp, Category.assoc]
      change _ ≫ ((((ModuleCat.restrictScalars i).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (h a • 𝟙 K')) ≫
          ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.app K') = _
      rw [hn]
      dsimp only [Functor.comp_map]
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      exact (Category.assoc _ _ _).symm
    rw [baseChangeCohomology_includeLeft_smul]
    exact congrArg (fun l => l.hom m) hnat
  have hqr (r : R') (m : H) :
      q.hom ((Algebra.TensorProduct.includeRight r : B) • m) = i r • (show H' from q.hom m) := by
    rw [baseChangeCohomology_includeRight_smul]
    exact q.hom.map_smul r m
  let l : H ⟶ (ModuleCat.restrictScalars k).obj H' :=
    ModuleCat.ofHom (X := H) (Y := (ModuleCat.restrictScalars k).obj H')
      (show H →ₗ[B] ((ModuleCat.restrictScalars k).obj H') from
        { toFun := fun m => q.hom m
          map_add' := fun x y => q.hom.map_add x y
          map_smul' := fun t m => by
            change q.hom (t • m) = k t • (show H' from q.hom m)
            induction t using TensorProduct.induction_on with
            | zero =>
              rw [zero_smul, k.map_zero]
              exact q.hom.map_zero.trans (zero_smul A' (show H' from q.hom m)).symm
            | add x y hx hy =>
              rw [add_smul, k.map_add]
              exact (q.hom.map_add _ _).trans
                ((congrArg₂ (· + ·) hx hy).trans
                  (add_smul (k x) (k y) (show H' from q.hom m)).symm)
            | tmul a r =>
              rw [tmul_eq_includeLeft_mul_includeRight a r, mul_smul, hqa, hqr, ← mul_smul,
                ← tmul_eq_includeLeft_mul_includeRight a r]
              rfl })
  let adj := ModuleCat.extendRestrictScalarsAdj k
  let b := (adj.homEquiv H H').symm l
  have hb (m : H) : b.hom ((1 : A') ⊗ₜ[B, k] m) = q.hom m :=
    (congrArg (fun l => l.hom m) (adj.homEquiv_unit (f := b))).symm.trans
      (congrArg (fun l => l.hom m) ((adj.homEquiv H H').apply_symm_apply l))
  exact ⟨b, hb, fun b' hb' => ModuleCat.ExtendScalars.hom_ext fun m => (hb' m).trans (hb m).symm⟩

end RingTheory.TorIndependence

end
