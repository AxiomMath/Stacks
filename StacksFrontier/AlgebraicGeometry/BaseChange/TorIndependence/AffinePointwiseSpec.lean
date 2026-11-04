module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseTildeStalk
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineSpecComposition
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkLocalization

/-!
# Stacks 0DJ9 over a pushout square of rings

For a pushout square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'`, a K-flat complex `M` of
`A`-modules, a complex `N` of `A'`-modules and `ψ₀ : A' ⊗_A M ⟶ N`, if the map of Stacks 0DJ7 of
the square of spectra at the datum attached to `ψ₀` is invertible at every point and in every
degree, then the composition `Lg^*Rf_*M̃ ⟶ Rf'_*L(g')^*M̃ ⟶ Rf'_*Ñ` is an isomorphism.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_comp_specMap_of_pointwise`: if the map of Stacks 0DJ7
  is invertible at every point and in every degree, the composition above is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingTheory.TorIndependence

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- For a ring map `f : R ⟶ S` and `p ∈ Spec S`, the composite of `R ⟶ 𝒪_{Spec R, f(p)}` with the
stalk map of `Spec f` at `p` equals `R ⟶ S ⟶ 𝒪_{Spec S, p}`. -/
theorem specStalkMap_toStalk {R S : CommRingCat.{u}} (f : R ⟶ S) (p : Spec S) :
    StructureSheaf.toStalk R ((Spec.map f) p) ≫ (Spec.map f).stalkMap p =
      f ≫ StructureSheaf.toStalk S p :=
  stalkMap_toStalk f p

/-- For `p = q` in `Spec R`, the map `R ⟶ 𝒪_{Spec R, p}` followed by the identification of stalks
`𝒪_{Spec R, p} ≅ 𝒪_{Spec R, q}` is the map `R ⟶ 𝒪_{Spec R, q}`. -/
theorem stalkCongr_toStalk {R : CommRingCat.{u}} {p q : Spec R} (h : p = q) :
    StructureSheaf.toStalk R p ≫ ((Spec R).presheaf.stalkCongr (.of_eq h)).hom =
      StructureSheaf.toStalk R q := by
  subst h
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact Category.comp_id _

/-- The stalk of `Spec S` at `z` is the localization of `S` at the prime of `z`. -/
private theorem isLocalization_atPrime_toStalk {S : CommRingCat.{u}} (z : Spec S) :
    letI : Algebra S ((Spec S).presheaf.stalk z) := (StructureSheaf.toStalk S z).hom.toAlgebra
    haveI := z.isPrime
    IsLocalization.AtPrime ((Spec S).presheaf.stalk z) z.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk S z

variable {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'}

/-- **The datum of a map of complexes, on stalks**: the stalk at `q` of the composite
`(Spec c)^* M̃ ≅ (A' ⊗_A M)~ ⟶ Ñ` carries the germ of `m` to the germ of `ψ₀(1 ⊗ m)`. -/
theorem pullbackStalk_tildeMap_germ (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N)
    (q : Spec A') (p : ℤ) (m : M.X p) :
    ((((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso (Spec.map c) q)
        (ComplexShape.up ℤ)).hom.app (((tilde.functor A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)) ≫
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A') q).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((AlgebraicGeometry.tildePullbackComplexIso A A'
          c).hom.app M ≫ ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀)).f
          p).hom ((1 : (Spec A').presheaf.stalk q) ⊗ₜ[(Spec A).presheaf.stalk ((Spec.map c) q),
            ((Spec.map c).stalkMap q).hom] ((tildeStalkMap M ((Spec.map c) q)).f p).hom m) =
      ((tildeStalkMap N q).f p).hom ((ψ₀.f p).hom ((1 : A') ⊗ₜ[A, c.hom] m)) := by
  let θ := (AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
    ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀
  refine (congrArg (fun z => ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A') q).map
    (θ.f p)).hom z) (Stacks.ModuleSkyscraper.pullbackStalkIso_hom_app_one_tmul (Spec.map c) q
      (tilde (M.X p)) ⊤ trivial (tilde.toOpen (M.X p) ⊤ m))).trans ?_
  refine (Stacks.ModuleSkyscraper.stalkMapLinear_germ ((SheafOfModules.forget _).map (θ.f p)) q
    ((Spec.map c) ⁻¹ᵁ ⊤) trivial _).trans ?_
  have hθ : θ.f p = (pullbackTildeIso A A' c).hom.app (M.X p) ≫ tilde.map (ψ₀.f p) := by
    simp only [θ, HomologicalComplex.comp_f,
      AlgebraicGeometry.StandardModel.tildePullbackComplexIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f]
    rfl
  rw [hθ]
  show (tilde (N.X p)).presheaf.germ ⊤ q trivial
    ((((pullbackTildeIso A A' c).hom.app (M.X p)).val.app (Opposite.op ⊤) ≫
        (tilde.map (ψ₀.f p)).val.app (Opposite.op ⊤)).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map c)).unit.app
          (tilde (M.X p))).val.app (Opposite.op ⊤)) (tilde.toOpen (M.X p) ⊤ m))) =
    (tilde (N.X p)).presheaf.germ ⊤ q trivial (tilde.toOpen (N.X p) ⊤ ((ψ₀.f p).hom
      ((1 : A') ⊗ₜ[A, c.hom] m)))
  exact congrArg (fun z => (tilde (N.X p)).presheaf.germ ⊤ q trivial z)
    ((congrArg (fun z => ((tilde.map (ψ₀.f p)).val.app (Opposite.op ⊤)).hom z)
      (pullbackTildeIso_hom_app_unit_toOpen A A' c (M.X p) m)).trans
      (congrArg (fun φ => φ.hom ((1 : A') ⊗ₜ[A, c.hom] m)) (tilde.toOpen_map_app (ψ₀.f p) ⊤)))

/-- The map `B ⊗_A X ⟶ Y` adjoint to `g : X ⟶ Y` carries `1 ⊗ m` to `g(m)`. -/
theorem fromExtendScalars_one_tmul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B} (g : X ⟶ (ModuleCat.restrictScalars f).obj Y)
    (m : X) :
    (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g).hom
      ((1 : B) ⊗ₜ[A, f] m) = g.hom m :=
  congrArg (fun h => h.hom m) ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv f).apply_symm_apply g)

/-- The map of complexes `B ⊗_A M ⟶ Z`, `b ⊗ m ↦ b • κ(m)`, attached to a map `κ : M ⟶ Z` over
`A ⟶ B`. -/
def extendScalarsLift {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : CochainComplex (ModuleCat.{u} A) ℤ} {Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (κ : M ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ Z where
  f i := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f (κ.f i)
  comm' i j _ := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    change (Z.d i j).hom (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f (κ.f i)
      |>.hom ((1 : B) ⊗ₜ[A, f] m)) = (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        f (κ.f j)).hom ((1 : B) ⊗ₜ[A, f] (M.d i j).hom m)
    rw [fromExtendScalars_one_tmul, fromExtendScalars_one_tmul]
    exact congrArg (fun φ => φ.hom m) (κ.comm i j)

/-- In degree `i`, the map `extendScalarsLift f κ` carries `1 ⊗ m` to `κ(m)`. -/
theorem extendScalarsLift_f_one_tmul {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    {M : CochainComplex (ModuleCat.{u} A) ℤ} {Z : CochainComplex (ModuleCat.{u} B) ℤ}
    (κ : M ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
    (i : ℤ) (m : M.X i) :
    ((extendScalarsLift f κ).f i).hom ((1 : B) ⊗ₜ[A, f] m) = (κ.f i).hom m :=
  fromExtendScalars_one_tmul f (κ.f i) m

/-- **Stacks 0DJ9 over a pushout square of rings.**  If the map of Stacks 0DJ7 of the square of
spectra at the datum of `ψ₀ : A' ⊗_A M ⟶ N` is invertible at every point and in every degree, the
composition `Lg^*Rf_*M̃ ⟶ Rf'_*L(g')^*M̃ ⟶ Rf'_*Ñ` is an isomorphism. -/
theorem isIso_comp_specMap_of_pointwise (h : IsPushout a b c d)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : CochainComplex.KFlat.{u, u} M)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N)
    (hp : ∀ (x' : Spec A') (n : ℤ), IsIso (baseChangeCohomologyMap (Spec.map a) (Spec.map b)
      (Spec.map d) (Spec.map c) (isPullback_specMap h).w
      (DerivedCategory.Q.obj (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
      (DerivedCategory.Q.obj (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N))
      (pullbackComparisonOnComplex (Spec.map c)
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((AlgebraicGeometry.tildePullbackComplexIso A A'
          c).hom.app M ≫ ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀))
      x' n)) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
        (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
        (comp_toShHom_of_comm (isPullback_specMap h).w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) ≫
      (derivedPushforward (Spec.map d).toLRSHom.toShHom).map (specPullbackDatum c M N ψ₀)) := by
  let : Algebra R A := a.hom.toAlgebra
  let : Algebra R R' := b.hom.toAlgebra
  let : Algebra A A' := c.hom.toAlgebra
  let : Algebra R' A' := d.hom.toAlgebra
  let : Algebra R A' := (a ≫ c).hom.toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun k : R ⟶ A' => k.hom r) h.w
  have hpush : Function.Bijective
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
    let e := CommRingCat.pushoutTensorLinearEquiv R A R' A' a b c d h
    have he : ⇑(baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) = ⇑e :=
      funext fun t => by
        induction t using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul x y =>
          rw [baseChangeTensorRingMap_tmul]
          exact (CommRingCat.pushoutTensorLinearEquiv_tmul R A R' A' a b c d h x y).symm
    rw [he]
    exact e.bijective
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  obtain ⟨P, π, hP, -, hπ, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M)
  let κ₀ := ((ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.up ℤ)).map π ≫ tau0C R A R' A' M ≫
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ψ₀
  have hκ : ∀ n (x : P.X n), (κ₀.f n).hom ((1 : R') ⊗ₜ[R, algebraMap R R'] x) =
      (ψ₀.f n).hom ((1 : A') ⊗ₜ[A, algebraMap A A'] (show M.X n from (π.f n).hom x)) := by
    intro n x
    show (ψ₀.f n).hom (((squareTermComparison R A R' A').app (M.X n)).hom
      ((1 : R') ⊗ₜ[R, algebraMap R R'] (π.f n).hom x)) = _
    rw [squareTermComparison_tmul, map_one]
  have hq : QuasiIso κ₀ := by
    refine quasiIso_of_bijective_localizedModule_map hsurj hpush ε hF M N ψ₀
      (fun n q hqp => ?_) P hP π κ₀ hκ
    have hw := (isPullback_specMap h).w
    let x' : Spec A' := ⟨q, hqp⟩
    let y : Spec A := (Spec.map c) x'
    let s' : Spec R' := (Spec.map d) x'
    let s₀ : Spec R := (Spec.map a) y
    let B := (Spec A').presheaf.stalk x'
    let A₁ := (Spec A).presheaf.stalk y
    let R'₁ := (Spec R').presheaf.stalk s'
    let R₁ := (Spec R).presheaf.stalk s₀
    let : Algebra R₁ A₁ := ((Spec.map a).stalkMap y).hom.toAlgebra
    let : Algebra R₁ R'₁ := (baseStalkMap (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c)
      hw x').toAlgebra
    let : Algebra R₁ B := (((Spec.map c).stalkMap x').hom.comp
      ((Spec.map a).stalkMap y).hom).toAlgebra
    let : Algebra A₁ B := ((Spec.map c).stalkMap x').hom.toAlgebra
    let : Algebra R'₁ B := ((Spec.map d).stalkMap x').hom.toAlgebra
    have : IsScalarTower R₁ A₁ B := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower R₁ R'₁ B := IsScalarTower.of_algebraMap_eq'
      (stalkMap_square (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c) hw x')
    let : Algebra A' B := (StructureSheaf.toStalk A' x').hom.toAlgebra
    let : Algebra A B := (c ≫ StructureSheaf.toStalk A' x').hom.toAlgebra
    let : Algebra R B := (a ≫ c ≫ StructureSheaf.toStalk A' x').hom.toAlgebra
    let : Algebra R' B := (d ≫ StructureSheaf.toStalk A' x').hom.toAlgebra
    have : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R' A' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R R' B := IsScalarTower.of_algebraMap_eq fun r =>
      congrArg (fun k : R ⟶ A' => (StructureSheaf.toStalk A' x').hom (k.hom r)) h.w
    have : IsLocalization.AtPrime B q := StructureSheaf.IsLocalization.to_stalk A' x'
    let : Algebra R R₁ := (StructureSheaf.toStalk R s₀).hom.toAlgebra
    let : Algebra A A₁ := (StructureSheaf.toStalk A y).hom.toAlgebra
    let : Algebra R' R'₁ := (StructureSheaf.toStalk R' s').hom.toAlgebra
    let : Algebra R A₁ := (a ≫ StructureSheaf.toStalk A y).hom.toAlgebra
    let : Algebra R R'₁ := (b ≫ StructureSheaf.toStalk R' s').hom.toAlgebra
    have : IsScalarTower R A A₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R R₁ A₁ := IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun k => k.hom r) (specStalkMap_toStalk a y)).symm
    have : IsScalarTower A A₁ B := IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun k => k.hom r) (specStalkMap_toStalk c x')).symm
    have : IsScalarTower R' R'₁ B := IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun k => k.hom r) (specStalkMap_toStalk d x')).symm
    have : IsScalarTower R R' R'₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hpt : s₀ = (Spec.map b) s' := congrArg (fun k : Spec A' ⟶ Spec R => k x') hw
    have e : (StructureSheaf.toStalk R s₀ ≫ ((Spec R).presheaf.stalkCongr (.of_eq hpt)).hom) ≫
        (Spec.map b).stalkMap s' = b ≫ StructureSheaf.toStalk R' s' :=
      (congrArg (· ≫ (Spec.map b).stalkMap s') (stalkCongr_toStalk hpt)).trans
        (specStalkMap_toStalk b s')
    have : IsScalarTower R R₁ R'₁ := IsScalarTower.of_algebraMap_eq fun r =>
      (congrArg (fun k => k.hom r) e).symm
    have := s₀.isPrime
    have := y.isPrime
    have := s'.isPrime
    have := isLocalization_atPrime_toStalk s₀
    have := isLocalization_atPrime_toStalk y
    have := isLocalization_atPrime_toStalk s'
    let θ := (AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
      ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀
    let M₁ : CochainComplex (ModuleCat.{u} A₁) ℤ :=
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A) y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((tilde.functor A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M)
    let μ : M ⟶ ((ModuleCat.restrictScalars (algebraMap A A₁)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M₁ := tildeStalkMap M y
    let eM : ((RingTheory.TorIndependence.baseChangeFunctor A A₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M ≅ M₁ :=
      RingTheory.TorIndependence.baseChangeComplexIsoOfIsLocalizedModule
        (A₁ := A₁) (y : PrimeSpectrum A).asIdeal.primeCompl μ
        (isLocalizedModule_tildeStalkMap M y)
    let ζ := tildeStalkMap N x'
    let κ : M ⟶ ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A')
          x').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :=
      (Adjunction.mapHomologicalComplexAdjunction (ModuleCat.extendRestrictScalarsAdj c.hom)
        (ComplexShape.up ℤ)).unit.app M ≫
      ((ModuleCat.restrictScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀ ≫
      ((ModuleCat.restrictScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).map ζ
    let α := extendScalarsLift (algebraMap A B) κ
    have hα : ∀ i (m : M.X i), (α.f i).hom ((1 : B) ⊗ₜ[A, algebraMap A B] m) =
        (ζ.f i).hom ((ψ₀.f i).hom ((1 : A') ⊗ₜ[A, algebraMap A A'] m)) :=
      extendScalarsLift_f_one_tmul (algebraMap A B) κ
    let α₁ := (NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso
        (Spec.map c) x') (ComplexShape.up ℤ)).hom.app
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A') x').mapHomologicalComplex
        (ComplexShape.up ℤ)).map θ
    have hα₁ : ∀ i (m : M.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁, algebraMap A₁ B]
        (eM.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A, algebraMap A B] m) :=
      fun i m => (congrArg (fun z => (α₁.f i).hom ((1 : B) ⊗ₜ[A₁, algebraMap A₁ B] z))
        (RingTheory.TorIndependence.baseChangeComplexIsoOfIsLocalizedModule_hom_f_tmul
          (A₁ := A₁) (y : PrimeSpectrum A).asIdeal.primeCompl μ
          (isLocalizedModule_tildeStalkMap M y) i m)).trans
        ((pullbackStalk_tildeMap_germ M N ψ₀ x' i m).trans (hα i m).symm)
    exact bijective_localizedModule_map_of_isIso_local hsurj hpush ε hF M N ψ₀ q B R₁ A₁ R'₁
      (s₀ : PrimeSpectrum R).asIdeal.primeCompl (y : PrimeSpectrum A).asIdeal.primeCompl
      (s' : PrimeSpectrum R').asIdeal.primeCompl
      (AlgebraicGeometry.exists_isLocalization_stalk (isPullback_specMap h) x') eM ζ
      (isLocalizedModule_tildeStalkMap N x') α hα α₁ hα₁ n
      ((isIso_baseChangeCohomologyMap_complex_iff (Spec.map a) (Spec.map b) (Spec.map d)
        (Spec.map c) hw (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
        (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N) θ x' n).1
        (hp x' n))
  exact isIso_comp_specMap_of_quasiIso h M hM P hP π hπ N ψ₀ κ₀ hκ hq

end Stacks.Cohomology.DerivedBaseChange
