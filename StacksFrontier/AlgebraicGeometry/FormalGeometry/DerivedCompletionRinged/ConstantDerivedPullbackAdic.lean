module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantPullbackKoszul
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Derived pullback and derived direct image of the constant adic tower

Let `f : Sh(𝒟) ⟶ Sh(𝒞)` be a morphism of topoi, `Λ` a Noetherian ring, `I ⊂ Λ` an ideal, and read
`f` as the morphism of ringed topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` of
`MorphismOfTopoi.constantRingedToposHom`. Write `(Λ/Iⁿ)̲` for the tower of constant sheaves of
modules placed in degree zero, on either site. This file proves:

* the tower `n ↦ Lf^*(Λ/Iⁿ)̲` in `D(𝒟, Λ)` is pro-isomorphic to the tower `n ↦ (Λ/Iⁿ)̲`;
* for every `E` in `D(𝒟, Λ)` the tower `n ↦ Rf_*E ⊗^𝐋_Λ (Λ/Iⁿ)̲` in `D(𝒞, Λ)` is pro-isomorphic
  to the tower `n ↦ Rf_*(E ⊗^𝐋_Λ (Λ/Iⁿ)̲)`.

Neither tower consists of perfect objects, so neither statement holds termwise in general. Both
are proved by passing through the tower of Koszul complexes `K_n = K(Λ, g_1^{n+1}, …, g_r^{n+1})`
on generators `g_i` of `I`, which is pro-isomorphic to `{Λ/Iⁿ}` by [Stacks, Tag 0921]: the
constant complexes `K_n̲` are strictly perfect, so `Lf^*` is computed on them by the degreewise
pullback, which carries `K_n̲` on `𝒞` to `K_n̲` on `𝒟`
(`MorphismOfTopoi.koszulPowerDualComplexSystemPullbackIso`), and the projection formula of
[Stacks, Tag 0944] holds at them
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isStrictlyPerfect`).

## Main results

* `MorphismOfTopoi.nonempty_proIso_constantAdicTower_derivedPullback`: the first statement.
* `MorphismOfTopoi.nonempty_proIso_constantAdicTower_derivedPushforward`: the second statement.

## References

* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 099N](https://stacks.math.columbia.edu/tag/099N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The dual Koszul complex is strictly perfect** ([Stacks, Tag 08FL]): it is concentrated in
degrees `-r, …, 0`, and its terms are those of the Koszul complex, finite free `𝒪`-modules. -/
theorem isStrictlyPerfect_koszulPowerDualComplex (n : ℕ) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (koszulPowerDualComplex X f n) where
  bounded := (Set.finite_Icc (-(r : ℤ)) 0).subset fun j hj => by
    simp only [Set.mem_ofPred_eq] at hj
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · by_contra h
      exact hj (isZero_koszulPowerDualComplex_X_of_lt X f n (by omega))
    · by_contra h
      exact hj (isZero_koszulPowerDualComplex_X_of_pos X f n (by omega))
  termDirectSummand j := isDirectSummandOfFiniteFree_koszulPowerComplex_X X f n (-j)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (h : RingedToposHom X Y)

attribute [local instance] pullbackModules_additive

/-- **`Lf^*` on a diagram of K-flat complexes with flat terms is the degreewise pullback**: the
canonical comparison `Lf^* ⟶ f^*` of [Stacks, Tag 06YY], which is invertible at such complexes,
read on a diagram of them. -/
def derivedPullbackMapIsoOfIsKFlat {ι : Type*} [Category ι]
    (T : ι ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hT : ∀ i, Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)
      ((HomotopyCategory.quotient _ _).obj (T.obj i))) :
    T ⋙ DerivedCategory.Q ⋙ derivedPullback h ≅
      T ⋙ h.toModulesHom.pullbackModules.mapHomologicalComplex _ ⋙ DerivedCategory.Q :=
  haveI : IsIso (Functor.whiskerLeft (T ⋙ HomotopyCategory.quotient _ _)
      (derivedPullbackComparison h)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun i =>
      open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
      isIso_derivedPullbackComparison_app_isKFlat h _ (hT i))
  Functor.isoWhiskerLeft T (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _) ≪≫
    asIso (Functor.whiskerLeft (T ⋙ HomotopyCategory.quotient _ _)
      (derivedPullbackComparison h)) ≪≫
    Functor.isoWhiskerLeft T (Functor.isoWhiskerRight
      (h.toModulesHom.pullbackModules.mapHomotopyCategoryFactors _) DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (T ⋙ h.toModulesHom.pullbackModules.mapHomologicalComplex _)
      (DerivedCategory.quotientCompQhIso _)

end AlgebraicGeometry.RingedToposHom

namespace MorphismOfTopoi

open Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D} (Λ : Type u) [CommRing Λ]
  (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))

/-- `Lf^*` exists along `MorphismOfTopoi.constantRingedToposHom`, as it does along every morphism
of ringed topoi. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_constantRingedToposHom :
    (pullbackOnHomotopy (constantRingedToposHom Λ f)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := RingedTopos.constant J Λ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (constantRingedToposHom Λ f)

/-- **The derived pullback `Lf^* : D(𝒞, Λ) ⥤ D(𝒟, Λ)`** along
`MorphismOfTopoi.constantRingedToposHom`. -/
abbrev constantDerivedPullback :
    DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant J Λ).O)) ⥤
    DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)) :=
  derivedPullback (X := RingedTopos.constant K Λ) (Y := RingedTopos.constant J Λ)
    (constantRingedToposHom Λ f)

/-- `Lf^*` commutes with the shift. -/
noncomputable instance commShift_constantDerivedPullback :
    (constantDerivedPullback Λ f).CommShift ℤ :=
  derivedPullback_commShift (constantRingedToposHom Λ f)

/-- The dual Koszul complexes on the constant site are K-flat with flat terms. -/
theorem isKFlat_koszulPowerDualComplex {r : ℕ} (x : Fin r → Λ) (n : ℕ) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := RingedTopos.constant J Λ)
      ((HomotopyCategory.quotient _ _).obj (RingedSite.koszulPowerDualComplex
        (RingedSite.constant J Λ) (fun i => RingedSite.constantGlobalSection J Λ (x i)) n)) :=
  ⟨RingedSite.kFlat_of_isStrictlyPerfect (RingedSite.constant J Λ) _
      (RingedSite.isStrictlyPerfect_koszulPowerDualComplex (RingedSite.constant J Λ) _ n),
    fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect
      (Y := RingedSite.constant J Λ) (RingedSite.isStrictlyPerfect_koszulPowerDualComplex _ _ n) i⟩

/-- `Lf^*` on the tower of dual Koszul complexes on `(𝒞, Λ̲)` is the degreewise pullback. -/
def koszulPowerDualComplexSystemDerivedPullbackIso {r : ℕ} (x : Fin r → Λ) :
    RingedSite.koszulPowerDualComplexSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙ DerivedCategory.Q ⋙
      constantDerivedPullback Λ f ≅
    RingedSite.koszulPowerDualComplexSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      (constantRingedToposHom Λ f).toModulesHom.pullbackModules.mapHomologicalComplex _ ⋙
        DerivedCategory.Q :=
  RingedToposHom.derivedPullbackMapIsoOfIsKFlat (constantRingedToposHom Λ f) _
    (fun n => isKFlat_koszulPowerDualComplex Λ x n.unop)

/-- The tower of derived duals of the Koszul complexes, read through the dual complexes, on the
constant site of `𝒞`, followed by `Lf^*`. -/
def koszulPowerDualSystemDerivedPullbackIso₁ {r : ℕ} (x : Fin r → Λ) :
    RingedSite.koszulPowerDualSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙ constantDerivedPullback Λ f ≅
      (RingedSite.koszulPowerDualComplexSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙ DerivedCategory.Q) ⋙
          constantDerivedPullback Λ f :=
  Functor.isoWhiskerRight (RingedSite.derivedDualKoszulPowerSystemIso
    (RingedSite.constant J Λ) (fun i => RingedSite.constantGlobalSection J Λ (x i))) _

/-- The degreewise pullback of the dual Koszul complexes, passed to `D(𝒟, Λ)`. -/
def koszulPowerDualSystemDerivedPullbackIso₃ {r : ℕ} (x : Fin r → Λ) :
    (RingedSite.koszulPowerDualComplexSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      (constantRingedToposHom Λ f).toModulesHom.pullbackModules.mapHomologicalComplex _) ⋙
        DerivedCategory.Q ≅
      RingedSite.koszulPowerDualSystem (RingedSite.constant K Λ)
        (fun i => RingedSite.constantGlobalSection K Λ (x i)) :=
  Functor.isoWhiskerRight (koszulPowerDualComplexSystemPullbackIso Λ f x) DerivedCategory.Q ≪≫
    (RingedSite.derivedDualKoszulPowerSystemIso (RingedSite.constant K Λ)
      (fun i => RingedSite.constantGlobalSection K Λ (x i))).symm

/-- **`Lf^*` carries the tower of dual Koszul complexes `K_n^∨` on `(𝒞, Λ̲)` to the tower of dual
Koszul complexes on `(𝒟, Λ̲)`**, for the sections `x̲_1, …, x̲_r`. -/
def koszulPowerDualSystemDerivedPullbackIso {r : ℕ} (x : Fin r → Λ) :
    RingedSite.koszulPowerDualSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      constantDerivedPullback Λ f ≅
      RingedSite.koszulPowerDualSystem (RingedSite.constant K Λ)
        (fun i => RingedSite.constantGlobalSection K Λ (x i)) :=
  (koszulPowerDualSystemDerivedPullbackIso₁ Λ f x).trans
    ((koszulPowerDualComplexSystemDerivedPullbackIso Λ f x).trans
      (koszulPowerDualSystemDerivedPullbackIso₃ Λ f x))

/-- **The tower `n ↦ Lf^*(Λ/Iⁿ)̲` is pro-isomorphic to the tower `n ↦ (Λ/Iⁿ)̲`**, in `D(𝒟, Λ)`. -/
theorem nonempty_proIso_constantAdicTower_derivedPullback [IsNoetherianRing Λ] (I : Ideal Λ) :
    Nonempty (InverseSequence.ProIso
      (Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor J Λ ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ constantDerivedPullback Λ f)
      (Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor K Λ ⋙
        DerivedCategory.singleFunctor _ 0)) := by
  obtain ⟨r, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian I)
  exact ⟨(((RingedSite.koszulPowerDualSystemProIso J Λ x I hx).symm.whiskerRight
      (constantDerivedPullback Λ f)).trans
    (InverseSequence.ProIso.ofNatIso (koszulPowerDualSystemDerivedPullbackIso Λ f x))).trans
      (RingedSite.koszulPowerDualSystemProIso K Λ x I hx)⟩

/-- **The derived direct image `Rf_* : D(𝒟, Λ) ⥤ D(𝒞, Λ)`** along
`MorphismOfTopoi.constantRingedToposHom`. -/
abbrev constantDerivedPushforward :
    DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O)) ⥤
    DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant J Λ).O)) :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := RingedTopos.constant K Λ)
    (Y := RingedTopos.constant J Λ) (constantRingedToposHom Λ f)

/-- **The projection formula along the tower of dual Koszul complexes**:
`Rf_*E ⊗^𝐋 K_n^∨ ≅ Rf_*(E ⊗^𝐋 Lf^*K_n^∨)`, naturally in `n`, by [Stacks, Tag 0944] at the strictly
perfect complexes representing `K_n^∨`. -/
def koszulPowerDualSystemProjectionFormulaIso {r : ℕ} (x : Fin r → Λ)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))) :
    RingedSite.koszulPowerDualSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (RingedTopos.constant J Λ).O).obj ((constantDerivedPushforward Λ f).obj E) ≅
    RingedSite.koszulPowerDualSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      (constantDerivedPullback Λ f ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (RingedTopos.constant K Λ).O).obj E ⋙ constantDerivedPushforward Λ f) :=
  haveI : ∀ n, IsIso ((Functor.whiskerLeft (RingedSite.koszulPowerDualSystem
      (RingedSite.constant J Λ) (fun i => RingedSite.constantGlobalSection J Λ (x i)))
      (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaNatTrans
        (constantRingedToposHom Λ f) E)).app n) := fun n =>
    ((Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaNatTrans
        (constantRingedToposHom Λ f) E).isIso_app_iff_of_iso
      ((RingedSite.derivedDualKoszulPowerSystemIso (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i))).app n ≪≫
        (shiftFunctorZero _ ℤ).symm.app _)).mpr
      (Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_projectionFormulaMap_of_isStrictlyPerfect
        (constantRingedToposHom Λ f) E _
        (RingedSite.isStrictlyPerfect_koszulPowerDualComplex (RingedSite.constant J Λ) _ n.unop)
        0)
  @asIso _ _ _ _ (Functor.whiskerLeft (RingedSite.koszulPowerDualSystem
      (RingedSite.constant J Λ) (fun i => RingedSite.constantGlobalSection J Λ (x i)))
      (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaNatTrans
        (constantRingedToposHom Λ f) E)) (NatIso.isIso_of_isIso_app _)

/-- **The tower `n ↦ Rf_*E ⊗^𝐋_Λ (Λ/Iⁿ)̲` is pro-isomorphic to the tower
`n ↦ Rf_*(E ⊗^𝐋_Λ (Λ/Iⁿ)̲)`**, in `D(𝒞, Λ)`, for every `E` in `D(𝒟, Λ)`. -/
theorem nonempty_proIso_constantAdicTower_derivedPushforward [IsNoetherianRing Λ]
    (I : Ideal Λ) (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedTopos.constant K Λ).O))) :
    Nonempty (InverseSequence.ProIso
      (RingedSite.constantAdicTower J Λ I ((constantDerivedPushforward Λ f).obj E))
      (RingedSite.constantAdicTower K Λ I E ⋙ constantDerivedPushforward Λ f)) := by
  obtain ⟨r, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian I)
  let KC := RingedSite.koszulPowerDualSystem (RingedSite.constant J Λ)
    (fun i => RingedSite.constantGlobalSection J Λ (x i))
  let KD := RingedSite.koszulPowerDualSystem (RingedSite.constant K Λ)
    (fun i => RingedSite.constantGlobalSection K Λ (x i))
  let AC := Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor J Λ ⋙
    DerivedCategory.singleFunctor _ 0
  let AD := Stacks.ConstantSheaf.adicQuotientSystem I ⋙ RingedSite.constantModuleFunctor K Λ ⋙
    DerivedCategory.singleFunctor _ 0
  let SC := (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedSite.constant J Λ)).obj
    ((constantDerivedPushforward Λ f).obj E)
  let OC := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (RingedTopos.constant J Λ).O).obj ((constantDerivedPushforward Λ f).obj E)
  let SD := (Stacks.SheafOfModules.derivedTensorProductFunctor (RingedSite.constant K Λ)).obj E
  let OD := (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (RingedTopos.constant K Λ).O).obj E
  let R := constantDerivedPushforward Λ f
  let p₁ : InverseSequence.ProIso (AC ⋙ SC) (KC ⋙ SC) :=
    (RingedSite.koszulPowerDualSystemProIso J Λ x I hx).symm.whiskerRight SC
  let e₂ : KC ⋙ SC ≅ KC ⋙ OC :=
    Functor.isoWhiskerLeft KC ((RingedSite.derivedTensorFunctorIso
      (RingedSite.constant J Λ)).app ((constantDerivedPushforward Λ f).obj E))
  let e₃ : KC ⋙ OC ≅ KC ⋙ (constantDerivedPullback Λ f ⋙ OD ⋙ R) :=
    koszulPowerDualSystemProjectionFormulaIso Λ f x E
  let e₄ : KC ⋙ (constantDerivedPullback Λ f ⋙ OD ⋙ R) ≅ KD ⋙ (OD ⋙ R) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (koszulPowerDualSystemDerivedPullbackIso Λ f x) (OD ⋙ R)
  let e₅ : KD ⋙ (OD ⋙ R) ≅ KD ⋙ (SD ⋙ R) :=
    Functor.isoWhiskerLeft KD (Functor.isoWhiskerRight ((RingedSite.derivedTensorFunctorIso
      (RingedSite.constant K Λ)).app E).symm R)
  let p₆ : InverseSequence.ProIso (KD ⋙ (SD ⋙ R)) (AD ⋙ (SD ⋙ R)) :=
    (RingedSite.koszulPowerDualSystemProIso K Λ x I hx).whiskerRight (SD ⋙ R)
  exact ⟨((((p₁.trans (InverseSequence.ProIso.ofNatIso e₂)).trans
    (InverseSequence.ProIso.ofNatIso e₃)).trans (InverseSequence.ProIso.ofNatIso e₄)).trans
      (InverseSequence.ProIso.ofNatIso e₅)).trans p₆⟩

end MorphismOfTopoi

end
