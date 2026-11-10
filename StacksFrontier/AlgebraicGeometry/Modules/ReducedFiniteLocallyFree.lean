module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.Functoriality
public import StacksFrontier.RingTheory.Module.Projective.LocallyConstantRank
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite locally free sheaves on reduced schemes

On a reduced scheme, a quasi-coherent sheaf is finite locally free if and only if
it is of finite type and its residue-field fibre rank is locally constant.

## Main results

* `isFiniteLocallyFree_iff_isFiniteType_and_isLocallyConstant_fiberRank`
  characterizes finite locally free sheaves on reduced schemes by finite type and
  locally constant fibre rank.
* `Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict`: the fibre rank is unchanged by
  restriction along an open immersion. Reducedness plays no part in it; it is here because the
  semilinear transport of the residue-field fibre it is proved by is built here.

## Implementation notes

The equivalence here identifies condition (4) of Tag 05P2 with condition (6)
of this tag. Together with the five-condition equivalence of Tag 05P2, it gives
the full six-condition equivalence in the source. The fibre rank is natural-number
valued; finite type makes this equivalent to the source's integer-valued rank.

## References

* [Stacks Project, Tag 0FWH](https://stacks.math.columbia.edu/tag/0FWH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open CategoryTheory Opposite
open Stacks.FiniteLocallyFree
open AlgebraicGeometry.Scheme.Modules (fiberRank)
open scoped TensorProduct

universe u

namespace Stacks.FiniteLocallyFree.Reduced

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

private lemma stalkMap_germ_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    f.stalkMap x (Y.presheaf.germ (f ''ᵁ U) (f x) (by simpa) ((f.appIso U).inv r)) =
      X.presheaf.germ U x hx r := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  change (X.presheaf.germ _ x _).hom ((f.app (f ''ᵁ U)).hom ((f.appIso U).inv.hom r)) = _
  have hcomp := congrArg (fun g : Γ(X, U) ⟶ Γ(X, f ⁻¹ᵁ f ''ᵁ U) => g.hom r)
    (Scheme.Hom.appIso_inv_app f U)
  dsimp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
  change (X.presheaf.germ _ x _).hom _ = _
  rw [hcomp]
  simpa using X.presheaf.germ_res_apply (eqToHom (f.preimage_image_eq U)) x
    (by simpa using hx) r

/-- A stalk of the structure sheaf and a stalk of a module are represented by germs of sections
over a common open neighbourhood. -/
private lemma exists_germ_eq_pair {X : Scheme.{u}} (F : X.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : F.presheaf.stalk x) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (a : Γ(X, V)) (b : Γ(F, V)),
      r = X.presheaf.germ V x hxV a ∧ m = F.presheaf.germ V x hxV b := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ := F.presheaf.exists_le_germ_eq m hxU
  exact ⟨V, hxV, X.presheaf.map (homOfLE hVU).op a, b,
    (X.presheaf.germ_res_apply (homOfLE hVU) x hxV a).symm, rfl⟩

private lemma restrictStalk_smul {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : Y.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x) ((F.restrict f).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (F.restrict f).val x
    letI : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk (f x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f x)
    let e : (F.restrict f).presheaf.stalk x →+ F.presheaf.stalk (f x) :=
      ((Scheme.Modules.restrictStalkNatIso f x).hom.app F).hom
    ∀ (r : X.presheaf.stalk x) (m : (F.restrict f).presheaf.stalk x),
      e (r • m) = (inv (f.stalkMap x)).hom r • e m := by
  let : Module (X.presheaf.stalk x) ((F.restrict f).presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (F.restrict f).val x
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk (f x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f x)
  let e : (F.restrict f).presheaf.stalk x →+ F.presheaf.stalk (f x) :=
    ((Scheme.Modules.restrictStalkNatIso f x).hom.app F).hom
  change ∀ r m, e (r • m) = (inv (f.stalkMap x)).hom r • e m
  intro r m
  obtain ⟨V, hxV, a', b, rfl, rfl⟩ := exists_germ_eq_pair (F.restrict f) x r m
  have hsmul : (F.restrict f).presheaf.germ V x hxV (a' • b) =
      X.presheaf.germ V x hxV a' • (F.restrict f).presheaf.germ V x hxV b :=
    PresheafOfModules.germ_smul (R := X.presheaf) (F.restrict f).val x V hxV a' b
  rw [← hsmul]
  have hring := stalkMap_germ_appIso_inv f x V hxV a'
  have hinv : (inv (f.stalkMap x)) (X.presheaf.germ V x hxV a') =
      Y.presheaf.germ (f ''ᵁ V) (f x) (by simpa) ((f.appIso V).inv a') := by
    rw [← hring, ← CommRingCat.comp_apply, IsIso.hom_inv_id]
    rfl
  rw [hinv]
  have hmod (s : (F.restrict f).val.obj (op V)) :
      e ((F.restrict f).presheaf.germ V x hxV s) =
      F.presheaf.germ (f ''ᵁ V) (f x) (by simpa) s :=
    congrArg (fun g => g s) (Scheme.Modules.germ_restrictStalkNatIso_hom_app f x F hxV)
  exact (hmod _).trans ((PresheafOfModules.germ_smul (R := Y.presheaf) F.val (f x) (f ''ᵁ V)
    (by simpa) ((f.appIso V).inv a') b).trans (congrArg _ (hmod b).symm))

private noncomputable def restrictStalkEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : Y.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x) ((F.restrict f).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (F.restrict f).val x
    letI : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk (f x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f x)
    let ringEquiv : X.presheaf.stalk x ≃+* Y.presheaf.stalk (f x) :=
      (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv
    LinearEquiv (↑ringEquiv : X.presheaf.stalk x →+* Y.presheaf.stalk (f x))
      (σ' := (↑ringEquiv.symm : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x))
      ((F.restrict f).presheaf.stalk x) (F.presheaf.stalk (f x)) := by
  let : Module (X.presheaf.stalk x) ((F.restrict f).presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (F.restrict f).val x
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk (f x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f x)
  let ringEquiv : X.presheaf.stalk x ≃+* Y.presheaf.stalk (f x) :=
    (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let linearMap : (F.restrict f).presheaf.stalk x
      →ₛₗ[(↑ringEquiv : X.presheaf.stalk x →+* Y.presheaf.stalk (f x))]
      F.presheaf.stalk (f x) := {
    __ := ((Scheme.Modules.restrictStalkNatIso f x).hom.app F).hom
    map_smul' := restrictStalk_smul f F x }
  exact LinearEquiv.ofBijective linearMap
    (ConcreteCategory.bijective_of_isIso ((Scheme.Modules.restrictStalkNatIso f x).hom.app F))

private lemma finrank_tensorProduct_congr
    {R S K L M N : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [AddCommGroup M] [AddCommGroup N] [Algebra R K] [Algebra S L]
    [Module R M] [Module S N] (ringEquiv : R ≃+* S) (fieldEquiv : K ≃+* L)
    (moduleEquiv : LinearEquiv (↑ringEquiv : R →+* S)
      (σ' := (↑ringEquiv.symm : S →+* R)) M N)
    (commutes : ∀ scalar, fieldEquiv (algebraMap R K scalar) =
      algebraMap S L (ringEquiv scalar)) :
    Module.finrank K (K ⊗[R] M) = Module.finrank L (L ⊗[S] N) := by
  let fieldLinearMap : K →ₛₗ[(↑ringEquiv : R →+* S)] L := {
    __ := fieldEquiv.toAddEquiv.toAddMonoidHom
    map_smul' := by
      intro scalar element
      change fieldEquiv (scalar • element) = ringEquiv scalar • fieldEquiv element
      simp only [Algebra.smul_def, map_mul, commutes] }
  let fieldLinearEquiv : LinearEquiv (↑ringEquiv : R →+* S)
      (σ' := (↑ringEquiv.symm : S →+* R)) K L :=
    LinearEquiv.ofBijective fieldLinearMap fieldEquiv.bijective
  let tensorEquiv := TensorProduct.congr fieldLinearEquiv moduleEquiv
  have semilinear (scalar : K) (element : K ⊗[R] M) :
      tensorEquiv (scalar • element) = fieldEquiv scalar • tensorEquiv element := by
    induction element using TensorProduct.inductionOn with
    | tmul left right =>
      simp only [TensorProduct.smul_tmul']
      exact congrArg (fun element : L => element ⊗ₜ[S] moduleEquiv right)
        (fieldEquiv.map_mul scalar left)
    | add left right left_eq right_eq =>
      simp only [smul_add, map_add, left_eq, right_eq]
  have rank_eq := lift_rank_eq_of_equiv_equiv fieldEquiv tensorEquiv.toAddEquiv
    fieldEquiv.bijective semilinear
  simpa only [Cardinal.toNat_lift, Module.finrank] using congrArg Cardinal.toNat rank_eq

/-- **The fibre rank is unchanged by restriction along an open immersion.**  An open immersion
identifies the local ring at `x` with the local ring at `f x`, hence the two residue fields, and
carries the stalk of `ℱ|_X` at `x` to the stalk of `ℱ` at `f x` semilinearly along that
identification; a semilinear equivalence of that shape preserves the dimension of the
residue-field fibre. -/
lemma fiberRank_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (F : Y.Modules) (x : X) :
    fiberRank (F.restrict f) x = fiberRank F (f x) := by
  let : Module (X.presheaf.stalk x) ((F.restrict f).presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (F.restrict f).val x
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk (f x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (f x)
  let : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    (Y.residue (f x)).hom.toAlgebra
  let ringEquiv : X.presheaf.stalk x ≃+* Y.presheaf.stalk (f x) :=
    (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let fieldEquiv := IsLocalRing.ResidueField.mapEquiv ringEquiv
  exact finrank_tensorProduct_congr ringEquiv fieldEquiv (restrictStalkEquiv f F x)
    fun scalar => IsLocalRing.ResidueField.map_residue
      (↑ringEquiv : X.presheaf.stalk x →+* Y.presheaf.stalk (f x)) scalar

private noncomputable def stalkLinearEquiv {X : Scheme.{u}} {F G : X.Modules}
    (equiv : F ≅ G) (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    letI : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
    F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  let : Module (X.presheaf.stalk x) (G.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
  let stalkIso : F.presheaf.stalk x ≅ G.presheaf.stalk x :=
    (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso equiv
  let linearMap : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] G.presheaf.stalk x := {
    __ := stalkIso.hom.hom
    map_smul' := by
      intro scalar element
      change stalkIso.hom (scalar • element) = scalar • stalkIso.hom element
      obtain ⟨V, hxV, s, element, rfl, rfl⟩ := exists_germ_eq_pair F x scalar element
      have hsmulF : F.presheaf.germ V x hxV (s • element) =
          X.presheaf.germ V x hxV s • F.presheaf.germ V x hxV element :=
        PresheafOfModules.germ_smul (R := X.presheaf) F.val x V hxV s element
      rw [← hsmulF]
      have germ_map (section_ : Γ(F, V)) :
          stalkIso.hom (F.presheaf.germ V x hxV section_) =
          G.presheaf.germ V x hxV (equiv.hom.app V section_) :=
        TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV equiv.hom.mapPresheaf section_
      rw [germ_map, germ_map]
      have hsmulG : G.presheaf.germ V x hxV (s • equiv.hom.app V element) =
          X.presheaf.germ V x hxV s • G.presheaf.germ V x hxV (equiv.hom.app V element) :=
        PresheafOfModules.germ_smul (R := X.presheaf) G.val x V hxV s
          (equiv.hom.app V element)
      rw [← hsmulG]
      exact congrArg (fun element => G.presheaf.germ V x hxV element)
        ((equiv.hom.val.app (op V)).hom.map_smul _ _) }
  exact LinearEquiv.ofBijective linearMap (ConcreteCategory.bijective_of_isIso stalkIso.hom)

private lemma fiberRank_iso {X : Scheme.{u}} {F G : X.Modules}
    (equiv : F ≅ G) (x : X) : fiberRank F x = fiberRank G x := by
  let A := ToType (X.presheaf.stalk x)
  let K := ToType (X.residueField x)
  let MF := ToType (F.presheaf.stalk x)
  let MG := ToType (G.presheaf.stalk x)
  let : Module A MF :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  let : Module A MG :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
  let : Algebra A K := (X.residue x).hom.toAlgebra
  let stalkEquiv : MF ≃ₗ[A] MG := stalkLinearEquiv equiv x
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) stalkEquiv).finrank_eq

private noncomputable def stalk_basechange {R : CommRingCat.{u}} (M : ModuleCat R)
    (p : PrimeSpectrum (↑R)) :
    let A := (Spec (↑R)).presheaf.stalk p
    letI : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
    letI : IsLocalization.AtPrime A p.asIdeal := StructureSheaf.IsLocalization.to_stalk (↑R) p
    let N := TopCat.Presheaf.stalk (moduleStructurePresheaf (↑R) (↑M)).presheaf p
    letI : Module A N :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := structurePresheafInCommRingCat (↑R))
        (moduleStructurePresheaf (↑R) (↑M)) p
    TensorProduct R A (↑M) ≃ₗ[A] N := by
  let A := (Spec (↑R)).presheaf.stalk p
  let N := TopCat.Presheaf.stalk (moduleStructurePresheaf (↑R) (↑M)).presheaf p
  let : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
  let : IsLocalization.AtPrime A p.asIdeal := StructureSheaf.IsLocalization.to_stalk (↑R) p
  let f : ↑M →ₗ[↑R] N := (tilde.toStalk M p).hom
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := structurePresheafInCommRingCat (↑R))
    (moduleStructurePresheaf (↑R) (↑M)) p
  let : IsScalarTower (↑R) A N := .of_algebraMap_smul (fun r n => rfl)
  let : IsLocalizedModule p.asIdeal.primeCompl f :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk M p
  exact IsLocalizedModule.isBaseChange p.asIdeal.primeCompl A f |>.equiv

private theorem fiberRank_tilde_eq_finrank {R : CommRingCat.{u}} (M : ModuleCat R)
    (p : PrimeSpectrum (↑R)) :
    fiberRank (tilde M) p =
      let A := (Spec R).presheaf.stalk p
      let K := ↑((Spec R).residueField p)
      letI : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
      letI : Algebra A K := ((Spec R).residue p).hom.toAlgebra
      letI : Algebra (↑R) K := Algebra.restrictScalars (↑R) A K
      Module.finrank K (K ⊗[(↑R)] ↑M) := by
  classical
  let A := (Spec (↑R)).presheaf.stalk p
  let N := TopCat.Presheaf.stalk (moduleStructurePresheaf (↑R) (↑M)).presheaf p
  let K := ↑((Spec R).residueField p)
  let : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
  let : IsLocalization.AtPrime A p.asIdeal := StructureSheaf.IsLocalization.to_stalk (↑R) p
  let : Algebra A K := ((Spec R).residue p).hom.toAlgebra
  let : Algebra (↑R) K := Algebra.restrictScalars (↑R) A K
  let : IsScalarTower (↑R) A K := .of_algebraMap_smul (fun r k => rfl)
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := structurePresheafInCommRingCat (↑R))
    (moduleStructurePresheaf (↑R) (↑M)) p
  let : IsScalarTower (↑R) A N := .of_algebraMap_smul (fun r n => rfl)
  let eBase : A ⊗[(↑R)] ↑M ≃ₗ[A] N := stalk_basechange M p
  let eCongr : K ⊗[A] (A ⊗[(↑R)] ↑M) ≃ₗ[K] K ⊗[A] N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) eBase
  let eCancel : K ⊗[A] (A ⊗[(↑R)] ↑M) ≃ₗ[K] K ⊗[(↑R)] ↑M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (↑R) A K K (↑M)
  let e : K ⊗[(↑R)] ↑M ≃ₗ[K] K ⊗[A] N := eCancel.symm.trans eCongr
  change Module.finrank K (K ⊗[A] N) = Module.finrank K (K ⊗[(↑R)] ↑M)
  exact e.finrank_eq.symm

private theorem finrank_residueField_change {R : CommRingCat.{u}} (M : ModuleCat R)
    [Module.Finite (↑R) (↑M)] (p : Spec R) :
    let q : PrimeSpectrum (↑R) := p
    letI : q.asIdeal.IsPrime := q.isPrime
    let K0 : Type u := ↑((Spec R).residueField p)
    let K1 := q.asIdeal.ResidueField
    let A := (Spec R).presheaf.stalk p
    letI : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
    letI : Algebra A K0 := ((Spec R).residue p).hom.toAlgebra
    letI : Algebra (↑R) K0 := Algebra.restrictScalars (↑R) A K0
    Module.finrank K0 (K0 ⊗[(↑R)] ↑M) =
      Module.finrank K1 (K1 ⊗[(↑R)] ↑M) := by
  classical
  let q : PrimeSpectrum (↑R) := p
  let K0 : Type u := ↑((Spec R).residueField p)
  let K1 := q.asIdeal.ResidueField
  let A := (Spec R).presheaf.stalk p
  let : Algebra (↑R) A := StructureSheaf.stalkAlgebra (↑R) p
  let : Algebra A K0 := ((Spec R).residue p).hom.toAlgebra
  let : Algebra (↑R) K0 := Algebra.restrictScalars (↑R) A K0
  let e : K0 ≃+* K1 :=
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso R p).commRingCatIsoToRingEquiv
  have hecomm (r : ↑R) : e (algebraMap (↑R) K0 r) = algebraMap (↑R) K1 r := by
    have hh := AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv R p
    have hh' := congrArg (fun f : CommRingCat.of (↑R) ⟶ CommRingCat.of K0 => f.hom r) hh
    change e.symm (algebraMap (↑R) K1 r) = algebraMap (↑R) K0 r at hh'
    exact e.symm.injective (by simpa [e] using hh'.symm)
  let eR : K0 →ₗ[↑R] K1 := {
    toFun := e
    map_add' := e.map_add
    map_smul' := by
      intro r x
      rw [Algebra.smul_def, Algebra.smul_def, e.map_mul, hecomm]
      rfl }
  let eR' : K0 ≃ₗ[↑R] K1 := LinearEquiv.ofBijective eR e.bijective
  let j : K0 ⊗[(↑R)] ↑M ≃ₗ[↑R] K1 ⊗[(↑R)] ↑M :=
    TensorProduct.AlgebraTensorModule.congr eR' (LinearEquiv.refl (↑R) (↑M))
  have hc : ∀ (r : K0) (m : K0 ⊗[(↑R)] ↑M),
      j (r • m) = e r • j m := by
    intro r m
    induction m using TensorProduct.inductionOn with
    | tmul a b =>
      rw [TensorProduct.smul_tmul']
      simp only [j, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
      rw [TensorProduct.smul_tmul']
      simp [eR', eR, LinearEquiv.ofBijective_apply, map_mul]
    | add x y hx hy =>
      simp only [smul_add, j.map_add, hx, hy]
  have hrank : Module.rank K0 (K0 ⊗[(↑R)] ↑M) =
      Module.rank K1 (K1 ⊗[(↑R)] ↑M) :=
    rank_eq_of_equiv_equiv e j.toAddEquiv e.bijective hc
  exact_mod_cast (Module.finrank_eq_rank K0 (K0 ⊗[(↑R)] ↑M)).trans
    (hrank.trans (Module.finrank_eq_rank K1 (K1 ⊗[(↑R)] ↑M)).symm)

private theorem fiberRank_tilde_eq_fiber {R : CommRingCat.{u}} (M : ModuleCat R)
    [Module.Finite (↑R) (↑M)] (p : PrimeSpectrum (↑R)) :
    fiberRank (tilde M) p =
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (↑M)) := by
  rw [fiberRank_tilde_eq_finrank]
  exact finrank_residueField_change M p

private theorem free_stalk_of_isLocallyConstant_fiberRank {R : CommRingCat.{u}}
    [IsReduced (↑R)] (F : (Spec R).Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (rank_constant : IsLocallyConstant (fiberRank F)) (point : Spec R) :
    letI : Module ((Spec R).presheaf.stalk point) (F.presheaf.stalk point) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val point
    Module.Free ((Spec R).presheaf.stalk point) (F.presheaf.stalk point) := by
  let : Module ((Spec R).presheaf.stalk point) (F.presheaf.stalk point) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val point
  let prime : PrimeSpectrum (↑R) := point
  let : prime.asIdeal.IsPrime := prime.isPrime
  let sections := (modulesSpecToSheaf.obj F).presheaf.obj (op ⊤)
  let equiv : tilde sections ≅ F := asIso F.fromTildeΓ
  have : (tilde sections).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} equiv.symm
  have : Module.Finite (↑R) (↑sections) :=
    (AlgebraicGeometry.tilde_isFiniteType_iff sections).mp inferInstance
  have module_rank_constant : IsLocallyConstant fun prime : PrimeSpectrum (↑R) =>
      Module.finrank prime.asIdeal.ResidueField (prime.asIdeal.Fiber (↑sections)) := by
    have rank_eq : (fun prime : PrimeSpectrum (↑R) =>
        Module.finrank prime.asIdeal.ResidueField (prime.asIdeal.Fiber (↑sections))) =
        fiberRank F := funext fun prime =>
      (fiberRank_tilde_eq_fiber sections prime).symm.trans (fiberRank_iso equiv prime)
    rw [rank_eq]
    exact rank_constant
  have projective : Module.Projective (↑R) (↑sections) :=
    (Module.projective_iff_isLocallyConstant_finrank_fiber (↑R) (↑sections)).mpr
      module_rank_constant
  have finite_projective : Module.Finite (↑R) (↑sections) ∧
    Module.Projective (↑R) (↑sections) := ⟨inferInstance, projective⟩
  have free_locus := ((Module.finite_projective_tfae (↑R) (↑sections)).out 2 8).mp
    finite_projective
  let stalk := (Spec R).presheaf.stalk point
  let : Algebra (↑R) stalk := StructureSheaf.stalkAlgebra (↑R) point
  let : IsLocalization.AtPrime stalk point.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (↑R) point
  have : Module.Free stalk (stalk ⊗[↑R] ↑sections) :=
    (Module.mem_freeLocus_iff_tensor point stalk).mp (by rw [free_locus.2.1]; trivial)
  let : Module stalk ((tilde sections).presheaf.stalk point) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (tilde sections).val point
  have : Module.Free stalk ((tilde sections).presheaf.stalk point) :=
    Module.Free.of_equiv (stalk_basechange sections point)
  exact Module.Free.of_equiv (stalkLinearEquiv equiv point)

/-- On a reduced scheme, a quasi-coherent sheaf is finite locally free exactly
when it is of finite type and has locally constant fibre rank. -/
@[stacks 0FWH]
theorem isFiniteLocallyFree_iff_isFiniteType_and_isLocallyConstant_fiberRank
    {X : Scheme.{u}} [IsReduced X] (F : X.Modules) [F.IsQuasicoherent] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F ↔
      (F.IsFiniteType ∧ IsLocallyConstant (fiberRank F)) := by
  constructor
  · intro h
    have h45 := ((ModuleTFAE.finiteLocallyFree_tfae F).out 4 5).mp h
    exact ⟨h45.1, h45.2.2⟩
  · rintro ⟨hfinite, hrank⟩
    let : F.IsFiniteType := hfinite
    have h45 := (ModuleTFAE.finiteLocallyFree_tfae F).out 4 5
    apply h45.mpr
    refine ⟨hfinite, ?_, hrank⟩
    intro x
    obtain ⟨ring, inclusion, open_immersion, point, point_eq⟩ := X.exists_Spec_apply_eq x
    change inclusion point = x at point_eq
    subst x
    let : IsOpenImmersion inclusion := open_immersion
    let : IsReduced (Spec ring) := isReduced_of_isOpenImmersion inclusion
    let : IsReduced (↑ring) := (affine_isReduced_iff ring).mp inferInstance
    let restricted := F.restrict inclusion
    let : Module ((Spec ring).presheaf.stalk point) (restricted.presheaf.stalk point) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        restricted.val point
    let : Module (X.presheaf.stalk (inclusion point)) (F.presheaf.stalk (inclusion point)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        F.val (inclusion point)
    have : restricted.IsFiniteType :=
      Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict inclusion F
    have restricted_rank : IsLocallyConstant (fiberRank restricted) := by
      convert hrank.comp_continuous inclusion.continuous using 1
      funext point
      exact fiberRank_restrict inclusion F point
    have := free_stalk_of_isLocallyConstant_fiberRank restricted restricted_rank point
    exact Module.Free.of_equiv (restrictStalkEquiv inclusion F point)

end Stacks.FiniteLocallyFree.Reduced
