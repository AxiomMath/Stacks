module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkComplexIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexIntoSingleDifferential

/-!
# The internal Hom complex out of a Koszul complex, at a stalk

Let `O♯` be a sheaf of commutative rings on a space, `K` the Koszul complex of a morphism
`φ : (O♯)ʳ ⟶ O♯` given by global sections `f₁, …, f_r`, and `M` an `O♯`-module. At a point `x`,
the degree-`n` term of the internal Hom complex `𝓗om^•(K, M)` has stalk the module of
`O_x`-linear maps `⋀ⁿ((O_x)ʳ) ⟶ M_x`, and under this identification the differential of the
internal Hom complex is `(-1)^{n+1}` times the transpose of the ring-level Koszul differential of
the germs of the `fᵢ`.

## Main results

* `Stacks.RegularSequence.KoszulChainData.homComplexStalkEquiv`: the stalk of
  `𝓗om^•(K, M[0])^n` is `Hom_{O_x}(⋀ⁿ((O_x)ʳ), M_x)`.
* `Stacks.RegularSequence.KoszulChainData.homComplexXIso_hom_app_d`: on sections, the
  differential is `(-1)^{n+1}` times precomposition with the Koszul differential.
* `Stacks.RegularSequence.KoszulChainData.homComplexStalkEquiv_stalkLin_d`: the same at a stalk,
  against the ring-level Koszul differential of the germs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules Stacks.SheafOfModules.SheafHomStalk

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ)

/-- The internal Hom complex `𝓗om^•(K, M[0])` out of the Koszul cochain complex. -/
abbrev homComplex (M : StructureSheafModules Rc) :
    CochainComplex (StructureSheafModules Rc) ℤ :=
  (RingedSite.sheafHomComplex (ringedSite Rc) (cochain Rc K)
    ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).obj M)).obj

/-- The degree-`n` term of `𝓗om^•(K, M[0])` is `𝓗om(⋀ⁿ((O♯)ʳ), M)`. -/
def homComplexXIso (M : StructureSheafModules Rc) (n : ℕ) :
    (homComplex Rc K M).X n ≅
      RingedSite.internalHomSheaf (ringedSite Rc) (A.exteriorPower n) M :=
  RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K) M n ≪≫
    eqToIso (congrArg (fun N => RingedSite.internalHomSheaf (ringedSite Rc) N M)
      ((congrArg K.chain.X (neg_neg ((n : ℕ) : ℤ))).trans (K.chain_X n)))

/-- **The stalk of a term of the internal Hom complex out of the Koszul complex**: the
`O_x`-linear maps out of the exterior power of the free module `(O_x)ʳ`. -/
def homComplexStalkEquiv (M : StructureSheafModules Rc) (n : ℕ) (x : X) :
    modStalk ((homComplex Rc K M).X n) x ≃ₗ[ringStalk Rc x]
      (⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^n (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x)) →ₗ[
          ringStalk Rc x] modStalk M x) :=
  have : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheaf Rc) (A.exteriorPower n) :=
    isFinitePresentation_koszulExteriorPower Rc (A := A) n
  modStalkEquivOfIso Rc (homComplexXIso Rc K M n) x ≪≫ₗ
    internalHomSheafStalkEquiv Rc (A.exteriorPower n) M x ≪≫ₗ
    LinearEquiv.arrowCongr (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x)
      (LinearEquiv.refl (ringStalk Rc x) (modStalk M x))

/-- The stalk identification on the germ of a section, evaluated on the germ of a section. -/
private theorem homComplexStalkEquiv_germ_apply (M : StructureSheafModules Rc) (n : ℕ) (x : X)
    (U : Opens X) (hxU : x ∈ U) (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op U))
    (m : (commVal (Rc := Rc) (A.exteriorPower n)).obj (op U)) :
    homComplexStalkEquiv Rc K M n x (germAt ((homComplex Rc K M).X n) U x hxU s)
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
          (germAt (A.exteriorPower n) U x hxU m))
      = germAt M U x hxU
          (((homComplexXIso Rc K M n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U))) m) := by
  have hfp : _root_.SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheaf Rc) (A.exteriorPower n) :=
    isFinitePresentation_koszulExteriorPower Rc (A := A) n
  rw [homComplexStalkEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply,
    LinearEquiv.symm_apply_apply]
  rw [modStalkEquivOfIso_germ]
  exact internalHomSheafStalkEquiv_germ Rc (A.exteriorPower n) M x U hxU _ m

/-- **The stalk identification on germs.** The linear map attached to the germ of a section `s`
of `𝓗om^•(K, M[0])^n` takes the basis wedge indexed by `i` to the germ of the value of `s`, read in
`𝓗om(⋀ⁿ((O♯)ʳ), M)`, on the corresponding basis section of the exterior power. -/
theorem homComplexStalkEquiv_germ (M : StructureSheafModules Rc) (n : ℕ) (x : X) (U : Opens X)
    (hxU : x ∈ U) (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op U))
    (i : Fin n → Fin r) :
    homComplexStalkEquiv Rc K M n x (germAt ((homComplex Rc K M).X n) U x hxU s)
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Rc.obj x) n fun j => Pi.single (i j) 1)
      = germAt M U x hxU
          (((homComplexXIso Rc K M n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U)))
            (exteriorBasisSection A U n i)) := by
  rw [← Stacks.SheafOfModules.exteriorKoszulStalkEquiv_germ_exteriorBasisSection A n U hxU i]
  exact homComplexStalkEquiv_germ_apply Rc K M n x U hxU s _

/-- The identification of the term of the Koszul cochain complex in degree `-n` with the `n`-th
exterior power. -/
theorem cochain_X_neg (n : ℕ) : (cochain Rc K).X (-((n : ℕ) : ℤ)) = A.exteriorPower n :=
  (congrArg K.chain.X (neg_neg ((n : ℕ) : ℤ))).trans (K.chain_X n)

/-- **The stalk identification on germs of arbitrary sections.** -/
theorem homComplexStalkEquiv_germ_germ (M : StructureSheafModules Rc) (n : ℕ) (x : X)
    (U : Opens X) (hxU : x ∈ U) (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op U))
    (m : (commVal (Rc := Rc) (A.exteriorPower n)).obj (op U)) :
    homComplexStalkEquiv Rc K M n x (germAt ((homComplex Rc K M).X n) U x hxU s)
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
          (germAt (A.exteriorPower n) U x hxU m))
      = germAt M U x hxU
          (((homComplexXIso Rc K M n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U))) m) := by
  exact homComplexStalkEquiv_germ_apply Rc K M n x U hxU s m

/-- **The collapse `𝓗om^•(K, M[0])^n ≅ 𝓗om(⋀ⁿ((O♯)ʳ), M)` on evaluations** is the evaluation of
the Hom section on the corresponding section of the Koszul cochain complex. -/
theorem homComplexXIso_hom_app (M : StructureSheafModules Rc) (n : ℕ) (U : Opens X)
    (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op U))
    (m : (commVal (Rc := Rc) (A.exteriorPower n)).obj (op U)) :
    ((homComplexXIso Rc K M n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U))) m =
      RingedSite.evalSingle (ringedSite Rc) (cochain Rc K) M U U (𝟙 U) n (-((n : ℕ) : ℤ))
        (by omega) s ((eqToHom (cochain_X_neg Rc K n).symm).val.app (op U) m) := by
  rw [homComplexXIso, Iso.trans_hom, eqToIso.hom]
  refine (RingedSite.eqToHom_internalHomSheaf_source_app (ringedSite Rc) (cochain_X_neg Rc K n)
    U ((RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K) M n).hom.val.app (op U) s)
    (op (Over.mk (𝟙 U))) m).trans ?_
  refine (congrArg (fun z => ((RingedSite.homDegreeIsoSingle (ringedSite Rc) (cochain Rc K) M
      n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U))) z)
    (RingedSite.eqToHom_over_app (ringedSite Rc) (cochain_X_neg Rc K n).symm U U (𝟙 U) m)).trans ?_
  exact RingedSite.homDegreeIsoSingle_hom_app (ringedSite Rc) (cochain Rc K) M n U U (𝟙 U) s _

/-- A differential of a complex conjugated by transports does not depend on how its two indices
are written. -/
theorem _root_.HomologicalComplex.eqToHom_d_eqToHom {V : Type*} [Category V] [HasZeroMorphisms V]
    {ι : Type*} {c : ComplexShape ι} (C : HomologicalComplex V c) {P Q Q' : V} {a a' b b' : ι}
    (ha : a = a') (hb : b = b') (h₁ : P = C.X a) (h₂ : C.X b = Q) (h₁' : P = C.X a')
    (h₂' : C.X b' = Q') (h₃ : Q' = Q) :
    eqToHom h₁ ≫ C.d a b ≫ eqToHom h₂ = (eqToHom h₁' ≫ C.d a' b' ≫ eqToHom h₂') ≫ eqToHom h₃ := by
  subst ha hb h₃
  simp

/-- The differential of the Koszul cochain complex from degree `-(n+1)` is the Koszul
differential `⋀^{n+1} ⟶ ⋀ⁿ`. -/
theorem cochain_d_eq_dNat (n : ℕ) (h : -((n + 1 : ℕ) : ℤ) + 1 = -((n : ℕ) : ℤ)) :
    eqToHom (cochain_X_neg Rc K (n + 1)).symm ≫
        (cochain Rc K).d (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) ≫
          eqToHom (congrArg (cochain Rc K).X h) =
      K.dNat n ≫ eqToHom (cochain_X_neg Rc K n).symm := by
  refine Eq.trans ?_ (congrArg (· ≫ eqToHom (cochain_X_neg Rc K n).symm) (K.chain_d_natCast n))
  exact K.chain.eqToHom_d_eqToHom (a := -(-((n + 1 : ℕ) : ℤ)))
    (b := -(-((n + 1 : ℕ) : ℤ) + 1)) (by omega) (by omega) _ _ _ _ _

/-- **The differential of `𝓗om^•(K, M[0])` on sections**: through the collapses onto
`𝓗om(⋀ⁿ((O♯)ʳ), M)`, it is `(-1)^{n+1}` times precomposition with the Koszul differential. -/
theorem homComplexXIso_hom_app_d (M : StructureSheafModules Rc) (n : ℕ) (U : Opens X)
    (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op U))
    (m : (commVal (Rc := Rc) (A.exteriorPower (n + 1))).obj (op U)) :
    ((homComplexXIso Rc K M (n + 1)).hom.val.app (op U)
        (((homComplex Rc K M).d n (n + 1)).val.app (op U) s)).app (op (Over.mk (𝟙 U))) m =
      (((n : ℕ) : ℤ) + 1).negOnePow •
        ((homComplexXIso Rc K M n).hom.val.app (op U) s).app (op (Over.mk (𝟙 U)))
          ((K.dNat n).val.app (op U) m) := by
  rw [homComplexXIso_hom_app, homComplexXIso_hom_app]
  refine (RingedSite.evalSingle_d (ringedSite Rc) (cochain Rc K) M U U (𝟙 U) (n : ℤ)
    (-((n + 1 : ℕ) : ℤ)) (by omega) s _).trans ?_
  congr 1
  refine (RingedSite.evalSingle_congr (ringedSite Rc) (cochain Rc K) M U U (𝟙 U) (n : ℤ) _
    (-((n : ℕ) : ℤ)) (by omega) _ (by omega) s _).trans ?_
  congr 1
  have h := congrArg (fun g => g.val.app (op U) m)
    (cochain_d_eq_dNat Rc K n (by omega))
  exact h

/-- Every pair of an element of a stalk and an element of the exterior power of the free stalk is
a pair of germs of sections over a common open. -/
private theorem exists_germ_exteriorKoszul {M : StructureSheafModules Rc} (n : ℕ) (x : X)
    {P : modStalk M x → (⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^n
      (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x))) → Prop}
    (h : ∀ (W : Opens X) (hW : x ∈ W) s m, P (germAt M W x hW s)
      (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x (germAt (A.exteriorPower n) W x hW m)))
    (z : modStalk M x) (w : ⋀[↑(TopCat.Presheaf.stalk Rc.obj x)]^n
      (Fin r → ↑(TopCat.Presheaf.stalk Rc.obj x))) : P z w := by
  obtain ⟨w, rfl⟩ := (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x).surjective w
  obtain ⟨U, hxU, s, hz⟩ := Stacks.RegularSequence.exists_germAddHom_eq _ z
  obtain ⟨V, hxV, m, hw⟩ := Stacks.RegularSequence.exists_germAddHom_eq _ w
  have hW : x ∈ (U ⊓ V : Opens X) := ⟨hxU, hxV⟩
  have es := (Stacks.SheafOfModules.germAddHom_resAddHom _ (inf_le_left : U ⊓ V ≤ U) hW s).symm
  have em := (Stacks.SheafOfModules.germAddHom_resAddHom _ (inf_le_right : U ⊓ V ≤ V) hW m).symm
  have hz' := hz.symm.trans es
  have hw' := hw.symm.trans em
  subst hz' hw'
  exact h _ hW _ _

/-- The stalk identification is natural in the target module, on germs over a common open. -/
theorem homComplexStalkEquiv_stalkLin_homMap_germ {M N : StructureSheafModules Rc} (g : M ⟶ N)
    (n : ℕ) (x : X) (W : Opens X) (hW : x ∈ W)
    (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op W))
    (m : (commVal (Rc := Rc) (A.exteriorPower n)).obj (op W)) :
    homComplexStalkEquiv Rc K N n x (Stacks.RegularSequence.stalkLin
        ((RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map g)).f n).val x
        (germAt ((homComplex Rc K M).X n) W x hW s))
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x (germAt (A.exteriorPower n) W x hW m))
      = Stacks.RegularSequence.stalkLin g.val x (homComplexStalkEquiv Rc K M n x
        (germAt ((homComplex Rc K M).X n) W x hW s)
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
          (germAt (A.exteriorPower n) W x hW m))) := by
  refine (congrArg (fun y => homComplexStalkEquiv Rc K N n x y _)
    (Stacks.RegularSequence.stalkLin_germAddHom _ _ hW _)).trans ?_
  refine (homComplexStalkEquiv_germ_germ Rc K N n x W hW _ _).trans ?_
  refine Eq.trans ?_ (congrArg (Stacks.RegularSequence.stalkLin g.val x)
    (homComplexStalkEquiv_germ_germ Rc K M n x W hW s m).symm)
  refine Eq.trans ?_ (Stacks.RegularSequence.stalkLin_germAddHom _ _ hW _).symm
  refine congrArg (germAt N W x hW) ?_
  rw [homComplexXIso_hom_app, homComplexXIso_hom_app]
  exact RingedSite.evalSingle_homMap (ringedSite Rc) (cochain Rc K) g W W (𝟙 W) n _ _ s _

/-- **The stalk identification is natural in the target module.** -/
theorem homComplexStalkEquiv_stalkLin_homMap {M N : StructureSheafModules Rc} (g : M ⟶ N)
    (n : ℕ) (x : X) (z : modStalk ((homComplex Rc K M).X n) x) :
    homComplexStalkEquiv Rc K N n x (Stacks.RegularSequence.stalkLin
        ((RingedSite.homMap (ringedSite Rc) (𝟙 (cochain Rc K))
          ((single (StructureSheafModules Rc) (ComplexShape.up ℤ) 0).map g)).f n).val x z) =
      Stacks.RegularSequence.stalkLin g.val x ∘ₗ homComplexStalkEquiv Rc K M n x z := by
  refine LinearMap.ext fun w => ?_
  induction z, w using exists_germ_exteriorKoszul Rc (A := A) n x with
  | h W hW s m => exact homComplexStalkEquiv_stalkLin_homMap_germ Rc K g n x W hW s m

variable (f : Fin r → ↑(Rc.obj.obj (op (⊤ : Opens ↥X))))
  (hφ : ∀ k : Fin r,
    ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)).freeHomEquiv φ
      (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)

include hφ in
/-- The differential of `𝓗om^•(K, M[0])` at a stalk, on germs over a common open. -/
theorem homComplexStalkEquiv_stalkLin_d_germ (M : StructureSheafModules Rc) (n : ℕ) (x : X)
    (W : Opens X) (hW : x ∈ W) (s : (commVal (Rc := Rc) ((homComplex Rc K M).X n)).obj (op W))
    (m : (commVal (Rc := Rc) (A.exteriorPower (n + 1))).obj (op W)) :
    homComplexStalkEquiv Rc K M (n + 1) x
        (Stacks.RegularSequence.stalkLin ((homComplex Rc K M).d n (n + 1)).val x
          (germAt ((homComplex Rc K M).X n) W x hW s))
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x
          (germAt (A.exteriorPower (n + 1)) W x hW m)) =
      ((((n : ℕ) : ℤ) + 1).negOnePow • (homComplexStalkEquiv Rc K M n x
        (germAt ((homComplex Rc K M).X n) W x hW s) ∘ₗ
        Koszul.d (Koszul.seqDual fun k =>
          TopCat.Presheaf.germ Rc.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n))
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x
          (germAt (A.exteriorPower (n + 1)) W x hW m)) := by
  have hd : Stacks.RegularSequence.stalkLin ((homComplex Rc K M).d n (n + 1)).val x
      (germAt ((homComplex Rc K M).X n) W x hW s) =
      germAt ((homComplex Rc K M).X (n + 1)) W x hW
        (((homComplex Rc K M).d n (n + 1)).val.app (op W) s) :=
    Stacks.RegularSequence.stalkLin_germAddHom _ _ hW s
  have hk : Koszul.d (Koszul.seqDual fun k =>
        TopCat.Presheaf.germ Rc.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n
      (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x
        (germAt (A.exteriorPower (n + 1)) W x hW m)) =
      Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
        (germAt (A.exteriorPower n) W x hW ((K.dNat n).val.app (op W) m)) := by
    rw [← exteriorKoszulStalkEquiv_stalkLin K f hφ n x]
    exact congrArg _ (Stacks.RegularSequence.stalkLin_germAddHom _ _ hW m)
  refine (congrArg (fun z => homComplexStalkEquiv Rc K M (n + 1) x z
    (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x
      (germAt (A.exteriorPower (n + 1)) W x hW m))) hd).trans ?_
  refine (homComplexStalkEquiv_germ_germ Rc K M (n + 1) x W hW _ m).trans ?_
  refine (congrArg (germAt M W x hW) (homComplexXIso_hom_app_d Rc K M n W s m)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => (((n : ℕ) : ℤ) + 1).negOnePow •
    homComplexStalkEquiv Rc K M n x (germAt ((homComplex Rc K M).X n) W x hW s) z) hk.symm)
  refine Eq.trans ?_ (congrArg (fun z => (((n : ℕ) : ℤ) + 1).negOnePow • z)
    (homComplexStalkEquiv_germ_germ Rc K M n x W hW s _).symm)
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (TopCat.Presheaf.germ (C := Ab) (commVal M).presheaf W x hW).hom _ _

include hφ in
/-- **The differential of `𝓗om^•(K, M[0])` at a stalk** is `(-1)^{n+1}` times the transpose of
the ring-level Koszul differential of the germs of the sequence. -/
theorem homComplexStalkEquiv_stalkLin_d (M : StructureSheafModules Rc) (n : ℕ) (x : X)
    (z : modStalk ((homComplex Rc K M).X n) x) :
    homComplexStalkEquiv Rc K M (n + 1) x
        (Stacks.RegularSequence.stalkLin ((homComplex Rc K M).d n (n + 1)).val x z) =
      (((n : ℕ) : ℤ) + 1).negOnePow • (homComplexStalkEquiv Rc K M n x z ∘ₗ
        Koszul.d (Koszul.seqDual fun k =>
          TopCat.Presheaf.germ Rc.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) n) := by
  refine LinearMap.ext fun w => ?_
  induction z, w using exists_germ_exteriorKoszul Rc (A := A) (n + 1) x with
  | h W hW s m => exact homComplexStalkEquiv_stalkLin_d_germ Rc K f hφ M n x W hW s m

end Stacks.RegularSequence.KoszulChainData
