module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProjectionFormulaUnitHomCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardDerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquivAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedAcyclicPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.Algebra.Homology.HomBicomplexExt
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplex

/-!
# Ext from a perfect object into `𝒢^• ⊗ f^*ℱ` as cohomology on the base (Stacks 08JN)

Let `B` be a Noetherian algebraic space, `f : X ⟶ B` locally of finite type and quasi-separated,
`E` a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat
over `B`, with support proper over `B`, and `K = Rf_* RSheafHom(E, 𝒢^•)`.  This file constructs,
for `M ∈ D_QCoh(𝒪_B)`, the identification

`Hom(𝒪_B, K ⊗^L M) ≅ Hom(E, 𝒢^• ⊗^L Lf^*M)`,

naturally in `M`, and its shifted form `H^i(B, K ⊗^L M) ≅ Ext^i(E, 𝒢^• ⊗^L Lf^*M)`, compatibly
with the boundary maps of triangles.  This is the proof of Stacks 08JN with Stacks 0A1M unfolded:
`RSheafHom(E, 𝒢^•) = E^∨ ⊗^L 𝒢^•`, the projection formula of Stacks 08IN on a quasi-compact open
neighbourhood of the support of `𝒢^•`, the associativity of `⊗^L`, and
`Hom(𝒪_X, E^∨ ⊗^L W) = Hom(E, W)`.

## Main definitions

* `AlgebraicGeometry.Space.extPerfectUnitHomNatTrans`: `Hom(𝒪_B, K ⊗^L -) ⟶ Hom(E, Ψ -)`, an
  isomorphism on `D_QCoh(𝒪_B)`, where `Ψ M = 𝒢^• ⊗^L Lf^*M`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

/-- An abstract form of the compatibility of a shifted natural transformation with boundary
maps: for `Φ : F ⋙ G ⟶ F' ⋙ G'` with `F`, `F'` commuting with the shifts, the transformations
`G (F(-)[i]) ⟶ G' (F'(-)[i])` obtained from `Φ` at `-[i]` and the commutation isomorphisms carry
composition with `(F a)[i]` (followed by `-[1][i] ≅ -[1 + i]`) to composition with `(F' a)[i]`. -/
theorem _root_.CategoryTheory.Functor.shiftedNatTrans_delta_aux {C D D' A : Type*} [Category C]
    [Category D] [Category D'] [Category A] [HasShift C ℤ] [HasShift D ℤ] [HasShift D' ℤ]
    (F : C ⥤ D) (F' : C ⥤ D') [F.CommShift ℤ] [F'.CommShift ℤ] (G : D ⥤ A) (G' : D' ⥤ A)
    (Φ : F ⋙ G ⟶ F' ⋙ G') {M₁ M₃ : C} (a : M₃ ⟶ M₁⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) :
    G.map ((F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' D 1 i j h).inv.app (F.obj M₁)) ≫
        (G.map ((F.commShiftIso j).inv.app M₁) ≫ Φ.app (M₁⟦j⟧) ≫
          G'.map ((F'.commShiftIso j).hom.app M₁)) =
      (G.map ((F.commShiftIso i).inv.app M₃) ≫ Φ.app (M₃⟦i⟧) ≫
          G'.map ((F'.commShiftIso i).hom.app M₃)) ≫
        G'.map ((F'.map a ≫ (F'.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' D' 1 i j h).inv.app (F'.obj M₁)) := by
  have kF2 : (F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
        (shiftFunctorAdd' D 1 i j h).inv.app (F.obj M₁) ≫ (F.commShiftIso j).inv.app M₁ =
      (F.commShiftIso i).inv.app M₃ ≫ F.map (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app M₁) := by
    rw [← cancel_epi ((F.commShiftIso i).hom.app M₃), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% (Functor.map_comp_shiftFunctorAdd'_inv_commShiftIso F a i j h),
      Iso.hom_inv_id_app]
    simp
  have hΦ := Φ.naturality (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app M₁)
  simp only [Functor.comp_map] at hΦ
  calc G.map ((F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' D 1 i j h).inv.app (F.obj M₁)) ≫
        (G.map ((F.commShiftIso j).inv.app M₁) ≫ Φ.app (M₁⟦j⟧) ≫
          G'.map ((F'.commShiftIso j).hom.app M₁))
      = G.map ((F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' D 1 i j h).inv.app (F.obj M₁) ≫ (F.commShiftIso j).inv.app M₁) ≫
        Φ.app (M₁⟦j⟧) ≫ G'.map ((F'.commShiftIso j).hom.app M₁) := by
          simp only [Functor.map_comp, Category.assoc]
    _ = G.map ((F.commShiftIso i).inv.app M₃) ≫
        (G.map (F.map (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app M₁)) ≫ Φ.app (M₁⟦j⟧)) ≫
          G'.map ((F'.commShiftIso j).hom.app M₁) := by
          rw [kF2, G.map_comp]
          simp only [Category.assoc]
    _ = G.map ((F.commShiftIso i).inv.app M₃) ≫ Φ.app (M₃⟦i⟧) ≫
        G'.map (F'.map (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app M₁) ≫
          (F'.commShiftIso j).hom.app M₁) := by
          rw [hΦ, G'.map_comp]
          simp only [Category.assoc]
    _ = _ := by
          rw [Functor.map_comp_shiftFunctorAdd'_inv_commShiftIso F' a i j h, G'.map_comp]
          simp only [Category.assoc]

/-- `d ≫ α ≫ μ = (α' ≫ μ') ≫ ν` from `d ≫ α = α' ≫ m` and `m ≫ μ = μ' ≫ ν`. -/
theorem _root_.CategoryTheory.comp_comp_eq_of_eq_of_eq {C : Type*} [Category C]
    {P Q R S P' R' : C} (d : P ⟶ Q) (α : Q ⟶ R) (μ : R ⟶ S) (α' : P ⟶ P') (m : P' ⟶ R)
    (μ' : P' ⟶ R') (ν : R' ⟶ S) (h₁ : d ≫ α = α' ≫ m) (h₂ : m ≫ μ = μ' ≫ ν) :
    d ≫ α ≫ μ = (α' ≫ μ') ≫ ν := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Transport of a commutative square along a fully faithful functor: if `U x ≫ e' = e ≫ U y`
then `x ≫ preimage e' = preimage e ≫ y`. -/
theorem _root_.CategoryTheory.Functor.FullyFaithful.preimageIso_hom_comm {C D : Type*}
    [Category C] [Category D] {U : C ⥤ D} (hU : U.FullyFaithful) {X X' Y Y' : C}
    (e : U.obj X ≅ U.obj Y) (e' : U.obj X' ≅ U.obj Y') (x : X ⟶ X') (y : Y ⟶ Y')
    (h : U.map x ≫ e'.hom = e.hom ≫ U.map y) :
    x ≫ (hU.preimageIso e').hom = (hU.preimageIso e).hom ≫ y :=
  hU.map_injective (by simpa using h)

/-- Pasting two commutative squares horizontally. -/
theorem _root_.CategoryTheory.comp_comp_eq_comp_comp_of_eq_of_eq {C : Type*} [Category C]
    {P P' Q Q' R R' : C} (x : P ⟶ P') (e₁ : P ⟶ Q) (e₁' : P' ⟶ Q') (y : Q ⟶ Q') (e₂ : Q ⟶ R)
    (e₂' : Q' ⟶ R') (z : R ⟶ R') (h₁ : x ≫ e₁' = e₁ ≫ y) (h₂ : y ≫ e₂' = e₂ ≫ z) :
    x ≫ e₁' ≫ e₂' = (e₁ ≫ e₂) ≫ z :=
  comp_comp_eq_of_eq_of_eq _ _ _ _ _ _ _ h₁ h₂

/-- A square through the preimage, under a fully faithful functor, of a composite of an
isomorphism with the image of an isomorphism. -/
theorem _root_.CategoryTheory.Functor.FullyFaithful.preimageIso_trans_mapIso_hom_comm
    {C D : Type*} [Category C] [Category D] {U : C ⥤ D} (hU : U.FullyFaithful)
    {H H' W W' X X' : C} (L : U.obj H ≅ U.obj W) (L' : U.obj H' ≅ U.obj W') (t : W ≅ X)
    (t' : W' ≅ X') (hm : H ⟶ H') (wm : W ⟶ W') (xm : X ⟶ X')
    (hL : U.map hm ≫ L'.hom = L.hom ≫ U.map wm) (ht : wm ≫ t'.hom = t.hom ≫ xm) :
    hm ≫ (hU.preimageIso (L' ≪≫ U.mapIso t')).hom =
      (hU.preimageIso (L ≪≫ U.mapIso t)).hom ≫ xm := by
  apply hU.preimageIso_hom_comm
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [reassoc_of% hL, ← U.map_comp, ht, U.map_comp, Category.assoc]

/-- The image of a commutative square under a functor. -/
theorem _root_.CategoryTheory.Functor.map_comp_eq_map_comp_of_eq {C D : Type*} [Category C]
    [Category D] (G : C ⥤ D) {P Q Q' R : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ Q'} {d : Q' ⟶ R}
    (h : a ≫ b = c ≫ d) : G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, h, G.map_comp]

/-- Shifting a commutative square `a ≫ t[1] = t' ≫ d` by `i` and composing with
`-[1][i] ≅ -[1 + i]`. -/
theorem _root_.CategoryTheory.shift_comp_shiftFunctorAdd'_inv_eq {C : Type*} [Category C]
    [HasShift C ℤ] {P Q R Z : C} {a : P ⟶ Q⟦(1 : ℤ)⟧} {t : Q ⟶ R} {t' : P ⟶ Z}
    {d : Z ⟶ R⟦(1 : ℤ)⟧} (h : a ≫ t⟦(1 : ℤ)⟧' = t' ≫ d) (i j : ℤ) (hij : 1 + i = j) :
    (a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j hij).inv.app Q) ≫ t⟦j⟧' =
      t'⟦i⟧' ≫ (d⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j hij).inv.app R) := by
  have hn := (shiftFunctorAdd' C 1 i j hij).inv.naturality t
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp,
    Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

section Comparison

variable (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hG : FlatProperSupportComplex B S hS f hf G)

attribute [local instance] isGrothendieckAbelian_modules in
/-- The object `K = Rf_* RSheafHom(E, 𝒢^•)` of Stacks 0DKK and 08JN. -/
abbrev extPerfectDirectImageObj :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
    (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (DerivedCategory.Q.obj G))

/-- The functor `M ↦ 𝒢^• ⊗^L Lf^*M` from `D(𝒪_Y)` to `D(𝒪_X)`. -/
abbrev extPerfectCoefficientFunctor :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  smallEtaleDerivedModulePullback B S hS f ⋙
    (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)

attribute [local instance] isGrothendieckAbelian_modules in
include hfqs hY hE hG in
/-- The projection formula on morphisms out of the structure sheaf for `A = E^∨ ⊗^L 𝒢^•`. -/
theorem exists_unitHomProjectionFormula_extPerfect :
    ∃ θ : (smallEtaleDerivedTensor B S hS Y).obj
          ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
            (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj
              (DerivedCategory.Q.obj G))) ⋙
          preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
        smallEtaleDerivedModulePullback B S hS f ⋙
          (smallEtaleDerivedTensor B S hS X).obj
            (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj
              (DerivedCategory.Q.obj G)) ⋙
          preadditiveCoyoneda.obj (op (structureDerived X)),
      ∀ M, QcohDerived B S hS Y M → IsIso (θ.app M) := by
  obtain ⟨Z, hZcl, hZp, hGZ⟩ := hG.properSupport
  have hZc : IsCompact Z := isCompact_of_isProperOver B S hS X.2 Y.2 hY.1 f.hom hf Z hZcl hZp
  have hQG : QcohDerived B S hS X (DerivedCategory.Q.obj G) :=
    (qcohDerived_Q_obj_iff B S hS G).2 fun q => isQuasicoherentOnSite_homology B S hS G
      (fun n => (hG.isCoherent n).toIsQuasicoherentOnSite) q
  have hA := qcohDerived_smallEtaleDerivedTensor X _ _
    (qcohDerived_of_isPerfect B S hS X _ (isPerfect_smallEtaleDerivedDual B S hS X E hE)) hQG
  exact exists_unitHomProjectionFormula_of_cohomologySupportedOn B S hS hTop f hfqs hY.2.1 _ hA Z
    hZcl hZc (cohomologySupportedOn_derivedTensor B S hS X (smallEtaleDerivedTensorProduct B S hS X)
      _ G Z hGZ)

/-- A projection formula on morphisms out of the structure sheaf for `A = E^∨ ⊗^L 𝒢^•`. -/
def extPerfectProjectionFormula :=
  (exists_unitHomProjectionFormula_extPerfect B S hS hTop f hf hfqs hY E hE G hG).choose

/-- `extPerfectProjectionFormula` is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_extPerfectProjectionFormula_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((extPerfectProjectionFormula B S hS hTop f hf hfqs hY E hE G hG).app M) :=
  (exists_unitHomProjectionFormula_extPerfect B S hS hTop f hf hfqs hY E hE G hG).choose_spec M hM

/-- **`Hom(𝒪_Y, K ⊗^L -) ⟶ Hom(E, 𝒢^• ⊗^L Lf^*-)`**, as a natural transformation of functors
`D(𝒪_Y) ⥤ Ab`: `K ≅ Rf_*(E^∨ ⊗^L 𝒢^•)`, the projection formula, and the associativity of `⊗^L`
with `Hom(𝒪_X, E^∨ ⊗^L W) = Hom(E, W)`.  It is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`
(`AlgebraicGeometry.Space.isIso_extPerfectUnitHomNatTrans_app`). -/
def extPerfectUnitHomNatTrans :
    (smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G) ⋙
        preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      extPerfectCoefficientFunctor B S hS f G ⋙ preadditiveCoyoneda.obj (op E) :=
  Functor.whiskerRight ((smallEtaleDerivedTensor B S hS Y).map
      (derivedSheafHomPushforwardIsoTensorDual B S hS f E hE (DerivedCategory.Q.obj G)).hom)
      (preadditiveCoyoneda.obj (op (structureDerived Y))) ≫
    extPerfectProjectionFormula B S hS hTop f hf hfqs hY E hE G hG ≫
    Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleUnitTensorDualAssocNatIso B S hS X E hE (DerivedCategory.Q.obj G)).hom

/-- `extPerfectUnitHomNatTrans` is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_extPerfectUnitHomNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app M) := by
  have hK : IsIso (((smallEtaleDerivedTensor B S hS Y).map (derivedSheafHomPushforwardIsoTensorDual
      B S hS f E hE (DerivedCategory.Q.obj G)).hom).app M) :=
    (((smallEtaleDerivedTensor B S hS Y).mapIso (derivedSheafHomPushforwardIsoTensorDual
      B S hS f E hE (DerivedCategory.Q.obj G))).app M).isIso_hom
  have hA := NatIso.hom_app_isIso
    (smallEtaleUnitTensorDualAssocNatIso B S hS X E hE (DerivedCategory.Q.obj G))
    ((smallEtaleDerivedModulePullback B S hS f).obj M)
  have hK' : IsIso ((preadditiveCoyoneda.obj (op (structureDerived Y))).map
      (((smallEtaleDerivedTensor B S hS Y).map (derivedSheafHomPushforwardIsoTensorDual
        B S hS f E hE (DerivedCategory.Q.obj G)).hom).app M)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' hK' (IsIso.comp_isIso'
    (isIso_extPerfectProjectionFormula_app B S hS hTop f hf hfqs hY E hE G hG M hM) hA)

/-- **`Hom(𝒪_Y, (K ⊗^L -)[i]) ⟶ Ext^i(E, 𝒢^• ⊗^L Lf^*-)`**, as a natural transformation of
functors `D(𝒪_Y) ⥤ Ab`: `extPerfectUnitHomNatTrans` at `-[i]`, read through the commutation of
`K ⊗^L -` and of `𝒢^• ⊗^L Lf^*-` with the shift by `i`. -/
def extPerfectShiftedNatTrans (i : ℤ) :
    (smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G) ⋙
        shiftFunctor _ i ⋙ preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      extPerfectCoefficientFunctor B S hS f G ⋙ shiftFunctor _ i ⋙
        preadditiveCoyoneda.obj (op E) :=
  (Functor.isoWhiskerRight (((smallEtaleDerivedTensor B S hS Y).obj
      (extPerfectDirectImageObj B S hS f E G)).commShiftIso i).symm
      (preadditiveCoyoneda.obj (op (structureDerived Y)))).hom ≫
    Functor.whiskerLeft (shiftFunctor _ i)
      (extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG) ≫
    (Functor.isoWhiskerRight ((extPerfectCoefficientFunctor B S hS f G).commShiftIso i)
      (preadditiveCoyoneda.obj (op E))).hom

/-- The component of `extPerfectShiftedNatTrans` at `M` is that of `extPerfectUnitHomNatTrans`
at `M[i]`, between the commutation isomorphisms with the shift by `i`. -/
theorem extPerfectShiftedNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (i : ℤ) :
    (extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M =
      (preadditiveCoyoneda.obj (op (structureDerived Y))).map
          ((((smallEtaleDerivedTensor B S hS Y).obj
            (extPerfectDirectImageObj B S hS f E G)).commShiftIso i).inv.app M) ≫
        (extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app (M⟦i⟧) ≫
        (preadditiveCoyoneda.obj (op E)).map
          (((extPerfectCoefficientFunctor B S hS f G).commShiftIso i).hom.app M) :=
  rfl

/-- `extPerfectShiftedNatTrans` is an isomorphism at every `M ∈ D_QCoh(𝒪_Y)`. -/
theorem isIso_extPerfectShiftedNatTrans_app
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) (i : ℤ) :
    IsIso ((extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M) := by
  rw [extPerfectShiftedNatTrans_app]
  have h1 := isIso_extPerfectUnitHomNatTrans_app B S hS hTop f hf hfqs hY E hE G hG (M⟦i⟧)
    (qcohDerived_shift M i hM)
  have h0 : IsIso ((preadditiveCoyoneda.obj (op (structureDerived Y))).map
      ((((smallEtaleDerivedTensor B S hS Y).obj
        (extPerfectDirectImageObj B S hS f E G)).commShiftIso i).inv.app M)) :=
    Functor.map_isIso _ _
  have h2 : IsIso ((preadditiveCoyoneda.obj (op E)).map
      (((extPerfectCoefficientFunctor B S hS f G).commShiftIso i).hom.app M)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' h0 (IsIso.comp_isIso' h1 h2)

/-- **The shifted comparison carries the boundary maps of `K ⊗^L -` to those of
`𝒢^• ⊗^L Lf^*-`**: for `a : M₃ ⟶ M₁[1]` with `M₁, M₃ ∈ D_QCoh(𝒪_Y)`, composing with
`(K ⊗^L a)[i]` on `Hom(𝒪_Y, (K ⊗^L -)[•])` corresponds to composing with
`(𝒢^• ⊗^L Lf^*a)[i]` on `Ext^•(E, 𝒢^• ⊗^L Lf^*-)`, each followed by the commutation with the
shift by `1` and `-[1][i] ≅ -[1 + i]`. -/
theorem extPerfectShiftedNatTrans_delta
    {M₁ M₃ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (a : M₃ ⟶ M₁⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) :
    (preadditiveCoyoneda.obj (op (structureDerived Y))).map
        ((((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).map a ≫
          (((smallEtaleDerivedTensor B S hS Y).obj
            (extPerfectDirectImageObj B S hS f E G)).commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' _ 1 i j h).inv.app (((smallEtaleDerivedTensor B S hS Y).obj
            (extPerfectDirectImageObj B S hS f E G)).obj M₁)) ≫
        (extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG j).app M₁ =
      (extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M₃ ≫
        (preadditiveCoyoneda.obj (op E)).map
          (((extPerfectCoefficientFunctor B S hS f G).map a ≫
            ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i j h).inv.app
              ((extPerfectCoefficientFunctor B S hS f G).obj M₁)) := by
  rw [extPerfectShiftedNatTrans_app, extPerfectShiftedNatTrans_app]
  exact Functor.shiftedNatTrans_delta_aux _ _ _ _ _ a i j h

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- **`H^i(Y, K ⊗^L M) ≅ Ext^i(E, 𝒢^• ⊗^L Lf^*M)` for `M ∈ D_QCoh(𝒪_Y)`**, read through the
universe lift of `AlgebraicGeometry.Space.cohomologyIsoUnitHomShift`. -/
def extPerfectCohomologyIsoLifted
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) (i : ℤ) :
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) i ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).obj
        (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).obj M) ≅
      AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.obj ((preadditiveCoyoneda.obj (op E)).obj
        (((extPerfectCoefficientFunctor B S hS f G).obj M)⟦i⟧)) :=
  (cohomologyIsoUnitHomShift Y i).app
      (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).obj M) ≪≫
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.mapIso
      (@asIso _ _ _ _ ((extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).app M)
        (isIso_extPerfectShiftedNatTrans_app B S hS hTop f hf hfqs hY E hE G hG M hM i))

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- **The identification `H^i(Y, K ⊗^L M) ≅ Ext^i(E, 𝒢^• ⊗^L Lf^*M)` is compatible with boundary
maps**: for a triangle `M₁ ⟶ M₂ ⟶ M₃ ⟶ M₁[1]` of `D_QCoh(𝒪_Y)` (only `M₁`, `M₃` and the third
morphism enter), the boundary map of cohomology of `K ⊗^L` the triangle corresponds to composition
with `(𝒢^• ⊗^L Lf^*` of the third morphism`)[i]`. -/
theorem extPerfectCohomologyIsoLifted_homologySequenceδ
    (T : Pretriangulated.Triangle
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))))
    (h₁ : QcohDerived B S hS Y T.obj₁) (h₃ : QcohDerived B S hS Y T.obj₃) (i j : ℤ)
    (h : i + 1 = j) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
          ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
            (((smallEtaleDerivedTensor B S hS Y).obj
              (extPerfectDirectImageObj B S hS f E G)).mapTriangle.obj T)) i j h) ≫
        (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG T.obj₁ h₁ j).hom =
      (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG T.obj₃ h₃ i).hom ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map ((preadditiveCoyoneda.obj (op E)).map
          (((extPerfectCoefficientFunctor B S hS f G).map T.mor₃ ≫
            ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app T.obj₁)⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i j (by omega)).inv.app
              ((extPerfectCoefficientFunctor B S hS f G).obj T.obj₁))) := by
  have hδ := cohomologyIsoUnitHomShift_homologySequenceδ Y
    (((smallEtaleDerivedTensor B S hS Y).obj
      (extPerfectDirectImageObj B S hS f E G)).mapTriangle.obj T) i j h
  have hΦ := congrArg (AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map)
    (extPerfectShiftedNatTrans_delta B S hS hTop f hf hfqs hY E hE G hG T.mor₃ i j (by omega))
  rw [AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map_comp,
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map_comp] at hΦ
  exact comp_comp_eq_of_eq_of_eq _ _ _ _ _ _ _ hδ hΦ

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- **The identification `H^i(Y, K ⊗^L M) ≅ Ext^i(E, 𝒢^• ⊗^L Lf^*M)` is natural in
`M ∈ D_QCoh(𝒪_Y)`.** -/
theorem extPerfectCohomologyIsoLifted_naturality
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hM : QcohDerived B S hS Y M) (hM' : QcohDerived B S hS Y M') (q : M ⟶ M') (i : ℤ) :
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2 ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) i ⋙
        forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
          AddCommGrpCat.{u + 1} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u + 1}).map
        (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).map q) ≫
        (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG M' hM' i).hom =
      (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG M hM i).hom ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map ((preadditiveCoyoneda.obj (op E)).map
          (((extPerfectCoefficientFunctor B S hS f G).map q)⟦i⟧')) := by
  have hα := (cohomologyIsoUnitHomShift Y i).hom.naturality
    (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).map q)
  have hΦ := congrArg (AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map)
    ((extPerfectShiftedNatTrans B S hS hTop f hf hfqs hY E hE G hG i).naturality q)
  simp only [Functor.map_comp] at hΦ
  exact comp_comp_eq_of_eq_of_eq _ _ _ _ _ _ _ hα hΦ

/-- The class of a quasi-coherent module placed in degree zero lies in `D_QCoh`. -/
theorem qcohDerived_Q_singleFunctor_obj {Z : AlgebraicSpaces B S hS}
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    (hF : F.IsQuasicoherentOnSite) :
    QcohDerived B S hS Z (DerivedCategory.Q.obj
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
        (ComplexShape.up ℤ) 0).obj F)) := by
  refine (qcohDerived_Q_obj_iff B S hS _).2 fun q => ?_
  rcases eq_or_ne q 0 with rfl | hq
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((HomologicalComplex.singleObjHomologySelfIso _ 0 F).symm) hF
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (HomologicalComplex.isZero_single_obj_homology _ 0 F q hq)

/-- A module `ℱ` on `Y` placed in degree zero, as an object of `D(𝒪_Y)`. -/
abbrev extPerfectSingle (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  DerivedCategory.Q.obj ((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)

/-- The class in `D(𝒪_X)` of the complex `𝒢^• ⊗ f^*ℱ`. -/
abbrev extPerfectCoefficientObj (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj ((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F))

/-- A morphism of modules on `Y` placed in degree zero, as a morphism of `D(𝒪_Y)`. -/
abbrev extPerfectSingleMap {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
    (q : F ⟶ F') : extPerfectSingle B S hS F ⟶ extPerfectSingle B S hS F' :=
  DerivedCategory.Q.map ((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map q)

/-- The morphism `𝒢^• ⊗ f^*ℱ ⟶ 𝒢^• ⊗ f^*ℱ'` of `D(𝒪_X)` induced by `ℱ ⟶ ℱ'`. -/
abbrev extPerfectCoefficientMap {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
    (q : F ⟶ F') : extPerfectCoefficientObj B S hS f G F ⟶ extPerfectCoefficientObj B S hS f G F' :=
  DerivedCategory.Q.map ((tensorPullbackComplex f G).map ((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map q))

/-- A comparison of coefficients at a module placed in degree zero. -/
abbrev extPerfectCoefficientComparison
    (τ : DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (extPerfectCoefficientFunctor B S hS f G).obj (extPerfectSingle B S hS F) ⟶
      extPerfectCoefficientObj B S hS f G F :=
  τ.app ((HomologicalComplex.single
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- The group `H^i(Y, K ⊗^L ℱ)`, read in abelian groups. -/
abbrev extPerfectBaseCohomology (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (i : ℤ) : AddCommGrpCat.{u + 1} :=
  (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
      AddCommGrpCat.{u + 1}).obj (((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).obj
      ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj
        (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).obj
          (extPerfectSingle B S hS F))))

/-- The group `Ext^i(E, 𝒢^• ⊗ f^*ℱ) = Hom(E, (𝒢^• ⊗ f^*ℱ)[i])`. -/
abbrev extPerfectExtGroup (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (i : ℤ) : AddCommGrpCat.{u + 1} :=
  (preadditiveCoyoneda.obj (op E)).obj ((extPerfectCoefficientObj B S hS f G F)⟦i⟧)

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- `H^i(Y, K ⊗^L ℱ) ≅ Ext^i(E, 𝒢^• ⊗ f^*ℱ)` from a comparison `τ` of coefficients. -/
abbrev extPerfectCohomologyIsoOfCoefficient
    (τ : DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) (i : ℤ) :
    extPerfectBaseCohomology B S hS f E G F i ≅ extPerfectExtGroup B S hS f E G F i :=
  AddCommGrpCat.uliftFunctorFullyFaithful.preimageIso
    (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG
        (extPerfectSingle B S hS F) (qcohDerived_Q_singleFunctor_obj B S hS F hF) i ≪≫
      AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.mapIso ((preadditiveCoyoneda.obj (op E)).mapIso
        ((shiftFunctor _ i).mapIso (@asIso _ _ _ _ (extPerfectCoefficientComparison B S hS f G τ F)
          (hτ F)))))

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- The isomorphism `extPerfectCohomologyIsoOfCoefficient` is natural in the quasi-coherent
module `ℱ`: it commutes with the maps induced by a morphism `ℱ ⟶ ℱ'`. -/
theorem extPerfectCohomologyIsoOfCoefficient_naturality
    (τ : DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ) :
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
        AddCommGrpCat.{u + 1}).map (((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).map
        ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
          (((smallEtaleDerivedTensor B S hS Y).obj (extPerfectDirectImageObj B S hS f E G)).map
            (extPerfectSingleMap B S hS q)))) ≫
      (extPerfectCohomologyIsoOfCoefficient B S hS hTop f hf hfqs hY E hE G hG τ hτ F' hF' i).hom =
    (extPerfectCohomologyIsoOfCoefficient B S hS hTop f hf hfqs hY E hE G hG τ hτ F hF i).hom ≫
      (preadditiveCoyoneda.obj (op E)).map ((extPerfectCoefficientMap B S hS f G q)⟦i⟧') := by
  have hτq : (extPerfectCoefficientFunctor B S hS f G).map (extPerfectSingleMap B S hS q) ≫
      extPerfectCoefficientComparison B S hS f G τ F' =
      extPerfectCoefficientComparison B S hS f G τ F ≫ extPerfectCoefficientMap B S hS f G q :=
    τ.naturality _
  exact Functor.FullyFaithful.preimageIso_trans_mapIso_hom_comm
    AddCommGrpCat.uliftFunctorFullyFaithful _ _ _ _ _ _ _
    (extPerfectCohomologyIsoLifted_naturality B S hS hTop f hf hfqs hY E hE G hG
      (qcohDerived_Q_singleFunctor_obj B S hS F hF) (qcohDerived_Q_singleFunctor_obj B S hS F' hF')
      (extPerfectSingleMap B S hS q) i)
    (Functor.map_comp_eq_map_comp_of_eq (shiftFunctor _ i ⋙ preadditiveCoyoneda.obj (op E)) hτq)

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- The boundary map `H^i(Y, K ⊗^L ℱ₃) ⟶ H^{i+1}(Y, K ⊗^L ℱ₁)` of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on `Y`: the connecting morphism of cohomology of `RΓ` of
`K ⊗^L` the distinguished triangle of the sequence. -/
abbrev extPerfectBaseDelta
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) (i j : ℤ) (h : i + 1 = j) :
    extPerfectBaseCohomology B S hS f E G T.X₃ i ⟶ extPerfectBaseCohomology B S hS f E G T.X₁ j :=
  (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
    AddCommGrpCat.{u + 1}).map ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).homologySequenceδ
    ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).mapTriangle.obj
      (((smallEtaleDerivedTensor B S hS Y).obj
        (extPerfectDirectImageObj B S hS f E G)).mapTriangle.obj
        (DerivedCategory.triangleOfSES (hT.map_of_exact (HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ)
            0))))) i j h)

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- `extPerfectCohomologyIsoLifted_homologySequenceδ` at the triangle of a short exact sequence of
modules placed in degree zero. -/
theorem extPerfectCohomologyIsoLifted_homologySequenceδ_shortExact
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
    (i j : ℤ) (h : i + 1 = j) :
    AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map
        (extPerfectBaseDelta B S hS f E G T hT i j h) ≫
        (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG
          (extPerfectSingle B S hS T.X₁) (qcohDerived_Q_singleFunctor_obj B S hS T.X₁ h₁) j).hom =
      (extPerfectCohomologyIsoLifted B S hS hTop f hf hfqs hY E hE G hG
          (extPerfectSingle B S hS T.X₃) (qcohDerived_Q_singleFunctor_obj B S hS T.X₃ h₃) i).hom ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u + 1}.map ((preadditiveCoyoneda.obj (op E)).map
          (((extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ
              (hT.map_of_exact (HomologicalComplex.single
                (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ)
                  0))) ≫
            ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
              (extPerfectSingle B S hS T.X₁))⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i j (by omega)).inv.app
              ((extPerfectCoefficientFunctor B S hS f G).obj (extPerfectSingle B S hS T.X₁)))) :=
  extPerfectCohomologyIsoLifted_homologySequenceδ B S hS hTop f hf hfqs hY E hE G hG
    (DerivedCategory.triangleOfSES (hT.map_of_exact (HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)))
    (qcohDerived_Q_singleFunctor_obj B S hS T.X₁ h₁)
    (qcohDerived_Q_singleFunctor_obj B S hS T.X₃ h₃) i j h

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
/-- The isomorphism `extPerfectCohomologyIsoOfCoefficient` carries the boundary map
`extPerfectBaseDelta` of a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of quasi-coherent modules
to the map on `Ext^•(E, -)` induced by the boundary map of the distinguished triangle of the
short exact sequence `0 ⟶ 𝒢^• ⊗ f^*ℱ₁ ⟶ 𝒢^• ⊗ f^*ℱ₂ ⟶ 𝒢^• ⊗ f^*ℱ₃ ⟶ 0`. -/
theorem extPerfectCohomologyIsoOfCoefficient_delta
    (τ : DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hδ : ∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (hT : T.ShortExact),
      (extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ
          (hT.map_of_exact (HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0))) ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (extPerfectSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
        DerivedCategory.triangleOfSESδ (hex T hT))
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
    (i j : ℤ) (h : i + 1 = j) :
    extPerfectBaseDelta B S hS f E G T hT i j h ≫
      (extPerfectCohomologyIsoOfCoefficient B S hS hTop f hf hfqs hY E hE G hG τ hτ T.X₁ h₁ j).hom =
    (extPerfectCohomologyIsoOfCoefficient B S hS hTop f hf hfqs hY E hE G hG τ hτ T.X₃ h₃ i).hom ≫
      (preadditiveCoyoneda.obj (op E)).map ((DerivedCategory.triangleOfSESδ (hex T hT))⟦i⟧' ≫
        (shiftFunctorAdd' _ 1 i j (by omega)).inv.app
          (extPerfectCoefficientObj B S hS f G T.X₁)) := by
  have hδT : ((extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ
        (hT.map_of_exact (HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0))) ≫
      ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
        (extPerfectSingle B S hS T.X₁)) ≫
      (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
    extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
      DerivedCategory.triangleOfSESδ (hex T hT) :=
    (Category.assoc _ _ _).trans (hδ T hT)
  exact Functor.FullyFaithful.preimageIso_trans_mapIso_hom_comm
    AddCommGrpCat.uliftFunctorFullyFaithful _ _ _ _ _ _ _
    (extPerfectCohomologyIsoLifted_homologySequenceδ_shortExact B S hS hTop f hf hfqs hY E hE G hG
      T hT h₁ h₃ i j h)
    (Functor.map_comp_eq_map_comp_of_eq (preadditiveCoyoneda.obj (op E))
      (shift_comp_shiftFunctorAdd'_inv_eq hδT i j (by omega)))

attribute [local instance 20000] ModuleCat.hasDerivedCategory in
include hTop hf hfqs hY hE hG in
/-- **Stacks 08JN from a comparison of coefficients.**  Given the comparison
`τ : 𝒢^• ⊗^L Lf^*Q(-) ⟶ Q(𝒢^• ⊗ f^*(-))`, invertible at every module placed in degree zero,
carrying short exact sequences to short exact sequences and compatible with the connecting
morphisms of the two triangles, the cohomology `H^i(Y, K ⊗^L ℱ)` is identified with
`Ext^i(E, 𝒢^• ⊗ f^*ℱ)` for quasi-coherent `ℱ`, functorially in `ℱ` and compatibly with the
boundary maps. -/
theorem exists_extPerfectCohomologyIso_of_coefficient
    (τ : DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
      tensorPullbackComplex f G ⋙ DerivedCategory.Q)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hδ : ∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (hT : T.ShortExact),
      (extPerfectCoefficientFunctor B S hS f G).map (DerivedCategory.triangleOfSESδ
          (hT.map_of_exact (HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0))) ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (extPerfectSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
        DerivedCategory.triangleOfSESδ (hex T hT)) :
    ∃ c : ∀ (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
        F.IsQuasicoherentOnSite → ∀ i : ℤ,
        extPerfectBaseCohomology B S hS f E G F i ≅ extPerfectExtGroup B S hS f E G F i,
      (∀ (F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ),
          (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
              AddCommGrpCat.{u + 1}).map (((DerivedCategory.homologyFunctor
                (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2)) 0).shift i).map
              ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
                (((smallEtaleDerivedTensor B S hS Y).obj
                  (extPerfectDirectImageObj B S hS f E G)).map (extPerfectSingleMap B S hS q)))) ≫
            (c F' hF' i).hom =
          (c F hF i).hom ≫
            (preadditiveCoyoneda.obj (op E)).map ((extPerfectCoefficientMap B S hS f G q)⟦i⟧')) ∧
      (∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
          (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
          (i j : ℤ) (h : i + 1 = j),
          extPerfectBaseDelta B S hS f E G T hT i j h ≫
            (c T.X₁ h₁ j).hom =
          (c T.X₃ h₃ i).hom ≫ (preadditiveCoyoneda.obj (op E)).map
            ((DerivedCategory.triangleOfSESδ (hex T hT))⟦i⟧' ≫
              (shiftFunctorAdd' _ 1 i j (by omega)).inv.app
                (extPerfectCoefficientObj B S hS f G T.X₁))) :=
  ⟨fun F hF i =>
    extPerfectCohomologyIsoOfCoefficient B S hS hTop f hf hfqs hY E hE G hG τ hτ F hF i,
    fun _ _ hF hF' q i => extPerfectCohomologyIsoOfCoefficient_naturality B S hS hTop f hf hfqs hY E
      hE G hG τ hτ hF hF' q i,
    fun T hT h₁ h₃ i j h => extPerfectCohomologyIsoOfCoefficient_delta B S hS hTop f hf hfqs hY E
      hE G hG τ hτ hex hδ T hT h₁ h₃ i j h⟩

end Comparison

end AlgebraicGeometry.Space

end
