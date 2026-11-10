module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Flat.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus

/-!
# Characterizations of flatness for a quasi-coherent module over a scheme

For a morphism of schemes, flatness of a quasi-coherent module over the target can be checked on
every compatible pair of affine opens, on suitable open covers, or on suitable affine open
covers. Flatness over the target is also preserved by restriction to compatible open subschemes.

The affine case is the statement that the stalk of the tilde construction is the localized
module, together with the fact that flatness over a ring is detected after localizing at every
maximal ideal of the algebra; restriction to an open subscheme changes the base stalk only by a
localization at units, which does not affect flatness.

## Main results

* `AlgebraicGeometry.isFlatOver_tfae` gives the four equivalent criteria for flatness.
* `AlgebraicGeometry.isFlatOver_resLE` gives flatness after restriction to compatible opens.

## Implementation notes

The four entries of `isFlatOver_tfae` are, in order, stalkwise flatness over the target,
flatness of sections on every compatible pair of affine opens, an open-covering criterion for
restricted sheaves, and an affine-open-covering criterion for modules of sections. The
restriction result states the final clause of the source lemma. Scalar restriction on sections
is along the canonical map induced by the scheme morphism.

## References

* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry


noncomputable section


/-- For a ring map `φ : A ⟶ B`, a `B`-module `M` and a point `q` of `Spec B`, the stalk at `q` of
`tilde M` is flat over `A` if and only if the localized module `M_q` is flat over `A`, both being
regarded as `A`-modules through `φ`. -/
theorem flat_tilde_stalk_iff_localizedModule
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : ModuleCat.{u} B)
    (q : Spec B) :
    let N := (tilde M).presheaf.stalk q
    let : q.asIdeal.IsPrime := q.2
    let : Algebra A B := φ.hom.toAlgebra
    let : Module B N :=
      AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
    let : Module A N := Module.compHom N φ.hom
    let : Module A (LocalizedModule q.asIdeal.primeCompl (↑M)) :=
      Module.compHom _ φ.hom
    Module.Flat A N ↔ Module.Flat A (LocalizedModule q.asIdeal.primeCompl (↑M)) := by
  let N := (tilde M).presheaf.stalk q
  let : q.asIdeal.IsPrime := q.2
  let : Algebra A B := φ.hom.toAlgebra
  let : Module A (↑M) := Module.compHom (↑M) φ.hom
  let : Module B N :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  let : Module A N := Module.compHom N φ.hom
  let : Module A (LocalizedModule q.asIdeal.primeCompl (↑M)) :=
    Module.compHom _ φ.hom
  let f := AlgebraicGeometry.tilde.toStalk M q
  let : IsLocalizedModule q.asIdeal.primeCompl f.hom := by
    open AlgebraicGeometry.tilde in
    exact instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      M q
  let eB : N ≃ₗ[B] LocalizedModule q.asIdeal.primeCompl (↑M) :=
    (IsLocalizedModule.iso q.asIdeal.primeCompl f.hom).symm
  let eA : N ≃ₗ[A] LocalizedModule q.asIdeal.primeCompl (↑M) := {
    toFun := eB
    invFun := eB.symm
    left_inv := eB.left_inv
    right_inv := eB.right_inv
    map_add' := eB.map_add
    map_smul' := fun a m => eB.map_smul (φ.hom a) m }
  exact Module.Flat.equiv_iff eA


private theorem germ_fromSpec_stalkMap
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    (p : Spec Γ(S, U)) (hp : hU.fromSpec p ∈ U) :
    S.presheaf.germ U (hU.fromSpec p) hp ≫ hU.fromSpec.stalkMap p =
      (Scheme.ΓSpecIso Γ(S, U)).inv ≫
        (Spec Γ(S, U)).presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _) := by
  rw [Scheme.Hom.germ_stalkMap, hU.fromSpec_app_self, Category.assoc]
  exact congrArg (fun t => (Scheme.ΓSpecIso Γ(S, U)).inv ≫ t)
    ((Spec Γ(S, U)).presheaf.germ_res
      (eqToHom hU.fromSpec_preimage_self) p hp)

private theorem germ_spec_comp_stalkMap
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)
    {B : CommRingCat.{u}} (φ : Γ(S, U) ⟶ B) (q : Spec B)
    (hq : (Spec.map φ ≫ hU.fromSpec) q ∈ U) :
    S.presheaf.germ U ((Spec.map φ ≫ hU.fromSpec) q) hq ≫
      (Spec.map φ ≫ hU.fromSpec).stalkMap q =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫
        (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _) := by
  calc
    _ = (S.presheaf.germ U (hU.fromSpec (Spec.map φ q)) hq ≫
          hU.fromSpec.stalkMap (Spec.map φ q)) ≫
          (Spec.map φ).stalkMap q := by
            rw [Scheme.Hom.stalkMap_comp]
            rfl
    _ = ((Scheme.ΓSpecIso Γ(S, U)).inv ≫
          (Spec Γ(S, U)).presheaf.germ ⊤ (Spec.map φ q) (TopologicalSpace.Opens.mem_top _)) ≫
          (Spec.map φ).stalkMap q := by
            rw [germ_fromSpec_stalkMap hU (Spec.map φ q) hq]
    _ = _ := by
      rw [Category.assoc, Scheme.Hom.germ_stalkMap]
      change (Scheme.ΓSpecIso Γ(S, U)).inv ≫
        (Spec.map φ).appTop ≫
          (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _) =
        φ ≫ (Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _)
      calc
        _ = ((Scheme.ΓSpecIso Γ(S, U)).inv ≫ (Spec.map φ).appTop) ≫
            (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _) := by
              rw [Category.assoc]
        _ = (φ ≫ (Scheme.ΓSpecIso B).inv) ≫
            (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _) :=
              congrArg (fun t => t ≫ (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _))
                (Scheme.ΓSpecIso_inv_naturality φ).symm
        _ = _ := Category.assoc _ _ _


private theorem isFlatOverAt_iff_flat_sectionsStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {V : S.Opens} (hV : IsAffineOpen V) (x : X) (hx : f x ∈ V) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      let M : PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
      let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        inferInstanceAs (Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))
      let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
        Module.compHom _ (f.stalkMap x).hom
      let : Module Γ(S, V) (F.presheaf.stalk x) :=
        Module.compHom _ (S.presheaf.germ V (f x) hx).hom
      Module.Flat Γ(S, V) (F.presheaf.stalk x) := by
  let : Algebra Γ(S, V) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hx⟩
  let : IsLocalization (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl
      (S.presheaf.stalk (f x)) := hV.isLocalization_stalk ⟨f x, hx⟩
  let M : PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    inferInstanceAs (Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : Module Γ(S, V) (F.presheaf.stalk x) :=
    Module.compHom _ (S.presheaf.germ V (f x) hx).hom
  let : IsScalarTower Γ(S, V) (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.flat_iff_of_isLocalization (S.presheaf.stalk (f x))
    (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.primeCompl (F.presheaf.stalk x)

private theorem isFlatOverAt_iff_flat_localizedSections
    {B : CommRingCat.{u}} {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (φ : Γ(S, V) ⟶ B)
    (F : (Spec B).Modules) [F.IsQuasicoherent] (q : Spec B) :
    IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
      let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
      let : Module B ((tilde M).presheaf.stalk q) :=
        AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
      let : Module Γ(S, V) ((tilde M).presheaf.stalk q) :=
        Module.compHom _ φ.hom
      Module.Flat Γ(S, V) ((tilde M).presheaf.stalk q) := by
  let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
  let e : F ≅ tilde M := (asIso F.fromTildeΓ).symm
  let : Module B ((tilde M).presheaf.stalk q) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  let : Module Γ(S, V) ((tilde M).presheaf.stalk q) :=
    Module.compHom _ φ.hom
  change IsFlatOverAt
      (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
    Module.Flat Γ(S, V) ((tilde M).presheaf.stalk q)
  rw [isFlatOverAt_iff_of_moduleIso (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom e q]
  have hx : (Spec.map φ ≫ hV.fromSpec) q ∈ V := by
    change (Spec.map φ q) ∈ hV.fromSpec ⁻¹ᵁ V
    rw [hV.fromSpec_preimage_self]
    trivial
  rw [isFlatOverAt_iff_flat_sectionsStalk
    (Spec.map φ ≫ hV.fromSpec) (tilde M) hV q hx]
  let N := (tilde M).presheaf.stalk q
  let : Module ((Spec B).presheaf.stalk q) N :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (tilde M) q
  let : Module B N := AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf M q
  let : Algebra B ((Spec B).presheaf.stalk q) := StructureSheaf.stalkAlgebra B q
  have hB (b : B) (m : N) :
      (algebraMap B ((Spec B).presheaf.stalk q) b) • m = b • m := by
    rfl
  have hr :
      S.presheaf.germ V ((Spec.map φ ≫ hV.fromSpec) q) hx ≫
          (Spec.map φ ≫ hV.fromSpec).stalkMap q =
        φ ≫ CommRingCat.ofHom (algebraMap B ((Spec B).presheaf.stalk q)) := by
    calc
      _ = φ ≫ (Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.germ ⊤ q (TopologicalSpace.Opens.mem_top _) :=
        germ_spec_comp_stalkMap hV φ q hx
      _ = _ := by
        ext a
        rfl
  let moduleS : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N :=
    Module.compHom N ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
  let moduleLeft : Module Γ(S, V) N :=
    let : Module (S.presheaf.stalk ((Spec.map φ ≫ hV.fromSpec) q)) N := moduleS
    Module.compHom N (S.presheaf.germ V _ hx).hom
  let moduleRight : Module Γ(S, V) N := Module.compHom N φ.hom
  have hmodule : moduleLeft = moduleRight := by
    apply Module.ext'
    intro a m
    change ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
      ((S.presheaf.germ V _ hx).hom a) • m = (φ.hom a) • m
    have hval := congrArg
      (fun t : Γ(S, V) ⟶ (Spec B).presheaf.stalk q => t a) hr
    change ((Spec.map φ ≫ hV.fromSpec).stalkMap q).hom
        ((S.presheaf.germ V _ hx).hom a) =
      algebraMap B ((Spec B).presheaf.stalk q) (φ.hom a) at hval
    rw [hval, hB]
  change @Module.Flat Γ(S, V) N _ _ moduleLeft ↔
    @Module.Flat Γ(S, V) N _ _ moduleRight
  rw [hmodule]

private theorem isFlatOverAt_iff_flat_localizedSectionsAtPrime
    {B : CommRingCat.{u}} {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (φ : Γ(S, V) ⟶ B)
    (F : (Spec B).Modules) [F.IsQuasicoherent] (q : Spec B) :
    IsFlatOverAt (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F q ↔
      let _hq : q.asIdeal.IsPrime := q.2
      let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
      let : Algebra Γ(S, V) B := φ.hom.toAlgebra
      let : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
      let : Module Γ(S, V)
        (LocalizedModule q.asIdeal.primeCompl (↑M)) := Module.compHom _ φ.hom
      Module.Flat Γ(S, V)
        (LocalizedModule q.asIdeal.primeCompl (↑M)) := by
  let _hq : q.asIdeal.IsPrime := q.2
  let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
  let : Algebra Γ(S, V) B := φ.hom.toAlgebra
  let : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
  let : Module Γ(S, V)
      (LocalizedModule q.asIdeal.primeCompl (↑M)) := Module.compHom _ φ.hom
  rw [isFlatOverAt_iff_flat_localizedSections hV φ F q]
  exact flat_tilde_stalk_iff_localizedModule φ M q

private theorem flat_localizedModule_of_flat
    {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (T : Submonoid A) [Module.Flat R M] :
    let : Module R (LocalizedModule T M) :=
      Module.compHom _ (algebraMap R A)
    Module.Flat R (LocalizedModule T M) := by
  let : Module R (LocalizedModule T M) :=
    Module.compHom _ (algebraMap R A)
  let g := LocalizedModule.mkLinearMap T M
  let : SMul R (LocalizedModule T M) :=
    SMul.comp (LocalizedModule T M) (algebraMap R A)
  let : IsScalarTower R A (LocalizedModule T M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.of_isLocalizedModule_of_tower T g

private theorem flat_iff_localized_maximal
    {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] :
    Module.Flat A M ↔
      ∀ (P : Ideal B) (_ : P.IsMaximal),
        let : Module A (LocalizedModule P.primeCompl M) :=
          Module.compHom _ (algebraMap A B)
        Module.Flat A (LocalizedModule P.primeCompl M) := by
  constructor
  · intro h P hP
    let : P.IsPrime := hP.isPrime
    let : Module.Flat A M := h
    exact flat_localizedModule_of_flat P.primeCompl
  · intro h
    let Mₚ : ∀ (P : Ideal B) [P.IsMaximal], Type u :=
      fun (P : Ideal B) [hP : P.IsMaximal] => by
      let : P.IsPrime := hP.isPrime
      exact LocalizedModule P.primeCompl M
    exact @Module.flat_of_isLocalized_maximal A B _ _ _ M _ _ _ _ Mₚ
      (fun (P : Ideal B) [hP : P.IsMaximal] => inferInstance)
      (fun (P : Ideal B) [hP : P.IsMaximal] => by
        let : P.IsPrime := hP.isPrime
        exact Module.compHom (Mₚ P) (algebraMap A B))
      (fun (P : Ideal B) [hP : P.IsMaximal] => inferInstance)
      (fun (P : Ideal B) [hP : P.IsMaximal] => by
        let : P.IsPrime := hP.isPrime
        let : Module A (Mₚ P) := Module.compHom (Mₚ P) (algebraMap A B)
        let : SMul A (Mₚ P) :=
          (Module.compHom (Mₚ P) (algebraMap A B)).toDistribMulAction.toDistribSMul.toSMul
        exact IsScalarTower.of_algebraMap_smul (R := A) (A := B)
          (fun _ _ => rfl))
      (fun (P : Ideal B) [hP : P.IsMaximal] => by
        let : P.IsPrime := hP.isPrime
        exact LocalizedModule.mkLinearMap P.primeCompl M)
      (fun (P : Ideal B) [hP : P.IsMaximal] => inferInstance)
      (fun (P : Ideal B) [hP : P.IsMaximal] => by
        let : P.IsPrime := hP.isPrime
        exact h P hP)

private theorem isFlatOver_spec_iff_flat_sections
    {B : CommRingCat.{u}} {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (φ : Γ(S, V) ⟶ B)
    (F : (Spec B).Modules) [F.IsQuasicoherent] :
    IsFlatOver (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F ↔
      let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
      let : Algebra Γ(S, V) B := φ.hom.toAlgebra
      let : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
      Module.Flat Γ(S, V) (↑M) := by
  let M := (modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤)
  let : Algebra Γ(S, V) B := φ.hom.toAlgebra
  let : Module Γ(S, V) (↑M) := Module.compHom _ φ.hom
  let : IsScalarTower (Γ(S, V)) B (↑M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hloc := flat_iff_localized_maximal
    (A := Γ(S, V)) (B := B) (M := (↑M))
  constructor
  · intro h
    apply hloc.mpr
    intro P hP
    let : P.IsPrime := hP.isPrime
    have hq : IsFlatOverAt
        (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom F ⟨P, hP.isPrime⟩ := h _
    have hlocP := (isFlatOverAt_iff_flat_localizedSectionsAtPrime hV φ F
      ⟨P, hP.isPrime⟩).mp hq
    simpa only [show (⟨P, hP.isPrime⟩ : Spec B).asIdeal = P from rfl] using hlocP
  · intro h q
    let : q.asIdeal.IsPrime := q.2
    let : Module Γ(S, V)
        (LocalizedModule q.asIdeal.primeCompl (↑M)) :=
      Module.compHom _ (algebraMap (Γ(S, V)) B)
    have hloc' : Module.Flat (Γ(S, V))
        (LocalizedModule q.asIdeal.primeCompl (↑M)) :=
      let : Module.Flat (Γ(S, V)) (↑M) := h
      flat_localizedModule_of_flat q.asIdeal.primeCompl
    change Module.Flat (Γ(S, V))
      (LocalizedModule q.asIdeal.primeCompl
        ((modulesSpecToSheaf.obj F).presheaf.obj (.op ⊤))) at hloc'
    exact (isFlatOverAt_iff_flat_localizedSectionsAtPrime hV φ F q).mpr
      (by simpa only using hloc')

private theorem flat_restrictAppIso
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {A : CommRingCat.{u}} (φ : A ⟶ Γ(X, U)) (F : X.Modules) :
    let j := hU.fromSpec
    let G := F.restrict j
    let M := (modulesSpecToSheaf.obj G).presheaf.obj (.op ⊤)
    let : Module A M := Module.compHom _ φ.hom
    let : Module A Γ(F, U) := Module.compHom _ φ.hom
    Module.Flat A M ↔ Module.Flat A Γ(F, U) := by
  let j := hU.fromSpec
  let : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let G := F.restrict j
  let M := (modulesSpecToSheaf.obj G).presheaf.obj (.op ⊤)
  let : Module A M := Module.compHom _ φ.hom
  let : Module A Γ(F, U) := Module.compHom _ φ.hom
  let : Module A Γ(G, ⊤) := Module.compHom _ φ.hom
  have hrange : j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    apply Opens.ext
    rw [Scheme.Hom.coe_image, Opens.coe_top, Set.image_univ, hU.range_fromSpec]
  let e₀ : Γ(G, ⊤) ≅ Γ(F, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) :=
    F.restrictAppIso j ⊤
  have hImage : U = j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := hrange.symm
  let eRing : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) ≅ Γ(X, U) :=
    X.presheaf.mapIso (eqToIso hImage).op
  have hR (a : Γ(X, U)) :
      eRing.hom ((j.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv
        ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = a := by
    have hpreEq : j ⁻¹ᵁ U = ⊤ := by
      simp [j]
    have hpre : ⊤ ≤ j ⁻¹ᵁ U := le_of_eq hpreEq.symm
    have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv =
        (j.appIso (⊤ : (Spec Γ(X, U)).Opens)).hom := by
      simp only [eRing, Functor.mapIso_hom, Iso.op_hom,
        Scheme.Hom.appIso_hom']
      have hAppLE : j.appLE U ⊤ hpre =
          (Scheme.ΓSpecIso Γ(X, U)).inv := by
        change j.app U ≫
          (Spec Γ(X, U)).presheaf.map (homOfLE hpre).op = _
        rw [hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp, ← op_comp]
        have hcomp : homOfLE hpre ≫ eqToHom hpreEq = 𝟙 _ := Subsingleton.elim _ _
        rw [hcomp]
        simp
      rw [← hAppLE]
      simpa only [eqToIso.hom] using
        (hU.fromSpec.map_appLE' (V := ⊤)
          (by rw [← hImage]; exact hpre) hImage)
    have hAEq' : eRing.hom =
        (j.appIso (⊤ : (Spec Γ(X, U)).Opens)).hom ≫
          (Scheme.ΓSpecIso Γ(X, U)).hom := by
      rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hAEq', ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  let e : Γ(G, ⊤) ≅ Γ(F, U) :=
    e₀ ≪≫ F.presheaf.mapIso (eqToIso hrange).symm.op
  let eA : Γ(G, ⊤) ≃ₗ[A] Γ(F, U) := {
    toFun := e.hom
    invFun := e.inv
    left_inv := e.hom_inv_id_apply
    right_inv := e.inv_hom_id_apply
    map_add' := e.hom.hom.map_add
    map_smul' := by
      intro a m
      let r : Γ(Spec Γ(X, U), ⊤) := (Spec Γ(X, U)).presheaf.map
          (Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)).op
          ((Scheme.ΓSpecIso Γ(X, U)).inv (φ.hom a))
      have hs := Scheme.Modules.smul_restrictAppIso_hom_apply j F ⊤ r m
      have hscalar : X.presheaf.map (eqToHom hrange.symm).op
          ((j.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv
            r) = φ.hom a :=
        hR (φ.hom a)
      change e.hom (φ.hom a • m) = φ.hom a • e.hom m
      calc
        e.hom (φ.hom a • m) = e.hom
            (((Spec Γ(X, U)).presheaf.map
              (Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)).op
              ((Scheme.ΓSpecIso Γ(X, U)).inv (φ.hom a))) • m) := by
                rw [Scheme.Modules.smul_Spec_def]
        _ = φ.hom a • e.hom m := by
          dsimp [e, e₀]
          have h' := congrArg (F.presheaf.map (eqToHom hrange.symm).op) hs
          have hmap : F.presheaf.map (eqToHom hrange.symm).op
              (((j.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv r) • e₀.hom m) =
            (X.presheaf.map (eqToHom hrange.symm).op
                ((j.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv r)) •
              F.presheaf.map (eqToHom hrange.symm).op (e₀.hom m) :=
            F.val.map_smul (eqToHom hImage).op
              ((j.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv r) (e₀.hom m)
          rw [hmap, hscalar] at h'
          exact h' }
  exact Module.Flat.equiv_iff eA

/-- Flatness of the sections over a compatible affine pair gives flatness at every point of `U`. -/
private theorem isFlatOverAt_of_flat_sections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V)
    (h : let : Module Γ(S, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
      Module.Flat Γ(S, V) Γ(F, U))
    {x : X} (hx : x ∈ U) : IsFlatOverAt f.toLRSHom.toShHom F x := by
  let j := hU.fromSpec
  let φ : Γ(S, V) ⟶ Γ(X, U) := f.appLE V U hUV
  have hj : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  let G := F.restrict j
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  have hjf : Spec.map φ ≫ hV.fromSpec = j ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  let : Module Γ(S, V) Γ(F, U) := Module.compHom _ φ.hom
  have hM := (flat_restrictAppIso hU φ F).mpr h
  have hG := (isFlatOver_spec_iff_flat_sections hV φ G).mpr hM
  obtain ⟨q, hq⟩ : x ∈ Set.range j := by rw [hU.range_fromSpec]; exact hx
  have hG' : IsFlatOverAt (j ≫ f).toLRSHom.toShHom G q := by
    simpa only [← hjf] using hG q
  have hxflat := (AlgebraicGeometry.isFlatOverAt_restrict_iff j f F q).mp hG'
  simpa [hq] using hxflat

private theorem isFlatOver_iff_affineSections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        let : Module Γ(S, V) Γ(F, U) :=
          Module.compHom Γ(F, U) (f.appLE V U hUV).hom
        Module.Flat Γ(S, V) Γ(F, U) := by
  constructor
  · intro h U hU V hV hUV
    let j := hU.fromSpec
    let φ : Γ(S, V) ⟶ Γ(X, U) := f.appLE V U hUV
    have hj : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
    let G := F.restrict j
    have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
    have hjf : Spec.map φ ≫ hV.fromSpec = j ≫ f :=
      IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
    have hG : IsFlatOver
        (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom G := by
      intro q
      have hq := (AlgebraicGeometry.isFlatOverAt_restrict_iff j f F q).mpr (h (j q))
      change IsFlatOverAt
        (Spec.map φ ≫ hV.fromSpec).toLRSHom.toShHom G q
      simpa only [← hjf] using hq
    have hM := (isFlatOver_spec_iff_flat_sections hV φ G).mp hG
    let : Module Γ(S, V) Γ(F, U) := Module.compHom _ φ.hom
    exact (flat_restrictAppIso hU φ F).mp hM
  · intro h x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV
        (V.2.preimage f.continuous)
    exact isFlatOverAt_of_flat_sections f F hU hV hUV (h U hU V hV hUV) hxU

private theorem isFlatOverAt_iff_resLE
    {X S : Scheme.{u}} {f : X ⟶ S} (F : X.Modules)
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (w : U.toScheme) :
    IsFlatOverAt
      (f.resLE V U hUV).toLRSHom.toShHom (F.restrict U.ι) w ↔
    IsFlatOverAt f.toLRSHom.toShHom F (U.ι w) := by
  let g := f.resLE V U hUV
  let x : X := U.ι w
  let y : V.toScheme := g w
  let R := V.toScheme.presheaf.stalk y
  let T := S.presheaf.stalk (f x)
  let M := (F.restrict U.ι).presheaf.stalk w
  let q := Scheme.Hom.resLEStalkMap f hUV w
  have : IsIso q.hom.left := by infer_instance
  let e : R ≃+* T := (asIso q.hom.left).commRingCatIsoToRingEquiv
  let : Algebra R T := e.toRingHom.toAlgebra
  let ea : R ≃ₐ[R] T := AlgEquiv.ofRingEquiv (f := e) (by intro r; rfl)
  let : IsLocalization (IsUnit.submonoid R) T :=
    IsLocalization.isLocalization_of_algEquiv (M := IsUnit.submonoid R) ea
  let : Module (U.toScheme.presheaf.stalk w) M :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf (F.restrict U.ι) w
  let : Module T M := Module.compHom _ ((U.ι ≫ f).stalkMap w).hom
  let : Module R M := Module.compHom _ (g.stalkMap w).hom
  have hcomp : ∀ r : R,
      ((U.ι ≫ f).stalkMap w).hom (e r) = (g.stalkMap w).hom r := by
    intro r
    have hsquare := congrArg (fun k => k r) q.hom.w
    change (f.stalkMap x).hom (e r) =
      q.hom.right ((g.stalkMap w).hom r) at hsquare
    calc
      ((U.ι ≫ f).stalkMap w).hom (e r) =
          (U.ι.stalkMap w).hom ((f.stalkMap x).hom (e r)) := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
      _ = (U.ι.stalkMap w).hom
          (q.hom.right ((g.stalkMap w).hom r)) := by rw [hsquare]
      _ = (g.stalkMap w).hom r := by
        have hr : q.hom.right ≫ U.ι.stalkMap w = 𝟙 _ := by
          change (U.stalkIso w).hom ≫ U.ι.stalkMap w = 𝟙 _
          have h0 := (U.stalkIso w).hom_inv_id
          rwa [Scheme.Opens.stalkIso_inv U w] at h0
        exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom ((g.stalkMap w).hom r)) hr
  let : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul fun r m => by
    change ((U.ι ≫ f).stalkMap w).hom (e r) • m =
      (g.stalkMap w).hom r • m
    rw [hcomp r]
  exact (Module.flat_iff_of_isLocalization T (IsUnit.submonoid R) M).symm.trans
    (AlgebraicGeometry.isFlatOverAt_restrict_iff U.ι f F w)

private theorem affineSubopens_iSup (X : Scheme.{u}) (O : X.Opens) :
    (⨆ W : {W : X.affineOpens // W.1 ≤ O}, (W.1 : X.Opens)) = O := by
  apply Opens.ext
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  constructor
  · rintro ⟨W, hxW⟩
    exact W.2 hxW
  · intro hx
    obtain ⟨W, hW, hxW, hWO⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact ⟨⟨⟨W, hW⟩, hWO⟩, hxW⟩



/-- For a morphism of schemes `f : X ⟶ S` and a quasi-coherent module `F` on `X`, the following
are equivalent:
1. `F` is flat over `S`;
2. for all affine opens `U` of `X` and `V` of `S` with `U ≤ f ⁻¹ᵁ V`, the sections `Γ(F, U)` are
   flat over `Γ(S, V)`;
3. there is an open cover `V` of `S` and, for each `j`, an open cover `U` of `f ⁻¹ᵁ V j` such that
   each restriction of `F` to `U i` is flat over `V j`;
4. there is an affine open cover `V` of `S` and, for each `j`, an affine open cover `U` of
   `f ⁻¹ᵁ V j` such that each `Γ(F, U i)` is flat over `Γ(S, V j)`. -/
@[stacks 01U4 "flatness characterization"]
public theorem isFlatOver_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] :
    List.TFAE [
      IsFlatOver f.toLRSHom.toShHom F,
      ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
        (hUV : U ≤ f ⁻¹ᵁ V),
        let : Module Γ(S, V) Γ(F, U) :=
          Module.compHom Γ(F, U) (f.appLE V U hUV).hom
        Module.Flat Γ(S, V) Γ(F, U),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            ∀ i, IsFlatOver
              (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)).toLRSHom.toShHom
              (F.restrict (U i).ι),
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i,
                let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                let : Module Γ(S, V j) Γ(F, U i) :=
                  Module.compHom Γ(F, U i) (f.appLE (V j) (U i) hUV).hom
                Module.Flat Γ(S, V j) Γ(F, U i)] := by
  let C1 : Prop := IsFlatOver f.toLRSHom.toShHom F
  let C2 : Prop :=
    ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
      (hUV : U ≤ f ⁻¹ᵁ V),
      let : Module Γ(S, V) Γ(F, U) :=
        Module.compHom Γ(F, U) (f.appLE V U hUV).hom
      Module.Flat Γ(S, V) Γ(F, U)
  let C3 : Prop :=
    ∃ (J : Type u) (V : J → S.Opens), IsOpenCover V ∧
      ∀ j, ∃ (I : Type u) (U : I → X.Opens)
        (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
        ∀ i, IsFlatOver
          (f.resLE (V j) (U i) ((le_iSup U i).trans hU.le)).toLRSHom.toShHom
          (F.restrict (U i).ι)
  let C4 : Prop :=
    ∃ (J : Type u) (V : J → S.Opens), IsOpenCover V ∧
      (∀ j, IsAffineOpen (V j)) ∧
      ∀ j, ∃ (I : Type u) (U : I → X.Opens)
        (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
        (∀ i, IsAffineOpen (U i)) ∧
        ∀ i,
          let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
          let : Module Γ(S, V j) Γ(F, U i) :=
            Module.compHom Γ(F, U i) (f.appLE (V j) (U i) hUV).hom
          Module.Flat Γ(S, V j) Γ(F, U i)
  have h13 : C1 → C3 := by
    intro h
    refine ⟨S.affineOpens, fun V => (V : S.Opens),
      IsOpenCover.mk (iSup_affineOpens_eq_top S), ?_⟩
    intro j
    let V : S.Opens := (j : S.Opens)
    refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V},
      fun i => (i.1 : X.affineOpens).1,
      affineSubopens_iSup X (f ⁻¹ᵁ V), ?_⟩
    intro i w
    let Ui : X.Opens := (i.1 : X.affineOpens).1
    exact (isFlatOverAt_iff_resLE F Ui V i.2 w).mpr (h (Ui.ι w))
  have h31 : C3 → C1 := by
    rintro ⟨J, V, hV, hdata⟩ x
    obtain ⟨j, hxV⟩ := hV.exists_mem (f x)
    obtain ⟨I, U, hU, hflat⟩ := hdata j
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; exact hxV)
    let w : (U i).toScheme := ⟨x, hxi⟩
    have hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
    exact (isFlatOverAt_iff_resLE F (U i) (V j) hUV w).mp (hflat i w)
  have h14 : C1 → C4 := by
    intro h
    refine ⟨S.affineOpens, fun V => (V : S.Opens),
      IsOpenCover.mk (iSup_affineOpens_eq_top S), fun j => j.2, ?_⟩
    intro j
    let V : S.Opens := (j : S.Opens)
    let hV : IsAffineOpen V := (j : S.affineOpens).2
    refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ V},
      fun i => (i.1 : X.affineOpens).1,
      affineSubopens_iSup X (f ⁻¹ᵁ V), fun i => i.1.2, ?_⟩
    intro i
    let U : X.Opens := (i.1 : X.affineOpens).1
    let hU : IsAffineOpen U := (i.1 : X.affineOpens).2
    let hUV : U ≤ f ⁻¹ᵁ V := i.2
    let : Module Γ(S, V) Γ(F, U) :=
      Module.compHom Γ(F, U) (f.appLE V U hUV).hom
    exact (isFlatOver_iff_affineSections f F).mp h U hU V hV hUV
  have h41 : C4 → C1 := by
    rintro ⟨J, V, hVcover, hVaff, hdata⟩ x
    obtain ⟨j, hxV⟩ := hVcover.exists_mem (f x)
    obtain ⟨I, U, hU, hUaff, hsections⟩ := hdata j
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; exact hxV)
    exact isFlatOverAt_of_flat_sections f F (hUaff i) (hVaff j)
      ((le_iSup U i).trans hU.le) (hsections i) hxi
  change List.TFAE [C1, C2, C3, C4]
  refine List.tfae_of_forall (b := C1) ?_
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact (isFlatOver_iff_affineSections f F).symm
  · exact ⟨h31, h13⟩
  · exact ⟨h41, h14⟩


/-- A module flat over the target remains flat over any compatible open
subscheme of the target after restriction to an open of the source. -/
@[stacks 01U4 "restriction to open subschemes"]
public theorem isFlatOver_resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (F : X.Modules) (hF : IsFlatOver f.toLRSHom.toShHom F)
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    IsFlatOver (f.resLE V U hUV).toLRSHom.toShHom
      (F.restrict U.ι) :=
  fun w => (isFlatOverAt_iff_resLE F U V hUV w).mpr (hF (U.ι w))

end

end AlgebraicGeometry
