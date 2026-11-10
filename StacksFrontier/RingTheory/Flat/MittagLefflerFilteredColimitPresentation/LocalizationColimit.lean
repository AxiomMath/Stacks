module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Util.CountHeartbeats
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.Colimit
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Restriction
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsFiniteType05MF
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.HenselianCollapse
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.TFAE
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation.LocalizationAndAssociatedPoints
import all StacksFrontier.RingTheory.Flat.MittagLefflerFilteredColimitPresentation.LocalizationAndAssociatedPoints

/-!
# Stalks as filtered colimits of localized sections

Auxiliary results for the filtered-colimit presentation of Stacks 05U7: the stalk of `M~` as a
localization, free sections on affine opens and their pullbacks, the system of localizations
of a module at the elements of a submonoid and its colimit, and the injectivity of reductions
modulo the maximal ideal coming from injectivity on the closed fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped TensorProduct

universe u v uM uP uQ uN w
private noncomputable def tilde_stalk_equiv_localized
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M] [Module R M]
    (q : Spec R) :
    let N := (AlgebraicGeometry.tilde (ModuleCat.of R M)).presheaf.stalk q
    letI : q.asIdeal.IsPrime := q.2
    letI : Module R N :=
      AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf
        (ModuleCat.of R M) q
    letI : Module R (LocalizedModule q.asIdeal.primeCompl M) :=
      Module.compHom _ (RingHom.id R)
    N ≃ₗ[R] LocalizedModule q.asIdeal.primeCompl M := by
  letI : q.asIdeal.IsPrime := q.2
  letI : Module R
      ((AlgebraicGeometry.tilde (ModuleCat.of R M)).presheaf.stalk q) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf
      (ModuleCat.of R M) q
  let f := AlgebraicGeometry.tilde.toStalk (ModuleCat.of R M) q
  letI : IsLocalizedModule q.asIdeal.primeCompl f.hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      (ModuleCat.of R M) q
  exact (IsLocalizedModule.iso q.asIdeal.primeCompl f.hom).symm

@[instance_reducible]
private noncomputable def stalkModule
    {X : Scheme.{w}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

private lemma isFlatOverAt_tilde_of_isLocalizedModule
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {M N : Type u} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (q : PrimeSpectrum B) (l : M →ₗ[B] N)
    [IsLocalizedModule q.asIdeal.primeCompl l] [Module.Flat A N] :
    AlgebraicGeometry.IsFlatOverAt
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).toLRSHom.toShHom
      (tilde (ModuleCat.of B M)) q := by
  let : Module A M := Module.compHom M (algebraMap A B)
  let : IsScalarTower A B M := IsScalarTower.of_compHom A B M
  rw [isFlatOverAt_spec_tilde_iff_flat_localizedModule
    (CommRingCat.ofHom (algebraMap A B)) (ModuleCat.of B M) rfl q]
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.asIdeal.primeCompl l).restrictScalars A)

private noncomputable def affinePullbackSectionsIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj F) ≅
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F) := by
  haveI hiso : IsIso F.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ F).mp inferInstance
  exact tilde.toTildeΓNatIso.app _ ≪≫
    moduleSpecΓFunctor.mapIso
      ((AlgebraicGeometry.pullbackTildeIso R S φ).app
        (moduleSpecΓFunctor.obj F)).symm ≪≫
    moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pullback (Spec.map φ)).mapIso
        (@asIso _ _ _ _ F.fromTildeΓ hiso))

private noncomputable def affinePullbackSectionsMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent] :
    (moduleSpecΓFunctor.obj F) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F)) :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app _ ≫
    (ModuleCat.restrictScalars φ.hom).map (affinePullbackSectionsIso φ F).hom

private theorem affinePullbackSectionsIso_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent]
    (m : moduleSpecΓFunctor.obj F) :
    letI : Algebra R S := φ.hom.toAlgebra
    (affinePullbackSectionsIso φ F).hom ((1 : S) ⊗ₜ[R] m) =
      affinePullbackSectionsMap φ F m := rfl

private theorem isBaseChange_affinePullbackSectionsMap
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent] :
    letI : Algebra R S := φ.hom.toAlgebra
    let N := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F)
    letI : Module R N := Module.compHom N φ.hom
    letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
    IsBaseChange S (show moduleSpecΓFunctor.obj F →ₗ[R] N from
      (affinePullbackSectionsMap φ F).hom) := by
  let : Algebra R S := φ.hom.toAlgebra
  let N := moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map φ)).obj F)
  let : Module R N := Module.compHom N φ.hom
  let : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  exact IsBaseChange.of_equiv (affinePullbackSectionsIso φ F).toLinearEquiv
    (affinePullbackSectionsIso_unit φ F)

private lemma ker_eq_smul_top_of_quotient_baseChange
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (I : Ideal A) [Module (A ⧸ I) N]
    [IsScalarTower A (A ⧸ I) N] (f : M →ₗ[A] N) (hf : IsBaseChange (A ⧸ I) f) :
    LinearMap.ker f = I • (⊤ : Submodule A M) := by
  ext m
  change f m = 0 ↔ m ∈ I • (⊤ : Submodule A M)
  have ht : f m = 0 ↔ (1 : A ⧸ I) ⊗ₜ[A] m = 0 := by
    rw [← hf.equiv.map_eq_zero_iff, hf.equiv_tmul, one_smul]
  rw [ht, ← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff]
  simp

private lemma ker_restrictScalars_eq_smul_top_of_pushout_quotient
    {A B C M N : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IsPushout A (A ⧸ I) B C]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N] [Module A N] [Module B N] [Module C N] [Module (A ⧸ I) N]
    [IsScalarTower A B N] [IsScalarTower B C N] [IsScalarTower A C N]
    [IsScalarTower A (A ⧸ I) N] [IsScalarTower (A ⧸ I) C N]
    (f : M →ₗ[B] N) (hf : IsBaseChange C f) :
    LinearMap.ker (f.restrictScalars A) = I • (⊤ : Submodule A M) := by
  apply ker_eq_smul_top_of_quotient_baseChange
  apply IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange A (A ⧸ I) B C M).symm.trans
      (hf.equiv.restrictScalars (A ⧸ I)))
  intro m
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, hf.equiv_tmul, one_smul]
  rfl

private lemma free_sections_of_open_restriction (R : CommRingCat.{u})
    {P Z : Scheme.{u}} (j : Z ⟶ P) [IsOpenImmersion j]
    (M : P.Modules) (φ : R ⟶ Γ(P, j ''ᵁ ⊤)) (ψ : R ⟶ Γ(Z, ⊤))
    (hφ : ∀ r, (j.appIso ⊤).hom (φ.hom r) = ψ.hom r)
    (hfree : letI : Module R Γ(M, j ''ᵁ ⊤) := Module.compHom _ φ.hom
      Module.Free R Γ(M, j ''ᵁ ⊤)) :
    letI : Module R Γ(M.restrict j, ⊤) := Module.compHom _ ψ.hom
    Module.Free R Γ(M.restrict j, ⊤) := by
  let : Module R Γ(M, j ''ᵁ ⊤) := Module.compHom _ φ.hom
  let : Module R Γ(M.restrict j, ⊤) := Module.compHom _ ψ.hom
  let : Module.Free R Γ(M, j ''ᵁ ⊤) := hfree
  let e := (M.restrictAppIso j ⊤).symm
  let E : Γ(M, j ''ᵁ ⊤) ≃ₗ[R] Γ(M.restrict j, ⊤) :=
    { Equiv.ofBijective (fun x => (ConcreteCategory.hom e.hom) x)
        (ConcreteCategory.bijective_of_isIso e.hom) with
      map_add' := fun x y => map_add (ConcreteCategory.hom e.hom) x y
      map_smul' := fun r x => by
        change (ConcreteCategory.hom e.hom) (r • x) = _
        calc
          (ConcreteCategory.hom e.hom) (r • x) =
              (j.appIso ⊤).hom (φ.hom r) •
                (ConcreteCategory.hom e.hom) x := by
                  change (M.restrictAppIso j ⊤).inv (r • x) = _
                  exact Scheme.Modules.smul_restrictAppIso_inv_apply j M ⊤
                    (φ.hom r) x
          _ = ψ.hom r • (ConcreteCategory.hom e.hom) x := by rw [hφ r] }
  exact Module.Free.of_equiv E

private lemma free_sections_of_opens_eq (R : CommRingCat.{u})
    {P : Scheme.{u}} (M : P.Modules) (V W : P.Opens) (hVW : V = W)
    (φ : R ⟶ Γ(P, W)) (φ' : R ⟶ Γ(P, V))
    (hφ : ∀ r, φ'.hom r = P.presheaf.map (eqToHom hVW).op (φ.hom r))
    (hfree : letI : Module R Γ(M, W) := Module.compHom _ φ.hom
      Module.Free R Γ(M, W)) :
    letI : Module R Γ(M, V) := Module.compHom _ φ'.hom
    Module.Free R Γ(M, V) := by
  let : Module R Γ(M, W) := Module.compHom _ φ.hom
  let : Module R Γ(M, V) := Module.compHom _ φ'.hom
  let : Module.Free R Γ(M, W) := hfree
  let m := M.presheaf.mapIso (eqToIso hVW).op
  let E : Γ(M, W) ≃ₗ[R] Γ(M, V) :=
    { Equiv.ofBijective (fun x => (ConcreteCategory.hom m.hom) x)
        (ConcreteCategory.bijective_of_isIso m.hom) with
      map_add' := fun x y => map_add (ConcreteCategory.hom m.hom) x y
      map_smul' := fun r x => by
        change (ConcreteCategory.hom m.hom) (r • x) = _
        calc
          (ConcreteCategory.hom m.hom) (r • x) =
              (P.presheaf.map (eqToHom hVW).op (φ.hom r)) •
                (ConcreteCategory.hom m.hom) x := by
                  exact M.map_smul (eqToHom hVW) (φ.hom r) x
          _ = φ'.hom r • (ConcreteCategory.hom m.hom) x := by rw [hφ r] }
  exact Module.Free.of_equiv E

private abbrev LocalizedIndex {R : Type u} [CommRing R] (T : Submonoid R) := T

private instance localizedIndexCategory {R : Type u} [CommRing R] (T : Submonoid R) :
    Category (LocalizedIndex T) where
  Hom s t := {a : T // (s : R) * (a : R) = (t : R)}
  id s := ⟨1, by simp⟩
  comp := fun {i j k} f g => ⟨f.1 * g.1, by
    calc
      (i : R) * ((f.1 : R) * (g.1 : R)) = ((i : R) * (f.1 : R)) * (g.1 : R) := by ring
      _ = (j : R) * (g.1 : R) := by rw [f.2]
      _ = (k : R) := g.2⟩
  id_comp := by intro i j f; apply Subtype.ext; simp
  comp_id := by intro i j f; apply Subtype.ext; simp
  assoc := by intro a b c d f g h; apply Subtype.ext; simp [mul_assoc]

private instance localizedIndexFiltered {R : Type u} [CommRing R] (T : Submonoid R) :
    IsFiltered (LocalizedIndex T) := by
  let : IsFilteredOrEmpty (LocalizedIndex T) := {
    cocone_objs := by
      intro i j
      refine ⟨i * j, ⟨j, ?_⟩, ⟨i, ?_⟩, trivial⟩ <;> simp [mul_comm]
    cocone_maps := by
      intro i j f g
      refine ⟨j * i, ⟨i, ?_⟩, ?_⟩
      · simp [mul_comm]
      · apply Subtype.ext
        change f.1 * (i : T) = g.1 * (i : T)
        apply Subtype.ext
        calc
          (f.1 : R) * (i : R) = (i : R) * (f.1 : R) := mul_comm _ _
          _ = (j : R) := f.2
          _ = (i : R) * (g.1 : R) := g.2.symm
          _ = (g.1 : R) * (i : R) := mul_comm _ _
  }
  let : Nonempty (LocalizedIndex T) := ⟨1⟩
  exact IsFiltered.mk

private noncomputable def localizedIndexMap {R : Type u} [CommRing R] {T : Submonoid R}
    {M : Type u} [AddCommGroup M] [Module R M] {i j : LocalizedIndex T}
    (f : i ⟶ j) : M →ₗ[R] M where
  toFun x := (f.1 : R) • x
  map_add' x y := smul_add _ _ _
  map_smul' r x := by
    calc
      (f.1 : R) • (r • x) = ((f.1 : R) * r) • x := by rw [mul_smul]
      _ = (r * (f.1 : R)) • x := by rw [mul_comm]
      _ = r • ((f.1 : R) • x) := by rw [mul_smul]

private noncomputable def localizedIndexDiagram {R : Type u} [CommRing R]
    (T : Submonoid R) {M : Type u} [AddCommGroup M] [Module R M] :
    LocalizedIndex T ⥤ ModuleCat.{u} R where
  obj _ := ModuleCat.of R M
  map f := ModuleCat.ofHom (localizedIndexMap f)
  map_id := by
    intro i
    apply ModuleCat.hom_ext
    ext x
    change (1 : R) • x = x
    simp
  map_comp := by
    intro i j k f g
    apply ModuleCat.hom_ext
    ext x
    change ((f.1 : R) * (g.1 : R)) • x = (g.1 : R) • ((f.1 : R) • x)
    calc
      ((f.1 : R) * (g.1 : R)) • x = (f.1 : R) • ((g.1 : R) • x) := by rw [mul_smul]
      _ = (g.1 : R) • ((f.1 : R) • x) := by rw [smul_comm]

private noncomputable def localizedIndexLeg {R : Type u} [CommRing R] (T : Submonoid R)
    {M : Type u} [AddCommGroup M] [Module R M] (i : LocalizedIndex T) :
    M →ₗ[R] LocalizedModule T M :=
  (LocalizedModule.divBy i).comp (LocalizedModule.mkLinearMap T M)

private lemma localizedIndexLeg_natural {R : Type u} [CommRing R] {T : Submonoid R}
    {M : Type u} [AddCommGroup M] [Module R M] {i j : LocalizedIndex T}
    (f : i ⟶ j) (x : M) :
    localizedIndexLeg T j (localizedIndexMap f x) = localizedIndexLeg T i x := by
  simp only [localizedIndexLeg, LinearMap.comp_apply, LocalizedModule.divBy_apply,
    LocalizedModule.mkLinearMap_apply, localizedIndexMap]
  apply LocalizedModule.mk_eq.mpr
  refine ⟨1, ?_⟩
  simpa [Submonoid.smul_def, mul_smul] using congrArg (fun a : R => a • x) f.2

private noncomputable def localizedIndexCocone {R : Type u} [CommRing R]
    (T : Submonoid R) {M : Type u} [AddCommGroup M] [Module R M] :
    Cocone (localizedIndexDiagram T (M := M)) where
  pt := ModuleCat.of R (LocalizedModule T M)
  ι := {
    app := fun i => ModuleCat.ofHom (localizedIndexLeg T i)
    naturality := by
      intro i j f
      apply ModuleCat.hom_ext
      ext x
      exact localizedIndexLeg_natural f x }

private noncomputable def localizedIndexColimitEquiv {R : Type u} [CommRing R]
    (T : Submonoid R) {M : Type u} [AddCommGroup M] [Module R M] :
    ↑(colimit (localizedIndexDiagram T (M := M) :
      LocalizedIndex T ⥤ ModuleCat.{u} R)) ≃ₗ[R] LocalizedModule T M := by
  classical
  let F : LocalizedIndex T ⥤ ModuleCat.{u} R := localizedIndexDiagram T (M := M)
  letI : SmallCategory (LocalizedIndex T) := inferInstance
  letI : IsFiltered (LocalizedIndex T) := localizedIndexFiltered T
  let c : Cocone F := colimit.cocone F
  let hc : IsColimit c := colimit.isColimit F
  let d : Cocone F := localizedIndexCocone T (M := M)
  haveI : PreservesColimit F (forget (ModuleCat R)) := by infer_instance
  let φ := colimit.desc F d
  have hleg (i : LocalizedIndex T) (x : M) :
      (d.ι.app i) x = LocalizedModule.mk x i := by
    change LocalizedModule.divBy i (LocalizedModule.mkLinearMap T M x) = _
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.divBy_apply,
      LocalizedModule.liftOn_mk]
    simp
  have hrep (i : LocalizedIndex T) (x : M) : φ (c.ι.app i x) = LocalizedModule.mk x i := by
    change φ.hom ((c.ι.app i).hom x) = _
    have hh := ConcreteCategory.congr_hom (colimit.ι_desc d i) x
    exact hh.trans (hleg i x)
  have hsurj : Function.Surjective φ.hom := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h x s => exact ⟨c.ι.app s x, hrep s x⟩
  have hinj : Function.Injective φ.hom := by
    intro x y hxy
    obtain ⟨i, m, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    obtain ⟨j, n, rfl⟩ := Concrete.isColimit_exists_rep F hc y
    change φ (c.ι.app i m) = φ (c.ι.app j n) at hxy
    rw [hrep i m, hrep j n] at hxy
    obtain ⟨s, hs⟩ := (LocalizedModule.mk_eq).mp hxy
    let k : LocalizedIndex T := i * j * s
    let f : i ⟶ k := ⟨j * s, by
      change (i : R) * ((j : R) * (s : R)) = _
      simp [k, mul_assoc]⟩
    let g : j ⟶ k := ⟨i * s, by
      change (j : R) * ((i : R) * (s : R)) = _
      simp [k, mul_comm, mul_left_comm]⟩
    have hfg : (F.map f).hom m = (F.map g).hom n := by
      change (s : R) • ((j : R) • m) = (s : R) • ((i : R) • n) at hs
      change ((j : R) * (s : R)) • m = ((i : R) * (s : R)) • n
      have hs' : ((s : R) * (j : R)) • m = ((s : R) * (i : R)) • n := by
        simpa only [← mul_smul] using hs
      rw [mul_comm (j : R) (s : R), mul_comm (i : R) (s : R)]
      exact hs'
    change (colimit.cocone F).ι.app i m = (colimit.cocone F).ι.app j n
    exact Concrete.isColimit_rep_eq_of_exists F m n ⟨k, f, g, hfg⟩
  exact LinearEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩

private noncomputable def localizedScalarMapOver
    {A : Type v} {R M : Type u} [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    (r : R) : M →ₗ[A] M where
  toFun x := r • x
  map_add' x y := smul_add r x y
  map_smul' a x := by
    calc
      r • (a • x) = r • (algebraMap A R a • x) := by rw [IsScalarTower.algebraMap_smul]
      _ = (r * algebraMap A R a) • x := by rw [mul_smul]
      _ = (algebraMap A R a * r) • x := by rw [mul_comm]
      _ = algebraMap A R a • (r • x) := by rw [mul_smul]
      _ = a • (r • x) := IsScalarTower.algebraMap_smul (R := A) (A := R) a (r • x)

private noncomputable def localizedIndexCocone_isColimit {R : Type u} [CommRing R]
    (T : Submonoid R) {M : Type u} [AddCommGroup M] [Module R M] :
    IsColimit (localizedIndexCocone T (M := M)) := by
  classical
  let F : LocalizedIndex T ⥤ ModuleCat.{u} R := localizedIndexDiagram T (M := M)
  letI : SmallCategory (LocalizedIndex T) := inferInstance
  letI : IsFiltered (LocalizedIndex T) := localizedIndexFiltered T
  let c : Cocone F := colimit.cocone F
  let hc : IsColimit c := colimit.isColimit F
  let d : Cocone F := localizedIndexCocone T (M := M)
  have hbij : Function.Bijective (colimit.desc F d).hom :=
    (localizedIndexColimitEquiv T (M := M)).bijective
  haveI : IsIso (colimit.desc F d) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  exact IsColimit.ofIsoColimit hc
    (Cocone.ext (asIso (colimit.desc F d)) (by
      intro i
      simp [c, d]))

/-- A localization of a free `A`-module is a filtered colimit of copies of that module.
If every denominator acts injectively after reduction modulo the maximal ideal, then all
transition maps in this presentation retain that property. -/
private theorem exists_filteredColimit_localized
    {A : Type v} {R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
    {M : Type u} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    (T : Submonoid R) (hfree : Module.Free A M)
    (hred : ∀ r : T, Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A M))
        (maximalIdeal A • (⊤ : Submodule A M))
        (localizedScalarMapOver (A := A) (R := R) (M := M) r)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A)
          (localizedScalarMapOver (A := A) (R := R) (M := M) r)))) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ ModuleCat.{u} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A (LocalizedModule T M)) := by
  classical
  let : SmallCategory (LocalizedIndex T) := inferInstance
  let : IsFiltered (LocalizedIndex T) := localizedIndexFiltered T
  let FR := localizedIndexDiagram T (M := M)
  let F := FR ⋙ ModuleCat.restrictScalars (algebraMap A R)
  let dR := localizedIndexCocone T (M := M)
  let c := Functor.mapCocone (ModuleCat.restrictScalars (algebraMap A R)) dR
  have hcR : IsColimit dR := localizedIndexCocone_isColimit T (M := M)
  have hc : IsColimit c := isColimitOfPreserves
    (ModuleCat.restrictScalars (algebraMap A R)) hcR
  have hmod (i : LocalizedIndex T) : (inferInstance : Module A M) = (F.obj i).isModule := by
    apply Module.ext'
    intro a x
    change a • x = algebraMap A R a • x
    exact (IsScalarTower.algebraMap_smul (R := A) (A := R) a x).symm
  refine ⟨LocalizedIndex T, inferInstance, localizedIndexFiltered T, F, c, ?_, ?_, ⟨hc⟩, ?_⟩
  · intro i
    cases hmod i
    exact hfree
  · intro i j f
    cases hmod i
    cases hmod j
    exact hred f.1
  · change Nonempty (((ModuleCat.restrictScalars (algebraMap A R)).obj
      (ModuleCat.of R (LocalizedModule T M))) ≅ ModuleCat.of A (LocalizedModule T M))
    let e : ((ModuleCat.restrictScalars (algebraMap A R)).obj
        (ModuleCat.of R (LocalizedModule T M))) ≃ₗ[A] LocalizedModule T M :=
      { Equiv.refl _ with
        map_add' := fun _ _ => rfl
        map_smul' := fun a m =>
          IsScalarTower.algebraMap_smul (M := LocalizedModule T M) R a m }
    exact ⟨e.toModuleIso⟩

private theorem exists_filteredColimit_of_isLocalizedModule
    {A : Type v} {R : Type u} [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
    {M : Type u} [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]
    {N : Type u} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower A R N]
    (T : Submonoid R) (l : M →ₗ[R] N) [IsLocalizedModule T l]
    (hfree : Module.Free A M)
    (hred : ∀ r : T, Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A M))
        (maximalIdeal A • (⊤ : Submodule A M))
        (localizedScalarMapOver (A := A) (R := R) (M := M) r)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A)
          (localizedScalarMapOver (A := A) (R := R) (M := M) r)))) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ ModuleCat.{u} A) (c : Cocone F),
      (∀ i, Module.Free A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
          (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom))) ∧
      Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of A N) := by
  obtain ⟨I, hI, hIf, F, c, hF, hredF, hc, ⟨e⟩⟩ :=
    exists_filteredColimit_localized T hfree hred
  exact ⟨I, hI, hIf, F, c, hF, hredF, hc,
    ⟨e ≪≫ ((IsLocalizedModule.iso T l).restrictScalars A).toModuleIso⟩⟩

private lemma stalkIso_restrict_smul
    {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (H : W.Modules) (e : H ≅ F.restrict j)
    (w : W) (x : X) (hx : j w = x)
    (r : Γ(X, ⊤)) (m : H.presheaf.stalk w) :
    letI := stalkModule H w
    letI := stalkModule F x
    let E := (Scheme.Modules.toPresheaf W ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} w).mapIso e ≪≫
      (Scheme.Modules.restrictStalkNatIso j w).app F ≪≫
        eqToIso (congrArg (fun y => F.presheaf.stalk y) hx)
    E.hom ((W.presheaf.germ ⊤ w (by simp)) (j.appTop r) • m) =
      (X.presheaf.germ ⊤ x (by simp)) r • E.hom m := by
  subst x
  let := stalkModule H w
  let := stalkModule (F.restrict j) w
  let := stalkModule F (j w)
  dsimp only
  simp only [Iso.trans_hom]
  let t : H.presheaf.stalk w →+ (F.restrict j).presheaf.stalk w :=
    ((Scheme.Modules.toPresheaf W ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} w).map e.hom).hom
  have he : t ((W.presheaf.germ ⊤ w (by simp)) (j.appTop r) • m) =
      (W.presheaf.germ ⊤ w (by simp)) (j.appTop r) • t m := by
    exact (OXModule.stalkLinearMap H (F.restrict j) e.hom w).map_smul
      ((W.presheaf.germ ⊤ w (by simp)) (j.appTop r)) m
  change restrictStalkMap j F w (t ((W.presheaf.germ ⊤ w (by simp))
    (j.appTop r) • m)) = (X.presheaf.germ ⊤ (j w) (by simp)) r •
      restrictStalkMap j F w (t m)
  rw [he]
  have hr : (W.presheaf.germ ⊤ w (by simp)) (j.appTop r) =
      (j.stalkMap w).hom ((X.presheaf.germ ⊤ (j w) (by simp)) r) := by
    have h : ((X.presheaf.germ ⊤ (j w) (by simp) ≫ j.stalkMap w)).hom r =
        ((j.app ⊤ ≫ W.presheaf.germ ⊤ w (by simp))).hom r := by
      rw [Scheme.Hom.germ_stalkMap]
      rfl
    exact h.symm
  rw [hr]
  exact restrictStalkMap_smul j F w _ _

/-- **The comparison of stalks along an open immersion.** An isomorphism `H ≅ F.restrict j`
induces an isomorphism from the stalk of `H` at `w` to the stalk of `F` at the image point. -/
private noncomputable def restrictStalkIso {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) (H : W.Modules) (e : H ≅ F.restrict j) (w : W) (x : X) (hx : j w = x) :
    H.presheaf.stalk w ≅ F.presheaf.stalk x :=
  (Scheme.Modules.toPresheaf W ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} w).mapIso e ≪≫
    (Scheme.Modules.restrictStalkNatIso j w).app F ≪≫
      eqToIso (congrArg (fun y => F.presheaf.stalk y) hx)

private lemma smul_injective_pullback_iso {Y X : Scheme.{u}} (i : Y ⟶ X) [IsIso i]
    (F : X.Modules) (r : Γ(X, ⊤))
    (hr : Function.Injective (fun m : Γ(F, ⊤) => r • m)) :
    Function.Injective (fun m : Γ((Scheme.Modules.pullback i).obj F, ⊤) =>
      i.appTop r • m) := by
  have htop : i ''ᵁ (⊤ : Y.Opens) = ⊤ := by
    ext x
    change (∃ y, y ∈ (⊤ : Y.Opens) ∧ i y = x) ↔ True
    exact ⟨fun _ => trivial, fun _ => ⟨(inv i) x, trivial, by
      have hh := congrArg (fun f : X ⟶ X => f.base x) (IsIso.inv_hom_id i)
      exact hh⟩⟩
  have hr' : Function.Injective (fun m : Γ(F, i ''ᵁ ⊤) =>
      X.presheaf.map (homOfLE (le_top : i ''ᵁ ⊤ ≤ ⊤)).op r • m) := by
    have aux (V : X.Opens) (hV : V = ⊤) : Function.Injective
        (fun m : Γ(F, V) => X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • m) := by
      subst V
      simpa using hr
    exact aux _ htop
  let e := ((Scheme.Modules.restrictFunctorIsoPullback i).app F).symm
  intro m n h
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  apply (ConcreteCategory.bijective_of_isIso (F.restrictAppIso i ⊤).hom).injective
  apply hr'
  have he := congrArg (fun t => (F.restrictAppIso i ⊤).hom ((e.hom.app ⊤) t)) h
  simp only [Scheme.Modules.Hom.app_smul,
    Scheme.Modules.smul_restrictAppIso_hom_apply] at he
  have hi : (i.appIso ⊤).inv (i.appTop r) =
      X.presheaf.map (homOfLE (le_top : i ''ᵁ ⊤ ≤ ⊤)).op r := by
    rw [open_appTop_eq_restrict i r]
    exact ConcreteCategory.congr_hom (i.appIso ⊤).hom_inv_id _
  rwa [hi] at he

private lemma residue_closedPoint_comparison (A : CommRingCat.{u}) [IsLocalRing A] :
    let e := (ResidueField.mapEquiv (stalkClosedPointIso A).commRingCatIsoToRingEquiv)
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      (Spec A).fromSpecResidueField (closedPoint A) =
        Spec.map (CommRingCat.ofHom (residue A)) := by
  dsimp only
  dsimp only [Scheme.fromSpecResidueField]
  rw [← Spec_stalkClosedPointIso]
  have h : CommRingCat.ofHom (residue (A : Type u)) =
      (stalkClosedPointIso A).inv ≫ (Spec A).residue (closedPoint A) ≫
        CommRingCat.ofHom
          (ResidueField.mapEquiv
            (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom := by
    ext a
    change residue (A : Type u) a =
      (ResidueField.mapEquiv (stalkClosedPointIso A).commRingCatIsoToRingEquiv)
        (residue _ ((stalkClosedPointIso A).inv a))
    rw [ResidueField.mapEquiv_apply, ResidueField.map_residue]
    exact congrArg (fun z : (A : Type u) => residue (A : Type u) z)
      (ConcreteCategory.congr_hom (stalkClosedPointIso A).inv_hom_id a).symm
  rw [h, Spec.map_comp ((stalkClosedPointIso A).inv)
      ((Spec A).residue (closedPoint (A : Type u)) ≫
        CommRingCat.ofHom
          (ResidueField.mapEquiv
            (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom),
    Spec.map_comp ((Spec A).residue (closedPoint (A : Type u)))
      (CommRingCat.ofHom
        (ResidueField.mapEquiv
          (stalkClosedPointIso A).commRingCatIsoToRingEquiv).toRingHom),
    Category.assoc]
  rfl

lemma reduction_injective_of_fiber_smul_injective
    {A C : CommRingCat.{u}} [IsLocalRing A]
    (f : Spec C ⟶ Spec A) (H : (Spec C).Modules) [H.IsQuasicoherent]
    (r : Γ(Spec C, ⊤))
    (hinj : Function.Injective (fun m : Γ((Scheme.Modules.pullback
      (f.fiberι (closedPoint A))).obj H, ⊤) =>
        (f.fiberι (closedPoint A)).appTop r • m)) :
    letI : Module A Γ(H, ⊤) := Module.compHom _
      (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)
    ∀ m : Γ(H, ⊤), r • m ∈ maximalIdeal A • (⊤ : Submodule A Γ(H, ⊤)) →
      m ∈ maximalIdeal A • (⊤ : Submodule A Γ(H, ⊤)) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra A C := φ.hom.toAlgebra
  let : Module A Γ(H, ⊤) := Module.compHom _
    (((Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop).hom)
  let f := Spec.map φ
  let D := (A ⧸ maximalIdeal A) ⊗[A] C
  let σ : C ⟶ CommRingCat.of D :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let eκ := (ResidueField.mapEquiv (stalkClosedPointIso A).commRingCatIsoToRingEquiv)
  let i := Spec.map (CommRingCat.ofHom eκ.toRingHom)
  have hisoI : IsIso i := by
    change IsIso (Spec.map eκ.toCommRingCatIso.hom)
    infer_instance
  have hi : i ≫ (Spec A).fromSpecResidueField (closedPoint A) =
      Spec.map (CommRingCat.ofHom (residue A)) := residue_closedPoint_comparison A
  let b := pullback.map f (Spec.map (CommRingCat.ofHom (residue A)))
    f ((Spec A).fromSpecResidueField (closedPoint A))
    (𝟙 _) i (𝟙 _) (by simp) hi.symm
  have hisoB : IsIso b := by
    dsimp only [b]
    exact isIso_pullbackMap_of_isIso _ _ _ _ _ _ _ _ _ inferInstance hisoI inferInstance
  let E : Spec (.of D) ≅ f.fiber (closedPoint A) :=
    (pullbackSpecIso A (A ⧸ maximalIdeal A) C).symm ≪≫
      pullbackSymmetry _ _ ≪≫ @asIso _ _ _ _ b hisoB
  have hbfst : b ≫ pullback.fst f ((Spec A).fromSpecResidueField (closedPoint A)) =
      pullback.fst f (Spec.map (CommRingCat.ofHom (residue (A : Type u)))) := by
    dsimp only [b, pullback.map]
    rw [pullback.lift_fst, Category.comp_id]
  have hE : E.hom ≫ f.fiberι (closedPoint A) = Spec.map σ := by
    dsimp only [E, Iso.trans_hom, Iso.symm_hom, Scheme.Hom.fiberι]
    refine (congrArg
      (fun t : pullback f (Spec.map (CommRingCat.ofHom (residue (A : Type u)))) ⟶ Spec C =>
        (pullbackSpecIso (A : Type u) ((A : Type u) ⧸ maximalIdeal (A : Type u))
            (C : Type u)).inv ≫
          ((pullbackSymmetry
              (Spec.map (CommRingCat.ofHom
                (algebraMap (A : Type u) ((A : Type u) ⧸ maximalIdeal (A : Type u)))))
              (Spec.map (CommRingCat.ofHom (algebraMap (A : Type u) (C : Type u))))).hom :
            _ ⟶ pullback f (Spec.map (CommRingCat.ofHom (residue (A : Type u))))) ≫ t)
      hbfst).trans ?_
    change (pullbackSpecIso (A : Type u) ((A : Type u) ⧸ maximalIdeal (A : Type u))
          (C : Type u)).inv ≫
        (pullbackSymmetry
              (Spec.map (CommRingCat.ofHom
                (algebraMap (A : Type u) ((A : Type u) ⧸ maximalIdeal (A : Type u)))))
              (Spec.map (CommRingCat.ofHom (algebraMap (A : Type u) (C : Type u))))).hom ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap (A : Type u) (C : Type u))))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (A : Type u) ((A : Type u) ⧸ maximalIdeal (A : Type u))))) =
      Spec.map σ
    rw [pullbackSymmetry_hom_comp_fst, pullbackSpecIso_inv_snd]
    rfl
  let Hs := (Scheme.Modules.pullback (f.fiberι (closedPoint A))).obj H
  let K := (Scheme.Modules.pullback (Spec.map σ)).obj H
  let eK : (Scheme.Modules.pullback E.hom).obj Hs ≅ K :=
    (Scheme.Modules.pullbackComp E.hom (f.fiberι (closedPoint A))).app H ≪≫
      (Scheme.Modules.pullbackCongr hE).app H
  have hinjK : Function.Injective (fun m : Γ(K, ⊤) => (Spec.map σ).appTop r • m) := by
    have he := smul_injective_pullback_iso E.hom Hs
      ((f.fiberι (closedPoint A)).appTop r) hinj
    have hscalar : E.hom.appTop ((f.fiberι (closedPoint A)).appTop r) =
        (Spec.map σ).appTop r := by
      change ((f.fiberι (closedPoint A)).appTop ≫ E.hom.appTop) r = _
      rw [← Scheme.Hom.comp_appTop, hE]
    rw [hscalar] at he
    intro m n h
    apply (ConcreteCategory.bijective_of_isIso (eK.inv.app ⊤)).injective
    apply he
    simpa only [Scheme.Modules.Hom.app_smul] using congrArg (eK.inv.app ⊤) h
  let T := Γ(K, ⊤)
  let : Module D T :=
    Scheme.Modules.instModuleCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecAbPresheafOp
      (R := .of D) (M := K) (U := ⊤)
  let : Algebra C D := Algebra.TensorProduct.rightAlgebra
  let : Module C T := Module.compHom T σ.hom
  let : IsScalarTower C D T := IsScalarTower.of_compHom C D T
  let : Module A T := Module.compHom T φ.hom
  let : IsScalarTower A C T := IsScalarTower.of_compHom A C T
  let : IsScalarTower A D T := by
    refine ⟨fun a d m => ?_⟩
    change (a • d) • m = σ (φ a) • (d • m)
    calc
      (a • d) • m = (algebraMap A D a * d) • m :=
        congrArg (fun t : D => t • m) (Algebra.smul_def a d)
      _ = algebraMap A D a • (d • m) := mul_smul _ _ _
      _ = σ (φ a) • (d • m) := by
        congr 1
        exact IsScalarTower.algebraMap_apply A C D a
  let : Module (A ⧸ maximalIdeal A) T :=
    Module.compHom T (algebraMap (A ⧸ maximalIdeal A) D)
  let : IsScalarTower (A ⧸ maximalIdeal A) D T :=
    IsScalarTower.of_compHom (A ⧸ maximalIdeal A) D T
  let : IsScalarTower A (A ⧸ maximalIdeal A) T := by
    apply IsScalarTower.of_algebraMap_smul
    intro a m
    change algebraMap (A ⧸ maximalIdeal A) D (algebraMap A (A ⧸ maximalIdeal A) a) • m =
      σ (φ a) • m
    rw [← IsScalarTower.algebraMap_apply A (A ⧸ maximalIdeal A) D,
      IsScalarTower.algebraMap_apply A C D]
    rfl
  have : IsScalarTower A C Γ(H, ⊤) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a m
    rw [Scheme.Modules.smul_Spec_def]
    change ((Scheme.ΓSpecIso C).inv (φ a)) • m =
      ((Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appTop) a • m
    rw [← Scheme.ΓSpecIso_inv_naturality φ]
    rfl
  let l : Γ(H, ⊤) →ₗ[C] T := (affinePullbackSectionsMap σ H).hom
  have hl : IsBaseChange D l := isBaseChange_affinePullbackSectionsMap σ H
  have hker := ker_restrictScalars_eq_smul_top_of_pushout_quotient
    (maximalIdeal A) l hl
  have hid {X : Scheme.{u}} (x : Γ(X, ⊤)) :
      X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op x = x :=
    ConcreteCategory.congr_hom (X.presheaf.map_id (.op ⊤)) x
  intro m hm
  rw [← hker] at hm ⊢
  change l (r • m) = 0 at hm
  change l m = 0
  apply hinjK
  change (Spec.map σ).appTop r • l m = (Spec.map σ).appTop r • (0 : T)
  rw [smul_zero]
  have hr : r = (Scheme.ΓSpecIso C).inv ((Scheme.ΓSpecIso C).hom r) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso C).hom_inv_id r).symm
  have hm' : l (((Scheme.ΓSpecIso C).hom r) • m) = 0 := by
    rw [Scheme.Modules.smul_Spec_def]
    exact (congrArg (fun t : Γ(Spec C, ⊤) => l (t • m))
      (hid _ |>.trans hr.symm)).trans hm
  rw [l.map_smul] at hm'
  change σ ((Scheme.ΓSpecIso C).hom r) • l m = 0 at hm'
  rw [Scheme.Modules.smul_Spec_def] at hm'
  have he : (Scheme.ΓSpecIso (.of D)).inv (σ ((Scheme.ΓSpecIso C).hom r)) =
      (Spec.map σ).appTop r := by
    have hn := congrArg (fun f : C ⟶ Γ(Spec (.of D), ⊤) => f ((Scheme.ΓSpecIso C).hom r))
      (Scheme.ΓSpecIso_inv_naturality σ)
    simpa only [ConcreteCategory.comp_apply, ← hr] using hn
  exact (congrArg (fun t : Γ(Spec (.of D), ⊤) => t • l m)
    (hid _ |>.trans he)).symm.trans hm'

end
