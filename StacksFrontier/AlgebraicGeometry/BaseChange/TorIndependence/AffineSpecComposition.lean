module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Perfect.AffinePullbackComparisonCocycle

/-!
# The base-change composition over a pushout square of rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a pushout square of rings, `M` a K-flat complex of
`A`-modules, `N` a complex of `A'`-modules and `ψ₀ : A' ⊗_A M ⟶ N` a map of complexes.  Let
`ψ : L(Spec c)^*M̃ ⟶ Ñ` be the composite of the comparison of the derived with the degreewise
pullback, the affine pullback comparison and `ψ₀`.  If `π : P ⟶ M` is a quasi-isomorphism from a
K-flat complex of `R`-modules, then the composition `Lg^*Rf_*M̃ ⟶ Rf'_*Ñ` of the square of spectra
is an isomorphism as soon as the map of complexes `R' ⊗_R P ⟶ N`, `1 ⊗ x ↦ ψ₀(1 ⊗ π x)`, is a
quasi-isomorphism.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_comp_specMap_of_quasiIso`.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped ChangeOfRings
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'}

/-- The map out of the derived pullback along `Spec c` attached to a map of complexes
`ψ₀ : A' ⊗_A M ⟶ N`. -/
def specPullbackDatum (c : A ⟶ A') (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N) :
    (derivedPullback (Spec.map c).toLRSHom.toShHom).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) :=
  (derivedPullbackComparison (Spec.map c).toLRSHom.toShHom).app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
        ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀))

/-- **The degreewise composite through the base change morphism, on complexes.** -/
theorem tilde_baseChange_comp_complex (w : Spec.map c ≫ Spec.map a = Spec.map d ≫ Spec.map b)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (π : P ⟶ ((ModuleCat.restrictScalars a.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N)
    (κ₀ : ((ModuleCat.extendScalars b.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars d.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (hκ : ∀ (n : ℤ) (x : P.X n),
      (κ₀.f n).hom ((1 : R') ⊗ₜ[R,b.hom] x) = (ψ₀.f n).hom ((1 : A') ⊗ₜ[A,c.hom] (π.f n).hom x)) :
    ((Scheme.Modules.pullback (Spec.map b)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map π ≫
          (NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R A a)
            (ComplexShape.up ℤ)).app M) ≫
      (NatTrans.mapHomologicalComplex
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w) (ComplexShape.up ℤ)).app
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      ((Scheme.Modules.pushforward (Spec.map d)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
          ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀) =
    (AlgebraicGeometry.tildePullbackComplexIso R R' b).hom.app P ≫
      ((tilde.functor R').mapHomologicalComplex (ComplexShape.up ℤ)).map κ₀ ≫
      (NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R' A' d)
        (ComplexShape.up ℤ)).app N := by
  ext n : 1
  have key := AlgebraicGeometry.tilde_baseChange_comp w (P.X n) (M.X n) (N.X n) (π.f n) (ψ₀.f n)
    (κ₀.f n) (hκ n)
  rw [← cancel_epi ((pullbackTildeIso R R' b).inv.app (P.X n))]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f,
    AlgebraicGeometry.StandardModel.tildePullbackComplexIso_hom_app_f, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp (Scheme.Modules.pushforward (Spec.map d))]
  rwa [Functor.map_comp (Scheme.Modules.pullback (Spec.map b))] at key

/-- Degreewise pullback followed by localization, on the class of a map of complexes. -/
theorem pullbackOnHomotopy_map_quotient_map {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (φ : K ⟶ L) :
    (pullbackOnHomotopy f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
  rfl

/-- Degreewise pushforward followed by localization, on the class of a map of complexes. -/
theorem pushforwardToDerivedCategory_map_quotient_map {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (φ : K ⟶ L) :
    (pushforwardToDerivedCategory f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
  rfl

/-- Degreewise pullback, a map of the homotopy category of the pulled-back complexes, and
degreewise pushforward, all followed by localization, compose to the class of the composite. -/
theorem pullbackOnHomotopy_comp_Qh_comp_pushforward {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Z ⟶ X) {K₁ K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    {L₁ L₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    (e : K₁ ⟶ K₂)
    (v : ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₂ ⟶
      ((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj L₁) (θ : L₁ ⟶ L₂) :
    (pullbackOnHomotopy f).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map e) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map v) ≫
        (pushforwardToDerivedCategory g).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map θ) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map e ≫ v ≫
          ((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).map θ)) := by
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  rfl

/-- The underived base change map of a square of schemes, between degreewise pullback and
degreewise pushforward of maps of complexes, is the class of a quasi-isomorphism as soon as the
degreewise composite through the base change morphism of Stacks 02KG is one. -/
theorem isIso_pullbackOnHomotopy_comp_underived_comp {X X' S S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g)
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing S.toSheafedSpace)) ℤ}
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) ℤ)
    {L : CochainComplex (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)) ℤ}
    (e : K ⟶
      ((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    (θ : ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      L)
    (h : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing S'.toSheafedSpace)) (ComplexShape.up ℤ)).map
      (((modulePullback g.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).map e ≫
        (NatTrans.mapHomologicalComplex
          (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w)
            (ComplexShape.up ℤ)).app C ≫
        ((modulePushforward f'.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map θ)))) :
    IsIso ((pullbackOnHomotopy g.toLRSHom.toShHom).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map e) ≫
      DerivedCategory.Qh.map ((underivedBaseChangeSquare g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm w)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (pushforwardToDerivedCategory f'.toLRSHom.toShHom).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map θ)) := by
  rw [underivedBaseChangeSquare_app_quotient_eq, moduleBaseChange_eq w]
  have k := pullbackOnHomotopy_comp_Qh_comp_pushforward g.toLRSHom.toShHom f'.toLRSHom.toShHom
    (L₁ := ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
    e ((NatTrans.mapHomologicalComplex
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w)
          (ComplexShape.up ℤ)).app C)
    θ
  exact (congrArg IsIso k).mpr h

/-- The chase closing the composition over a pushout square: a composite `X ≫ B ≫ R` is
invertible once it is related through two naturality squares and an invertible middle factor to
a composite of isomorphisms. -/
theorem isIso_of_chase {𝒞 : Type*} [Category 𝒞] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ p₀ p₁ p₂ : 𝒞}
    (A : o₀ ⟶ o₁) (X : o₁ ⟶ o₂) (B : o₂ ⟶ o₃) (C : o₀ ⟶ o₄) (D : o₄ ⟶ o₅) (E : o₅ ⟶ o₃)
    (Rθ : o₃ ⟶ o₆) (F : o₅ ⟶ p₂) (E' : p₂ ⟶ o₆) (Le : p₀ ⟶ o₀) (C' : p₀ ⟶ p₁) (G : p₁ ⟶ o₄)
    (hG : A ≫ X ≫ B = C ≫ D ≫ E) (hη : E ≫ Rθ = F ≫ E') (hν : Le ≫ C = C' ≫ G)
    (hA : IsIso A) (hLe : IsIso Le) (hC' : IsIso C') (hE' : IsIso E') (hm : IsIso (G ≫ D ≫ F)) :
    IsIso (X ≫ B ≫ Rθ) := by
  have e : (Le ≫ A) ≫ X ≫ B ≫ Rθ = C' ≫ (G ≫ D ≫ F) ≫ E' := by
    simp only [Category.assoc, reassoc_of% hG, hη, reassoc_of% hν]
  have : IsIso ((Le ≫ A) ≫ X ≫ B ≫ Rθ) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_left (Le ≫ A) _

/-- The comparison `pushforwardTildeNatTrans` is an isomorphism on every complex of modules. -/
private theorem isIso_mapHomologicalComplex_pushforwardTildeNatTrans_app {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : CochainComplex (ModuleCat.{u} S) ℤ) :
    IsIso ((NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R S φ)
      (ComplexShape.up ℤ)).app M) :=
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R S φ)
    (ComplexShape.up ℤ)).app M).f n) := fun n => isIso_pushforwardTildeNatTrans_app R S φ (M.X n)
  HomologicalComplex.Hom.isIso_of_components _

/-- **The composition over a pushout square of rings, from a quasi-isomorphism of complexes.** -/
theorem isIso_comp_specMap_of_quasiIso (h : IsPushout a b c d)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (_hM : CochainComplex.KFlat.{u, u} M)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (π : P ⟶ ((ModuleCat.restrictScalars a.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (hπ : QuasiIso π) (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N)
    (κ₀ : ((ModuleCat.extendScalars b.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars d.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
    (hκ : ∀ (n : ℤ) (x : P.X n),
      (κ₀.f n).hom ((1 : R') ⊗ₜ[R,b.hom] x) = (ψ₀.f n).hom ((1 : A') ⊗ₜ[A,c.hom] (π.f n).hom x))
    (hq : QuasiIso κ₀) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
        (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
        (comp_toShHom_of_comm (isPullback_specMap h).w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) ≫
      (derivedPushforward (Spec.map d).toLRSHom.toShHom).map (specPullbackDatum c M N ψ₀)) := by
  have sq := isPullback_specMap h
  have hf' : IsAffineHom (Spec.map d) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  have := Stacks.AffineTilde.tildeFunctor_preservesHomology R'
  have := Stacks.AffineTilde.tildeFunctor_preservesHomology R
  let θ := (AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
    ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀
  let e := ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map π ≫
    (NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R A a) (ComplexShape.up ℤ)).app M
  have hA : IsIso ((derivedPushforwardUnit (Spec.map a).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom (Spec.map a) _
      (fun n => (inferInstance : ((tilde.functor A).obj (M.X n)).IsQuasicoherent))
  have hE' : IsIso ((derivedPushforwardUnit (Spec.map d).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N))) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom (Spec.map d) _
      (fun n => (inferInstance : ((tilde.functor A').obj (N.X n)).IsQuasicoherent))
  have hC' : IsIso ((derivedPullbackComparison (Spec.map b).toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      (Spec.map b).toLRSHom.toShHom _ (Stacks.TildeStalk.kFlatComplex_tilde R P hP)
  have he : QuasiIso e := by
    have h₁ : QuasiIso (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map π) := by
      have := hπ
      infer_instance
    have := isIso_mapHomologicalComplex_pushforwardTildeNatTrans_app a M
    exact quasiIso_comp _ _
  have hLe : IsIso
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map e)) :=
    (DerivedCategory.isIso_Qh_map_iff _).2 ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 he)
  have hX : QuasiIso ((AlgebraicGeometry.tildePullbackComplexIso R R' b).hom.app P ≫
      ((tilde.functor R').mapHomologicalComplex (ComplexShape.up ℤ)).map κ₀ ≫
      (NatTrans.mapHomologicalComplex (pushforwardTildeNatTrans R' A' d)
        (ComplexShape.up ℤ)).app N) := by
    have := hq
    have := isIso_mapHomologicalComplex_pushforwardTildeNatTrans_app d N
    infer_instance
  have hX' := (DerivedCategory.isIso_Qh_map_iff _).2
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hX)
  rw [← tilde_baseChange_comp_complex sq.w P M N π ψ₀ κ₀ hκ] at hX'
  have hm := isIso_pullbackOnHomotopy_comp_underived_comp sq.w
    (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) e θ hX'
  have hη := (derivedPushforwardUnit (Spec.map d).toLRSHom.toShHom).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map θ)
  have hν := (derivedPullbackComparison (Spec.map b).toLRSHom.toShHom).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map e)
  have hG := derivedBaseChangeMap_Qh_comparison (Spec.map c).toLRSHom.toShHom
    (Spec.map d).toLRSHom.toShHom (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
    (comp_toShHom_of_comm sq.w) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
  have hLe' : IsIso ((derivedPullback (Spec.map b).toLRSHom.toShHom).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map e))) :=
    ((derivedPullback (Spec.map b).toLRSHom.toShHom).mapIso (@asIso _ _ _ _ _ hLe)).isIso_hom
  rw [specPullbackDatum, Functor.map_comp]
  exact isIso_of_chase _ _ _ _ _ _ _ _ _ _ _ _ hG hη.symm hν (Functor.map_isIso _ _)
    hLe' hC' hE' hm

end Stacks.Cohomology.DerivedBaseChange
