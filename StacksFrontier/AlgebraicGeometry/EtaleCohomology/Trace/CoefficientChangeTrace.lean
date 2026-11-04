module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientFunctorTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AcyclicTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HomSheafAcyclicEverywhere
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SectionwiseFunctorEtaleQuasiIso
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.InjectiveFunctorTrace

/-!
# The Frobenius trace after the change of coefficients `Hom_R(N, -)`

Let `R` be a finite ring which is injective as a module over itself, `S` a ring, `N` a finite
`(R, S)`-bimodule, and `H = Hom_R(N, -) : Mod_R ⥤ Mod_S`, applied sectionwise to sheaves on small
étale sites. Suppose `H` carries finite projective `R`-modules to finite projective `S`-modules,
so that it induces `H♮ : R^♮ → S^♮` on additive commutator quotients
(`CategoryTheory.FilteredDerived.functorTraceMap`). Let `Y` be a scheme over a finite field `k`
and `L` a bounded below complex of sheaves of `R`-modules on `Y_étale` whose restriction to
`Y_k̄` has injective stalks, with `RΓ(Y_k̄, L|_{Y_k̄})` perfect. Then `RΓ(Y_k̄, H(L)|_{Y_k̄})` is
perfect and

`Tr_S(π_Y^* | RΓ(Y_k̄, H(L)|_{Y_k̄})) = H♮(Tr_R(π_Y^* | RΓ(Y_k̄, L|_{Y_k̄})))`.

The functor `H` is not exact, so `RΓ(Y_k̄, H(L)|)` is not `H` of `RΓ(Y_k̄, L|)` in any derived
sense. It is computed on `H(I^•)` for an injective resolution `L| ⟶ I^•`: `H` preserves the
quasi-isomorphism because the stalks are injective and `H` commutes with stalks
(`AlgebraicGeometry.Scheme.quasiIso_sheafCompose_map_of_injective_stalks`), the terms `H(I^n)`
are acyclic for every direct image
(`Stacks.EtaleCohomology.rightAcyclic_directImage_bimoduleHom_of_injective`), and the Frobenius
twists correspond under `H` (`Stacks.EtaleCohomology.frobeniusBaseChangeTwist_coefficient`). The
complex `Γ(Y_k̄, I^•)` is a bounded below complex of injective `R`-modules, and the trace of `H`
of an endomorphism of it is `H♮` of its trace
(`CategoryTheory.FilteredDerived.perfectDerivedTrace_map_of_injective_of_baer`).

This is Step 7 of the proof of [Stacks, Tag 03UG], with `R = A[G]`, `S = Λ`, `N = M^*` and `L`
the extension by zero of the direct image `f_* A` of a Galois cover.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_bimoduleHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.EtaleCohomology

/-! ### Maps into K-injective complexes -/

/-- Two maps into a K-injective complex with the same image in the derived category are
homotopic. -/
theorem homotopy_of_Q_map_eq_of_isKInjective {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K I : CochainComplex C ℤ} [I.IsKInjective] (f g : K ⟶ I)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Nonempty (Homotopy f g) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ I).injective
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)]
  simpa only [DerivedCategory.quotientCompQhIso_hom_naturality] using
    congrArg (((DerivedCategory.quotientCompQhIso C).hom.app K) ≫ ·) h

/-- An additive functor applied to two maps into a K-injective complex with the same image in
the derived category gives maps with the same image in the derived category. -/
theorem Q_map_mapHomologicalComplex_eq_of_isKInjective {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D] [Abelian D] [HasDerivedCategory D] (G : C ⥤ D)
    [G.Additive] {K I : CochainComplex C ℤ} [I.IsKInjective] (f g : K ⟶ I)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex _).map f) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex _).map g) := by
  obtain ⟨hh⟩ := homotopy_of_Q_map_eq_of_isKInjective f g h
  exact DerivedCategory.Q_map_eq_of_homotopy (h := G.mapHomotopy hh)

/-! ### Global sections and a change of coefficients -/

section GlobalSections

variable {R S : Type} [Ring R] [Ring S] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Gf]

/-- **Global sections commute with a change of coefficients**: both are evaluation at the final
object of the small étale site. -/
def etaleModuleGlobalSectionsCoefficientIso (X : Scheme.{u}) :
    sheafCompose X.smallEtaleTopology Gf ⋙ etaleModuleGlobalSections.{u, 0} S X ≅
      etaleModuleGlobalSections.{u, 0} R X ⋙ Gf :=
  Functor.isoWhiskerLeft (sheafCompose X.smallEtaleTopology Gf)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} S)
        (etaleMkIdIsTerminal X)) ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _)
        (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) :
      sheafCompose X.smallEtaleTopology Gf ⋙
          (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} S)).obj
            (op (Scheme.Etale.mk (𝟙 X))) ≅
        (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
            (op (Scheme.Etale.mk (𝟙 X))) ⋙ Gf) ≪≫
    Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} R) (etaleMkIdIsTerminal X)).symm Gf

/-- The identification of global sections commutes with a natural endomorphism of `Gf`. -/
lemma etaleModuleGlobalSectionsCoefficientIso_hom_natTrans (X : Scheme.{u}) (θ : Gf ⟶ Gf)
    (F : EtaleModules.{u, 0} R X) :
    (etaleModuleGlobalSections.{u, 0} S X).map ((sheafCompose_map X.smallEtaleTopology θ).app F) ≫
        (etaleModuleGlobalSectionsCoefficientIso Gf X).hom.app F =
      (etaleModuleGlobalSectionsCoefficientIso Gf X).hom.app F ≫
        θ.app ((etaleModuleGlobalSections.{u, 0} R X).obj F) := by
  have h₁ := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} S)
    (etaleMkIdIsTerminal X)).hom.naturality ((sheafCompose_map X.smallEtaleTopology θ).app F)
  have h₂ := θ.naturality ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (etaleMkIdIsTerminal X)).inv.app F)
  simp only [etaleModuleGlobalSectionsCoefficientIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom] at h₂ ⊢
  rw [reassoc_of% h₁]
  exact congrArg _ h₂.symm

end GlobalSections

/-! ### The trace after a change of coefficients -/

section Coefficient

variable {R S : Type} [Ring R] [Ring S] [Finite R] (Gf : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [Gf.Additive] [PreservesFilteredColimitsOfSize.{u + 1, u + 1} Gf]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Gf]
  [∀ X : Scheme.{u}, X.smallEtaleTopology.PreservesSheafification Gf]
  [∀ (X Y : Scheme.{u}) (g : X ⟶ Y), Gf.PreservesLeftKanExtensions (smallEtaleBaseChange g).op]

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsSepClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [Finite R] [Gf.Additive] [PreservesFilteredColimitsOfSize.{u + 1, u + 1} Gf]
  [IsSepClosed kbar] in
/-- On global sections over `k̄` of the direct image to `Spec k̄`, the change of coefficients `Gf`
twisted by `θ` commutes with the Frobenius twist of a map `f : A ⟶ πb_* B`. -/
theorem globalSections_coefficient_frobeniusTwist_comm (θ : Gf ⟶ Gf)
    {A B : EtaleModules.{u, 0} R (fieldBaseChange Y kbar)}
    (f : A ⟶ (etaleModuleDirectImage.{u, 0} R
      (geometricFrobeniusBaseChange Y kbar p q hcard)).obj B) :
    (etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))).map
        ((etaleModuleDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((etaleModuleCoefficient Gf (fieldBaseChange Y kbar)).map f ≫
            (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)).map
              ((sheafCompose_map (fieldBaseChange Y kbar).smallEtaleTopology θ).app B)) ≫
          (etaleModuleDirectImageComp.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)
            (pullback.snd Y.hom (specAlgebraMap k kbar))
            (pullback.snd Y.hom (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm).hom.app
            ((etaleModuleCoefficient Gf (fieldBaseChange Y kbar)).obj B)) ≫
      (etaleModuleGlobalSectionsCoefficientIso Gf (Spec (.of kbar))).hom.app
        ((etaleModuleDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj B) =
    (etaleModuleGlobalSectionsCoefficientIso Gf (Spec (.of kbar))).hom.app
        ((etaleModuleDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj A) ≫
      θ.app ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).obj
        ((etaleModuleDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj A)) ≫
      Gf.map ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).map
        ((etaleModuleDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).map f ≫
          (etaleModuleDirectImageComp.{u, 0} R (geometricFrobeniusBaseChange Y kbar p q hcard)
            (pullback.snd Y.hom (specAlgebraMap k kbar))
            (pullback.snd Y.hom (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm).hom.app B)) := by
  let πb := geometricFrobeniusBaseChange Y kbar p q hcard
  let fk := pullback.snd Y.hom (specAlgebraMap k kbar)
  let hw := (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
  let G := etaleModuleCoefficient Gf (fieldBaseChange Y kbar)
  let G' := etaleModuleCoefficient Gf (Spec (.of kbar))
  let F₁R := etaleModuleDirectImage.{u, 0} R fk
  let F₂R := etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))
  let θR := etaleModuleDirectImageComp.{u, 0} R πb fk fk hw
  let F₁S := etaleModuleDirectImage.{u, 0} S fk
  let F₂S := etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))
  let θS := etaleModuleDirectImageComp.{u, 0} S πb fk fk hw
  let γ := etaleModuleGlobalSectionsCoefficientIso Gf (Spec (.of kbar))
  let θ' := sheafCompose_map (fieldBaseChange Y kbar).smallEtaleTopology θ
  let θk := sheafCompose_map (Spec (.of kbar)).smallEtaleTopology θ
  let m := F₁R.map f ≫ θR.hom.app B
  have hθ := congrArg Iso.hom (coefficient_mapIso_directImageComp_app Gf πb fk fk hw B)
  simp only [Functor.mapIso_hom, Iso.app_hom] at hθ
  have key : F₁S.map (G.map f ≫ (etaleModuleDirectImage.{u, 0} S πb).map (θ'.app B)) ≫
      θS.hom.app (G.obj B) = G'.map m ≫ θk.app (F₁R.obj B) := by
    refine ((congrArg (· ≫ θS.hom.app (G.obj B)) (F₁S.map_comp _ _)).trans
      (Category.assoc _ _ _)).trans ?_
    refine (congrArg (F₁S.map (G.map f) ≫ ·) (θS.hom.naturality (θ'.app B))).trans ?_
    refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ θk.app (F₁R.obj B)) ?_)
    rw [← hθ]
    exact (G'.map_comp (F₁R.map f) (θR.hom.app B)).symm
  show F₂S.map (F₁S.map (G.map f ≫ (etaleModuleDirectImage.{u, 0} S πb).map (θ'.app B)) ≫
      θS.hom.app (G.obj B)) ≫ γ.hom.app (F₁R.obj B) =
    γ.hom.app (F₁R.obj A) ≫ θ.app (F₂R.obj (F₁R.obj A)) ≫ Gf.map (F₂R.map m)
  rw [key]
  refine ((congrArg (· ≫ γ.hom.app (F₁R.obj B)) (F₂S.map_comp _ _)).trans
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg (F₂S.map (G'.map m) ≫ ·)
    (etaleModuleGlobalSectionsCoefficientIso_hom_natTrans Gf (Spec (.of kbar)) θ
      (F₁R.obj B))).trans ?_
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ θ.app _) (γ.hom.naturality m)).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (γ.hom.app _ ≫ ·) (θ.naturality (F₂R.map m)))

/-- **Step 7 of [Stacks, Tag 03UG]: the Frobenius trace after the change of coefficients
`Gf`, twisted by a natural endomorphism `θ` of `Gf`.** Here `Gf : Mod_R ⥤ Mod_S` is any additive
functor commuting with filtered colimits, applied sectionwise, which carries injective sheaves to
sheaves acyclic everywhere (`hacyc`). For a bounded below complex `L` of sheaves of `R`-modules
on `Y_étale` whose restriction to `Y_k̄` has injective stalks and with `RΓ(Y_k̄, L|)` perfect,
`RΓ(Y_k̄, H(L)|)` is perfect and the trace of `θ ∘ π_Y^*` on it (the derived endomorphism of the
Frobenius twist followed by `θ`) is `H♮_θ(Tr_R(π_Y^* | RΓ(Y_k̄, L|)))`. -/
theorem perfectDerivedTrace_derivedTwistEndo_coefficient
    (hacyc : ∀ (X : Scheme.{u}) (I : EtaleModules.{u, 0} R X), Injective I →
      IsAcyclicEverywhere ((sheafCompose X.smallEtaleTopology Gf).obj I))
    (θ : Gf ⟶ Gf)
    (hR : Module.Baer R R)
    (hΦ : PreservesFiniteProjective.{0, u + 1} (Gf))
    (L : CochainComplex.Plus (EtaleModules.{u, 0} R Y.left))
    (hL : ∀ (x : fieldBaseChange Y kbar) (n : ℤ), Module.Injective R
      (((residueEtalePoint.{u, 0} (fieldBaseChange Y kbar) x).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L).obj.X n)))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} R (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} R Y kbar L))))) :
    ∃ hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} S (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} S Y kbar
            ((etaleModuleCoefficient (Gf)
              Y.left).mapCochainComplexPlus.obj L))))),
      perfectDerivedTrace S ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} S (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleCoefficient (Gf)
            Y.left).mapCochainComplexPlus.obj L))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} S
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleCoefficient (Gf)
              Y.left).mapCochainComplexPlus.obj L))
          (Y := (etaleModuleDirectImage.{u, 0} S
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} S
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleCoefficient (Gf)
                Y.left).mapCochainComplexPlus.obj L)))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} S Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleCoefficient (Gf)
              Y.left).mapCochainComplexPlus.obj L).obj) ≫
          (etaleModuleDirectImage.{u, 0} S
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} S
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              (ObjectProperty.homMk
                (X := (etaleModuleCoefficient (Gf)
                  Y.left).mapCochainComplexPlus.obj L)
                (Y := (etaleModuleCoefficient (Gf)
                  Y.left).mapCochainComplexPlus.obj L)
                ((NatTrans.mapHomologicalComplex
                (sheafCompose_map Y.left.smallEtaleTopology θ) (ComplexShape.up ℤ)).app
                  L.obj)))))) =
        functorTraceMap (Gf) θ hΦ
          (perfectDerivedTrace R ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
            (frobeniusRestrictionCohomologyEndo.{u, 0} R Y kbar p q hcard L))) := by
  let π := fieldBaseChangeProj Y kbar
  let πb := geometricFrobeniusBaseChange Y kbar p q hcard
  let fk := pullback.snd Y.hom (specAlgebraMap k kbar)
  let hw := (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
  let G := etaleModuleCoefficient Gf (fieldBaseChange Y kbar)
  let K := (etaleModuleInverseImage.{u, 0} R π).mapCochainComplexPlus.obj L
  let τ : K ⟶ (etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj K :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} R Y kbar p q hcard) (ComplexShape.up ℤ)).app L.obj)
  obtain ⟨T, ψ, hq, hinj, g, hg⟩ :=
    Functor.exists_twist_lift_of_injectiveResolution (etaleModuleDirectImage.{u, 0} R πb) K τ
  let F₁R := etaleModuleDirectImage.{u, 0} R fk
  let F₂R := etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))
  let θR := etaleModuleDirectImageComp.{u, 0} R πb fk fk hw
  have hT' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj
        (F₂R.mapCochainComplexPlus.obj (F₁R.mapCochainComplexPlus.obj T)).obj) :=
    StacksDraft.Perfect.isPerfect_of_iso (Functor.twistResolutionIso F₁R F₂R ψ hinj).symm hperf
  have hRtr := Functor.perfectDerivedTrace_derivedTwistEndo_eq
    (etaleModuleDirectImage.{u, 0} R πb) F₁R F₂R θR ψ hinj τ g hg hperf hT'
  rw [← frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo] at hRtr
  let X := (F₂R.mapCochainComplexPlus.obj (F₁R.mapCochainComplexPlus.obj T)).obj
  have hXinj : ∀ n, Injective (X.X n) := fun n =>
    have := hinj n; injective_etaleModuleGlobalSections R (F₁R.obj (T.obj.X n))
  obtain ⟨d, hd⟩ := (F₂R.mapCochainComplexPlus.obj (F₁R.mapCochainComplexPlus.obj T)).property
  have : X.IsStrictlyGE d := hd
  let gX := (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} R πb) F₁R F₂R θR T g).hom
  have hGX := isPerfect_map_of_injective_of_baer Gf hΦ hR X d hT'
  have hHtr := perfectDerivedTrace_map_of_injective_of_baer Gf hΦ θ hR X d hT' gX
  let LS := (etaleModuleCoefficient Gf Y.left).mapCochainComplexPlus.obj L
  let KS := (etaleModuleInverseImage.{u, 0} S π).mapCochainComplexPlus.obj LS
  let τS : KS ⟶ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.obj KS :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} S Y kbar p q hcard) (ComplexShape.up ℤ)).app LS.obj)
  let TS := G.mapCochainComplexPlus.obj T
  let c : KS ≅ G.mapCochainComplexPlus.obj K := ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex (asIso (inverseImageCoefficientTwoSquare Gf π).natTrans)
      (ComplexShape.up ℤ)).app L.obj)
  let ψS : KS ⟶ TS := c.hom ≫ G.mapCochainComplexPlus.map ψ
  let gS : TS ⟶ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.obj TS :=
    G.mapCochainComplexPlus.map g
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := T.property
  have : K.obj.IsStrictlyGE (min a b) := K.obj.isStrictlyGE_of_ge _ a (min_le_left _ _)
  have : T.obj.IsStrictlyGE (min a b) := T.obj.isStrictlyGE_of_ge _ b (min_le_right _ _)
  have : QuasiIso ψ.hom := hq
  have hψG : QuasiIso (G.mapCochainComplexPlus.map ψ).hom :=
    AlgebraicGeometry.Scheme.quasiIso_sheafCompose_map_of_injective_stalks Gf ψ.hom (min a b) hL
      (fun x n => have := hinj n; moduleInjective_residueEtalePoint_sheafFiber _ x)
  have : QuasiIso ψS.hom := by
    show QuasiIso (c.hom.hom ≫ (G.mapCochainComplexPlus.map ψ).hom)
    have : IsIso c.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map c.hom))
    infer_instance
  have hcτ : τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map c.hom =
      c.hom ≫ G.mapCochainComplexPlus.map τ := by
    ext n : 2
    exact frobeniusBaseChangeTwist_coefficient Gf Y kbar p q hcard (L.obj.X n)
  obtain ⟨b', hb'⟩ := ((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj T).property
  have : ∀ n, Injective
      (((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj T).obj.X n) := fun n => by
    have := hinj n
    show Injective ((etaleModuleDirectImage.{u, 0} R πb).obj (T.obj.X n))
    infer_instance
  have := CochainComplex.isKInjective_of_injective
    ((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj T).obj b'
  have hGhom := Q_map_mapHomologicalComplex_eq_of_isKInjective G
    (τ ≫ (etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.map ψ).hom (ψ ≫ g).hom
    (congrArg DerivedCategory.Plus.ι.map hg)
  have hS : DerivedCategory.Plus.Q.map
      (τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS) =
      DerivedCategory.Plus.Q.map (ψS ≫ gS) := by
    apply DerivedCategory.Plus.ι.map_injective
    have e1 : (τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS).hom =
        c.hom.hom ≫ (G.mapHomologicalComplex _).map
          (τ ≫ (etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.map ψ).hom := by
      have := congrArg (fun f => f.hom ≫ (G.mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.map ψ)).hom) hcτ
      simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] at this
      simp only [ψS, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom]
      exact this
    have e2 : (ψS ≫ gS).hom = c.hom.hom ≫ (G.mapHomologicalComplex _).map (ψ ≫ g).hom := by
      simp only [ψS, gS, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
      rfl
    show DerivedCategory.Q.map
        (τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS).hom =
      DerivedCategory.Q.map (ψS ≫ gS).hom
    rw [e1, e2]
    exact (Functor.map_comp _ _ _).trans ((congrArg (DerivedCategory.Q.map c.hom.hom ≫ ·)
      hGhom).trans (Functor.map_comp _ _ _).symm)
  let δ : LS ⟶ LS := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (sheafCompose_map Y.left.smallEtaleTopology θ) (ComplexShape.up ℤ)).app L.obj)
  let θT : TS ⟶ TS := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (sheafCompose_map (fieldBaseChange Y kbar).smallEtaleTopology θ) (ComplexShape.up ℤ)).app T.obj)
  let τ'S := τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map
    ((etaleModuleInverseImage.{u, 0} S π).mapCochainComplexPlus.map δ)
  let g'S := gS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map θT
  have hδ : (etaleModuleInverseImage.{u, 0} S π).mapCochainComplexPlus.map δ ≫ ψS = ψS ≫ θT := by
    ext n : 2
    have h₁ := inverseImageCoefficientApp_naturality Gf π θ (L.obj.X n)
    have h₂ := (sheafCompose_map (fieldBaseChange Y kbar).smallEtaleTopology θ).naturality
      (ψ.hom.f n)
    show (etaleModuleInverseImage.{u, 0} S π).map
        ((sheafCompose_map Y.left.smallEtaleTopology θ).app (L.obj.X n)) ≫
        inverseImageCoefficientApp Gf π (L.obj.X n) ≫ G.map (ψ.hom.f n) =
      (inverseImageCoefficientApp Gf π (L.obj.X n) ≫ G.map (ψ.hom.f n)) ≫
        (sheafCompose_map (fieldBaseChange Y kbar).smallEtaleTopology θ).app (T.obj.X n)
    rw [reassoc_of% h₁, Category.assoc]
    exact congrArg _ h₂.symm
  have hS' : DerivedCategory.Plus.Q.map
      (τ'S ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS) =
      DerivedCategory.Plus.Q.map (ψS ≫ g'S) := by
    have e1 : τ'S ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS =
        (τS ≫ (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS) ≫
          (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map θT := by
      simp only [τ'S, Category.assoc, ← Functor.map_comp, hδ]
    rw [e1, Functor.map_comp, hS, ← Functor.map_comp, Category.assoc]
  let F₁S := etaleModuleDirectImage.{u, 0} S fk
  let F₂S := etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))
  let θS := etaleModuleDirectImageComp.{u, 0} S πb fk fk hw
  have : IsIso (Functor.twistComparison F₁S F₂S TS) :=
    Functor.isIso_twistComparison_of_rightAcyclic F₁S F₂S TS
      (fun n => rightAcyclic_directImage_of_isAcyclicEverywhere fk _ (hacyc _ _ (hinj n)))
      (fun n => Functor.rightAcyclic_of_exact F₂S _)
  let γ := etaleModuleGlobalSectionsCoefficientIso Gf (Spec (.of kbar))
  let e : (F₂S.mapCochainComplexPlus.obj (F₁S.mapCochainComplexPlus.obj TS)).obj ≅
      (Gf.mapHomologicalComplex (ComplexShape.up ℤ)).obj X :=
    HomologicalComplex.Hom.isoOfComponents (fun n => γ.app (F₁R.obj (T.obj.X n)))
      (fun i j _ => (γ.hom.naturality (F₁R.map (T.obj.d i j))).symm)
  have hechain :
      (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} S πb) F₁S F₂S θS TS g'S).hom ≫
        e.hom = e.hom ≫ ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app X ≫
        (Gf.mapHomologicalComplex (ComplexShape.up ℤ)).map gX) := by
    ext n : 1
    exact globalSections_coefficient_frobeniusTwist_comm Gf Y kbar p q hcard θ
      (A := T.obj.X n) (B := T.obj.X n) (g.hom.f n)
  have hTS : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj
        (F₂S.mapCochainComplexPlus.obj (F₁S.mapCochainComplexPlus.obj TS)).obj) :=
    StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso e) hGX
  have hperf' := StacksDraft.Perfect.isPerfect_of_iso
    (Functor.twistResolutionIsoOfIsIso F₁S F₂S ψS) hTS
  refine ⟨hperf', ?_⟩
  have hStr := Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_isIso
    (etaleModuleDirectImage.{u, 0} S πb) F₁S F₂S θS ψS τ'S g'S hS' hperf' hTS
  refine hStr.trans ?_
  rw [hRtr, ← hHtr]
  refine perfectDerivedTrace_congr S ⟨_, hTS⟩ ⟨_, hGX⟩ (DerivedCategory.Q.mapIso e) _ _ ?_
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp, hechain, Functor.map_comp]

end Coefficient

section BimoduleHom

variable {R S : Type} [Ring R] [Ring S] [Finite R] (N : Type (u + 1)) [AddCommGroup N]
  [Module R N] [Module Sᵐᵒᵖ N] [SMulCommClass Sᵐᵒᵖ R N] [Finite N]

/-- On the small étale site of a scheme `X`, sheafification commutes with the functor
`Hom_R(N, -)` from `R`-modules to `S`-modules. -/
instance bimoduleHom_preservesSheafification (X : Scheme.{u}) :
    X.smallEtaleTopology.PreservesSheafification (ModuleCat.BimoduleHom.functor R S N) :=
  ModuleCat.BimoduleHom.preservesSheafification N _

/-- The functor `Hom_R(N, -)` from `R`-modules to `S`-modules preserves filtered colimits. -/
instance bimoduleHom_preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u + 1} (ModuleCat.BimoduleHom.functor R S N) :=
  have := ModuleCat.BimoduleHom.preservesFilteredColimitsOfSize_of_univLE.{u + 1, 0, u + 1}
    (R := R) (S := S) N
  CategoryTheory.Limits.preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _

/-- The functor `Hom_R(N, -)` from `R`-modules to `S`-modules preserves left Kan extensions
along the opposite of the small étale base change functor of a morphism of schemes. -/
instance bimoduleHom_preservesLeftKanExtensions {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ModuleCat.BimoduleHom.functor R S N).PreservesLeftKanExtensions
      (smallEtaleBaseChange g).op :=
  inferInstance

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsSepClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Step 7 of [Stacks, Tag 03UG]: the Frobenius trace after the change of coefficients
`H = Hom_R(N, -)`, twisted by a natural endomorphism `θ` of `H`.** For a bounded below complex
`L` of sheaves of `R`-modules on `Y_étale` whose restriction to `Y_k̄` has injective stalks and
with `RΓ(Y_k̄, L|)` perfect, `RΓ(Y_k̄, H(L)|)` is perfect and the trace of `θ ∘ π_Y^*` on it (the
derived endomorphism of the Frobenius twist followed by `θ`) is
`H♮_θ(Tr_R(π_Y^* | RΓ(Y_k̄, L|)))`. -/
theorem perfectDerivedTrace_derivedTwistEndo_bimoduleHom
    (θ : ModuleCat.BimoduleHom.functor R S N ⟶ ModuleCat.BimoduleHom.functor R S N)
    (hR : Module.Baer R R)
    (hΦ : PreservesFiniteProjective.{0, u + 1} (ModuleCat.BimoduleHom.functor R S N))
    (L : CochainComplex.Plus (EtaleModules.{u, 0} R Y.left))
    (hL : ∀ (x : fieldBaseChange Y kbar) (n : ℤ), Module.Injective R
      (((residueEtalePoint.{u, 0} (fieldBaseChange Y kbar) x).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L).obj.X n)))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} R (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} R Y kbar L))))) :
    ∃ hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} S (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} S Y kbar
            ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
              Y.left).mapCochainComplexPlus.obj L))))),
      perfectDerivedTrace S ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} S (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} S (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
            Y.left).mapCochainComplexPlus.obj L))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} S
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
              Y.left).mapCochainComplexPlus.obj L))
          (Y := (etaleModuleDirectImage.{u, 0} S
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} S
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
                Y.left).mapCochainComplexPlus.obj L)))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} S Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
              Y.left).mapCochainComplexPlus.obj L).obj) ≫
          (etaleModuleDirectImage.{u, 0} S
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} S
                (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              (ObjectProperty.homMk
                (X := (etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
                  Y.left).mapCochainComplexPlus.obj L)
                (Y := (etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
                  Y.left).mapCochainComplexPlus.obj L)
                ((NatTrans.mapHomologicalComplex
                (sheafCompose_map Y.left.smallEtaleTopology θ) (ComplexShape.up ℤ)).app
                  L.obj)))))) =
        functorTraceMap (ModuleCat.BimoduleHom.functor R S N) θ hΦ
          (perfectDerivedTrace R ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
            (frobeniusRestrictionCohomologyEndo.{u, 0} R Y kbar p q hcard L))) :=
  perfectDerivedTrace_derivedTwistEndo_coefficient (ModuleCat.BimoduleHom.functor R S N)
    Y kbar p q hcard
    (fun _ I _ => isAcyclicEverywhere_bimoduleHom_of_injective N I) θ hR hΦ L hL hperf

/-- **Step 7 of [Stacks, Tag 03UG]: the Frobenius trace after the change of coefficients
`H = Hom_R(N, -)`.** For a bounded below complex `L` of sheaves of `R`-modules on `Y_étale` whose
restriction to `Y_k̄` has injective stalks and with `RΓ(Y_k̄, L|)` perfect, `RΓ(Y_k̄, H(L)|)` is
perfect and `Tr_S(π_Y^* | RΓ(Y_k̄, H(L)|)) = H♮(Tr_R(π_Y^* | RΓ(Y_k̄, L|)))`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_bimoduleHom
    (hR : Module.Baer R R)
    (hΦ : PreservesFiniteProjective.{0, u + 1} (ModuleCat.BimoduleHom.functor R S N))
    (L : CochainComplex.Plus (EtaleModules.{u, 0} R Y.left))
    (hL : ∀ (x : fieldBaseChange Y kbar) (n : ℤ), Module.Injective R
      (((residueEtalePoint.{u, 0} (fieldBaseChange Y kbar) x).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj L).obj.X n)))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} R (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} R (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} R Y kbar L))))) :
    ∃ hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} S (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} S (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} S Y kbar
            ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
              Y.left).mapCochainComplexPlus.obj L))))),
      perfectDerivedTrace S ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} S Y kbar p q hcard
            ((etaleModuleCoefficient (ModuleCat.BimoduleHom.functor R S N)
              Y.left).mapCochainComplexPlus.obj L))) =
        functorTraceMap (ModuleCat.BimoduleHom.functor R S N) (𝟙 _) hΦ
          (perfectDerivedTrace R ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
            (frobeniusRestrictionCohomologyEndo.{u, 0} R Y kbar p q hcard L))) := by
  obtain ⟨hperf', h⟩ :=
    perfectDerivedTrace_derivedTwistEndo_bimoduleHom N Y kbar p q hcard (𝟙 _) hR hΦ L hL hperf
  refine ⟨hperf', Eq.trans ?_ h⟩
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  convert rfl using 5
  refine (congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)
  refine (congrArg _ ?_).trans (CategoryTheory.Functor.map_id _ _)
  refine (congrArg _ ?_).trans (CategoryTheory.Functor.map_id _ _)
  exact ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun n => rfl)

end BimoduleHom

end Stacks.EtaleCohomology

end
