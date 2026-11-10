module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AcyclicTwistResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleCoinduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TorsionHomAcyclic

/-!
# Compactly supported cohomology after a left exact change of coefficients

Let `Ψ : Mod_R ⥤ Mod_S` be an additive change of coefficients preserving sheaves, commuting with
inverse image along `X̄_k̄ ⟶ X̄` and with extension by zero along `j : X ⟶ X̄` (the comparisons are
invertible).  Suppose that the terms of `(j_! K)|_{X̄_k̄}` are `Ψ`-acyclic and that `Ψ` carries
injective sheaves to sheaves acyclic everywhere.  Then for a bounded below complex `Q` of
`Ψ`-acyclic `R`-modules with an isomorphism `Q ≅ RΓ_c(X_k̄, K)` and a chain endomorphism `g` of
`Q` representing the geometric Frobenius `π_X^*`, there is an isomorphism

`Ψ(Q) ≅ RΓ_c(X_k̄, Ψ K)`

in the derived category of `S`-modules carrying `Ψ(g)` to `π_X^*`.  Both sides are computed on an
injective resolution `I` of `(j_! K)|_{X̄_k̄}`: `Ψ(I)` resolves `(j_! Ψ K)|_{X̄_k̄}` by sheaves
acyclic everywhere, the Frobenius twist lifts to `I` and `Ψ` of the lift lifts the twist of
`Ψ K`, and `RΓ(X̄_k̄, -)` of `Ψ(I)` is `Ψ` of `RΓ(X̄_k̄, I)`.

## Main results

* `Stacks.EtaleCohomology.compactSupportRestrictedComplexCoefficientIso`: `(j_! Ψ K)|_{X̄_k̄} ≅
  Ψ((j_! K)|_{X̄_k̄})`.
* `Stacks.EtaleCohomology.compactSupportTwist_comp_coefficientIso`: it intertwines the Frobenius
  twists.
* `Stacks.EtaleCohomology.globalSectionsCoefficientIso`: global sections commute with `Ψ`.
* `Stacks.EtaleCohomology.twistChainEndo_sheafCompose`: the chain model of the Frobenius of
  `RΓ(X̄_k̄, Ψ I)` is `Γ ∘ Ψ` of the chain model for `I`.
* `Stacks.EtaleCohomology.exists_iso_compactSupport_coefficientChange`: `Ψ(Q) ≅ RΓ_c(X_k̄, Ψ K)`,
  carrying `Ψ(g)` to `π_X^*`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {R S : Type} [Ring R] [Ring S] (Ψ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
  [Ψ.Additive] [∀ X : Scheme.{u}, X.smallEtaleTopology.HasSheafCompose Ψ]

/-- A sheaf acyclic everywhere has a direct image acyclic everywhere. -/
theorem IsAcyclicEverywhere.directImage {T : Type} [Ring T] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A : EtaleModules.{u, 0} T X} (hA : IsAcyclicEverywhere A) :
    IsAcyclicEverywhere ((etaleModuleDirectImage.{u, 0} T f).obj A) := by
  intro V
  have hFG : ∀ I : EtaleModules.{u, 0} T X, Injective I →
      ((sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} T)).obj (Opposite.op V)).rightAcyclic
        ((etaleModuleDirectImage.{u, 0} T f).obj I) := fun I hI =>
    have : Injective ((etaleModuleDirectImage.{u, 0} T f).obj I) :=
      (etaleModuleDirectImage.{u, 0} T f).injective_obj_of_injective hI
    Functor.rightAcyclic_of_injective _ _
  have hX := rightAcyclic_directImage_of_isAcyclicEverywhere f A hA
  have hcomp : (etaleModuleDirectImage.{u, 0} T f ⋙
      (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} T)).obj
        (Opposite.op V)).rightAcyclic A :=
    Functor.rightAcyclic_of_iso (Iso.refl _ : (sheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} T)).obj (Opposite.op ((smallEtaleBaseChange f).obj V)) ≅ _) A
      (hA ((smallEtaleBaseChange f).obj V))
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat] at hcomp ⊢
  intro n hn
  exact (hcomp n hn).of_iso
    (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso _ _ hFG A hX n).symm

omit [Ψ.Additive] in
/-- A change of coefficients commutes with the composition isomorphism of direct images. -/
lemma sheafCompose_map_etaleModuleDirectImageComp_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : EtaleModules.{u, 0} R X) :
    (sheafCompose Z.smallEtaleTopology Ψ).map
        ((etaleModuleDirectImageComp.{u, 0} R f g fg hfg).hom.app A) =
      (etaleModuleDirectImageComp.{u, 0} S f g fg hfg).hom.app
        ((sheafCompose X.smallEtaleTopology Ψ).obj A) := by
  apply Sheaf.hom_ext
  ext U : 2
  have h₁ := etaleModuleDirectImageComp_hom_app_hom_app R f g fg hfg A U
  have h₂ := etaleModuleDirectImageComp_hom_app_hom_app S f g fg hfg
    ((sheafCompose X.smallEtaleTopology Ψ).obj A) U
  exact (congrArg Ψ.map h₁).trans h₂.symm

/-- **The chain model of a twisted endomorphism after a change of coefficients.**  For a twist
`g : T ⟶ π_* T` of a bounded below complex on `Y` and `h = π ≫ h`, the chain model of the
endomorphism of `RΓ(Z, Rh_* Ψ T)` attached to `Ψ g` is `Γ ∘ Ψ` of the componentwise endomorphism
`h_*(g) ≫ θ` of `h_* T`. -/
lemma twistChainEndo_sheafCompose {Y Z : Scheme.{u}} (π : Y ⟶ Y) (h : Y ⟶ Z) (hπ : h = π ≫ h)
    (T : CochainComplex.Plus (EtaleModules.{u, 0} R Y))
    (gT : T ⟶ (etaleModuleDirectImage.{u, 0} R π).mapCochainComplexPlus.obj T) :
    (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} S π) (etaleModuleDirectImage.{u, 0} S h)
      (etaleModuleGlobalSections.{u, 0} S Z) (etaleModuleDirectImageComp.{u, 0} S π h h hπ)
      ((sheafCompose Y.smallEtaleTopology Ψ).mapCochainComplexPlus.obj T)
      ((sheafCompose Y.smallEtaleTopology Ψ).mapCochainComplexPlus.map gT)).hom =
    ((sheafCompose Z.smallEtaleTopology Ψ ⋙
        etaleModuleGlobalSections.{u, 0} S Z).mapHomologicalComplex _).map
      ((etaleModuleDirectImage.{u, 0} R h).mapCochainComplexPlus.map gT ≫
        Functor.twistCompMap (etaleModuleDirectImage.{u, 0} R π)
          (etaleModuleDirectImage.{u, 0} R h) (etaleModuleDirectImageComp.{u, 0} R π h h hπ)
          T).hom := by
  ext n : 1
  change (etaleModuleGlobalSections.{u, 0} S Z).map
      ((etaleModuleDirectImage.{u, 0} S h).map ((sheafCompose Y.smallEtaleTopology Ψ).map
          (gT.hom.f n)) ≫
        (etaleModuleDirectImageComp.{u, 0} S π h h hπ).hom.app
          ((sheafCompose Y.smallEtaleTopology Ψ).obj (T.obj.X n))) =
    (etaleModuleGlobalSections.{u, 0} S Z).map ((sheafCompose Z.smallEtaleTopology Ψ).map
      ((etaleModuleDirectImage.{u, 0} R h).map (gT.hom.f n) ≫
        (etaleModuleDirectImageComp.{u, 0} R π h h hπ).hom.app (T.obj.X n)))
  refine congrArg (etaleModuleGlobalSections.{u, 0} S Z).map
    (Eq.symm (((sheafCompose Z.smallEtaleTopology Ψ).map_comp _ _).trans ?_))
  exact congrArg (fun φ => (sheafCompose Z.smallEtaleTopology Ψ).map
      ((etaleModuleDirectImage.{u, 0} R h).map (gT.hom.f n)) ≫ φ)
    (sheafCompose_map_etaleModuleDirectImageComp_hom_app Ψ π h h hπ (T.obj.X n))

/-- `Ψ` of `Γ` of a morphism of bounded below complexes is `Γ ⋙ Ψ` of it. -/
lemma mapHomologicalComplex_map_mapCochainComplexPlus_map_hom {A B C : Type*} [Category* A]
    [Category* B] [Category* C] [Preadditive A] [Preadditive B] [Preadditive C] (F : A ⥤ B)
    (G : B ⥤ C) [F.Additive] [G.Additive] {K L : CochainComplex.Plus A} (φ : K ⟶ L) :
    (G.mapHomologicalComplex _).map (F.mapCochainComplexPlus.map φ).hom =
      ((F ⋙ G).mapHomologicalComplex _).map φ.hom :=
  rfl

section CompactSupport

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The comparison `j_!(Ψ 𝒩) ⟶ Ψ(j_! 𝒩)`. -/
abbrev extensionByZeroMate :=
  sheafComposeCoefficientMate (Scheme.Etale.smallEtaleCompose j.immersion) _ _
    (etaleModuleExtensionByZeroAdj.{u, 0} R j.immersion)
    (etaleModuleExtensionByZeroAdj.{u, 0} S j.immersion) Ψ

/-- The comparison `pr^{-1}(Ψ 𝒩) ⟶ Ψ(pr^{-1} 𝒩)` for `pr : X̄_k̄ ⟶ X̄`. -/
abbrev fieldBaseChangeMate :=
  sheafComposeCoefficientMate (smallEtaleBaseChange (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (Over.mk j.toBase).left.smallEtaleTopology
    (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
    (etaleModuleInverseImageAdj.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar))
    (etaleModuleInverseImageAdj.{u, 0} S (fieldBaseChangeProj (Over.mk j.toBase) kbar)) Ψ

variable [IsIso (extensionByZeroMate Ψ f j)]
  [IsIso (fieldBaseChangeMate Ψ f j kbar)]

/-- `pr^{-1} j_! ∘ Ψ ≅ Ψ ∘ pr^{-1} j_!`, the two comparisons. -/
def compactSupportRestrictionCoefficientIso :
    sheafCompose X.smallEtaleTopology Ψ ⋙ etaleModuleExtensionByZero.{u, 0} S j.immersion ⋙
        etaleModuleInverseImage.{u, 0} S (fieldBaseChangeProj (Over.mk j.toBase) kbar) ≅
      etaleModuleExtensionByZero.{u, 0} R j.immersion ⋙
        etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar) ⋙
          sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (extensionByZeroMate Ψ f j)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (fieldBaseChangeMate Ψ f j kbar))

/-- **`(j_! Ψ K)|_{X̄_k̄} ≅ Ψ((j_! K)|_{X̄_k̄})`**, termwise on a bounded below complex. -/
def compactSupportRestrictedComplexCoefficientIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} R X)) :
    compactSupportRestrictedComplex f j kbar S
        ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K) ≅
      (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapCochainComplexPlus.obj (compactSupportRestrictedComplex f j kbar R K) :=
  ObjectProperty.isoMk _ (by
    exact (NatIso.mapHomologicalComplex (compactSupportRestrictionCoefficientIso Ψ f j kbar)
      (ComplexShape.up ℤ)).app K.obj)

end CompactSupport

section Frobenius

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsIso (extensionByZeroMate Ψ f j)] [IsIso (fieldBaseChangeMate Ψ f j kbar)]

/-- The Frobenius twist of `(j_! K)|_{X̄_k̄}`, a morphism of complexes. -/
abbrev compactSupportTwist (T : Type) [Ring T] (K : CochainComplex.Plus (EtaleModules.{u, 0} T X)) :
    compactSupportRestrictedComplex f j kbar T K ⟶
      (etaleModuleDirectImage.{u, 0} T (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q
        hcard)).mapCochainComplexPlus.obj (compactSupportRestrictedComplex f j kbar T K) :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (frobeniusBaseChangeTwist.{u, 0} T (Over.mk j.toBase) kbar p q hcard) (ComplexShape.up ℤ)).app
      ((etaleModuleExtensionByZero.{u, 0} T j.immersion).mapCochainComplexPlus.obj K).obj)

/-- **The coefficient comparison intertwines the Frobenius twists.** -/
theorem compactSupportTwist_comp_coefficientIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} R X)) :
    compactSupportTwist f j kbar p q hcard S
        ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K) ≫
      (etaleModuleDirectImage.{u, 0} S (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q
        hcard)).mapCochainComplexPlus.map
          (compactSupportRestrictedComplexCoefficientIso Ψ f j kbar K).hom =
    (compactSupportRestrictedComplexCoefficientIso Ψ f j kbar K).hom ≫
      (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapCochainComplexPlus.map (compactSupportTwist f j kbar p q hcard R K) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun n => ?_)
  let L := (etaleModuleExtensionByZero.{u, 0} R j.immersion).obj (K.obj.X n)
  have h1 := (frobeniusBaseChangeTwist.{u, 0} S (Over.mk j.toBase) kbar p q hcard).naturality
    ((extensionByZeroMate Ψ f j).app (K.obj.X n))
  have h2 := frobeniusBaseChangeTwist_sheafCompose Ψ (Over.mk j.toBase) kbar p q hcard L
  change (frobeniusBaseChangeTwist.{u, 0} S (Over.mk j.toBase) kbar p q hcard).app _ ≫
      (etaleModuleDirectImage.{u, 0} S _).map
        ((etaleModuleInverseImage.{u, 0} S _).map ((extensionByZeroMate Ψ f j).app
          (K.obj.X n)) ≫ (fieldBaseChangeMate Ψ f j kbar).app L) =
    ((etaleModuleInverseImage.{u, 0} S _).map ((extensionByZeroMate Ψ f j).app
          (K.obj.X n)) ≫ (fieldBaseChangeMate Ψ f j kbar).app L) ≫
      (sheafCompose _ Ψ).map
        ((frobeniusBaseChangeTwist.{u, 0} R (Over.mk j.toBase) kbar p q hcard).app L)
  dsimp only [Functor.comp_map] at h1
  rw [Functor.map_comp, ← Category.assoc, ← h1, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) h2

/-- Conjugation of a commutative square by an isomorphism. -/
lemma Iso.inv_comp_eq_comp_inv_of_comp_hom {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    {f : X ⟶ X} {g : Y ⟶ Y} (h : f ≫ e.hom = e.hom ≫ g) : e.inv ≫ f = g ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Global sections commute with a change of coefficients, up to the identification of global
sections with sections over the terminal object. -/
def globalSectionsCoefficientIso (Y : Scheme.{u}) :
    sheafCompose Y.smallEtaleTopology Ψ ⋙ etaleModuleGlobalSections.{u, 0} S Y ≅
      etaleModuleGlobalSections.{u, 0} R Y ⋙ Ψ :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
      (ModuleCat.{u + 1} S) terminalIsTerminal) ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      sheafCompose Y.smallEtaleTopology Ψ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} S)).obj
            (Opposite.op (⊤_ Y.Etale)) ≅
        (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (Opposite.op (⊤_ Y.Etale)) ⋙
          Ψ) ≪≫
    Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
      (ModuleCat.{u + 1} R) terminalIsTerminal).symm Ψ

/-- **Compactly supported cohomology after a left exact change of coefficients**, with its
Frobenius.  Let `Ψ` commute with the inverse image to `X̄_k̄` and with extension by zero along
`j`, let the terms of `(j_! K)|_{X̄_k̄}` be `Ψ`-acyclic and let `Ψ` carry injective sheaves to
sheaves acyclic everywhere.  For a bounded below complex `Q` of `Ψ`-acyclic `R`-modules with
`e_M : Q ≅ RΓ_c(X_k̄, K)` and a chain endomorphism `g` of `Q` representing `π_X^*`, there is an
isomorphism `Ψ(Q) ≅ RΓ_c(X_k̄, Ψ K)` carrying `Ψ(g)` to `π_X^*`. -/
theorem exists_iso_compactSupport_coefficientChange
    (K : CochainComplex.Plus (EtaleModules.{u, 0} R X))
    (hA1 : ∀ n, (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
      Ψ).rightAcyclic ((compactSupportRestrictedComplex f j kbar R K).obj.X n))
    (hA2 : ∀ I : EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar), Injective I →
      IsAcyclicEverywhere
        ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).obj I))
    (Q : CochainComplex (ModuleCat.{u + 1} R) ℤ) (hQ : CochainComplex.plus _ Q)
    (hA3 : ∀ i, Ψ.rightAcyclic (Q.X i)) (g : Q ⟶ Q)
    (eM : DerivedCategory.Q.obj Q ≅
      DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} R f j kbar K))
    (hg : DerivedCategory.Q.map g = eM.hom ≫
      DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} R f j kbar p q hcard K) ≫
        eM.inv) :
    ∃ e : DerivedCategory.Q.obj ((Ψ.mapHomologicalComplex _).obj Q) ≅
        DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} S f j kbar
          ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K)),
      DerivedCategory.Q.map ((Ψ.mapHomologicalComplex _).map g) ≫ e.hom =
        e.hom ≫ DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} S f j kbar p q
          hcard ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K)) := by
  classical
  let πb := geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard
  let hb := pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)
  let C := compactSupportRestrictedComplex f j kbar R K
  -- an injective resolution of `C` and a lift of the twist
  obtain ⟨a₀, ha₀⟩ := (CochainComplex.plus_iff _ C.obj).1 C.property
  obtain ⟨Rs, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a₀ C.obj
  let T : CochainComplex.Plus (EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar)) :=
    ⟨Rs.cocomplex, Rs.boundedBelow⟩
  let ψ : C ⟶ T := ObjectProperty.homMk Rs.ι
  have : QuasiIso ψ.hom := Rs.quasiIso
  have hT : ∀ n, Injective (T.obj.X n) := Rs.injective
  obtain ⟨gT, hgT⟩ := Functor.exists_twist_lift (etaleModuleDirectImage.{u, 0} R πb) ψ hT
    (compactSupportTwist f j kbar p q hcard R K)
  have hR := Functor.twistResolutionIso_hom_comp (etaleModuleDirectImage.{u, 0} R πb)
    (etaleModuleDirectImage.{u, 0} R hb) (etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} R πb hb hb
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    ψ hT _ gT hgT
  -- the module complex `W = Γ(X̄_k̄, T)` and a chain map `Q ⟶ W`
  let W := (etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).mapCochainComplexPlus.obj
    ((etaleModuleDirectImage.{u, 0} R hb).mapCochainComplexPlus.obj T)
  have hW : ∀ n, Injective (W.obj.X n) := fun n => by
    have : Injective ((etaleModuleDirectImage.{u, 0} R hb).obj (T.obj.X n)) :=
      (etaleModuleDirectImage.{u, 0} R hb).injective_obj_of_injective (hT n)
    exact injective_etaleModuleGlobalSections_obj R
      ((etaleModuleDirectImage.{u, 0} R hb).obj (T.obj.X n))
  obtain ⟨fQ, hfQ⟩ := Functor.exists_Q_map_eq W.property
    (eM.hom ≫ (Functor.twistResolutionIso _ _ ψ hT).hom)
  have hfQiso : IsIso (DerivedCategory.Q.map fQ) := by
    rw [hfQ]
    infer_instance
  have : QuasiIso fQ := (DerivedCategory.isIso_Q_map_iff_quasiIso _ fQ).1 hfQiso
  have hgf : DerivedCategory.Q.map (g ≫ fQ) = DerivedCategory.Q.map (fQ ≫
      (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} R πb)
        (etaleModuleDirectImage.{u, 0} R hb) (etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} R πb hb hb
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
        T gT).hom) := by
    rw [Functor.map_comp, Functor.map_comp, hg, hfQ, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    change eM.hom ≫ DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo _ _ _ _ _ _) ≫ _ = _
    rw [hR, Category.assoc]
  -- the `S` side
  let μ := compactSupportRestrictedComplexCoefficientIso Ψ f j kbar K
  let ψS : compactSupportRestrictedComplex f j kbar S
      ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K) ⟶
      (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
        Ψ).mapCochainComplexPlus.obj T :=
    μ.hom ≫ (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
      Ψ).mapCochainComplexPlus.map ψ
  have hΨψ : QuasiIso ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
      Ψ).mapCochainComplexPlus.map ψ).hom :=
    Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic
      (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ) ψ.hom
      C.property T.property hA1 fun n => Functor.rightAcyclic_of_injective _ _
  have hμ : QuasiIso μ.hom.hom := by
    have : IsIso μ.hom.hom := Functor.map_isIso (ObjectProperty.ι _) μ.hom
    infer_instance
  have : QuasiIso ψS.hom := by
    change QuasiIso (μ.hom.hom ≫ ((sheafCompose (fieldBaseChange (Over.mk j.toBase)
      kbar).smallEtaleTopology Ψ).mapCochainComplexPlus.map ψ).hom)
    infer_instance
  have h₁S : ∀ n, (etaleModuleDirectImage.{u, 0} S hb).rightAcyclic
      (((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
        Ψ).mapCochainComplexPlus.obj T).obj.X n) := fun n =>
    rightAcyclic_directImage_of_isAcyclicEverywhere _ _ (hA2 _ (hT n))
  have h₂S : ∀ n, (etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))).rightAcyclic
      ((etaleModuleDirectImage.{u, 0} S hb).obj
        (((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapCochainComplexPlus.obj T).obj.X n)) :=
    fun n => rightAcyclic_globalSections_of_isAcyclicEverywhere _
      (IsAcyclicEverywhere.directImage hb (hA2 _ (hT n)))
  let gS : (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
        Ψ).mapCochainComplexPlus.obj T ⟶
      (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.obj
        ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapCochainComplexPlus.obj T) :=
    (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
      Ψ).mapCochainComplexPlus.map gT
  have hgS : DerivedCategory.Plus.Q.map (compactSupportTwist f j kbar p q hcard S
        ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K) ≫
        (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS) =
      DerivedCategory.Plus.Q.map (ψS ≫ gS) := by
    have htw := compactSupportTwist_comp_coefficientIso Ψ f j kbar p q hcard K
    have hinj : ∀ n, Injective
        (((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj T).obj.X n) := fun n =>
      (etaleModuleDirectImage.{u, 0} R πb).injective_obj_of_injective (hT n)
    have h' := Functor.Q_map_mapHomologicalComplex_eq_of_injective
      (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ)
      ((etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.obj T).property
      (a := (compactSupportTwist f j kbar p q hcard R K ≫
        (etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.map ψ).hom)
      (b := (ψ ≫ gT).hom) (congrArg DerivedCategory.Plus.ι.map hgT)
    have ha : (compactSupportTwist f j kbar p q hcard S
          ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K) ≫
          (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS).hom =
        μ.hom.hom ≫ ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapHomologicalComplex _).map
          (compactSupportTwist f j kbar p q hcard R K ≫
            (etaleModuleDirectImage.{u, 0} R πb).mapCochainComplexPlus.map ψ).hom := by
      ext n : 1
      have hn := congrArg (fun φ => φ.hom.f n) htw
      change _ ≫ (etaleModuleDirectImage.{u, 0} S πb).map (μ.hom.hom.f n ≫
          (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map
            (ψ.hom.f n)) =
        μ.hom.hom.f n ≫
          (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map
            (_ ≫ (etaleModuleDirectImage.{u, 0} R πb).map (ψ.hom.f n))
      exact (congrArg (_ ≫ ·) ((etaleModuleDirectImage.{u, 0} S πb).map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
            ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map_comp
              ((compactSupportTwist f j kbar p q hcard R K).hom.f n)
              ((etaleModuleDirectImage.{u, 0} R πb).map (ψ.hom.f n))).symm))))
    have hb : (ψS ≫ gS).hom =
        μ.hom.hom ≫ ((sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
          Ψ).mapHomologicalComplex _).map (ψ ≫ gT).hom := by
      ext n : 1
      change (μ.hom.hom.f n ≫
          (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map
            (ψ.hom.f n)) ≫
          (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map
            (gT.hom.f n) =
        μ.hom.hom.f n ≫
          (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology Ψ).map
            (ψ.hom.f n ≫ gT.hom.f n)
      rw [Functor.map_comp]
      exact Category.assoc _ _ _
    apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Q.map (compactSupportTwist f j kbar p q hcard S _ ≫
        (etaleModuleDirectImage.{u, 0} S πb).mapCochainComplexPlus.map ψS).hom =
      DerivedCategory.Q.map (ψS ≫ gS).hom
    exact (congrArg DerivedCategory.Q.map ha).trans ((DerivedCategory.Q.map_comp _ _).trans
      ((congrArg (_ ≫ ·) h').trans ((DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map hb).symm)))
  have hS := Functor.twistAcyclicResolutionIso_hom_comp (etaleModuleDirectImage.{u, 0} S πb)
    (etaleModuleDirectImage.{u, 0} S hb) (etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} S πb hb hb
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    ψS h₁S h₂S _ gS hgS
  have hΨf : QuasiIso ((Ψ.mapHomologicalComplex _).map fQ) :=
    Functor.quasiIso_mapHomologicalComplex_of_rightAcyclic Ψ fQ hQ W.property hA3
      fun n => Functor.rightAcyclic_of_injective _ _
  have h3 := Functor.Q_map_mapHomologicalComplex_eq_of_injective Ψ W.property hgf
  let N := (etaleModuleDirectImage.{u, 0} R hb).mapCochainComplexPlus.obj T
  let νC := (NatIso.mapHomologicalComplex (globalSectionsCoefficientIso Ψ (Spec (.of kbar)))
    (ComplexShape.up ℤ)).app N.obj
  let x := ((etaleModuleDirectImage.{u, 0} R hb).mapCochainComplexPlus.map gT ≫
    Functor.twistCompMap (etaleModuleDirectImage.{u, 0} R πb) (etaleModuleDirectImage.{u, 0} R hb)
      (etaleModuleDirectImageComp.{u, 0} R πb hb hb
        (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm) T).hom
  have hν := (NatIso.mapHomologicalComplex (globalSectionsCoefficientIso Ψ (Spec (.of kbar)))
    (ComplexShape.up ℤ)).hom.naturality x
  have hν' := Iso.inv_comp_eq_comp_inv_of_comp_hom νC hν
  have hS' := Iso.inv_comp_eq_comp_inv_of_comp_hom _ hS
  rw [twistChainEndo_sheafCompose] at hS'
  have e₁ : DerivedCategory.Q.map ((Ψ.mapHomologicalComplex _).map g) ≫
      DerivedCategory.Q.map ((Ψ.mapHomologicalComplex _).map fQ) =
      DerivedCategory.Q.map ((Ψ.mapHomologicalComplex _).map fQ) ≫
        DerivedCategory.Q.map
          (((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar)) ⋙ Ψ).mapHomologicalComplex
            _).map x) := by
    rw [← Functor.map_comp, ← Functor.map_comp, h3, Functor.map_comp, Functor.map_comp,
      mapHomologicalComplex_map_mapCochainComplexPlus_map_hom]
  have e₂ := congrArg DerivedCategory.Q.map hν'
  rw [Functor.map_comp, Functor.map_comp] at e₂
  have e₃ : DerivedCategory.Q.map (((sheafCompose (Spec (.of kbar)).smallEtaleTopology Ψ ⋙
        etaleModuleGlobalSections.{u, 0} S (Spec (.of kbar))).mapHomologicalComplex _).map x) ≫
      (Functor.twistAcyclicResolutionIso _ _ ψS h₁S h₂S).inv =
      (Functor.twistAcyclicResolutionIso _ _ ψS h₁S h₂S).inv ≫
        DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} S f j kbar p q
          hcard ((sheafCompose X.smallEtaleTopology Ψ).mapCochainComplexPlus.obj K)) := by
    rw [canonicalCompactSupportFrobenius, frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
    exact hS'.symm
  exact ⟨asIso (DerivedCategory.Q.map ((Ψ.mapHomologicalComplex _).map fQ)) ≪≫
    (DerivedCategory.Q.mapIso νC).symm ≪≫ (Functor.twistAcyclicResolutionIso _ _ ψS h₁S h₂S).symm,
    ((CommSq.mk e₁.symm).horiz_comp ((CommSq.mk e₂).horiz_comp (CommSq.mk e₃.symm))).w.symm⟩

end Frobenius

end Stacks.EtaleCohomology

end
