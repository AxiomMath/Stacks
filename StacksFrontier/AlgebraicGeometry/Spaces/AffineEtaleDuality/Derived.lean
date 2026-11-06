module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.LocalComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Naturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteDerivedInternalHom
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import Mathlib.CategoryTheory.Localization.Prod

/-!
# Stacks 0E50: `ε^*` of `R Hom_A` is `R SheafHom` on the small étale site of an affine scheme

Let `A` be a Noetherian ring, `X = Spec A`, `𝒪_étale` the structure sheaf of the small étale site
of `X` and `ε : (X_étale, 𝒪_étale) ⟶ (X, 𝒪_X)` the comparison morphism, whose pullback is the
associated-module functor `AlgebraicGeometry.SmallEtale.associatedModule`. This file constructs
the canonical comparison map

`ε^* (R Hom_A(K, L))~ ⟶ R SheafHom_{𝒪_étale}(ε^* K̃, ε^* L̃)`

as a natural transformation of functors `D(A)ᵒᵖ × D(A) ⥤ D(𝒪_étale)` and proves that it is an
isomorphism when `K ∈ D_Coh(A)` and `L` has finite injective dimension (Stacks 0E50).

`R Hom_A` is `StacksDraft.DerivedHom.derivedHomAdjunction.hom`; `R SheafHom` is
`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor`. The latter lands in sheaves of modules
with sections one universe up, because the objects of the small étale site live there; the source
is lifted to the same universe by the exact functor `Stacks.SheafOfModules.moduleULift`.

## Construction

The comparison descends, along the localization `D(A)ᵒᵖ × D(A)` of pairs of complexes, the
chain-level map `AlgebraicGeometry.AffineEtaleDuality.chainComparison`: for complexes `P` and `M`
it is the morphism `(ε^* Hom^•_A(P, R M)~)^lift ⟶ SheafHom^•(ε^* P̃, R(ε^* (R M)~))` sending a
cochain `d` to `ε^* d̃` followed by the resolution, `R` being the chosen K-injective resolutions,
composed with the canonical identifications of both sides with the derived functors.

## Proof

Represent `L` by a bounded complex `I` of injectives. The chain-level map at `(P, I)` is compared
with the one at `(P, R I)` by naturality, and the former is a quasi-isomorphism by
`AlgebraicGeometry.AffineEtaleDuality.quasiIso_compMap`: on sections over an affine `V = Spec B'`
it is flat base change `B' ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, B' ⊗_A I)`, a quasi-isomorphism for `P`
with finite cohomology over the Noetherian ring `A`, followed by a quasi-isomorphism between
K-injective complexes (`B' ⊗_A I` is a bounded complex of injectives by Stacks 0E4F).

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.comparison`: the canonical comparison map.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.isIso_comparison_app`: **Stacks 0E50**.

## References

* [Stacks Project, Tag 0E50](https://stacks.math.columbia.edu/tag/0E50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe w w' u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The universe lift `Up A B hX` preserves finite limits. -/
scoped instance up_preservesFiniteLimits : PreservesFiniteLimits (Up A B hX) :=
  Stacks.SheafOfModules.preservesFiniteLimits_moduleULift

/-- The universe lift `Up A B hX` preserves finite colimits. -/
scoped instance up_preservesFiniteColimits : PreservesFiniteColimits (Up A B hX) :=
  Stacks.SheafOfModules.preservesFiniteColimits_moduleULift _

set_option synthInstance.maxHeartbeats 400000 in
/-- The universe lift `Up A B hX` is additive. -/
scoped instance up_additive : (Up A B hX).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `M ↦ M̃` from `A`-modules to `𝒪_{Spec A}`-modules preserves finite limits. -/
scoped instance tilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor A) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits A

/-- The functor `M ↦ M̃` from `A`-modules to `𝒪_{Spec A}`-modules preserves finite colimits. -/
scoped instance tilde_preservesFiniteColimits : PreservesFiniteColimits (tilde.functor A) :=
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor A

/-- The functor `M ↦ M̃` from `A`-modules to `𝒪_{Spec A}`-modules is additive. -/
scoped instance tilde_additive : (tilde.functor A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `ε^*`, the associated module on the small étale site of `Spec A`. -/
abbrev epsStar : (Spec A).Modules ⥤ Mod A B hX := SmallEtale.associatedModule B (Spec A) hX

/-- `ε^*` preserves finite limits. -/
instance epsStar_preservesFiniteLimits : PreservesFiniteLimits (epsStar A B hX) :=
  SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf B (Spec A) hX

/-- `ε^*` preserves finite colimits. -/
instance epsStar_preservesFiniteColimits : PreservesFiniteColimits (epsStar A B hX) := by
  have : PreservesColimitsOfSize.{0, 0} (SmallEtale.associatedModule B (Spec A) hX) :=
    (SmallEtale.associatedModuleAdjunction B (Spec A) hX).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits (SmallEtale.associatedModule B (Spec A) hX)

/-- `ε^*` is additive. -/
instance epsStar_additive : (epsStar A B hX).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The chain-level comparison as a natural transformation -/

/-- The chosen K-injective resolution of complexes of `A`-modules. -/
abbrev RA : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} A)

/-- The chosen K-injective resolution of complexes of `𝒪_étale`-modules. -/
abbrev RE : CochainComplex (Mod A B hX) ℤ ⥤ CochainComplex (Mod A B hX) ℤ :=
  Stacks.Injectives.kInjectiveResolutionFunctor (Mod A B hX)

/-- `ε^*T` on complexes. -/
abbrev EC : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (Mod A B hX) ℤ :=
  (epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The source of the chain-level comparison: `(P, M) ↦ (ε^* Hom^•_A(P, R M)~)^lift`. -/
abbrev chainSource :
    (CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ × CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (O A B hX)) ℤ :=
  (𝟭 _).prod (RA A) ⋙ StacksDraft.DerivedHom.Model.homComplexFunctor A ⋙ EC A B hX ⋙
    (Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The target of the chain-level comparison:
`(P, M) ↦ SheafHom^•(ε^* P̃, R (ε^* (R M)~))`. -/
abbrev chainTarget :
    (CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ × CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (O A B hX)) ℤ :=
  (EC A B hX).op.prod (RA A ⋙ EC A B hX ⋙ RE A B hX) ⋙
    Functor.uncurry.obj (RingedSite.Raised.mixedSheafHomComplexBifunctor (Xs A B hX))

/-- **The chain-level comparison of Stacks 0E50, natural in both complexes.** -/
def chainComparison : chainSource A B hX ⟶ chainTarget A B hX where
  app X := compMap (P := X.1.unop) (I := (RA A).obj X.2)
    ((Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).app
      ((EC A B hX).obj ((RA A).obj X.2)))
  naturality X Y f := by
    have h := compMap_naturality
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).app
        ((EC A B hX).obj ((RA A).obj X.2)))
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).app
        ((EC A B hX).obj ((RA A).obj Y.2)))
      f.1.unop ((RA A).map f.2) ((RE A B hX).map ((EC A B hX).map ((RA A).map f.2)))
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).naturality
        ((EC A B hX).map ((RA A).map f.2)))
    refine h.trans ?_
    change _ = _ ≫ RingedSite.homMap (Xs A B hX) ((EC A B hX).map f.1.unop) (𝟙 _) ≫
      RingedSite.homMap (Xs A B hX) (𝟙 _) ((RE A B hX).map ((EC A B hX).map ((RA A).map f.2)))
    rw [RingedSite.homMap_comp, Category.id_comp, Category.id_comp]

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (Spec A).Modules]
  [HasDerivedCategory.{u + 1} (Mod A B hX)]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (O A B hX))]

/-- `M ↦ ε^* M̃` on derived categories. -/
abbrev epsTD : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (Mod A B hX) :=
  (tilde.functor A).mapDerivedCategory ⋙ (epsStar A B hX).mapDerivedCategory

/-- The source of the comparison: `(K, L) ↦ (ε^* (R Hom_A(K, L))~)^lift`. -/
abbrev sourceFunctor :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (O A B hX)) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom ⋙ epsTD A B hX ⋙
    (Up A B hX).mapDerivedCategory

/-- The target of the comparison: `(K, L) ↦ R SheafHom(ε^* K̃, ε^* L̃)`. -/
abbrev targetFunctor :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (O A B hX)) :=
  (epsTD A B hX).op.prod (epsTD A B hX) ⋙
    Functor.uncurry.obj (SmallEtale.derivedSheafHomBifunctor B (Spec A) hX)

/-! ### The comparison on derived categories -/

/-- The inclusion `M ⟶ R M` of a complex of `A`-modules into its chosen K-injective resolution
becomes an isomorphism in the derived category, naturally in `M`. -/
instance isIso_whiskerRight_inclusion_Q :
    IsIso (Functor.whiskerRight (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A))
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)) := by
  have : ∀ M, IsIso ((Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A))
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _)).app M) := fun M =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- The map `ε^* M̃ ⟶ ε^* (R M)~` induced by the chosen K-injective resolution of a complex `M`
of `A`-modules becomes an isomorphism in the derived category, naturally in `M`. -/
instance isIso_whiskerRight_EC_inclusion_Q :
    IsIso (Functor.whiskerRight (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)) (EC A B hX))
      (DerivedCategory.Q : CochainComplex (Mod A B hX) ℤ ⥤ _)) := by
  have : ∀ M, IsIso ((Functor.whiskerRight (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)) (EC A B hX))
      (DerivedCategory.Q : CochainComplex (Mod A B hX) ℤ ⥤ _)).app M) := fun M =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (inferInstanceAs (QuasiIso ((EC A B hX).map
        ((Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app M))))
  exact NatIso.isIso_of_isIso_app _

/-- `Q(M) ≅ Q(R M)` for the chosen K-injective resolution of complexes of `A`-modules. -/
abbrev qResA : (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _) ≅
    RA A ⋙ DerivedCategory.Q :=
  asIso (Functor.whiskerRight (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A))
    DerivedCategory.Q)

/-- `Q(ε^* M̃) ≅ Q(ε^* (R M)~)`. -/
abbrev qResE : EC A B hX ⋙ (DerivedCategory.Q : CochainComplex (Mod A B hX) ℤ ⥤ _) ≅
    RA A ⋙ EC A B hX ⋙ DerivedCategory.Q :=
  asIso (Functor.whiskerRight (Functor.whiskerRight
    (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)) (EC A B hX))
    DerivedCategory.Q)

/-- `ε^*T` commutes with localization. -/
def epsTDFactors : DerivedCategory.Q ⋙ epsTD A B hX ≅ EC A B hX ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (tilde.functor A).mapDerivedCategoryFactors
      (epsStar A B hX).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft ((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ))
      (epsStar A B hX).mapDerivedCategoryFactors

/-- `(ε^*T)^lift` commutes with localization. -/
def upEpsTDFactors :
    DerivedCategory.Q ⋙ epsTD A B hX ⋙ (Up A B hX).mapDerivedCategory ≅
      (EC A B hX ⋙ (Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.isoWhiskerRight (epsTDFactors A B hX) (Up A B hX).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (EC A B hX) (Up A B hX).mapDerivedCategoryFactors

/-- The localization functor of pairs of complexes. -/
abbrev LQ : (CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ × CochainComplex (ModuleCat.{u} A) ℤ ⥤
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ _).op.prod DerivedCategory.Q

/-- The source of the comparison, computed on complexes. -/
def sourceIso : LQ A ⋙ sourceFunctor A B hX ≅ chainSource A B hX ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (NatIso.prod (Iso.refl _) (qResA A))
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom ⋙ epsTD A B hX ⋙
        (Up A B hX).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod ((StacksDraft.DerivedHom.Model.KInjectiveComplexes A).lift
        (RA A) (fun _ => inferInstance)))
      (Functor.isoWhiskerRight
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homComparison
        (epsTD A B hX ⋙ (Up A B hX).mapDerivedCategory)) ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod (RA A) ⋙ StacksDraft.DerivedHom.Model.homComplexFunctor A)
      (upEpsTDFactors A B hX)

/-- The target of the comparison on complexes, read through the model of the derived internal
Hom. -/
def targetModelIso : chainTarget A B hX ⋙ DerivedCategory.Q ≅
    (EC A B hX).op.prod (RA A ⋙ EC A B hX) ⋙
      Functor.uncurry.obj (RingedSite.Raised.mixedDerivedSheafHomModel (Xs A B hX)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact Functor.map_comp _ _ _)

/-- Reassociation of the derived internal Hom precomposed with localization. -/
def targetBifunctorIso : (EC A B hX).op.prod (RA A ⋙ EC A B hX) ⋙
      Functor.uncurry.obj ((((Functor.whiskeringLeft₂ _).obj DerivedCategory.Q.op).obj
        DerivedCategory.Q).obj (RingedSite.Raised.mixedDerivedSheafHomBifunctor (Xs A B hX))) ≅
    (EC A B hX ⋙ DerivedCategory.Q).op.prod (RA A ⋙ EC A B hX ⋙ DerivedCategory.Q) ⋙
      Functor.uncurry.obj (SmallEtale.derivedSheafHomBifunctor B (Spec A) hX) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The target of the comparison, computed on complexes. -/
def targetIso : chainTarget A B hX ⋙ DerivedCategory.Q ≅ LQ A ⋙ targetFunctor A B hX :=
  targetModelIso A B hX ≪≫
  (Functor.isoWhiskerLeft ((EC A B hX).op.prod (RA A ⋙ EC A B hX))
      (Functor.uncurry.mapIso
        (RingedSite.Raised.mixedDerivedSheafHomNatIso (Xs A B hX)))).symm ≪≫
    targetBifunctorIso A B hX ≪≫
    Functor.isoWhiskerRight (NatIso.prod (Iso.refl _) (qResE A B hX).symm)
      (Functor.uncurry.obj (SmallEtale.derivedSheafHomBifunctor B (Spec A) hX)) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (NatIso.op (epsTDFactors A B hX)) (epsTDFactors A B hX).symm)
      (Functor.uncurry.obj (SmallEtale.derivedSheafHomBifunctor B (Spec A) hX))

/-- **The canonical comparison of Stacks 0E50** on pairs of complexes. -/
def comparisonOnComplexes : LQ A ⋙ sourceFunctor A B hX ⟶ LQ A ⋙ targetFunctor A B hX :=
  (sourceIso A B hX).hom ≫ Functor.whiskerRight (chainComparison A B hX) DerivedCategory.Q ≫
    (targetIso A B hX).hom

/-- The target of the comparison is `R SheafHom(ε^* K̃, ε^* L̃)`. -/
lemma targetFunctor_obj (K L : DerivedCategory (ModuleCat.{u} A)) :
    (targetFunctor A B hX).obj (op K, L) =
      SmallEtale.derivedSheafHom B (Spec A) hX ((epsTD A B hX).obj K) ((epsTD A B hX).obj L) :=
  rfl

/-- The source of the comparison is `(ε^* (R Hom_A(K, L))~)^lift`. -/
lemma sourceFunctor_obj (K L : DerivedCategory (ModuleCat.{u} A)) :
    (sourceFunctor A B hX).obj (op K, L) =
      (Up A B hX).mapDerivedCategory.obj ((epsStar A B hX).mapDerivedCategory.obj
        ((tilde.functor A).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (op K, L)))) :=
  rfl

/-- The quasi-isomorphisms of pairs of complexes. -/
abbrev WQ : MorphismProperty
    ((CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ × CochainComplex (ModuleCat.{u} A) ℤ) :=
  (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).op.prod
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

/-- **The canonical comparison map of Stacks 0E50**
`ε^* (R Hom_A(K, L))~ ⟶ R SheafHom_{𝒪_étale}(ε^* K̃, ε^* L̃)`, natural in `K` and `L`. Its
value on complexes `P` and `M` is the class of the morphism of complexes sending a cochain
`d : P ⟶ (R M)[n]` to the cochain `ε^* d̃` followed by the chosen K-injective resolution of
`ε^* (R M)~`, `R` being the chosen K-injective resolution. -/
def comparison : sourceFunctor A B hX ⟶ targetFunctor A B hX :=
  Localization.liftNatTrans (LQ A) (WQ A) (LQ A ⋙ sourceFunctor A B hX)
    (LQ A ⋙ targetFunctor A B hX) (sourceFunctor A B hX) (targetFunctor A B hX)
    (comparisonOnComplexes A B hX)

/-- On the localization of a pair of complexes, `comparison` is `comparisonOnComplexes`. -/
lemma comparison_app_LQ (X : (CochainComplex (ModuleCat.{u} A) ℤ)ᵒᵖ ×
    CochainComplex (ModuleCat.{u} A) ℤ) :
    (comparison A B hX).app ((LQ A).obj X) = (comparisonOnComplexes A B hX).app X := by
  rw [comparison, Localization.liftNatTrans_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

omit [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w'} (Spec A).Modules]
  [HasDerivedCategory.{u + 1} (Mod A B hX)]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (O A B hX))] in
/-- **The chain-level comparison is a quasi-isomorphism** at a complex `P` with finite cohomology
and a bounded complex `I` of injective modules over a Noetherian ring. -/
theorem quasiIso_chainComparison_app [IsNoetherianRing A]
    (P I : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [I.IsStrictlyGE a] [I.IsStrictlyLE b]
    [∀ k, Injective (I.X k)] (hP : ∀ i, Module.Finite A (P.homology i)) :
    QuasiIso ((chainComparison A B hX).app (op P, I)) := by
  let ι₀ := (Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).app ((EC A B hX).obj I)
  let ι₁ := (Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).app
    ((EC A B hX).obj ((RA A).obj I))
  let j := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} A)).app I
  have h₀ : QuasiIso (compMap (P := P) ι₀) := quasiIso_compMap P I ι₀ a b hP
  have hn := compMap_naturality ι₀ ι₁ (𝟙 P) j ((RE A B hX).map ((EC A B hX).map j))
    ((Stacks.Injectives.kInjectiveResolutionInclusion (Mod A B hX)).naturality _)
  have : CochainComplex.IsKInjective ((𝟭 (CochainComplex (ModuleCat.{u} A) ℤ)).obj I) :=
    CochainComplex.isKInjective_of_injective I a
  have : QuasiIso (dcMap (𝟙 P) j) := quasiIso_dcMap _ _
  have : QuasiIso ((RE A B hX).map ((EC A B hX).map j)) :=
    RingedSite.Raised.quasiIso_kInjectiveResolutionFunctor_map _ _
  have : QuasiIso (RingedSite.homMap (Xs A B hX) ((EC A B hX).map (𝟙 P))
      ((RE A B hX).map ((EC A B hX).map j))) :=
    RingedSite.homMap_quasiIso _ _ _
  have hc : QuasiIso (compMap (P := P) ι₀ ≫ RingedSite.homMap (Xs A B hX)
      ((EC A B hX).map (𝟙 P)) ((RE A B hX).map ((EC A B hX).map j))) :=
    inferInstance
  rw [← hn] at hc
  exact quasiIso_of_comp_left (((Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((EC A B hX).map (dcMap (𝟙 P) j))) (compMap (P := P) ι₁)

/-- **Stacks 0E50.** Let `A` be a Noetherian ring and `X = Spec A`, let `𝒪_étale` be the
structure sheaf of the small étale site of `X`, and let `ε : (X_étale, 𝒪_étale) ⟶ (X, 𝒪_X)` be
the comparison morphism. For `K, L ∈ D(A)` with `K ∈ D_Coh(A)` and `L` of finite injective
dimension, the canonical map
`ε^* (R Hom_A(K, L))~ ⟶ R SheafHom_{𝒪_étale}(ε^* K̃, ε^* L̃)` is an isomorphism in `D(𝒪_étale)`.

The source is lifted to the module universe of the derived internal Hom, which on the small étale
site lands one universe up (`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor`). -/
@[stacks 0E50]
theorem isIso_comparison_app [IsNoetherianRing A] (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ n : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L) :
    IsIso ((comparison A B hX).app (op K, L)) := by
  obtain ⟨a, b, I, _, _, hI, ⟨eL⟩⟩ := hL
  have : ∀ k, Injective (I.X k) := hI
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hP : ∀ i, Module.Finite A (P.homology i) := fun i =>
    Module.Finite.equiv ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eK.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app P).toLinearEquiv
  have h₀ : IsIso ((comparison A B hX).app ((LQ A).obj (op P, I))) := by
    rw [comparison_app_LQ]
    have := quasiIso_chainComparison_app A B hX P I a b hP
    have : IsIso (DerivedCategory.Q.map ((chainComparison A B hX).app (op P, I))) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this
    change IsIso ((sourceIso A B hX).hom.app _ ≫
      DerivedCategory.Q.map ((chainComparison A B hX).app (op P, I)) ≫
        (targetIso A B hX).hom.app _)
    infer_instance
  let e : (LQ A).obj (op P, I) ≅ (op K, L) := Iso.prod eK.symm.op eL.symm
  have h : (comparison A B hX).app (op K, L) = (sourceFunctor A B hX).map e.inv ≫
      (comparison A B hX).app ((LQ A).obj (op P, I)) ≫ (targetFunctor A B hX).map e.hom := by
    have hnat := (comparison A B hX).naturality e.hom
    rw [← hnat, ← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [h]
  infer_instance

end AlgebraicGeometry.AffineEtaleDuality

end
