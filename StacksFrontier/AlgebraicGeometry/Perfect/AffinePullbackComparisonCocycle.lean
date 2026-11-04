module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes

/-!
# The composition cocycle of the affine comparison square

For ring maps `g : R ⟶ S` and `h : S ⟶ T`, the affine comparison square
`AlgebraicGeometry.StandardModel.affinePullbackComparison` of Stacks 08DW is compatible with
composition: around `Spec T ⟶ Spec S ⟶ Spec R`, the comparison for `g` pulled back along
`Spec h`, followed by the comparison for `h` and the composition isomorphism of derived
extension of scalars, is the composition isomorphism of Stacks 0D5S followed by the comparison
for `g ≫ h`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.StandardModel

section Pullback

variable {X Y Z : RingedSpace.{u, u}}

/-- The comparison on complexes of `derivedPullbackComplexComparison` is
`derivedPullbackComparisonOnComplex`. -/
theorem derivedPullbackComplexComparison_app_eq_onComplex (f : X ⟶ Y)
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullbackComplexComparison f).app N = derivedPullbackComparisonOnComplex f N := by
  simp [derivedPullbackComplexComparison, derivedPullbackComparisonOnComplex]

/-- **The composition isomorphism of Stacks 0D5S along a factorisation, read on complexes.** -/
theorem factorIso_hom_app_comp_complexComparison (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hk : f ≫ g = k) (N : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (Stacks.DerivedPullback.factorIso f g k hk).hom.app (DerivedCategory.Q.obj N) ≫
        (derivedPullbackComplexComparison k).app N =
      (derivedPullback f).map ((derivedPullbackComplexComparison g).app N) ≫
        (derivedPullbackComplexComparison f).app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f g)
            (ComplexShape.up ℤ)).hom.app N ≫ eqToHom (by rw [hk])) := by
  subst hk
  simp only [derivedPullbackComplexComparison_app_eq_onComplex, eqToHom_refl, Category.comp_id]
  exact derivedPullbackComparisonOnComplex_comp f g N

end Pullback

variable {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)

/-- The degreewise pullback-composition isomorphism of ringed spaces at spectra is the
pullback-composition isomorphism of schemes. -/
theorem modulePullbackComp_spec :
    Stacks.DerivedPullback.Composition.modulePullbackComp (Spec.map h).toLRSHom.toShHom
        (Spec.map g).toLRSHom.toShHom =
      Scheme.Modules.pullbackComp (Spec.map h) (Spec.map g) := rfl

/-- The composition isomorphism of Stacks 0D5S along `Spec T ⟶ Spec S ⟶ Spec R`. -/
def specDerivedPullbackCompIso :
    specDerivedPullback g ⋙ specDerivedPullback h ≅ specDerivedPullback (g ≫ h) :=
  Stacks.DerivedPullback.schemeFactorIso (Spec.map h) (Spec.map g) (Spec.map (g ≫ h))
    (Spec.map_comp g h).symm

/-- The comparison `L~ ∘ L(S ⊗ -) ⟶ (S ⊗ -)~` at a complex, written out. -/
theorem extendScalarsTildeComparison_app (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsTildeComparison R S g).app P =
      (tilde.functor S).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} g.hom).comparison.app P) ≫
        (tilde.functor S).mapDerivedCategoryFactors.hom.app
          ((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj P) := by
  simp only [extendScalarsTildeComparison, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]
  exact congrArg _ (Category.id_comp _)

/-- **The affine comparison square at a complex**, with every comparison written out: the
comparison for `g` followed by the two derived-functor comparisons of derived extension of
scalars and derived sheafification is derived pullback of the comparison for derived
sheafification, the comparison of derived pullback on complexes, and Stacks 01I9 on complexes. -/
theorem affinePullbackComparison_fac' (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (affinePullbackComparison R S g).hom.app (DerivedCategory.Q.obj P) ≫
        (tilde.functor S).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} g.hom).comparison.app P) ≫
        (tilde.functor S).mapDerivedCategoryFactors.hom.app
          ((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj P) =
      (specDerivedPullback g).map ((tilde.functor R).mapDerivedCategoryFactors.hom.app P) ≫
        (derivedPullbackComplexComparison (Spec.map g).toLRSHom.toShHom).app
          ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj P) ≫
        DerivedCategory.Q.map ((tildePullbackComplexIso R S g).hom.app P) := by
  have := affinePullbackComparison_fac R S g P
  rw [extendScalarsTildeComparison_app] at this
  simp only [tildeDerivedPullbackComparison, tildeDerivedPullbackFactor,
    tildePullbackComplexCompQIso, NatTrans.comp_app, Iso.trans_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Iso.symm_hom] at this
  rw [Category.assoc] at this
  exact this

/-- **The composition isomorphism of derived extension of scalars at a complex**, written out. -/
theorem derivedExtensionScalarsComp_hom_app_comp_comparison
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (PseudoCoherence.derivedExtensionScalarsComp.{u, u} g.hom h.hom).hom.app
          (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).comparison.app P =
      (totalDerivedExtensionScalars.{u, u, u} h.hom).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} g.hom).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} h.hom).comparison.app
          ((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp g.hom h.hom) (ComplexShape.up ℤ)).inv.app P) := by
  rw [PseudoCoherence.derivedExtensionScalarsComp_hom]
  exact PseudoCoherence.derivedExtensionScalarsCompHom_fac.{u, u} g.hom h.hom P

/-- The degree `n` component of Stacks 01I9 on complexes is Stacks 01I9 at the degree `n`
module. -/
theorem tildePullbackComplexIso_hom_app_f (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((tildePullbackComplexIso R S g).hom.app P).f n = (pullbackTildeIso R S g).hom.app (P.X n) := by
  simp only [tildePullbackComplexIso, HomologicalComplex.comp_f, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **Stacks 01I9 is compatible with composition**, at a module, in the form used on
complexes. -/
theorem pullbackTildeIso_comp_app (N : ModuleCat.{u} R) :
    (pullbackSpecMapCompIso R S T g h).inv.app ((tilde.functor R).obj N) ≫
        (pullbackTildeIso R T (g ≫ h)).hom.app N =
      (Scheme.Modules.pullback (Spec.map h)).map ((pullbackTildeIso R S g).hom.app N) ≫
        (pullbackTildeIso S T h).hom.app ((ModuleCat.extendScalars g.hom).obj N) ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp g.hom h.hom).inv.app N) := by
  rw [pullbackTildeIso_comp]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Iso.symm_hom, Functor.comp_obj, Iso.inv_hom_id_app_assoc]

section Generic

variable {𝒜 ℬ 𝒞 𝒟 𝒜' 𝒜'' : Type*} {_ : Category 𝒜} {_ : Category ℬ} {_ : Category 𝒞}
  {_ : Category 𝒟} {_ : Category 𝒜'} {_ : Category 𝒜''} {_ : Preadditive 𝒜} {_ : Preadditive ℬ}
  {_ : Preadditive 𝒞} {_ : Preadditive 𝒟} {_ : Preadditive 𝒜'} {_ : Preadditive 𝒜''}
  (t : 𝒜 ⥤ ℬ) (t' : 𝒜' ⥤ 𝒞) (t'' : 𝒜'' ⥤ 𝒟) (p₁ : ℬ ⥤ 𝒞) (p₂ : 𝒞 ⥤ 𝒟) (p₁₂ p : ℬ ⥤ 𝒟)
  (e₁ : 𝒜 ⥤ 𝒜') (e₂ : 𝒜' ⥤ 𝒜'') (e : 𝒜 ⥤ 𝒜'')
  [t.Additive] [t'.Additive] [t''.Additive] [p₁.Additive] [p₂.Additive] [p₁₂.Additive]
  [p.Additive] [e₁.Additive] [e₂.Additive] [e.Additive]

/-- **A cocycle of comparison isomorphisms, read on complexes.** If a comparison
`τ : t ⋙ p ≅ e ⋙ t''` is the composite of `τ₁ : t ⋙ p₁ ≅ e₁ ⋙ t'` and `τ₂ : t' ⋙ p₂ ≅ e₂ ⋙ t''`
through `ν : p ≅ p₁ ⋙ p₂` and `ε : e ≅ e₁ ⋙ e₂`, where `ν` is an equality of functors followed by
the inverse of `μ : p₁ ⋙ p₂ ≅ p₁₂`, then the same holds degreewise on complexes. -/
theorem mapHomologicalComplex_comparison_cocycle (hp : p = p₁₂) (μ : p₁ ⋙ p₂ ≅ p₁₂)
    (ν : p ≅ p₁ ⋙ p₂) (hν : ν = eqToIso hp ≪≫ μ.symm)
    (τ₁ : t ⋙ p₁ ≅ e₁ ⋙ t') (τ₂ : t' ⋙ p₂ ≅ e₂ ⋙ t'') (τ : t ⋙ p ≅ e ⋙ t'')
    (ε : e ≅ e₁ ⋙ e₂)
    (hτ : τ = Functor.isoWhiskerLeft t ν ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight τ₁ p₂ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e₁ τ₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ε.symm t'')
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex 𝒜 c)
    (E : (p₁₂.mapHomologicalComplex c).obj ((t.mapHomologicalComplex c).obj K) =
      (p.mapHomologicalComplex c).obj ((t.mapHomologicalComplex c).obj K)) :
    (Functor.mapHomologicalComplexCompIso μ c).hom.app ((t.mapHomologicalComplex c).obj K) ≫
        eqToHom E ≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ p)) c) ≪≫
          NatIso.mapHomologicalComplex τ c ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (e ⋙ t'')) c).symm).hom.app K =
      (p₂.mapHomologicalComplex c).map
          (((Functor.mapHomologicalComplexCompIso (Iso.refl (t ⋙ p₁)) c) ≪≫
            NatIso.mapHomologicalComplex τ₁ c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (e₁ ⋙ t')) c).symm).hom.app K) ≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (t' ⋙ p₂)) c) ≪≫
            NatIso.mapHomologicalComplex τ₂ c ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (e₂ ⋙ t'')) c).symm).hom.app
          ((e₁.mapHomologicalComplex c).obj K) ≫
        (t''.mapHomologicalComplex c).map
          ((NatIso.mapHomologicalComplex ε c).inv.app K) := by
  subst hp hν hτ
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  simp

end Generic

/-- **Stacks 01I9 on complexes is compatible with composition**, against the degreewise
pullback-composition isomorphism through which the composition isomorphism of Stacks 0D5S acts
on complexes. -/
theorem tildePullbackComplexIso_comp (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (E : ((Scheme.Modules.pullback (Spec.map h ≫ Spec.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj P) =
        ((Scheme.Modules.pullback (Spec.map (g ≫ h))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj P)) :
    (Functor.mapHomologicalComplexCompIso
          (Scheme.Modules.pullbackComp (Spec.map h) (Spec.map g)) (ComplexShape.up ℤ)).hom.app
          ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj P) ≫
        eqToHom E ≫ (tildePullbackComplexIso R T (g ≫ h)).hom.app P =
      ((Scheme.Modules.pullback (Spec.map h)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((tildePullbackComplexIso R S g).hom.app P) ≫
        (tildePullbackComplexIso S T h).hom.app
          ((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
            (ComplexShape.up ℤ) |>.obj P) ≫
        ((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex
            (ModuleCat.extendScalarsComp g.hom h.hom) (ComplexShape.up ℤ)).inv.app P) := by
  have key := mapHomologicalComplex_comparison_cocycle (tilde.functor R) (tilde.functor S)
      (tilde.functor T)
      (Scheme.Modules.pullback (Spec.map g)) (Scheme.Modules.pullback (Spec.map h))
      (Scheme.Modules.pullback (Spec.map h ≫ Spec.map g))
      (Scheme.Modules.pullback (Spec.map (g ≫ h)))
      (ModuleCat.extendScalars.{u, u, u} g.hom) (ModuleCat.extendScalars.{u, u, u} h.hom)
      (ModuleCat.extendScalars.{u, u, u} (g ≫ h).hom)
      (congrArg Scheme.Modules.pullback (Spec.map_comp g h))
      (Scheme.Modules.pullbackComp (Spec.map h) (Spec.map g)) (pullbackSpecMapCompIso R S T g h)
      rfl (pullbackTildeIso R S g) (pullbackTildeIso S T h) (pullbackTildeIso R T (g ≫ h))
      (ModuleCat.extendScalarsComp g.hom h.hom) (pullbackTildeIso_comp R S T g h) P E
  unfold tildePullbackComplexIso
  exact key

/-! ### The cocycle -/

section Cocycle

/-- Derived pullback along a morphism of schemes, with both derived categories spelled in the
scheme form. -/
def dpb {X Y : Scheme.{u}} (f : X ⟶ Y) : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  derivedPullback f.toLRSHom.toShHom

/-- The comparison of derived pullback on complexes, in the scheme spelling. -/
def pcoc {X Y : Scheme.{u}} (f : X ⟶ Y) (N : CochainComplex Y.Modules ℤ) :
    (dpb f).obj (DerivedCategory.Q.obj N) ⟶
      DerivedCategory.Q.obj (((Scheme.Modules.pullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) :=
  pullbackComparisonOnComplex f N

/-- The comparison of derived extension of scalars at a complex, with its target written as the
localisation of the degreewise extension of scalars. -/
def extComparison {R S : CommRingCat.{u}} (g : R ⟶ S) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P) :=
  (totalDerivedExtensionScalars.{u, u, u} g.hom).comparison.app P

/-- The comparison of derived sheafification at a complex. -/
def tildeFactor (R : CommRingCat.{u}) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (tilde.functor R).mapDerivedCategoryFactors.hom.app P

/-- The affine comparison square of Stacks 08DW at an object. -/
def cmp {R S : CommRingCat.{u}} (g : R ⟶ S) (M : DerivedCategory (ModuleCat.{u} R)) :
    (dpb (Spec.map g)).obj ((tilde.functor R).mapDerivedCategory.obj M) ⟶
      (tilde.functor S).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) :=
  (affinePullbackComparison R S g).hom.app M

/-- The composition isomorphism of Stacks 0D5S along `Spec T ⟶ Spec S ⟶ Spec R`, at an
object. -/
def fcomp {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)
    (X : DerivedCategory (Spec R).Modules) :
    (dpb (Spec.map h)).obj ((dpb (Spec.map g)).obj X) ⟶ (dpb (Spec.map (g ≫ h))).obj X :=
  (specDerivedPullbackCompIso g h).hom.app X

/-- The composition isomorphism of derived extension of scalars, at an object. -/
def extComp {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} h.hom).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) ⟶
      (totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).functor.obj M :=
  (PseudoCoherence.derivedExtensionScalarsComp.{u, u} g.hom h.hom).hom.app M

/-- Stacks 01I9 on complexes, at a complex. -/
def tpc {R S : CommRingCat.{u}} (g : R ⟶ S) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P) :=
  (tildePullbackComplexIso R S g).hom.app P

/-- The degreewise composition isomorphism of extension of scalars, at a complex. -/
def escomp {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} h.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P) ⟶
      ((ModuleCat.extendScalars.{u, u, u} (g ≫ h).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp g.hom h.hom)
    (ComplexShape.up ℤ)).inv.app P

/-- The degreewise composition isomorphism of pullbacks along `Spec T ⟶ Spec S ⟶ Spec R`, at a
complex. -/
def pbcomp {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)
    (N : CochainComplex (Spec R).Modules ℤ) :
    ((Scheme.Modules.pullback (Spec.map h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ⟶
      ((Scheme.Modules.pullback (Spec.map (g ≫ h))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        N :=
  (Functor.mapHomologicalComplexCompIso
      (Scheme.Modules.pullbackComp (Spec.map h) (Spec.map g)) (ComplexShape.up ℤ)).hom.app N ≫
    eqToHom (by rw [Spec.map_comp])

variable {R S T : CommRingCat.{u}} (g : R ⟶ S) (h : S ⟶ T)

/-- The comparison of the standard model on complexes is `pcoc`. -/
theorem derivedPullbackComplexComparison_app_eq_pcoc {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : CochainComplex Y.Modules ℤ) :
    (derivedPullbackComplexComparison f.toLRSHom.toShHom).app N = pcoc f N :=
  (derivedPullbackComplexComparison_app_eq_onComplex f.toLRSHom.toShHom N).trans
    (pullbackComparisonOnComplex_eq f N).symm

/-- On a complex `P`, the affine comparison `cmp g` composed with the comparisons of derived
extension of scalars and derived sheafification equals the derived pullback of `tildeFactor R P`
followed by `pcoc` and the image of `tpc g P`. -/
theorem cmp_fac (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cmp g (DerivedCategory.Q.obj P) ≫ (tilde.functor S).mapDerivedCategory.map (extComparison g P) ≫
        tildeFactor S (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) =
      (dpb (Spec.map g)).map (tildeFactor R P) ≫
        pcoc (Spec.map g) (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (tpc g P) :=
  (affinePullbackComparison_fac' g P).trans
    (congrArg (fun x => (dpb (Spec.map g)).map (tildeFactor R P) ≫ x ≫
        DerivedCategory.Q.map (tpc g P))
      (derivedPullbackComplexComparison_app_eq_pcoc (Spec.map g)
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))

/-- On a complex `P`, `extComp g h` followed by `extComparison (g ≫ h) P` equals the composite of
the comparisons for `g` and `h` followed by the image of `escomp g h P`. -/
theorem extComp_fac (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    extComp g h (DerivedCategory.Q.obj P) ≫ extComparison (g ≫ h) P =
      (totalDerivedExtensionScalars.{u, u, u} h.hom).functor.map (extComparison g P) ≫
        extComparison h (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (escomp g h P) :=
  derivedExtensionScalarsComp_hom_app_comp_comparison g h P

/-- **Stacks 0D5S along a factorisation of morphisms of schemes, read on complexes.** -/
theorem schemeFactorIso_hom_app_comp_pcoc {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (f' : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ f' = k) (N : CochainComplex Z.Modules ℤ) :
    (Stacks.DerivedPullback.schemeFactorIso f f' k hk).hom.app (DerivedCategory.Q.obj N) ≫
        pcoc k N =
      (dpb f).map (pcoc f' N) ≫
        pcoc f (((Scheme.Modules.pullback f').mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Scheme.Modules.pullbackComp f f') (ComplexShape.up ℤ)).hom.app N ≫
          eqToHom (by rw [hk])) := by
  subst hk
  simp only [← derivedPullbackComplexComparison_app_eq_pcoc]
  exact factorIso_hom_app_comp_complexComparison f.toLRSHom.toShHom f'.toLRSHom.toShHom
    (f ≫ f').toLRSHom.toShHom rfl N

/-- On a complex `N`, `fcomp g h` followed by `pcoc` for `Spec.map (g ≫ h)` equals the composite
of the comparisons `pcoc` for `Spec.map g` and `Spec.map h` followed by the image of
`pbcomp g h N`. -/
theorem fcomp_fac (N : CochainComplex (Spec R).Modules ℤ) :
    fcomp g h (DerivedCategory.Q.obj N) ≫ pcoc (Spec.map (g ≫ h)) N =
      (dpb (Spec.map h)).map (pcoc (Spec.map g) N) ≫
        pcoc (Spec.map h) (((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Q.map (pbcomp g h N) :=
  schemeFactorIso_hom_app_comp_pcoc (Spec.map h) (Spec.map g)
    (Spec.map (g ≫ h)) (Spec.map_comp g h).symm N

/-- The isomorphisms `tpc` are compatible with composition: `pbcomp g h` followed by `tpc (g ≫ h)`
equals the pullback of `tpc g` followed by `tpc h` and the sheafification of `escomp g h`. -/
theorem tpc_comp (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    pbcomp g h (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        tpc (g ≫ h) P =
      ((Scheme.Modules.pullback (Spec.map h)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (tpc g P) ≫
        tpc h (((ModuleCat.extendScalars.{u, u, u} g.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
        ((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map (escomp g h P) := by
  rw [pbcomp, Category.assoc]
  exact tildePullbackComplexIso_comp g h P _

/-- Naturality of the affine comparison `cmp h` in the derived-category object. -/
theorem cmp_naturality {X Y : DerivedCategory (ModuleCat.{u} S)} (γ : X ⟶ Y) :
    cmp h X ≫ (tilde.functor T).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} h.hom).functor.map γ) =
      (dpb (Spec.map h)).map ((tilde.functor S).mapDerivedCategory.map γ) ≫ cmp h Y :=
  ((affinePullbackComparison S T h).hom.naturality γ).symm

/-- Naturality of the composition isomorphism `fcomp g h` in the derived-category object. -/
theorem fcomp_naturality {X Y : DerivedCategory (Spec R).Modules} (φ : X ⟶ Y) :
    fcomp g h X ≫ (dpb (Spec.map (g ≫ h))).map φ =
      (dpb (Spec.map h)).map ((dpb (Spec.map g)).map φ) ≫ fcomp g h Y :=
  ((specDerivedPullbackCompIso g h).hom.naturality φ).symm

/-- Naturality of `tildeFactor T` in the complex. -/
theorem tildeFactor_naturality {P P' : CochainComplex (ModuleCat.{u} T) ℤ} (ι : P ⟶ P') :
    (tilde.functor T).mapDerivedCategory.map (DerivedCategory.Q.map ι) ≫ tildeFactor T P' =
      tildeFactor T P ≫
        DerivedCategory.Q.map
          (((tilde.functor T).mapHomologicalComplex (ComplexShape.up ℤ)).map ι) :=
  (tilde.functor T).mapDerivedCategoryFactors.hom.naturality ι

/-- Naturality of the comparison `pcoc f` in the complex. -/
theorem pcoc_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) {N N' : CochainComplex Y.Modules ℤ}
    (φ : N ⟶ N') :
    (dpb f).map (DerivedCategory.Q.map φ) ≫ pcoc f N' =
      pcoc f N ≫ DerivedCategory.Q.map
        (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  rw [← derivedPullbackComplexComparison_app_eq_pcoc,
    ← derivedPullbackComplexComparison_app_eq_pcoc]
  exact (derivedPullbackComplexComparison f.toLRSHom.toShHom).naturality φ

/-- **The composition cocycle of the affine comparison square, on a K-flat complex.** -/
theorem cmp_comp_of_kFlat (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    (dpb (Spec.map h)).map (cmp g (DerivedCategory.Q.obj P)) ≫
        cmp h ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj
          (DerivedCategory.Q.obj P)) ≫
        (tilde.functor T).mapDerivedCategory.map (extComp g h (DerivedCategory.Q.obj P)) =
      fcomp g h ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        cmp (g ≫ h) (DerivedCategory.Q.obj P) := by
  have hc : IsIso (extComparison (g ≫ h) P) :=
    (totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).comparison_isIso_of_kFlat P hP
  have hf : IsIso (tildeFactor T
      (((ModuleCat.extendScalars.{u, u, u} (g ≫ h).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) := by
    rw [tildeFactor]; infer_instance
  rw [← cancel_mono ((tilde.functor T).mapDerivedCategory.map (extComparison (g ≫ h) P) ≫
    tildeFactor T (((ModuleCat.extendScalars.{u, u, u} (g ≫ h).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P))]
  simp only [Category.assoc]
  rw [cmp_fac (g ≫ h) P, reassoc_of% fcomp_naturality, reassoc_of% fcomp_fac,
    ← Functor.map_comp, tpc_comp, Functor.map_comp, Functor.map_comp,
    ← Functor.map_comp_assoc, extComp_fac, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, tildeFactor_naturality, reassoc_of% cmp_naturality,
    reassoc_of% cmp_fac h, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [cmp_fac g P, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% pcoc_naturality]

/-- Naturality of the composition isomorphism `extComp g h` in the derived-category object. -/
theorem extComp_naturality {X Y : DerivedCategory (ModuleCat.{u} R)} (γ : X ⟶ Y) :
    extComp g h X ≫ (totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).functor.map γ =
      (totalDerivedExtensionScalars.{u, u, u} h.hom).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.map γ) ≫ extComp g h Y :=
  ((PseudoCoherence.derivedExtensionScalarsComp.{u, u} g.hom h.hom).hom.naturality γ).symm

/-- **The composition cocycle of the affine comparison square of Stacks 08DW.** For ring maps
`g : R ⟶ S` and `h : S ⟶ T` and `M ∈ D(R)`, the comparison for `g` pulled back along `Spec h`,
followed by the comparison for `h` and the composition isomorphism of derived extension of
scalars, is the composition isomorphism of Stacks 0D5S followed by the comparison for
`g ≫ h`. -/
theorem cmp_comp (M : DerivedCategory (ModuleCat.{u} R)) :
    (dpb (Spec.map h)).map (cmp g M) ≫
        cmp h ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) ≫
        (tilde.functor T).mapDerivedCategory.map (extComp g h M) =
      fcomp g h ((tilde.functor R).mapDerivedCategory.obj M) ≫ cmp (g ≫ h) M := by
  obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative M
  have key := cmp_comp_of_kFlat g h P hP
  rw [← cancel_epi ((dpb (Spec.map h)).map ((dpb (Spec.map g)).map
    ((tilde.functor R).mapDerivedCategory.map e.hom)))]
  have hL : (dpb (Spec.map h)).map ((dpb (Spec.map g)).map
        ((tilde.functor R).mapDerivedCategory.map e.hom)) ≫
      (dpb (Spec.map h)).map (cmp g M) ≫
        cmp h ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) ≫
        (tilde.functor T).mapDerivedCategory.map (extComp g h M) =
      ((dpb (Spec.map h)).map (cmp g (DerivedCategory.Q.obj P)) ≫
        cmp h ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj
          (DerivedCategory.Q.obj P)) ≫
        (tilde.functor T).mapDerivedCategory.map (extComp g h (DerivedCategory.Q.obj P))) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).functor.map e.hom) := by
    simp only [Category.assoc]
    rw [← Functor.map_comp, extComp_naturality, Functor.map_comp, reassoc_of% cmp_naturality,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, cmp_naturality]
  have hR : (dpb (Spec.map h)).map ((dpb (Spec.map g)).map
        ((tilde.functor R).mapDerivedCategory.map e.hom)) ≫
      fcomp g h ((tilde.functor R).mapDerivedCategory.obj M) ≫ cmp (g ≫ h) M =
      (fcomp g h ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        cmp (g ≫ h) (DerivedCategory.Q.obj P)) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, u} (g ≫ h).hom).functor.map e.hom) := by
    simp only [Category.assoc]
    rw [cmp_naturality, ← reassoc_of% fcomp_naturality]
  rw [hL, hR, key]

end Cocycle

end AlgebraicGeometry.StandardModel

end
