module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback

/-!
# The adjunction `Lf^* ⊣ Rf_*` on `D_QCoh` of algebraic spaces

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces. Both `Lf^*`
(Stacks 08F4) and `Rf_*` (Stacks 08FA) preserve the quasi-coherent derived categories, so the
derived adjunction `Lf^* ⊣ Rf_*` restricts to `D_QCoh`. If the inclusions `D_QCoh → D` have right
adjoints `DQ_X`, `DQ_Y`, then `Rf_* ∘ DQ_X = DQ_Y ∘ Rf_*` (Stacks 0CR5).

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedModuleAdjunction`: `Lf^* ⊣ Rf_*` on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPushforwardCompCoheratorIso`: Stacks 0CR5.
* `AlgebraicGeometry.Space.ι_map_quasicoherentDerivedModuleAdjunction_unit_app` and the
  `counit_app`, `homEquiv` analogues: the unit, counit and adjunction bijection on `D_QCoh` are
  those of the derived adjunction.

## References

* [Stacks Project, Tag 0CR5](https://stacks.math.columbia.edu/tag/0CR5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The derived adjunction `Lf^* ⊣ Rf_*` restricted to the quasi-coherent derived categories**,
for a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces. -/
def quasicoherentDerivedModuleAdjunction (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    quasicoherentDerivedModulePullback f ⊣ quasicoherentDerivedPushforward B S hS f hfqc hfqs :=
  (smallEtaleDerivedModuleAdjunction B S hS f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (quasicoherentDerivedModulePullbackCompιIso f).symm
    (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs).symm

/-- The unit of `Lf^* ⊣ Rf_*` on `D_QCoh` is the unit of the derived adjunction. -/
theorem ι_map_quasicoherentDerivedModuleAdjunction_unit_app (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    ((quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).unit.app K).hom =
      (smallEtaleDerivedModuleAdjunction B S hS f).unit.app K.obj := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y))
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X))
    (quasicoherentDerivedModulePullbackCompιIso f).symm
    (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs).symm K).trans ?_
  refine (congrArg (_ ≫ ·) (Category.comp_id _)).trans ?_
  refine (congrArg (_ ≫ ·) ((derivedModulePushforward B S hS f).map_id _)).trans ?_
  exact Category.comp_id _

/-- The counit of `Lf^* ⊣ Rf_*` on `D_QCoh` is the counit of the derived adjunction. -/
theorem ι_map_quasicoherentDerivedModuleAdjunction_counit_app (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    ((quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).counit.app E).hom =
      (smallEtaleDerivedModuleAdjunction B S hS f).counit.app E.obj := by
  refine (Adjunction.map_restrictFullyFaithful_counit_app
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y))
    (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X))
    (quasicoherentDerivedModulePullbackCompιIso f).symm
    (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs).symm E).trans ?_
  refine (Category.id_comp (obj := DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) _).trans ?_
  refine (congrArg (· ≫ _) ((smallEtaleDerivedModulePullback B S hS f).map_id _)).trans ?_
  exact Category.id_comp _

/-- The adjunction bijection of `Lf^* ⊣ Rf_*` on `D_QCoh` is that of the derived adjunction. -/
theorem ι_map_quasicoherentDerivedModuleAdjunction_homEquiv (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (g : (quasicoherentDerivedModulePullback f).obj K ⟶ E) :
    ((quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).homEquiv K E g).hom =
      (smallEtaleDerivedModuleAdjunction B S hS f).homEquiv K.obj E.obj g.hom := by
  refine ((QcohDerived B S hS Y).ι.congr_map
    (Adjunction.homEquiv_unit _ K E g)).trans ?_
  refine ((QcohDerived B S hS Y).ι.map_comp _ _).trans ?_
  refine (congrArg (· ≫ _) (ι_map_quasicoherentDerivedModuleAdjunction_unit_app B S hS f hfqc hfqs
    K)).trans ?_
  exact (Adjunction.homEquiv_unit _ K.obj E.obj g.hom).symm

/-- **Stacks 0CR5.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic
spaces. If the inclusions `D_QCoh(𝒪_X) → D(𝒪_X)` and `D_QCoh(𝒪_Y) → D(𝒪_Y)` have right adjoints
`DQ_X` and `DQ_Y`, then `Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*`: both are right adjoint to
`Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)`. -/
def quasicoherentDerivedPushforwardCompCoheratorIso (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    {DQX : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
    {DQY : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2}
    (adjX : (QcohDerived B S hS X).ι ⊣ DQX) (adjY : (QcohDerived B S hS Y).ι ⊣ DQY) :
    DQX ⋙ quasicoherentDerivedPushforward B S hS f hfqc hfqs ≅
      derivedModulePushforward B S hS f ⋙ DQY :=
  ((quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).comp adjX).ofNatIsoLeft
      (quasicoherentDerivedModulePullbackCompιIso f) |>.rightAdjointUniq
    (adjY.comp (smallEtaleDerivedModuleAdjunction B S hS f))

end AlgebraicGeometry.Space

end
