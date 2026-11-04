module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel

/-!
# The composition law for the complex-level derived pullback comparison

For composable morphisms of ringed spaces the comparison from derived pullback to degreewise
pullback is compatible with the composition isomorphism of [Stacks Project, Tag 0D5S]. That
statement, `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` in the namespace
`Stacks.Cohomology.DerivedPushforwardComposition`, is about the presentation
`CategoryTheory.DerivedCategory.Qh` of the derived category by the homotopy category. Derived
extension of scalars is instead left derived along `CategoryTheory.DerivedCategory.Q`, so the
affine comparison square of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentStandardModel.lean` uses the repackaged
comparison `AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison` out of `Q`. This
file transports the composition law to that presentation, and records the two sides of the
resulting cocycle for the morphisms of affine schemes induced by a pair of ring maps
`f : R ⟶ S` and `g : S ⟶ T`.

The content is the `Qh`-level law; the passage to `Q` is that law conjugated by
`CategoryTheory.DerivedCategory.quotientCompQhIso` together with the naturality of the three
comparisons.

## Main definitions

* `AlgebraicGeometry.StandardModel.specDerivedPullbackComp` — the composition isomorphism
  `Lf^* ⋙ Lg^* ≅ L(f ≫ g)^*` of [Stacks Project, Tag 0D5S] for the morphisms of affine schemes
  induced by `f` and `g`.
* `AlgebraicGeometry.StandardModel.specPullbackComp` — the degreewise composition isomorphism
  `f^* ⋙ g^* ≅ (f ≫ g)^*` on sheaves of modules.
* `AlgebraicGeometry.StandardModel.iteratedDerivedPullbackComplexComparison` and
  `AlgebraicGeometry.StandardModel.iteratedPullbackComplexIso` — the two sides of the cocycle:
  the comparison from `Q ⋙ (Lf^* ⋙ Lg^*)` to the iterated degreewise pullback, and the
  identification of the degreewise pullback along `f ≫ g` with the iterated one.

## Main results

* `Stacks.DerivedPullback.ComplexLevel.comparison_comp_of_homotopyPinning` — the chase, stated
  for arbitrary categories, functors and comparison maps: a composition law for comparisons out
  of one presentation of a localization gives the law for the comparisons repackaged along a
  second presentation.
* `Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp` — the pullback-composition
  isomorphism of `AlgebraicGeometry.Scheme.Modules` is the ringed-space one, both being the mate
  of the pushforward-composition isomorphism.
* `AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison_comp_compIsoCanonical` — the
  composition law at `Q` for composable morphisms of ringed spaces, and
  `AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison_comp_schemeFactorIso` — the
  same for a factorisation `p ≫ q = k` of morphisms of schemes.
* `AlgebraicGeometry.StandardModel.iteratedDerivedPullbackComplexComparison_app` — the value of
  the iterated comparison at a complex.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPullbackComparison)
open Stacks.Cohomology.DerivedPushforwardComposition
  (derivedPullbackCompIsoCanonical_hom_app_comp_comparison)

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u

namespace Stacks.DerivedPullback.ComplexLevel

/-! ### The chase, for arbitrary categories and comparison maps -/

section Abstract

variable {CX : Type u₁} [Category.{v₁} CX] {CY : Type u₂} [Category.{v₂} CY]
  {CZ : Type u₃} [Category.{v₃} CZ]
  {KX : Type u₄} [Category.{v₄} KX] {KY : Type u₅} [Category.{v₅} KY]
  {KZ : Type u₆} [Category.{v₆} KZ]
  {DX : Type u₇} [Category.{v₇} DX] {DY : Type u₈} [Category.{v₈} DY]
  {DZ : Type u₉} [Category.{v₉} DZ]
  {quotX : CX ⥤ KX} {quotY : CY ⥤ KY} {quotZ : CZ ⥤ KZ}
  {QhX : KX ⥤ DX} {QhY : KY ⥤ DY} {QhZ : KZ ⥤ DZ}
  {QX : CX ⥤ DX} {QY : CY ⥤ DY} {QZ : CZ ⥤ DZ}
  (qX : quotX ⋙ QhX ≅ QX) (qY : quotY ⋙ QhY ≅ QY) (qZ : quotZ ⋙ QhZ ≅ QZ)
  {Pa : CY ⥤ CX} {Pb : CZ ⥤ CY} {Pc : CZ ⥤ CX}
  {Pah : KY ⥤ KX} {Pbh : KZ ⥤ KY} {Pch : KZ ⥤ KX}
  (Fa : quotY ⋙ Pah ≅ Pa ⋙ quotX) (Fb : quotZ ⋙ Pbh ≅ Pb ⋙ quotY)
  (Fc : quotZ ⋙ Pch ≅ Pc ⋙ quotX)
  {La : DY ⥤ DX} {Lb : DZ ⥤ DY} {Lc : DZ ⥤ DX}
  (γa : QhY ⋙ La ⟶ Pah ⋙ QhX) (γb : QhZ ⋙ Lb ⟶ Pbh ⋙ QhY)
  (γc : QhZ ⋙ Lc ⟶ Pch ⋙ QhX)
  (Φ : Lb ⋙ La ≅ Lc) (ph : Pbh ⋙ Pah ≅ Pch) (pc : Pb ⋙ Pa ≅ Pc)

/-- **Transport of a composition law between two presentations of a localization.** Let `Pa`,
`Pb`, `Pc` be functors on the unlocalized categories with lifts `Pah`, `Pbh`, `Pch` to the
intermediate categories, let `qX`, `qY`, `qZ` identify `quot ⋙ Qh` with `Q`, and let `Ca`, `Cb`,
`Cc` be comparisons out of `Q` obtained from comparisons `γa`, `γb`, `γc` out of `Qh` by
conjugation (`hCa`, `hCb`, `hCc`). If the composition isomorphism `Φ` of the localized functors
satisfies the composition law for `γa`, `γb`, `γc` through the intermediate composition
isomorphism `ph` (`hΦ`), and `ph` agrees with the unlocalized composition isomorphism `pc`
(`hdeg`), then `Φ` satisfies the composition law for `Ca`, `Cb`, `Cc` through `pc`.

The two sides are brought together by the naturality of `Φ`, of `γa` and of `qX`. -/
theorem comparison_comp_of_homotopyPinning
    (Ca : QY ⋙ La ⟶ Pa ⋙ QX) (Cb : QZ ⋙ Lb ⟶ Pb ⋙ QY) (Cc : QZ ⋙ Lc ⟶ Pc ⋙ QX)
    (hCa : ∀ M : CY, Ca.app M = La.map (qY.inv.app M) ≫ γa.app (quotY.obj M) ≫
      QhX.map (Fa.hom.app M) ≫ qX.hom.app (Pa.obj M))
    (hCb : ∀ M : CZ, Cb.app M = Lb.map (qZ.inv.app M) ≫ γb.app (quotZ.obj M) ≫
      QhY.map (Fb.hom.app M) ≫ qY.hom.app (Pb.obj M))
    (hCc : ∀ M : CZ, Cc.app M = Lc.map (qZ.inv.app M) ≫ γc.app (quotZ.obj M) ≫
      QhX.map (Fc.hom.app M) ≫ qX.hom.app (Pc.obj M))
    (hΦ : ∀ W : KZ, Φ.hom.app (QhZ.obj W) ≫ γc.app W =
      La.map (γb.app W) ≫ γa.app (Pbh.obj W) ≫ QhX.map (ph.hom.app W))
    (hdeg : ∀ M : CZ, ph.hom.app (quotZ.obj M) ≫ Fc.hom.app M =
      Pah.map (Fb.hom.app M) ≫ Fa.hom.app (Pb.obj M) ≫ quotX.map (pc.hom.app M))
    (K : CZ) :
    Cc.app K ≫ QX.map (pc.inv.app K) =
      Φ.inv.app (QZ.obj K) ≫ La.map (Cb.app K) ≫ Ca.app (Pb.obj K) := by
  have n1 := Φ.hom.naturality (qZ.inv.app K)
  have n2 := γa.naturality (Fb.hom.app K)
  have n3 := qX.hom.naturality (pc.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3
  suffices Φ.hom.app (QZ.obj K) ≫ Cc.app K ≫ QX.map (pc.inv.app K) =
      La.map (Cb.app K) ≫ Ca.app (Pb.obj K) by
    rw [← this, Iso.inv_hom_id_app_assoc]
  rw [hCc, hCb, hCa]
  simp only [Category.assoc]
  rw [← reassoc_of% n1, reassoc_of% (hΦ (quotZ.obj K)),
    ← Functor.map_comp_assoc QhX (ph.hom.app (quotZ.obj K)) (Fc.hom.app K), hdeg K]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n3]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Functor.map_comp_assoc La (qY.hom.app (Pb.obj K)) (qY.inv.app (Pb.obj K))]
  simp only [Iso.hom_inv_id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% n2]

end Abstract

/-! ### Components of the whiskered assemblies -/

section Whiskered

variable {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] {B₁ : Type u₄} [Category.{v₄} B₁]
  {B₂ : Type u₅} [Category.{v₅} B₂] {B₃ : Type u₆} [Category.{v₆} B₃]

/-- The value at an object of the comparison for a composite assembled by whiskering two
comparisons: the first comparison pushed along the second functor, then the second. -/
theorem whiskerComp_app {QZ : A₃ ⥤ B₃} {QY : A₂ ⥤ B₂} {QX : A₁ ⥤ B₁}
    {Lb : B₃ ⥤ B₂} {La : B₂ ⥤ B₁} {Pb : A₃ ⥤ A₂} {Pa : A₂ ⥤ A₁}
    (α : QZ ⋙ Lb ⟶ Pb ⋙ QY) (β : QY ⋙ La ⟶ Pa ⋙ QX) (K : A₃) :
    ((Functor.associator QZ Lb La).inv ≫ Functor.whiskerRight α La ≫
        (Functor.associator Pb QY La).hom ≫ Functor.whiskerLeft Pb β).app K =
      La.map (α.app K) ≫ β.app (Pb.obj K) := by
  simp

end Whiskered

/-! ### The composition isomorphism on complexes and on the homotopy category -/

section Homotopy

variable {ι : Type u₁} {V : Type u₂} [Category.{v₂} V] [Preadditive V]
  {W : Type u₃} [Category.{v₃} W] [Preadditive W]
  {W' : Type u₄} [Category.{v₄} W'] [Preadditive W']

end Homotopy

end Stacks.DerivedPullback.ComplexLevel

/-! ### The two spellings of the pullback-composition isomorphism -/

namespace Stacks.Scheme.Modules

variable {X Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)

/-- **The pullback-composition isomorphism of a pair of morphisms of schemes is the
ringed-space one.** Both `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`Stacks.DerivedPullback.Composition.modulePullbackComp` are
`CategoryTheory.Adjunction.leftAdjointCompIso` of the pushforward-composition isomorphism, and
the two pushforward-composition isomorphisms have identity components. -/
theorem pullbackComp_eq_modulePullbackComp :
    AlgebraicGeometry.Scheme.Modules.pullbackComp p q =
      Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
        q.toLRSHom.toShHom :=
  congrArg
    (Adjunction.leftAdjointCompIso
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction q)
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p)
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)))
    (Iso.ext (NatTrans.ext (funext fun _ => rfl)) :
      AlgebraicGeometry.Scheme.Modules.pushforwardComp p q =
        RingedSpaceModuleAdjunction.modulePushforwardComp
          p.toLRSHom.toShHom q.toLRSHom.toShHom)

end Stacks.Scheme.Modules

namespace AlgebraicGeometry.StandardModel

/-! ### The composition law at the presentation `DerivedCategory.Q` -/

/-- The value of `AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison` at a complex,
written out as a composite of four maps: the comparison of [Stacks Project, Tag 06YJ] conjugated
by the identification of the two presentations of the derived category and by the factorisation
of degreewise pullback through the homotopy category. -/
theorem derivedPullbackComplexComparison_app {X Y : RingedSpace.{u, u}} (a : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullbackComplexComparison a).app K =
      (derivedPullback a).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing Y))).inv.app K) ≫
        (derivedPullbackComparison a).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((modulePullback a).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
          (((modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  dsimp only [derivedPullbackComplexComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]

/-- **[Stacks Project, Tag 0D5S] at the presentation `CategoryTheory.DerivedCategory.Q`.** For
composable morphisms of ringed spaces the comparison from `L(a ≫ b)^*` to degreewise pullback,
followed by the degreewise composition isomorphism, is the composition isomorphism of the derived
pullbacks followed by the iterated comparison.

This is `derivedPullbackCompIsoCanonical_hom_app_comp_comparison` transported along
`CategoryTheory.DerivedCategory.quotientCompQhIso`. -/
theorem derivedPullbackComplexComparison_comp_compIsoCanonical {X Y Z : RingedSpace.{u, u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (derivedPullbackComplexComparison (a ≫ b)).app K ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Stacks.DerivedPullback.Composition.modulePullbackComp a b)
            (ComplexShape.up ℤ)).inv.app K) =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a b).inv.app
          (DerivedCategory.Q.obj K) ≫
        (derivedPullback a).map ((derivedPullbackComplexComparison b).app K) ≫
          (derivedPullbackComplexComparison a).app
            (((modulePullback b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Stacks.DerivedPullback.ComplexLevel.comparison_comp_of_homotopyPinning
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X)))
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y)))
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z)))
    ((modulePullback a).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    ((modulePullback b).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    ((modulePullback (a ≫ b)).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    (derivedPullbackComparison a) (derivedPullbackComparison b)
    (derivedPullbackComparison (a ≫ b))
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a b)
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a b)
    (Functor.mapHomologicalComplexCompIso
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b) (ComplexShape.up ℤ))
    (derivedPullbackComplexComparison a) (derivedPullbackComplexComparison b)
    (derivedPullbackComplexComparison (a ≫ b))
    (derivedPullbackComplexComparison_app a) (derivedPullbackComplexComparison_app b)
    (derivedPullbackComplexComparison_app (a ≫ b))
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison a b)
    (fun M => StacksDraft.MapHomotopyCategory.mapHomotopyCategoryCompIso_hom_app_comp_factors
      (Stacks.DerivedPullback.Composition.modulePullbackComp a b) (ComplexShape.up ℤ) M)
    K

/-- **[Stacks Project, Tag 0D5S] at `CategoryTheory.DerivedCategory.Q`, for schemes.** The same
statement as `derivedPullbackComplexComparison_comp_compIsoCanonical`, for a factorisation
`p ≫ q = k` of morphisms of schemes and the composition isomorphisms of
`AlgebraicGeometry.Scheme.Modules` and `Stacks.DerivedPullback.schemeFactorIso`. -/
theorem derivedPullbackComplexComparison_comp_schemeFactorIso {X Y Z : Scheme.{u}}
    (p : X ⟶ Y) (q : Y ⟶ Z) (k : X ⟶ Z) (hk : p ≫ q = k)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ) :
    (derivedPullbackComplexComparison k.toLRSHom.toShHom).app K ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Scheme.Modules.pullbackComp p q ≪≫
            Scheme.Modules.pullbackCongr hk).symm (ComplexShape.up ℤ)).hom.app K) =
      (Stacks.DerivedPullback.schemeFactorIso p q k hk).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedPullback p.toLRSHom.toShHom).map
            ((derivedPullbackComplexComparison q.toLRSHom.toShHom).app K) ≫
          (derivedPullbackComplexComparison p.toLRSHom.toShHom).app
            (((Scheme.Modules.pullback q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  subst hk
  have hpc : (Scheme.Modules.pullbackComp p q ≪≫
        Scheme.Modules.pullbackCongr (rfl : p ≫ q = p ≫ q)) =
      Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
        q.toLRSHom.toShHom :=
    (congrArg (fun i => Scheme.Modules.pullbackComp p q ≪≫ i)
        (show Scheme.Modules.pullbackCongr (rfl : p ≫ q = p ≫ q) =
          Iso.refl (Scheme.Modules.pullback (p ≫ q)) from rfl)).trans
      ((Iso.trans_refl _).trans (Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp p q))
  rw [hpc]
  exact derivedPullbackComplexComparison_comp_compIsoCanonical p.toLRSHom.toShHom
    q.toLRSHom.toShHom K

/-! ### The cocycle for a pair of ring maps -/

variable (R S T : CommRingCat.{u}) (f : R ⟶ S) (g : S ⟶ T)

/-- The composition isomorphism `Lf^* ⋙ Lg^* ≅ L(f ≫ g)^*` of [Stacks Project, Tag 0D5S] for the
morphisms of affine schemes induced by `f : R ⟶ S` and `g : S ⟶ T`. -/
def specDerivedPullbackComp :
    specDerivedPullback f ⋙ specDerivedPullback g ≅ specDerivedPullback (f ≫ g) :=
  Stacks.DerivedPullback.schemeFactorIso (Spec.map g) (Spec.map f) (Spec.map (f ≫ g))
    (Spec.map_comp f g).symm

/-- The degreewise composition isomorphism `f^* ⋙ g^* ≅ (f ≫ g)^*` on sheaves of modules over
the affine schemes induced by `f : R ⟶ S` and `g : S ⟶ T`. -/
def specPullbackComp :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map (f ≫ g)) :=
  Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
    Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm

/-- The comparison from `Q ⋙ (Lf^* ⋙ Lg^*)` to the iterated degreewise pullback: the comparison
for `Lf^*` pushed along `Lg^*`, then the comparison for `Lg^*`. -/
def iteratedDerivedPullbackComplexComparison :
    DerivedCategory.Q ⋙ (specDerivedPullback f ⋙ specDerivedPullback g) ⟶
      (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom)
      (specDerivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (derivedPullbackComplexComparison (Spec.map g).toLRSHom.toShHom)

/-- `AlgebraicGeometry.StandardModel.specPullbackComp` on complexes, after localisation: the
degreewise pullback along `Spec (f ≫ g)` is the iterated degreewise pullback. -/
def iteratedPullbackComplexIso :
    (Scheme.Modules.pullback (Spec.map (f ≫ g))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅
      (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((Scheme.Modules.pullback (Spec.map g)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) :=
  Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (specPullbackComp R S T f g).symm (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (Scheme.Modules.pullback (Spec.map f) ⋙
            Scheme.Modules.pullback (Spec.map g))) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-- The value of `AlgebraicGeometry.StandardModel.iteratedDerivedPullbackComplexComparison` at a
complex: the comparison for `Lf^*` pushed along `Lg^*`, then the comparison for `Lg^*`. -/
theorem iteratedDerivedPullbackComplexComparison_app
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace)) ℤ) :
    (iteratedDerivedPullbackComplexComparison R S T f g).app K =
      (specDerivedPullback g).map
          ((derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom).app K) ≫
        (derivedPullbackComplexComparison (Spec.map g).toLRSHom.toShHom).app
          (((Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  Stacks.DerivedPullback.ComplexLevel.whiskerComp_app
    (derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom)
    (derivedPullbackComplexComparison (Spec.map g).toLRSHom.toShHom) K

end AlgebraicGeometry.StandardModel

end
