module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.UnderivedBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Homology.KFlat.RestrictFlat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# The derived base change map on a K-flat complex of quasi-coherent modules

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` affine, and let `C` be a complex of quasi-coherent
`𝒪_X`-modules which is K-flat and whose direct image `f_*C` is K-flat.  Then the derived base
change map `Lg^*Rf_*C ⟶ Rf'_*L(g')^*C` of Stacks 08HY is an isomorphism: both derived pullbacks
are computed degreewise, both derived direct images are computed degreewise (Stacks 0G9N for an
affine morphism), and the degreewise base change morphism is invertible (Stacks 02KG).

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_Qh_of_isAffineHom`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- The middle factor of a threefold composite is invertible as soon as the composite and the two
outer factors are. -/
theorem isIso_of_isIso_comp₃ {C : Type*} [Category C] {P Q R T : C} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : R ⟶ T} (h : IsIso (a ≫ b ≫ c)) (ha : IsIso a) (hc : IsIso c) : IsIso b := by
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_right b c

/-- The second factor of a composite is invertible as soon as the composite and the first factor
are. -/
theorem isIso_right_of_isIso_comp {C : Type*} [Category C] {P Q R : C} {a : P ⟶ Q} {b : Q ⟶ R}
    (h : IsIso (a ≫ b)) (ha : IsIso a) : IsIso b :=
  IsIso.of_isIso_comp_left a b

/-- The first factor of a composite is invertible as soon as the composite and the second factor
are. -/
theorem isIso_left_of_isIso_comp {C : Type*} [Category C] {P Q R : C} {a : P ⟶ Q} {b : Q ⟶ R}
    (h : IsIso (a ≫ b)) (hb : IsIso b) : IsIso a :=
  IsIso.of_isIso_comp_right a b

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The derived base change map at a K-flat complex of quasi-coherent modules**, for a cartesian
square with affine right-hand morphism, is an isomorphism as soon as the comparison of the derived
pullback with the degreewise pullback is invertible at the direct image of the complex. -/
theorem isIso_derivedBaseChangeMap_Qh_of_isIso_comparison (sq : IsPullback g' f' f g)
    [IsAffineHom f]
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hC : ∀ n, (C.X n).IsQuasicoherent)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace C)
    (h₃ : IsIso ((derivedPullbackComparison g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) := by
  have hf' : IsAffineHom f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    inferInstance
  have hG := derivedBaseChangeMap_Qh_comparison g'.toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)
  have h₁ : IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom f C hC
  have h₂ : IsIso ((derivedPullbackComparison g'.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      g'.toLRSHom.toShHom C hK
  have h₄ := isIso_underivedBaseChangeSquare_app_quotient sq C hC
  have h₅ : IsIso ((derivedPushforwardUnit f'.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom f' _ fun n =>
      @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _ g' (C.X n) (hC n)
  have hR : IsIso ((derivedPullbackComparison g.toLRSHom.toShHom).app
        (((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      DerivedCategory.Qh.map ((underivedBaseChangeSquare g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
        (comp_toShHom_of_comm sq.w)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (derivedPushforwardUnit f'.toLRSHom.toShHom).app
        (((modulePullback g'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ (@IsIso.comp_isIso _ _ _ _ _ _ _
      (Functor.map_isIso DerivedCategory.Qh _) h₅)
  rw [← hG] at hR
  have hA : IsIso ((derivedPullback g.toLRSHom.toShHom).map
      ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) := Functor.map_isIso _ _
  have hB : IsIso ((derivedPushforward f'.toLRSHom.toShHom).map
      ((derivedPullbackComparison g'.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) := Functor.map_isIso _ _
  exact isIso_of_isIso_comp₃ hR hA hB

/-- **The derived base change map at a K-flat complex of quasi-coherent modules with K-flat
direct image**, for a cartesian square with affine right-hand morphism, is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_Qh_of_isAffineHom (sq : IsPullback g' f' f g) [IsAffineHom f]
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hC : ∀ n, (C.X n).IsQuasicoherent)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace C)
    (hK' : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex S.toRingedSpace
      (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) :=
  isIso_derivedBaseChangeMap_Qh_of_isIso_comparison sq C hC hK
    (Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
      g.toLRSHom.toShHom _ hK')

/-- The direct image along `Spec φ` of the complex of sheaves associated to a K-flat complex of
`F`-modules is K-flat, for `φ : R ⟶ F` flat. -/
theorem kFlatComplex_pushforward_tilde {R F : CommRingCat.{u}} (φ : R ⟶ F) (hφ : φ.hom.Flat)
    (Q : CochainComplex (ModuleCat.{u} F) ℤ) (hQ : CochainComplex.KFlat.{u, u} Q) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace
      (((modulePushforward (Spec.map φ).toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((tilde.functor F).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q)) := by
  have h₁ := Stacks.TildeStalk.kFlatComplex_tilde R _
    (CochainComplex.KFlat.kFlat_restrictScalarsLarge_of_flat φ.hom hφ hQ)
  exact CochainComplex.KFlatBifunctor.KFlat.of_iso _ h₁
    ((NatIso.mapHomologicalComplex (asIso (pushforwardTildeNatTrans R F φ))
      (ComplexShape.up ℤ)).app Q)

/-- Invertibility of the derived base change map transports along an isomorphism of objects. -/
theorem isIso_derivedBaseChangeMap_of_iso {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (e : K ≅ L)
    (h : IsIso (derivedBaseChangeMap g' f' f g sq K)) :
    IsIso (derivedBaseChangeMap g' f' f g sq L) := by
  have hn := derivedBaseChangeMap_naturality g' f' f g sq e.hom
  have : IsIso ((derivedPullback g).map ((derivedPushforward f).map e.hom) ≫
      derivedBaseChangeMap g' f' f g sq L) := by
    rw [hn]
    infer_instance
  exact isIso_right_of_isIso_comp this inferInstance

/-- **Flat base change along `Spec` of a flat ring map, on `D_QCoh`.**  For a flat homomorphism
`φ : R ⟶ F` and a cartesian square over an arbitrary `T' ⟶ Spec R`, the derived base change map
of Stacks 08HY is an isomorphism at every object of `D(𝒪_{Spec F})` with quasi-coherent
cohomology. -/
theorem isIso_derivedBaseChangeMap_of_flat {R F : CommRingCat.{u}} (φ : R ⟶ F)
    (hφ : φ.hom.Flat) {P' T' : Scheme.{u}} {gP : P' ⟶ Spec F} {p' : P' ⟶ T'}
    {gT : T' ⟶ Spec R} (sq : IsPullback gP p' (Spec.map φ) gT)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec F).toRingedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec F).Modules n).obj E).IsQuasicoherent) :
    IsIso (derivedBaseChangeMap gP.toLRSHom.toShHom p'.toLRSHom.toShHom
      (Spec.map φ).toLRSHom.toShHom gT.toLRSHom.toShHom (comp_toShHom_of_comm sq.w) E) := by
  obtain ⟨M, ⟨e⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory F E hE
  obtain ⟨Q, hQ, ⟨e'⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} M
  let C := ((tilde.functor F).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
  let u : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≅ E :=
    (DerivedCategory.quotientCompQhIso _).app C ≪≫
      ((tilde.functor F).mapDerivedCategoryFactors.app Q).symm ≪≫
      (tilde.functor F).mapDerivedCategory.mapIso e' ≪≫ e
  exact isIso_derivedBaseChangeMap_of_iso _ _ _ _ _ u
    (isIso_derivedBaseChangeMap_Qh_of_isAffineHom sq C
      (fun n => (inferInstance : ((tilde.functor F).obj (Q.X n)).IsQuasicoherent))
      (Stacks.TildeStalk.kFlatComplex_tilde F Q hQ) (kFlatComplex_pushforward_tilde φ hφ Q hQ))

end Stacks.Cohomology.DerivedBaseChange
