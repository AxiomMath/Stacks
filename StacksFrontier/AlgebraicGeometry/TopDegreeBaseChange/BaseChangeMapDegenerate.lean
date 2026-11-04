module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationInhabitant

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] when the top higher direct image vanishes

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap` is the canonical map

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

of [Stacks, Tag 0EX3], and conclusion (c) of that tag is the assertion that `γ` is an
isomorphism. This file proves (c) when the two objects `γ` compares are both zero, discharges
that vanishing by [Stacks, Tag 01XC] when the base-changed morphisms are affine and `d > 0`, and
shows that at `d = 0` it fails: for the second square taken to be the identity, both ends of `γ`
are nonzero as soon as `R^d f'_* F'` is. Conclusion (c) in full, with no vanishing hypothesis, is
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`).

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMapSelf`: the canonical
  map `γ` for the second square taken to be the identity square on `f'`.

## Main results

* `…TopDegreeBaseChange.isZero_rightDerivedPlus_of_isZero_homologyFunctor_obj`:
  the converse of `isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus` — the two
  models of a right derived functor agree on the vanishing of the cohomology of a single object
  in *both* directions.
* `…TopDegreeBaseChange.isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus`
  and `…isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward`: that equivalence
  at a morphism of schemes, which is the spelling the canonical map is stated at.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isZero`:
  **conclusion (c) when both objects compared are zero.**
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isAffineHom`
  and `…_ofIsAffineHom`: its instances at an affine morphism and `d > 0`.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isIso_restrict`:
  **conclusion (c) is local on `Y''`**.
* `…TopDegreeBaseChange.not_isZero_source_topDirectImageBaseChangeMapSelf`,
  `…not_isZero_target_topDirectImageBaseChangeMapSelf` and their `…_unit` instances: at the
  identity second square the two ends of `γ` are nonzero.

## Implementation notes

The two `IsZero` hypotheses of `isIso_topDirectImageBaseChangeMap_of_isZero` say that the
objects the tag's conclusions are about are zero; they are stated explicitly, so the theorem is
not mistaken for the tag.

`DerivedModelCrossing.lean` proves that the vanishing of `Functor.rightDerivedPlus` implies the
vanishing of the degree-`i` cohomology of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`. The nonvanishing
statements need the converse, which is proved here from the same isomorphism
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`.

The projections `(ofIsAffineHom f d g' f' g sq).X'` and `(…).f'` agree with `X'` and `f'` by
`rfl`, but instance search does not see through them. So the quasi-coherence binder of
`isIso_topDirectImageBaseChangeMap_ofIsAffineHom` is stated on
`(ofIsAffineHom f d g' f' g sq).X'.Modules`, the affineness hypotheses of
`isIso_topDirectImageBaseChangeMap_of_isAffineHom` are explicit arguments, and the situation and
the module are written out at its call site.

No `stacks` attribute is placed: every theorem here concluding (c) carries a vanishing
hypothesis that [Stacks, Tag 0EX3] does not. The tag is carried by
`isZero_rightDerivedPlus_pushforward_baseChange` (`BaseChangeVanishing.lean`, clause (a)),
`isIso_higherDirectImageTensorMap` and `topDirectImageTensorComparison`
(`TensorComparisonBase.lean`, clause (b)) and
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`,
clause (c)).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open DerivedCategory

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

section Generic

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- **The two models of a right derived functor agree on the vanishing of the cohomology of a
single object, in the direction from the unbounded model to the bounded below one.**

This is the converse of `isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus`, with the same
hypotheses on `R` and `β`: an additive `F : A ⥤ B`, a functor `R` of the unbounded derived
categories carrying a comparison from degreewise `F` invertible at every K-injective complex. If
the degree-`i` cohomology of `R(M[0])` vanishes, so does `RⁱF(M)`. -/
theorem isZero_rightDerivedPlus_of_isZero_homologyFunctor_obj (F : A ⥤ B) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hβ : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (M : A) (i : ℤ)
    (h : IsZero ((homologyFunctor B i).obj (R.obj ((singleFunctor A 0).obj M)))) :
    IsZero ((F.rightDerivedPlus i).obj M) := by
  have hE : ((DerivedCategory.Plus.singleFunctor A 0).obj M).obj.IsGE 0 := by
    show ((singleFunctor A 0).obj M).IsGE 0
    infer_instance
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus F R β hβ
    ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 hE
  exact IsZero.of_iso h ((homologyFunctor B i).mapIso e).symm

end Generic

section Schemes

variable {X Y : Scheme.{u}}

/-- **`Rⁱ f_* F = 0` implies `Hⁱ(Rf_*(F[0])) = 0`, at a morphism of schemes.** This is
`isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus` at `F = f_*` and
`R = Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f`, whose comparison is
invertible at the K-injective complexes. -/
theorem isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus (f : X ⟶ Y)
    (F : X.Modules) (i : ℤ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F)) :
    IsZero ((homologyFunctor Y.Modules i).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor X.Modules 0).obj F))) :=
  isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus
    (modulePushforward f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f.toLRSHom.toShHom)
    (fun I hI =>
      isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    F i h

/-- **`Hⁱ(Rf_*(F[0])) = 0` implies `Rⁱ f_* F = 0`, at a morphism of schemes.** The converse of
`isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus`, needed because the ends of
the canonical base-change map are stated at the unbounded model while the available nonvanishing
is stated at the bounded below one. -/
theorem isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward (f : X ⟶ Y)
    (F : X.Modules) (i : ℤ)
    (h : IsZero ((homologyFunctor Y.Modules i).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor X.Modules 0).obj F)))) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) :=
  isZero_rightDerivedPlus_of_isZero_homologyFunctor_obj
    (modulePushforward f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f.toLRSHom.toShHom)
    (fun I hI =>
      isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    F i h

end Schemes

variable {X'' Y'' : Scheme.{u}}

/-- **Conclusion (c) of [Stacks, Tag 0EX3] when both objects compared are zero.** The canonical
map

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`

is an isomorphism as soon as `R^d f'_* F'` vanishes on `Y'` and `R^d f''_* (h')^* F'` vanishes on
`Y''`. Both hypotheses assert that the objects the tag's conclusions are about are zero; see
`not_isZero_source_topDirectImageBaseChangeMapSelf` for a situation where the first fails. -/
theorem isIso_topDirectImageBaseChangeMap_of_isZero
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (hsrc : IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F'))
    (htgt : IsZero (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
      ((Scheme.Modules.pullback h').obj F'))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) :=
  IsZero.isIso
    (Functor.map_isZero (Scheme.Modules.pullback h)
      (isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus S.f' F'
        (S.d : ℤ) hsrc))
    (isZero_homologyFunctor_derivedPushforward_of_isZero_rightDerivedPlus f''
      ((Scheme.Modules.pullback h').obj F') (S.d : ℤ) htgt)
    _

/-- **Conclusion (c) of [Stacks, Tag 0EX3] above the cohomological dimension of an affine
morphism.** If the base-changed morphism and the twice-base-changed morphism are both affine and
`d > 0`, then both objects the canonical map compares vanish by [Stacks, Tag 01XC] and the map is
an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_isAffineHom
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    (haf' : IsAffineHom S.f') (haf'' : IsAffineHom f'') (hd : 0 < S.d) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) := by
  have := haf'
  have := haf''
  exact isIso_topDirectImageBaseChangeMap_of_isZero S F' h' f'' h sq
    (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom S.f' F' (S.d : ℤ)
      (by exact_mod_cast hd))
    (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f''
      ((Scheme.Modules.pullback h').obj F') (S.d : ℤ) (by exact_mod_cast hd))

/-- **Conclusion (c) at the base case of the situation structure.** The structure morphism is
affine, so both base changes of it are affine
(`CategoryTheory.MorphismProperty.of_isPullback`), and above degree zero the canonical map of
[Stacks, Tag 0EX3] compares two zero objects. -/
theorem isIso_topDirectImageBaseChangeMap_ofIsAffineHom
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (hd : 0 < d) [IsAffineHom f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g)
    (F' : (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom
      f d g' f' g sq).X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ Y') (sq₂ : IsPullback h' f'' f' h) :
    IsIso (topDirectImageBaseChangeMap
      (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom f d g' f' g sq)
      F' h' f'' h
      (toShHom_comm_of_isPullback
        (S := Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom f d g' f' g sq)
        h' f'' h sq₂)) :=
  have haf' : IsAffineHom f' :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) sq ‹IsAffineHom f›
  isIso_topDirectImageBaseChangeMap_of_isAffineHom
    (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom f d g' f' g sq)
    F' h' f'' h _ haf'
    (MorphismProperty.of_isPullback (P := @IsAffineHom) sq₂ haf') hd

/-- **Conclusion (c) of [Stacks, Tag 0EX3] is local on `Y''`.** The canonical map is a morphism of
sheaves of modules on `Y''`, and invertibility of such a morphism is local on the scheme
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), so it suffices that the
restriction of the map to each member of an open covering of `Y''` be invertible. This is the
half concerning `Y''` of the source's reduction *"we can check (a), (b), and (c) locally on `Y'`
and `Y''`"*. -/
theorem isIso_topDirectImageBaseChangeMap_of_isIso_restrict
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)
    {I : Type*} (V : I → Y''.Opens) (hV : TopologicalSpace.IsOpenCover V)
    (hiso : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (V i).ι).map
      (topDirectImageBaseChangeMap S F' h' f'' h sq))) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ V hV hiso

/-! ### Where the vanishing reduction does not reach

The second cartesian square of [Stacks, Tag 0EX3] may be taken to be the identity square on `f'`.
The canonical map is then a morphism between two objects each isomorphic to `H^d(Rf'_*(F'[0]))`,
and so nonzero whenever `R^d f'_* F'` is. -/

/-- The identity square on `f'`, read as a commutative square of sheaved spaces, which is the form
in which `topDirectImageBaseChangeMap` consumes a square. -/
theorem toShHom_comm_id_square
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) :
    (Scheme.Hom.toLRSHom (𝟙 S.X')).toShHom ≫ S.f'.toLRSHom.toShHom
      = S.f'.toLRSHom.toShHom ≫ (Scheme.Hom.toLRSHom (𝟙 S.Y')).toShHom := by
  rw [show Scheme.Hom.toLRSHom (𝟙 S.X') = 𝟙 S.X'.toLocallyRingedSpace from rfl,
    show Scheme.Hom.toLRSHom (𝟙 S.Y') = 𝟙 S.Y'.toLocallyRingedSpace from rfl,
    LocallyRingedSpace.id_toShHom', LocallyRingedSpace.id_toShHom']
  simp

/-- **The canonical map `γ` of [Stacks, Tag 0EX3] at the identity second square.** Its declared
type names the two objects that `not_isZero_source_topDirectImageBaseChangeMapSelf` and
`not_isZero_target_topDirectImageBaseChangeMapSelf` are about. -/
def topDirectImageBaseChangeMapSelf
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] :
    (Scheme.Modules.pullback (𝟙 S.Y')).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F'))) ⟶
    (homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj
          ((Scheme.Modules.pullback (𝟙 S.X')).obj F'))) :=
  topDirectImageBaseChangeMap S F' (𝟙 S.X') S.f' (𝟙 S.Y') (toShHom_comm_id_square S)

/-- **The source of the canonical map at the identity second square is nonzero whenever
`R^d f'_* F'` is.** Pullback along the identity is isomorphic to the identity functor
(`AlgebraicGeometry.Scheme.Modules.pullbackId`), and the vanishing of the degree-`d` cohomology of
`Rf'_*(F'[0])` would force the vanishing of `R^d f'_* F'`. -/
theorem not_isZero_source_topDirectImageBaseChangeMapSelf
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) (F' : S.X'.Modules)
    (hne : ¬ IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')) :
    ¬ IsZero ((Scheme.Modules.pullback (𝟙 S.Y')).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F')))) := by
  intro hz
  refine hne (isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward S.f' F'
    (S.d : ℤ) (IsZero.of_iso hz ?_))
  exact ((Scheme.Modules.pullbackId S.Y').app _).symm

/-- **The target of the canonical map at the identity second square is nonzero whenever
`R^d f'_* F'` is.** -/
theorem not_isZero_target_topDirectImageBaseChangeMapSelf
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) (F' : S.X'.Modules)
    (hne : ¬ IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')) :
    ¬ IsZero ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj
          ((Scheme.Modules.pullback (𝟙 S.X')).obj F')))) := by
  intro hz
  exact hne (IsZero.of_iso
    (isZero_rightDerivedPlus_of_isZero_homologyFunctor_derivedPushforward S.f' _ (S.d : ℤ) hz)
    (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).mapIso
      ((Scheme.Modules.pullbackId S.X').app F').symm))

/-- **The source of the canonical map is nonzero at the structure sheaf of the base case, at
`d = 0`.** So the vanishing hypothesis of `isIso_topDirectImageBaseChangeMap_of_isZero` fails
there, and conclusion (c) of [Stacks, Tag 0EX3] at that situation is not covered by it. -/
theorem not_isZero_source_topDirectImageBaseChangeMapSelf_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero ((Scheme.Modules.pullback
      (𝟙 (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf f 0).Y')).obj
      ((homologyFunctor
          (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf f 0).Y'.Modules
          (((Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
            f 0).d : ℕ) : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
              f 0).f'.toLRSHom.toShHom).obj
          ((singleFunctor
              (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
                f 0).X'.Modules 0).obj
            (show (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
              f 0).X'.Modules from SheafOfModules.unit X.ringCatSheaf))))) :=
  not_isZero_source_topDirectImageBaseChangeMapSelf _ _
    (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.not_isZero_topDirectImage_unit f)

/-- **The target of the canonical map is nonzero at the structure sheaf of the base case, at
`d = 0`.** -/
theorem not_isZero_target_topDirectImageBaseChangeMapSelf_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [Nontrivial Γ(X, (⊤ : X.Opens))] :
    ¬ IsZero ((homologyFunctor
        (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf f 0).Y'.Modules
        (((Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
          f 0).d : ℕ) : ℤ)).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
            f 0).f'.toLRSHom.toShHom).obj
        ((singleFunctor
            (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
              f 0).X'.Modules 0).obj
          ((Scheme.Modules.pullback
              (𝟙 (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
                f 0).X')).obj
            (show (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHomSelf
              f 0).X'.Modules from SheafOfModules.unit X.ringCatSheaf))))) :=
  not_isZero_target_topDirectImageBaseChangeMapSelf _ _
    (Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.not_isZero_topDirectImage_unit f)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
