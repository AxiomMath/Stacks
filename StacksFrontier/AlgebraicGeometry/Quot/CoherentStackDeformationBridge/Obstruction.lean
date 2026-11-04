module

public import
  StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.FlatLiftCorrespondence
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningFlatLifts
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseFlatness

/-!
# The obstruction to lifting an object of `Coh_{X/Y}` across a first order thickening

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` a first order thickening
of schemes over `Y`, and assume `X_{T'} ⟶ T'` flat. Then the relative square of
`AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm` is Situation 08VV of the source:
a strict morphism of first order thickenings of ringed topoi whose vertical arrow
`X_{T'} ⟶ (X_{T'}, f'⁻¹𝒪_{T'})` is flat, and `𝒢` is flat over the base. Stacks 08VW, part (1),
then says that `ξ` lifts to `T'` exactly when the class
`o(𝒢, f^*𝒥 ⊗ 𝒢, 1) ∈ Ext²(𝒢, f^*𝒥 ⊗ 𝒢)` vanishes. This is the obstruction of the first proof of
Stacks 08WA.

## Main results

* `Stacks.isFlatMapULift_iso_hom_comp`: precomposing a flat morphism of sheaves of commutative
  rings on a site with enough points with an isomorphism keeps it flat.
* `AlgebraicGeometry.Space.isFlat_relBaseRight_smallEtaleRingedToposHom`: for a flat morphism
  `p : X ⟶ Y` of algebraic spaces, `X ⟶ (X, p⁻¹𝒪_Y)` is flat.
* `AlgebraicGeometry.Space.CoherentSituation.isFlatOverBase_thickenedModule`: `𝒢` is flat over the
  base of the relative square.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftObstruction`: the obstruction class.
* `AlgebraicGeometry.Space.CoherentSituation.nonempty_thickeningLift_iff_obstruction_eq_zero`:
  `ξ` lifts to `T'` exactly when the obstruction class vanishes.

## References

* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e u

namespace Stacks

/-- **Precomposing a flat morphism of sheaves of commutative rings with an isomorphism keeps it
flat**, on a site with a conservative family of points: at each point the fibre of the composite
is a ring isomorphism followed by a flat ring map (Stacks 05VC). -/
theorem isFlatMapULift_iso_hom_comp {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {t : Type*} (p : t → J.Point.{u})
    (hp : (ObjectProperty.ofObj (fun i ↦ (p i).ulift.{u + 1})).IsConservativeFamilyOfPoints)
    {P O O' : Sheaf J CommRingCat.{u}} (e : P ≅ O) (g : O ⟶ O')
    (hg : AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u} g) :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u} (e.hom ≫ g) := by
  rw [isFlatMapULift_iff_forall_flat p hp] at hg ⊢
  intro i
  have he : (((p i).presheafFiber (A := CommRingCat.{u})).map e.hom.hom).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (((p i).presheafFiber (A := CommRingCat.{u})).map e.hom.hom))
  change (((p i).presheafFiber (A := CommRingCat.{u})).map (e.hom.hom ≫ g.hom)).hom.Flat
  rw [Functor.map_comp, CommRingCat.hom_comp]
  exact RingHom.Flat.comp he (hg i)

end Stacks

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **For a flat morphism `p : X ⟶ Y` of algebraic spaces, `X ⟶ (X, p⁻¹𝒪_Y)` is flat**: its
structure map is that of the morphism of small étale ringed topoi of `p` (Stacks 073C) read
through the identification `id⁻¹p⁻¹𝒪_Y ≅ p⁻¹𝒪_Y`. -/
theorem isFlat_relBaseRight_smallEtaleRingedToposHom {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (hp : IsFlat B S hS p.hom) :
    RingedToposHom.IsFlat.{u, u + 1, u, u, u + 1, u}
      (relBaseRight (smallEtaleRingedToposHom B S hS p)) := by
  change AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{u, u + 1, u}
    (relBaseRight (smallEtaleRingedToposHom B S hS p)).fSharpInverseImage
  rw [relBaseRight_fSharpInverseImage (f' := smallEtaleRingedToposHom B S hS p)]
  exact Stacks.isFlatMapULift_iso_hom_comp _
    (isConservativeFamilyOfPoints_uliftEtaleSitePoint B S hS X.1 X.2) _ _
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS p).1 hp)

namespace CoherentSituation

attribute [local instance] pointTopology

variable {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

-- Scoped priority 10000: at default priority `thickeningLiftObstruction` fails to
-- elaborate.
/-- The small étale site of `X_{T'}`, read as the site of the base `(X_{T'}, f'⁻¹t_*𝒪_T)` of the
relative square of `D`, has sheaf composition with the forgetful functor of abelian groups. This is
`AlgebraicGeometry.Space.QuotientSituation.relBaseBottom_hasSheafCompose_forget` for the quotient
situation `AlgebraicGeometry.Space.CoherentSituation.relativeSquareSituation`, recorded at the
coherent situation because instance search does not reach that one through the abbreviation. -/
scoped instance (priority := 10000) relBaseBottom_hasSheafCompose_forget :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'))).J.HasSheafCompose
        (forget AddCommGrpCat.{u}) :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).HasSheafCompose
    (forget AddCommGrpCat.{u}))

-- Scoped priority 10000: at default priority `thickeningLiftObstruction` fails to
-- elaborate.
/-- Sheafification of abelian presheaves on the site of the base of the relative square of `D`;
see `AlgebraicGeometry.Space.CoherentSituation.relBaseBottom_hasSheafCompose_forget`. -/
scoped instance (priority := 10000) relBaseBottom_hasWeakSheafify :
    HasWeakSheafify (relBaseBottom
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'))).J
        AddCommGrpCat.{u} :=
  inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS (D.space T').1) AddCommGrpCat.{u})

-- Scoped priority 10000: at default priority `thickeningLiftObstruction` fails to
-- elaborate.
/-- Local bijectivity of the weak equivalences of abelian presheaves on the site of the base of the
relative square of `D`; see
`AlgebraicGeometry.Space.CoherentSituation.relBaseBottom_hasSheafCompose_forget`. -/
scoped instance (priority := 10000) relBaseBottom_wEqualsLocallyBijective :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.projection T'))).J.WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B S hS (D.space T').1).WEqualsLocallyBijective
    AddCommGrpCat.{u})

include hh in
/-- **`𝒢` is flat over the base of the relative square**: it is flat over `T`, which is flatness
over `f'⁻¹t_*𝒪_T` along `X_T ⟶ (X_{T'}, f'⁻¹t_*𝒪_T)`. -/
theorem isFlatOverBase_thickenedModule :
    IsFlatOverBase.{u, u + 1, u, u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareLeft h) (thickenedModule ξ h) := by
  have := ξ.quasicoherent
  exact (D.relativeSquareSituation.isFlatOver_iff_isFlatOverBase_relativeSquareLeft h hh ξ.F).1
    ξ.flat

variable (hfl : IsFlat B S hS (D.projection T').hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]

include hh hfl in
/-- **The obstruction to lifting `ξ` to `T'`**: the class `o(𝒢, f^*𝒥 ⊗ 𝒢, 1)` of Stacks 08MF in
`Ext²(𝒢, f^*𝒥 ⊗ 𝒢)`, for the action `I ⊗ 𝒢 ⟶ f^*𝒥 ⊗ 𝒢` which is the identity under the
identification `I = f^*𝒥` of Situation 08VV
(`Deformation.ToposThickening.basePullbackIdealTensorIso`); this is the class of Stacks 08VW,
part (1). -/
def thickeningLiftObstruction :=
  existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e}
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) (thickenedModule ξ h) _
    (basePullbackIdealTensorIso
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareThickening h)
      (D.relativeSquareSituation.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquare_comm h)
      (isFlat_relBaseRight_smallEtaleRingedToposHom _ hfl)
      (D.relativeSquareSituation.isStrict_relativeSquare h hh)
      (thickenedModule ξ h)).inv

include hh hfl in
/-- **The obstruction to lifting an object of `Coh_{X/Y}` across a first order thickening.** For
`X_{T'} ⟶ T'` flat, an object `ξ = (T, 𝒢)` of `Coh_{X/Y}` lifts across the first order
thickening `T ⊂ T'` exactly when its obstruction class in `Ext²(𝒢, f^*𝒥 ⊗ 𝒢)` vanishes: this is
Stacks 08VW, part (1), on the relative square, whose flat lifts are the lifts of `ξ`
(`AlgebraicGeometry.Space.CoherentSituation.nonempty_thickeningLift_iff`). -/
theorem nonempty_thickeningLift_iff_obstruction_eq_zero :
    Nonempty (D.ThickeningLift ξ h) ↔ thickeningLiftObstruction h hh hfl = 0 :=
  (nonempty_thickeningLift_iff h hh).trans
    ((hasFlatLift_iff_nonempty_flatLift
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
        (thickenedModule ξ h)).symm.trans
      (hasFlatLift_iff_basePullbackIdeal_obstruction_eq_zero.{u, u + 1, u, u, u + 1, u, u + 1, u,
          u, u + 1, u, e}
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
        (D.relativeSquareSituation.relativeSquareThickening h)
        (D.relativeSquareSituation.relativeSquareLeft h)
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
        (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
        (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
        (D.relativeSquareSituation.isStrict_relativeSquare h hh)
        (isFlat_relBaseRight_smallEtaleRingedToposHom _ hfl)
        (isFlatOverBase_thickenedModule h hh)))

end CoherentSituation

end AlgebraicGeometry.Space

end
