module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyExactness
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of a blowup pushes forward to the structure sheaf of the base

Let `b : X' ⟶ X` be the blowing up of a normal integral Noetherian scheme `X` in a nonzero
quasi-coherent sheaf of ideals. Then

`b_*𝒪_{X'} = 𝒪_X`,

both as sheaves of rings and as sheaves of `𝒪_X`-modules. For `X = Spec A` the spectrum of a
regular local ring of dimension two and the centre its closed point this is part (4) of
[Stacks, Tag 0AGS] in degree `0`, in its sheaf form rather than its form on global sections.

## Main results

* `AlgebraicGeometry.isIso_toRingCatSheafHom_of_isIso_c` and
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_of_isIso_c`: a morphism of schemes with
  invertible structure map of sheaves of rings has `𝒪 ⟶ f_*𝒪` invertible as a map of modules.
* `AlgebraicGeometry.isIso_c_blowUpToBase_of_isNormal` and
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_of_isNormal`:
  `b_*𝒪_{X'} = 𝒪_X` for the blowing up of a normal integral Noetherian scheme in a nonzero ideal
  sheaf, for sheaves of rings and for sheaves of `𝒪_X`-modules.
* `AlgebraicGeometry.isIso_c_blowUpToBase_vanishingIdeal_singleton` and
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton`: the
  case of the blowing up of an integral regular Noetherian surface at a closed point.
* `AlgebraicGeometry.isIso_c_blowUpToBase_maximalIdeal` and
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_blowUpToBase_maximalIdeal`: part (4) of
  [Stacks, Tag 0AGS] in degree `0`, at sheaf level, for the blowing up of the spectrum of a
  regular local ring of dimension two in its maximal ideal.

## Implementation notes

Everything here is stated for `AlgebraicGeometry.blowUp`, the blowing up of a quasi-coherent
sheaf of ideals through a chosen Rees datum, and for its structure morphism
`AlgebraicGeometry.blowUpToBase`.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### From sheaves of rings to sheaves of modules -/

/-- A morphism of schemes whose structure map of sheaves of rings is invertible has invertible
structure map of sheaves of rings on the site of the target. -/
theorem isIso_toRingCatSheafHom_of_isIso_c {X Y : Scheme.{u}} (f : X ⟶ Y) (hc : IsIso f.c) :
    IsIso f.toRingCatSheafHom := by
  have hval : IsIso ((sheafToPresheaf _ RingCat.{u}).map f.toRingCatSheafHom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    have : IsIso (f.c.app U) := NatIso.isIso_app_of_isIso _ U
    exact inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat.{u}).map (f.c.app U)))
  exact (fullyFaithfulSheafToPresheaf _ RingCat.{u}).isIso_of_isIso_map _

/-- `𝒪_Y ⟶ f_*𝒪_X` is an isomorphism of `𝒪_Y`-modules as soon as `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` is an
isomorphism of sheaves of rings. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_c {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hc : IsIso f.c) :
    IsIso (C := Y.Modules)
      (_root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  have : IsIso (C := CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) RingCat.{u})
      f.toRingCatSheafHom := isIso_toRingCatSheafHom_of_isIso_c f hc
  exact Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit f.toRingCatSheafHom

/-! ### The blowing up of a normal integral Noetherian scheme -/

variable {X : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsNoetherian X]

/-- `b_*𝒪_{X'} = 𝒪_X` for the blowing up `b : X' ⟶ X` of a normal integral Noetherian scheme in a
nonzero quasi-coherent sheaf of ideals ([Stacks, Tag 0AY8]). -/
@[ega "III 4.3.12" "special case"]
theorem isIso_c_blowUpToBase_of_isNormal (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsIso (blowUpToBase I).c :=
  IsModification.isIso_c_of_isNormal_target
    (f := blowUpToBase I)
    ⟨isBirational_blowUpToBase I hI, inferInstance, isIntegral_blowUp I hI⟩

/-- `𝒪_X ⟶ b_*𝒪_{X'}` is an isomorphism of `𝒪_X`-modules for the blowing up `b : X' ⟶ X` of a
normal integral Noetherian scheme in a nonzero quasi-coherent sheaf of ideals. -/
@[ega "III 4.3.12" "special case"]
theorem isIso_unitToPushforwardObjUnit_blowUpToBase_of_isNormal (I : X.IdealSheafData)
    (hI : I ≠ ⊥) :
    IsIso (C := X.Modules) (_root_.SheafOfModules.unitToPushforwardObjUnit
      (blowUpToBase I).toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_of_isIso_c _ (isIso_c_blowUpToBase_of_isNormal I hI)

/-! ### The blowing up of a regular surface at a closed point -/

/-- `b_*𝒪_{X'} = 𝒪_X` for the blowing up `b : X' ⟶ X` of an integral regular Noetherian surface at
a closed point. -/
@[ega "III 4.3.12" "special case"]
theorem isIso_c_blowUpToBase_vanishingIdeal_singleton {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] (hreg : IsRegular X) (hdim : topologicalKrullDim X = 2) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsIso (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).c :=
  have := isNormal_of_isRegular X hreg
  isIso_c_blowUpToBase_of_isNormal _
    (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim x hx)

/-- `𝒪_X ⟶ b_*𝒪_{X'}` is an isomorphism of `𝒪_X`-modules for the blowing up of an integral regular
Noetherian surface at a closed point. -/
theorem isIso_unitToPushforwardObjUnit_blowUpToBase_vanishingIdeal_singleton {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] (hreg : IsRegular X) (hdim : topologicalKrullDim X = 2)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIso (C := X.Modules) (_root_.SheafOfModules.unitToPushforwardObjUnit
      (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_of_isIso_c _
    (isIso_c_blowUpToBase_vanishingIdeal_singleton hreg hdim x hx)

/-! ### The blowing up of a regular local surface in its maximal ideal -/

/-- For `(A, 𝔪)` a regular local ring with `ringKrullDim A = 2` and `b : X ⟶ Spec A` the blowing up
of `Spec A` in `𝔪`,

`b_*𝒪_X = 𝒪_{Spec A}`

as sheaves of rings. -/
theorem isIso_c_blowUpToBase_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    IsIso (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)))).c :=
  have := isNormalDomain_of_isRegularLocalRing A
  (isModification_blowUpToBase_maximalIdeal A hdim).isIso_c

/-- `𝒪_{Spec A} ⟶ b_*𝒪_X` is an isomorphism of `𝒪_{Spec A}`-modules for the blowing up of the
spectrum of a regular local ring of dimension two in its maximal ideal. -/
theorem isIso_unitToPushforwardObjUnit_blowUpToBase_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    IsIso (C := (Spec (CommRingCat.of A)).Modules)
      (_root_.SheafOfModules.unitToPushforwardObjUnit
        (blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))).toRingCatSheafHom) :=
  isIso_unitToPushforwardObjUnit_of_isIso_c _ (isIso_c_blowUpToBase_maximalIdeal A hdim)

end AlgebraicGeometry

end
