module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Relative ampleness pulls back along an affine morphism of algebraic spaces

Let `h : X ⟶ Z` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site,
let `π : Z ⟶ Y` be a morphism of algebraic spaces and let `M` be an invertible `𝒪_Z`-module
ample relative to `π` (Stacks 0D31). Then `h^* M` is ample relative to `h ≫ π`. This is the
algebraic-space form of [Stacks, Tag 0892], part (2), in its relative form, as the proof of
Stacks 0D3D uses it.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_comp_of_isAffineHom`: relative ampleness pulls back
  along an affine morphism into the source.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_isAffineHom_of_comp_eq`: the same for a
  morphism `f' : X ⟶ Y` written as `h ≫ π` and a module isomorphic to `h^* M`.

## Implementation notes

A cartesian square testing Stacks 0D31 for `h ≫ π` at a scheme `T` with corner `U` factors
through the scheme `W` representing `Z ×_Y T` (`π` is representable): the induced morphism
`U ⟶ W` is a morphism of schemes, whose square over `h` is cartesian by the pasting lemma, so it
is an affine morphism of schemes (Stacks 03WG, (2) implies (1), in the form
`AlgebraicGeometry.Space.presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace`). The scheme
form of Stacks 0892
(`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom`) then
applies, and the reading of `h^* M` on `U` is the pullback of the reading of `M` on `W` by
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`.

## References

* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0892 (2) for algebraic spaces, relative form.** Let `h : X ⟶ Z` be an affine
morphism of algebraic spaces and let `M` be an invertible `𝒪_Z`-module ample relative to
`π : Z ⟶ Y`. Then the pullback `h^* M` is ample relative to `h ≫ π`. -/
theorem isRelativelyAmple_comp_of_isAffineHom {X Z Y : AlgebraicSpaces B S hS} (h : X ⟶ Z)
    (π : Z ⟶ Y) (hh : IsAffineHom B S hS h.hom) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (hMinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).property M)
    (hM : IsRelativelyAmple B S hS π M) :
    IsRelativelyAmple B S hS (h ≫ π) ((modulePullback B S hS h).obj M) := by
  obtain ⟨hrep, haff⟩ := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.2 Z.2 hh
  refine ⟨MorphismProperty.comp_mem _ _ _ hrep hM.1, fun T U g p q hsq => ?_⟩
  -- the scheme `W` representing `Z ×_Y T`
  let W := hM.1.pullback g
  let pZ : yoneda.obj W ⟶ Z.1 := hM.1.fst g
  let qZ : W ⟶ T := hM.1.snd g
  have hsqZ : IsPullback pZ (yoneda.map qZ) π.hom g := hM.1.isPullback g
  -- the induced morphism `U ⟶ W`
  have hw : (p ≫ h.hom) ≫ π.hom = yoneda.map q ≫ g := by
    rw [Category.assoc]; exact hsq.w
  let ψ : yoneda.obj U ⟶ yoneda.obj W := hsqZ.lift (p ≫ h.hom) (yoneda.map q) hw
  let φ : U ⟶ W := yoneda.preimage ψ
  have hφ : yoneda.map φ = ψ := yoneda.map_preimage ψ
  have hφfst : yoneda.map φ ≫ pZ = p ≫ h.hom := by rw [hφ]; exact hsqZ.lift_fst _ _ _
  have hφsnd : yoneda.map φ ≫ yoneda.map qZ = yoneda.map q := by
    rw [hφ]; exact hsqZ.lift_snd _ _ _
  have hq : φ ≫ qZ = q := yoneda.map_injective (by rw [Functor.map_comp]; exact hφsnd)
  -- the square of `φ` over `h` is cartesian, so `φ` is affine
  have hbig : IsPullback p (yoneda.map φ ≫ yoneda.map qZ) (h.hom ≫ π.hom) g := by
    rw [hφsnd]; exact hsq
  have hsqφ : IsPullback p (yoneda.map φ) h.hom pZ := IsPullback.of_bot hbig hφfst.symm hsqZ
  have hφaff : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map φ) :=
    haff.property pZ p φ hsqφ
  -- ampleness on `W` and its pullback to `U`
  obtain ⟨hinvW, hampW⟩ := hM.2 T W g pZ qZ hsqZ
  have hampU := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    ((BigFppfOver.toScheme B S hS).map φ) ((BigFppfOver.toScheme B S hS).map qZ)
    (baseChangeModule B S hS M W pZ) hampW
  rw [← Functor.map_comp, hq] at hampU
  obtain ⟨e₀⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible M hMinv W U pZ φ
  let e : baseChangeModule B S hS ((modulePullback B S hS h).obj M) U p ≅
      pullbackModule ((BigFppfOver.toScheme B S hS).map φ) (baseChangeModule B S hS M W pZ) :=
    (baseChangeModuleCompIso B S hS h M U p).symm ≪≫ eqToIso (by rw [hφfst]) ≪≫ e₀
  have hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS h).obj M) U p) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  exact ⟨hinv, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp hampU⟩

/-- **Stacks 0892 (2) for algebraic spaces, for a factorization.** Let `f' : X ⟶ Y` factor as
`h ≫ π` with `h : X ⟶ Z` affine, let `M` be an invertible `𝒪_Z`-module ample relative to `π`, and
let `L` be an `𝒪_X`-module isomorphic to `h^* M`. Then `L` is ample relative to `f'`. -/
theorem isRelativelyAmple_of_isAffineHom_of_comp_eq {X Z Y : AlgebraicSpaces B S hS}
    {f' : X ⟶ Y} (h : X ⟶ Z) (π : Z ⟶ Y) (hfac : h ≫ π = f') (hh : IsAffineHom B S hS h.hom)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    (hMinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).property M)
    (hM : IsRelativelyAmple B S hS π M) {L : Modules.{u, u} B S hS X.1 X.2}
    (e : L ≅ (modulePullback B S hS h).obj M) :
    IsRelativelyAmple B S hS f' L := by
  subst hfac
  exact (isRelativelyAmple_congr _ e).mpr (isRelativelyAmple_comp_of_isAffineHom h π hh M hMinv hM)

end AlgebraicGeometry.Space

end
