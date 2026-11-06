module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleAffinePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocus

/-!
# Relative ampleness over the preimage of an open subspace of a stage

Let `f' : X' ⟶ Y'` and `fᵢ : Xᵢ ⟶ Yᵢ` be morphisms of algebraic spaces over a scheme `S` of a
big fppf site, with a commutative square `b ≫ fᵢ = f' ≫ a`, and suppose that the induced
morphism `X' ⟶ Y' ×_{Yᵢ} Xᵢ` is affine. If an invertible `𝒪_{Xᵢ}`-module `Lᵢ` is ample over a
subfunctor `Vᵢ` of `Yᵢ`, then `b^* Lᵢ` is ample over the preimage of `Vᵢ` in `Y'`. This is the
last step of the proof of Stacks 0D3D ("hints: use Morphisms, Lemma 0893 and the fact that
`X ⟶ Y ×_{Yᵢ} Xᵢ` is affine and ... Morphisms, Lemma 0892"), where `X' ⟶ Y'` is the limit of
the inverse system `Xᵢ ⟶ Yᵢ`.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmpleOver_preimage_of_isAffineHom_lift`: the statement
  above.
* `AlgebraicGeometry.Space.isAffineHom_lift_of_isAffineHom`: the induced morphism
  `X' ⟶ Y' ×_{Yᵢ} Xᵢ` is affine when `X' ⟶ Xᵢ` and `Y' ⟶ Yᵢ` are, as for the projections from a
  limit with affine transition morphisms to a stage.

## Implementation notes

For `g : Y'' ⟶ Y'` factoring through the preimage of `Vᵢ`, a base change `X''` of `f'` along `g`
maps to the base change `Z''` of `fᵢ` along `g ≫ a`; that morphism is a base change of the
affine morphism `X' ⟶ Y' ×_{Yᵢ} Xᵢ` (pasting), hence affine, and `Lᵢ` pulled back to `Z''` is
ample over `Y''` because `g ≫ a` factors through `Vᵢ`. Stacks 0892 for algebraic spaces,
`AlgebraicGeometry.Space.isRelativelyAmple_of_isAffineHom_of_comp_eq`, concludes.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_relativeAmpleStagePullback :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_relativeAmpleStagePullback
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Ampleness over the preimage of an open subspace of a stage.** Let `b ≫ fᵢ = f' ≫ a` be a
commutative square of algebraic spaces, `Z` a base change of `fᵢ` along `a`, and suppose that the
induced morphism `X' ⟶ Z` is affine. If the invertible `𝒪_{Xᵢ}`-module `Lᵢ` is ample over a
subfunctor `Vᵢ` of `Yᵢ`, then every `𝒪_{X'}`-module isomorphic to `b^* Lᵢ` is ample over the
preimage of `Vᵢ` along `a`. -/
theorem isRelativelyAmpleOver_preimage_of_isAffineHom_lift
    {X' Y' Xᵢ Yᵢ Z : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {fᵢ : Xᵢ ⟶ Yᵢ} {a : Y' ⟶ Yᵢ}
    {b : X' ⟶ Xᵢ} (hw : b ≫ fᵢ = f' ≫ a) {pZ : Z ⟶ Xᵢ} {fZ : Z ⟶ Y'}
    (hZ : IsPullback pZ fZ fᵢ a) (haff : IsAffineHom B S hS (hZ.lift b f' hw).hom)
    (Lᵢ : Modules.{u, u} B S hS Xᵢ.1 Xᵢ.2)
    (hLᵢ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Xᵢ.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Xᵢ.1 Xᵢ.2).O)).property Lᵢ)
    {L' : Modules.{u, u} B S hS X'.1 X'.2} (e : L' ≅ (modulePullback B S hS b).obj Lᵢ)
    {Vᵢ : Subfunctor Yᵢ.1} (hamp : IsRelativelyAmpleOver fᵢ Lᵢ Vᵢ) :
    IsRelativelyAmpleOver f' L' (Vᵢ.preimage a.hom) := by
  rintro X'' Y'' g p f'' hsq ⟨l, hl⟩
  let c : X' ⟶ Z := hZ.lift b f' hw
  have hcp : c ≫ pZ = b := hZ.lift_fst _ _ _
  have hcf : c ≫ fZ = f' := hZ.lift_snd _ _ _
  -- the base change of `fᵢ` along `g ≫ a`
  let Z'' : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS fZ g
  let pZ'' : Z'' ⟶ Z := ObjectProperty.homMk (pullback.fst fZ.hom g.hom)
  let fZ'' : Z'' ⟶ Y'' := ObjectProperty.homMk (pullback.snd fZ.hom g.hom)
  have hsqZ'' : IsPullback pZ'' fZ'' fZ g := AlgebraicSpaces.isPullback_fiberProduct B S hS fZ g
  have hsqᵢ : IsPullback (pZ'' ≫ pZ) fZ'' fᵢ (g ≫ a) := hsqZ''.paste_horiz hZ
  have hampZ := hamp (g ≫ a) (pZ'' ≫ pZ) fZ'' hsqᵢ
    ⟨l ≫ Vᵢ.fromPreimage a.hom, by
      rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, hl]; rfl⟩
  -- the morphism `X'' ⟶ Z''` is a base change of `c`, hence affine
  let h : X'' ⟶ Z'' := hsqZ''.lift (p ≫ c) f'' (by rw [Category.assoc, hcf]; exact hsq.w)
  have hhp : h ≫ pZ'' = p ≫ c := hsqZ''.lift_fst _ _ _
  have hhf : h ≫ fZ'' = f'' := hsqZ''.lift_snd _ _ _
  have hsqh : IsPullback p h c pZ'' := by
    refine IsPullback.of_bot ?_ hhp.symm hsqZ''
    rw [hhf, hcf]; exact hsq
  have hhaff : IsAffineHom B S hS h.hom :=
    isAffineHom_of_isPullback' B S hS (AlgebraicSpaces.isPullback_hom B S hS hsqh) haff
  -- Stacks 0892 for algebraic spaces
  have hLZ : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z''.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Z''.1 Z''.2).O)).property
      ((modulePullback B S hS (pZ'' ≫ pZ)).obj Lᵢ) :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS (pZ'' ≫ pZ)) (L := Lᵢ) (hL := hLᵢ)
  have hpb : p ≫ b = h ≫ pZ'' ≫ pZ := by
    rw [← Category.assoc, hhp, Category.assoc, hcp]
  refine isRelativelyAmple_of_isAffineHom_of_comp_eq h fZ'' hhf hhaff _ hLZ hampZ ?_
  exact (modulePullback B S hS p).mapIso e ≪≫ (modulePullbackCompIso B S hS p b).app Lᵢ ≪≫
    eqToIso (by rw [hpb]) ≪≫ ((modulePullbackCompIso B S hS h (pZ'' ≫ pZ)).app Lᵢ).symm

/-- **The lift into a base change of two affine morphisms is affine.** If `b : X' ⟶ Xᵢ` and
`a : Y' ⟶ Yᵢ` are affine and `b ≫ fᵢ = f' ≫ a`, then the induced morphism `X' ⟶ Z` into a base
change `Z` of `fᵢ` along `a` is affine: composed with the projection `Z ⟶ Xᵢ`, a base change of
`a` and so separated, it is `b` (Stacks 08GB, part (2)). -/
theorem isAffineHom_lift_of_isAffineHom
    {X' Y' Xᵢ Yᵢ Z : AlgebraicSpaces B S hS} {f' : X' ⟶ Y'} {fᵢ : Xᵢ ⟶ Yᵢ} {a : Y' ⟶ Yᵢ}
    {b : X' ⟶ Xᵢ} (hw : b ≫ fᵢ = f' ≫ a) {pZ : Z ⟶ Xᵢ} {fZ : Z ⟶ Y'}
    (hZ : IsPullback pZ fZ fᵢ a) (hb : IsAffineHom B S hS b.hom)
    (ha : IsAffineHom B S hS a.hom) :
    IsAffineHom B S hS (hZ.lift b f' hw).hom := by
  have hpZ : IsAffineHom B S hS pZ.hom :=
    isAffineHom_of_isPullback' B S hS (AlgebraicSpaces.isPullback_hom B S hS hZ.flip) ha
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS _ pZ.hom ?_
    (isSeparated_of_isAffineHom B S hS pZ.hom Z.2 Xᵢ.2 hpZ)
  have h : (hZ.lift b f' hw).hom ≫ pZ.hom = b.hom :=
    congrArg (fun k => k.hom) (hZ.lift_fst b f' hw)
  rw [h]; exact hb

end AlgebraicGeometry.Space

end
