module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineOpenKernel
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSourceCocycle
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeComp

/-!
# The cocycle condition of the kernels of the affine opens, read on the inverse images

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with the diagonal of `X` over
`R` affine, and let `F : QCoh(O_X) ⥤ QCoh(O_Y)` be `R`-linear, right exact and commuting with
arbitrary direct sums.  To every affine open `U` of `X` is attached a quasi-coherent kernel `K_U`
on `U ×_R Y` (`AlgebraicGeometry.openKernel`), together with an identification of the inverse
image of `K_U` along the chart map of a smaller affine open `U' ≤ U` with `K_{U'}`
(`AlgebraicGeometry.openKernelRestrictIso`), read as an identification of the *restriction* of
`K_U` along the chart map (`AlgebraicGeometry.openKernelRestrictSigma`).

This file proves the compatibility of those identifications along a chain `U'' ≤ U' ≤ U`:

* on the kernels themselves -- `AlgebraicGeometry.affineSourceKernelRestrictIso_trans`, which is
  the cocycle condition `AlgebraicGeometry.affineSourceKernelSourceChangeIso_comp` of Tag 0FZF
  with the three composites presented as given morphisms, and
  `AlgebraicGeometry.openKernelRestrictIso_trans`, its instance at the inclusions of the affine
  opens of `X`;
* on the underlying sheaves of modules --
  `AlgebraicGeometry.pullbackCompIsoOfEq_sourceChangeKernel`, which translates such a cocycle
  condition into the cocycle condition on the inverse images.

## Main definitions

* `AlgebraicGeometry.affineSourceKernelRestrictIso`: Tag 0FZF for the kernels with affine
  source, with the composite presented as a given morphism.
* `AlgebraicGeometry.openKernelRestrictRho`: the identification
  `AlgebraicGeometry.openKernelRestrictIso` with its type written out on the inverse image of
  the sheaf of modules.

## Main results

* `AlgebraicGeometry.map_sourceChangeKernelCompIso_hom` and
  `AlgebraicGeometry.map_sourceChangeKernelMap_ι`: the comparison of the two iterated inverse
  images of a kernel, and the inverse image of a morphism of kernels, read on the underlying
  sheaves of modules.
* `AlgebraicGeometry.affineSourceKernelRestrictIso_trans`: **the cocycle condition of the
  identifications of the kernels with affine source**, for a chain of three morphisms with
  affine source, with every composite presented as a given morphism.
* `AlgebraicGeometry.openKernelRestrictIso_trans`: the same at the inclusions of three nested
  affine opens of `X`.
* `AlgebraicGeometry.pullbackCompIsoOfEq_sourceChangeKernel`: **such a cocycle condition, read on
  the underlying sheaves of modules**.
* `AlgebraicGeometry.openKernelRestrictSigma_eq`: `openKernelRestrictSigma` is the comparison of
  the restriction with the inverse image followed by
  `AlgebraicGeometry.openKernelRestrictRho`.

## Implementation notes

`AlgebraicGeometry.pullbackCompIsoOfEq_sourceChangeKernel` takes the identifications twice: as
isomorphisms of quasi-coherent kernels (`ρ`, `ρ'`, `ρ''`) and as isomorphisms of the inverse
images of the underlying sheaves of modules (`σ`, `σ'`, `σ''`), together with the three equations
saying that the second family is the image of the first.  The two spellings are equal by
definition, but recognising this at a concrete kernel such as `openKernel R X Y F hF hU` is
expensive, so it is done once, with the kernels variables.

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] isOpenImmersion_over_comp_left

/-! ### Change of source, read on the underlying sheaves of modules -/

section SourceChange

variable (R : Type u) [CommRing R] (Y : Over (Spec (.of R)))

/-- **The comparison of the two iterated inverse images of a quasi-coherent kernel, read on the
underlying sheaves of modules.** -/
theorem map_sourceChangeKernelCompIso_hom {W V V' : Over (Spec (.of R))} (j : V ⟶ W)
    (j' : V' ⟶ V) (K : Scheme.QuasicoherentModules (pullback W.hom Y.hom)) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent
          (pullback V'.hom Y.hom).ringCatSheaf)).map
        (sourceChangeKernelCompIso R W V V' Y j j' K).hom =
      (pullbackCompIsoOfEq (sourceChangeMap R V V' Y j') (sourceChangeMap R W V Y j)
        (sourceChangeMap_comp R W V V' Y j j') K.obj).inv := rfl

/-- **The inverse image of a morphism of quasi-coherent kernels, read on the underlying sheaves
of modules.** -/
theorem map_sourceChangeKernelMap_ι {Z Z' : Over (Spec (.of R))} (a : Z' ⟶ Z)
    {K L : Scheme.QuasicoherentModules (pullback Z.hom Y.hom)} (φ : K ⟶ L) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent
          (pullback Z'.hom Y.hom).ringCatSheaf)).map (sourceChangeKernelMap R Z Z' Y a φ) =
      (Scheme.Modules.pullback (sourceChangeMap R Z Z' Y a)).map
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent
          (pullback Z.hom Y.hom).ringCatSheaf)).map φ) := rfl

/-- **The cocycle condition of a family of identifications of inverse images of quasi-coherent
kernels, read on the underlying sheaves of modules.**  The identifications are given twice --
as isomorphisms `ρ` of kernels and as isomorphisms `σ` of the inverse images of the underlying
sheaves, with `hσ` saying that the second family is the image of the first; if the `ρ` satisfy
the cocycle condition `hc`, then the `σ` satisfy the cocycle condition on the inverse images. -/
theorem pullbackCompIsoOfEq_sourceChangeKernel {W V V' : Over (Spec (.of R))} (j : V ⟶ W)
    (j' : V' ⟶ V) {m : V' ⟶ W} (hm : j' ≫ j = m)
    {K : Scheme.QuasicoherentModules (pullback W.hom Y.hom)}
    {L : Scheme.QuasicoherentModules (pullback V.hom Y.hom)}
    {N : Scheme.QuasicoherentModules (pullback V'.hom Y.hom)}
    (ρ : sourceChangeKernel R W V Y j K ≅ L) (ρ' : sourceChangeKernel R V V' Y j' L ≅ N)
    (ρ'' : sourceChangeKernel R W V' Y m K ≅ N)
    (σ : (Scheme.Modules.pullback (sourceChangeMap R W V Y j)).obj K.obj ≅ L.obj)
    (σ' : (Scheme.Modules.pullback (sourceChangeMap R V V' Y j')).obj L.obj ≅ N.obj)
    (σ'' : (Scheme.Modules.pullback (sourceChangeMap R W V' Y m)).obj K.obj ≅ N.obj)
    (hσ : σ.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V.hom Y.hom).ringCatSheaf)).map ρ.hom)
    (hσ' : σ'.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V'.hom Y.hom).ringCatSheaf)).map ρ'.hom)
    (hσ'' : σ''.hom = (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback V'.hom Y.hom).ringCatSheaf)).map ρ''.hom)
    (hk : sourceChangeMap R V V' Y j' ≫ sourceChangeMap R W V Y j =
      sourceChangeMap R W V' Y m)
    (hc : eqToHom (congrArg (fun q : V' ⟶ W ↦ sourceChangeKernel R W V' Y q K) hm.symm) ≫
        (sourceChangeKernelCompIso R W V V' Y j j' K).hom ≫
          sourceChangeKernelMap R V V' Y j' ρ.hom ≫ ρ'.hom = ρ''.hom) :
    (pullbackCompIsoOfEq (sourceChangeMap R V V' Y j') (sourceChangeMap R W V Y j) hk K.obj).hom ≫
        σ''.hom =
      (Scheme.Modules.pullback (sourceChangeMap R V V' Y j')).map σ.hom ≫ σ'.hom := by
  subst hm
  rw [eqToHom_refl, Category.id_comp] at hc
  have key := congrArg (fun φ : sourceChangeKernel R W V' Y (j' ≫ j) K ⟶ N ↦
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent
        (pullback V'.hom Y.hom).ringCatSheaf)).map φ) hc
  simp only [CategoryTheory.Functor.map_comp, map_sourceChangeKernelCompIso_hom,
    map_sourceChangeKernelMap_ι, ← hσ, ← hσ', ← hσ''] at key
  rw [hσ'', ← hσ'', ← key]
  exact Iso.hom_inv_id_assoc _ _

end SourceChange

/-! ### The cocycle condition of the kernels with affine source -/

section AffineSourceRestrict

attribute [local instance] isOpenImmersion_openSubOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- **Tag 0FZF for the kernels with affine source, with the composite presented as a given
morphism.**  This is `AlgebraicGeometry.affineSourceKernelSourceChangeIso` followed by the
transport identifying the kernel of `g ≫ f` with the kernel of the given `f'`. -/
def affineSourceKernelRestrictIso {X₁ X₂ : Over (Spec (.of R))} [IsAffine X₁.left]
    [IsAffine X₂.left] (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) {f' : X₂ ⟶ X} [IsOpenImmersion f.left]
    [IsOpenImmersion g.left] [IsOpenImmersion f'.left] (hf : g ≫ f = f') :
    sourceChangeKernel R X₁ X₂ Y g (affineSourceKernel R X Y F hF f) ≅
      affineSourceKernel R X Y F hF f' :=
  affineSourceKernelSourceChangeIso R X Y F hF f g ≪≫
    eqToIso (affineSourceKernel_congr R X Y F hF hf)

/-- **The cocycle condition of the identifications of the kernels with affine source.**  For a
chain `f : X₁ ⟶ X`, `g : X₂ ⟶ X₁`, `h : X₃ ⟶ X₂` of morphisms of schemes over `R` with `X₁`,
`X₂` and `X₃` affine, changing the source along `h ≫ g` in one step agrees with changing it
along `g` and then along `h`. -/
theorem affineSourceKernelRestrictIso_trans {X₁ X₂ X₃ : Over (Spec (.of R))} [IsAffine X₁.left]
    [IsAffine X₂.left] [IsAffine X₃.left] (f : X₁ ⟶ X) (g : X₂ ⟶ X₁) (h : X₃ ⟶ X₂)
    {f' : X₂ ⟶ X} {f'' : X₃ ⟶ X} {m : X₃ ⟶ X₁} [IsOpenImmersion f.left]
    [IsOpenImmersion g.left] [IsOpenImmersion h.left] [IsOpenImmersion f'.left]
    [IsOpenImmersion f''.left] [IsOpenImmersion m.left] (hf : g ≫ f = f')
    (hf' : h ≫ f' = f'') (hm : h ≫ g = m) (hm' : m ≫ f = f'') :
    eqToHom (congrArg (fun n : X₃ ⟶ X₁ ↦
          sourceChangeKernel R X₁ X₃ Y n (affineSourceKernel R X Y F hF f)) hm.symm) ≫
        (sourceChangeKernelCompIso R X₁ X₂ X₃ Y g h (affineSourceKernel R X Y F hF f)).hom ≫
          sourceChangeKernelMap R X₂ X₃ Y h
              (affineSourceKernelRestrictIso R X Y F hF f g hf).hom ≫
            (affineSourceKernelRestrictIso R X Y F hF f' h hf').hom =
      (affineSourceKernelRestrictIso R X Y F hF f m hm').hom := by
  subst hf hf' hm
  simp only [affineSourceKernelRestrictIso, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.comp_id, Category.id_comp]
  exact (affineSourceKernelSourceChangeIso_comp R X Y F hF f g h).symm

/-- **The cocycle condition of the kernels of the affine opens of `X`**, for a chain
`U'' ≤ U' ≤ U` of affine opens:  the identification of the inverse image of `K_U` with `K_{U''}`
does not depend on whether it is taken in one step or in two. -/
theorem openKernelRestrictIso_trans {U U' U'' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'') (hle : U' ≤ U) (hle' : U'' ≤ U') :
    eqToHom (congrArg (fun n : openSubOver R X U'' ⟶ openSubOver R X U ↦
          sourceChangeKernel R (openSubOver R X U) (openSubOver R X U'') Y n
            (openKernel R X Y F hF hU)) (openSubInclusionOver_trans R X hle hle').symm) ≫
        (sourceChangeKernelCompIso R (openSubOver R X U) (openSubOver R X U')
            (openSubOver R X U'') Y (openSubInclusionOver R X hle)
            (openSubInclusionOver R X hle') (openKernel R X Y F hF hU)).hom ≫
          sourceChangeKernelMap R (openSubOver R X U') (openSubOver R X U'') Y
              (openSubInclusionOver R X hle')
              (openKernelRestrictIso R X Y F hF hU hU' hle).hom ≫
            (openKernelRestrictIso R X Y F hF hU' hU'' hle').hom =
      (openKernelRestrictIso R X Y F hF hU hU'' (hle'.trans hle)).hom := by
  let : IsAffine (openSubOver R X U).left := hU
  let : IsAffine (openSubOver R X U').left := hU'
  let : IsAffine (openSubOver R X U'').left := hU''
  exact affineSourceKernelRestrictIso_trans R X Y F hF (openSubOverHom R X U)
    (openSubInclusionOver R X hle) (openSubInclusionOver R X hle')
    (openSubInclusionOver_comp R X hle) (openSubInclusionOver_comp R X hle')
    (openSubInclusionOver_trans R X hle hle') (openSubInclusionOver_comp R X (hle'.trans hle))

/-! ### The chart identification read on the inverse image -/

/-- `AlgebraicGeometry.openKernelRestrictIso` with its type written out on the inverse image of
the underlying sheaf of modules. -/
def openKernelRestrictRho {U U' : X.left.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hle : U' ≤ U) :
    (Scheme.Modules.pullback (openSubChartMap R X Y hle)).obj
        (openKernel R X Y F hF hU).obj ≅ (openKernel R X Y F hF hU').obj :=
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent
      (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).mapIso
    (openKernelRestrictIso R X Y F hF hU hU' hle)

/-- The forward map of `AlgebraicGeometry.openKernelRestrictRho` is the forward map of
`AlgebraicGeometry.openKernelRestrictIso` on the underlying sheaves of modules. -/
theorem openKernelRestrictRho_hom {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    (openKernelRestrictRho R X Y F hF hU hU' hle).hom =
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent
        (pullback (openSubOver R X U').hom Y.hom).ringCatSheaf)).map
          (openKernelRestrictIso R X Y F hF hU hU' hle).hom := rfl

/-- **`AlgebraicGeometry.openKernelRestrictSigma` is the comparison of the restriction with the
inverse image, followed by `AlgebraicGeometry.openKernelRestrictRho`.** -/
theorem openKernelRestrictSigma_eq {U U' : X.left.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hle : U' ≤ U) :
    openKernelRestrictSigma R X Y F hF hU hU' hle =
      (Scheme.Modules.restrictFunctorIsoPullback (openSubChartMap R X Y hle)).app
          (openKernel R X Y F hF hU).obj ≪≫
        openKernelRestrictRho R X Y F hF hU hU' hle := rfl

end AffineSourceRestrict

end AlgebraicGeometry

end
