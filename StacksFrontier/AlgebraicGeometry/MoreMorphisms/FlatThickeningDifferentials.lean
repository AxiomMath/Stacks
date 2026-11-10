module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatThickeningActingGroup
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDiagonalSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionDifference
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeMiddleExact
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairConormalSequence
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalMap
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison

/-!
# Differentials of a flat deformation across a first-order thickening

Let `S ⊂ S'` be a first order thickening of schemes, let `f : X ⟶ S` be flat, let `f' : X' ⟶ S'`
be a morphism and let `i : X ⟶ X'` make the square
```
X  --i-->  X'
|          |
f          f'
↓          ↓
S  --t-->  S'
```
cartesian, so that `X = X' ×_{S'} S`.  This file proves that the conormal sequence of
[Stacks Project, Tag 01UZ] for `i` over `f'` degenerates: its first arrow
`𝒞_{X/X'} ⟶ i^*Ω_{X'/S'}` is **zero**, and therefore its second arrow exhibits
`i^*Ω_{X'/S'} ≅ Ω_{X/S'} ≅ Ω_{X/S}`.

Geometrically: the defining ideal of `X` in `X'` is pulled back from the base, so the universal
differential of `X'` over `S'` kills it, and `X ⊂ X'` contributes no differentials relative to
`S'`.  This is the degeneration that makes the group of [Stacks Project, Tag 0D14] act: the
difference of two lifts of `f` across `X ⊂ X'`, which a priori lives on `i^*Ω_{X'/S'}`, is the
same datum as a map out of `Ω_{X/S}`.

## Main results

* `Stacks.Thickenings.conormalDifferential_eq_zero_of_isPullback`: **the conormal differential of
  a flat deformation vanishes.** This is the only place the cartesian hypothesis is used, through
  the surjectivity clause of [Stacks Project, Tag 0473].
* `Stacks.Thickenings.isIso_relativeDifferentialsMap_of_eq` and
  `Stacks.Thickenings.isIso_relativeDifferentialsMapBase`: the canonical maps
  `i^*Ω_{X'/S'} ⟶ Ω_{X/S'}` and `i^*Ω_{X'/S'} ⟶ Ω_{X/S}` are isomorphisms.
* `Stacks.Thickenings.pullbackCotangentComparison`, with
  `Stacks.Thickenings.isIso_pullbackCotangentComparison` and
  `Stacks.Thickenings.pullbackCotangentComparison_pullbackD`: the isomorphism
  `(𝟙 X)^*Ω_{X/S'} ≅ Ω_{X/S}` and its generator formula.  This is the shape in which
  `Stacks.Thickenings.derivationActionGlobal` consumes a derivation, so the comparison is what
  lets a map out of `Ω_{X/S}` act on a lift.
* `Stacks.Thickenings.exists_conormalClass_eq`: **every section of the conormal sheaf of a
  first-order thickening is a conormal class.** The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` is injective on
  sections (`Stacks.Thickenings.injective_firstOrderImmersionConormalSheafι_val_app`) and a
  section of `𝒞_{X/X'}` lands in the defining ideal, so it is the class of its own image.
* `Stacks.Thickenings.conormalDifferential_conormalClass_eq_zero`: the conormal differential kills
  the class of a section whose universal differential vanishes, which is the generator formula the
  vanishing above is read off.

## Route for the vanishing

The first arrow is pinned down by its transpose
`Stacks.ConormalSequenceRight.conormalDifferentialTranspose`, so
`Stacks.Thickenings.kernelSubmoduleIso_hom_comp_conormalDifferential` reads that pinning on the
submodule presentation of the ideal sheaf — the presentation `Stacks.Conormal.conormalClass` uses
is the categorical kernel, and the two are matched by
`Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso`, i.e. by
`Stacks.AlgebraicGeometry.kernelSubmoduleIso`.  That gives the value of the first arrow on a
conormal class, and the value is the universal differential of the representing section.

Vanishing is then a morphism-level argument, not a sectionwise one: the canonical map
`f^*𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] is an epimorphism for a cartesian square
(`Stacks.Immersion.epi_immersionConormalSheafMap`), so it may be cancelled; transposing along
`f^* ⊣ f_*` reduces the claim to opens of `S`, every one of which is `t ⁻¹ᵁ U` because a
first-order thickening is a homeomorphism; and over such an open every section of `𝒞_{S/S'}` is
the conormal class of a section `a` of `𝒪_{S'}`, whose image in `𝒞_{X/X'}` is the class of
`(f')^♯ a`.  The universal differential of `(f')^♯ a` over `S'` vanishes because `a` comes from
the base, which is `Stacks.AlgebraicGeometry.AffineDifferentials.d_appLE_eq_zero`.

Flatness of `f'` is **not** used: cartesianness alone gives the epimorphism, and that is all the
vanishing needs.

## Partial coverage

**No `@[stacks]` attribute is placed by this file.**  Neither clause of
[Stacks Project, Tag 0D14] is proved here, and nothing here is a clause of
[Stacks Project, Tag 01UZ] beyond what
`StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic` already registers: Tag 01UZ's
labelled assertions are the two arrows, the complex, and exactness, and what is added here is the
vanishing of the first arrow under the extra hypothesis that the thickening is a flat base change,
which the source does not state.

What clause (2) of [Stacks Project, Tag 0D14] still needs, on top of this file, is the
identification of the set of automorphisms of `X'` over `S'` reducing to the identity on `X` with
`Hom_{𝒪_X}(Ω_{X/S}, 𝒞_{X/X'})`: the difference map of [Stacks Project, Tag 04FL] for the pair
`(𝟙 X', φ)` descended along the isomorphism this file provides, matched against the action of
[Stacks Project, Tag 02H5] through
`Stacks.Thickenings.pullbackCotangentComparison_pullbackD`.  The acting group itself is
`Stacks.Thickenings.flatThickeningActingGroupAddEquiv`.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Opposite

universe u w

namespace Stacks.Thickenings

open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.ConormalSequenceRight
open Stacks.ConormalSequenceUnramifiedPair (conormalSheafComparisonIso)

section Zero

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **The conormal differential, read on the submodule presentation of the ideal sheaf.** -/
theorem kernelSubmoduleIso_hom_comp_conormalDifferential :
    (Stacks.AlgebraicGeometry.kernelSubmoduleIso
          (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom ≫
        (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom) ≫
          (modulePushforward i.liftCoborder.toLRSHom.toShHom).map
            ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p) =
      conormalDifferentialTranspose i p := by
  refine Eq.trans ?_ ((conormalComparison_comp_map i (conormalDifferential i p)).symm.trans
    (conormalComparison_comp_conormalDifferential i p))
  refine Eq.trans ?_ (congrArg ((modulePullbackPushforwardAdjunction
      i.liftCoborder.toLRSHom.toShHom).homEquiv _ _)
    (Iso.hom_inv_id_assoc (conormalSheafComparisonIso i) (conormalDifferential i p)))
  exact (Adjunction.homEquiv_naturality_left _ _ _).symm

/-- The same identity read on a section of the defining ideal sheaf. -/
theorem conormalDifferential_unit_kernelSubmoduleIso
    (W₀ : (i.coborderRange.toScheme).Opens)
    (s : (definingIdeal i).toSheafOfModules.val.obj (op W₀)) :
    ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p).val.app
        (op (i.liftCoborder ⁻¹ᵁ W₀))
      (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app (op W₀)
        ((Stacks.AlgebraicGeometry.kernelSubmoduleIso
            (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom.val.app (op W₀) s)) =
      (conormalDifferentialTranspose i p).val.app (op W₀) s :=
  congr($(kernelSubmoduleIso_hom_comp_conormalDifferential i p).val.app (op W₀) s)

/-- **The conormal differential kills the class of a section whose differential vanishes.** -/
theorem conormalDifferential_conormalClass_eq_zero
    (U : X.Opens) {V : Z.Opens} (hV : V ≤ i ⁻¹ᵁ U) (r : Γ(X, U))
    (hr : (i.app U).hom r = 0)
    (hd : (Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
        ((i.coborderRange.ι.app U).hom r) = 0) :
    ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p).val.app (op V)
        (Stacks.Conormal.conormalClass i U hV r hr) = 0 := by
  have hinner : ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i p).val.app
        (op (i.liftCoborder ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ U)))
      (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom)).val.app
          (op (i.coborderRange.ι ⁻¹ᵁ U))
        (Stacks.Conormal.idealSectionOf i U r hr)) = 0 := by
    have hks : (Stacks.AlgebraicGeometry.kernelSubmoduleIso
          (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).hom.val.app
          (op (i.coborderRange.ι ⁻¹ᵁ U))
          (⟨(i.coborderRange.ι.app U).hom r,
            Stacks.Conormal.mem_ker_app_liftCoborder i U r hr⟩ :
              (definingIdeal i).toSheafOfModules.val.obj
                (op (i.coborderRange.ι ⁻¹ᵁ U))) =
        Stacks.Conormal.idealSectionOf i U r hr := by
      refine Stacks.Conormal.kernelι_inj i.liftCoborder (i.coborderRange.ι ⁻¹ᵁ U) ?_
      rw [Stacks.Conormal.kernelι_idealSectionOf]
      have hpin := congr($(Stacks.AlgebraicGeometry.kernelSubmoduleIso_hom_comp_ι
        (structureSheafModuleHom i.liftCoborder.toLRSHom.toShHom)).val.app
          (op (i.coborderRange.ι ⁻¹ᵁ U))
          (⟨(i.coborderRange.ι.app U).hom r,
            Stacks.Conormal.mem_ker_app_liftCoborder i U r hr⟩ :
              (definingIdeal i).toSheafOfModules.val.obj
                (op (i.coborderRange.ι ⁻¹ᵁ U))))
      exact hpin
    rw [← hks]
    refine Eq.trans (conormalDifferential_unit_kernelSubmoduleIso i p
      (i.coborderRange.ι ⁻¹ᵁ U) _) ?_
    refine Eq.trans (conormalDifferentialTranspose_val_app i p
      (op (i.coborderRange.ι ⁻¹ᵁ U)) _) ?_
    rw [hd]
    exact map_zero _
  rw [Stacks.Conormal.conormalClass_eq_unit]
  refine Eq.trans (AlgebraicGeometry.RingedSpace.val_app_naturality _
    (homOfLE (Stacks.Conormal.le_liftCoborder_preimage i U hV)) _) ?_
  rw [hinner]
  exact map_zero _

end Zero


section Pullback

variable {X X' S S' : Scheme.{u}}

/-- **Every section of the conormal sheaf of a first-order thickening is a conormal class.** -/
theorem exists_conormalClass_eq (i : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (U : X'.Opens)
    (z : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ U))) :
    ∃ (r : Γ(X', U)) (hr : (i.app U).hom r = 0),
      Stacks.Conormal.conormalClass i U (le_refl (i ⁻¹ᵁ U)) r hr = z := by
  refine ⟨(firstOrderImmersionConormalSheafι i hsq).val.app (op U) z,
    conormalSection_mem_ker hsq U z, ?_⟩
  refine injective_firstOrderImmersionConormalSheafι_val_app i hsq U ?_
  exact Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass i hsq U _ _



/-- **For a flat deformation the conormal differential of the thickening vanishes.** -/
theorem conormalDifferential_eq_zero_of_isPullback (i : X ⟶ X') (t : S ⟶ S')
    [IsImmersion i] [AlgebraicGeometry.IsClosedImmersion t] (f : X ⟶ S) (f' : X' ⟶ S')
    (hst : t.ker ^ 2 = ⊥) (sq : IsPullback i f f' t) :
    conormalDifferential i f' =
      (0 : (Scheme.Modules.pullback i.liftCoborder).obj ((definingIdeal i).toSheafOfModules) ⟶
        (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f')) := by
  have hC : ∀ U : S'.Opens, f ⁻¹ᵁ (t ⁻¹ᵁ U) ≤ i ⁻¹ᵁ (f' ⁻¹ᵁ U) := by
    intro U
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w]
  have hkey : (conormalSheafComparisonIso i).inv ≫ conormalDifferential i f' =
      (0 : (Scheme.Modules.pullback i.liftCoborder).obj
          (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom) ⟶
        (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f')) := by
    have := Stacks.Immersion.epi_immersionConormalSheafMap i t f f' sq
    refine zero_of_epi_comp (Stacks.Immersion.immersionConormalSheafMap i t f f'
      (Stacks.Immersion.toShHom_square sq.w)) ?_
    have hz : (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv
        (immersionConormalSheaf t)
        ((modulePullback i.toLRSHom.toShHom).obj (Scheme.Hom.relativeDifferentials f')) 0 = 0 := by
      rw [Adjunction.homEquiv_unit, modulePushforward_map_zero]
      exact Limits.comp_zero
    refine ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _).injective
      (Eq.trans ?_ hz.symm)
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun D =>
      ModuleCat.hom_ext (LinearMap.ext fun z => ?_))
    obtain ⟨D⟩ := D
    have hth := IsFirstOrderThickening.isThickening (i := t) ⟨inferInstance, hst⟩
    obtain ⟨U, rfl⟩ : ∃ U : S'.Opens, t ⁻¹ᵁ U = D :=
      ⟨hth.opensCongr D, hth.preimage_opensCongr D⟩
    obtain ⟨a, ha, rfl⟩ := exists_conormalClass_eq t hst U z
    have hd : (Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ f')).d
        ((i.coborderRange.ι.app (f' ⁻¹ᵁ U)).hom ((f'.app U).hom a)) = 0 := by
      have h0 := Stacks.AlgebraicGeometry.AffineDifferentials.d_appLE_eq_zero
        (i.coborderRange.ι ≫ f') _ (Scheme.Hom.universalRelativeDerivation
          (i.coborderRange.ι ≫ f')) U ((i.coborderRange.ι ≫ f') ⁻¹ᵁ U) le_rfl a
      rw [Scheme.Hom.appLE_eq_app] at h0
      exact h0
    change ((conormalSheafComparisonIso i).inv ≫ conormalDifferential i f').val.app
        (op (f ⁻¹ᵁ (t ⁻¹ᵁ U)))
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _
            (Stacks.Immersion.immersionConormalSheafMap i t f f'
              (Stacks.Immersion.toShHom_square sq.w))).val.app (op (t ⁻¹ᵁ U))
          (Stacks.Conormal.conormalClass t U (le_refl (t ⁻¹ᵁ U)) a ha)) = 0
    rw [Stacks.Conormal.conormalClass_immersionConormalSheafMap_app i t f f' sq.w U
      (t ⁻¹ᵁ U) (le_refl (t ⁻¹ᵁ U)) (hC U) a ha]
    exact conormalDifferential_conormalClass_eq_zero i f' (f' ⁻¹ᵁ U) (hC U) _ _ hd
  exact zero_of_epi_comp (conormalSheafComparisonIso i).inv hkey

/-- **The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` undoes a conormal class read over a smaller open.** -/
theorem conormalSection_conormalClass_of_le (i : X ⟶ X')
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (L V : X'.Opens)
    (hVL : V ≤ L) (r : Γ(X', L)) (hr : (i.app L).hom r = 0) :
    conormalSection hsq V (Stacks.Conormal.conormalClass i L (i.preimage_mono hVL) r hr) =
      (X'.presheaf.map (homOfLE hVL).op).hom r := by
  have h1 : Stacks.Conormal.conormalClass i L (i.preimage_mono hVL) r hr =
      ((modulePushforward i.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i)).val.map
        (homOfLE hVL).op (Stacks.Conormal.conormalClass i L (le_refl (i ⁻¹ᵁ L)) r hr) := by
    refine Eq.trans ?_ (Stacks.Conormal.modulePushforward_obj_val_map i
      (Stacks.Conormal.conormalSheaf i) hVL (i.preimage_mono hVL) _).symm
    exact (Stacks.Conormal.conormalClass_restrict_target i L (le_refl (i ⁻¹ᵁ L))
      (i.preimage_mono hVL) (i.preimage_mono hVL) r hr).symm
  rw [h1]
  refine Eq.trans (AlgebraicGeometry.RingedSpace.val_app_naturality
    (firstOrderImmersionConormalSheafι i hsq) (homOfLE hVL)
    (Stacks.Conormal.conormalClass i L (le_refl (i ⁻¹ᵁ L)) r hr)) ?_
  exact congrArg _
    (Stacks.Conormal.firstOrderImmersionConormalSheafι_conormalClass i hsq L r hr)

/-! ### The comparison of sheaves of differentials -/

/-- **The canonical map `i^*Ω_{X'/S'} ⟶ Ω_{X/S'}` of a flat deformation is invertible.**
The conormal sequence of `i` over `f'` is exact at its middle term and its first arrow
vanishes, so the second arrow is a monomorphism; it is always an epimorphism. -/
theorem isIso_relativeDifferentialsMap_of_eq (i : X ⟶ X') (t : S ⟶ S')
    [IsImmersion i] [AlgebraicGeometry.IsClosedImmersion t] (f : X ⟶ S) (f' : X' ⟶ S')
    (hst : t.ker ^ 2 = ⊥) (sq : IsPullback i f f' t) (q : X ⟶ S') (hq : q = i ≫ f')
    (hc : i ≫ f' = q ≫ 𝟙 S') :
    IsIso (Scheme.Hom.relativeDifferentialsMap i f' q (𝟙 S') hc) := by
  subst hq
  have : Mono (Scheme.Hom.relativeDifferentialsMap i f' (i ≫ f') (𝟙 S') hc) :=
    (conormalShortComplex_exact i f').mono_g
      (conormalDifferential_eq_zero_of_isPullback i t f f' hst sq)
  have := differentialsMapOver_epi i f'
  exact isIso_of_mono_of_epi _

/-- **`i^*Ω_{X'/S'} ≅ Ω_{X/S}` for a flat deformation.** The canonical map of the cartesian
square is the canonical map over `S'` followed by `Ω_{X/S'} ⟶ Ω_{X/S}`, and the latter is
invertible because `S ⊂ S'` is an immersion, hence formally unramified. -/
theorem isIso_relativeDifferentialsMapBase (i : X ⟶ X') (t : S ⟶ S')
    [IsImmersion i] [AlgebraicGeometry.IsClosedImmersion t] (f : X ⟶ S) (f' : X' ⟶ S')
    (hst : t.ker ^ 2 = ⊥) (sq : IsPullback i f f' t) :
    IsIso (Scheme.Hom.relativeDifferentialsMap i f' f t sq.w) := by
  have := isIso_relativeDifferentialsMap_of_eq i t f f' hst sq (f ≫ t) sq.w.symm
    (sq.w.trans (Category.comp_id (f ≫ t)).symm)
  have :=
    Stacks.ConormalSequenceUnramifiedPair.isIso_toRelativeDifferentials_of_formallyUnramified f t
  rw [← Scheme.Hom.relativeDifferentialsMap_comp_toRelativeDifferentials i f' f t sq.w]
  infer_instance

/-! ### The pulled-back cotangent sheaf of the thickened base -/

/-- **The comparison `(𝟙 X)^*Ω_{X/S'} ⟶ Ω_{X/S}`.** This is the datum
`Stacks.Thickenings.derivationActionGlobal` consumes, read as a map out of `Ω_{X/S}`. -/
def pullbackCotangentComparison (i : X ⟶ X') (t : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
    (hw : i ≫ f' = f ≫ t) :
    Stacks.Smooth.pullbackCotangentSheaf (i ≫ f') (𝟙 X) ⟶
      Scheme.Hom.relativeDifferentials f :=
  (Scheme.Modules.pullback (𝟙 X)).map (Scheme.Hom.cotangentSheafIso (i ≫ f')).inv ≫
    Scheme.Hom.relativeDifferentialsMap (𝟙 X) (i ≫ f') f t
      ((Category.id_comp (i ≫ f')).trans hw)

/-- The canonical map `(𝟙 X)^*Ω_{X/S'} ⟶ Ω_{X/S}` of the degenerate square is invertible when
`S ⊂ S'` is formally unramified: it is `Ω_{X/S'} ⟶ Ω_{X/S}` read through `pullbackId`. -/
theorem isIso_relativeDifferentialsMap_id (q : X ⟶ S') (f : X ⟶ S) (t : S ⟶ S')
    [IsImmersion t] (hq : q = f ≫ t) (hc : 𝟙 X ≫ q = f ≫ t) :
    IsIso (Scheme.Hom.relativeDifferentialsMap (𝟙 X) q f t hc) := by
  subst hq
  have :=
    Stacks.ConormalSequenceUnramifiedPair.isIso_toRelativeDifferentials_of_formallyUnramified f t
  have : IsIso ((Scheme.Modules.pullbackId X).inv.app
        (Scheme.Hom.relativeDifferentials (f ≫ t)) ≫
      Scheme.Hom.relativeDifferentialsMap (𝟙 X) (f ≫ t) f t hc) := by
    have hdef : Scheme.Hom.toRelativeDifferentials f t =
        (Scheme.Modules.pullbackId X).inv.app (Scheme.Hom.relativeDifferentials (f ≫ t)) ≫
          Scheme.Hom.relativeDifferentialsMap (𝟙 X) (f ≫ t) f t hc := rfl
    rw [← hdef]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullbackId X).inv.app (Scheme.Hom.relativeDifferentials (f ≫ t))) _

/-- `Stacks.Thickenings.pullbackCotangentComparison` is invertible. -/
theorem isIso_pullbackCotangentComparison (i : X ⟶ X') (t : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
    [IsImmersion t] (hw : i ≫ f' = f ≫ t) :
    IsIso (pullbackCotangentComparison i t f f' hw) := by
  have := isIso_relativeDifferentialsMap_id (i ≫ f') f t hw
    ((Category.id_comp (i ≫ f')).trans hw)
  change IsIso ((Scheme.Modules.pullback (𝟙 X)).map
      (Scheme.Hom.cotangentSheafIso (i ≫ f')).inv ≫
    Scheme.Hom.relativeDifferentialsMap (𝟙 X) (i ≫ f') f t
      ((Category.id_comp (i ≫ f')).trans hw))
  infer_instance

/-- **The comparison carries the pulled-back universal differential of `Ω_{X/S'}` to the
universal differential of `Ω_{X/S}`.** -/
theorem pullbackCotangentComparison_pullbackD (i : X ⟶ X') (t : S ⟶ S') (f : X ⟶ S)
    (f' : X' ⟶ S') (hw : i ≫ f' = f ≫ t) (W U : X.Opens) (hUW : U ≤ W) (x : Γ(X, W)) :
    (pullbackCotangentComparison i t f f' hw).val.app (op U)
        (Stacks.Smooth.pullbackD (i ≫ f') (𝟙 X) W hUW x) =
      (Scheme.Hom.relativeDifferentials f).val.map (homOfLE hUW).op
        (Scheme.Hom.universalRelativeDerivation f |>.d x) := by
  have hmor : (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
        (pullbackCotangentComparison i t f f' hw) =
      (Scheme.Hom.cotangentSheafIso (i ≫ f')).inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
          (Scheme.Hom.relativeDifferentialsMap (𝟙 X) (i ≫ f') f t
            ((Category.id_comp (i ≫ f')).trans hw)) :=
    Adjunction.homEquiv_naturality_left _ _ _
  have hd : (Scheme.Hom.cotangentSheafIso (i ≫ f')).inv.val.app (op W)
        (Stacks.Smooth.universalD (i ≫ f') W x) =
      (Scheme.Hom.universalRelativeDerivation (i ≫ f')).d x :=
    congrArg (fun D => D.d (X := op W) x)
      (Scheme.Hom.universalDerivation_postcomp_cotangentSheafIso_inv (i ≫ f'))
  have hW : (pullbackCotangentComparison i t f f' hw).val.app (op W)
        (Stacks.Smooth.pullbackCotangentUnitApp (i ≫ f') (𝟙 X) W
          (Stacks.Smooth.universalD (i ≫ f') W x)) =
      (Scheme.Hom.universalRelativeDerivation f).d x := by
    refine Eq.trans
      (congr($(hmor).val.app (op W) (Stacks.Smooth.universalD (i ≫ f') W x))) ?_
    refine Eq.trans (congrArg
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
        (Scheme.Hom.relativeDifferentialsMap (𝟙 X) (i ≫ f') f t
          ((Category.id_comp (i ≫ f')).trans hw))).val.app (op W)) hd) ?_
    exact Scheme.Hom.relativeDifferentialsMap_app_d t
      ((Category.id_comp (i ≫ f')).trans hw) W x
  refine Eq.trans (congrArg ((pullbackCotangentComparison i t f f' hw).val.app (op U))
    (Stacks.Smooth.pullbackD_apply (i ≫ f') (𝟙 X) W hUW x)) ?_
  refine Eq.trans (AlgebraicGeometry.RingedSpace.val_app_naturality
    (pullbackCotangentComparison i t f f' hw) (homOfLE hUW) _) ?_
  exact congrArg _ hW





end Pullback

end Stacks.Thickenings

end
