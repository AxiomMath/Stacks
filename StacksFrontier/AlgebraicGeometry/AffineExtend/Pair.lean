module

public import StacksFrontier.AlgebraicGeometry.AffineExtend.Basic

/-!
# The two-member step of the induction of Tag 01PF

The proof of [Stacks, Tag 01PF] reduces, by a recursion on the number of affine opens needed to
cover `X` together with the given quasi-compact open `U`, to the case `X = U ∪ V` with `V` affine;
that case is then reduced to the affine case by working on `V` and glueing along `U ∩ V`. This
file is that step: `exists_submodule_obj_eq_sup` extends a submodule given over `U` to one whose
restriction to `U ⊔ V` is quasi-coherent and of finite type and whose sections over the opens
inside `U` are unchanged.

## Main results

* `exists_submodule_obj_eq_sup`: **the two-member step.**
* `isQuasicoherent_restrictTo_of_le`, `isFiniteType_restrictTo_of_le`: the two properties of a
  concrete submodule over an open descend to a smaller open.
* `isQuasicoherent_restrictTo_restrictTo`, `isFiniteType_restrictTo_restrictTo`: restricting a
  concrete submodule to `V` and then to an open `W` of the open subscheme `V` is restricting it to
  the image open `V.ι ''ᵁ W`, for both properties.
* `coRestrict_obj_eq_of_obj_eq` and `coRestrict_obj_eq_of_restrictTo_eq`: **the agreement
  hypothesis of the glueing step, discharged from the conclusion of the affine case.** The second
  is the form the step uses: a piece on `V` that agrees with the given submodule over the opens of
  `V` inside `U` co-restricts to a submodule of `F` with the given sections over the opens of `X`
  inside `U ⊓ V`.

## The two topological hypotheses, and why they are hypotheses

`hcpt` and `hqcm` say that the open `V.ι ⁻¹ᵁ U` of the open subscheme `V` is quasi-compact, as a
subset and as a morphism. In [Stacks, Tag 01PF] these come from quasi-separatedness of `X`:
`U ∩ V` is the intersection of two quasi-compact opens, and `V.ι ⁻¹ᵁ U` is homeomorphic to it.
They are left as named hypotheses rather than derived because that derivation is pure topology
and is not what this step is about; the recursion that consumes this step carries
`[QuasiSeparatedSpace X]` and discharges them once.

Nothing else is assumed: `V` is an arbitrary affine open, `U` an arbitrary open, and `F` is only
quasi-coherent.

## Implementation notes

The nested-restriction comparison is `AlgebraicGeometry.Modules.restrictCompIso` along
`AlgebraicGeometry.Scheme.Hom.isoImage`, with
`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules` — which is `rfl` — doing
the rest: the `𝒪`-module of a twice-restricted concrete submodule *is* the twice-restricted module
of the submodule, so no comparison of submodules is needed, only one of modules. Likewise
`isQuasicoherent_restrictTo_of_le` is
`Stacks.AlgebraicGeometry.CoherentFinite.restrictLEIso` plus the instance that restriction along
an open immersion preserves each property.

`coRestrict_obj_eq_of_obj_eq` is where the asymmetry of the co-restriction is paid for. The
co-restriction imposes no condition away from the range of the immersion, so two pieces agreeing
over the opens below `W` give co-restrictions agreeing only over the opens below `V.ι ''ᵁ W` —
and that is exactly the range of opens the agreement hypothesis of
`Stacks.AlgebraicGeometry.SubmoduleGlueOpens.Agree` inspects, by
`Stacks.AlgebraicGeometry.SubmoduleAgree.agree_pair`.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** This is one step of the proof of
[Stacks, Tag 01PF] and not the lemma: the lemma asserts the extension over the *whole* of a
quasi-compact and quasi-separated `X`, and what is here extends over `U ⊔ V` for one affine `V`.
What remains of [Stacks, Tag 01PF] is the recursion: a finite family of affine opens `V₁, …, Vₙ`
with `U ⊔ ⨆ Vᵢ = ⊤` from quasi-compactness of `X`, and the iteration of this step along it, with
the two topological hypotheses discharged from `[QuasiSeparatedSpace X]` at each stage.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01PFAffineExtend

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict
open Stacks.AlgebraicGeometry.SubmoduleGlueOpens Stacks.AlgebraicGeometry.SubmoduleAgree
open Stacks.AlgebraicGeometry.SubmoduleRelativeLocality

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### The two properties descend to a smaller open -/

/-- **Quasi-coherence over an open descends to a smaller open.** -/
theorem isQuasicoherent_restrict_of_le (M : X.Modules) {Z W : X.Opens} (h : Z ≤ W)
    (hqc : (Scheme.Modules.restrict M W.ι).IsQuasicoherent) :
    (Scheme.Modules.restrict M Z.ι).IsQuasicoherent :=
  have := hqc
  isQuasicoherent_of_iso (CoherentFinite.restrictLEIso M h).symm inferInstance

/-- **Finite type over an open descends to a smaller open.** -/
theorem isFiniteType_restrict_of_le (M : X.Modules) {Z W : X.Opens} (h : Z ≤ W)
    (hft : (Scheme.Modules.restrict M W.ι).IsFiniteType) :
    (Scheme.Modules.restrict M Z.ι).IsFiniteType :=
  AlgebraicGeometry.Modules.isFiniteType_of_iso (CoherentFinite.restrictLEIso M h).symm
    (AlgebraicGeometry.Modules.isFiniteType_restrict (X.homOfLE h) _ hft)

/-- `isQuasicoherent_restrict_of_le` for a concrete submodule. -/
theorem isQuasicoherent_restrictTo_of_le (N : F.Submodule) {Z W : X.Opens} (h : Z ≤ W)
    (hqc : ((restrictTo W.ι N).toSheafOfModules : W.toScheme.Modules).IsQuasicoherent) :
    ((restrictTo Z.ι N).toSheafOfModules : Z.toScheme.Modules).IsQuasicoherent := by
  rw [restrictTo_toSheafOfModules] at hqc ⊢
  exact isQuasicoherent_restrict_of_le _ h hqc

/-- `isFiniteType_restrict_of_le` for a concrete submodule. -/
theorem isFiniteType_restrictTo_of_le (N : F.Submodule) {Z W : X.Opens} (h : Z ≤ W)
    (hft : ((restrictTo W.ι N).toSheafOfModules : W.toScheme.Modules).IsFiniteType) :
    ((restrictTo Z.ι N).toSheafOfModules : Z.toScheme.Modules).IsFiniteType := by
  rw [restrictTo_toSheafOfModules] at hft ⊢
  exact isFiniteType_restrict_of_le _ h hft

/-! ### Restricting twice is restricting to the image open -/

/-- **Restricting to `V` and then to an open `W` of `V` is restricting to the image open**, for
the module of a concrete submodule. Both steps are
`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules`. -/
theorem toSheafOfModules_restrictTo_restrictTo (N : F.Submodule) (V : X.Opens)
    (W : V.toScheme.Opens) :
    ((restrictTo W.ι (restrictTo V.ι N)).toSheafOfModules : W.toScheme.Modules) =
      Scheme.Modules.restrict
        (Scheme.Modules.restrict (N.toSheafOfModules : X.Modules) V.ι) W.ι :=
  (restrictTo_toSheafOfModules W.ι (restrictTo V.ι N)).trans
    (congrArg (fun M : V.toScheme.Modules => Scheme.Modules.restrict M W.ι)
      (restrictTo_toSheafOfModules V.ι N))

/-- **Quasi-coherence over an open of the open subscheme `V` is quasi-coherence over the image
open.** -/
theorem isQuasicoherent_restrict_restrict (M : X.Modules) (V : X.Opens)
    (W : V.toScheme.Opens)
    (hqc : (Scheme.Modules.restrict M (V.ι ''ᵁ W).ι).IsQuasicoherent) :
    (Scheme.Modules.restrict (Scheme.Modules.restrict M V.ι) W.ι).IsQuasicoherent :=
  have := hqc
  isQuasicoherent_of_iso
    (AlgebraicGeometry.Modules.restrictCompIso M V.ι W.ι (V.ι ''ᵁ W).ι
      (V.ι.isoImage W).hom (Scheme.Hom.isoImage_hom_ι V.ι W).symm).symm inferInstance

/-- **Finite type over an open of the open subscheme `V` is finite type over the image open.** -/
theorem isFiniteType_restrict_restrict (M : X.Modules) (V : X.Opens)
    (W : V.toScheme.Opens)
    (hft : (Scheme.Modules.restrict M (V.ι ''ᵁ W).ι).IsFiniteType) :
    (Scheme.Modules.restrict (Scheme.Modules.restrict M V.ι) W.ι).IsFiniteType :=
  AlgebraicGeometry.Modules.isFiniteType_of_iso
    (AlgebraicGeometry.Modules.restrictCompIso M V.ι W.ι (V.ι ''ᵁ W).ι
      (V.ι.isoImage W).hom (Scheme.Hom.isoImage_hom_ι V.ι W).symm).symm
    (AlgebraicGeometry.Modules.isFiniteType_restrict (V.ι.isoImage W).hom _ hft)

/-- `isQuasicoherent_restrict_restrict` for a concrete submodule. -/
theorem isQuasicoherent_restrictTo_restrictTo (N : F.Submodule) (V : X.Opens)
    (W : V.toScheme.Opens)
    (hqc : ((restrictTo (V.ι ''ᵁ W).ι N).toSheafOfModules :
      (V.ι ''ᵁ W).toScheme.Modules).IsQuasicoherent) :
    ((restrictTo W.ι (restrictTo V.ι N)).toSheafOfModules :
      W.toScheme.Modules).IsQuasicoherent := by
  rw [toSheafOfModules_restrictTo_restrictTo]
  rw [restrictTo_toSheafOfModules] at hqc
  exact isQuasicoherent_restrict_restrict _ V W hqc

/-- `isFiniteType_restrict_restrict` for a concrete submodule. -/
theorem isFiniteType_restrictTo_restrictTo (N : F.Submodule) (V : X.Opens)
    (W : V.toScheme.Opens)
    (hft : ((restrictTo (V.ι ''ᵁ W).ι N).toSheafOfModules :
      (V.ι ''ᵁ W).toScheme.Modules).IsFiniteType) :
    ((restrictTo W.ι (restrictTo V.ι N)).toSheafOfModules : W.toScheme.Modules).IsFiniteType := by
  rw [toSheafOfModules_restrictTo_restrictTo]
  rw [restrictTo_toSheafOfModules] at hft
  exact isFiniteType_restrict_restrict _ V W hft

/-! ### The agreement hypothesis of the glueing step -/

/-- **Two pieces agreeing over the opens below `W` have co-restrictions agreeing over the opens
below the image of `W`.** -/
theorem coRestrict_obj_eq_of_obj_eq {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {P Q : (F.restrict f).Submodule} {W : Y.Opens}
    (h : ∀ V : Y.Opens, V ≤ W → P.obj (op V) = Q.obj (op V))
    {Z : X.Opens} (hZ : Z ≤ f ''ᵁ W) :
    (coRestrict f P).obj (op Z) = (coRestrict f Q).obj (op Z) := by
  refine SetLike.ext fun s =>
    (mem_coRestrict_iff f P s).trans (Iff.trans ?_ (mem_coRestrict_iff f Q s).symm)
  refine forall₂_congr fun V hV => ?_
  rw [h V ((f.image_le_image_iff V W).1 (hV.trans hZ))]

/-- **The agreement hypothesis, discharged from the conclusion of the affine case.** A piece `P`
on the open subscheme `V` whose restriction to an open `W` of `V` agrees with that of `N₀`
co-restricts to a submodule of `F` with the sections of `N₀` over every open of `X` inside both
`V` and the image of `W`. -/
theorem coRestrict_obj_eq_of_restrictTo_eq (V : X.Opens) (N₀ : F.Submodule)
    {P : (F.restrict V.ι).Submodule} {W : V.toScheme.Opens}
    (hP : restrictTo W.ι P = restrictTo W.ι (restrictTo V.ι N₀))
    {Z : X.Opens} (hZV : Z ≤ V) (hZW : Z ≤ V.ι ''ᵁ W) :
    (coRestrict V.ι P).obj (op Z) = N₀.obj (op Z) :=
  (coRestrict_obj_eq_of_obj_eq V.ι
    (fun _ hV => obj_eq_of_restrictTo_eq hP hV) hZW).trans
    (coRestrict_restrictTo_obj_of_le_opens V N₀ hZV)

/-! ### The two-member step -/

/-- **The two-member step of the induction of [Stacks, Tag 01PF].** Let `F` be a quasi-coherent
`𝒪_X`-module, `U` an open and `V` an affine open such that `V.ι ⁻¹ᵁ U` is quasi-compact. A
concrete submodule `N₀` of `F` whose restriction to `U` is quasi-coherent and of finite type
extends to a concrete submodule of `F` whose restriction to `U ⊔ V` is quasi-coherent and of
finite type, and whose sections over the opens inside `U` are those of `N₀`.

The piece over `V` is produced by `exists_isFiniteType_submodule_restrictTo_eq` applied on the
affine scheme `V`, carried back to `F` by
`Stacks.AlgebraicGeometry.SubmodulePrimitives.coRestrict`, and glued to `N₀` along the two-member
family `{U, V}`; `coRestrict_obj_eq_of_restrictTo_eq` discharges the agreement hypothesis of the
glueing from the prescription the affine case delivers over `V.ι ⁻¹ᵁ U`. -/
theorem exists_submodule_obj_eq_sup [F.IsQuasicoherent] (U V : X.Opens) (hV : IsAffineOpen V)
    (hcpt : IsCompact (((V.ι ⁻¹ᵁ U) : V.toScheme.Opens) : Set V.toScheme))
    (hqcm : QuasiCompact ((V.ι ⁻¹ᵁ U) : V.toScheme.Opens).ι)
    (N₀ : F.Submodule)
    (hqc : ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsQuasicoherent)
    (hft : ((restrictTo U.ι N₀).toSheafOfModules : U.toScheme.Modules).IsFiniteType) :
    ∃ N : F.Submodule,
      ((restrictTo (U ⊔ V).ι N).toSheafOfModules :
        (U ⊔ V).toScheme.Modules).IsQuasicoherent ∧
      ((restrictTo (U ⊔ V).ι N).toSheafOfModules : (U ⊔ V).toScheme.Modules).IsFiniteType ∧
      ∀ Z : X.Opens, Z ≤ U → N.obj (op Z) = N₀.obj (op Z) := by
  have : IsAffine V.toScheme := hV
  have himg : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = V ⊓ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, V.opensRange_ι]
  have hqc' : ((restrictTo ((V.ι ⁻¹ᵁ U) : V.toScheme.Opens).ι
      (restrictTo V.ι N₀)).toSheafOfModules : _).IsQuasicoherent := by
    refine isQuasicoherent_restrictTo_restrictTo N₀ V (V.ι ⁻¹ᵁ U) ?_
    rw [himg]
    exact isQuasicoherent_restrictTo_of_le N₀ inf_le_right hqc
  have hft' : ((restrictTo ((V.ι ⁻¹ᵁ U) : V.toScheme.Opens).ι
      (restrictTo V.ι N₀)).toSheafOfModules : _).IsFiniteType := by
    refine isFiniteType_restrictTo_restrictTo N₀ V (V.ι ⁻¹ᵁ U) ?_
    rw [himg]
    exact isFiniteType_restrictTo_of_le N₀ inf_le_right hft
  obtain ⟨P, hPqc, hPft, hPres⟩ :=
    exists_isFiniteType_submodule_restrictTo_eq (F := F.restrict V.ι) hcpt hqcm
      (restrictTo V.ι N₀) hqc' hft'
  have hagree : ∀ Z : X.Opens, Z ≤ U → Z ≤ V →
      N₀.obj (op Z) = (coRestrict V.ι P).obj (op Z) := by
    intro Z hZU hZV
    refine (coRestrict_obj_eq_of_restrictTo_eq V N₀ hPres hZV ?_).symm
    rw [himg]
    exact le_inf hZV hZU
  have hP₁qc : ((restrictTo V.ι (coRestrict V.ι P)).toSheafOfModules :
      V.toScheme.Modules).IsQuasicoherent := by
    rwa [restrictTo_coRestrict]
  have hP₁ft : ((restrictTo V.ι (coRestrict V.ι P)).toSheafOfModules :
      V.toScheme.Modules).IsFiniteType := by
    rwa [restrictTo_coRestrict]
  exact ⟨glue (pairOpens.{u} U V) (pairPieces.{u} N₀ (coRestrict V.ι P)),
    isQuasicoherent_glue_pair hagree hqc hP₁qc,
    isFiniteType_glue_pair hagree hft hP₁ft,
    fun _ hZ => obj_glue_pair_of_le_left hagree hZ⟩

end Stacks.AlgebraicGeometry.Tag01PFAffineExtend

end
