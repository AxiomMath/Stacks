module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.Defs
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Extending an open immersion from a dense open

Let `f : X ⟶ S` be a separated flat morphism of schemes, locally of finite type, and let
`U ⊆ S` be a retrocompact scheme-theoretically dense open subscheme. If `f` restricts to an
isomorphism over `U`, then `f` is an open immersion.

The criterion goes through the diagonal. Base changing the first projection of `X ×_S X` along
the inclusion of `U` gives a scheme-theoretically dominant morphism to `X ×_S X`, and it factors
through the diagonal because the two projections agree after the isomorphism over `U`; so the
diagonal, a closed immersion by separatedness, has trivial kernel and is an isomorphism. Hence
`f` is a monomorphism, and a flat monomorphism locally of finite presentation is an open
immersion.

The local finite presentation that criterion consumes is
`AlgebraicGeometry.locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`, proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen` and imported
above.

## Main results

* `AlgebraicGeometry.isOpenImmersion_of_isIso_morphismRestrict`: **Stacks 081M**, a separated
  flat morphism locally of finite type which is an isomorphism over a retrocompact
  scheme-theoretically dense open of the target is an open immersion.
* `AlgebraicGeometry.isFlatOver_unit_of_flat`: a flat morphism is flat over its target in the
  stalkwise sense of Tag 08KT, with the structure sheaf of the source as coefficients.

## Implementation notes

The inverse image of an open `U` of the target and the restricted morphism are Mathlib's
`AlgebraicGeometry.Scheme.Hom.morphismRestrict`, written `f ∣_ U`. Retrocompactness is stated
for the underlying subset, and scheme-theoretic density is
`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense`, which unfolds to scheme-theoretic
dominance of the inclusion of `U ∩ V` for every open `V`; the case `V = ⊤` gives dominance of
the inclusion of `U` itself.

## References

* [The Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
* [The Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-! ### Scheme-theoretic density and retrocompactness -/

/-- The inclusion of a scheme-theoretically dense open subscheme is scheme-theoretically
dominant. -/
private theorem isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense {S : Scheme.{u}}
    (U : S.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) :
    IsSchemeTheoreticallyDominant U.ι := by
  let topInclusion : (⊤ : S.Opens).toScheme ⟶ S := (⊤ : S.Opens).ι
  have : IsIso topInclusion := by change IsIso (Scheme.topIso S).hom; infer_instance
  have hq : IsSchemeTheoreticallyDominant ((⊤ : S.Opens).ι ⁻¹ᵁ U).ι := hU ⊤
  apply IsSchemeTheoreticallyDominant.mk
  rw [← Scheme.Hom.ker_comp_of_isIso (topInclusion.preimageIso U).hom U.ι,
    Scheme.Hom.preimageIso_hom_ι, Scheme.Hom.ker_comp, hq.ker_eq_bot,
    Scheme.IdealSheafData.map_bot]
  exact topInclusion.ker_eq_bot

/-- The inclusion of a retrocompact open subscheme is quasi-compact. -/
@[ega "IV 1.2.7" "partial"]
private theorem quasiCompact_ι_of_isRetrocompact {S : Scheme.{u}} (U : S.Opens)
    (hU : IsRetrocompact (U : Set S)) : QuasiCompact U.ι := by
  rw [quasiCompact_iff_isSpectralMap]
  show IsSpectralMap (Subtype.val : ↑U → S)
  exact IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hU

/-! ### Flatness over the target -/

/-- A flat morphism of schemes is flat over the target in the stalkwise sense of Tag 08KT, with
the structure sheaf of the source as coefficients. -/
public theorem isFlatOver_unit_of_flat {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] :
    IsFlatOver f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) :=
  fun x => (isFlatOverAt_unit_iff_isFlatAt f x).2 (Flat.stalkMap f x)


/-! ### Open immersions from a dense open -/

/-- A separated flat morphism which is an isomorphism over a retrocompact
scheme-theoretically dense open subscheme of the target is a monomorphism. -/
private theorem mono_of_isIso_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [Flat f] (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : Scheme.Opens.IsSchemeTheoreticallyDense U)
    [IsIso (f ∣_ U)] : Mono f := by
  have : IsSchemeTheoreticallyDominant U.ι :=
    isSchemeTheoreticallyDominant_of_isSchemeTheoreticallyDense U hUdense
  have : QuasiCompact U.ι := quasiCompact_ι_of_isRetrocompact U hUretro
  let selfProduct : Scheme := pullback f f
  let toBase : selfProduct ⟶ S := pullback.fst f f ≫ f
  let base : pullback toBase U.ι ⟶ selfProduct := pullback.fst toBase U.ι
  let toOpen : pullback toBase U.ι ⟶ U.toScheme := pullback.snd toBase U.ι
  let left : pullback toBase U.ι ⟶ X := base ≫ pullback.fst f f
  let right : pullback toBase U.ι ⟶ X := base ≫ pullback.snd f f
  let diag : X ⟶ selfProduct := pullback.diagonal f
  have : IsSchemeTheoreticallyDominant base := inferInstance
  have hleft : toOpen ≫ U.ι = left ≫ f := by
    dsimp [left, base, toOpen, toBase]
    rw [Category.assoc, ← pullback.condition (f := toBase) (g := U.ι)]
  have hright : toOpen ≫ U.ι = right ≫ f := by
    rw [hleft]; dsimp [left, right, base]
    rw [Category.assoc, pullback.condition (f := f) (g := f)]; simp only [Category.assoc]
  have hagree : left = right := by
    let restriction := isPullback_morphismRestrict f U
    have key (g : pullback toBase U.ι ⟶ X) (h : toOpen ≫ U.ι = g ≫ f) :
        g = toOpen ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι := by
      rw [← restriction.lift_snd toOpen g h, ← Category.assoc]
      congr 1
      rw [IsIso.eq_comp_inv, restriction.lift_fst]
    exact (key left hleft).trans (key right hright).symm
  have hfactor : base = left ≫ diag := by
    apply pullback.hom_ext <;> simp [left, right, diag, hagree]
  have : IsIso diag := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (bot_unique (by simpa only [← hfactor, IsSchemeTheoreticallyDominant.ker_eq_bot]
      using Scheme.Hom.le_ker_comp left diag))
  exact (pullback.isIso_diagonal_iff f).mp inferInstance

/-- **Stacks Project, Tag 081M.** A separated flat morphism locally of finite type which is an
isomorphism over a retrocompact scheme-theoretically dense open subscheme of the target is an
open immersion. -/
@[stacks 081M]
theorem isOpenImmersion_of_isIso_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [Flat f] (U : S.Opens) (hUretro : IsRetrocompact (U : Set S))
    (hUdense : Scheme.Opens.IsSchemeTheoreticallyDense U)
    [IsIso (f ∣_ U)] : IsOpenImmersion f := by
  have : LocallyOfFinitePresentation (f ∣_ U) := inferInstance
  have : LocallyOfFinitePresentation f :=
    FinitePresentationFromDenseOpen.locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open
      f U hUretro hUdense
  have : Mono f := mono_of_isIso_morphismRestrict f U hUretro hUdense
  exact IsOpenImmersion.of_flat_of_mono f

end AlgebraicGeometry

end
