module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Relative ampleness under base change

Let `f : X ⟶ S` be a morphism of schemes, let `L` be an invertible `𝒪_X`-module which is ample
relative to `f`, and let `g : S' ⟶ S` be arbitrary. Writing `f' : X ×_S S' ⟶ S'` for the base
change of `f` and `L'` for the pullback of `L` to `X ×_S S'`, this file proves that `L'` is ample
relative to `f'` (Stacks Tag 0893).

## Main definitions

* `Stacks.RelativeAmpleBaseChange.chartMap`: the comparison morphism
  `f⁻¹U ×_U W' ⟶ X ×_S S'` for `U` an open of `S` and `W'` an open of `S'` with `g(W') ⊆ U`.
* `Stacks.RelativeAmpleBaseChange.chartIso`: the isomorphism `f⁻¹U ×_U W' ≅ f'⁻¹W'` it induces.
* `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`,
  `Stacks.RelativeAmpleBaseChange.pullbackModuleCongr`: pseudofunctoriality of the module pullback
  along a composite of morphisms of schemes, and its transport along an equality of morphisms.

## Main results

* `Stacks.RelativeAmpleBaseChange.isAffineHom_fst_chart`: over an affine open `U ⊆ S` and an
  affine open `W' ⊆ g⁻¹U`, the projection `f⁻¹U ×_U W' ⟶ f⁻¹U` is an affine morphism.
* `Stacks.RelativeAmpleBaseChange.isAmple_modulePullback_preimage_snd`: for `U ⊆ S` affine and
  `W' ⊆ g⁻¹U` affine, the restriction of `L'` to `f'⁻¹W'` is ample as soon as the restriction of
  `L` to `f⁻¹U` is.
* `Stacks.RelativeAmpleBaseChange.quasiCompact_snd`: the base change of a quasi-compact morphism
  is quasi-compact.
* `Stacks.RelativeAmpleBaseChange.exists_isAffineOpen_isAmple_modulePullback_preimage_snd`: every
  point of `S'` has an affine open neighbourhood over whose preimage `L'` is ample.
* `Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_of_forall_exists_affine`:
  `L'` is ample relative to `f'` whenever every affine open of `S'` lies over an affine open of
  `S`.
* `Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_of_isAffine`: `L'` is ample
  relative to `f'` when `S` is affine.
* `Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback`: `L'` is ample relative to
  `f'`, given `Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase`.
* `Stacks.RelativeAmpleBaseChange.isRelativelyAmple_modulePullback_unconditional`: `L'` is ample
  relative to `f'`.

## References

* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01SD](https://stacks.math.columbia.edu/tag/01SD)
* [Stacks Project, Tag 01SH](https://stacks.math.columbia.edu/tag/01SH)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [EGA II, Proposition 4.6.13 (iii)]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeAmpleBaseChange

/-! ### Pseudofunctoriality of the module pullback, for morphisms of schemes -/

/-- The isomorphism `(a ≫ b)^* L ≅ a^* (b^* L)` for morphisms of schemes, given by
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` on the underlying morphisms of ringed
spaces. -/
def pullbackModuleCompIso {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (L : C.Modules) :
    Stacks.AmpleLocallyClosed.pullbackModule (a ≫ b) L ≅
      Stacks.AmpleLocallyClosed.pullbackModule a
        (Stacks.AmpleLocallyClosed.pullbackModule b L) :=
  (Stacks.PullbackPseudofunctor.modulePullbackCompIso b.toLRSHom.toShHom
    a.toLRSHom.toShHom).app L

/-- The module pullback transported along an equality of morphisms of schemes. -/
def pullbackModuleCongr {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) (L : B.Modules) :
    Stacks.AmpleLocallyClosed.pullbackModule a L ≅
      Stacks.AmpleLocallyClosed.pullbackModule b L :=
  eqToIso (congrArg (fun m : A ⟶ B => Stacks.AmpleLocallyClosed.pullbackModule m L) h)

/-! ### The chart of a base change over an affine open of the base -/

section Chart

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {U : S.Opens} {W' : S'.Opens}
  (hle : W' ≤ g ⁻¹ᵁ U)

/-- The chart of the base change over `W'`: the fibre product of the restriction
`f⁻¹U ⟶ U` of `f` with the restriction `W' ⟶ U` of `g`. -/
abbrev chart : Scheme.{u} :=
  pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle)

/-- The comparison morphism `f⁻¹U ×_U W' ⟶ X ×_S S'` induced by the open immersions
`f⁻¹U ⟶ X`, `W' ⟶ S'` and `U ⟶ S`. -/
def chartMap : chart f g hle ⟶ pullback f g :=
  pullback.map _ _ f g (f ⁻¹ᵁ U).ι W'.ι U.ι
    (Scheme.Hom.resLE_comp_ι f le_rfl) (Scheme.Hom.resLE_comp_ι g hle)

/-- The comparison morphism is an open immersion. -/
instance isOpenImmersion_chartMap : IsOpenImmersion (chartMap f g hle) := by
  delta chartMap
  infer_instance

/-- The comparison morphism commutes with the first projections. -/
theorem chartMap_comp_fst :
    chartMap f g hle ≫ pullback.fst f g
      = pullback.fst (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle) ≫ (f ⁻¹ᵁ U).ι :=
  pullback.lift_fst _ _ _

/-- The comparison morphism commutes with the second projections. -/
theorem chartMap_comp_snd :
    chartMap f g hle ≫ pullback.snd f g
      = pullback.snd (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle) ≫ W'.ι :=
  pullback.lift_snd _ _ _

include hle in
/-- The preimage of `W'` under the second projection of the base change is contained in the
preimage of `f⁻¹U` under the first projection. -/
theorem preimage_snd_le_preimage_fst :
    pullback.snd f g ⁻¹ᵁ W' ≤ pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro z hz
  have h : f (pullback.fst f g z) = g (pullback.snd f g z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hmem : g (pullback.snd f g z) ∈ U := hle hz
  rwa [← h] at hmem

/-- The image of the comparison morphism is the preimage of `W'` under the second projection of
the base change. -/
theorem range_chartMap :
    Set.range (chartMap f g hle) = Set.range (pullback.snd f g ⁻¹ᵁ W').ι := by
  rw [Scheme.Opens.range_ι, chartMap, Scheme.Pullback.range_map, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι]
  exact Set.inter_eq_right.mpr fun z hz => preimage_snd_le_preimage_fst f g hle hz

/-- The chart is isomorphic to the open subscheme `f'⁻¹W'` of the base change. -/
def chartIso : chart f g hle ≅ (pullback.snd f g ⁻¹ᵁ W').toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartMap f g hle) (pullback.snd f g ⁻¹ᵁ W').ι
    (range_chartMap f g hle)

/-- The identification of the chart with `f'⁻¹W'` is a factorisation of the comparison
morphism. -/
theorem chartIso_hom_comp_ι :
    (chartIso f g hle).hom ≫ (pullback.snd f g ⁻¹ᵁ W').ι = chartMap f g hle :=
  IsOpenImmersion.isoOfRangeEq_hom_fac (chartMap f g hle) (pullback.snd f g ⁻¹ᵁ W').ι
    (range_chartMap f g hle)

/-- For `U` and `W'` affine, the projection of the chart onto `f⁻¹U` is an affine morphism. -/
theorem isAffineHom_fst_chart (hU : IsAffineOpen U) (hW' : IsAffineOpen W') :
    IsAffineHom (pullback.fst (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle)) := by
  have hUa : IsAffine U.toScheme := hU
  have hW'a : IsAffine W'.toScheme := hW'
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip inferInstance

end Chart

/-! ### The local half of Stacks Tag 0893 -/

section Local

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules)
  [IsInvertibleModule X L] {U : S.Opens} {W' : S'.Opens} (hle : W' ≤ g ⁻¹ᵁ U)

/-- The isomorphism between the pullback to the chart of the restriction of `L` to `f⁻¹U` and
the pullback along `chartIso` of the restriction of `L'` to `f'⁻¹W'`. -/
def chartModuleIso :
    Stacks.AmpleLocallyClosed.pullbackModule
        (pullback.fst (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle))
        (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ U).ι L) ≅
      Stacks.AmpleLocallyClosed.pullbackModule (chartIso f g hle).hom
        (Stacks.AmpleLocallyClosed.pullbackModule (pullback.snd f g ⁻¹ᵁ W').ι
          (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L)) :=
  (pullbackModuleCompIso (pullback.fst (f.resLE U (f ⁻¹ᵁ U) le_rfl) (g.resLE U W' hle))
      (f ⁻¹ᵁ U).ι L).symm ≪≫
    pullbackModuleCongr (by
      rw [← chartMap_comp_fst f g hle, ← chartIso_hom_comp_ι f g hle, Category.assoc]) L ≪≫
    pullbackModuleCompIso (chartIso f g hle).hom
      ((pullback.snd f g ⁻¹ᵁ W').ι ≫ pullback.fst f g) L ≪≫
    (modulePullback (chartIso f g hle).hom.toLRSHom.toShHom).mapIso
      (pullbackModuleCompIso (pullback.snd f g ⁻¹ᵁ W').ι (pullback.fst f g) L)

include hle in
/-- For `U ⊆ S` an affine open and `W' ⊆ g⁻¹U` an affine open of `S'`, the restriction of the
pulled-back module `L'` to `f'⁻¹W'` is ample as soon as the restriction of `L` to `f⁻¹U` is. -/
theorem isAmple_modulePullback_preimage_snd (hU : IsAffineOpen U) (hW' : IsAffineOpen W')
    (hA : IsAmple (f ⁻¹ᵁ U).toScheme (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ U).ι L)) :
    IsAmple (pullback.snd f g ⁻¹ᵁ W').toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (pullback.snd f g ⁻¹ᵁ W').ι
        (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L)) := by
  have := isAffineHom_fst_chart f g hle hU hW'
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback (chartIso f g hle).hom _
    ((Stacks.RelativeVeryAmple.isAmple_congr _ _ (chartModuleIso f g L hle)).mp
      (Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _ hA))

end Local

/-! ### Stacks Tag 0893 -/

section BaseChange

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules)
  [IsInvertibleModule X L]

/-- The base change of a quasi-compact morphism is quasi-compact. -/
theorem quasiCompact_snd (hf : QuasiCompact f) : QuasiCompact (pullback.snd f g) := by
  infer_instance

/-- Every point of `S'` has an affine open neighbourhood `W'` over whose preimage the
pulled-back module is ample. -/
theorem exists_isAffineOpen_isAmple_modulePullback_preimage_snd
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (s' : S') :
    ∃ W' : S'.Opens, IsAffineOpen W' ∧ s' ∈ W' ∧
      IsAmple (pullback.snd f g ⁻¹ᵁ W').toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule (pullback.snd f g ⁻¹ᵁ W').ι
          (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L)) := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hgs', -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base s')) isOpen_univ
  obtain ⟨-, ⟨W', hW', rfl⟩, hs'W', hW'U⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (a := s') hgs' (g ⁻¹ᵁ U).isOpen
  exact ⟨W', hW', hs'W',
    isAmple_modulePullback_preimage_snd f g L hW'U hU hW' (hL.2 U hU)⟩

/-- If every affine open of `S'` lies over an affine open of `S` and `L` is ample relative to
`f`, then the pullback of `L` to `X ×_S S'` is ample relative to the base change
`X ×_S S' ⟶ S'`. -/
theorem isRelativelyAmple_modulePullback_of_forall_exists_affine
    (hga : ∀ V' : S'.Opens, IsAffineOpen V' → ∃ U : S.Opens, IsAffineOpen U ∧ V' ≤ g ⁻¹ᵁ U)
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.snd f g)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L) := by
  refine ⟨quasiCompact_snd f g hL.quasiCompact, fun V' hV' => ?_⟩
  obtain ⟨U, hU, hV'U⟩ := hga V' hV'
  exact isAmple_modulePullback_preimage_snd f g L hV'U hU hV' (hL.2 U hU)

/-- For `S` affine, if `L` is ample relative to `f`, then the pullback of `L` to `X ×_S S'` is
ample relative to the base change `X ×_S S' ⟶ S'`. -/
theorem isRelativelyAmple_modulePullback_of_isAffine [IsAffine S]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.snd f g)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L) :=
  isRelativelyAmple_modulePullback_of_forall_exists_affine f g L
    (fun _ _ => ⟨⊤, isAffineOpen_top S, le_top⟩) hL

/-- Assuming `Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase`, if `L` is ample
relative to `f : X ⟶ S`, then its pullback to `X ×_S S'` is ample relative to the base change
`X ×_S S' ⟶ S'`, for any `g : S' ⟶ S`. -/
theorem isRelativelyAmple_modulePullback
    (h01VJ : Stacks.RelativeAmpleComposition.RelativeAmpleLocalOnBase.{u})
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.snd f g)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L) :=
  h01VJ _ _ _ _ inferInstance (quasiCompact_snd f g hL.quasiCompact)
    (exists_isAffineOpen_isAmple_modulePullback_preimage_snd f g L hL)

/-- If `L` is ample relative to `f : X ⟶ S`, then its pullback to `X ×_S S'` is ample relative
to the base change `X ×_S S' ⟶ S'`, for any `g : S' ⟶ S`. -/
@[stacks 0893]
theorem isRelativelyAmple_modulePullback_unconditional
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.snd f g)
      (Stacks.AmpleLocallyClosed.pullbackModule (pullback.fst f g) L) :=
  isRelativelyAmple_modulePullback f g L
    Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase hL

end BaseChange

end Stacks.RelativeAmpleBaseChange

end
