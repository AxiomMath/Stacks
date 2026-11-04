module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.SpecialFibreDirectImages
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionGlobal
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Japanese
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.FlatnessSpreadOut
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The `(S₂)` criterion for the direct images of the special fibre

Let `(R, 𝔪)` be a Noetherian local ring, `p : X ⟶ Spec R` locally of finite type, `Z ⊆ X` closed
and `U = X ∖ Z`, with special fibre `j₁ : U₁ ⟶ X₁` of the inclusion. The closing paragraph of
Stacks Remark 0EJV observes that if `X₁` is `(S₂)` and irreducible, `dim(X₁) - dim(Z) ≥ 3` and
`F₁` is a locally free `𝒪_{U₁}`-module, then `j₁,*F₁` and `R¹j₁,*F₁` are coherent, so that the
hypotheses of the algebraization statement
(`Stacks.Algebraization.isCompletionOfCoherent_of_flat_of_isCoherent`) hold; the identification of
those direct images with `j_*F₁` and `R¹j_*F₁` is
`Stacks.Algebraization.exists_specialFibre_directImage_iso`.

## Main results

* `Stacks.Algebraization.isCoherent_pushforward_and_rightDerived_one_of_hasPropertySk_two`: on an
  irreducible `(S₂)` scheme `Y` locally of finite type over a field, for an open immersion
  `j : V ⟶ Y` whose complement lies in a set `T` with `dim(T) + 3 ≤ dim(Y)` and a finite locally
  free `𝒪_V`-module `G`, the modules `j_*G` and `R¹j_*G` are coherent.
* `Stacks.Algebraization.isCoherent_specialFibre_directImages_of_hasPropertySk_two`: the closing
  paragraph of Stacks 0EJV.

## Implementation notes

The proof is Stacks 0BJY for `n = 2`
(`Stacks.LocalCohomologySequence.forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived`).
Its two standing hypotheses come from a dualizing complex on affine neighbourhoods
(`Stacks.Algebraization.hasDualizingComplexOnAffineCover_of_locallyOfFiniteType`): the scheme is
universally catenary and its formal fibres are `(S₂)`. For the depth condition at `x ∈ V` and
`z ∉ j(V)` specializing from `y = j(x)`, the transcendence degree `δ` of residue fields is a
dimension function, so `codim({z}‾, {y}‾) = δ(y) - δ(z)` (Stacks 02IA); `δ(z) = dim({z}‾) ≤ dim(T)`
and `dim(𝒪_{Y,y}) + δ(y) = dim(Y)` (Stacks 0A21); and `depth(G_x) ≥ depth(𝒪_{Y,y}) ≥
min(2, dim(𝒪_{Y,y}))`. If `dim(𝒪_{Y,y}) ≥ 2` the sum is at least `2 + 1`; otherwise it is at
least `dim(𝒪_{Y,y}) + δ(y) - δ(z) ≥ dim(Y) - dim(T) ≥ 3`.

The module `F₁` of Stacks is coherent, so "locally free" for it is finite local freeness, which is
the hypothesis `Scheme.Modules.IsFiniteLocallyFree`. The scheme `X₁` is the closed subscheme cut
out by `𝔪𝒪_X`, and `Z` is any closed subset of `X`; the source takes `Z ⊆ X₁`, and only
`Z ∩ X₁`, of dimension at most `dim(Z)`, matters.

## References

* [Stacks Project, Tag 0EJV](https://stacks.math.columbia.edu/tag/0EJV)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open TopologicalSpace.IrreducibleCloseds (closureSingleton)
open IrreducibleClosedsCodim (topCodim)
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)
open Stacks.LocalCohomologySequence
  (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- A scheme locally of finite type over a field has a dualizing complex on an affine
neighbourhood of every point. -/
theorem hasDualizingComplexOnAffineCover_of_locallyOfFiniteType (k : Type u) [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    HasDualizingComplexOnAffineCover Y := by
  intro y
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  refine ⟨⟨U, hU⟩, hyU, ?_⟩
  let : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra k Γ(Y, U) :=
    (Stacks.AlgebraicGeometry.UnitsNormalProper.structMapLE f U).toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.finiteType_structMapLE f ⟨U, hU⟩
  exact exists_isDualizingComplex_of_finiteType_field k Γ(Y, U)

/-- The arithmetic of the depth condition: with `a + δ(y) = D`, `dim(T) + 3 ≤ D`,
`δ(z) ≤ dim(T)`, `δ(z) < δ(y)` and `min(2, a) ≤ e`, one has `2 < e + (δ(y) - δ(z))`. -/
private lemma two_lt_add_toNat_sub {a D dZ : WithBot ℕ∞} {δy δz : ℕ} {e : ℕ∞}
    (hsum : a + (δy : WithBot ℕ∞) = D) (hdim : dZ + 3 ≤ D) (hz : (δz : WithBot ℕ∞) ≤ dZ)
    (hlt : δz < δy) (he : min 2 a ≤ (e : WithBot ℕ∞)) :
    ((2 : ℕ) : ℕ∞) < e + (((δy : ℤ) - δz).toNat : ℕ∞) := by
  rw [show ((δy : ℤ) - δz).toNat = δy - δz by omega]
  rcases le_or_gt 2 a with h2 | h2
  · rw [min_eq_left h2] at he
    have h1 : (1 : ℕ∞) ≤ ((δy - δz : ℕ) : ℕ∞) := by exact_mod_cast (by omega : 1 ≤ δy - δz)
    calc ((2 : ℕ) : ℕ∞) < 2 + 1 := by norm_num
      _ ≤ e + _ := add_le_add (WithBot.coe_le_coe.mp he) h1
  · rw [min_eq_right h2.le] at he
    cases a using WithBot.recBotCoe with
    | bot =>
      subst hsum
      rw [WithBot.bot_add, le_bot_iff, WithBot.add_eq_bot] at hdim
      rcases hdim with h | h
      · subst h
        exact absurd hz (by simp)
      · exact absurd h (by simp)
    | coe a =>
    cases a using ENat.recTopCoe with
    | top => exact absurd h2 (by simp)
    | coe m =>
    have hm : m < 2 := by
      have h2' : ((m : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ∞) : WithBot ℕ∞) := h2
      exact_mod_cast WithBot.coe_lt_coe.mp h2'
    have he' : (m : ℕ∞) ≤ e := WithBot.coe_le_coe.mp he
    have hle : (δz : WithBot ℕ∞) + 3 ≤ ((m + δy : ℕ) : WithBot ℕ∞) := by
      rw [← hsum] at hdim
      push_cast
      exact (add_le_add hz le_rfl).trans hdim
    have hle' : δz + 3 ≤ m + δy := by exact_mod_cast hle
    calc ((2 : ℕ) : ℕ∞) < ((m + (δy - δz) : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
      _ = (m : ℕ∞) + ((δy - δz : ℕ) : ℕ∞) := Nat.cast_add _ _
      _ ≤ e + _ := add_le_add he' le_rfl

/-- On a scheme locally of finite type over a field, the dimension of the closure of a point is
the transcendence degree of its residue field. -/
theorem dimClosureAt_eq_natTrdegResidueField (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : Y) :
    dimClosureAt Y y = ((natTrdegResidueField k Y f y : ℕ) : WithBot ℕ∞) := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have := residueField_finTrdeg k f y
  rw [dimClosureAt, topologicalKrullDim_closure_singleton_eq_trdeg k Y f y]
  congr 1
  exact Cardinal.toENat_eq_natCast.mpr
    (Cardinal.cast_toNat_of_lt_aleph0 (trdeg_lt_aleph0 k (Y.residueField y))).symm

/-- **The depth condition of Stacks 0BJY for `n = 2`.** Let `Y` be an irreducible `(S₂)` scheme
locally of finite type over a field, `j : V ⟶ Y` an open immersion whose complement lies in a set
`T` with `dim(T) + 3 ≤ dim(Y)`, and `G` a finite locally free `𝒪_V`-module. At every `x ∈ V` and
every `z ∉ j(V)` specializing from `j(x)`, `depth(G_x) + codim({z}‾, {j(x)}‾) > 2`. -/
theorem two_lt_depth_add_topCodim_of_hasPropertySk_two (k : Type u) [Field k]
    {Y V : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IrreducibleSpace Y] (j : V ⟶ Y) [IsOpenImmersion j] (hS₂ : HasPropertySk Y 2)
    (T : Set Y) (hT : (Set.range j.base)ᶜ ⊆ T)
    (hdim : topologicalKrullDim T + 3 ≤ topologicalKrullDim Y)
    (G : V.Modules) (hG : Scheme.Modules.IsFiniteLocallyFree G) (x : V) (z : Y)
    (hz : z ∉ Set.range j.base) (hzx : z ∈ closure ({j.base x} : Set Y)) :
    ((2 : ℕ) : ℕ∞) <
      Module.depth (V.presheaf.stalk x) (IsLocalRing.maximalIdeal (V.presheaf.stalk x))
          (G.presheaf.stalk x) +
        topCodim (closureSingleton z) (closureSingleton (j.base x)) := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion j
  have := (Scheme.Modules.isFiniteLocallyFree_iff G).mp hG
  have hyz : j.base x ⤳ z := specializes_iff_mem_closure.mpr hzx
  let δ := residueFieldTrdegDimensionFunction k Y f
  have hSober : StacksSober Y :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  rw [(isCatenarySpace_and_topCodim_eq_of_isDimensionFunction Y hSober δ
    δ.isDimensionFunctionForCatenary).2 _ _ hyz]
  have hlt : natTrdegResidueField k Y f z < natTrdegResidueField k Y f (j.base x) :=
    natTrdegResidueField_lt_of_specializes k Y f hyz fun h => hz ⟨x, h⟩
  have hsum := ringKrullDim_stalk_add_dimClosureAt k Y f (j.base x)
  rw [dimClosureAt_eq_natTrdegResidueField k f] at hsum
  have hclz : closure ({z} : Set Y) ⊆ T :=
    (closure_minimal (Set.singleton_subset_iff.mpr hz)
      j.isOpenEmbedding.isOpen_range.isClosed_compl).trans hT
  have hzT : ((natTrdegResidueField k Y f z : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim T := by
    rw [← dimClosureAt_eq_natTrdegResidueField k f, dimClosureAt]
    exact (Topology.IsEmbedding.inclusion hclz).isInducing.topologicalKrullDim_le
  have hdepth : Module.depth (Y.presheaf.stalk (j.base x))
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (j.base x))) (Y.presheaf.stalk (j.base x)) ≤
      Module.depth (V.presheaf.stalk x) (IsLocalRing.maximalIdeal (V.presheaf.stalk x))
        (G.presheaf.stalk x) := by
    rw [Module.depth_self_eq_of_ringEquiv
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv]
    exact depth_stalk_le_sheafDepthAt G x
  exact two_lt_add_toNat_sub hsum hdim hzT hlt
    ((hS₂ (j.base x)).trans (WithBot.coe_le_coe.mpr hdepth))

/-- **Direct images of a finite locally free module across a closed subset of codimension at
least three in an `(S₂)` scheme of finite type over a field.** Let `Y` be an irreducible `(S₂)`
scheme locally of finite type over a field and `j : V ⟶ Y` an open immersion whose complement
lies in a set `T` with `dim(T) + 3 ≤ dim(Y)`. For every finite locally free `𝒪_V`-module `G`,
`j_*G` and `R¹j_*G` are coherent.

This is Stacks 0BJY for `n = 2`: `Y` has a dualizing complex on an affine neighbourhood of each
point, so it is universally catenary and its formal fibres are `(S₂)`, and the depth condition is
`Stacks.Algebraization.two_lt_depth_add_topCodim_of_hasPropertySk_two`. -/
theorem isCoherent_pushforward_and_rightDerived_one_of_hasPropertySk_two (k : Type u) [Field k]
    {Y V : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    [IrreducibleSpace Y] (j : V ⟶ Y) [IsOpenImmersion j] (hS₂ : HasPropertySk Y 2)
    (T : Set Y) (hT : (Set.range j.base)ᶜ ⊆ T)
    (hdim : topologicalKrullDim T + 3 ≤ topologicalKrullDim Y)
    (G : V.Modules) (hG : Scheme.Modules.IsFiniteLocallyFree G) :
    ((Scheme.Modules.pushforward j).obj G).IsCoherent ∧
      (((Scheme.Modules.pushforward j).rightDerived 1).obj G).IsCoherent := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion j
  have := (Scheme.Modules.isFiniteLocallyFree_iff G).mp hG
  have : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree V G
  have hD := hasDualizingComplexOnAffineCover_of_locallyOfFiniteType k f
  have key := (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived j G 2
    (isUniversallyCatenary_of_hasDualizingComplexOnAffineCover Y hD)
    (fun z _ =>
      formalFibersHavePropertySk_stalk_of_hasDualizingComplexOnAffineCover Y hD z 2)).mp
    (fun x _ z hz hzx =>
      two_lt_depth_add_topCodim_of_hasPropertySk_two k f j hS₂ T hT hdim G hG x z hz hzx)
  have : (((Scheme.Modules.pushforward j).rightDerived 0).obj G).IsCoherent := key 0 two_pos
  exact ⟨isCoherent_of_iso
    ((Scheme.Modules.pushforward j).rightDerivedZeroIsoSelf.app G).symm, key 1 one_lt_two⟩

/-- A point of the special fibre `X₁` lying in `U` is in the image of the special fibre
`j₁ : U₁ ⟶ X₁` of `U ⊆ X`. -/
theorem mem_range_specialFibreMap {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)
    (y : I.subscheme) (hy : I.subschemeι.base y ∈ U) :
    y ∈ Set.range (specialFibreMap I U).base := by
  have hsupp : I.subschemeι.base y ∈ (I.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  let a : U.toScheme := ⟨I.subschemeι.base y, hy⟩
  have ha : a ∈ ((I.comap U.ι).support : Set U.toScheme) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hsupp
  rw [← Scheme.IdealSheafData.range_subschemeι] at ha
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, I.subschemeι.isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, specialFibreMap_subschemeι, Scheme.Hom.comp_apply, hc]
  rfl

/-- **Stacks 0EJV, the closing paragraph: the `(S₂)` criterion on the special fibre.** Let
`(R, 𝔪)` be a Noetherian local ring, `p : X ⟶ Spec R` locally of finite type, `Z ⊆ X` closed and
`U = X ∖ Z`. Write `X₁` and `U₁` for the special fibres and `j₁ : U₁ ⟶ X₁` for the special fibre
of the inclusion `U ⊆ X`. If `X₁` is `(S₂)` and irreducible, `dim(X₁) - dim(Z) ≥ 3`, and `G` is a
finite locally free `𝒪_{U₁}`-module, then `j₁,*G` and `R¹j₁,*G` are coherent.

The special fibre is locally of finite type over the residue field `R/𝔪`, being the base change
`X ×_{Spec R} Spec(R/𝔪)`
(`Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback`); `j₁` is an open immersion
whose image is `X₁ ∖ Z`; and the closed subset `X₁ ∩ Z` of `X₁` has dimension at most `dim(Z)`.
So `Stacks.Algebraization.isCoherent_pushforward_and_rightDerived_one_of_hasPropertySk_two`
applies. -/
@[stacks 0EJV "the closing paragraph: if X₁ is (S₂) and irreducible, dim(X₁) - dim(Z) ≥ 3 and \
F₁ is a locally free O_{U₁}-module, then j₁,*F₁ and R¹j₁,*F₁ are coherent"]
theorem isCoherent_specialFibre_directImages_of_hasPropertySk_two
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [LocallyOfFiniteType p]
    (Z : Closeds X) (U : X.Opens) (hU : (U : Set X) = (Z : Set X)ᶜ)
    [IrreducibleSpace (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subscheme]
    (hS₂ : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
      letI : IsLocallyNoetherian (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion
          (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subschemeι
      HasPropertySk (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subscheme 2)
    (hdim : topologicalKrullDim (Z : Set X) + 3 ≤
      topologicalKrullDim (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).subscheme)
    (G : ((baseIdealSheaf R (IsLocalRing.maximalIdeal R) p).comap U.ι).subscheme.Modules)
    (hG : Scheme.Modules.IsFiniteLocallyFree G) :
    ((Scheme.Modules.pushforward
        (specialFibreMap (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U)).obj G).IsCoherent ∧
      (((Scheme.Modules.pushforward
        (specialFibreMap (baseIdealSheaf R (IsLocalRing.maximalIdeal R) p) U)).rightDerived
          1).obj G).IsCoherent := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let I := baseIdealSheaf R (IsLocalRing.maximalIdeal R) p
  let : IsLocallyNoetherian I.subscheme := isLocallyNoetherian_of_isClosedImmersion I.subschemeι
  have : IsOpenImmersion (specialFibreMap I U) :=
    Stacks.AlgebraicGeometry.isOpenImmersion_subschemeMap_comap I U
  let κ := R ⧸ IsLocalRing.maximalIdeal R
  let : Field κ := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let f : I.subscheme ⟶ Spec (.of κ) :=
    (Stacks.PuncturedSpectrumPicard.baseIdealSubschemeIsoPullback R
        (IsLocalRing.maximalIdeal R) p).hom ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))))
  have : LocallyOfFiniteType f := inferInstance
  let T : Set I.subscheme := I.subschemeι.base ⁻¹' (Z : Set X)
  have hT : (Set.range (specialFibreMap I U).base)ᶜ ⊆ T := by
    intro y hy
    by_contra hyZ
    exact hy (mem_range_specialFibreMap I U y (by rwa [← SetLike.mem_coe, hU]))
  have hTdim : topologicalKrullDim T ≤ topologicalKrullDim (Z : Set X) :=
    (Set.restrictPreimage_isInducing (Z : Set X)
      I.subschemeι.isEmbedding.isInducing).topologicalKrullDim_le
  exact isCoherent_pushforward_and_rightDerived_one_of_hasPropertySk_two κ f
    (specialFibreMap I U) hS₂ T hT ((add_le_add hTdim le_rfl).trans hdim) G hG

end Stacks.Algebraization

end
