module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSliceCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.QuasiFiniteSliceZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale slices through a smooth point

Let `f : X ⟶ S` be a morphism of schemes which is smooth at a point `x : X` lying over
`s = f x`.  Assume that `x` is a closed point of the fibre `X_s` and that the residue field
extension `κ(x)/κ(s)` is separable.  Then `x` lies on an immersed subscheme `Z ⊆ X` which is
étale over `S` and whose fibre over `s` is the single point `x`.

The proof is by induction on `d = dim_x X_s`.  When `d = 0` the point is isolated in its fibre
and `f` is already étale at `x`, so an open neighbourhood of `x` isolating the fibre point will
do.  When `d > 0` the point `x` is not a generic point of `X_s`, because closedness in the fibre
makes `κ(x)/κ(s)` finite and hence the local ring of `X_s` at `x` of positive dimension;  Stacks
tag 057F then cuts a smooth effective Cartier divisor `D ⊆ U ⊆ X` through `x`, whose fibre
`D_s ⊆ X_s` is again an effective Cartier divisor, so `dim_x D_s < d` and the induction applies
to `D ⟶ S`.

## Main results

* `Stacks.AlgebraicGeometry.exists_etale_immersion_with_singleton_fiber`:
  **Stacks tag 057G**, the étale slice through a smooth point closed in its fibre with separable
  residue field extension.

## Implementation notes

The slice is returned as an immersion `i : Z ⟶ X` together with a point `z : Z` over `x`.  Its
fibre condition is written as the equality of sets `{z' | (i ≫ f) z' = f x} = {z}`;  the
scheme-theoretic fibre `Z_s` is canonically homeomorphic to that preimage
(`AlgebraicGeometry.Scheme.Hom.fiberHomeo`), so this says that `Z_s = {x}` set theoretically.

The separability hypothesis is phrased for the `κ(s)`-algebra structure on `κ(x)` induced by
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`.  Passing from `X` to a locally closed subscheme
through `x` replaces `κ(x)` by an isomorphic field, and `Algebra.IsSeparableExtension` has to be
transported along that isomorphism;  since the class quantifies over intermediate fields, the
transport is done by hand, first for `Algebra.IsSeparablyGenerated` and then for
`Algebra.IsSeparableExtension`.

## References

* [Stacks Project, Tag 057G](https://stacks.math.columbia.edu/tag/057G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SmoothAtJacobian

universe u

namespace Stacks.AlgebraicGeometry

/-! ### Generic points and the dimension of a fibre -/

/-- A generic point of an irreducible component is maximal for the specialization order. -/
private theorem isMax_of_mem_genericPoints {X : Scheme.{u}} {x : X}
    (hx : x ∈ genericPoints X) : IsMax x := by
  have hx' : Maximal IsIrreducible (closure ({x} : Set X)) := hx
  intro y hxy
  have hsp : y ⤳ x := Scheme.le_iff_specializes.mp hxy
  have hsub : closure ({x} : Set X) ⊆ closure ({y} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr hsp.mem_closure) isClosed_closure
  have hmax : closure ({y} : Set X) ⊆ closure ({x} : Set X) :=
    hx'.2 isIrreducible_singleton.closure hsub
  exact Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr (hmax (subset_closure rfl)))

/-- At a point closed in its fibre, the local dimension of the fibre is the dimension of the
local ring of the fibre:  the residue field extension is finite, so its transcendence degree
vanishes. -/
private alias topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_of_isClosed :=
  _root_.AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk

/-- A point closed in its fibre with positive-dimensional fibre is not a generic point of that
fibre. -/
private lemma notMem_genericPoints_of_pos_topologicalKrullDimAt_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hpos : 0 < topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) :
    f.asFiber x ∉ genericPoints (f.fiber (f x)) := by
  intro hgen
  rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_of_isClosed f x hclosed,
    AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hpos
  exact (Order.coheight_pos.mp (by exact_mod_cast hpos))
    (isMax_of_mem_genericPoints hgen)

/-- The local dimension of a fibre is finite at a point closed in that fibre. -/
private lemma topologicalKrullDimAt_fiber_lt_top_of_isClosed
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) < ⊤ := by
  have := isLocallyNoetherian_fiber f (f x)
  rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_of_isClosed f x hclosed]
  exact ringKrullDim_lt_top

/-! ### Slicing by an effective Cartier divisor drops the fibre dimension -/

/-- The morphism on scheme-theoretic fibres induced by a factorization `X ⟶ Y ⟶ S`. -/
private def compFiberMap {X Y S : Scheme.{u}} (j : X ⟶ Y) (q : Y ⟶ S) (s : S) :
    (j ≫ q).fiber s ⟶ q.fiber s :=
  pullback.lift ((j ≫ q).fiberι s ≫ j) ((j ≫ q).fiberToSpecResidueField s)
    (by simpa only [Category.assoc] using (j ≫ q).fiber_fac s)

/-- **An effective Cartier divisor cuts the local dimension of a fibre.**  The base change of the
divisor to the fibre is again an effective Cartier divisor, cut out on the fibre of the
restricted morphism, so Stacks tag 056N applies there. -/
private theorem topologicalKrullDimAt_fiber_subscheme_lt
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [LocallyOfFiniteType (I.subschemeι ≫ f)]
    [Flat (I.subschemeι ≫ f)] (z : I.subscheme)
    (hfinite : topologicalKrullDimAt (f.fiber (f (I.subschemeι z)))
      (f.asFiber (I.subschemeι z)) < ⊤) :
    topologicalKrullDimAt ((I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) z))
        ((I.subschemeι ≫ f).asFiber z) <
      topologicalKrullDimAt (f.fiber (f (I.subschemeι z)))
        (f.asFiber (I.subschemeι z)) := by
  classical
  let g := I.subschemeι ≫ f
  let J := I.comap (pullback.fst f (S.fromSpecResidueField (g z)))
  let J₀ := I.comap (pullback.snd (S.fromSpecResidueField (g z)) f)
  let eSwap := pullbackSymmetry f (S.fromSpecResidueField (g z))
  let e : J.subscheme ≅ g.fiber (g z) :=
    I.comapIso (pullback.fst f (S.fromSpecResidueField (g z))) ≪≫
      pullbackSymmetry (pullback.fst f (S.fromSpecResidueField (g z))) I.subschemeι ≪≫
        pullbackRightPullbackFstIso f (S.fromSpecResidueField (g z)) I.subschemeι
  have hbase : Stacks.Divisors.IsEffectiveCartierDivisor J₀ :=
    AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback f
      (S.fromSpecResidueField (g z)) I hI
  have hJ' : Stacks.Divisors.IsEffectiveCartierDivisor (J₀.comap eSwap.hom) :=
    Stacks.Divisors.isPullbackDefined_of_flat eSwap.hom _ hbase
  have hJ : Stacks.Divisors.IsEffectiveCartierDivisor J := by
    rw [← Scheme.IdealSheafData.comap_comp] at hJ'
    simpa [J, J₀, eSwap, Scheme.Hom.fiberι, Scheme.Hom.fiber,
      pullbackSymmetry_hom_comp_snd] using hJ'
  let w : g.fiber (g z) := g.asFiber z
  let y : J.subscheme := e.inv w
  have hepoint : e.hom y = w := by simp [y]
  have hcomp' : J.subschemeι ≫ pullback.fst f (S.fromSpecResidueField (g z)) =
      e.hom ≫ compFiberMap I.subschemeι f (g z) ≫
        pullback.fst f (S.fromSpecResidueField (g z)) := by
    rw [← I.comapIso_hom_fst (pullback.fst f (S.fromSpecResidueField (g z)))]
    show (I.comapIso (pullback.fst f (S.fromSpecResidueField (g z)))).hom ≫
        (pullback.fst (pullback.fst f (S.fromSpecResidueField (g z))) I.subschemeι ≫
          pullback.fst f (S.fromSpecResidueField (g z))) = _
    unfold e
    simp only [Iso.trans_hom, Category.assoc]
    apply (cancel_epi
      (I.comapIso (pullback.fst f (S.fromSpecResidueField (g z)))).hom).2
    simp only [compFiberMap, Scheme.Hom.fiberι,
      Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    with_unfolding_all
      rw [pullback.lift_fst]
      simp only [Iso.trans_hom, Category.assoc,
        pullbackRightPullbackFstIso_hom_fst_assoc,
        pullbackSymmetry_hom_comp_fst_assoc]
      exact pullback.condition
  have hcomp : J.subschemeι ≫ f.fiberι (g z) =
      e.hom ≫ compFiberMap I.subschemeι f (g z) ≫ f.fiberι (g z) := by
    simpa [Scheme.Hom.fiberι] using hcomp'
  have hyPoint : J.subschemeι y = f.asFiber (I.subschemeι z) := by
    have hgs : g z = f (I.subschemeι z) := rfl
    cases hgs
    apply (f.fiberι (f (I.subschemeι z))).isEmbedding.injective
    have hval := congrArg (fun q => q y) hcomp
    simp only [Scheme.Hom.comp_apply] at hval
    rw [hepoint] at hval
    have hmor : compFiberMap I.subschemeι f (f (I.subschemeι z)) w =
        f.asFiber (I.subschemeι z) := by
      apply (f.fiberι (f (I.subschemeι z))).isEmbedding.injective
      have hproj : compFiberMap I.subschemeι f (f (I.subschemeι z)) ≫
          f.fiberι (f (I.subschemeι z)) =
          (I.subschemeι ≫ f).fiberι (f (I.subschemeι z)) ≫ I.subschemeι := by
        dsimp [compFiberMap]
        exact pullback.lift_fst _ _ _
      calc
        f.fiberι (f (I.subschemeι z))
            (compFiberMap I.subschemeι f (f (I.subschemeι z)) w) =
            (compFiberMap I.subschemeι f (f (I.subschemeι z)) ≫
              f.fiberι (f (I.subschemeι z))) w :=
          (Scheme.Hom.comp_apply _ _ w).symm
        _ = ((I.subschemeι ≫ f).fiberι (f (I.subschemeι z)) ≫ I.subschemeι) w :=
          congrArg (fun k => k w) hproj
        _ = I.subschemeι ((I.subschemeι ≫ f).fiberι (f (I.subschemeι z)) w) :=
          Scheme.Hom.comp_apply _ _ w
        _ = f.fiberι (f (I.subschemeι z)) (f.asFiber (I.subschemeι z)) := by
          have hgw : (I.subschemeι ≫ f).fiberι (f (I.subschemeι z)) w = z := by
            show (I.subschemeι ≫ f).fiberι ((I.subschemeι ≫ f) z)
              ((I.subschemeι ≫ f).asFiber z) = z
            exact Scheme.Hom.fiberι_asFiber (I.subschemeι ≫ f) z
          rw [congrArg I.subschemeι hgw]
          exact (Scheme.Hom.fiberι_asFiber f (I.subschemeι z)).symm
    exact hval.trans (congrArg _ hmor)
  have hfinite' : topologicalKrullDimAt (f.fiber (g z)) (J.subschemeι y) < ⊤ := by
    rwa [hyPoint]
  have hlt := AlgebraicGeometry.topologicalKrullDimAt_subscheme_lt J hJ y hfinite'
  have heDim : topologicalKrullDimAt J.subscheme y =
      topologicalKrullDimAt (g.fiber (g z)) w := by
    simpa [hepoint] using topologicalKrullDimAt_eq_of_homeomorph e.hom.homeomorph y
  rwa [heDim, hyPoint] at hlt

/-- **The smooth divisor through a point of positive fibre dimension.**  Stacks tag 057F, with
its hypothesis that the point is not a generic point of the fibre supplied from positivity of
the fibre dimension, and with a point of the divisor over the given point extracted from the
support. -/
private theorem exists_smooth_divisor_of_pos_topologicalKrullDimAt_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hsmooth : InfinitesimalLifting.SmoothAt f x)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f x)) (X.residueField x))
    (hpos : 0 < topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (_hxU : x ∈ U)
      (I : U.toScheme.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (∃ z : I.subscheme, (I.subschemeι ≫ U.ι) z = x) ∧
      Smooth (I.subschemeι ≫ U.ι ≫ f) := by
  obtain ⟨U, hU, hxU, I, hI, hmem, hsm⟩ :=
    exists_smooth_divisor_of_separable_residueField f x hsmooth hsep
      (notMem_genericPoints_of_pos_topologicalKrullDimAt_fiber f x hclosed hpos)
  refine ⟨U, hU, hxU, I, hI, ?_, hsm⟩
  obtain ⟨z, hz⟩ : (⟨x, hxU⟩ : U.toScheme) ∈ Set.range I.subschemeι.base := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  refine ⟨z, ?_⟩
  rw [Scheme.Hom.comp_apply, hz]
  rfl

/-! ### The base case of the induction -/

/-- A module generated by at most zero elements is a subsingleton. -/
private alias subsingleton_of_generatedByAtMost_zero :=
  _root_.AlgebraicGeometry.subsingleton_of_generatedByAtMost_zero

/-- **A smooth point with zero-dimensional fibre is an étale point.**  The numerical criterion of
Stacks tag 01V9 bounds the relative cotangent space at `x` by the fibre dimension, so it vanishes,
and Stacks tag 02GU then gives étaleness at `x`. -/
@[sga "3 XI 1.9" "partial"]
private lemma etaleAt_of_smoothAt_of_topologicalKrullDimAt_fiber_eq_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    (hsmooth : InfinitesimalLifting.SmoothAt f x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0) :
    EtaleAt f x := by
  have h12 := (Stacks.Tag01V9NumericalCriterion.smoothAt_tfae f x).out 1 2
  have hflat : (f.stalkMap x).hom.Flat := (h12.mp hsmooth).1
  have h14 := (Stacks.Tag01V9NumericalCriterion.smoothAt_tfae f x).out 1 4
  have hgen : GeneratedByAtMost (X.residueField x) (relativeCotangentSpace f x)
      (topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) := (h14.mp hsmooth).2
  apply ((AlgebraicGeometry.etaleAt_tfae f x).out 1 6).mpr
  refine ⟨hflat, ?_⟩
  apply subsingleton_of_generatedByAtMost_zero (R := X.residueField x)
  simpa [hdim] using hgen

/-- **An étale point with zero-dimensional fibre has an open étale slice.**  The point is isolated
in its fibre, so an affine open neighbourhood on which the morphism is étale can be shrunk to meet
the fibre only in that point. -/
private lemma exists_etale_open_slice_of_etaleAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0)
    (hetale : EtaleAt f x) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
      Etale (i ≫ f) ∧ {z' : Z | (i ≫ f) z' = f x} = {z} := by
  have := isLocallyNoetherian_fiber f (f x)
  have hisol : IsOpen ({f.asFiber x} : Set (f.fiber (f x))) :=
    (AlgebraicGeometry.topologicalKrullDimAt_eq_zero_iff_isIsolatedPoint (f.fiber (f x))
      (f.asFiber x)).mp hdim
  let p : f ⁻¹' {f x} := ⟨x, rfl⟩
  have hpOpen : IsOpen ({p} : Set (f ⁻¹' {f x})) := by
    have he := (f.fiberHomeo (f x)).isOpen_image.mpr hisol
    have hpoint : f.fiberHomeo (f x) (f.asFiber x) = p := by
      apply Subtype.ext
      simp [p]
    have himage : (f.fiberHomeo (f x)) '' {f.asFiber x} = {p} := by
      ext y
      simp [hpoint]
    rwa [himage] at he
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hpOpen
  obtain ⟨V, hV, hxV, hVEtale⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_etale_comp_ι_of_etaleAt f x hetale
  let O' : X.Opens := ⟨O, hO⟩
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ V ⊓ O' from
      ⟨hxV, show p ∈ Subtype.val ⁻¹' O by simp [hOeq]⟩)
  have hUO : U ≤ O' := hUV.trans inf_le_right
  have hUEtale : Etale (U.ι ≫ f) := by
    have hopen : IsOpenImmersion (Scheme.homOfLE X (hUV.trans inf_le_left)) := by
      unfold Scheme.homOfLE
      infer_instance
    have hetaleOpen : Etale (Scheme.homOfLE X (hUV.trans inf_le_left)) := inferInstance
    rw [← Scheme.homOfLE_ι X (hUV.trans inf_le_left), Category.assoc]
    exact Etale.etale_comp _ _
  let z : U.toScheme := ⟨x, hxU⟩
  refine ⟨U.toScheme, U.ι, z, inferInstance, rfl, hUEtale, ?_⟩
  ext y
  constructor
  · intro hy
    have hyO : (⟨U.ι y, hy⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' O := hUO y.2
    rw [hOeq, Set.mem_singleton_iff] at hyO
    exact Subtype.ext (congrArg Subtype.val hyO : U.ι y = x)
  · rintro rfl
    show (U.ι ≫ f) z = f x
    rw [Scheme.Hom.comp_apply]
    simp [z]

/-! ### Transport along an immersion -/

/-- `Algebra.IsSeparablyGenerated` transports along an isomorphism of extensions:  the image of a
separating transcendence basis is one. -/
private theorem isSeparablyGenerated_of_algEquiv {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L)
    (hK : Algebra.IsSeparablyGenerated k K) : Algebra.IsSeparablyGenerated k L := by
  obtain ⟨s, hs, hsep⟩ := hK
  let t : Set L := e '' s
  let es : s ≃ t := Equiv.Set.image e.toEquiv s e.toEquiv.injective
  have hcomp : (fun w : t => (w : L)) ∘ es = fun w : s => e w := rfl
  have ht' : IsTranscendenceBasis k (fun w : t => (w : L)) :=
    (isTranscendenceBasis_equiv' es hcomp).mp (e.isTranscendenceBasis hs)
  let F : IntermediateField k K := IntermediateField.adjoin k s
  let F' : IntermediateField k L := IntermediateField.adjoin k t
  let eF : F ≃ₐ[k] F.map e.toAlgHom := IntermediateField.intermediateFieldMap e F
  have hF : F.map e.toAlgHom = F' :=
    IntermediateField.adjoin_map k s (e : K →ₐ[k] L)
  let e1 : F ≃ₐ[k] F' := eF.trans (IntermediateField.equivOfEq hF)
  have he : (algebraMap F' L).comp (e1 : F →ₐ[k] F') =
      (e : K →+* L).comp (algebraMap F K) := by
    ext w
    rfl
  have : Algebra.IsSeparable F K := hsep
  exact ⟨t, ht', Algebra.IsSeparable.of_equiv_equiv e1.toRingEquiv e.toRingEquiv he⟩

/-- `Algebra.IsSeparableExtension` transports along an isomorphism of extensions:  the finitely
generated subextensions correspond under the isomorphism. -/
private theorem isSeparableExtension_of_algEquiv {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L)
    [hK : Algebra.IsSeparableExtension k K] : Algebra.IsSeparableExtension k L := by
  refine ⟨fun L' hL' => ?_⟩
  let K' : IntermediateField k K := L'.comap e.toAlgHom
  have hmap : K'.map e.toAlgHom = L' := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      show e (e.symm w) ∈ L'
      simpa using hw
  have hK'fg : K'.FG := by
    have hL'fg : L'.FG := IntermediateField.essFiniteType_iff.mp hL'
    rw [IntermediateField.fg_def] at hL'fg ⊢
    obtain ⟨s, hsfinite, hsgen⟩ := hL'fg
    refine ⟨e.symm '' s, hsfinite.image _, ?_⟩
    apply IntermediateField.map_injective e.toAlgHom
    rw [IntermediateField.adjoin_map, Set.image_image, hmap]
    simpa using hsgen
  have : Algebra.EssFiniteType k K' := IntermediateField.essFiniteType_iff.mpr hK'fg
  let e' : K' ≃ₐ[k] L' :=
    (IntermediateField.intermediateFieldMap e K').trans (IntermediateField.equivOfEq hmap)
  exact isSeparablyGenerated_of_algEquiv e' (hK.isSeparablyGenerated K')

/-- Separability of the residue field extension passes to an immersed subscheme, for the algebra
structure given by the composite of the two residue field maps. -/
private lemma isSeparableExtension_residueField_comp_of_isImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) [IsImmersion j] (y : Y)
    (hsep : letI := (f.residueFieldMap (j y)).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f (j y)))
        (X.residueField (j y))) :
    (letI := (((j.residueFieldMap y).hom.comp
        (f.residueFieldMap (j y)).hom).toAlgebra);
      Algebra.IsSeparableExtension (S.residueField (f (j y)))
        (Y.residueField y)) := by
  let k := S.residueField (f (j y))
  let K := X.residueField (j y)
  let L := Y.residueField y
  let _ : Algebra k K := (f.residueFieldMap (j y)).hom.toAlgebra
  let _ : Algebra k L := ((j.residueFieldMap y).hom.comp
    (f.residueFieldMap (j y)).hom).toAlgebra
  have : IsIso (j.residueFieldMap y) := isIso_residueFieldMap_of_isImmersion j y
  let eRing : K ≃+* L :=
    RingEquiv.ofBijective (show K →+* L from (j.residueFieldMap y).hom)
      (ConcreteCategory.bijective_of_isIso (j.residueFieldMap y))
  have hmap : eRing.toRingHom.comp (algebraMap k K) = algebraMap k L := rfl
  have : Algebra.IsSeparableExtension k K := hsep
  let e : K ≃ₐ[k] L := AlgEquiv.ofRingEquiv (f := eRing) (fun a => by
    simpa using congrArg (fun q : k →+* L => q a) hmap)
  exact isSeparableExtension_of_algEquiv e

/-- Separability of the residue field extension passes to an immersed subscheme through the
point. -/
private lemma isSeparableExtension_residueField_of_isImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) [IsImmersion j]
    (x : X) (y : Y) (hy : j y = x)
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f x)) (X.residueField x)) :
    letI := ((j ≫ f).residueFieldMap y).hom.toAlgebra
    Algebra.IsSeparableExtension (S.residueField ((j ≫ f) y)) (Y.residueField y) := by
  subst x
  convert isSeparableExtension_residueField_comp_of_isImmersion f j y hsep using 1 <;>
    simp only [Scheme.Hom.comp_apply, Scheme.residueFieldMap_comp] <;> rfl

/-- Closedness in the fibre passes to an immersed subscheme:  the fibre of the composite embeds
in the fibre of the original morphism. -/
private lemma isClosed_asFiber_comp_of_isImmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) [IsImmersion j] (y : Y)
    (hclosed : IsClosed ({f.asFiber (j y)} : Set (f.fiber (f (j y))))) :
    IsClosed ({(j ≫ f).asFiber y} : Set ((j ≫ f).fiber ((j ≫ f) y))) := by
  let F := (f.fiberHomeo (f (j y))).symm ∘
    (f ⁻¹' {f (j y)}).restrictPreimage j ∘ (j ≫ f).fiberHomeo ((j ≫ f) y)
  have hF : Topology.IsEmbedding F :=
    (f.fiberHomeo _).symm.isEmbedding.comp
      ((j.isEmbedding.restrictPreimage _).comp ((j ≫ f).fiberHomeo _).isEmbedding)
  have hp : F ((j ≫ f).asFiber y) = f.asFiber (j y) := by
    apply (f.fiberHomeo _).injective
    dsimp only [F, Function.comp_apply]
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    show j ((j ≫ f).fiberι _ ((j ≫ f).asFiber y)) = f.fiberι _ (f.asFiber (j y))
    rw [Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]
  convert hclosed.preimage hF.continuous using 1
  ext a
  show a = (j ≫ f).asFiber y ↔ F a = f.asFiber (j y)
  rw [← hp, hF.injective.eq_iff]

/-! ### The étale slice -/

/-- An étale slice for `j ≫ f` through `y` composes with an immersion `j` to an étale slice for `f`
through `j y`. -/
private lemma exists_etale_slice_of_comp_immersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (j : Y ⟶ X) [IsImmersion j] (x : X) (y : Y) (hy : j y = x)
    (h : ∃ (Z : Scheme.{u}) (i : Z ⟶ Y) (z : Z), IsImmersion i ∧ i z = y ∧
      Etale (i ≫ j ≫ f) ∧ {z' : Z | (i ≫ j ≫ f) z' = (j ≫ f) y} = {z}) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
      Etale (i ≫ f) ∧ {z' : Z | (i ≫ f) z' = f x} = {z} := by
  obtain ⟨Z, i, z, hi, hiz, het, hfib⟩ := h
  have : IsImmersion i := hi
  refine ⟨Z, i ≫ j, z, inferInstance, ?_, ?_, ?_⟩
  · simpa only [Scheme.Hom.comp_apply, hiz] using hy
  · simpa only [Category.assoc] using het
  · simpa only [Category.assoc, Scheme.Hom.comp_apply, hy] using hfib

/-- **The étale slice through a point of a smooth morphism**, by induction on the local dimension
`d` of the fibre.  For `d = 0` the slice is an open neighbourhood of the point;  for `d > 0` a
smooth effective Cartier divisor through the point drops the fibre dimension and the induction
hypothesis applies to it. -/
private theorem exists_etale_slice_of_smooth
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f x)) (X.residueField x)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z), IsImmersion i ∧ i z = x ∧
      Etale (i ≫ f) ∧ {z' : Z | (i ≫ f) z' = f x} = {z} := by
  generalize hd : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = d
  induction d using (wellFounded_lt (α := WithBot ℕ∞)).induction generalizing X S with
  | h d ih =>
    have hsmooth : InfinitesimalLifting.SmoothAt f x := InfinitesimalLifting.smoothAt_of_smooth f x
    by_cases hzero : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 0
    · exact exists_etale_open_slice_of_etaleAt f x hzero
        (etaleAt_of_smoothAt_of_topologicalKrullDimAt_fiber_eq_zero f x hsmooth hzero)
    have hpos : 0 < topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
      rw [topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_of_isClosed f x hclosed] at hzero ⊢
      exact lt_of_le_of_ne ringKrullDim_nonneg_of_nontrivial (Ne.symm hzero)
    obtain ⟨U, hU, hxU, I, hI, ⟨y, hy⟩, hsm⟩ :=
      exists_smooth_divisor_of_pos_topologicalKrullDimAt_fiber f x hsmooth hclosed hsep hpos
    let j := I.subschemeι ≫ U.ι
    let g := j ≫ f
    have : Smooth g := by simpa [g, j, Category.assoc] using hsm
    have hy' : j y = x := hy
    have hclosed' : IsClosed ({g.asFiber y} : Set (g.fiber (g y))) :=
      isClosed_asFiber_comp_of_isImmersion f j y (by cases hy'; exact hclosed)
    have hsep' := isSeparableExtension_residueField_of_isImmersion f j x y hy' hsep
    have hdimU := AlgebraicGeometry.fiberDimensionAt_comp_openImmersion U.ι f
      (I.subschemeι y)
    have hfiniteU : topologicalKrullDimAt ((U.ι ≫ f).fiber ((U.ι ≫ f) (I.subschemeι y)))
        ((U.ι ≫ f).asFiber (I.subschemeι y)) < ⊤ := by
      rw [hdimU, show U.ι (I.subschemeι y) = x from hy]
      exact topologicalKrullDimAt_fiber_lt_top_of_isClosed f x hclosed
    have : Smooth (I.subschemeι ≫ (U.ι ≫ f)) := hsm
    have hlt := topologicalKrullDimAt_fiber_subscheme_lt (U.ι ≫ f) I hI y hfiniteU
    have hlt' : topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) < d := by
      rw [hdimU, show U.ι (I.subschemeι y) = x from hy, hd] at hlt
      show topologicalKrullDimAt (((I.subschemeι ≫ U.ι) ≫ f).fiber
        (((I.subschemeι ≫ U.ι) ≫ f) y)) (((I.subschemeι ≫ U.ι) ≫ f).asFiber y) < d
      rw [Category.assoc]
      exact hlt
    exact exists_etale_slice_of_comp_immersion f j x y hy' (ih _ hlt' g y hclosed' hsep' rfl)

/-- **Stacks Project, Tag 057G.**  Let `f : X ⟶ S` be a morphism of schemes, `x : X` a point with
image `s = f x`.  If `f` is smooth at `x`, if `x` is a closed point of the fibre `X_s`, and if the
residue field extension `κ(x)/κ(s)` is separable, then there is an immersion `i : Z ⟶ X` whose
image contains `x` such that `Z ⟶ S` is étale and `Z_s = {x}` set theoretically. -/
@[stacks 057G, ega "IV 17.16.3" "Clause (i)", sga "3 XI 1.10" "more general"]
public theorem exists_etale_immersion_with_singleton_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hsmooth : InfinitesimalLifting.SmoothAt f x)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))))
    (hsep : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparableExtension (S.residueField (f x)) (X.residueField x)) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z),
      IsImmersion i ∧ i z = x ∧ Etale (i ≫ f) ∧
        {z' : Z | (i ≫ f) z' = f x} = {z} := by
  obtain ⟨U, hxU, hsm⟩ := hsmooth
  have : Smooth (f.resLE ⊤ U le_top) := hsm
  have : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f (show U ≤ f ⁻¹ᵁ ⊤ from le_top)]
    infer_instance
  let y : U.toScheme := ⟨x, hxU⟩
  have hclosed' := isClosed_asFiber_comp_of_isImmersion f U.ι y hclosed
  have hsep' := isSeparableExtension_residueField_of_isImmersion f U.ι x y rfl hsep
  exact exists_etale_slice_of_comp_immersion f U.ι x y rfl
    (exists_etale_slice_of_smooth (U.ι ≫ f) y hclosed' hsep')

end Stacks.AlgebraicGeometry

end
