module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.GenericProperness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence

/-!
# A refined Noetherian valuative criterion for separatedness of algebraic spaces

Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S` with `Y` locally
Noetherian, `f` locally of finite type and quasi-separated, `h` of finite type and the image of
`|h|` dense in `|X|`. If every valuative diagram for `f` over a discrete valuation ring whose
generic arrow factors through `h` has at most one dotted arrow, then `f` is separated
(Stacks 0CME).

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_denseRange_of_subsingleton_discreteLift`:
  **Stacks 0CME**, with exactly the hypotheses of the tag.
* `AlgebraicGeometry.exists_comp_eq_of_specMap_comp_eq`: a morphism from the spectrum of a
  discrete valuation ring `A` factors through a monomorphism of schemes once its composite with
  `Spec B ⟶ Spec A` does, for an injective local homomorphism `A ⟶ B` to a local domain.

## Implementation notes

The source deduces the tag from its properness companion, Stacks 0CMD, applied to the diagonal,
whose proof needs the weak Chow lemma for algebraic spaces. The argument here instead runs the
proof of Stacks 0H1W: the base change `V ⟶ C` of the relative diagonal of `f` along an étale chart
`C` of `X ×_Y X` is a quasi-compact monomorphism of schemes, locally of finite type over a locally
Noetherian scheme, so by Stacks 0208
(`AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`) it is proper, hence a closed
immersion, as soon as discrete valuation subrings `A` of the residue fields at generic points `η`
of `V` have dotted arrows. To produce one, `η` is placed in an affine open `V₀`, and the base
change of `h` to `V₀` is given a quasi-compact étale atlas `T`; the induced `T ⟶ V₀` is
quasi-compact, locally of finite type and has dense image, because `V₀ ⟶ X` is étale and so open on
points (Stacks 03IR) while points of a fibre product are pairs of points (Stacks 03H4). Hence `η`
is the image of a point `x` of `T` (Stacks 01RL), and `A` is dominated by a discrete valuation ring
`R ⊆ κ(x)` with fraction field `κ(x)` (Stacks 00PH). Over `R` the generic arrow factors through
`h`, so the two projections to `X` agree and give a dotted arrow over `R`; it descends to `A`
because `Spec R ⟶ Spec A` is faithfully flat and isomorphisms descend along faithfully flat
quasi-compact morphisms.

Density of the image of `|h|` is `DenseRange` of `AlgebraicGeometry.Space.pointsMap` for the
topology `AlgebraicGeometry.Space.pointTopology` of Stacks 03BX. As throughout the chapter, the
valuative diagrams are those whose valuation ring and fraction field have spectra in the chosen
big site, and the dotted arrows are `AlgebraicGeometry.Space.ValuativeSquare.Lift`.

## References

* [Stacks Project, Tag 0CME](https://stacks.math.columbia.edu/tag/0CME)
* [Stacks Project, Tag 0H1W](https://stacks.math.columbia.edu/tag/0H1W)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism `Spec A ⟶ U` from the spectrum of a discrete valuation ring factors through a
monomorphism `p : V ⟶ U` of schemes as soon as its composite with `Spec B ⟶ Spec A` does, for an
injective local homomorphism `A ⟶ B` to a local domain: `Spec B ⟶ Spec A` is faithfully flat, and
the base change of `p` along it is a monomorphism with a section, hence an isomorphism, so `p`
pulled back to `Spec A` is an isomorphism by flat descent. -/
theorem exists_comp_eq_of_specMap_comp_eq {A B : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    (φ : A →+* B) (hφ : Function.Injective φ) [IsLocalHom φ]
    {V U : Scheme.{u}} (p : V ⟶ U) [Mono p] (i : Spec (.of A) ⟶ U)
    (l : Spec (.of B) ⟶ V) (hl : l ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ i) :
    ∃ m : Spec (.of A) ⟶ V, m ≫ p = i := by
  let _ : Algebra A B := φ.toAlgebra
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  have hff : (CommRingCat.ofHom φ).hom.FaithfullyFlat := by
    change Module.FaithfullyFlat A B
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom φ)).2 hff
  have hfst : IsIso (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (pullback.snd p i)) := by
    have : IsSplitEpi (pullback.fst (Spec.map (CommRingCat.ofHom φ)) (pullback.snd p i)) :=
      ⟨⟨pullback.lift (𝟙 _) (pullback.lift l (Spec.map (CommRingCat.ofHom φ)) hl)
        (by rw [pullback.lift_snd, Category.id_comp]), pullback.lift_fst _ _ _⟩⟩
    exact isIso_of_mono_of_isSplitEpi _
  have hsnd : IsIso (pullback.snd p i) :=
    MorphismProperty.of_pullback_fst_of_descendsAlong (P := MorphismProperty.isomorphisms _)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨hsurj, hflat⟩, inferInstance⟩ hfst
  exact ⟨inv (pullback.snd p i) ≫ pullback.fst p i, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_RefinedValuativeSeparatedness :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RefinedValuativeSeparatedness
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

open TopologicalSpace in
/-- The dotted arrows of the chart of the diagonal. Let `atlas` be a chart of `X ×_Y X`, let
`s : W ⟶ C` be the base change of the relative diagonal of `f` along it, and let `τ : T ⟶ W` be
a morphism of the site whose composite with `W ⟶ X` factors through `h : U ⟶ X`. If valuative
diagrams for `f` over discrete valuation rings whose generic arrow factors through `h` have at
most one dotted arrow, then every morphism from the spectrum of a discrete valuation subring `R`
of a residue field `κ(x)` of `T` to `C` which agrees on `Spec κ(x)` with `Spec κ(x) ⟶ T ⟶ W ⟶ C`
factors through `s`: it is a pair of morphisms to `X` agreeing over `Y` and on `Spec κ(x)`, the
generic arrow factors through `h`, so the two agree. -/
private theorem exists_comp_eq_of_subsingleton_lift {f : X ⟶ Y} (h : U ⟶ X)
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Subsingleton q.Lift)
    {C W : BigFppfOver B S hS} (atlas : yoneda.obj C ⟶ pullback f f)
    (c : yoneda.obj W ⟶ X) (s : W ⟶ C)
    (hdiagPB : IsPullback c (yoneda.map s) (pullback.diagonal f) atlas)
    {T : BigFppfOver B S hS} (τ : T ⟶ W) (a : yoneda.obj T ⟶ U)
    (hτ : yoneda.map τ ≫ c = a ≫ h)
    (x : (BigFppfOver.toScheme B S hS).obj T)
    (R : Subring (((BigFppfOver.toScheme B S hS).obj T).residueField x))
    [IsDiscreteValuationRing R]
    [IsFractionRing R (((BigFppfOver.toScheme B S hS).obj T).residueField x)]
    (j : Spec (.of R) ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (w : ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField x ≫
        (BigFppfOver.toScheme B S hS).map τ ≫ (BigFppfOver.toScheme B S hS).map s =
      Spec.map (CommRingCat.ofHom R.subtype) ≫ j) :
    ∃ l : Spec (.of R) ⟶ (BigFppfOver.toScheme B S hS).obj W,
      l ≫ (BigFppfOver.toScheme B S hS).map s = j := by
  classical
  have hKmem : B.Contains
      (Spec (.of (((BigFppfOver.toScheme B S hS).obj T).residueField x : Type u))) :=
    B.residueField_spec_contains T.left.property x
  have hAmem : B.Contains (Spec (.of (R : Type u))) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R hKmem
  have hsubtype : R.subtype =
      algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x) := rfl
  set baseA : Spec (.of (R : Type u)) ⟶ S := j ≫ B.inclusion.map C.hom with hbaseA
  set iK := ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField x with hiKdef
  set uA : siteObject B S hS hAmem baseA ⟶ C :=
    Over.homMk (B.inclusion.preimage (X := B.obj hAmem) (Y := C.left) j) (by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      change j ≫ B.inclusion.map C.hom = baseA
      rw [hbaseA]) with huAdef
  have hTbase : (BigFppfOver.toScheme B S hS).map τ ≫ (BigFppfOver.toScheme B S hS).map s ≫
      B.inclusion.map C.hom = B.inclusion.map T.hom := by
    change B.inclusion.map τ.left ≫ B.inclusion.map s.left ≫ B.inclusion.map C.hom = _
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, ← Category.assoc, ← Over.comp_left,
      Over.w (τ ≫ s)]
  set uK₀ : siteObject B S hS hKmem
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x))) ≫ baseA) ⟶ T :=
    Over.homMk (B.inclusion.preimage (X := B.obj hKmem) (Y := T.left) iK) (by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      change iK ≫ B.inclusion.map T.hom =
        Spec.map (CommRingCat.ofHom
          (algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x))) ≫ baseA
      have w' := w
      rw [← hTbase, hiKdef]
      simp only [← Category.assoc] at w' ⊢
      rw [w', hbaseA, ← hsubtype, Category.assoc])
      with huK₀def
  set uFrac : siteObject B S hS hKmem
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x))) ≫ baseA) ⟶
      siteObject B S hS hAmem baseA :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x)))) :
      B.obj hKmem ⟶ B.obj hAmem) with huFracdef
  have huKs : (uK₀ ≫ τ) ≫ s = uFrac ≫ uA := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    rw [Over.comp_left, Over.comp_left, Over.comp_left, B.inclusion.map_comp,
      B.inclusion.map_comp, B.inclusion.map_comp, huK₀def, huAdef, huFracdef]
    change B.inclusion.map (B.inclusion.preimage (X := B.obj hKmem) (Y := T.left) iK) ≫
        B.inclusion.map τ.left ≫ B.inclusion.map s.left =
      Spec.map (CommRingCat.ofHom
          (algebraMap R (((BigFppfOver.toScheme B S hS).obj T).residueField x))) ≫
        B.inclusion.map (B.inclusion.preimage (X := B.obj hAmem) (Y := C.left) j)
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage, ← hsubtype]
    exact w
  have hmap : yoneda.map (uK₀ ≫ τ) ≫ yoneda.map s = yoneda.map uFrac ≫ yoneda.map uA := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, huKs]
  have hcf : ∀ p : pullback f f ⟶ X, pullback.diagonal f ≫ p = 𝟙 X →
      c = yoneda.map s ≫ atlas ≫ p := fun p hp => by
    rw [← Category.assoc, ← hdiagPB.w, Category.assoc, hp, Category.comp_id]
  set q : ValuativeSquare f :=
    { R := R
      K := (((BigFppfOver.toScheme B S hS).obj T).residueField x : Type u)
      ring_mem := hAmem
      field_mem := hKmem
      base := baseA
      generic := yoneda.map (uK₀ ≫ τ) ≫ c
      special := yoneda.map uA ≫ atlas ≫ pullback.fst f f ≫ f
      comm := by
        change (yoneda.map (uK₀ ≫ τ) ≫ c) ≫ f =
          yoneda.map uFrac ≫ yoneda.map uA ≫ atlas ≫ pullback.fst f f ≫ f
        rw [hcf _ (pullback.diagonal_fst f)]
        simp only [Category.assoc]
        rw [reassoc_of% hmap] }
  have hgen : yoneda.map uK₀ ≫ a ≫ h = q.generic := by
    change yoneda.map uK₀ ≫ a ≫ h = yoneda.map (uK₀ ≫ τ) ≫ c
    rw [← hτ, yoneda.map_comp, Category.assoc]
  have : Subsingleton q.Lift :=
    hvaluative q (inferInstanceAs (IsDiscreteValuationRing (R : Type u)))
      (yoneda.map uK₀ ≫ a) ((Category.assoc _ _ _).trans hgen)
  have hlift : ∀ p : pullback f f ⟶ X, pullback.diagonal f ≫ p = 𝟙 X →
      p ≫ f = pullback.fst f f ≫ f → ∃ l : q.Lift, l.map = yoneda.map uA ≫ atlas ≫ p :=
    fun p hp hpf => ⟨
      { map := yoneda.map uA ≫ atlas ≫ p
        generic_comm := by rw [← reassoc_of% hmap, ← hcf p hp]
        special_comm := by
          change _ = yoneda.map uA ≫ atlas ≫ pullback.fst f f ≫ f
          simp only [Category.assoc, hpf] }, rfl⟩
  obtain ⟨l₁, hl₁⟩ := hlift _ (pullback.diagonal_fst f) rfl
  obtain ⟨l₂, hl₂⟩ := hlift _ (pullback.diagonal_snd f) pullback.condition.symm
  have hmEq : l₁.map = l₂.map := congrArg ValuativeSquare.Lift.map (Subsingleton.elim l₁ l₂)
  have hdiagSq : l₁.map ≫ pullback.diagonal f = yoneda.map uA ≫ atlas := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, hl₁]
      simp only [Category.assoc]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hmEq, hl₂]
      simp only [Category.assoc]
  set lA : siteObject B S hS hAmem baseA ⟶ W :=
    yoneda.preimage (hdiagPB.lift l₁.map (yoneda.map uA) hdiagSq)
  have hlAmap : yoneda.map lA = hdiagPB.lift l₁.map (yoneda.map uA) hdiagSq :=
    yoneda.map_preimage _
  have hlAs : lA ≫ s = uA :=
    yoneda.map_injective <| by rw [yoneda.map_comp, hlAmap, hdiagPB.lift_snd]
  refine ⟨(BigFppfOver.toScheme B S hS).map lA, ?_⟩
  rw [← (BigFppfOver.toScheme B S hS).map_comp, hlAs, huAdef]
  change B.inclusion.map (B.inclusion.preimage (X := B.obj hAmem) (Y := C.left) j) = j
  rw [B.inclusion.map_preimage]

open TopologicalSpace in
/-- The existence half of condition (4) of Stacks 0208 for the chart `s : W ⟶ C` of the
diagonal of `f`. A generic point `η` of `W` lies in an affine open `W₀`; the base change of the
quasi-compact morphism `h` to `W₀` has a quasi-compact étale atlas `T`, and the induced morphism of
schemes `T ⟶ W₀` is quasi-compact, locally of finite type and has dense image, because `W₀ ⟶ X` is
étale, hence open on points, and `h` has dense image. So `η` is the image of a point `x` of `T`
(Stacks 01RL), the discrete valuation ring `A ⊆ κ(η)` is dominated by a discrete valuation ring
`R ⊆ κ(x)` with fraction field `κ(x)` (Stacks 00PH), the valuative diagram over `R` has a dotted
arrow since its generic arrow factors through `h`, and that dotted arrow descends to `A` along
the faithfully flat `Spec R ⟶ Spec A` because `s` is a monomorphism. -/
private theorem nonempty_liftStruct_of_denseRange (hX : IsAlgebraicSpace B S hS X)
    (hU : IsAlgebraicSpace B S hS U) {f : X ⟶ Y} (h : U ⟶ X)
    (hh : IsFiniteType B S hS h)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Subsingleton q.Lift)
    {C W : BigFppfOver B S hS} (atlas : yoneda.obj C ⟶ pullback f f)
    (c : yoneda.obj W ⟶ X) (s : W ⟶ C)
    (hdiagPB : IsPullback c (yoneda.map s) (pullback.diagonal f) atlas)
    (hcEtale : IsEtale B S hS c)
    (hsMono : Mono ((BigFppfOver.toScheme B S hS).map s))
    (η : (BigFppfOver.toScheme B S hS).obj W)
    (hη : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj W))
    (A : Subring (((BigFppfOver.toScheme B S hS).obj W).residueField η))
    [IsDiscreteValuationRing A]
    [IsFractionRing A (((BigFppfOver.toScheme B S hS).obj W).residueField η)]
    (i₂ : Spec (.of A) ⟶ (BigFppfOver.toScheme B S hS).obj C)
    (sq : CommSq (((BigFppfOver.toScheme B S hS).obj W).fromSpecResidueField η)
      (Spec.map (CommRingCat.ofHom A.subtype)) ((BigFppfOver.toScheme B S hS).map s) i₂) :
    Nonempty sq.LiftStruct := by
  classical
  let _ : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  -- an affine open neighbourhood of `η`, as an object of the site
  obtain ⟨Wo, hWoaff, hηWo, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj W) (x := η)
      (U := ⊤) trivial
  have hWo : B.Contains (Wo : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion Wo.ι W.left.property
  let oL : B.obj hWo ⟶ W.left := B.inclusion.preimage (X := B.obj hWo) (Y := W.left) Wo.ι
  let Wo' : BigFppfOver B S hS := Over.mk (oL ≫ W.hom)
  let o : Wo' ⟶ W := Over.homMk oL
  have ho : (BigFppfOver.toScheme B S hS).map o = Wo.ι := B.inclusion.map_preimage _
  have hWoAff : IsAffine ((BigFppfOver.toScheme B S hS).obj Wo') := hWoaff
  let g : yoneda.obj Wo' ⟶ X := yoneda.map o ≫ c
  have hoEt : IsEtale B S hS (yoneda.map o) :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS o).2 (by rw [ho]; infer_instance))
  have hgEt : IsEtale B S hS g := isEtale_comp B S hS hoEt hcEtale
  have hWoAlg : IsAlgebraicSpace B S hS (yoneda.obj Wo') := isAlgebraicSpace_yoneda B S hS Wo'
  -- a quasi-compact étale atlas of the base change of `h` to `W₀`
  obtain ⟨T, t, hTc, htSurj, htEt⟩ := hh.2 (yoneda.obj Wo') hWoAlg
    (isQuasiCompact_yoneda_of_compact B S hS Wo' inferInstance) g
  have hPB : IsAlgebraicSpace B S hS (pullback g h) :=
    isAlgebraicSpace_pullback B S hS g h hWoAlg hU hX
  have hsndEt : IsEtale B S hS (pullback.snd g h) :=
    isEtale_pullback_snd B S hS hU hX hWoAlg g h hgEt
  have haEt : IsEtale B S hS (t ≫ pullback.snd g h) := isEtale_comp B S hS htEt hsndEt
  set τ₀ : T ⟶ Wo' := yoneda.preimage (t ≫ pullback.fst g h)
  have hτ₀ : yoneda.map τ₀ = t ≫ pullback.fst g h := yoneda.map_preimage _
  have hτ₀g : yoneda.map τ₀ ≫ g = (t ≫ pullback.snd g h) ≫ h := by
    rw [hτ₀, Category.assoc, pullback.condition, Category.assoc]
  have hτ : yoneda.map (τ₀ ≫ o) ≫ c = (t ≫ pullback.snd g h) ≫ h := by
    rw [yoneda.map_comp, Category.assoc, hτ₀g]
  -- the morphism of schemes `T ⟶ W₀`
  set τ' := (BigFppfOver.toScheme B S hS).map τ₀
  have hτ'LFT : LocallyOfFiniteType τ' :=
    hh.1 T Wo' (t ≫ pullback.snd g h) g τ₀ ((isEtale_iff_presheaf_of_yoneda B S hS _).1 haEt)
      ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hgEt) hτ₀g
  have hτ'QC : QuasiCompact τ' :=
    have := hTc
    quasiCompact_of_compactSpace τ'
  have hτ'dense : DenseRange τ' := by
    let _ : TopologicalSpace (points B S hS (yoneda.obj Wo')) :=
      pointTopology B S hS (yoneda.obj Wo')
    let e := schemePointsHomeomorph B S hS Wo'
    have hD : Dense (pointsMap B S hS (yoneda.obj Wo') g ⁻¹'
        Set.range (pointsMap B S hS U h)) :=
      hdense.preimage (isOpenMap_pointsMap_of_isEtale B S hS g hWoAlg hX hgEt)
    refine (e.isDenseEmbedding.dense_image.2 hD).mono ?_
    rintro _ ⟨z, ⟨y, hy⟩, rfl⟩
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g h) z y
      hy.symm
    obtain ⟨v, rfl⟩ :=
      (surjective_iff_surjective_pointsMap B S hS (pullback g h) hPB T t).1 htSurj w
    refine ⟨pointsToScheme B S hS T v, ?_⟩
    rw [← hw, ← pointsMap_comp_apply, ← hτ₀, schemePointsHomeomorph_apply,
      pointsToScheme_pointsMap]
  -- `η` is the image of a point `x` of `T`
  have hηgen : (⟨η, hηWo⟩ : (BigFppfOver.toScheme B S hS).obj Wo') ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj Wo') :=
    mem_genericPoints_source_of_isOpenImmersion Wo.ι hη
  obtain ⟨x, hx⟩ := (isDominant_iff_genericPoints_subset_range τ').1
    ((isDominant_iff τ').2 hτ'dense) hηgen
  have hτ'' : (BigFppfOver.toScheme B S hS).map (τ₀ ≫ o) = τ' ≫ Wo.ι := by
    rw [Functor.map_comp, ho]
  have hxη : (BigFppfOver.toScheme B S hS).map (τ₀ ≫ o) x = η := by
    rw [hτ'', Scheme.Hom.comp_apply, hx]
    rfl
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (τ₀ ≫ o)) := by
    rw [hτ'']
    infer_instance
  generalize hF : (BigFppfOver.toScheme B S hS).map (τ₀ ≫ o) = F at hxη this
  subst hxη
  -- a discrete valuation ring of `κ(x)` dominating `A`
  let _ : Algebra (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (((BigFppfOver.toScheme B S hS).obj T).residueField x) :=
    (F.residueFieldMap x).hom.toAlgebra
  have _ : Algebra.EssFiniteType (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (((BigFppfOver.toScheme B S hS).obj T).residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap (f := F) x)
  let _ : Algebra A (((BigFppfOver.toScheme B S hS).obj T).residueField x) :=
    ((algebraMap (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (((BigFppfOver.toScheme B S hS).obj T).residueField x)).comp
      (algebraMap A (((BigFppfOver.toScheme B S hS).obj W).residueField (F x)))).toAlgebra
  have _ : IsScalarTower A (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (((BigFppfOver.toScheme B S hS).obj T).residueField x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨Bs, hBdvr, hBfrac, hBloc⟩ :=
    _root_.exists_isDiscreteValuationRing_isFractionRing_of_not_isField
      (R := A) (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (L := ((BigFppfOver.toScheme B S hS).obj T).residueField x)
      (IsDiscreteValuationRing.not_isField A)
  let R : Subring (((BigFppfOver.toScheme B S hS).obj T).residueField x) := Bs.toSubring
  have : IsDiscreteValuationRing R := hBdvr
  have : IsFractionRing R (((BigFppfOver.toScheme B S hS).obj T).residueField x) := hBfrac
  let φ : A →+* R := algebraMap A Bs
  have : IsLocalHom φ := hBloc
  have hring : CommRingCat.ofHom φ ≫ CommRingCat.ofHom R.subtype =
      CommRingCat.ofHom A.subtype ≫ F.residueFieldMap x :=
    CommRingCat.hom_ext <| RingHom.ext fun a ↦ (IsScalarTower.algebraMap_apply A Bs
      (((BigFppfOver.toScheme B S hS).obj T).residueField x) a).symm
  have hspec := congrArg Spec.map hring
  rw [Spec.map_comp, Spec.map_comp] at hspec
  have w : ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField x ≫
      F ≫ (BigFppfOver.toScheme B S hS).map s =
      Spec.map (CommRingCat.ofHom R.subtype) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ i₂) := by
    rw [← Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc, sq.w, ← Category.assoc]
    exact (congrArg (· ≫ i₂) hspec).symm.trans (Category.assoc _ _ _)
  obtain ⟨l, hl⟩ := exists_comp_eq_of_subsingleton_lift h hvaluative atlas c s hdiagPB (τ₀ ≫ o)
    (t ≫ pullback.snd g h) hτ x R (Spec.map (CommRingCat.ofHom φ) ≫ i₂) (by rwa [hF])
  have hφinj : Function.Injective φ := fun a b hab ↦ Subtype.ext
    ((algebraMap (((BigFppfOver.toScheme B S hS).obj W).residueField (F x))
      (((BigFppfOver.toScheme B S hS).obj T).residueField x)).injective (congrArg Subtype.val hab))
  obtain ⟨m, hm⟩ := exists_comp_eq_of_specMap_comp_eq φ hφinj
    ((BigFppfOver.toScheme B S hS).map s) i₂ l hl
  exact ⟨⟨m, (cancel_mono ((BigFppfOver.toScheme B S hS).map s)).1
    (by rw [Category.assoc, hm, sq.w]), hm⟩⟩

/-- **Stacks 0CME.** Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S`
with `Y` locally Noetherian, `f` locally of finite type and quasi-separated, `h` of finite type
and the image of `|h| : |U| → |X|` dense in `|X|`. If every commutative valuative diagram for `f`
over a discrete valuation ring `A` with fraction field `K` whose generic arrow `Spec K ⟶ X`
factors through `h` has at most one dotted arrow `Spec A ⟶ X`, then `f` is separated.

The relative diagonal of `f` is representable, a monomorphism, separated, locally of finite type,
and quasi-compact because `f` is quasi-separated. Its base change `V ⟶ C` along an étale chart
`C` of the locally Noetherian algebraic space `X ×_Y X` (Stacks 04ZK) is therefore a
quasi-compact monomorphism of schemes locally of finite type over a locally Noetherian scheme,
and it satisfies condition (4) of Stacks 0208: at a generic point of `V` a dotted arrow exists by
`nonempty_liftStruct_of_denseRange`, and it is unique since `V ⟶ C` is a monomorphism. So
`V ⟶ C` is proper (Stacks 0208), hence a closed immersion (Stacks 04XV), and being a closed
immersion descends from the chart to the diagonal (Stacks 02L6, 02WZ). -/
@[stacks 0CME]
theorem isSeparated_of_denseRange_of_subsingleton_discreteLift
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hlft : IsLocallyOfFiniteType B S hS f) (hqs : IsQuasiSeparated B S hS f)
    (hh : IsFiniteType B S hS h)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Subsingleton q.Lift) :
    IsSeparated B S hS f := by
  classical
  have hZ : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hX hX hY
  have hRep : yoneda.relativelyRepresentable (pullback.diagonal f) :=
    relativelyRepresentable_pullbackDiagonal B S hS f hX
  have hfstFT : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hlft
  have hcompFT : IsLocallyOfFiniteType B S hS (pullback.fst f f ≫ f) :=
    isLocallyOfFiniteType_comp' B S hS _ _ hX hY hfstFT hlft
  obtain ⟨C, atlas, hatlasSurj, hatlasEtale, hC⟩ :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hZ hY _ hcompFT hnoeth
  set W := hRep.pullback atlas
  set c := hRep.fst atlas
  set s := hRep.snd atlas
  have hdiagPB : IsPullback c (yoneda.map s) (pullback.diagonal f) atlas := hRep.isPullback atlas
  have hsLFT : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX).property atlas c s hdiagPB
  have hsMono : Mono ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_monomorphisms_pullbackDiagonal B S hS f hX).property atlas c s hdiagPB
  have hsQC : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map s) :=
    (presheaf_quasiCompact_of_isQuasiCompact B S hS hRep hqs).property atlas c s hdiagPB
  have hCnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj C) := hC
  have hcEtale : IsEtale B S hS c :=
    isEtale_of_isPullback_yoneda B S hS hdiagPB.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS atlas).2 hatlasEtale)
  have hsCrit : AlgebraicGeometry.GenericDiscreteValuativeCriterion
      ((BigFppfOver.toScheme B S hS).map s) := by
    intro η hη A hA hAK i₂ sq
    refine ⟨nonempty_liftStruct_of_denseRange hX hU h hh hdense hvaluative atlas c s hdiagPB
      hcEtale hsMono η hη A i₂ sq, ⟨fun a b => ?_⟩⟩
    apply CommSq.LiftStruct.ext
    apply (cancel_mono ((BigFppfOver.toScheme B S hS).map s)).1
    rw [a.fac_right, b.fac_right]
  have hsCI : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s) :=
    (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono _).2
      ⟨isProper_of_genericDiscreteValuativeCriterion _ hsCrit, hsMono⟩
  have _ : (show MorphismProperty Scheme.{u} from
      @AlgebraicGeometry.IsClosedImmersion).IsLocalAtTarget Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (presheaf_inverseImage_iff_atlas_snd B S hS
    (@AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.diagonal f) hRep C atlas
    hatlasSurj hatlasEtale).2 hsCI

end AlgebraicGeometry.Space

end
