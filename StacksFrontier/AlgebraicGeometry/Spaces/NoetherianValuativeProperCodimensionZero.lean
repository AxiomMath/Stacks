module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.GenericProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparatednessTFAE
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.Topology.Sober.Generization

/-!
# The Noetherian valuative criterion for properness at codimension-zero points

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is quasi-separated and of
finite type, with `Y` locally Noetherian. Then `f` is proper exactly when it satisfies the
valuative criterion, exactly when every valuative diagram has exactly one dotted arrow, exactly
when this holds for the diagrams over discrete valuation rings, and exactly when it holds for
the diagrams over discrete valuation rings whose generic arrow picks out a point of codimension
zero of `X` (Stacks 0H1X).

## Main results

* `AlgebraicGeometry.Space.universallyClosed_pullback_fst_of_chowCover_of_codimensionZero`: the
  affine Noetherian base case of the implication from condition (5) to universal closedness,
  with the cover of Chow's lemma taken as data.
* `AlgebraicGeometry.Space.universallyClosed_of_codimensionZeroValuativeExistence`: condition
  (5), existence half, implies universal closedness for a separated morphism.
* `AlgebraicGeometry.Space.isProper_tfae_of_isQuasiSeparated_of_codimensionZero`:
  **Stacks 0H1X**.

## Implementation notes

Conditions (1), (2) and (3) are equivalent by Stacks 0A40
(`AlgebraicGeometry.Space.isProper_tfae_of_isFiniteType_of_isQuasiSeparated`), and (3) implies
(4) implies (5) trivially. For (5) implies (1), separatedness is Stacks 0H1W
(`AlgebraicGeometry.Space.isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness`).

Universal closedness is tested on an étale covering family of the target by spectra of
Noetherian rings `T` (Stacks 03IT), exactly as in the proof of Stacks 0ARK. Over such a `T`,
Chow's lemma (Stacks 089J) gives a scheme `X'` with a proper surjective morphism
`p : X' ⟶ X ×_Y T`. As in the source, `X'` is replaced by a closed subscheme `Z` whose generic
points lie over points of codimension zero of `X`: `Z` is the closure, with its reduced induced
structure, of the generic points of `X'` whose image in `X` has codimension zero. The composite
`Z ⟶ X ×_Y T` is still surjective: its image is closed and contains every point `x` of
codimension zero, because a generic point of `X'` specializing to a preimage of `x` maps to a
generalization of `x`, which is `x` itself since `X ×_Y T` is decent (it is separated over the
affine `T`) and a codimension-zero point of a decent space has no proper generalization
(`AlgebraicGeometry.Space.eq_of_specializes_of_localRingDimension_eq_zero`); and the
points of codimension zero are dense (Stacks 0BAR). Codimension zero passes from
`X ×_Y T` to `X` along the étale projection (Stacks 0A4H).

The morphism of schemes `Z ⟶ T` is then proper by Stacks 0208 applied at the generic points of
`Z`: a discrete valuation subring of the residue field at a generic point of `Z` gives a
valuative diagram for `f` whose generic arrow picks out a point of codimension zero of `X`, the
assumed dotted arrow of that diagram is lifted through the proper morphism `Z ⟶ X ×_Y T` by the
valuative criterion of Stacks 0A40, and uniqueness comes from separatedness of `Z ⟶ T`.
Finally Stacks 08AJ pushes universal closedness down along the surjection `Z ⟶ X ×_Y T`.

## References

* [Stacks Project, Tag 0H1X](https://stacks.math.columbia.edu/tag/0H1X)
* [Stacks Project, Tag 0A40](https://stacks.math.columbia.edu/tag/0A40)
* [Stacks Project, Tag 0H1W](https://stacks.math.columbia.edu/tag/0H1W)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Lifting valuative diagrams through a proper cover -/

section Core

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The base change of a morphism of algebraic spaces along a map from a representable is an
algebraic space. -/
private theorem isAlgebraicSpace_pullback_yoneda
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (T : BigFppfOver B S hS) (φ : yoneda.obj T ⟶ Y) : IsAlgebraicSpace B S hS (pullback φ f) :=
  isAlgebraicSpace_pullback B S hS φ f (isAlgebraicSpace_yoneda B S hS _) hX hY

/-- The first projection of a base change of a separated morphism of finite type is separated
and of finite type. -/
private theorem isSeparated_and_isFiniteType_pullback_fst
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : T ⟶ Y) :
    IsSeparated B S hS (pullback.fst φ f) ∧ IsFiniteType B S hS (pullback.fst φ f) :=
  ⟨isSeparated_pullback_fst_of_snd B S hS f φ (isSeparated_pullback B S hS f φ hsep),
    IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback φ f) hX hY hft⟩

/-- **A valuative diagram of a scheme over the chart, lifted through a proper cover.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `φ` a morphism to `Y` from the presheaf
represented by a chart `T`, and `p` a proper morphism to `X ×_Y T` from the presheaf represented
by an object `X'` of the site over `T`. A valuative diagram for the scheme morphism `X' ⟶ T`
over a discrete valuation ring whose generic point maps to a point of codimension zero of `X`
gives a valuative diagram for `f` of the kind of condition (5) of Stacks 0H1X; if every such
diagram for `f` has a dotted arrow, the diagram for `X' ⟶ T` has one too, by the valuative
criterion of Stacks 0A40 for `p`. -/
theorem hasLift_of_codimensionZeroLift
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      localRingDimension B S hS q.genericPoint = 0 → Nonempty q.Lift)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y)
    (X' : BigFppfOver B S hS) (ψ : X' ⟶ siteObject B S hS hA a)
    (p : yoneda.obj X' ⟶ pullback φ f) (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (D : _root_.AlgebraicGeometry.ValuativeCommSq ((BigFppfOver.toScheme B S hS).map ψ))
    (hDVR : IsDiscreteValuationRing D.R) (hR : B.Contains (Spec (.of D.R)))
    (hK : B.Contains (Spec (.of D.K)))
    (hcodim : localRingDimension B S hS
      (pointsMap B S hS (yoneda.obj X') (p ≫ pullback.snd φ f)
        ((schemePointsHomeomorph B S hS X').symm (D.i₁ (IsLocalRing.closedPoint D.K)))) = 0) :
    D.commSq.HasLift := by
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (siteObject B S hS hA a)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  have hXT := isAlgebraicSpace_pullback_yoneda B S hS hX hY f _ φ
  let baseR : Spec (.of D.R) ⟶ S := D.i₂ ≫ a
  let Robj : BigFppfOver B S hS := siteObject B S hS hR baseR
  let Kobj : BigFppfOver B S hS :=
    siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ baseR)
  let ιsite : Kobj ⟶ Robj :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) : B.obj hK ⟶ B.obj hR)
  let aT : Robj ⟶ siteObject B S hS hA a :=
    Over.homMk (ObjectProperty.homMk D.i₂ : B.obj hR ⟶ B.obj hA) (by rfl)
  -- the structure morphism of `X'` factors through that of `T`
  have hX'hom : (B.inclusion).map X'.hom =
      (BigFppfOver.toScheme B S hS).map ψ ≫ a := by
    conv_lhs => rw [← Over.w ψ]
    exact (B.inclusion).map_comp _ _
  let kX' : Kobj ⟶ X' :=
    Over.homMk (ObjectProperty.homMk D.i₁ : B.obj hK ⟶ X'.left) (by
      apply ObjectProperty.hom_ext
      show D.i₁ ≫ (B.inclusion).map X'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ baseR
      rw [hX'hom, ← Category.assoc, D.commSq.w, Category.assoc])
  have hιaT : ιsite ≫ aT = kX' ≫ ψ := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    show Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ =
      D.i₁ ≫ (BigFppfOver.toScheme B S hS).map ψ
    exact D.commSq.w.symm
  -- the valuative square for `f` obtained by composing
  let q₁ : ValuativeSquare f :=
    { R := D.R
      K := D.K
      ring_mem := hR
      field_mem := hK
      base := baseR
      generic := yoneda.map kX' ≫ p ≫ pullback.snd φ f
      special := yoneda.map aT ≫ φ
      comm := by
        calc (yoneda.map kX' ≫ p ≫ pullback.snd φ f) ≫ f
            = yoneda.map kX' ≫ p ≫ pullback.fst φ f ≫ φ := by
              rw [Category.assoc, Category.assoc, ← pullback.condition]
          _ = yoneda.map (ιsite ≫ aT) ≫ φ := by
              rw [← Category.assoc p, hpψ, ← Category.assoc, ← yoneda.map_comp, hιaT]
          _ = _ := by rw [yoneda.map_comp, Category.assoc] }
  -- its generic arrow picks out a point of codimension zero
  let pK : FieldValuedPoint B S hS (yoneda.obj X') :=
    { carrier := D.K
      contained := hK
      toBase := Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ baseR
      value := yonedaEquiv (yoneda.map kX') }
  have hcl : pK.class B S hS (yoneda.obj X') =
      (schemePointsHomeomorph B S hS X').symm (D.i₁ (IsLocalRing.closedPoint D.K)) := by
    apply (schemePointsHomeomorph B S hS X').injective
    rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply, pointsToScheme_class]
    show (BigFppfOver.toScheme B S hS).map (yonedaEquiv (yoneda.map kX')) _ = _
    rw [yonedaEquiv_yoneda_map]
    rfl
  have hgp : q₁.genericPoint = pointsMap B S hS (yoneda.obj X') (p ≫ pullback.snd φ f)
      ((schemePointsHomeomorph B S hS X').symm (D.i₁ (IsLocalRing.closedPoint D.K))) := by
    rw [← hcl, pointsMap_class]
    rfl
  obtain ⟨L⟩ := hlift q₁ hDVR (hgp ▸ hcodim)
  -- the lift into the fibre product
  have hLsq : yoneda.map aT ≫ φ = L.map ≫ f := L.special_comm.symm
  let c : yoneda.obj Robj ⟶ pullback φ f :=
    pullback.lift (yoneda.map aT) L.map hLsq
  have hcfst : c ≫ pullback.fst φ f = yoneda.map aT := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd φ f = L.map := pullback.lift_snd _ _ _
  have hcι : yoneda.map ιsite ≫ c = yoneda.map kX' ≫ p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hcfst, ← yoneda.map_comp, hιaT, yoneda.map_comp,
        Category.assoc, hpψ]
    · rw [Category.assoc, hcsnd, L.generic_comm]
      rfl
  -- the valuative square for the proper morphism `p`
  let q₂ : ValuativeSquare p :=
    { R := D.R
      K := D.K
      ring_mem := hR
      field_mem := hK
      base := baseR
      generic := yoneda.map kX'
      special := c
      comm := hcι.symm }
  have hunique := (isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated
    hX' hXT p hp.2.1 (isQuasiSeparated_of_isSeparated B S hS hp.1)).mp hp
  obtain ⟨M⟩ := (hunique q₂).1
  let m : Robj ⟶ X' := yoneda.preimage M.map
  have hm : yoneda.map m = M.map := yoneda.map_preimage _
  have hmψ : m ≫ ψ = aT := by
    apply Yoneda.fullyFaithful.map_injective (F := yoneda)
    rw [yoneda.map_comp, hm, ← hpψ, ← Category.assoc, M.special_comm, hcfst]
  have hmι : ιsite ≫ m = kX' := by
    apply Yoneda.fullyFaithful.map_injective (F := yoneda)
    rw [yoneda.map_comp, hm]
    exact M.generic_comm
  refine ⟨⟨(BigFppfOver.toScheme B S hS).map m, ?_, ?_⟩⟩
  · rw [show Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) =
      (BigFppfOver.toScheme B S hS).map ιsite from rfl,
      ← (BigFppfOver.toScheme B S hS).map_comp, hmι]
    rfl
  · show (BigFppfOver.toScheme B S hS).map m ≫
      (BigFppfOver.toScheme B S hS).map ψ = D.i₂
    rw [← (BigFppfOver.toScheme B S hS).map_comp, hmψ]
    rfl

/-- **The affine Noetherian base case of (5) implies universal closedness in Stacks 0H1X, with
the Chow cover taken as data.**

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces of finite type such that every
valuative diagram for `f` over a discrete valuation ring whose generic arrow picks out a point
of codimension zero of `X` has a dotted arrow, and let `φ` be an étale morphism to `Y` from the
presheaf represented by the spectrum of a Noetherian ring. If the base change of `f` along `φ`
receives a proper surjective morphism `p` from the presheaf represented by an object `X'` of the
site, over that chart, with `X' ⟶ Spec A` quasi-compact, then the base change of `f` along `φ`
is universally closed.

The cover `X'` is cut down to the closure `Z` of its generic points lying over points of
codimension zero of `X`, with its reduced induced structure; `Z` still covers the base change,
and `Z ⟶ Spec A` is proper by Stacks 0208. -/
theorem universallyClosed_pullback_fst_of_chowCover_of_codimensionZero
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S) [IsNoetherianRing A]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      localRingDimension B S hS q.genericPoint = 0 → Nonempty q.Lift)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y) (hφ : IsEtale B S hS φ)
    (X' : BigFppfOver B S hS) (ψ : X' ⟶ siteObject B S hS hA a)
    (p : yoneda.obj X' ⟶ pullback φ f)
    (hp : IsProper B S hS p) (hpsurj : IsSurjective B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (hqc : _root_.AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ψ)) :
    UniversallyClosed B S hS (pullback.fst φ f) := by
  classical
  have : _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS hA a)) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsNoetherian (Spec A))
  have hT : IsAlgebraicSpace B S hS (yoneda.obj (siteObject B S hS hA a)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  have hXT := isAlgebraicSpace_pullback_yoneda B S hS hX hY f _ φ
  obtain ⟨hsepT, hftT⟩ := isSeparated_and_isFiniteType_pullback_fst B S hS hX hY f hft hsep φ
  -- the projection to `X` is étale
  have hsndEt : IsEtale B S hS (pullback.snd φ f) := by
    let Tsp : AlgebraicSpaces B S hS := ⟨_, hT⟩
    let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let φsp : Tsp ⟶ Ysp := ObjectProperty.homMk φ
    let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
    let Wsp := AlgebraicSpaces.fiberProduct B S hS φsp fsp
    let p₁ : Wsp ⟶ Tsp := ObjectProperty.homMk (pullback.fst φsp.hom fsp.hom)
    let p₂ : Wsp ⟶ Xsp := ObjectProperty.homMk (pullback.snd φsp.hom fsp.hom)
    have hpull : IsPullback p₁ p₂ φsp fsp := by
      simpa [p₁, p₂] using AlgebraicSpaces.isPullback_fiberProduct B S hS φsp fsp
    have h := isEtale_of_isPullback B S hS p₁ p₂ φsp fsp hpull hφ
    simpa [p₂, Wsp, AlgebraicSpaces.fiberProduct, φsp, fsp] using h
  -- the base change is decent, being separated over an affine scheme
  have hdec : IsDecentSpace B S hS (pullback φ f) :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS _ hXT
      (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS B.contains_terminal _
        (isAbsolutelySeparated_of_isSeparated_to_affine B S hS B.contains_terminal
          (siteObject B S hS hA a) (inferInstanceAs (IsAffine (Spec A))) _ hsepT))
  -- the scheme `X'` is Noetherian
  have hlftSpace : IsLocallyOfFiniteType B S hS (yoneda.map ψ) := by
    rw [← hpψ]
    exact isLocallyOfFiniteType_comp B S hS hX' hXT hT p (pullback.fst φ f) hp.2.1.1 hftT.1
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map ψ) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS ψ).mp hlftSpace
  have : _root_.AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ψ) := hqc
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X') :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map ψ)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj X') :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map ψ)
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj X') := ⟨⟩
  -- the generic points of `X'` over points of codimension zero of `X`, and their closure
  set pt := (schemePointsHomeomorph B S hS X').symm with hptdef
  set E : Set ((BigFppfOver.toScheme B S hS).obj X') :=
    {v | v ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj X') ∧
      localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj X') (p ≫ pullback.snd φ f) (pt v)) = 0} with hEdef
  have hEfin : E.Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).subset
      fun v hv ↦ hv.1
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure E, isClosed_closure⟩ : Closeds ((BigFppfOver.toScheme B S hS).obj X')) with hIdef
  set ι := I.subschemeι with hιdef
  have hrange : Set.range ι = closure E := by
    rw [hιdef, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hZc : B.Contains I.subscheme := BigFppfSite.contains_of_mono B ι X'.left.property
  let Zobj : BigFppfOver B S hS := siteObject B S hS hZc (ι ≫ (B.inclusion).map X'.hom)
  let ιsite : Zobj ⟶ X' :=
    Over.homMk (ObjectProperty.homMk ι : B.obj hZc ⟶ X'.left) (by rfl)
  have hιsite : (BigFppfOver.toScheme B S hS).map ιsite = ι := rfl
  -- the generic points of `Z` lie in `E`
  have hgenE : ∀ η ∈ genericPoints I.subscheme, ι η ∈ E := by
    intro η hη
    have hmem : ι η ∈ closure E := hrange ▸ Set.mem_range_self η
    have hcl : closure E = ⋃ e ∈ E, closure ({e} : Set _) := by
      conv_lhs => rw [← Set.biUnion_of_singleton E]
      exact hEfin.closure_biUnion _
    rw [hcl] at hmem
    obtain ⟨e, he, hee⟩ := Set.mem_iUnion₂.mp hmem
    have hspec : e ⤳ ι η := specializes_iff_mem_closure.mpr hee
    obtain ⟨ζ, rfl⟩ : e ∈ Set.range ι := hrange ▸ subset_closure he
    have hζη : ζ ⤳ η := ι.isClosedEmbedding.isInducing.specializes_iff.mp hspec
    rw [← TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hη ζ hζη]
    exact he
  -- the cover restricted to `Z`
  set pZ : yoneda.obj Zobj ⟶ pullback φ f := yoneda.map ιsite ≫ p with hpZdef
  set ψZ : Zobj ⟶ siteObject B S hS hA a := ιsite ≫ ψ with hψZdef
  have hpZψ : pZ ≫ pullback.fst φ f = yoneda.map ψZ := by
    rw [hpZdef, hψZdef, Category.assoc, hpψ, yoneda.map_comp]
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj Zobj) := isAlgebraicSpace_yoneda B S hS Zobj
  have hpZ : IsProper B S hS pZ := by
    refine isProper_comp B S hS hZ hX' hXT _ p ?_ hp
    refine isProper_yoneda_map B S hS ιsite ?_
    rw [hιsite]
    infer_instance
  -- it is still surjective
  have hpZsurj : IsSurjective B S hS pZ := by
    have hclosedmap : IsClosedMap (pointsMap B S hS (yoneda.obj X') p) :=
      isClosedMap_pointsMap_of_pullback_fst_id B S hS p (hp.2.2 _ hXT (𝟙 _))
    set Im := pointsMap B S hS (yoneda.obj X') p '' (pt '' closure E) with hImdef
    have hImclosed : IsClosed Im :=
      hclosedmap _ (pt.isClosedMap _ isClosed_closure)
    have hcodimIm : ∀ x : points B S hS (pullback φ f),
        localRingDimension B S hS x = 0 → x ∈ Im := by
      intro x hx
      obtain ⟨x', rfl⟩ := hpsurj x
      set v := schemePointsHomeomorph B S hS X' x' with hvdef
      obtain ⟨ξ, hξ, hξv⟩ : ∃ ξ ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj X'),
          ξ ⤳ v := by
        let Zc : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj X') :=
          ⟨irreducibleComponent v, irreducibleComponent_mem_irreducibleComponents v⟩
        exact ⟨genericPoints.ofComponent Zc, (genericPoints.ofComponent Zc).2,
          (genericPoints.isGenericPoint_ofComponent Zc).specializes mem_irreducibleComponent⟩
      have h1 : pt ξ ⤳ x' := by
        have h := hξv.map pt.continuous
        rwa [hvdef, hptdef, Homeomorph.symm_apply_apply] at h
      have h2 := h1.map (continuous_pointsMap B S hS p)
      have h3 := eq_of_specializes_of_localRingDimension_eq_zero B S hS hXT hdec hx _ h2
      refine ⟨pt ξ, ⟨ξ, subset_closure ⟨hξ, ?_⟩, rfl⟩, h3⟩
      rw [pointsMap_comp, Function.comp_apply, h3,
        localRingDimension_pointsMap_of_etale B S hS hXT hX _ hsndEt]
      exact hx
    have hsub : closure {x : points B S hS (pullback φ f) |
        localRingDimension B S hS x = 0} ⊆ Im := closure_minimal hcodimIm hImclosed
    rw [(codimensionZeroPoints_dense B S hS hXT).closure_eq] at hsub
    intro x
    obtain ⟨_, ⟨v, hv, rfl⟩, hvx⟩ := hsub (Set.mem_univ x)
    rw [← hrange] at hv
    obtain ⟨z, rfl⟩ := hv
    refine ⟨(schemePointsHomeomorph B S hS Zobj).symm z, ?_⟩
    rw [← hvx, hpZdef, pointsMap_comp, Function.comp_apply,
      schemePointsHomeomorph_symm_naturality, hιsite]
  -- `Z ⟶ Spec A` is separated, locally of finite type and quasi-compact
  have hsepZ : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map ψZ) := by
    rw [← isSeparated_yoneda_map_iff B S hS ψZ, ← hpZψ]
    exact isSeparated_comp B S hS pZ (pullback.fst φ f) hpZ.1 hsepT
  have hψZ : (BigFppfOver.toScheme B S hS).map ψZ =
      ι ≫ (BigFppfOver.toScheme B S hS).map ψ := by
    rw [hψZdef, Functor.map_comp, hιsite]
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map ψZ) := by
    rw [hψZ]; infer_instance
  have : _root_.AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ψZ) := by
    rw [hψZ]; infer_instance
  -- condition (4) of Stacks 0208 for `Z ⟶ Spec A`
  have hcrit : GenericDiscreteValuativeCriterion ((BigFppfOver.toScheme B S hS).map ψZ) := by
    intro η hη A' hDVR hfrac i₂ sq
    have := hDVR
    have := hfrac
    have hKmem : B.Contains
        (Spec (.of (((BigFppfOver.toScheme B S hS).obj Zobj).residueField η : Type u))) :=
      B.residueField_spec_contains hZc η
    have hAmem : B.Contains (Spec (.of (A' : Type u))) :=
      Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A' hKmem
    have hsub : algebraMap A' (((BigFppfOver.toScheme B S hS).obj Zobj).residueField η : Type u) =
        A'.subtype := rfl
    let D : _root_.AlgebraicGeometry.ValuativeCommSq ((BigFppfOver.toScheme B S hS).map ψZ) :=
      { R := A'
        K := (((BigFppfOver.toScheme B S hS).obj Zobj).residueField η : Type u)
        i₁ := ((BigFppfOver.toScheme B S hS).obj Zobj).fromSpecResidueField η
        i₂ := i₂
        commSq := ⟨by rw [hsub]; exact sq.w⟩ }
    have hcodimD : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj Zobj) (pZ ≫ pullback.snd φ f)
          ((schemePointsHomeomorph B S hS Zobj).symm
            (D.i₁ (IsLocalRing.closedPoint D.K)))) = 0 := by
      have hpt : D.i₁ (IsLocalRing.closedPoint D.K) = η :=
        Scheme.fromSpecResidueField_apply _ _
      rw [hpt, hpZdef, Category.assoc, pointsMap_comp, Function.comp_apply,
        schemePointsHomeomorph_symm_naturality, hιsite]
      exact (hgenE η hη).2
    have hlift' := hasLift_of_codimensionZeroLift B S hS A hA a hX hY f hlift φ Zobj ψZ pZ hpZ
      hpZψ D hDVR hAmem hKmem hcodimD
    exact ⟨hlift'.exists_lift,
      _root_.AlgebraicGeometry.IsSeparated.valuativeCriterion
        (f := (BigFppfOver.toScheme B S hS).map ψZ) D⟩
  have hprop : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ψZ) :=
    isProper_of_genericDiscreteValuativeCriterion _ hcrit
  have hucSpace : UniversallyClosed B S hS (pZ ≫ pullback.fst φ f) := by
    rw [hpZψ]
    exact universallyClosed_yoneda_map B S hS ψZ inferInstance
  exact universallyClosed_of_isSurjective_comp B S hS hZ hXT hT pZ (pullback.fst φ f)
    hucSpace hpZsurj

/-- **Condition (5) of Stacks 0H1X, existence half, gives universal closedness.** Let
`f : X ⟶ Y` be a separated morphism of algebraic spaces over `S` of finite type with `Y`
locally Noetherian. If every valuative diagram for `f` over a discrete valuation ring whose
generic arrow picks out a point of codimension zero of `X` has a dotted arrow, then `f` is
universally closed.

Universal closedness is tested on an étale covering family of `Y` by spectra of Noetherian
rings (Stacks 03IT), and over each member Chow's lemma (Stacks 089J) supplies the cover used by
`AlgebraicGeometry.Space.universallyClosed_pullback_fst_of_chowCover_of_codimensionZero`. -/
theorem universallyClosed_of_codimensionZeroValuativeExistence
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hlift : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      localRingDimension B S hS q.genericPoint = 0 → Nonempty q.Lift) :
    UniversallyClosed B S hS f := by
  obtain ⟨I, A, hA, a, φ, hNR, -, hEtale, hCover⟩ :=
    exists_spec_isLocallyNoetherian_etale_covering_family B S hS hY hNoeth
  refine universallyClosed_of_etale_covering_family B S hS hY f
    (fun i ↦ siteObject B S hS (hA i) (a i)) φ hEtale hCover ?_
  intro i
  have := hNR i
  have hXT := isAlgebraicSpace_pullback_yoneda B S hS hX hY f _ (φ i)
  obtain ⟨hsepT, hftT⟩ := isSeparated_and_isFiniteType_pullback_fst B S hS hX hY f hft hsep (φ i)
  obtain ⟨X', ψ, p, hp, hpsurj, hpψ, hqp⟩ :=
    exists_chowSchemeCover_over_spec B S hS (A i) (hA i) (a i) hXT
      (pullback.fst (φ i) f) hsepT hftT
  exact universallyClosed_pullback_fst_of_chowCover_of_codimensionZero B S hS (A i) (hA i) (a i)
    hX hY f hft hsep hlift (φ i) (hEtale i) X' ψ p hp hpsurj hpψ
    (quasiCompact_of_isHQuasiProjective hqp)

/-- **Stacks 0H1X.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
quasi-separated and of finite type, with `Y` locally Noetherian. The following are equivalent:
1. `f` is proper;
2. `f` satisfies the valuative criterion (Stacks 03IX);
3. every valuative diagram (Stacks 0H1V) for `f` has exactly one dotted arrow;
4. every valuative diagram for `f` whose valuation ring is a discrete valuation ring has
   exactly one dotted arrow;
5. every valuative diagram for `f` whose valuation ring is a discrete valuation ring and whose
   generic arrow `Spec K ⟶ X` picks out a point of codimension zero of `X` has exactly one
   dotted arrow.

Conditions (1) to (3) are equivalent by Stacks 0A40, and (3) implies (4) implies (5) trivially.
Given (5), `f` is separated by Stacks 0H1W
(`AlgebraicGeometry.Space.isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness`)
and universally closed by
`AlgebraicGeometry.Space.universallyClosed_of_codimensionZeroValuativeExistence`. -/
@[stacks 0H1X]
theorem isProper_tfae_of_isQuasiSeparated_of_codimensionZero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    List.TFAE
      [ IsProper B S hS f,
        ValuativeCriterion f,
        ∀ q : ValuativeSquare f, Nonempty q.Lift ∧ Subsingleton q.Lift,
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          Nonempty q.Lift ∧ Subsingleton q.Lift,
        ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
          localRingDimension B S hS q.genericPoint = 0 →
            Nonempty q.Lift ∧ Subsingleton q.Lift ] := by
  have h0A40 := isProper_tfae_of_isFiniteType_of_isQuasiSeparated hX hY f hft hqs
  tfae_have 1 ↔ 2 := h0A40.out 1 2
  tfae_have 1 ↔ 3 := h0A40.out 1 3
  tfae_have 3 → 4 := fun h q _ ↦ h q
  tfae_have 4 → 5 := fun h q hq _ ↦ h q hq
  tfae_have 5 → 1 := by
    intro h
    have hsep : IsSeparated B S hS f :=
      isSeparated_of_isLocallyOfFiniteType_of_codimensionZeroUniqueness hX hY f hqs hft.1
        hNoeth (fun q hq h0 ↦ (h q hq h0).2)
    exact ⟨hsep, hft, universallyClosed_of_codimensionZeroValuativeExistence B S hS hX hY f
      hNoeth hft hsep (fun q hq h0 ↦ (h q hq h0).1)⟩
  tfae_finish

end Core

end AlgebraicGeometry.Space

end
