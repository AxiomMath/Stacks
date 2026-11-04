module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionDeformationScheme
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableContractionTransport
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation

/-!
# Deforming the contraction of a fibre of a family of curves (Stacks 0E7C)

Let `X ⟶ S` be a family of curves, `s ∈ S`, and let `m₀ : V ⟶ W₀` be a stable contraction (the
conditions of [Stacks, Tag 0E7Q]) of the fibre `V` of `X` at the residue field of `s`. Then there
are an étale morphism `t : U ⟶ S` with a point `u` over `s`, a family of curves `Y ⟶ U` and a
morphism `h : X_U ⟶ Y` over `U` whose fibres at every field-valued point over `u` are stable
contractions. This is [Stacks, Tag 0E7C] for families of curves, in the form consumed by the
proof of [Stacks, Tag 0E8A] (`AlgebraicGeometry.C1590Private.FibresStableContractionsAt`).

The proof: étale locally on `S` the family is a scheme ([Stacks, Tag 0E6F], the hypothesis
`h0E6F`); on an affine scheme chart the scheme case
(`ContractionDeformation.exists_etale_contraction_of_isAffine_of_fiberDimension`) deforms the
base change of `m₀` to the residue field of a point of the chart, over an étale neighbourhood
with a point of the same residue field, and the fibres at every field-valued point over it are
base changes of `m₀`, hence stable contractions (`isStableContraction_of_isPullback_baseChange`).

## Main results

* `AlgebraicGeometry.C1590Private.curveFamilyOfFiberDimension`: a proper flat morphism of finite
  presentation of schemes of the site with fibres of dimension at most one, as a family of curves.
* `AlgebraicGeometry.C1590Private.isIso_of_specMap_fromSpecResidueField_comp`: a lift of a
  residue field point has the same residue field.
* `AlgebraicGeometry.C1590Private.exists_etale_contraction_of_fibre`: the statement above.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

/-! ### Families of curves from morphisms of schemes with one-dimensional fibres -/

/-- The germ of a morphism of schemes at a point whose fibre has dimension at most `n` has fibre
dimension a natural number at most `n`. -/
theorem exists_hasFiberDimensionAt_ofSchemeHom_of_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (hdim : f.fiberDimension (f x) ≤ ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ n ∧ HasFiberDimensionAt (e : ℕ∞) (MorphismOfGerms.ofSchemeHom f x) := by
  set h : ((⊤ : X.Opens) : Scheme.{u}) ⟶ Y := X.topIso.hom ≫ f
  set z : ((⊤ : X.Opens) : Scheme.{u}) := ⟨x, by simp⟩
  have hsq : IsPullback X.topIso.hom h f (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
  have e1 := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback hsq) (h z)
  have e2 : (𝟙 Y : Y ⟶ Y) (h z) = f x := rfl
  have hle : topologicalKrullDimAt (h.fiber (h z)) (h.asFiber z) ≤ f.fiberDimension (f x) := by
    have := Scheme.Hom.topologicalKrullDimAt_fiber_le_fiberDimension h (rfl : h z = h z)
    rwa [e1, Function.comp_apply, e2] at this
  have hnat : ∀ d : WithBot ℕ∞, 0 ≤ d → d ≤ ((n : ℕ∞) : WithBot ℕ∞) →
      ∃ e : ℕ, e ≤ n ∧ d = ((e : ℕ∞) : WithBot ℕ∞) := by
    intro d h0 hn
    have hbot : d ≠ ⊥ := by
      rintro rfl
      simp at h0
    obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.1 hbot
    have hcn : c ≤ (n : ℕ∞) := WithBot.coe_le_coe.1 hn
    have htop : c ≠ ⊤ := by
      rintro rfl
      simp at hcn
    obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.1 htop
    exact ⟨m, ENat.natCast_le_natCast.mp hcn, rfl⟩
  obtain ⟨e, hen, hee⟩ := hnat _
    (topologicalKrullDimAt_nonneg (h.asFiber z)) (hle.trans hdim)
  exact ⟨e, hen, { source := ⊤
                   mem_source := by simp
                   hom := X.topIso.hom ≫ f
                   map_point := rfl }, rfl, hee⟩

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The relative-dimension condition of Stacks 0D4Z from the dimension of the fibres.** A
morphism of the site over `ℤ` whose fibres have dimension at most `n` induces a morphism of
algebraic spaces of relative dimension at most `n`. -/
theorem relativeDimensionLE_schemeSpaceMap_of_fiberDimension {T U : BigFppfOver B integerBase hZ}
    (g : T ⟶ U) [LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g)] (n : ℕ)
    (hdim : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map g).fiberDimension y ≤
      ((n : ℕ∞) : WithBot ℕ∞))
    (x : Space.points B integerBase hZ (schemeSpace T).obj) :
    ∃ e : ℕ, e ≤ n ∧
      Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (schemeSpaceMap g).hom x := by
  obtain ⟨e, hen, hee⟩ := exists_hasFiberDimensionAt_ofSchemeHom_of_fiberDimension
    ((BigFppfOver.toScheme B integerBase hZ).map g) (Space.pointsToScheme B integerBase hZ T x) n
    (hdim _)
  exact ⟨e, hen, (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ
    (@HasFiberDimensionAt.{u} (e : ℕ∞)) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞))
    g x).2 hee⟩

/-- **A family of curves from a morphism of schemes with fibres of dimension at most one.** A
flat proper morphism of finite presentation `g : T ⟶ U` of the site over `ℤ` whose fibres have
dimension at most one. -/
def curveFamilyOfFiberDimension {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : ∀ y, ((BigFppfOver.toScheme B integerBase hZ).map g).fiberDimension y ≤
      ((1 : ℕ∞) : WithBot ℕ∞)) :
    CurveFamily B hZ where
  base := U
  total := schemeSpace T
  toBase := schemeSpaceMap g
  flat := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget g).2 hflat
  proper := by
    refine ⟨(Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance,
      ⟨?_, Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance⟩, ?_⟩
    · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget g).2 inferInstance
    · have hrep : yoneda.relativelyRepresentable (yoneda.map g) :=
        Functor.relativelyRepresentable.map _ _
      exact (Space.presheaf_universallyClosed_iff B integerBase hZ
          (isAlgebraicSpace_yoneda B integerBase hZ T)
          (isAlgebraicSpace_yoneda B integerBase hZ U) hrep).1
        (Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ
          (P := @UniversallyClosed.{u}) inferInstance g inferInstance)
  finitePresentation :=
    ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).2 hlfp,
      Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance,
      (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance⟩
  relativeDimensionLE := relativeDimensionLE_schemeSpaceMap_of_fiberDimension g 1 hdim

/-! ### Lifts of residue field points -/

/-- **A lift of a residue field point has the same residue field.** Let `φ : U ⟶ S` map `x` to
`s`, and let `β : κ(x) ⟶ K` and an isomorphism `γ : κ(s) ⟶ K` define the same morphism
`Spec K ⟶ S` through `x` and `s`. Then `β` is an isomorphism. -/
theorem isIso_of_specMap_fromSpecResidueField_comp {K : Type u} [Field K] {U S : Scheme.{u}}
    (φ : U ⟶ S) (x : U) (s : S) (hx : φ x = s)
    (β : CommRingCat.of (U.residueField x) ⟶ CommRingCat.of K)
    (γ : CommRingCat.of (S.residueField s) ⟶ CommRingCat.of K) [IsIso γ]
    (h : Spec.map β ≫ U.fromSpecResidueField x ≫ φ = Spec.map γ ≫ S.fromSpecResidueField s) :
    IsIso β := by
  subst hx
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, cancel_mono] at h
  have h2 : φ.residueFieldMap x ≫ β = γ := Spec.map_injective h
  have hsurj : Function.Surjective β := fun y => by
    obtain ⟨z, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective γ).1 inferInstance).2 y
    exact ⟨φ.residueFieldMap x z, by
      rw [← h2]
      rfl⟩
  exact (ConcreteCategory.isIso_iff_bijective β).2 ⟨β.hom.injective, hsurj⟩

/-- A pullback square over `g = χ ≫ t` lifts through a pullback square over `t` to a pullback
square over `χ`. -/
private theorem isPullback_lift_comp_of_isPullback {C : Type*} [Category C] {A X P U Q S : C}
    {a : A ⟶ X} {b : A ⟶ P} {f : X ⟶ U} {t : P ⟶ U} (hab : IsPullback a b f t) {x : Q ⟶ X}
    {y : Q ⟶ S} {g : S ⟶ U} {χ : S ⟶ P} (hχ : χ ≫ t = g) (hxy : IsPullback x y f g) :
    IsPullback (hab.lift x (y ≫ χ) (by rw [hxy.w, Category.assoc, hχ])) y b χ := by
  refine IsPullback.of_right ?_ (hab.lift_snd _ _ _) hab
  rw [hab.lift_fst, hχ]
  exact hxy

/-! ### The deformation of the contraction of a fibre -/

open Stacks.Curves.StableModel ContractionDeformation in
/-- **Deforming the contraction of a fibre of a family of curves** ([Stacks, Tag 0E7C]). Let `X`
be a family of curves, `s` a point of its base and `P` a field-valued point of the base whose
field is the residue field of `s`. Let `V ⟶ X` present the fibre at `P`, of dimension at most one
with `H⁰(V, 𝒪_V) = κ(s)`, and let `m₀ : V ⟶ W₀` be a stable contraction over `P`. Then there are
an étale `t : U ⟶ S` with a point `u` over `s`, a family of curves `Y` over `U`, a presentation
`A` of the base change of `X` to `U` and a morphism `h : A ⟶ Y` over `U` whose fibres at every
field-valued point over `u` are stable contractions.

The étale-local scheme charts of families of curves ([Stacks, Tag 0E6F]) are the hypothesis
`h0E6F` (not yet proved here). -/
theorem exists_etale_contraction_of_fibre (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (X : CurveFamily B hZ) (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hP : ∃ e : CommRingCat.of
        ((BigFppfOver.toScheme B integerBase hZ).obj X.base |>.residueField s) ⟶
        CommRingCat.of P.carrier,
      IsIso e ∧ Spec.map e ≫
          ((BigFppfOver.toScheme B integerBase hZ).obj X.base).fromSpecResidueField s =
        (BigFppfOver.toScheme B integerBase hZ).map P.value)
    ⦃V W₀ : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject)
    (q : yoneda.obj V ⟶ X.total.obj)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (w₀ : W₀ ⟶ P.siteObject) (m₀ : V ⟶ W₀) (hm₀ : m₀ ≫ w₀ = v)
    (hc : IsStableContraction ((BigFppfOver.toScheme B integerBase hZ).map v)
      ((BigFppfOver.toScheme B integerBase hZ).map w₀)
      ((BigFppfOver.toScheme B integerBase hZ).map m₀))
    (hdimV : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1)
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫
      ((BigFppfOver.toScheme B integerBase hZ).map v).appTop)) :
    ∃ (Y : CurveFamily B hZ) (t : Y.base ⟶ X.base)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      (BigFppfOver.toScheme B integerBase hZ).map t u = s ∧
      ∃ (A : AlgebraicSpaces B integerBase hZ) (iA : A ⟶ X.total) (pA : A ⟶ schemeSpace Y.base),
        IsPullback iA pA X.toBase (schemeSpaceMap t) ∧
        ∃ h : A ⟶ Y.total, h ≫ Y.toBase = pA ∧ FibresStableContractionsAt Y pA h u := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨φK, _, hφK⟩ := hP
  have hdimV' : topologicalKrullDim (T.obj V) ≤ ((1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdimV
  -- the fibre `V`
  let pv : P.siteObject ⟶ X.base := P.value
  have hq0 : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map pv) := by
    rwa [yonedaEquiv_symm_value] at hq
  have hqA := isPullback_homMk_of_isPullback _ v q hq0
  have : IsProper (T.map v) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hqA
  have : IsProper (T.map w₀) := hc.isProper
  have : IsProper (T.map m₀) := by
    have : IsProper (T.map m₀ ≫ T.map w₀) := by
      rw [← Functor.map_comp, hm₀]
      infer_instance
    exact IsProper.of_comp (T.map m₀) (T.map w₀)
  -- a scheme chart, restricted to an affine neighbourhood
  obtain ⟨U₀, Z, φ₀, qZ, pZ, hφ₀, ⟨u₀, hu₀⟩, sqZ⟩ := h0E6F X s
  obtain ⟨W, hW, hu₀W, -⟩ := exists_isAffineOpen_mem_and_subset (x := u₀) (U := ⊤) trivial
  have hWc : B.Contains W.toScheme := Scheme.size_lt_of_isOpenImmersion W.ι U₀.left.2
  let U₁ := BigFppfOver.siteObjectOver B integerBase hZ U₀ hWc W.ι
  let eW : U₁ ⟶ U₀ := BigFppfOver.siteMapOver B integerBase hZ U₀ hWc W.ι
  have : IsAffine (T.obj U₁) := hW
  let u₁ : T.obj U₁ := ⟨u₀, hu₀W⟩
  let φ₁ := eW ≫ φ₀
  have : Etale (T.map φ₀) := hφ₀
  have : Etale (T.map φ₁) := by
    rw [Functor.map_comp]
    exact inferInstanceAs (Etale (W.ι ≫ T.map φ₀))
  have hu₁ : T.map φ₁ u₁ = s := by
    rwa [Functor.map_comp, Scheme.Hom.comp_apply]
  let qZ₁ := pullback.snd qZ eW
  have sqZ₁ : IsPullback (schemeSpaceMap (pullback.fst qZ eW) ≫ pZ) (schemeSpaceMap qZ₁)
      X.toBase (schemeSpaceMap φ₁) := by
    have := (isPullback_schemeSpaceMap (IsPullback.of_hasPullback qZ eW)).paste_horiz sqZ
    rwa [← schemeSpaceMap_comp] at this
  have : IsProper (T.map qZ₁) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqZ₁
  have : Flat (T.map qZ₁) := X.flat_toScheme_map_of_isPullback sqZ₁
  have : LocallyOfFinitePresentation (T.map qZ₁) :=
    X.locallyOfFinitePresentation_toScheme_map_of_isPullback sqZ₁
  -- the residue field point at `u₁`, and its comparison with `P`
  let P' := residuePointVia φ₁ u₁
  let ν : P'.siteObject ⟶ U₁ := Space.residueFieldMap B integerBase hZ U₁ u₁ _
  have hst : (T.map ν ≫ T.map φ₁) (IsLocalRing.closedPoint P'.carrier) = s :=
    (congrArg (T.map φ₁) (Scheme.fromSpecResidueField_apply _ _)).trans hu₁
  obtain ⟨ψ, hψ⟩ := exists_comp_fromSpecResidueField (T.map ν ≫ T.map φ₁) s hst
  let ρ : CommRingCat.of P.carrier ⟶ CommRingCat.of P'.carrier := inv φK ≫ ψ
  let τ : T.obj P'.siteObject ⟶ T.obj P.siteObject := Spec.map ρ
  have hτ : τ ≫ T.map P.value = T.map ν ≫ T.map φ₁ := by
    show Spec.map (inv φK ≫ ψ) ≫ T.map P.value = _
    rw [← hφK, Spec.map_comp, Category.assoc, ← Category.assoc (Spec.map (inv φK)),
      ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp, hψ]
  let τB : P'.siteObject ⟶ P.siteObject := homOfToScheme τ
  have hτB : τB ≫ pv = ν ≫ φ₁ := hom_ext_of_toScheme (by
    rwa [Functor.map_comp, toScheme_map_homOfToScheme, Functor.map_comp])
  have hτflat : Flat τ :=
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.flat_and_surjective_specMap_of_field ρ).1
  -- the base change of `m₀` to the residue field of `u₁`
  let fV := pullback.fst v τB
  let sV := pullback.snd v τB
  let fW := pullback.fst w₀ τB
  let sW := pullback.snd w₀ τB
  let m₀' : pullback v τB ⟶ pullback w₀ τB :=
    pullback.map v τB w₀ τB m₀ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hm₀]) (by simp)
  have hm₀'w : m₀' ≫ sW = sV := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hm₀'f : m₀' ≫ fW = fV ≫ m₀ := pullback.lift_fst _ _ _
  have sqVτ : IsPullback (T.map fV) (T.map sV) (T.map v) τ :=
    (IsPullback.of_hasPullback v τB).map T
  have sqWτ : IsPullback (T.map fW) (T.map sW) (T.map w₀) τ :=
    (IsPullback.of_hasPullback w₀ τB).map T
  have sqm : IsPullback (T.map fV) (T.map m₀') (T.map m₀) (T.map fW) := by
    have h1 : IsPullback fV m₀' m₀ fW := by
      refine IsPullback.of_bot ?_ hm₀'f.symm (IsPullback.of_hasPullback w₀ τB)
      rw [hm₀'w, hm₀]
      exact IsPullback.of_hasPullback v τB
    exact h1.map T
  have : Flat (T.map fW) := MorphismProperty.of_isPullback sqWτ.flip hτflat
  have : IsProper (T.map sW) := MorphismProperty.of_isPullback sqWτ inferInstance
  -- the conditions on the base change
  let : Algebra P.carrier P'.carrier := ρ.hom.toAlgebra
  have hτalg : τ = Spec.map (CommRingCat.ofHom (algebraMap P.carrier P'.carrier)) := rfl
  have hdimV₁ : topologicalKrullDim (T.obj (pullback v τB)) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rwa [topologicalKrullDim_baseChange P.carrier P'.carrier _ _ (T.map v) (hτalg ▸ sqVτ)]
  have hdimW₁ : topologicalKrullDim (T.obj (pullback w₀ τB)) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_baseChange P.carrier P'.carrier _ _ (T.map w₀) (hτalg ▸ sqWτ),
      hc.topologicalKrullDim_eq]
    exact le_rfl
  obtain ⟨h0₁, hR₁⟩ := fibreConditions_of_isPullback sqm
    (topologicalKrullDim_fiber_le_of_le (T.map m₀) hdimV') hc.isIso_unitToPushforwardObjUnit
    hc.isZero_rightDerived_one
  -- the fibre of the chart at `u₁`, identified with the base change of `V`
  have presV :
      IsPullback (yoneda.map fV ≫ q) (yoneda.map sV) X.toBase.hom (yoneda.map (ν ≫ φ₁)) := by
    have := ((IsPullback.of_hasPullback v τB).map yoneda).paste_horiz hq0
    have e : yoneda.map τB ≫ yoneda.map pv = yoneda.map (ν ≫ φ₁) := by
      rw [← hτB, Functor.map_comp]
    exact e ▸ this
  have presZ : IsPullback (schemeSpaceMap (pullback.fst qZ₁ ν) ≫
      (schemeSpaceMap (pullback.fst qZ eW) ≫ pZ)).hom (yoneda.map (pullback.snd qZ₁ ν))
      X.toBase.hom (yoneda.map (ν ≫ φ₁)) := by
    have := (isPullback_schemeSpaceMap (IsPullback.of_hasPullback qZ₁ ν)).paste_horiz sqZ₁
    rw [← schemeSpaceMap_comp] at this
    exact AlgebraicSpaces.isPullback_hom _ _ _ this
  let θ := presV.isoIsPullback _ _ presZ
  let θs : pullback v τB ≅ pullback qZ₁ ν := Yoneda.fullyFaithful.preimageIso θ
  have hθs : θs.hom ≫ pullback.snd qZ₁ ν = sV := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, show yoneda.map θs.hom = θ.hom from
      Yoneda.fullyFaithful.map_preimage θ.hom]
    exact IsPullback.isoIsPullback_hom_snd _ _ _ _)
  -- the scheme case
  let qV₁ := T.map θs.hom ≫ T.map (pullback.fst qZ₁ ν)
  have hV₁ : IsPullback qV₁ (T.map sV) (T.map qZ₁) (T.map ν) := by
    have h1 : IsPullback (T.map θs.hom) (T.map sV) (T.map (pullback.snd qZ₁ ν)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Functor.map_comp, hθs]⟩
    have := h1.paste_horiz ((IsPullback.of_hasPullback qZ₁ ν).map T)
    rwa [Category.id_comp] at this
  let e₁ : T.obj P'.siteObject ⟶ Spec ((T.obj U₁).residueField u₁) := 𝟙 _
  have : IsIso e₁ := IsIso.id _
  have he₁ : e₁ ≫ (T.obj U₁).fromSpecResidueField u₁ = T.map ν := Category.id_comp _
  obtain ⟨U, φ, tU, _, _, htU, XU, pXU, fXU, hXU, Y, fY, h, hh, hYp, hYf, hYl, hYdim, qVU,
      iY, hq₁, hq₂, hiY, hhh⟩ :=
    exists_etale_contraction_of_isAffine_of_fiberDimension u₁ (T.map qZ₁) (T.map ν) e₁ he₁ qV₁
      (T.map sV) hV₁ (T.map sW) (T.map m₀')
      (by rw [← Functor.map_comp, hm₀'w]) hdimV₁ h0₁ hR₁ hdimW₁
  -- the neighbourhood, the family and the base change as objects of the site
  have : T.Faithful := ⟨fun h => hom_ext_of_toScheme h⟩
  have : T.Full := ⟨fun f => ⟨homOfToScheme f, rfl⟩⟩
  have hUc : B.Contains U := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact φ U₁.left.2
  let Us := BigFppfOver.siteObjectOver B integerBase hZ U₁ hUc φ
  let φs : Us ⟶ U₁ := BigFppfOver.siteMapOver B integerBase hZ U₁ hUc φ
  have hYc : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fY hUc
  let Ys := BigFppfOver.siteObjectOver B integerBase hZ Us hYc fY
  let fYs : Ys ⟶ Us := BigFppfOver.siteMapOver B integerBase hZ Us hYc fY
  have : IsProper fXU := MorphismProperty.of_isPullback hXU inferInstance
  have hXc : B.Contains XU := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact fXU hUc
  let XUs := BigFppfOver.siteObjectOver B integerBase hZ Us hXc fXU
  let fXUs : XUs ⟶ Us := BigFppfOver.siteMapOver B integerBase hZ Us hXc fXU
  let pXUs : XUs ⟶ pullback qZ eW := homOfToScheme pXU
  let hs : XUs ⟶ Ys := homOfToScheme h
  have hhs : hs ≫ fYs = fXUs := hom_ext_of_toScheme (by rwa [Functor.map_comp])
  have sqXs : IsPullback pXUs fXUs qZ₁ φs :=
    IsPullback.of_map T (hom_ext_of_toScheme (by
      rw [Functor.map_comp, Functor.map_comp]
      exact hXU.w)) hXU
  have hYdim' : ∀ y, (T.map fYs).fiberDimension y ≤ ((1 : ℕ∞) : WithBot ℕ∞) := fun y => by
    exact_mod_cast hYdim y
  let Yc : CurveFamily B hZ := curveFamilyOfFiberDimension fYs hYf hYp hYl hYdim'
  let t : Us ⟶ X.base := φs ≫ φ₁
  have ht : Etale (T.map t) := by
    rw [Functor.map_comp]
    exact inferInstanceAs (Etale (φ ≫ T.map φ₁))
  let u : T.obj Us := tU (IsLocalRing.closedPoint P'.carrier)
  have hu : T.map t u = s := by
    have e1 : (tU ≫ φ ≫ T.map φ₁) (IsLocalRing.closedPoint P'.carrier) = s := by
      rwa [reassoc_of% htU]
    rw [Functor.map_comp]
    exact e1
  have hA : IsPullback (schemeSpaceMap pXUs ≫ schemeSpaceMap (pullback.fst qZ eW) ≫ pZ)
      (schemeSpaceMap fXUs) X.toBase (schemeSpaceMap t) := by
    have := (isPullback_schemeSpaceMap sqXs).paste_horiz sqZ₁
    rwa [← schemeSpaceMap_comp] at this
  refine ⟨Yc, t, u, ht, hu, schemeSpace XUs, _, schemeSpaceMap fXUs, hA, schemeSpaceMap hs, ?_, ?_⟩
  · show schemeSpaceMap hs ≫ schemeSpaceMap fYs = _
    rw [← schemeSpaceMap_comp, hhs]
    rfl
  -- the data of the scheme case, spelled through the objects of the site
  let tUs : T.obj P'.siteObject ⟶ T.obj Us := tU
  let qVUs : T.obj (pullback v τB) ⟶ T.obj XUs := qVU
  let iYs : T.obj (pullback w₀ τB) ⟶ T.obj Ys := iY
  have hXs : IsPullback (T.map pXUs) (T.map fXUs) (T.map qZ₁) (T.map φs) := hXU
  have hiYs : IsPullback iYs (T.map sW) (T.map fYs) tUs := hiY
  have hhhs : T.map m₀' ≫ iYs = qVUs ≫ T.map hs := hhh
  have hq₁s : qVUs ≫ T.map pXUs = qV₁ := hq₁
  have hq₂s : qVUs ≫ T.map fXUs = T.map sV ≫ tUs := hq₂
  have htUs : tUs ≫ T.map φs = T.map ν := htU
  -- the fibres at the field-valued points over `u`
  intro Q hQ V'' W'' v'' w'' q'' r'' m'' hq'' hr'' hmw hmr
  let Qv : Q.siteObject ⟶ Us := Q.value
  have hqQ : IsPullback q'' (yoneda.map v'') (yoneda.map fXUs) (yoneda.map Qv) := by
    rwa [yonedaEquiv_symm_value] at hq''
  have hrQ : IsPullback r'' (yoneda.map w'') (yoneda.map fYs) (yoneda.map Qv) := by
    rwa [yonedaEquiv_symm_value] at hr''
  let qs : V'' ⟶ XUs := Yoneda.fullyFaithful.preimage q''
  let rs : W'' ⟶ Ys := Yoneda.fullyFaithful.preimage r''
  have hqs : yoneda.map qs = q'' := Yoneda.fullyFaithful.map_preimage q''
  have hrs : yoneda.map rs = r'' := Yoneda.fullyFaithful.map_preimage r''
  have sqQV : IsPullback (T.map qs) (T.map v'') (T.map fXUs) (T.map Qv) := by
    have h1 : IsPullback (yoneda.map qs) (yoneda.map v'') (yoneda.map fXUs) (yoneda.map Qv) := by
      rwa [hqs]
    exact (IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp, Functor.map_comp]
      exact h1.w)) h1).map T
  have sqQW : IsPullback (T.map rs) (T.map w'') (T.map fYs) (T.map Qv) := by
    have h1 : IsPullback (yoneda.map rs) (yoneda.map w'') (yoneda.map fYs) (yoneda.map Qv) := by
      rwa [hrs]
    exact (IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp, Functor.map_comp]
      exact h1.w)) h1).map T
  have hm' : T.map m'' ≫ T.map rs = T.map qs ≫ T.map hs := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Yoneda.fullyFaithful.map_injective (by
      rwa [Functor.map_comp, Functor.map_comp, hqs, hrs])
  -- the field-valued point factors through `t_U`
  obtain ⟨α, hα⟩ := exists_comp_fromSpecResidueField (T.map Qv) u (hQ _)
  obtain ⟨β, hβ⟩ := exists_comp_fromSpecResidueField tUs u rfl
  have hu1 : T.map φs u = u₁ := by
    show (tUs ≫ T.map φs) (IsLocalRing.closedPoint P'.carrier) = u₁
    rw [htUs]
    exact Scheme.fromSpecResidueField_apply _ _
  let γ : CommRingCat.of ↑((T.obj U₁).residueField u₁) ⟶ CommRingCat.of P'.carrier := 𝟙 _
  have : IsIso γ := IsIso.id _
  have hγ : Spec.map γ ≫ (T.obj U₁).fromSpecResidueField u₁ = T.map ν :=
    (congrArg (· ≫ (T.obj U₁).fromSpecResidueField u₁) (Spec.map_id _)).trans
      (Category.id_comp _)
  have : IsIso β := isIso_of_specMap_fromSpecResidueField_comp (T.map φs) u u₁ hu1 β γ (by
    rw [reassoc_of% hβ, htUs, hγ])
  let χ : Spec (.of Q.carrier) ⟶ T.obj P'.siteObject := Spec.map α ≫ inv (Spec.map β)
  have hχ : χ ≫ tUs = T.map Qv := by
    rw [Category.assoc, ← hβ, IsIso.inv_hom_id_assoc, hα]
  -- presentations of the fibres at `Q` over `V` and `W₀`
  have vV : IsPullback qVUs (T.map sV) (T.map fXUs) tUs := by
    refine IsPullback.of_right ?_ hq₂s hXs
    rw [hq₁s, htUs]
    exact hV₁
  have hwV : T.map qs ≫ T.map fXUs = (T.map v'' ≫ χ) ≫ tUs := by
    rw [sqQV.w, Category.assoc, hχ]
  let lV := vV.lift (T.map qs) (T.map v'' ≫ χ) hwV
  have hlV₁ : lV ≫ qVUs = T.map qs := vV.lift_fst _ _ _
  have hlV₂ : lV ≫ T.map sV = T.map v'' ≫ χ := vV.lift_snd _ _ _
  have sqV1 : IsPullback lV (T.map v'') (T.map sV) χ :=
    isPullback_lift_comp_of_isPullback vV hχ sqQV
  have hwW : T.map rs ≫ T.map fYs = (T.map w'' ≫ χ) ≫ tUs := by
    rw [sqQW.w, Category.assoc, hχ]
  let lW := hiYs.lift (T.map rs) (T.map w'' ≫ χ) hwW
  have hlW₁ : lW ≫ iYs = T.map rs := hiYs.lift_fst _ _ _
  have hlW₂ : lW ≫ T.map sW = T.map w'' ≫ χ := hiYs.lift_snd _ _ _
  have sqW1 : IsPullback lW (T.map w'') (T.map sW) χ :=
    isPullback_lift_comp_of_isPullback hiYs hχ sqQW
  have sqVfull := sqV1.paste_horiz sqVτ
  have sqWfull := sqW1.paste_horiz sqWτ
  have hml : T.map m'' ≫ lW = lV ≫ T.map m₀' := by
    refine hiYs.hom_ext ?_ ?_
    · rw [Category.assoc, hlW₁, Category.assoc, hhhs, reassoc_of% hlV₁, hm']
    · rw [Category.assoc, hlW₂, Category.assoc, ← Functor.map_comp, hm₀'w, hlV₂,
        ← reassoc_of% (Functor.map_comp T m'' w''), hmw]
  have hcomp : T.map m'' ≫ lW ≫ T.map fW = (lV ≫ T.map fV) ≫ T.map m₀ := by
    rw [← Category.assoc, hml, Category.assoc, ← Functor.map_comp, hm₀'f, Functor.map_comp,
      Category.assoc]
  -- the base change of `m₀` along `Spec K_Q ⟶ Spec K`
  let : Algebra P.carrier Q.carrier := (Spec.preimage (χ ≫ τ)).hom.toAlgebra
  have hQalg : χ ≫ τ = Spec.map (CommRingCat.ofHom (algebraMap P.carrier Q.carrier)) :=
    (Spec.map_preimage _).symm
  rw [hQalg] at sqVfull sqWfull
  exact isStableContraction_of_isPullback_baseChange (lV ≫ T.map fV) (lW ≫ T.map fW) sqVfull
    sqWfull (by rw [← Functor.map_comp, hmw]) hcomp hc

end AlgebraicGeometry.C1590Private

end
