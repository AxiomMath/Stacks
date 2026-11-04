module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyOfIsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Condition (1) of Stacks 0E8A near a fibre (Stacks 0E88)

Let `c : X ⟶ Y` be a morphism of families of curves over an isomorphism of bases, and `s` a point
of the base of `Y`. If at every field-valued point over `s` the morphism of fibres `c_s` has
`𝒪 = c_{s,*}𝒪` and `R¹c_{s,*}𝒪 = 0` (and fibres of dimension at most one), then there is an open
neighbourhood `N` of `s` over which `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0` hold after every base change.

This is Stacks 0E88. The proof is the source's: étale locally on the base both families are
schemes (Stacks 0E6F, the hypothesis `h0E6F`), where the scheme case
(`AlgebraicGeometry.C1590Private.exists_isOpen_forall_isPullback_of_fibre`, from Stacks 0E7L)
applies, and the conclusions are étale local
(`AlgebraicGeometry.C1590Private.isIso_structureSharp_of_isPullback_etale`,
`AlgebraicGeometry.C1590Private.isZero_firstDirectImage_of_isPullback_etale`) and hold for
morphisms of schemes as soon as they hold on the Zariski site
(`AlgebraicGeometry.C1590Private.isIso_structureSharp_schemeSpaceMap`,
`AlgebraicGeometry.C1590Private.isZero_firstDirectImage_schemeSpaceMap`).

## Main results

* `AlgebraicGeometry.C1590Private.exists_isOpen_isUniversallyAcyclic_of_fibre`.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.TopDegreeBaseChange

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibre hypothesis of Stacks 0E88 at a point.** At every field-valued point of `U` lying
over the point `s`, for every presentation of the fibres of `A` and `D` by schemes and the
morphism of schemes `m` induced by `a : A ⟶ D`, the source of `m` has dimension at most one,
`R¹m_*𝒪 = 0` and `𝒪 ⟶ m_*𝒪` is an isomorphism. -/
def FibreAcyclicAt {A D : AlgebraicSpaces B integerBase hZ} {U : BigFppfOver B integerBase hZ}
    (a : A ⟶ D) (p : D ⟶ schemeSpace U) (s : (BigFppfOver.toScheme B integerBase hZ).obj U) :
    Prop :=
  ∀ P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj,
    (∀ x, (BigFppfOver.toScheme B integerBase hZ).map P.value x = s) →
    ∀ ⦃V W : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject) (w : W ⟶ P.siteObject)
      (q : yoneda.obj V ⟶ A.obj) (r : yoneda.obj W ⟶ D.obj) (m : V ⟶ W),
      IsPullback q (yoneda.map v) (a ≫ p).hom (yonedaEquiv.symm P.value) →
      IsPullback r (yoneda.map w) p.hom (yonedaEquiv.symm P.value) →
      m ≫ w = v → yoneda.map m ≫ r = q ≫ a.hom →
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤
            ((1 : ℕ) : WithBot ℕ∞) ∧
          IsZero (firstDirectImageStructureSheaf ((BigFppfOver.toScheme B integerBase hZ).map m)) ∧
          IsIso (Scheme.Modules.unitToPushforwardUnit
            ((BigFppfOver.toScheme B integerBase hZ).map m))

/-- A cartesian square of the site gives a cartesian square of represented algebraic spaces. -/
theorem isPullback_schemeSpaceMap {P X Y Z : BigFppfOver B integerBase hZ} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    IsPullback (schemeSpaceMap fst) (schemeSpaceMap snd) (schemeSpaceMap f) (schemeSpaceMap g) :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ (by
      change yoneda.map fst ≫ yoneda.map f = yoneda.map snd ≫ yoneda.map g
      rw [← Functor.map_comp, ← Functor.map_comp, h.w])) (h.map yoneda)

/-- Over a chart of two families, a morphism of total spaces of schemes over the chart is
proper. -/
theorem isProper_toScheme_map_of_isPullback_comp {X Y : CurveFamily B hZ}
    {U ZX ZY : BigFppfOver B integerBase hZ} {ψ : U ⟶ X.base} {φ : U ⟶ Y.base}
    {qX : ZX ⟶ U} {qY : ZY ⟶ U} {pX : schemeSpace ZX ⟶ X.total}
    {pY : schemeSpace ZY ⟶ Y.total} {f : ZX ⟶ ZY}
    (hX : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap ψ))
    (hY : IsPullback pY (schemeSpaceMap qY) Y.toBase (schemeSpaceMap φ)) (hf : f ≫ qY = qX) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map f) := by
  have := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hX
  have := Y.isProper_toScheme_map_of_isPullback_schemeSpaceMap hY
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map f ≫
      (BigFppfOver.toScheme B integerBase hZ).map qY) := by
    rw [← Functor.map_comp, hf]
    infer_instance
  exact IsProper.of_comp _ ((BigFppfOver.toScheme B integerBase hZ).map qY)

/-- A cartesian square over an étale surjective morphism of schemes `e` makes its top side `j` an
étale covering of algebraic spaces. -/
theorem isEtaleCovering_of_isPullback_schemeSpaceMap {D : AlgebraicSpaces B integerBase hZ}
    {V W E : BigFppfOver B integerBase hZ} {j : schemeSpace W ⟶ D} {g : W ⟶ E}
    {p : D ⟶ schemeSpace V} {e : E ⟶ V}
    (h : IsPullback j (schemeSpaceMap g) p (schemeSpaceMap e))
    [Etale ((BigFppfOver.toScheme B integerBase hZ).map e)]
    (he : Function.Surjective ((BigFppfOver.toScheme B integerBase hZ).map e)) :
    Space.IsEtaleCovering B integerBase hZ (fun _ : PUnit.{u + 1} => (schemeSpace W).1)
      (fun _ => j.hom) :=
  have hEt : Space.IsEtale B integerBase hZ (schemeSpaceMap e).hom :=
    Space.isEtale_of_presheaf_etale B integerBase hZ
      ((Space.presheaf_yoneda_map_etale_iff B integerBase hZ e).2 inferInstance)
  { target_isAlgebraicSpace := D.2
    source_isAlgebraicSpace := fun _ => (schemeSpace W).2
    etale := fun _ => Space.isEtale_of_isPullback B integerBase hZ _ j _ p h.flip hEt
    jointly_surjective := Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨PUnit.unit,
      Space.isSurjective_of_isPullback B integerBase hZ h.flip
        ((Space.surjective_pointsMap_yoneda_iff B integerBase hZ e).2 he) x⟩ }

/-- Pulling a chart square back along a morphism `g` of the site gives a chart square over the
composite `g ≫ φ`. -/
theorem isPullback_schemeSpaceMap_pullback_fst_comp {A : AlgebraicSpaces B integerBase hZ}
    {S U V W : BigFppfOver B integerBase hZ} {p : schemeSpace W ⟶ A} {q : W ⟶ U}
    {t : A ⟶ schemeSpace S} {φ : U ⟶ S}
    (h : IsPullback p (schemeSpaceMap q) t (schemeSpaceMap φ)) (g : V ⟶ U) :
    IsPullback (schemeSpaceMap (pullback.fst q g) ≫ p) (schemeSpaceMap (pullback.snd q g)) t
      (schemeSpaceMap (g ≫ φ)) := by
  rw [schemeSpaceMap_comp g φ]
  exact (isPullback_schemeSpaceMap (IsPullback.of_hasPullback q g)).paste_horiz h

/-- Pulling a chart square of `ZX` back along a morphism `g` of the site, through a morphism
`f : ZX ⟶ ZY` over the chart, gives a chart square over the composite `g ≫ φ`. -/
theorem isPullback_schemeSpaceMap_pullback_pullback {A : AlgebraicSpaces B integerBase hZ}
    {S U V ZX ZY : BigFppfOver B integerBase hZ} {pX : schemeSpace ZX ⟶ A} {qX : ZX ⟶ U}
    {qY : ZY ⟶ U} {f : ZX ⟶ ZY} {t : A ⟶ schemeSpace S} {φ : U ⟶ S}
    (hX : IsPullback pX (schemeSpaceMap qX) t (schemeSpaceMap φ)) (hf : f ≫ qY = qX)
    (g : V ⟶ U) :
    IsPullback (schemeSpaceMap (pullback.fst f (pullback.fst qY g)) ≫ pX)
      (schemeSpaceMap (pullback.snd f (pullback.fst qY g) ≫ pullback.snd qY g)) t
      (schemeSpaceMap (g ≫ φ)) := by
  rw [schemeSpaceMap_comp g φ]
  have h₁ := isPullback_schemeSpaceMap
    ((IsPullback.of_hasPullback f (pullback.fst qY g)).paste_vert (IsPullback.of_hasPullback qY g))
  rw [hf] at h₁
  exact h₁.paste_horiz hX

/-- A chart square over `ψ` gives a chart square over `ψ ≫ b` of the base composed with an
isomorphism `b`. -/
theorem isPullback_comp_schemeSpaceMap_of_isIso {A P : AlgebraicSpaces B integerBase hZ}
    {S S' W : BigFppfOver B integerBase hZ} {p : P ⟶ A} {q : P ⟶ schemeSpace W}
    {t : A ⟶ schemeSpace S} {ψ : W ⟶ S} {ψ' : W ⟶ S'} (b : S ⟶ S') [IsIso b]
    (h : IsPullback p q t (schemeSpaceMap ψ)) (hψ : ψ' = ψ ≫ b) :
    IsPullback p q (t ≫ schemeSpaceMap b) (schemeSpaceMap ψ') := by
  have : IsIso (schemeSpaceMap b) :=
    inferInstanceAs (IsIso ((schemeSpaceFunctor B integerBase hZ).map b))
  have h₁ : IsPullback (schemeSpaceMap ψ) (𝟙 _) (schemeSpaceMap b) (schemeSpaceMap ψ') :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, ← schemeSpaceMap_comp, hψ]⟩
  simpa using h.paste_vert h₁

/-- Every point of one leg of a cartesian square of schemes lifts to the corner when its image
agrees with the image of a point of the other leg. -/
private theorem exists_apply_fst_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f x = g y) : ∃ z, fst z = x := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  exact ⟨h.isoPullback.inv z, by rw [← hz, ← h.isoPullback_inv_fst, Scheme.Hom.comp_apply]⟩

/-- **Simultaneous étale scheme charts of two families of curves over isomorphic bases.** Given
`c : X ⟶ Y` over an isomorphism `b` of bases and a point `s` of the base of `Y`, there is an
étale `φ : U ⟶ Y.base` with `s` in its image over which both families are schemes `Z_X`, `Z_Y`,
and `c` is induced by a morphism of schemes `f : Z_X ⟶ Z_Y` over `U`. -/
theorem exists_schemeCharts (h0E6F : HasEtaleLocalSchemeCharts B hZ) {X Y : CurveFamily B hZ}
    (b : X.base ⟶ Y.base) [IsIso b] (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase = X.toBase ≫ schemeSpaceMap b)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y.base) :
    ∃ (U ZX ZY : BigFppfOver B integerBase hZ) (φ : U ⟶ Y.base) (qX : ZX ⟶ U) (qY : ZY ⟶ U)
      (pX : schemeSpace ZX ⟶ X.total) (pY : schemeSpace ZY ⟶ Y.total) (f : ZX ⟶ ZY),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsPullback pX (schemeSpaceMap qX) (X.toBase ≫ schemeSpaceMap b) (schemeSpaceMap φ) ∧
      IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap (φ ≫ inv b)) ∧
      IsPullback pY (schemeSpaceMap qY) Y.toBase (schemeSpaceMap φ) ∧
      f ≫ qY = qX ∧ schemeSpaceMap f ≫ pY = pX ≫ c := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨U₁, Z₁, φ₁, q₁, p₁, hφ₁, ⟨u₁, hu₁⟩, sq₁⟩ := h0E6F Y s
  obtain ⟨U₂, Z₂, φ₂, q₂, p₂, hφ₂, ⟨u₂, hu₂⟩, sq₂⟩ := h0E6F X (T.map (inv b) s)
  have : Etale (T.map φ₁) := hφ₁
  have : Etale (T.map (φ₂ ≫ b)) := by
    rw [Functor.map_comp]
    have := hφ₂
    infer_instance
  let π₁ := pullback.fst φ₁ (φ₂ ≫ b)
  let π₂ := pullback.snd φ₁ (φ₂ ≫ b)
  have hUT := (IsPullback.of_hasPullback φ₁ (φ₂ ≫ b)).map T
  have : Etale (T.map π₁) := MorphismProperty.of_isPullback hUT.flip inferInstance
  have hs₂ : T.map (φ₂ ≫ b) u₂ = T.map φ₁ u₁ := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hu₂, hu₁, ← Scheme.Hom.comp_apply,
      ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨u₃, hu₃⟩ := exists_apply_fst_eq_of_isPullback hUT u₁ u₂ hs₂.symm
  let ZY := pullback q₁ π₁
  let ZX := pullback q₂ π₂
  have hφ : π₁ ≫ φ₁ = π₂ ≫ φ₂ ≫ b := pullback.condition
  have sqY := isPullback_schemeSpaceMap_pullback_fst_comp sq₁ π₁
  have hX₀ := isPullback_schemeSpaceMap_pullback_fst_comp sq₂ π₂
  have sqX := isPullback_comp_schemeSpaceMap_of_isIso b (ψ' := π₁ ≫ φ₁) hX₀
    (by rw [hφ, Category.assoc])
  let g : schemeSpace ZX ⟶ schemeSpace ZY :=
    sqY.lift ((schemeSpaceMap (pullback.fst q₂ π₂) ≫ p₂) ≫ c)
      (schemeSpaceMap (pullback.snd q₂ π₂)) (by rw [Category.assoc, hc, sqX.w])
  let f : ZX ⟶ ZY := Yoneda.fullyFaithful.preimage g.hom
  have hf : schemeSpaceMap f = g :=
    ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage g.hom)
  refine ⟨pullback φ₁ (φ₂ ≫ b), ZX, ZY, π₁ ≫ φ₁, pullback.snd q₂ π₂, pullback.snd q₁ π₁,
    schemeSpaceMap (pullback.fst q₂ π₂) ≫ p₂, schemeSpaceMap (pullback.fst q₁ π₁) ≫ p₁, f,
    ?_, ⟨u₃, ?_⟩, sqX, ?_, sqY, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_apply, hu₃, hu₁]
  · rwa [show (π₁ ≫ φ₁) ≫ inv b = π₂ ≫ φ₂ by
      rw [hφ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
  · apply Yoneda.fullyFaithful.map_injective
    have h2 : schemeSpaceMap f ≫ schemeSpaceMap (pullback.snd q₁ π₁) =
        schemeSpaceMap (pullback.snd q₂ π₂) := by
      rw [hf]
      exact sqY.lift_snd _ _ _
    rw [Functor.map_comp]
    exact congrArg (fun k => k.hom) h2
  · rw [hf]
    exact sqY.lift_fst _ _ _

/-- **The scheme case of Stacks 0E88 on a chart.** In the situation of
`AlgebraicGeometry.C1590Private.exists_schemeCharts`, if the fibre hypothesis holds over the image
of a point `u` of the chart, then there is an open neighbourhood `N` of `u` in the chart over
which the morphism of schemes `f : Z_X ⟶ Z_Y` satisfies `𝒪 = f_*𝒪` and `R¹f_*𝒪 = 0` after every
base change landing in `N`. -/
theorem exists_isOpen_chart_of_fibreAcyclicAt {X Y : CurveFamily B hZ} (b : X.base ⟶ Y.base)
    [IsIso b] (c : X.total ⟶ Y.total) {U ZX ZY : BigFppfOver B integerBase hZ}
    {φ : U ⟶ Y.base} {qX : ZX ⟶ U} {qY : ZY ⟶ U} {pX : schemeSpace ZX ⟶ X.total}
    {pY : schemeSpace ZY ⟶ Y.total} {f : ZX ⟶ ZY}
    (hX : IsPullback pX (schemeSpaceMap qX) (X.toBase ≫ schemeSpaceMap b) (schemeSpaceMap φ))
    (hX' : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap (φ ≫ inv b)))
    (hY : IsPullback pY (schemeSpaceMap qY) Y.toBase (schemeSpaceMap φ))
    (hf : f ≫ qY = qX) (hfc : schemeSpaceMap f ≫ pY = pX ≫ c)
    (hc : c ≫ Y.toBase = X.toBase ≫ schemeSpaceMap b)
    (u : (BigFppfOver.toScheme B integerBase hZ).obj U)
    (hfib : FibreAcyclicAt c Y.toBase ((BigFppfOver.toScheme B integerBase hZ).map φ u)) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens, u ∈ N ∧
      ∀ ⦃T' Y' X' : Scheme.{u}⦄ (h : T' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj U)
        (iY : Y' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj ZY) (qY' : Y' ⟶ T')
        (iX : X' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj ZX) (f' : X' ⟶ Y'),
        Set.range h ⊆ N →
        IsPullback iY qY' ((BigFppfOver.toScheme B integerBase hZ).map qY) h →
        IsPullback iX f' ((BigFppfOver.toScheme B integerBase hZ).map f) iY →
        IsIso (Scheme.Modules.unitToPushforwardUnit f') ∧
          IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
            (SheafOfModules.unit X'.ringCatSheaf)) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  have : Flat (T.map qX) := X.flat_toScheme_map_of_isPullback hX'
  have : LocallyOfFinitePresentation (T.map qX) :=
    X.locallyOfFinitePresentation_toScheme_map_of_isPullback hX'
  have : IsProper (T.map qX) := X.isProper_toScheme_map_of_isPullback_schemeSpaceMap hX'
  have : LocallyOfFinitePresentation (T.map qY) :=
    Y.locallyOfFinitePresentation_toScheme_map_of_isPullback hY
  have : IsProper (T.map qY) := Y.isProper_toScheme_map_of_isPullback_schemeSpaceMap hY
  have hfT : T.map f ≫ T.map qY = T.map qX := by rw [← Functor.map_comp, hf]
  have : Flat (T.map f ≫ T.map qY) := by
    rw [hfT]
    infer_instance
  have : LocallyOfFinitePresentation (T.map f ≫ T.map qY) := by
    rw [hfT]
    infer_instance
  have : IsProper (T.map f) := isProper_toScheme_map_of_isPullback_comp hX' hY hf
  have hκ : B.Contains (Spec ((T.obj U).residueField u)) :=
    BigFppfSite.residueField_spec_contains B U.left.2 u
  let ρ : BigFppfOver.siteObjectOver B integerBase hZ U hκ ((T.obj U).fromSpecResidueField u) ⟶ U :=
    BigFppfOver.siteMapOver B integerBase hZ U hκ ((T.obj U).fromSpecResidueField u)
  let P : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj :=
    { carrier := (T.obj U).residueField u
      contained := hκ
      toBase := (T.obj U).fromSpecResidueField u ≫ U.hom.hom
      value := ρ ≫ φ }
  have hPu : ∀ x, T.map P.value x = T.map φ u := fun x =>
    congrArg (T.map φ) ((T.obj U).fromSpecResidueField_apply u x)
  let fstY := pullback.fst qY ρ
  let w := pullback.snd qY ρ
  let fstX := pullback.fst f fstY
  let m := pullback.snd f fstY
  have hr := isPullback_schemeSpaceMap_pullback_fst_comp hY ρ
  have hq : IsPullback (schemeSpaceMap fstX ≫ pX) (schemeSpaceMap (m ≫ w))
      (c ≫ Y.toBase) (schemeSpaceMap (ρ ≫ φ)) := by
    rw [hc]
    exact isPullback_schemeSpaceMap_pullback_pullback hX hf ρ
  have hmr : schemeSpaceMap m ≫ schemeSpaceMap fstY ≫ pY =
      (schemeSpaceMap fstX ≫ pX) ≫ c := by
    have h1 : schemeSpaceMap fstX ≫ schemeSpaceMap f = schemeSpaceMap m ≫ schemeSpaceMap fstY := by
      rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, pullback.condition]
    rw [← Category.assoc, ← h1, Category.assoc, hfc, Category.assoc]
  obtain ⟨hdim, hR, hiso⟩ := hfib P hPu (V := pullback f fstY) (W := pullback qY ρ) (m ≫ w) w
    (schemeSpaceMap fstX ≫ pX).hom (schemeSpaceMap fstY ≫ pY).hom m
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hq)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hr) rfl
    (congrArg (fun k => k.hom) hmr)
  exact exists_isOpen_forall_isPullback_of_fibre (T.map f) (T.map qY) u (T.map fstY) (T.map w)
    (T.map fstX) (T.map m) ((IsPullback.of_hasPullback qY ρ).map T)
    ((IsPullback.of_hasPullback f fstY).map T) hdim hR hiso

/-- **Descent of a base change to simultaneous scheme charts.** Given charts `ZX`, `ZY` over `U`
of the source and target of `c`, with `f : ZX ⟶ ZY` inducing `c`, a base change `a' : A' ⟶ D'`
of `c` along `v`, and `g : V₀ ⟶ U`, `e : V₀ ⟶ V` with `g ≫ φ = e ≫ v`, the pulled back charts
present `D'` over `e` and `a'` as the base change of the pulled back chart morphism. -/
theorem exists_isPullback_of_isPullback_schemeCharts
    {Xt Yt A' D' : AlgebraicSpaces B integerBase hZ}
    {S U V V₀ ZX ZY : BigFppfOver B integerBase hZ} {c : Xt ⟶ Yt} {t : Yt ⟶ schemeSpace S}
    {φ : U ⟶ S} {qX : ZX ⟶ U} {qY : ZY ⟶ U} {pX : schemeSpace ZX ⟶ Xt}
    {pY : schemeSpace ZY ⟶ Yt} {f : ZX ⟶ ZY}
    (hX : IsPullback pX (schemeSpaceMap qX) (c ≫ t) (schemeSpaceMap φ))
    (hY : IsPullback pY (schemeSpaceMap qY) t (schemeSpaceMap φ))
    (hf : f ≫ qY = qX) (hfc : schemeSpaceMap f ≫ pY = pX ≫ c)
    {v : V ⟶ S} {a' : A' ⟶ D'} {iA : A' ⟶ Xt} {iD : D' ⟶ Yt} {p' : D' ⟶ schemeSpace V}
    (hD : IsPullback iD p' t (schemeSpaceMap v))
    (hA : IsPullback iA (a' ≫ p') (c ≫ t) (schemeSpaceMap v)) (hcomm : a' ≫ iD = iA ≫ c)
    {g : V₀ ⟶ U} {e : V₀ ⟶ V} (hge : g ≫ φ = e ≫ v) :
    ∃ (jD : schemeSpace (pullback qY g) ⟶ D')
      (jA : schemeSpace (pullback f (pullback.fst qY g)) ⟶ A'),
      IsPullback jD (schemeSpaceMap (pullback.snd qY g)) p' (schemeSpaceMap e) ∧
        IsPullback jA (schemeSpaceMap (pullback.snd f (pullback.fst qY g))) a' jD := by
  let fstE := pullback.fst qY g
  let sndE := pullback.snd qY g
  let fstEX := pullback.fst f fstE
  let fE := pullback.snd f fstE
  have hY₄ : IsPullback (schemeSpaceMap fstE ≫ pY) (schemeSpaceMap sndE) t
      (schemeSpaceMap (e ≫ v)) := by
    rw [← hge]
    exact isPullback_schemeSpaceMap_pullback_fst_comp hY g
  let jD : schemeSpace (pullback qY g) ⟶ D' :=
    hD.lift (schemeSpaceMap fstE ≫ pY) (schemeSpaceMap (sndE ≫ e)) (by
      rw [schemeSpaceMap_comp, Category.assoc, ← schemeSpaceMap_comp]
      exact hY₄.w)
  have hDE : IsPullback jD (schemeSpaceMap sndE) p' (schemeSpaceMap e) := by
    refine IsPullback.of_right ?_ (by rw [hD.lift_snd, schemeSpaceMap_comp]) hD
    rw [hD.lift_fst, ← schemeSpaceMap_comp]
    exact hY₄
  have hX₄ : IsPullback (schemeSpaceMap fstEX ≫ pX) (schemeSpaceMap (fE ≫ sndE))
      (c ≫ t) (schemeSpaceMap (e ≫ v)) := by
    rw [← hge]
    exact isPullback_schemeSpaceMap_pullback_pullback hX hf g
  let jA : schemeSpace (pullback f fstE) ⟶ A' :=
    hA.lift (schemeSpaceMap fstEX ≫ pX) (schemeSpaceMap (fE ≫ sndE ≫ e)) (by
      simpa only [← schemeSpaceMap_comp, Category.assoc] using hX₄.w)
  have hAE : IsPullback jA (schemeSpaceMap fE ≫ schemeSpaceMap sndE) (a' ≫ p')
      (schemeSpaceMap e) := by
    refine IsPullback.of_right ?_ ?_ hA
    · rw [hA.lift_fst, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp]
      exact hX₄
    · rw [hA.lift_snd, ← schemeSpaceMap_comp, ← schemeSpaceMap_comp, Category.assoc]
  have hcomm' : jA ≫ a' = schemeSpaceMap fE ≫ jD := by
    apply hD.hom_ext
    · rw [Category.assoc, Category.assoc, hD.lift_fst, hcomm, ← Category.assoc, hA.lift_fst,
        Category.assoc, ← hfc, ← Category.assoc, ← Category.assoc, ← schemeSpaceMap_comp,
        ← schemeSpaceMap_comp, pullback.condition]
    · rw [Category.assoc, Category.assoc, hA.lift_snd, hD.lift_snd, ← schemeSpaceMap_comp]
  exact ⟨jD, jA, hDE, IsPullback.of_bot hAE hcomm' hDE⟩

/-- **Stacks 0E88.** Let `c : X ⟶ Y` be a morphism of families of curves over an isomorphism `b`
of bases and `s` a point of the base of `Y`. If the fibres of `c` over `s` satisfy
`𝒪 = c_{s,*}𝒪` and `R¹c_{s,*}𝒪 = 0` (`AlgebraicGeometry.C1590Private.FibreAcyclicAt`), then there
is an open neighbourhood `N` of `s` such that the base change of `c` along every morphism of
schemes `V ⟶ Y.base` landing in `N` satisfies `𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0`. Stacks 0E6F is the
hypothesis `h0E6F`. -/
theorem exists_isOpen_isUniversallyAcyclic_of_fibre (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    {X Y : CurveFamily B hZ} (b : X.base ⟶ Y.base) [IsIso b] (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase = X.toBase ≫ schemeSpaceMap b)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    (hfib : FibreAcyclicAt c Y.toBase s) :
    ∃ N : ((BigFppfOver.toScheme B integerBase hZ).obj Y.base).Opens, s ∈ N ∧
      ∀ ⦃V : BigFppfOver B integerBase hZ⦄ (v : V ⟶ Y.base),
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map v) ⊆ N →
        ∀ ⦃A' D' : AlgebraicSpaces B integerBase hZ⦄ (a' : A' ⟶ D') (iA : A' ⟶ X.total)
          (iD : D' ⟶ Y.total) (p' : D' ⟶ schemeSpace V),
          IsPullback iD p' Y.toBase (schemeSpaceMap v) →
          IsPullback iA (a' ≫ p') (c ≫ Y.toBase) (schemeSpaceMap v) → a' ≫ iD = iA ≫ c →
            IsIso (Space.structureSharp B integerBase hZ a') ∧
              IsZero (firstDirectImage B hZ a') := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨U, ZX, ZY, φ, qX, qY, pX, pY, f, hφ, ⟨u, hu⟩, hX, hX', hY, hf, hfc⟩ :=
    exists_schemeCharts h0E6F b c hc s
  obtain ⟨N₃, hu₃, hN₃⟩ := exists_isOpen_chart_of_fibreAcyclicAt b c hX hX' hY hf hfc hc u
    (hu ▸ hfib)
  have : Etale (T.map φ) := hφ
  refine ⟨⟨T.map φ '' N₃, (T.map φ).isOpenMap _ N₃.2⟩, ⟨u, hu₃, hu⟩, ?_⟩
  intro V v hv A' D' a' iA iD p' hD hA hcomm
  have hN : B.Contains N₃.toScheme := B.contains_of_mono N₃.ι U.left.2
  let ι₄ := BigFppfOver.siteMapOver B integerBase hZ U hN N₃.ι
  let φ₄ := ι₄ ≫ φ
  have : Etale (T.map φ₄) := by
    change Etale (N₃.ι ≫ T.map φ)
    infer_instance
  let e := pullback.fst v φ₄
  let π := pullback.snd v φ₄
  have sqV := IsPullback.of_hasPullback v φ₄
  have : Etale (T.map e) := MorphismProperty.of_isPullback (sqV.map T).flip inferInstance
  have he : Function.Surjective (T.map e) := by
    intro x
    obtain ⟨n, hn, hnx⟩ := hv ⟨x, rfl⟩
    obtain ⟨n', rfl⟩ : n ∈ Set.range N₃.ι := by rwa [Scheme.Opens.range_ι]
    exact exists_apply_fst_eq_of_isPullback (sqV.map T) x n' hnx.symm
  let fstE := pullback.fst qY (π ≫ ι₄)
  let fE := pullback.snd f fstE
  have sqEX := IsPullback.of_hasPullback f fstE
  obtain ⟨jD, jA, hDE, hsqA⟩ := exists_isPullback_of_isPullback_schemeCharts (by rwa [hc]) hY hf
    hfc hD hA hcomm ((Category.assoc _ _ _).trans sqV.w.symm)
  have hcov := isEtaleCovering_of_isPullback_schemeSpaceMap hDE he
  have : IsProper (T.map f) := isProper_toScheme_map_of_isPullback_comp hX' hY hf
  have : IsProper (T.map fE) := MorphismProperty.of_isPullback (sqEX.map T) inferInstance
  have hrange : Set.range (T.map (π ≫ ι₄)) ⊆ N₃ := by
    rintro _ ⟨y, rfl⟩
    have : N₃.ι (T.map π y) ∈ Set.range N₃.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  obtain ⟨hO, hR⟩ := hN₃ (T.map (π ≫ ι₄)) (T.map fstE) (T.map (pullback.snd qY (π ≫ ι₄)))
    (T.map (pullback.fst f fstE)) (T.map fE) hrange
    ((IsPullback.of_hasPullback qY (π ≫ ι₄)).map T) (sqEX.map T)
  exact ⟨isIso_structureSharp_of_isPullback_etale B integerBase hZ a'
      (W := fun _ : PUnit.{u + 1} => schemeSpace (pullback qY (π ≫ ι₄)))
      (A' := fun _ => schemeSpace (pullback f fstE)) (fun _ => jD) (fun _ => jA)
      (fun _ => schemeSpaceMap fE) hcov (fun _ => hsqA)
      (fun _ => isIso_structureSharp_schemeSpaceMap B integerBase hZ fE hO),
    isZero_firstDirectImage_of_isPullback_etale a'
      (W := fun _ : PUnit.{u + 1} => schemeSpace (pullback qY (π ≫ ι₄)))
      (A' := fun _ => schemeSpace (pullback f fstE)) (fun _ => jD) (fun _ => jA)
      (fun _ => schemeSpaceMap fE) hcov (fun _ => hsqA)
      (fun _ => isZero_firstDirectImage_schemeSpaceMap hZ fE hR)⟩

end AlgebraicGeometry.C1590Private

end
