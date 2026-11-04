module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatChartOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DenseOpenAgreement
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The restriction of a finite flat chart to an open substack

Let `f : 𝒮_W ⟶ 𝒳` be a 1-morphism from the algebraic stack of an object `W` of the big fppf site,
let `𝒰 ⊆ 𝒳` be an open substack and let `Q ⊆ W` be an open of the underlying scheme of `W` with
`f⁻¹(𝒰) = Q`, in the sense that an object `z : T ⟶ W` of `𝒮_W` has `f(z) ∈ 𝒰` exactly when `z`
factors through `Q`. Then the square

```text
  𝒮_Q ----> 𝒮_W
   |          |
   v          v f
   𝒰  ---->  𝒳
```

identifies `𝒮_Q` with the 2-fibre product `𝒰 ×_𝒳 𝒮_W`: the mediating 1-morphism to the canonical
2-fibre product is an equivalence. So the restriction `𝒮_Q ⟶ 𝒰` is a base change of `f`, and it is
surjective, flat, finite and of finite presentation when `f` is. If `Q` is affine, `𝒰` is
well-nigh affine (Stacks 0DUL).

## Main results

* `AlgebraicGeometry.Stack.FlatChart.isEquivalence_restrictLift`: the identification of `𝒮_Q`
  with `𝒰 ×_𝒳 𝒮_W`.
* `AlgebraicGeometry.Stack.FlatChart.restrictChart_properties`: the restricted chart is
  surjective, flat, finite and of finite presentation.
* `AlgebraicGeometry.Stack.FlatChart.isWellNighAffine_of_isAffineOpen`: `𝒰` is well-nigh affine
  when `Q` is affine.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 0DUL](https://stacks.math.columbia.edu/tag/0DUL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatChart

section OverMap

variable {C : Type*} [Category C] {X Y : C} (j : X ⟶ Y) [Mono j]

/-- Post-composition with a monomorphism is full on slices. -/
theorem full_overMap_of_mono : (Over.map j).Full where
  map_surjective {a b} φ :=
    ⟨Over.homMk φ.left ((cancel_mono j).1 (by simpa using Over.w φ)), by ext; rfl⟩

omit [Mono j] in
/-- Post-composition is faithful on slices. -/
theorem faithful_overMap : (Over.map j).Faithful where
  map_injective {_ _} _ _ h :=
    Over.OverMorphism.ext (congrArg (fun m => m.left) h)

end OverMap

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
  (f : schemeStack.{u, w} B S hS W ⟶ 𝒳) (𝒰 : OpenSubstack 𝒳)
  (Q : W.left.obj.Opens)
  (h𝒰 : ∀ z : (schemeStack.{u, w} B S hS W).val.val.obj,
    𝒰.property (f.hom.hom.obj z) ↔
      Set.range ⇑((BigFppfOver.toScheme B S hS).map z.hom) ⊆ (Q : Set W.left.obj))

/-- The open subscheme `Q` of `W`, as an object of the big fppf site. -/
noncomputable abbrev restrictObj : BigFppfOver B S hS := BigFppfOver.openSubObj B S hS W Q

/-- The inclusion `Q ⟶ W`. -/
noncomputable abbrev restrictHom : restrictObj Q ⟶ W := BigFppfOver.openSubHom B S hS W Q

include h𝒰 in
/-- Every object of `𝒮_Q`, read in `𝒮_W`, is sent into `𝒰`. -/
theorem mem_restrict (z : (schemeStack.{u, w} B S hS (restrictObj Q)).val.val.obj) :
    𝒰.property ((schemeStackMap.{u, w} B S hS (restrictHom Q) ≫ f).hom.hom.toFunctor.obj z) := by
  refine (h𝒰 ((Over.map (restrictHom Q)).obj z)).2 ?_
  have e : (BigFppfOver.toScheme B S hS).map ((Over.map (restrictHom Q)).obj z).hom =
      (BigFppfOver.toScheme B S hS).map z.hom ≫ Q.ι := by
    show (BigFppfOver.toScheme B S hS).map (z.hom ≫ restrictHom Q) = _
    rw [Functor.map_comp, Space.openSubHom_toScheme]
  rintro _ ⟨y, rfl⟩
  rw [e, Scheme.Hom.comp_apply, ← Q.range_ι]
  exact Set.mem_range_self _

/-- The restricted chart `𝒮_Q ⟶ 𝒰`: the composite `𝒮_Q ⟶ 𝒮_W ⟶ 𝒳` factored through `𝒰`. -/
noncomputable abbrev restrictChart :
    schemeStack.{u, w} B S hS (restrictObj Q) ⟶ 𝒰.toAlgebraicStack :=
  𝒰.factor B S hS (schemeStackMap.{u, w} B S hS (restrictHom Q) ≫ f) (mem_restrict f 𝒰 Q h𝒰)

/-- The 2-commutative square formed by the restricted chart, the inclusion of `𝒰`, the
inclusion `𝒮_Q ⟶ 𝒮_W` and `f`; it commutes on the nose. -/
noncomputable def restrictSquare : Bicategory.TwoCommSq (𝒰.inclusion B S hS).hom f.hom where
  pt := (schemeStack.{u, w} B S hS (restrictObj Q)).val
  fst := (restrictChart f 𝒰 Q h𝒰).hom
  snd := (schemeStackMap.{u, w} B S hS (restrictHom Q)).hom
  iso := Iso.refl _

/-- The mediating 1-morphism from `𝒮_Q` to the canonical 2-fibre product `𝒰 ×_𝒳 𝒮_W`. -/
noncomputable abbrev restrictLift :
    schemeStack.{u, w} B S hS (restrictObj Q) ⟶
      (twoFibreProductSquareAlgebraicStacks B S hS (𝒰.inclusion B S hS) f).pt :=
  Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (𝒰.inclusion B S hS).hom f.hom (restrictSquare f 𝒰 Q h𝒰))

/-- `𝒮_Q` is the 2-fibre product `𝒰 ×_𝒳 𝒮_W`: the mediating 1-morphism `restrictLift` is an
equivalence. -/
theorem isEquivalence_restrictLift :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom) := by
  have := Space.mono_openSubHom B S hS W Q
  have := 𝒰.strictlyFull
  have hfaith : (CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom).Faithful :=
    ⟨fun e => (faithful_overMap (restrictHom Q)).map_injective
      (congrArg TwoFibreProductOver.Hom.b e)⟩
  have hfull : (CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom).Full := by
    refine ⟨fun {z₁ z₂} Φ => ?_⟩
    obtain ⟨g, hg⟩ := (full_overMap_of_mono (restrictHom Q)).map_surjective Φ.b
    refine ⟨g, TwoFibreProductOver.Hom.ext' ?_ hg⟩
    apply ObjectProperty.hom_ext
    have hw := Φ.w
    change Φ.a.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.hom.toFunctor.map Φ.b at hw
    rw [Category.comp_id, Category.id_comp] at hw
    rw [hw, ← hg]
    rfl
  have hess : (CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom).EssSurj := by
    refine ⟨fun P => ?_⟩
    have hPy : 𝒰.property (f.hom.hom.obj P.y) := 𝒰.property.prop_of_iso P.iso P.x.property
    let a := Space.openSubObjLift B S hS W Q P.y.hom ((h𝒰 P.y).1 hPy)
    have ha : a ≫ restrictHom Q = P.y.hom :=
      Space.openSubObjLift_comp_openSubHom B S hS W Q P.y.hom ((h𝒰 P.y).1 hPy)
    let z' : (schemeStack.{u, w} B S hS (restrictObj Q)).val.val.obj := Over.mk a
    let b : (Over.map (restrictHom Q)).obj z' ⟶ P.y :=
      Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact ha.symm)
    have hb : (schemeStack.{u, w} B S hS W).val.val.p.IsHomLift (eqToHom P.hy) b :=
      IsHomLift.of_fac' _ _ _ rfl P.hy (by simp [b]; rfl)
    have hfb : 𝒳.val.val.p.IsHomLift (eqToHom P.hy) (f.hom.hom.toFunctor.map b) :=
      Functor.isHomLift_map_of_comp_eq f.hom.hom.w _ b
    have hv : 𝒳.val.val.p.IsHomLift (𝟙 P.base) P.iso.inv :=
      @IsHomLift.lift_id_inv _ _ _ _ _ _ _ _ P.iso P.vertical
    have hcomp : 𝒳.val.val.p.IsHomLift (eqToHom P.hy)
        (f.hom.hom.toFunctor.map b ≫ P.iso.inv) := by
      simpa using (inferInstance : 𝒳.val.val.p.IsHomLift (eqToHom P.hy ≫ 𝟙 P.base)
        (f.hom.hom.toFunctor.map b ≫ P.iso.inv))
    let Φ : (CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom).obj z' ⟶ P :=
      { hbase := eqToHom P.hy
        a := ObjectProperty.homMk (f.hom.hom.toFunctor.map b ≫ P.iso.inv)
        b := b
        ha := IsHomLift.of_fac' _ _ _
          ((CatFiberedInGroupoids.homFunctor (restrictLift f 𝒰 Q h𝒰).hom).obj z').hx P.hx
          (IsHomLift.fac' 𝒳.val.val.p (eqToHom P.hy) (f.hom.hom.toFunctor.map b ≫ P.iso.inv))
        hb := hb
        w := by
          show (f.hom.hom.toFunctor.map b ≫ P.iso.inv) ≫ P.iso.hom = 𝟙 _ ≫ _
          rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          exact (Category.id_comp _).symm }
    have hΦ : (twoFibreProductSquareAlgebraicStacks B S hS (𝒰.inclusion B S hS)
        f).pt.val.val.p.IsHomLift (eqToHom P.hy) Φ :=
      IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)
    have := (twoFibreProductSquareAlgebraicStacks B S hS (𝒰.inclusion B S hS)
      f).pt.val.property.isStronglyCartesian_homLift (eqToHom P.hy) Φ
    have : IsIso Φ := Functor.IsStronglyCartesian.isIso_of_base_isIso
      (twoFibreProductSquareAlgebraicStacks B S hS (𝒰.inclusion B S hS) f).pt.val.val.p
      (eqToHom P.hy) Φ
    exact ⟨z', ⟨asIso Φ⟩⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

/-- The restricted chart `𝒮_Q ⟶ 𝒰`, read through the 2-fibre product `𝒰 ×_𝒳 𝒮_W`. -/
noncomputable abbrev restrictChart' :
    schemeStack.{u, w} B S hS (restrictObj Q) ⟶ 𝒰.toAlgebraicStack :=
  restrictLift f 𝒰 Q h𝒰 ≫ (chartBaseChangeSquare (𝒰.inclusion B S hS) f).fst

/-- The restriction of a chart to an open substack is surjective, flat, finite and of finite
presentation when the chart is. -/
theorem restrictChart_properties (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hfin : AlgebraicStacks.IsFinite B S hS f)
    (hfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS f) :
    IsSurjective B S hS (restrictChart' f 𝒰 Q h𝒰) ∧
      AlgebraicStacks.IsFlat B S hS (restrictChart' f 𝒰 Q h𝒰) ∧
        AlgebraicStacks.IsFinite B S hS (restrictChart' f 𝒰 Q h𝒰) ∧
          AlgebraicStacks.IsRelativelyFinitePresentation B S hS (restrictChart' f 𝒰 Q h𝒰) :=
  chartBaseChange_properties (𝒰.inclusion B S hS) f (restrictLift f 𝒰 Q h𝒰)
    (isEquivalence_restrictLift f 𝒰 Q h𝒰) hsurj hflat hfin hfp

include h𝒰 in
/-- An open substack cut out by an affine open of a surjective, flat, finite and finitely
presented chart is well-nigh affine (Stacks 0DUL). -/
theorem isWellNighAffine_of_isAffineOpen (hQ : IsAffineOpen Q) (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hfin : AlgebraicStacks.IsFinite B S hS f)
    (hfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS f) :
    IsWellNighAffine.{u, w} B S hS 𝒰.toAlgebraicStack :=
  ⟨restrictObj Q, hQ, restrictChart' f 𝒰 Q h𝒰,
    restrictChart_properties f 𝒰 Q h𝒰 hsurj hflat hfin hfp⟩

end FlatChart

end AlgebraicGeometry.Stack

end
