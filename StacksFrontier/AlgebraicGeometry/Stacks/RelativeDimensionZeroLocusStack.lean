module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionOpenness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteNotionsAgree
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCoverGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# The relative-dimension-zero locus of a 1-morphism from an algebraic space to an algebraic stack

Let `f : U ⟶ 𝒳` be a 1-morphism, locally of finite type, from the algebraic stack of an algebraic
space `U` to an algebraic stack `𝒳` over `S`, and let `dim_t(U_x)` be its relative dimension at
`t ∈ |U|` (Stacks 0DRG), `AlgebraicGeometry.Stack.relativeDimensionAt`. The locus
`{t | dim_t(U_x) ≤ n}` is open, and `f` is locally quasi-finite exactly when `dim_t(U_x) = 0` at
every `t`. Both are computed on the base change of `f` along a smooth surjective chart of `𝒳` by a
scheme of the site.

## Main results

* `AlgebraicGeometry.Stack.eq_of_hasRelativeDimensionAt`: the relative dimension of a morphism of
  algebraic spaces at a point is unique.
* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange`: the
  relative dimension of `f` at a point of `U` is the relative dimension (Stacks 04NM) of the base
  change of `f` along any chart of `𝒳`, at any point above it.
* `AlgebraicGeometry.Stack.isOpen_setOf_relativeDimensionAt_le_of_algebraicStackTarget`: the locus
  of relative dimension at most `n` is open (Stacks 0DRQ, part (1)).
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero`: `f` is
  locally quasi-finite in the sense of Stacks 04XB exactly when its relative dimension vanishes at
  every point (Stacks 04NV).
* `Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero`: the same
  criterion for local quasi-finiteness in the sense of Stacks 06PU.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_chartBaseChange`: the 2-fibre product
  of a 1-morphism out of a stack representable by an algebraic space with a chart of the target is
  representable by an algebraic space.
* `Stack.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_chartBaseChange` and its
  Stacks 06PU counterpart: for a 1-morphism `c : 𝒯 ⟶ 𝒳` locally of finite type with `𝒯`
  representable by an algebraic space and a smooth surjective chart of `𝒳`, `c` is locally
  quasi-finite exactly when the base change of `c` along the chart has relative dimension zero at
  every point.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06M5](https://stacks.math.columbia.edu/tag/06M5)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Uniqueness of the relative dimension at a point -/

/-- The relative dimension of a morphism of algebraic spaces at a point is unique: two elements
of `ℕ∞` that are both the relative dimension (Stacks 04NM) of `g` at `x` agree. -/
theorem eq_of_hasRelativeDimensionAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y)
    (x : Space.points B S hS X) {d e : ℕ∞}
    (hd : Space.HasRelativeDimensionAt d B S hS g x)
    (he : Space.HasRelativeDimensionAt e B S hS g x) : d = e := by
  obtain ⟨c, hc⟩ := (Space.holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@AlgebraicGeometry.HasFiberDimensionAt.{u} e)
    (AlgebraicGeometry.fiberDimensionAt_isEtaleLocalOnSourceAndTarget e)
    hX hY g x).mp he
  have hce := (AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp hc
  have hcd := (AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff _ _ _).mp (hd c)
  exact_mod_cast hcd.symm.trans hce

/-! ### The relative dimension of Stacks 0DRG is computed on a smooth chart -/

section Chart

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)

/-- The base change of `f` along a chart of `𝒳` is locally of finite type as a morphism of the
algebraic spaces representing the two 2-fibre products. -/
private theorem isLocallyOfFiniteType_chartBaseChange
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom) := by
  have hQA : Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS a f) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f
  have hfstFT := AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a _ hQA hf
  exact isLocallyOfFiniteType_representingMap B S hS
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt)
    (𝒴 := schemeStack.{u, w} B S hS V₀) P (yoneda.obj V₀) hP
    (isAlgebraicSpace_yoneda B S hS V₀) eP
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) _ hfstFT

/-- Let `V ⟶ 𝒳` be a chart of the target, neither smooth nor surjective necessarily, and let `P`
be an algebraic space representing the 2-fibre product `U ×_𝒳 V`, so that the two projections
are morphisms of algebraic spaces `P ⟶ V` and `P ⟶ U`. For `z ∈ |P|`, the relative dimension
(Stacks 0DRG) of `f` at the image of `z` in `|U|` is `d` exactly when the projection `P ⟶ V` has
relative dimension `d` at `z` in the sense of Stacks 04NM. -/
theorem relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : Space.points B S hS P) (d : ℕ∞) :
    relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf
        (Space.pointsMap B S hS P (representingMap B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom) z) = (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS
        (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom) z := by
  have hforward : ∀ e : ℕ∞, relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf
      (Space.pointsMap B S hS P (representingMap B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom) z) = (e : WithBot ℕ∞) →
        Space.HasRelativeDimensionAt e B S hS
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom) z := by
    intro e he
    obtain ⟨p, q, hp, hq, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS U hU 𝒳 f hf _
    refine hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt B S hS a f
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) hf
      (Bicategory.isTwoFibreProduct_underlying
        (twoFibreProductSquareAlgebraicStacks B S hS a f)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          a.hom f.hom))
      ⟨P, hP, ⟨eP⟩⟩ (yoneda.obj V₀) P (isAlgebraicSpace_yoneda B S hS V₀) hP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀) eP
      (isLocallyOfFiniteType_chartBaseChange B S hS 𝒳 U hU f V₀ a P hP eP hf) rfl
      _ z rfl p q ?_ e (by rw [← hval]; exact he)
    rw [hq]
    exact spacePointMap_representing_naturality B S hS P U
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom z
  refine ⟨hforward d, fun hdz => ?_⟩
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast B S hS U hU 𝒳 f hf _
  have hkz := hforward (d₀ : ℕ∞) (by exact_mod_cast hd₀)
  have heq : (d₀ : ℕ∞) = d :=
    eq_of_hasRelativeDimensionAt B S hS hP (isAlgebraicSpace_yoneda B S hS V₀) _ z hkz hdz
  rw [hd₀]
  exact_mod_cast heq

/-- The base change of a smooth chart of `𝒳` along `f` is smooth as a morphism of algebraic
spaces. -/
private theorem isSmooth_chartProjection
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (haSm : AlgebraicStacks.IsSmooth B S hS a) :
    Space.IsSmooth B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom) := by
  have hsndSm : AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a f).snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS a f
      (twoFibreProductSquareAlgebraicStacks B S hS a f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f)) haSm
  exact isSmooth_representingMap_of_isSmooth B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt)
    (𝒴 := algebraicSpaceStack.{u, w} B S hS U hU) P U hP hU eP
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ hsndSm

/-- The base change of a surjective chart of `𝒳` along `f` is surjective on points. -/
private theorem isSurjective_chartProjection
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (haSurj : IsSurjective B S hS a) :
    Function.Surjective (Space.pointsMap B S hS P
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom)) := by
  have hsndSurj : IsSurjective B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).snd :=
    isSurjective_of_isTwoFibreProduct B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f) haSurj
  exact isSurjective_representingMap_of_isSurjective B S hS
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt)
    (𝒴 := algebraicSpaceStack.{u, w} B S hS U hU) P U eP
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ hsndSurj

/-- The locus of relative dimension at most `n` of `f` pulls back along the chart to the locus of
relative dimension at most `n` of the base change of `f`. -/
private theorem preimage_setOf_relativeDimensionAt_le
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (n : ℕ) :
    Space.pointsMap B S hS P (representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom) ⁻¹'
        {t : Space.points B S hS U |
          relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ ((n : ℕ∞) : WithBot ℕ∞)} =
      {z : Space.points B S hS P | ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧
        Space.HasRelativeDimensionAt d B S hS
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom) z} := by
  ext z
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast B S hS U hU 𝒳 f hf
    (Space.pointsMap B S hS P (representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom) z)
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  refine ⟨fun hz => ⟨(d₀ : ℕ∞), by rw [hd₀] at hz; exact_mod_cast hz,
    (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange
      B S hS 𝒳 U hU f V₀ a P hP eP hf z (d₀ : ℕ∞)).mp (by exact_mod_cast hd₀)⟩,
    fun ⟨d, hdn, hdz⟩ => ?_⟩
  rw [(relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange
    B S hS 𝒳 U hU f V₀ a P hP eP hf z d).mpr hdz]
  exact_mod_cast hdn

end Chart

/-! ### A source merely representable by an algebraic space -/

section RepresentedSource

variable (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
  (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)

/-- The 2-fibre product of a 1-morphism `c : 𝒯 ⟶ 𝒳`, with `𝒯` representable by an algebraic
space, and a chart `V ⟶ 𝒳` by a scheme of the site is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_chartBaseChange
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
    (schemeStack.{u, w} B S hS V₀).val 𝒯.val a.hom.hom c.hom.hom
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V₀)

/-- Let `c : 𝒯 ⟶ 𝒳` be locally of finite type with `𝒯` representable by an algebraic space, let
`V ⟶ 𝒳` be a smooth surjective chart by a scheme of the site, and let `P` be an algebraic space
representing `𝒯 ×_𝒳 V`. Then `c` is locally quasi-finite in the sense of Stacks 04XB exactly when
the projection `P ⟶ V` has relative dimension zero (Stacks 04NM) at every point of `P`. -/
theorem isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_chartBaseChange
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (haSm : AlgebraicStacks.IsSmooth B S hS a) (haSurj : IsSurjective B S hS a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    IsLocallyQuasiFinite B S hS c.hom ↔
      ∀ ξ : Space.points B S hS P, Space.HasRelativeDimensionAt 0 B S hS
        (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
          (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ := by
  have hcrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom
  have hfstFT := AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS c a _
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c) hc
  have hprFT := isLocallyOfFiniteType_representingMap B S hS
    (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS a c).pt)
    (𝒴 := schemeStack.{u, w} B S hS V₀) P (yoneda.obj V₀) hP
    (isAlgebraicSpace_yoneda B S hS V₀) eP
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) _ hfstFT
  refine Iff.trans ?_
    (Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _ hprFT)
  refine Iff.trans (hasRelativeProperty_iff_of_fppfCoverStack B S hS
    (Space.locallyQuasiFiniteProperty B S hS) c a hcrep haSurj
    (AlgebraicStacks.isFlat_of_isSmooth B S hS a haSm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSm)
    (twoFibreProductSquareAlgebraicStacks B S hS a c)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)) ?_
  refine ⟨fun h => ?_, fun h => ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1}
    B S hS _ _ _ c.hom a.hom _
    (Bicategory.isTwoFibreProduct_underlying
      (twoFibreProductSquareAlgebraicStacks B S hS a c)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        a.hom c.hom)) hcrep, ?_⟩⟩
  · obtain ⟨hfst, hfstP⟩ := h
    exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.locallyQuasiFiniteProperty B S hS)
      (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom hfst P (yoneda.obj V₀) hP
      (isAlgebraicSpace_yoneda B S hS V₀) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)).mp hfstP
  · exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.locallyQuasiFiniteProperty B S hS)
      (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom _ P (yoneda.obj V₀) hP
      (isAlgebraicSpace_yoneda B S hS V₀) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)).mpr h

/-- Let `c : 𝒯 ⟶ 𝒳` be locally of finite type with `𝒯` representable by an algebraic space, let
`V ⟶ 𝒳` be a smooth surjective chart by a scheme of the site, and let `P` be an algebraic space
representing `𝒯 ×_𝒳 V`. Then `c` is locally quasi-finite in the sense of Stacks 06PU exactly when
the projection `P ⟶ V` has relative dimension zero (Stacks 04NM) at every point of `P`. -/
theorem AlgebraicStacks.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_chartBaseChange
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (haSm : AlgebraicStacks.IsSmooth B S hS a) (haSurj : IsSurjective B S hS a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    AlgebraicStacks.IsLocallyQuasiFinite B S hS c ↔
      ∀ ξ : Space.points B S hS P, Space.HasRelativeDimensionAt 0 B S hS
        (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
          (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ :=
  (AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS c
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom)).trans
    (Stack.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_chartBaseChange
      B S hS 𝒳 𝒯 c V₀ a h𝒯 hc haSm haSurj P hP eP)

end RepresentedSource

/-! ### Stacks 0DRQ, part (1), and Stacks 04NV at an algebraic stack target -/

section Public

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)

/-- For a 1-morphism `f : U ⟶ 𝒳`, locally of finite type, from the algebraic stack of an algebraic
space to an algebraic stack, the set of points of `U` at which the relative dimension
(Stacks 0DRG) of `f` is at most `n` is open (Stacks 0DRQ, part (1)). -/
theorem isOpen_setOf_relativeDimensionAt_le_of_algebraicStackTarget (n : ℕ) :
    IsOpen {t : Space.points B S hS U |
      relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ ((n : ℕ∞) : WithBot ℕ∞)} := by
  obtain ⟨V₀, a, haSm, haSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨P, hP, ⟨eP⟩⟩ := isRepresentableByAlgebraicSpace_chartBaseChange B S hS 𝒳
    (algebraicSpaceStack.{u, w} B S hS U hU) f V₀ a
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
  have hc0Sm := isSmooth_chartProjection B S hS 𝒳 U hU f V₀ a P hP eP haSm
  rw [← Set.image_preimage_eq {t : Space.points B S hS U |
      relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ ((n : ℕ∞) : WithBot ℕ∞)}
    (isSurjective_chartProjection B S hS 𝒳 U hU f V₀ a P hP eP haSurj),
    preimage_setOf_relativeDimensionAt_le B S hS 𝒳 U hU f V₀ a P hP eP hf n]
  exact Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hP hU _
      (Space.isFlat_of_isSmooth B S hS _ hc0Sm)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hc0Sm) _
    (Space.isOpen_setOf_hasRelativeDimensionAt_le B S hS hP
      (isAlgebraicSpace_yoneda B S hS V₀) _
      (isLocallyOfFiniteType_chartBaseChange B S hS 𝒳 U hU f V₀ a P hP eP hf) n)

/-- A 1-morphism `f : U ⟶ 𝒳`, locally of finite type, from the algebraic stack of an algebraic
space to an algebraic stack is locally quasi-finite in the sense of Stacks 04XB exactly when the
relative dimension (Stacks 0DRG) of `f` vanishes at every point of `U` (Stacks 04NV). -/
theorem isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero :
    IsLocallyQuasiFinite B S hS f.hom ↔
      ∀ t : Space.points B S hS U,
        relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t = (0 : WithBot ℕ∞) := by
  obtain ⟨V₀, a, haSm, haSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨P, hP, ⟨eP⟩⟩ := isRepresentableByAlgebraicSpace_chartBaseChange B S hS 𝒳
    (algebraicSpaceStack.{u, w} B S hS U hU) f V₀ a
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
  have hsurj := isSurjective_chartProjection B S hS 𝒳 U hU f V₀ a P hP eP haSurj
  rw [isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_chartBaseChange B S hS 𝒳
    (algebraicSpaceStack.{u, w} B S hS U hU) f V₀ a
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) hf haSm haSurj P hP eP]
  refine ⟨fun h t => ?_, fun h z => ?_⟩
  · obtain ⟨z, hz⟩ := hsurj t
    rw [← hz]
    exact_mod_cast (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange
      B S hS 𝒳 U hU f V₀ a P hP eP hf z 0).mpr (h z)
  · exact (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_chartBaseChange
      B S hS 𝒳 U hU f V₀ a P hP eP hf z 0).mp (by rw [h]; rfl)

/-- A 1-morphism `f : U ⟶ 𝒳`, locally of finite type, from the algebraic stack of an algebraic
space to an algebraic stack is locally quasi-finite in the sense of Stacks 06PU exactly when the
relative dimension (Stacks 0DRG) of `f` vanishes at every point of `U`. -/
theorem AlgebraicStacks.isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero :
    AlgebraicStacks.IsLocallyQuasiFinite B S hS f ↔
      ∀ t : Space.points B S hS U,
        relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t = (0 : WithBot ℕ∞) :=
  (AlgebraicStacks.isLocallyQuasiFinite_iff_of_algebraicSpaceStack_source B S hS 𝒳 U hU f).trans
    (_root_.AlgebraicGeometry.Stack.isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero
      B S hS 𝒳 U hU f hf)

end Public

end AlgebraicGeometry.Stack

end
