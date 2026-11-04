module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLiftsFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingChartFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineGluingUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Gluing families of curves across a pushout along a first-order thickening

Let

```
X ---i---> X'
|          |
f          a
v          v
Y ---b---> Y'
```

be a commutative square of affine objects of the big fppf site whose square of schemes is a
pushout, with `i` and `b` first-order thickenings: the squares condition (RS*) of Stacks 07Y8
quantifies over. This file proves the two geometric facts about families of curves over such a
square that the proof of Stacks 0D56 rests on.

* **Gluing.** A family of curves `C_Y` over `Y` and a family `C_{X'}` over `X'`, together with a
  family `C_X` over `X` and cartesian morphisms `C_X ⟶ C_Y`, `C_X ⟶ C_{X'}` over `f` and `i`,
  glue to a family of curves over `Y'` restricting to the two given ones. Its total space is the
  pushout of algebraic spaces `C_Y ⨿_{C_X} C_{X'}` (Stacks 07VX), which restricts to the two
  given families (Stacks 07W0), is flat (Stacks 07W3, clause (2)) and locally of finite
  presentation (clause (3)); it is proper by Stacks 09ZZ (7) across the first-order thickening
  `Y ⊂ Y'`, and it has relative dimension at most one because the fibres of the glued family are
  the fibres of `C_Y` (Stacks 04NS (1)).
* **Descent.** Conversely the total space of any family of curves over `Y'` is the pushout of its
  restrictions to `Y` and to `X'` along its restriction to `X`, because it is flat over `Y'` (the
  counit assertion of Stacks 07W3).

The proofs follow the proof of Stacks 0E40 in
`StacksFrontier/Deformation/Examples/Geometric/SpacesRimSchlessinger.lean`; the étale charts of the
span of algebraic spaces lift across the thickening because it is of finite order
(`AlgebraicGeometry.Space.exists_etaleChart_lift_of_isFiniteOrderThickening`).

## Main definitions

* `AlgebraicGeometry.C1590Private.RSSquare`: the square, with the hypotheses above.

## Main results

* `AlgebraicGeometry.C1590Private.exists_glue`: the gluing of families of curves.
* `AlgebraicGeometry.C1590Private.isPushout_totalMap`: the descent of a family of curves over
  `Y'`.
* `AlgebraicGeometry.C1590Private.isProper_of_isPullback_of_isThickeningHom` and
  `AlgebraicGeometry.C1590Private.exists_hasRelativeDimensionAt_of_isPullback_of_isThickeningHom`:
  properness and relative dimension of a morphism of algebraic spaces read on its base change
  along a thickening of the target.

## References

* [Stacks Project, Tag 0D56](https://stacks.math.columbia.edu/tag/0D56)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 07W3](https://stacks.math.columbia.edu/tag/07W3)
* [Stacks Project, Tag 07W0](https://stacks.math.columbia.edu/tag/07W0)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Space

universe u

namespace AlgebraicGeometry.C1590Private

section Square

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square of the big fppf site of the shape condition (RS*) of Stacks 07Y8 produces: four
affine corners, a pushout of schemes, and first-order thickenings `i : X ⟶ X'` and
`b : Y ⟶ Y'`. -/
structure RSSquare {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y')
    (b : Y ⟶ Y') : Prop where
  isAffine_X : IsAffine ((BigFppfOver.toScheme B S hS).obj X)
  isAffine_X' : IsAffine ((BigFppfOver.toScheme B S hS).obj X')
  isAffine_Y : IsAffine ((BigFppfOver.toScheme B S hS).obj Y)
  isAffine_Y' : IsAffine ((BigFppfOver.toScheme B S hS).obj Y')
  firstOrder_i : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i)
  firstOrder_b : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map b)
  isPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f)
    ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)

namespace RSSquare

variable {X X' Y Y' : BigFppfOver B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {a : X' ⟶ Y'} {b : Y ⟶ Y'}

/-- A first-order thickening of objects of the site represents a thickening of algebraic
spaces. -/
theorem isThickeningHom_schemeSpaceMap {T T' : BigFppfOver B S hS} (t : T ⟶ T')
    (ht : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map t)) :
    IsThickeningHom B S hS (schemeSpaceMap t) :=
  FormalSpace.isThickeningHom_yonedaSpace_map B S hS t ht.isThickening

/-- A first-order thickening of objects of the site represents a thickening of algebraic spaces
of finite order. -/
theorem isFiniteOrderThickening_schemeSpaceMap {T T' : BigFppfOver B S hS} (t : T ⟶ T')
    (ht : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map t)) :
    IsFiniteOrderThickening B S hS (schemeSpace T') (Subfunctor.range (schemeSpaceMap t).hom) :=
  (isFirstOrderThickening_range_yoneda_map B S hS t ⟨ht.1, ht.2⟩).isFiniteOrderThickening

/-- The hypotheses of an `RSSquare` are insensitive to replacing its four corners by equal
objects of the site. -/
theorem of_eqToHom {X₁ X₁' Y₁ Y₁' : BigFppfOver B S hS} (h : RSSquare i f a b) (hX : X₁ = X)
    (hX' : X₁' = X') (hY : Y₁ = Y) (hY' : Y₁' = Y') {i₁ : X₁ ⟶ X₁'} {f₁ : X₁ ⟶ Y₁}
    {a₁ : X₁' ⟶ Y₁'} {b₁ : Y₁ ⟶ Y₁'} (hi : i₁ = eqToHom hX ≫ i ≫ eqToHom hX'.symm)
    (hf : f₁ = eqToHom hX ≫ f ≫ eqToHom hY.symm) (ha : a₁ = eqToHom hX' ≫ a ≫ eqToHom hY'.symm)
    (hb : b₁ = eqToHom hY ≫ b ≫ eqToHom hY'.symm) : RSSquare i₁ f₁ a₁ b₁ := by
  subst hX hX' hY hY'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi hf ha hb
  subst hi hf ha hb
  exact h

/-- The morphism of algebraic spaces represented by `i` is a thickening. -/
theorem isThickeningHom_i (h : RSSquare i f a b) : IsThickeningHom B S hS (schemeSpaceMap i) :=
  isThickeningHom_schemeSpaceMap i h.firstOrder_i

/-- The morphism of algebraic spaces represented by `b` is a thickening. -/
theorem isThickeningHom_b (h : RSSquare i f a b) : IsThickeningHom B S hS (schemeSpaceMap b) :=
  isThickeningHom_schemeSpaceMap b h.firstOrder_b

/-- The algebraic space represented by `X'` is a thickening of finite order of the image of `i`. -/
theorem isFiniteOrderThickening_i (h : RSSquare i f a b) :
    IsFiniteOrderThickening B S hS (schemeSpace X') (Subfunctor.range (schemeSpaceMap i).hom) :=
  isFiniteOrderThickening_schemeSpaceMap i h.firstOrder_i

/-- The algebraic space represented by `Y'` is a thickening of finite order of the image of `b`. -/
theorem isFiniteOrderThickening_b (h : RSSquare i f a b) :
    IsFiniteOrderThickening B S hS (schemeSpace Y') (Subfunctor.range (schemeSpaceMap b).hom) :=
  isFiniteOrderThickening_schemeSpaceMap b h.firstOrder_b

/-- The morphism of algebraic spaces represented by `f` is affine. -/
theorem isAffineHom_f (h : RSSquare i f a b) : Space.IsAffineHom B S hS (schemeSpaceMap f).hom := by
  have := h.isAffine_X
  have := h.isAffine_Y
  exact isAffineHom_yoneda_map B S hS f

/-- The square of algebraic spaces represented by the square is a pushout (Stacks 07SY). -/
theorem isPushout_schemeSpaceMap (h : RSSquare i f a b) :
    IsPushout (schemeSpaceMap i) (schemeSpaceMap f) (schemeSpaceMap a) (schemeSpaceMap b) := by
  have := h.isAffine_X
  have := h.isAffine_Y
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) :=
    inferInstance
  exact isPushout_algebraicSpaces_of_isThickening_of_isAffineHom' B S hS i f a b
    h.firstOrder_i.isThickening h.isPushout

end RSSquare

end Square

/-! ### Properness and relative dimension across a thickening of the target -/

section Thickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Properness across a cartesian thickening of the target (Stacks 09ZZ, part (7)).** In a
cartesian square `V = W ×_T E` of algebraic spaces along a thickening `t : W ⟶ T` of finite
order, `g : E ⟶ T` is proper as soon as its base change `p : V ⟶ W` is. -/
theorem isProper_of_isPullback_of_isThickeningHom {E T V W : AlgebraicSpaces B S hS}
    {g : E ⟶ T} {c : V ⟶ E} {p : V ⟶ W} {t : W ⟶ T} (sq : IsPullback c p g t)
    (ht : IsThickeningHom B S hS t)
    (htn : IsFiniteOrderThickening B S hS T (Subfunctor.range t.hom))
    (hp : Space.IsProper B S hS p.hom) : Space.IsProper B S hS g.hom := by
  have hc : IsThickeningHom B S hS c := isThickeningHom_of_isPullback B S hS sq.flip ht
  have sqh : IsPullback c.hom p.hom g.hom t.hom := AlgebraicSpaces.isPullback_hom B S hS sq
  have : IsIso (Subfunctor.toRange c.hom) := hc.1
  have : IsIso (Subfunctor.toRange t.hom) := ht.1
  let left : (Subfunctor.range c.hom).toFunctor ⟶ (Subfunctor.range t.hom).toFunctor :=
    inv (Subfunctor.toRange c.hom) ≫ p.hom ≫ Subfunctor.toRange t.hom
  have hw : left ≫ (Subfunctor.range t.hom).ι = (Subfunctor.range c.hom).ι ≫ g.hom := by
    have h1 : (Subfunctor.range c.hom).ι = inv (Subfunctor.toRange c.hom) ≫ c.hom := by
      rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
    simp only [left, Category.assoc, Subfunctor.toRange_ι, h1, sqh.w]
  let M : CartesianFiniteOrderMorphismOfThickenings B S hS :=
    { X' := E
      Y' := T
      X := Subfunctor.range c.hom
      Y := Subfunctor.range t.hom
      sourceThickening := hc.2
      targetFiniteOrder := htn
      morphism := Arrow.homMk left g.hom hw
      cartesian := by
        refine sqh.flip.of_iso (asIso (Subfunctor.toRange c.hom))
          (asIso (Subfunctor.toRange t.hom)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
        · simp [left]
        · simp
        · simp
        · simp }
  have hleft : Space.IsProper B S hS left := by
    have hsq : IsPullback (inv (Subfunctor.toRange c.hom)) left p.hom
        (inv (Subfunctor.toRange t.hom)) :=
      IsPullback.of_horiz_isIso ⟨by simp [left]⟩
    let Pc : AlgebraicSpaces B S hS := ⟨_, hc.2.1.1⟩
    let Pt : AlgebraicSpaces B S hS := ⟨_, ht.2.1.1⟩
    have hsq' : IsPullback (ObjectProperty.homMk (inv (Subfunctor.toRange c.hom)) : Pc ⟶ V)
        (ObjectProperty.homMk left : Pc ⟶ Pt) p
        (ObjectProperty.homMk (inv (Subfunctor.toRange t.hom)) : Pt ⟶ W) :=
      IsPullback.of_map_of_faithful (F := ObjectProperty.ι (IsAlgebraicSpace B S hS)) hsq
    exact MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ Space.IsProper B S hS k.hom)
      hsq' hp
  exact M.isProper_iff.1 hleft

/-- **Relative dimension across a cartesian thickening of the target.** In a cartesian square
`V = W ×_T E` of algebraic spaces along a thickening `t : W ⟶ T`, with `g : E ⟶ T` locally of
finite type, if `p : V ⟶ W` has relative dimension at most `d` at every point then so does `g`:
every point of `E` comes from `V`, and at corresponding points the two relative dimensions agree
(Stacks 04NS, part (1)). -/
theorem exists_hasRelativeDimensionAt_of_isPullback_of_isThickeningHom
    {E T V W : AlgebraicSpaces B S hS} {g : E ⟶ T} {c : V ⟶ E} {p : V ⟶ W} {t : W ⟶ T}
    (sq : IsPullback c p g t) (ht : IsThickeningHom B S hS t)
    (hg : IsLocallyOfFiniteType B S hS g.hom) (d : ℕ)
    (hp : ∀ x, ∃ e : ℕ, e ≤ d ∧ HasRelativeDimensionAt (e : ℕ∞) B S hS p.hom x) :
    ∀ y, ∃ e : ℕ, e ≤ d ∧ HasRelativeDimensionAt (e : ℕ∞) B S hS g.hom y := by
  have hc : IsThickeningHom B S hS c := isThickeningHom_of_isPullback B S hS sq.flip ht
  have sqh : IsPullback c.hom p.hom g.hom t.hom := AlgebraicSpaces.isPullback_hom B S hS sq
  intro y
  obtain ⟨x, rfl⟩ := hc.surjective_pointsMap y
  obtain ⟨e, he, hx⟩ := hp x
  exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS sqh E.2 W.2 T.2 hg x _).2 hx⟩

end Thickening

/-! ### Gluing families of curves -/

section Glue

/-- A thickening of finite order along an affine morphism has a compatible atlas. -/
private theorem nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' Y : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickeningHom B S hS i) (hf : Space.IsAffineHom B S hS f.hom)
    (hn : IsFiniteOrderThickening B S hS X' (Subfunctor.range i.hom)) :
    Nonempty (ThickeningAffineAtlas B S hS i f) :=
  nonempty_thickeningAffineAtlas_of_chartLift B S hS i f hi hf
    (exists_etaleChart_lift_of_isFiniteOrderThickening B S hS i hi hn)

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  {CU CY CX' : CurveFamily B hZ} (σ : CU ⟶ CY) (τ : CU ⟶ CX') {Y' : BigFppfOver B integerBase hZ}
  {a : CX'.base ⟶ Y'} {b : CY.base ⟶ Y'}

include σ τ in
/-- **Gluing families of curves (Stacks 0D56, the essential surjectivity).** A family of curves
`C_Y` over `Y` and a family `C_{X'}` over `X'` with cartesian morphisms from a common family
`C_X` over `X` glue, across a square of the shape of condition (RS*), to an algebraic space
`E ⟶ Y'` flat, proper, of finite presentation and of relative dimension at most one, whose
restrictions to `Y` and to `X'` are the two given families. -/
theorem exists_glue (h : RSSquare τ.baseMap σ.baseMap a b) :
    ∃ (E : AlgebraicSpaces B integerBase hZ) (g : E ⟶ schemeSpace Y') (c₁ : CY.total ⟶ E)
      (c₂ : CX'.total ⟶ E),
      IsPullback c₁ CY.toBase g (schemeSpaceMap b) ∧
      IsPullback c₂ CX'.toBase g (schemeSpaceMap a) ∧
      σ.totalMap ≫ c₁ = τ.totalMap ≫ c₂ ∧
      Space.IsFlat B integerBase hZ g.hom ∧ Space.IsProper B integerBase hZ g.hom ∧
      Space.IsFinitePresentation B integerBase hZ g.hom ∧
      ∀ x : Space.points B integerBase hZ E.obj, ∃ e : ℕ, e ≤ 1 ∧
        Space.HoldsOnEveryEtaleChartAtPoint B integerBase hZ
          (@HasFiberDimensionAt.{u} (e : ℕ∞)) g.hom x := by
  classical
  have hi := h.isThickeningHom_i
  have hf := h.isAffineHom_f
  have hE := h.isPushout_schemeSpaceMap
  have hin := h.isFiniteOrderThickening_i
  have hj₂ : IsThickeningHom B integerBase hZ τ.totalMap :=
    isThickeningHom_of_isPullback B integerBase hZ τ.cartesian.flip hi
  have hj₁ : Space.IsAffineHom B integerBase hZ σ.totalMap.hom :=
    Space.IsAffineHom.of_isPullback
      (AlgebraicSpaces.isPullback_hom B integerBase hZ σ.cartesian).flip hf
  have hj₂n : IsFiniteOrderThickening B integerBase hZ CX'.total
      (Subfunctor.range τ.totalMap.hom) :=
    isFiniteOrderThickening_range_of_isPullback B integerBase hZ τ.cartesian.flip hin
  obtain ⟨A₂⟩ := nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening τ.totalMap
    σ.totalMap hj₂ hj₁ hj₂n
  obtain ⟨E, c₂, c₁, hZpo, -⟩ := isPushout_quotient_of_thickeningAffineAtlas B integerBase hZ A₂
  have hzw : τ.totalMap ≫ CX'.toBase ≫ schemeSpaceMap a =
      σ.totalMap ≫ CY.toBase ≫ schemeSpaceMap b := by
    rw [← Category.assoc, ← Category.assoc, τ.cartesian.w, σ.cartesian.w, Category.assoc,
      Category.assoc, hE.w]
  let g := hZpo.desc (CX'.toBase ≫ schemeSpaceMap a) (CY.toBase ≫ schemeSpaceMap b) hzw
  have hgc₂ : c₂ ≫ g = CX'.toBase ≫ schemeSpaceMap a := hZpo.inl_desc _ _ _
  have hgc₁ : c₁ ≫ g = CY.toBase ≫ schemeSpaceMap b := hZpo.inr_desc _ _ _
  obtain ⟨D, hDV, hDU, hDY, hDX⟩ := exists_thickeningAffineGluingChart_of_isFiniteOrderThickening
    B integerBase hZ hi hin hf hE τ.cartesian σ.cartesian hZpo hgc₂ hgc₁
  have hc₁ : IsPullback c₁ CY.toBase g (schemeSpaceMap b) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_v hgc₁ hDV hDY).flip
  have hc₂ : IsPullback c₂ CX'.toBase g (schemeSpaceMap a) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (D.isPullback_u' hgc₂ hDU hDX).flip
  have hfl := D.isFlat_and_isLocallyOfFinitePresentation_iff.2
    ⟨⟨CY.flat, CY.finitePresentation.1⟩, ⟨CX'.flat, CX'.finitePresentation.1⟩⟩
  have hpr : Space.IsProper B integerBase hZ g.hom :=
    isProper_of_isPullback_of_isThickeningHom hc₁ h.isThickeningHom_b h.isFiniteOrderThickening_b
      CY.proper
  have hlft : IsLocallyOfFiniteType B integerBase hZ g.hom := hpr.2.1.1
  refine ⟨E, g, c₁, c₂, hc₁, hc₂, (congrArg (fun φ => φ) hZpo.w).symm, hfl.1, hpr,
    ⟨hfl.2, hpr.2.1.2, isQuasiSeparated_of_isSeparated B integerBase hZ hpr.1⟩, ?_⟩
  exact exists_hasRelativeDimensionAt_of_isPullback_of_isThickeningHom hc₁
    h.isThickeningHom_b hlft 1 CY.relativeDimensionLE

end Glue

/-! ### Descent of a family of curves over the pushout -/

section Descent

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  {CU CY CX' C : CurveFamily B hZ}

/-- **A family of curves over the pushout is the pushout of its restrictions** (the counit
assertion of Stacks 07W3). Let `C` be a family of curves over `Y'`, with cartesian morphisms
`ξ : C_Y ⟶ C` and `η : C_{X'} ⟶ C` over `b` and `a`, and `σ : C_X ⟶ C_Y`, `τ : C_X ⟶ C_{X'}`
over `f` and `i` with `σ ≫ ξ = τ ≫ η`, across a square of the shape of condition (RS*). Then the
total space of `C` is the pushout of those of `C_{X'}` and `C_Y` along that of `C_X`, because it is
flat over `Y'`. -/
theorem isPushout_totalMap (σ : CU ⟶ CY) (τ : CU ⟶ CX') (ξ : CY ⟶ C) (η : CX' ⟶ C)
    (hw : σ ≫ ξ = τ ≫ η) (h : RSSquare τ.baseMap σ.baseMap η.baseMap ξ.baseMap) :
    IsPushout τ.totalMap σ.totalMap η.totalMap ξ.totalMap := by
  have hi := h.isThickeningHom_i
  have hf := h.isAffineHom_f
  have hE := h.isPushout_schemeSpaceMap
  have hin := h.isFiniteOrderThickening_i
  obtain ⟨A⟩ := nonempty_thickeningAffineAtlas_of_isFiniteOrderThickening
    (schemeSpaceMap τ.baseMap) (schemeSpaceMap σ.baseMap) hi hf hin
  obtain ⟨Epo, aY₀, bY₀, qm, hpush, hqm, hqmS, hqmE, haX', hbYc⟩ :=
    exists_pushout_chart_of_thickeningAffineAtlas B integerBase hZ A hi
  let eP : Epo.1 ≅ (schemeSpace C.base).1 :=
    (ObjectProperty.ι _).mapIso (hpush.isoIsPushout _ _ hE)
  have hinl : aY₀.hom ≫ eP.hom = (schemeSpaceMap η.baseMap).hom :=
    congrArg (fun φ => φ.hom) (hpush.inl_isoIsPushout_hom _ _ hE)
  have hinr : bY₀.hom ≫ eP.hom = (schemeSpaceMap ξ.baseMap).hom :=
    congrArg (fun φ => φ.hom) (hpush.inr_isoIsPushout_hom _ _ hE)
  have hqm' : IsPullback (yoneda.map A.s) (yoneda.map A.t) (qm ≫ eP.hom) (qm ≫ eP.hom) :=
    hqm.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simp)
  have haX'' : IsPullback (yoneda.map A.a) A.p' (qm ≫ eP.hom)
      (schemeSpaceMap η.baseMap).hom :=
    haX'.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinl)
  have hbY'' : IsPullback (yoneda.map A.b) A.q (qm ≫ eP.hom) (schemeSpaceMap ξ.baseMap).hom :=
    hbYc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eP (by simp) (by simp) (by simp)
      (by simpa using hinr)
  have hback : (schemeSpaceMap τ.baseMap).hom ≫ (schemeSpaceMap η.baseMap).hom =
      (schemeSpaceMap σ.baseMap).hom ≫ (schemeSpaceMap ξ.baseMap).hom :=
    congrArg (fun φ => φ.hom) hE.w
  have hsides : σ.totalMap.hom ≫ ξ.totalMap.hom = τ.totalMap.hom ≫ η.totalMap.hom :=
    congrArg (fun φ => φ.hom) (congrArg CurveFamily.Hom.totalMap hw)
  exact isPushout_of_isFlat_of_thickeningAffineAtlas B integerBase hZ A hqm'
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmS)
    (MorphismProperty.RespectsIso.postcomp _ eP.hom qm hqmE) haX'' hbY'' hback C.flat
    (AlgebraicSpaces.isPullback_hom B integerBase hZ η.cartesian)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ ξ.cartesian)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ σ.cartesian)
    (congrArg (fun φ => φ.hom) τ.cartesian.w) hsides

end Descent

end AlgebraicGeometry.C1590Private

end
