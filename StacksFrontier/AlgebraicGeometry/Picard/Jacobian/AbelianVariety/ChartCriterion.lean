module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.ChartTranslates
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.RepresentingGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Charts of a scheme representing the Picard functor

Let `P` be an object of a big fppf site representing the Picard functor `Pic_{X/S}` of
[Stacks, Tag 0B9L], and let `F ⊆ Pic_{X/S}` be a subset of classes which is *open* in the sense
that, for every test scheme `T` and every class `c` over `T`, there is an open `U ⊆ T` such that
`h^* c ∈ F` exactly when `h : T' ⟶ T` factors through `U` (the shape of [Stacks, Tag 0B9V]).
Suppose that `F` is *represented* by `j : W ⟶ P`: every class in `F` is uniquely of the form
`t^*[j]`. Then `j` is an open immersion, onto the open subscheme of `P` cut out by `F` at the
universal class.

If moreover every point of `P` is carried into `F` by translation by an `S`-point of `P` (the
shape of [Stacks, Tag 0B9Y]), the right translates of the chart cover `P`, so that `P` is smooth
of relative dimension `n` as soon as `W` is. This is how the proof of [Stacks, Tag 0B9Z] and
[Stacks, Tag 0BA0] gets the smoothness of the Picard scheme of a curve from the open `W` of the
Hilbert scheme `Hilb^g_{X/k}` of [Stacks, Tag 0B9X].

## Main results

* `Stacks.PicardFunctor.isOpenImmersion_of_representsOpen`: the chart is an open immersion, and
  its image is cut out by `F`.
* `Stacks.PicardFunctor.exists_rightTranslation_mem_range`: translates of the chart cover.
* `Stacks.PicardFunctor.smoothOfRelativeDimension_of_representsOpen`: smoothness of `P`.

## References

* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {B : BigFppfSite.{u}} {X S : Scheme.{u}} {hX : B.Contains X} {hS : B.Contains S}
  {f : B.obj hX ⟶ B.obj hS}

/-- **A subset of the Picard functor which is open and represented is represented by an open
subscheme.** Let `P` represent `Pic_{X/S}`, let `F` be a subset of classes, open in the sense of
[Stacks, Tag 0B9V], and let `j : W ⟶ P` represent `F`: its class lies in `F`, every class in `F`
is `t^*[j]` for some `t`, and `t` is unique. Then `j` is an open immersion, and a morphism
`h : T ⟶ P` has class in `F` exactly when it lands in the image of `j`. -/
theorem isOpenImmersion_of_representsOpen {P W : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P)
    (F : ∀ T : BigFppfOver B S hS, Set ((picardFunctor B hX hS f).obj (op T)))
    (hopen : ∀ (T : BigFppfOver B S hS) (c : (picardFunctor B hX hS f).obj (op T)),
      ∃ U : ((BigFppfOver.toScheme B S hS).obj T).Opens, ∀ {T' : BigFppfOver B S hS} (h : T' ⟶ T),
        (picardFunctor B hX hS f).map h.op c ∈ F T' ↔
          Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ (U : Set _))
    (j : W ⟶ P) (hjF : R.homEquiv j ∈ F W)
    (hjsurj : ∀ {T : BigFppfOver B S hS} (c : (picardFunctor B hX hS f).obj (op T)), c ∈ F T →
      ∃ t : T ⟶ W, R.homEquiv (t ≫ j) = c)
    (hjinj : ∀ {T : BigFppfOver B S hS} (t t' : T ⟶ W), t ≫ j = t' ≫ j → t = t') :
    IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      ∀ {T : BigFppfOver B S hS} (h : T ⟶ P), R.homEquiv h ∈ F T ↔
        Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆
          Set.range ((BigFppfOver.toScheme B S hS).map j) := by
  obtain ⟨U, hU⟩ := hopen P (R.homEquiv (𝟙 P))
  have hF : ∀ {T : BigFppfOver B S hS} (h : T ⟶ P), R.homEquiv h ∈ F T ↔
      Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆ (U : Set _) := by
    intro T h
    rw [← hU h, ← R.homEquiv_comp, Category.comp_id]
  obtain ⟨Ub, i0, hιo, hιr, hιlift⟩ := exists_restrict_bigFppfOver P U
  have := hιo
  have : Mono i0 := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  obtain ⟨s, hs⟩ := hjsurj _ ((hF i0).2 hιr.le)
  have hs' : s ≫ j = i0 := R.homEquiv.injective hs
  obtain ⟨j', hj'⟩ := hιlift j ((hF j).1 hjF)
  have h1 : s ≫ j' = 𝟙 _ := by
    rw [← cancel_mono i0, Category.assoc, hj', hs', Category.id_comp]
  have h2 : j' ≫ s = 𝟙 _ := hjinj _ _ (by rw [Category.assoc, hs', hj', Category.id_comp])
  have : IsIso j' := ⟨s, h2, h1⟩
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map j) = (U : Set _) := by
    rw [← hj', Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ((BigFppfOver.toScheme B S hS).map j').surjective.range_eq, Set.image_univ, hιr]
  refine ⟨?_, fun h => by rw [hrange]; exact hF h⟩
  rw [← hj', Functor.map_comp]
  infer_instance

/-- The terminal test scheme, viewed as a scheme over `S`, is isomorphic to the unit of the
Cartesian monoidal structure on schemes over `S`. -/
def unitIsoTerminalTest :
    𝟙_ (Over S) ≅ (BigFppfOver.toOver B S hS).obj (terminalTest B hS) where
  hom := Over.homMk (𝟙 _) (by
    change 𝟙 S ≫ B.inclusion.map (𝟙 (B.obj hS)) = 𝟙 S
    rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)
  inv := Over.homMk (𝟙 _) (by
    change 𝟙 S ≫ 𝟙 S = B.inclusion.map (𝟙 (B.obj hS))
    rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)
  hom_inv_id := Over.OverMorphism.ext (Category.comp_id _)
  inv_hom_id := Over.OverMorphism.ext (Category.comp_id _)

attribute [local instance] bigFppfOverCartesianMonoidal toOverMonoidal

/-- The image under `BigFppfOver.toOver` of the morphism to the terminal test scheme. -/
theorem toOver_map_toUnit (T : BigFppfOver B S hS) :
    (BigFppfOver.toOver B S hS).map (toUnit T : T ⟶ terminalTest B hS) =
      toUnit _ ≫ (unitIsoTerminalTest (B := B) (hS := hS)).hom := by
  rw [← cancel_mono (unitIsoTerminalTest (B := B) (hS := hS)).inv, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact toUnit_unique _ _

/-- **Translation on points of the representing scheme.** For a `T`-point `x` and an `S`-point
`r` of `P`, the product `x * r_T` maps under `BigFppfOver.toOver` to `x` followed by right
translation by the `S`-point of `P` corresponding to `r`. -/
theorem toOver_map_mul_toUnit {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) {T : BigFppfOver B S hS} (x : T ⟶ P)
    (r : terminalTest B hS ⟶ P) :
    letI := grpObjOfRepresentableBy R
    letI := representingGrpObj R
    (BigFppfOver.toOver B S hS).map (x * (toUnit T ≫ r)) =
      (BigFppfOver.toOver B S hS).map x ≫
        (GrpObj.mulRight ((unitIsoTerminalTest (B := B) (hS := hS)).hom ≫
          (BigFppfOver.toOver B S hS).map r)).hom := by
  let := grpObjOfRepresentableBy R
  let := representingGrpObj R
  rw [Functor.map_mul, GrpObj.mulRight, Hom.mul_def, comp_lift_assoc, Category.comp_id,
    Functor.map_comp, toOver_map_toUnit, Category.assoc, comp_toUnit_assoc]

/-- **The class of a translate.** The class of `x * r_T` is the class of `x` plus the pullback of
the class of `r`. -/
theorem homEquiv_mul_toUnit {P : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P) {T : BigFppfOver B S hS} (x : T ⟶ P)
    (r : terminalTest B hS ⟶ P) :
    letI := grpObjOfRepresentableBy R
    R.homEquiv (x * (toUnit T ≫ r)) =
      R.homEquiv x + (picardFunctor B hX hS f).map (toUnit T).op (R.homEquiv r) := by
  let := grpObjOfRepresentableBy R
  rw [RepresentableBy.homEquiv_mul, R.homEquiv_comp]

/-- **Translates of the chart cover the representing scheme**, as soon as every point of `P` is
carried into `F` by translation by an `S`-point: for every point `p` there is a test scheme `T`,
a `T`-point `x` of `P` through `p` and an `S`-point `r` with `[x] + r_T ∈ F(T)`. -/
theorem exists_rightTranslation_mem_range {P W : BigFppfOver B S hS}
    (R : (picardFunctor B hX hS f).RepresentableBy P)
    (F : ∀ T : BigFppfOver B S hS, Set ((picardFunctor B hX hS f).obj (op T)))
    (j : W ⟶ P)
    (hrange : ∀ {T : BigFppfOver B S hS} (h : T ⟶ P), R.homEquiv h ∈ F T →
        Set.range ((BigFppfOver.toScheme B S hS).map h) ⊆
          Set.range ((BigFppfOver.toScheme B S hS).map j))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj P, ∃ (T : BigFppfOver B S hS) (x : T ⟶ P)
      (t : ((BigFppfOver.toOver B S hS).obj T).left) (r : terminalTest B hS ⟶ P),
        ((BigFppfOver.toOver B S hS).map x).left t = p ∧
          R.homEquiv x + (picardFunctor B hX hS f).map (toUnit T).op (R.homEquiv r) ∈ F T)
    (p : ((BigFppfOver.toOver B S hS).obj P).left) :
    letI := representingGrpObj R
    ∃ r : 𝟙_ (Over S) ⟶ (BigFppfOver.toOver B S hS).obj P,
      (GrpObj.mulRight r).hom.left p ∈ Set.range ((BigFppfOver.toOver B S hS).map j).left := by
  let := grpObjOfRepresentableBy R
  let := representingGrpObj R
  obtain ⟨T, x, t, r, hxt, hF⟩ := hcov p
  rw [← homEquiv_mul_toUnit] at hF
  refine ⟨(unitIsoTerminalTest (B := B) (hS := hS)).hom ≫ (BigFppfOver.toOver B S hS).map r,
    hrange _ hF ⟨t, ?_⟩⟩
  show ((BigFppfOver.toOver B S hS).map (x * (toUnit T ≫ r))).left t = _
  rw [toOver_map_mul_toUnit, Over.comp_left, ← hxt]
  rfl

section Field

variable {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))} {g : B.obj hX ⟶ B.obj hk}

/-- **A scheme representing the Picard functor, with an open represented chart whose translates
cover, is smooth of the chart's relative dimension.** -/
theorem smoothOfRelativeDimension_of_representsOpen {P W : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) (n : ℕ)
    (F : ∀ T : BigFppfOver B (Spec (.of k)) hk, Set ((picardFunctor B hX hk g).obj (op T)))
    (hopen : ∀ (T : BigFppfOver B (Spec (.of k)) hk) (c : (picardFunctor B hX hk g).obj (op T)),
      ∃ U : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).Opens,
        ∀ {T' : BigFppfOver B (Spec (.of k)) hk} (h : T' ⟶ T),
          (picardFunctor B hX hk g).map h.op c ∈ F T' ↔
            Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map h) ⊆ (U : Set _))
    (j : W ⟶ P) (hjF : R.homEquiv j ∈ F W)
    (hjsurj : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (c : (picardFunctor B hX hk g).obj (op T)),
      c ∈ F T → ∃ t : T ⟶ W, R.homEquiv (t ≫ j) = c)
    (hjinj : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t t' : T ⟶ W), t ≫ j = t' ≫ j → t = t')
    (hcov : ∀ p : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj P,
      ∃ (T : BigFppfOver B (Spec (.of k)) hk) (x : T ⟶ P)
      (t : ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).left) (r : terminalTest B hk ⟶ P),
        ((BigFppfOver.toOver B (Spec (.of k)) hk).map x).left t = p ∧
          R.homEquiv x + (picardFunctor B hX hk g).map (toUnit T).op (R.homEquiv r) ∈ F T)
    (hW : SmoothOfRelativeDimension n ((BigFppfOver.toOver B (Spec (.of k)) hk).obj W).hom) :
    SmoothOfRelativeDimension n ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P).hom := by
  let := representingGrpObj R
  obtain ⟨hj, hjr⟩ := isOpenImmersion_of_representsOpen R F hopen j hjF hjsurj hjinj
  have : IsOpenImmersion ((BigFppfOver.toOver B (Spec (.of k)) hk).map j).left := hj
  have : SmoothOfRelativeDimension n (((BigFppfOver.toOver B (Spec (.of k)) hk).map j).left ≫
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P).hom) := by
    rw [Over.w]; exact hW
  exact smoothOfRelativeDimension_of_rightTranslates
    (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)) n
    ((BigFppfOver.toOver B (Spec (.of k)) hk).map j).left
    (fun p => exists_rightTranslation_mem_range R F j (fun h hh => (hjr h).1 hh) hcov p)

end Field

end Stacks.PicardFunctor

end
