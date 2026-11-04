module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdd
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.LocalCharts
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective

/-!
# The degree components of the Picard scheme of a curve, and the Abel map onto them

Let `X` be a smooth projective curve of genus `g` over a separably closed field `k`, with
Picard scheme `Pic_{X/k}` ([Stacks, Tag 0B9Z]). The degree-`d` component `Pic^d_{X/k}` represents
the degree-`d` subfunctor, so the Abel map `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` of the proof of
[Stacks, Tag 0BA0] is defined, and it is surjective for `d ≥ g`. Since `Hilb^g_{X/k}` is a proper
variety ([Stacks, Tag 0B9I]) and `Pic_{X/k}` is separated ([Stacks, Tag 047L]) and smooth, the
component `Pic^g_{X/k}` is proper over `k` and irreducible.

## Main results

* `Stacks.PicardFunctor.degreeComponentRepresentableBy`: `Pic^d_{X/k}` represents the degree-`d`
  subfunctor.
* `Stacks.PicardFunctor.exists_surjective_abelMap_genus`: the Abel map
  `γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}` is surjective.
* `Stacks.PicardFunctor.universallyClosed_picardSchemeDegreeComponent_genus`: `Pic^g_{X/k}` is
  universally closed over `k`, quasi-compact and irreducible.
* `Stacks.PicardFunctor.universallyClosed_picardSchemeDegreeComponent_zero`: `Pic^0_{X/k}` is
  universally closed over `k`, quasi-compact and irreducible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

attribute [local instance] isZariskiLocalAtSource_smoothOfRelativeDimension

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]

/-- The degree-`d` subfunctor of the Picard functor of a pointed smooth projective curve. -/
abbrev curveDegreeSubfunctor (d : ℤ) : Subfunctor (picardFunctor B hX hk f) :=
  degreeSubfunctor B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) d

/-- A morphism of the site over `Spec k` is compatible with the structure morphisms. -/
private theorem inclusion_map_left_comp_inclusion_map_hom {Y Z : BigFppfOver B (Spec (.of k)) hk}
    (φ : Y ⟶ Z) : B.inclusion.map φ.left ≫ B.inclusion.map Z.hom = B.inclusion.map Y.hom := by
  rw [← Functor.map_comp, Over.w]

/-- **`Pic^d_{X/k}` represents the degree-`d` subfunctor.** -/
def degreeComponentRepresentableBy (d : ℤ) :
    (curveDegreeSubfunctor B hX hk f σ hσ d).toFunctor.RepresentableBy
      (picardSchemeDegreeComponent B hX hk f σ hσ d) where
  homEquiv {T} := Equiv.ofBijective
    (fun ψ => ⟨picardHomEquiv B hX hk f (ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d),
      (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ _ d).1 ⟨ψ, rfl⟩⟩)
    ⟨fun ψ₁ ψ₂ h => by
      have : Mono (picardSchemeDegreeComponentι B hX hk f σ hσ d) :=
        AlgebraicGeometry.Space.mono_of_mono_map_toScheme B _ hk _ (by
          change Mono (B.inclusion.map (picardSchemeDegreeComponentι B hX hk f σ hσ d).left)
          rw [inclusion_map_picardSchemeDegreeComponentι]
          exact inferInstanceAs (Mono ((picardScheme B hX hk f).ofRestrict _)))
      exact (cancel_mono _).1 ((picardHomEquiv B hX hk f).injective (congrArg Subtype.val h)),
    fun ζ => by
      obtain ⟨ψ, hψ⟩ := (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ
        ((picardHomEquiv B hX hk f).symm ζ.1) d).2 (by
          rw [Equiv.apply_symm_apply]
          exact ζ.2)
      exact ⟨ψ, Subtype.ext (by
        change picardHomEquiv B hX hk f _ = _
        rw [hψ, Equiv.apply_symm_apply])⟩⟩
  homEquiv_comp {T T'} φ ψ := by
    apply Subtype.ext
    change picardHomEquiv B hX hk f ((φ ≫ ψ) ≫ _) =
      (picardFunctor B hX hk f).map φ.op (picardHomEquiv B hX hk f (ψ ≫ _))
    rw [Category.assoc]
    exact (picardFunctor B hX hk f).representableBy.homEquiv_comp _ _

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The degree-`d` subfunctor of the Picard functor of the curve is a degree-`d` component in the
sense of `Stacks.AbelMap.IsDegreeComponent`. -/
theorem isDegreeComponent_curveDegreeSubfunctor (d : ℕ) :
    Stacks.AbelMap.IsDegreeComponent B hX hk f d (curveDegreeSubfunctor B hX hk f σ hσ d) :=
  isDegreeComponent_degreeSubfunctor B hX hk f σ hσ _ d

/-! ### Translation between degree components -/

omit [GeometricallyIrreducible (B.inclusion.map f)]
    [(picardFunctor B hX hk f).IsRepresentable] in
variable {σ hσ} in
/-- A point of degree `e` over the base has degree `e` on every fibre after restriction. -/
theorem fibreDegree_restrictBase {e : ℤ} (c : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (hc : c ∈ (curveDegreeSubfunctor B hX hk f σ hσ e).obj (op (baseObj B hk)))
    (T : BigFppfOver B (Spec (.of k)) hk) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    curveFibreDegree B hX hk f σ hσ T (restrictBase B hX hk f c T) t = e := by
  rw [restrictBase, curveFibreDegree, fibreDegree_map]
  exact hc _

/-- **Translation by a point of degree `e` identifies the degree-`d` subfunctor with the
degree-`d'` subfunctor, for `d' = d + e`.** -/
def degreeTranslateIso {e : ℤ} (c : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (hc : c ∈ (curveDegreeSubfunctor B hX hk f σ hσ e).obj (op (baseObj B hk)))
    (d d' : ℤ) (hd : d' = d + e) :
    (curveDegreeSubfunctor B hX hk f σ hσ d).toFunctor ≅
      (curveDegreeSubfunctor B hX hk f σ hσ d').toFunctor :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun x => ⟨(restrictBase B hX hk f c T.unop +
          (x.1 : (picardFunctor B hX hk f).obj (op T.unop)) :
            (picardFunctor B hX hk f).obj (op T.unop)), fun t => by
          change curveFibreDegree B hX hk f σ hσ T.unop _ t = d'
          rw [curveFibreDegree, fibreDegree_add, ← curveFibreDegree, ← curveFibreDegree,
            fibreDegree_restrictBase B hX hk f c hc]
          have := x.2 t
          change curveFibreDegree B hX hk f σ hσ T.unop _ t = d at this
          omega⟩
        invFun := fun y => ⟨(-restrictBase B hX hk f c T.unop +
          (y.1 : (picardFunctor B hX hk f).obj (op T.unop)) :
            (picardFunctor B hX hk f).obj (op T.unop)), fun t => by
          change curveFibreDegree B hX hk f σ hσ T.unop _ t = d
          have h1 := fibreDegree_add B hX hk f σ hσ
            (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T.unop
            (restrictBase B hX hk f c T.unop) (-restrictBase B hX hk f c T.unop + y.1) t
          rw [add_neg_cancel_left] at h1
          have h2 := fibreDegree_restrictBase B hX hk f c hc T.unop t
          have h3 := y.2 t
          change curveFibreDegree B hX hk f σ hσ T.unop _ t = d' at h3
          simp only [curveFibreDegree] at h2 h3 ⊢
          omega⟩
        left_inv := fun x => Subtype.ext (neg_add_cancel_left (restrictBase B hX hk f c T.unop)
          (x.1 : (picardFunctor B hX hk f).obj (op T.unop)))
        right_inv := fun y => Subtype.ext (add_neg_cancel_left (restrictBase B hX hk f c T.unop)
          (y.1 : (picardFunctor B hX hk f).obj (op T.unop))) })
    (fun {T T'} φ => by
      ext x
      apply Subtype.ext
      change restrictBase B hX hk f c T'.unop + (picardFunctor B hX hk f).map φ x.1 =
        (picardFunctor B hX hk f).map φ (restrictBase B hX hk f c T.unop + x.1)
      rw [show φ = φ.unop.op from rfl, picardFunctor_map_add, map_restrictBase])

/-- **Translation by a point of degree `e` identifies `Pic^d_{X/k}` with `Pic^{d'}_{X/k}`**,
`d' = d + e`. -/
def picardSchemeDegreeComponentTranslate {e : ℤ}
    (c : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (hc : c ∈ (curveDegreeSubfunctor B hX hk f σ hσ e).obj (op (baseObj B hk)))
    (d d' : ℤ) (hd : d' = d + e) :
    picardSchemeDegreeComponent B hX hk f σ hσ d ≅ picardSchemeDegreeComponent B hX hk f σ hσ d' :=
  (degreeComponentRepresentableBy B hX hk f σ hσ d).uniqueUpToIso
    ((degreeComponentRepresentableBy B hX hk f σ hσ d').ofIso
      (degreeTranslateIso B hX hk f σ hσ c hc d d' hd).symm)

variable [IsSepClosed k]

omit [IsSepClosed k] in
include σ hσ in
/-- **The Abel map `γ_g : Hilb^g_{X/k} ⟶ Pic^g_{X/k}` is surjective**, for a scheme `H`
representing the degree-`g` Hilbert functor (proof of [Stacks, Tag 0BA0], clause (5)). -/
theorem exists_surjective_abelMap_genus :
    ∃ (H : BigFppfOver B (Spec (.of k)) hk)
      (γ : H ⟶ picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))),
      Surjective (B.inclusion.map γ.left) ∧ IsProper (B.inclusion.map H.hom) ∧
        IrreducibleSpace (B.inclusion.obj H.left) := by
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme B hX hk f
  refine ⟨H, Stacks.AbelMap.abelMap B hX hk f
    (isDegreeComponent_curveDegreeSubfunctor B hX hk f σ hσ (genus (B.inclusion.map f))) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ _),
    Stacks.AbelMap.surjective_abelMap B hX hk f σ hσ
      (isDegreeComponent_curveDegreeSubfunctor B hX hk f σ hσ (genus (B.inclusion.map f))) H hH
      (degreeComponentRepresentableBy B hX hk f σ hσ _) le_rfl,
    (Stacks.Hilbert.smoothOfRelativeDimension_and_isProper_of_isCurve k
      (B.inclusion.map f) _ _ hH).2, ?_⟩
  have := (Stacks.Hilbert.isVariety_and_topologicalKrullDim_of_isCurve k
    (B.inclusion.map f) _ _ hH).1
  exact inferInstanceAs (IrreducibleSpace (Over.mk (B.inclusion.map H.hom)).left)

omit [IsSepClosed k] in
include σ hσ in
/-- **`Pic^g_{X/k}` is universally closed over `k`, quasi-compact and irreducible**: it is the
image of the proper irreducible `Hilb^g_{X/k}` under the surjective Abel map. -/
theorem universallyClosed_picardSchemeDegreeComponent_genus :
    UniversallyClosed (B.inclusion.map
        (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).hom) ∧
      CompactSpace (B.inclusion.obj
        (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).left) ∧
      IrreducibleSpace (B.inclusion.obj
        (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).left) := by
  obtain ⟨H, γ, hγ, hHp, hHi⟩ := exists_surjective_abelMap_genus B hX hk f σ hσ
  have hUC : UniversallyClosed (B.inclusion.map γ.left ≫ B.inclusion.map
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).hom) := by
    rw [inclusion_map_left_comp_inclusion_map_hom]
    infer_instance
  have : CompactSpace (B.inclusion.obj (B.obj hk)) := inferInstanceAs (CompactSpace (Spec (.of k)))
  have : CompactSpace (B.inclusion.obj H.left) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map H.hom)
  exact ⟨UniversallyClosed.of_comp_surjective (B.inclusion.map γ.left) _,
    (B.inclusion.map γ.left).surjective.compactSpace (B.inclusion.map γ.left).continuous,
    (B.inclusion.map γ.left).surjective.irreducibleSpace (B.inclusion.map γ.left).continuous⟩

include σ hσ in
/-- **Each degree component of the Picard scheme is smooth of relative dimension `g`**: it is
open in the Picard scheme. -/
theorem smoothOfRelativeDimension_picardSchemeDegreeComponent (d : ℤ) :
    SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ d).hom) := by
  have : AlgebraicGeometry.IsOpenImmersion
      (B.inclusion.map (picardSchemeDegreeComponentι B hX hk f σ hσ d).left) := by
    rw [inclusion_map_picardSchemeDegreeComponentι]
    exact inferInstanceAs
      (AlgebraicGeometry.IsOpenImmersion ((picardScheme B hX hk f).ofRestrict _))
  rw [← inclusion_map_left_comp_inclusion_map_hom B hk
    (picardSchemeDegreeComponentι B hX hk f σ hσ d)]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension (genus (B.inclusion.map f)))
    (smoothOfRelativeDimension_picardScheme B hX hk f σ hσ) _

/-- A section of the structure morphism of an object of the site over `Spec k`, as a morphism of
the site from the base object. -/
def baseObjHomOfSection (Y : BigFppfOver B (Spec (.of k)) hk)
    (q : Spec (.of k) ⟶ B.inclusion.obj Y.left) (hq : q ≫ B.inclusion.map Y.hom = 𝟙 _) :
    baseObj B hk ⟶ Y :=
  Over.homMk (B.inclusion.preimage (X := B.obj hk) (Y := Y.left) q) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hq.trans (B.inclusion.map_id (B.obj hk)).symm)

include σ hσ in
/-- **There is a `k`-rational point of `Pic^g_{X/k}`**: it is nonempty, being the image of the
integral scheme `Hilb^g_{X/k}`, and smooth over the separably closed field `k`. -/
theorem exists_mem_curveDegreeSubfunctor_genus :
    ∃ c : (picardFunctor B hX hk f).obj (op (baseObj B hk)),
      c ∈ (curveDegreeSubfunctor B hX hk f σ hσ (genus (B.inclusion.map f))).obj
        (op (baseObj B hk)) := by
  obtain ⟨H, γ, hγ, -, hHi⟩ := exists_surjective_abelMap_genus B hX hk f σ hσ
  have : Nonempty (B.inclusion.obj H.left) := hHi.toNonempty
  have : Nonempty (B.inclusion.obj
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).left) :=
    ⟨B.inclusion.map γ.left (Classical.arbitrary _)⟩
  have := (smoothOfRelativeDimension_picardSchemeDegreeComponent B hX hk f σ hσ
    (genus (B.inclusion.map f))).smooth
  obtain ⟨q, hq⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed k
    (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).hom)
  exact ⟨_, ((degreeComponentRepresentableBy B hX hk f σ hσ _).homEquiv
    (baseObjHomOfSection B hk _ q hq)).2⟩

include σ hσ in
/-- **`Pic^0_{X/k}` is isomorphic to `Pic^g_{X/k}`**, by translation by a rational point of
degree `g`. -/
theorem nonempty_picardSchemeDegreeComponent_zero_iso_genus :
    Nonempty (picardSchemeDegreeComponent B hX hk f σ hσ 0 ≅
      picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))) := by
  obtain ⟨c, hc⟩ := exists_mem_curveDegreeSubfunctor_genus B hX hk f σ hσ
  exact ⟨picardSchemeDegreeComponentTranslate B hX hk f σ hσ c hc 0 _ (zero_add _).symm⟩

include σ hσ in
/-- **`Pic^0_{X/k}` is universally closed over `k`, quasi-compact and irreducible.** -/
theorem universallyClosed_picardSchemeDegreeComponent_zero :
    UniversallyClosed (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom) ∧
      CompactSpace (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left) ∧
      IrreducibleSpace (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left) := by
  obtain ⟨e⟩ := nonempty_picardSchemeDegreeComponent_zero_iso_genus B hX hk f σ hσ
  obtain ⟨h1, h2, h3⟩ := universallyClosed_picardSchemeDegreeComponent_genus B hX hk f σ hσ
  let e' : B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left ≅
      B.inclusion.obj
        (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).left :=
    (Over.forget _ ⋙ B.inclusion).mapIso e
  have hw : e'.hom ≫ B.inclusion.map
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f))).hom =
      B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom := by
    exact inclusion_map_left_comp_inclusion_map_hom B hk e.hom
  refine ⟨?_, e'.inv.homeomorph.compactSpace,
    e'.inv.surjective.irreducibleSpace e'.inv.continuous⟩
  rw [← hw]
  infer_instance

end Stacks.PicardFunctor

end
