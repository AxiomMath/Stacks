module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.GroupSchemeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.OpenSubfunctor

/-!
# The translated charts of a group scheme obtained from Stacks 0B9Q

The group-scheme criterion `AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor`
([Stacks, Tag 0B9Q]) produces a group scheme `A` over a field `k` representing a Zariski sheaf of
groups `G`, from an open subfunctor `F ⊆ G` represented by a scheme `Y` whose translates by
`k`-rational points meet every field-valued point. Its proof shows more, and the source uses
that more in [Stacks, Tag 0BA0]: `Y` is an open subscheme of `A`, and the translates of this open
by the `k`-rational points of `A` cover `A`. This file proves that, for an arbitrary group scheme
`A` representing `G`; so every property of `Y` over `k` which is local on the source, such as
smoothness or local finiteness of type, passes to `A`.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_chart` — the open immersion `Y ⟶ A`.
* `AlgebraicGeometry.exists_translate_mem_range` — every point of `A` lies in a translate of the
  chart by a `k`-rational point.
* `AlgebraicGeometry.of_chart_of_isZariskiLocalAtSource` — a property local on the source which
  holds for `Y ⟶ Spec k` holds for `A ⟶ Spec k`.

## References

* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u}}
  (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ G)

/-- The isomorphism of presheaves of sets between the functor of points of `A` and `G`. -/
def representingIsoOfGrp : yoneda.obj A.X ≅ G ⋙ forget GrpCat :=
  NatIso.ofComponents (fun T => Functor.mapIso (forget GrpCat) (e.app T)) fun g => by
    ext x
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) (e.hom.naturality g)

/-- **The chart is an open subscheme.** If `A` represents `G` and the open subfunctor `F ⊆ G` is
represented by `Y`, the induced morphism `Y ⟶ A` is an open immersion. -/
theorem exists_isOpenImmersion_chart (F : Subfunctor (G ⋙ forget GrpCat)) (Y : Over (Spec (.of k)))
    (eF : yoneda.obj Y ≅ F.toFunctor)
    (hopen : (IsOpenImmersion.over (X := Spec (.of k))).presheaf F.ι) :
    ∃ j : Y ⟶ A.X, IsOpenImmersion j.left ∧
      yoneda.map j ≫ (representingIsoOfGrp A e).hom = eF.hom ≫ F.ι := by
  let φ : yoneda.obj Y ⟶ yoneda.obj A.X := eF.hom ≫ F.ι ≫ (representingIsoOfGrp A e).inv
  refine ⟨Yoneda.fullyFaithful.preimage φ, ?_, ?_⟩
  · refine MorphismProperty.of_relative_map (P := IsOpenImmersion.over (X := Spec (.of k)))
      (F := yoneda) ?_
    rw [Functor.FullyFaithful.map_preimage]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
      ((MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hopen)
  · rw [Functor.FullyFaithful.map_preimage]
    simp [φ]

/-- The structure morphism of an `S`-scheme, as a morphism to the terminal `S`-scheme. -/
abbrev grpToBase (Y : Over (Spec (.of k))) : Y ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk Y.hom

/-- Composing a morphism of `S`-schemes `g : Y ⟶ Z` with the structure morphism of `Z` gives the
structure morphism of `Y`. -/
theorem comp_grpToBase {Y Z : Over (Spec (.of k))} (g : Y ⟶ Z) : g ≫ grpToBase Z = grpToBase Y := by
  ext
  simp

/-- **Translation by a rational point** `r` of the group scheme `A`: the morphism `a ↦ r · a`. -/
def grpTranslate (r : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) : A.X ⟶ A.X :=
  (grpToBase A.X ≫ r) * 𝟙 A.X

/-- Composing `g : Y ⟶ A` with translation by `r` gives the product of `g` with the constant
morphism `Y ⟶ A` with value `r`. -/
theorem comp_grpTranslate {Y : Over (Spec (.of k))} (g : Y ⟶ A.X)
    (r : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) :
    g ≫ grpTranslate A r = (grpToBase Y ≫ r) * g := by
  rw [grpTranslate, MonObj.comp_mul, ← Category.assoc, comp_grpToBase, Category.comp_id]

/-- Translation by `r` followed by translation by `r'` is translation by `r' * r`. -/
theorem grpTranslate_comp_grpTranslate (r r' : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) :
    grpTranslate A r ≫ grpTranslate A r' = grpTranslate A (r' * r) := by
  rw [comp_grpTranslate, grpTranslate, grpTranslate, MonObj.comp_mul, ← mul_assoc]

/-- Translation by the identity point is the identity of `A`. -/
theorem grpTranslate_one : grpTranslate A 1 = 𝟙 A.X := by
  rw [grpTranslate, MonObj.comp_one, one_mul]

/-- Translation by a rational point `r` is an isomorphism, with inverse translation by `r⁻¹`. -/
instance (r : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X) : IsIso (grpTranslate A r) :=
  ⟨grpTranslate A r⁻¹, by rw [grpTranslate_comp_grpTranslate, inv_mul_cancel, grpTranslate_one],
    by rw [grpTranslate_comp_grpTranslate, mul_inv_cancel, grpTranslate_one]⟩

/-- **The translates of the chart cover the group scheme.** Under the hypotheses of
[Stacks, Tag 0B9Q], every point of a group scheme `A` representing `G` lies in the image of the
chart `Y ⟶ A` followed by translation by a `k`-rational point. -/
theorem exists_translate_mem_range (F : Subfunctor (G ⋙ forget GrpCat)) (Y : Over (Spec (.of k)))
    (eF : yoneda.obj Y ≅ F.toFunctor) (j : Y ⟶ A.X)
    (hj : yoneda.map j ≫ (representingIsoOfGrp A e).hom = eF.hom ≫ F.ι)
    (hfield : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (op (fieldExtensionPoint k K))),
      ∃ g' : G.obj (op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (fieldExtensionPoint k K).hom).op).hom g' * g ∈
          F.obj (op (fieldExtensionPoint k K)))
    (a : A.X.left) :
    ∃ r : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X, a ∈ Set.range (j ≫ grpTranslate A r).left := by
  let K : Type u := A.X.left.residueField a
  let α : Spec (A.X.left.residueField a) ⟶ Spec (.of k) := A.X.left.fromSpecResidueField a ≫ A.X.hom
  let : Algebra k K := RingHom.toAlgebra (Spec.homEquiv α).hom
  let V : Over (Spec (.of k)) := fieldExtensionPoint k K
  have hbase : V.hom = α := by
    apply Spec.homEquiv.injective
    simp [V, fieldExtensionPoint, α, RingHom.algebraMap_toAlgebra]
  let γ : V ⟶ A.X := Over.homMk (A.X.left.fromSpecResidueField a) hbase.symm
  obtain ⟨r₀, hr₀⟩ := hfield K ((e.hom.app (op V)).hom γ)
  let r : Over.mk (𝟙 (Spec (.of k))) ⟶ A.X := (e.inv.app (op _)).hom r₀
  have hr : (e.hom.app (op _)).hom r = r₀ := by
    simp [r]
  let z : V ⟶ A.X := (grpToBase V ≫ r) * γ
  have hz : (e.hom.app (op V)).hom z =
      (G.map (Over.homMk (fieldExtensionPoint k K).hom).op).hom r₀ *
        (e.hom.app (op V)).hom γ := by
    refine ((e.hom.app (op V)).hom.map_mul (grpToBase V ≫ r) γ).trans (congrArg (· * _) ?_)
    rw [← hr]
    exact congrArg (fun φ => GrpCat.Hom.hom φ r) (e.hom.naturality (grpToBase V).op)
  let zF : F.toFunctor.obj (op V) := ⟨(e.hom.app (op V)).hom z, hz ▸ hr₀⟩
  let t : V ⟶ Y := (eF.inv.app (op V)) zF
  have ht : t ≫ j = z := by
    have h1 := congrArg (fun φ => (ConcreteCategory.hom (φ.app (op V))) t) hj
    simp only [NatTrans.comp_app_apply, yoneda_map_app] at h1
    have h2 : F.ι.app (op V) ((eF.hom.app (op V)) t) = (e.hom.app (op V)).hom z := by
      simp [t]
      rfl
    have h3 : (representingIsoOfGrp A e).hom.app (op V) (t ≫ j) =
        (representingIsoOfGrp A e).hom.app (op V) z := h1.trans h2
    simpa using congrArg ((representingIsoOfGrp A e).inv.app (op V)) h3
  have hγ : γ = t ≫ j ≫ grpTranslate A r⁻¹ := by
    rw [comp_grpTranslate, MonObj.comp_mul, ← Category.assoc, comp_grpToBase, ht]
    show γ = (grpToBase V ≫ r⁻¹) * ((grpToBase V ≫ r) * γ)
    rw [Hom.inv_def r, ← Category.assoc, ← Hom.inv_def, ← mul_assoc, inv_mul_cancel, one_mul]
  let p : V.left := show PrimeSpectrum K from IsLocalRing.closedPoint K
  refine ⟨r⁻¹, t.left p, ?_⟩
  have hγl : t.left ≫ (j ≫ grpTranslate A r⁻¹).left = A.X.left.fromSpecResidueField a := by
    rw [← Over.comp_left, ← hγ]
    rfl
  show (t.left ≫ (j ≫ grpTranslate A r⁻¹).left) p = a
  rw [hγl]
  exact A.X.left.fromSpecResidueField_apply a _

include e in
/-- **Properties local on the source pass from the chart to the group scheme.** Under the
hypotheses of [Stacks, Tag 0B9Q], if the scheme `Y` representing the open subfunctor `F` has a
property `P` over `k` which is local on the source (smoothness, local finiteness of type, …),
then so has every group scheme `A` representing `G`: `A` is covered by the translates of the
open chart `Y ⟶ A` by its `k`-rational points, and translations are automorphisms over `k`. -/
theorem of_chart_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P] (F : Subfunctor (G ⋙ forget GrpCat)) (Y : Over (Spec (.of k)))
    (eF : yoneda.obj Y ≅ F.toFunctor)
    (hopen : (IsOpenImmersion.over (X := Spec (.of k))).presheaf F.ι)
    (hfield : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (op (fieldExtensionPoint k K))),
      ∃ g' : G.obj (op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (fieldExtensionPoint k K).hom).op).hom g' * g ∈
          F.obj (op (fieldExtensionPoint k K)))
    (hY : P Y.hom) : P A.X.hom := by
  obtain ⟨j, hjo, hj⟩ := exists_isOpenImmersion_chart A e F Y eF hopen
  choose r hr using exists_translate_mem_range A e F Y eF j hj hfield
  let 𝒰 : A.X.left.OpenCover := Scheme.Cover.mkOfCovers A.X.left (fun _ => Y.left)
    (fun a => (j ≫ grpTranslate A (r a)).left) (fun a => ⟨a, hr a⟩) (fun a => by
        rw [Over.comp_left]
        have : IsIso (grpTranslate A (r a)).left :=
          (inferInstance : IsIso ((Over.forget _).map (grpTranslate A (r a))))
        exact IsOpenImmersion.comp _ _)
  refine IsZariskiLocalAtSource.of_openCover 𝒰 fun a => ?_
  show P ((j ≫ grpTranslate A (r a)).left ≫ A.X.hom)
  rw [Over.w (j ≫ grpTranslate A (r a))]
  exact hY

end AlgebraicGeometry

end
