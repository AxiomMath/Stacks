module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism

/-!
# The base-change coherence transported at one object

`StacksFrontier/CategoryTheory/Adjunction/BaseChangeProjectionFormula.lean` identifies `Rg` applied
to the base change map of a square of adjunctions with a projection-formula map, and transports
that identification along two isomorphisms

`ι : Lg ⋙ Rg ≅ A(-, H)` and `ι' : Lg' ⋙ Rg' ≅ B(-, Lf H)`

of the two endofunctors with tensor products.  In the intended geometric situation those two
isomorphisms are [Stacks, Tag 08I9], and they are **not** available as isomorphisms of functors:
[Stacks, Tag 08I9] holds at a complex with quasi-coherent cohomology and not at an arbitrary one,
because the projection formula it is built from — [Stacks, Tag 08EU] — needs quasi-coherence.

This module therefore redoes the transport **one object at a time**.  Every object at which an
identification is needed is named in the hypotheses, so a consumer supplies [Stacks, Tag 08I9]
exactly where it holds.  Three objects occur, and in the geometric situation all three have
quasi-coherent cohomology whenever `K` does: `Rf K`, `Lf (Rf K)` and `K` itself.

## Main results

* `Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_of_map_comp_counit`: a mate is pinned at one
  object by the image of that object's component under `Lf(-) ≫ ε`.
* `Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_adjunctionTensorMap_of_app`: the component
  of the mate at `K` is the projection-formula map of
  `CategoryTheory.adjunctionTensorMap`, conjugated by the two identifications at `Rf K` and at
  `K`.
* `Stacks.CategoryTheory.BaseChange.isIso_mateEquiv_app_of_isIso_adjunctionTensorMap`: the same
  read as a transfer of invertibility.
* `Stacks.CategoryTheory.BaseChange.isIso_pushforward_map_of_isIso_adjunctionTensorMap_app`:
  invertibility of `Rg` applied to the base change map at `K`, which is the form the reduction of
  [Stacks, Tag 08IB] to [Stacks, Tag 08EU] consumes.
* `Stacks.CategoryTheory.BaseChange.map_adjunctionTensorMapRight_comp_counit`,
  `…mateEquiv_app_eq_adjunctionTensorMapRight_of_app`,
  `…isIso_mateEquiv_app_of_isIso_adjunctionTensorMapRight` and
  `…isIso_pushforward_map_of_isIso_adjunctionTensorMapRight_app`: the same four statements with
  the fixed tensor factor on the **left**, which is the order [Stacks, Tag 08I9] produces.  In
  that order the three identifications are [Stacks, Tag 08I9] itself, with no braiding; the
  braiding enters once, to get the interchanged-order projection formula out of
  [Stacks, Tag 08EU].

## Implementation notes

The pinning lemma is the only thing that replaces the global argument.  A mate is determined by
its transpose, so its component at `K` is determined by `Lf(-) ≫ ε` of that component; the
hypothesis of `mateEquiv_app_eq_of_map_comp_counit` is exactly the value
`CategoryTheory.mateEquiv_counit` computes, and `CategoryTheory.adjunctionTensorMap` has the
matching equation `CategoryTheory.map_adjunctionTensorMap_comp_counit`.  Comparing the two is
then one naturality of the counit and one hypothesis.

The hypothesis `hcompat` here is the component at `Rf K` of the equality of 2-squares that
`Stacks.CategoryTheory.BaseChange.pushforward_map_eq_adjunctionTensorMap` asks for globally, and
`hcounit` is the naturality square of the second identification at the single morphism
`ε_K : Lf (Rf K) ⟶ K`.  Neither is weaker than the global datum restricted to these objects;
they are literally its components, so a consumer with the global datum can discharge them by
`congrArg`, and a consumer with only the quasi-coherent case — which is the geometric one — can
discharge them where it holds.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### A mate is pinned at one object -/

section Pointwise

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  {Lf : A ⥤ B} {Rf : B ⥤ A} {M : A ⥤ A} {M' : B ⥤ B}

/-- **A mate is pinned at one object by its transpose there.**  For a 2-square
`w : M ⋙ Lf ⟶ Lf ⋙ M'` and an adjunction `Lf ⊣ Rf`, a morphism
`u : M (Rf K) ⟶ Rf (M' K)` whose image under `Lf(-) ≫ ε` is the value
`CategoryTheory.mateEquiv_counit` computes is the component of the mate at `K`.

This is what replaces the global transport: `CategoryTheory.mateEquiv` is a bijection, so the
component of a mate at one object is determined by its transpose at that object, and nothing
about the square at other objects enters. -/
theorem mateEquiv_app_eq_of_map_comp_counit (adjf : Lf ⊣ Rf) (w : TwoSquare M Lf Lf M') (K : B)
    (u : M.obj (Rf.obj K) ⟶ Rf.obj (M'.obj K))
    (hu : Lf.map u ≫ adjf.counit.app (M'.obj K) =
      w.natTrans.app (Rf.obj K) ≫ M'.map (adjf.counit.app K)) :
    (mateEquiv adjf adjf w).natTrans.app K = u := by
  have hinj : ∀ a b : M.obj (Rf.obj K) ⟶ Rf.obj (M'.obj K),
      Lf.map a ≫ adjf.counit.app (M'.obj K) =
        Lf.map b ≫ adjf.counit.app (M'.obj K) → a = b := by
    intro a b h
    refine (adjf.homEquiv _ _).symm.injective ?_
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    exact h
  exact hinj _ _ ((mateEquiv_counit adjf adjf w K).trans hu.symm)

/-- The mate at `K` is a conjugate of `a` when `a` and the identifications are compatible with
`w` and the counit. -/
private theorem mateEquiv_app_eq_comp_of_counit (adjf : Lf ⊣ Rf) (w : TwoSquare M Lf Lf M') (K : B)
    {Y₂ Y₃ : B} {X' : A} (ι₁ : M.obj (Rf.obj K) ≅ X') (ι₂ : M'.obj (Lf.obj (Rf.obj K)) ≅ Y₂)
    (ι₃ : M'.obj K ≅ Y₃) (β : Lf.obj X' ⟶ Y₂) (c : Y₂ ⟶ Y₃) (a : X' ⟶ Rf.obj Y₃)
    (ha : Lf.map a ≫ adjf.counit.app Y₃ = β ≫ c)
    (hcompat : w.natTrans.app (Rf.obj K) = Lf.map ι₁.hom ≫ β ≫ ι₂.inv)
    (hcounit : M'.map (adjf.counit.app K) ≫ ι₃.hom = ι₂.hom ≫ c) :
    (mateEquiv adjf adjf w).natTrans.app K = ι₁.hom ≫ a ≫ Rf.map ι₃.inv := by
  refine mateEquiv_app_eq_of_map_comp_counit adjf w K _ ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    adjf.counit_naturality ι₃.inv, reassoc_of% ha, hcompat, Category.assoc, Category.assoc]
  congr 2
  rw [Iso.comp_inv_eq, Category.assoc, hcounit, ι₂.inv_hom_id_assoc]

variable (adjf : Lf ⊣ Rf) (w : TwoSquare M Lf Lf M')
  (TA : A × A ⥤ A) (TB : B × B ⥤ B) (α : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (H : A)

/-- **The coherence transported at one object.**  Let the endofunctor `M` be identified at
`Rf K` with `TA(-, H)`, and the endofunctor `M'` be identified at `Lf (Rf K)` and at `K` with
`TB(-, Lf H)`, compatibly with the 2-square `w` at `Rf K` (`hcompat`) and with the counit at `K`
(`hcounit`).  Then the component of the mate of `w` at `K` is the projection-formula map

`TA (Rf K, H) ⟶ Rf (TB (K, Lf H))`

of `CategoryTheory.adjunctionTensorMap`, conjugated by the identifications at `Rf K` and at `K`.

The identification at `Lf (Rf K)` appears only in the two hypotheses; it is the object where the
2-square `w` lands, and in the geometric situation of [Stacks, Tag 08IB] it is `Lf^*Rf_*K`, whose
cohomology is quasi-coherent with that of `K`. -/
theorem mateEquiv_app_eq_adjunctionTensorMap_of_app (K : B)
    (ι₁ : M.obj (Rf.obj K) ≅ TA.obj (Rf.obj K, H))
    (ι₂ : M'.obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj (Rf.obj K), Lf.obj H))
    (ι₃ : M'.obj K ≅ TB.obj (K, Lf.obj H))
    (hcompat : w.natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (Rf.obj K, H) ≫ ι₂.inv)
    (hcounit : M'.map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (adjf.counit.app K ×ₘ 𝟙 (Lf.obj H))) :
    (mateEquiv adjf adjf w).natTrans.app K =
      ι₁.hom ≫ CategoryTheory.adjunctionTensorMap adjf TA TB α K H ≫ Rf.map ι₃.inv := by
  exact mateEquiv_app_eq_comp_of_counit adjf w K ι₁ ι₂ ι₃ _ _ _
    (CategoryTheory.map_adjunctionTensorMap_comp_counit adjf TA TB α K H) hcompat hcounit

/-- **Invertibility transfers at one object.**  Under the hypotheses of
`Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_adjunctionTensorMap_of_app`, the component of
the mate at `K` is invertible as soon as the projection-formula map is: the two conjugating
morphisms are isomorphisms. -/
theorem isIso_mateEquiv_app_of_isIso_adjunctionTensorMap (K : B)
    (ι₁ : M.obj (Rf.obj K) ≅ TA.obj (Rf.obj K, H))
    (ι₂ : M'.obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj (Rf.obj K), Lf.obj H))
    (ι₃ : M'.obj K ≅ TB.obj (K, Lf.obj H))
    (hcompat : w.natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (Rf.obj K, H) ≫ ι₂.inv)
    (hcounit : M'.map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (adjf.counit.app K ×ₘ 𝟙 (Lf.obj H)))
    (h : IsIso (CategoryTheory.adjunctionTensorMap adjf TA TB α K H)) :
    IsIso ((mateEquiv adjf adjf w).natTrans.app K) := by
  rw [mateEquiv_app_eq_adjunctionTensorMap_of_app adjf w TA TB α H K ι₁ ι₂ ι₃ hcompat hcounit]
  infer_instance

/-- **The defining equation of the interchanged-order projection-formula map, transposed.**  The
analogue of `CategoryTheory.map_adjunctionTensorMap_comp_counit` for
`Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight`, whose counit is taken in the second
tensor factor. -/
@[reassoc]
theorem map_adjunctionTensorMapRight_comp_counit (G : B) :
    Lf.map (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB α H G) ≫
        adjf.counit.app (TB.obj (Lf.obj H, G)) =
      α.app (H, Rf.obj G) ≫ TB.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G) := by
  have h := (adjf.homEquiv (TA.obj (H, Rf.obj G)) (TB.obj (Lf.obj H, G))).symm_apply_apply
    (α.app (H, Rf.obj G) ≫ TB.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G))
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- **The coherence transported at one object, with the fixed tensor factor on the left.**  The
variant of `Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_adjunctionTensorMap_of_app` in
which the two endofunctors are identified with `TA(H, -)` and `TB(Lf H, -)` rather than with
`TA(-, H)` and `TB(-, Lf H)`.

This is the order [Stacks, Tag 08I9] produces — it identifies `Rg_*Lg^*E` with
`g_*𝒪_{S'} ⊗^𝐋 E`, the fixed factor on the left — so the geometric application needs no
braiding to build the three identifications.  The braiding enters once, and only to get
invertibility of the interchanged-order projection-formula map out of [Stacks, Tag 08EU], which
is `Stacks.Cohomology.DerivedKunneth.isIso_adjunctionTensorMapRight_of_braiding`. -/
theorem mateEquiv_app_eq_adjunctionTensorMapRight_of_app (K : B)
    (ι₁ : M.obj (Rf.obj K) ≅ TA.obj (H, Rf.obj K))
    (ι₂ : M'.obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj H, Lf.obj (Rf.obj K)))
    (ι₃ : M'.obj K ≅ TB.obj (Lf.obj H, K))
    (hcompat : w.natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (H, Rf.obj K) ≫ ι₂.inv)
    (hcounit : M'.map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app K)) :
    (mateEquiv adjf adjf w).natTrans.app K =
      ι₁.hom ≫ Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB α H K ≫
        Rf.map ι₃.inv := by
  exact mateEquiv_app_eq_comp_of_counit adjf w K ι₁ ι₂ ι₃ _ _ _
    (map_adjunctionTensorMapRight_comp_counit adjf TA TB α H K) hcompat hcounit

/-- **Invertibility transfers at one object, with the fixed tensor factor on the left.** -/
theorem isIso_mateEquiv_app_of_isIso_adjunctionTensorMapRight (K : B)
    (ι₁ : M.obj (Rf.obj K) ≅ TA.obj (H, Rf.obj K))
    (ι₂ : M'.obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj H, Lf.obj (Rf.obj K)))
    (ι₃ : M'.obj K ≅ TB.obj (Lf.obj H, K))
    (hcompat : w.natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (H, Rf.obj K) ≫ ι₂.inv)
    (hcounit : M'.map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app K))
    (h : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB α H K)) :
    IsIso ((mateEquiv adjf adjf w).natTrans.app K) := by
  rw [mateEquiv_app_eq_adjunctionTensorMapRight_of_app adjf w TA TB α H K ι₁ ι₂ ι₃
    hcompat hcounit]
  infer_instance

end Pointwise

/-! ### The form the reduction of [Stacks, Tag 08IB] consumes -/

section Square

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {Lc : A ⥤ B'}

variable (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TA : A × A ⥤ A) (TB : B × B ⥤ B) (α : TA ⋙ Lf ⟶ Lf.prod Lf ⋙ TB) (H : A)

/-- **`Rg` applied to the base change map at `K` is invertible when the projection-formula map
at `K` is.**  The hypotheses identify the two endofunctors `Lg ⋙ Rg` and `Lg' ⋙ Rg'` with
tensoring by `H` and by `Lf H` at the three objects where the coherence needs them — `Rf K`,
`Lf (Rf K)` and `K` — and assert the compatibility of those identifications with the canonical
comparison `Stacks.CategoryTheory.BaseChange.pullbackPushforwardSquare` at `Rf K` and with the
counit at `K`.

This is `Stacks.CategoryTheory.BaseChange.isIso_pushforward_map_of_isIso_adjunctionTensorMap`
with every datum taken at an object rather than as a natural transformation, which is what the
geometric application needs: [Stacks, Tag 08I9] identifies `Rg_*Lg^*` with tensoring by
`g_*𝒪_{S'}` only on complexes with quasi-coherent cohomology. -/
theorem isIso_pushforward_map_of_isIso_adjunctionTensorMap_app (K : B)
    (ι₁ : (Lg ⋙ Rg).obj (Rf.obj K) ≅ TA.obj (Rf.obj K, H))
    (ι₂ : (Lg' ⋙ Rg').obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj (Rf.obj K), Lf.obj H))
    (ι₃ : (Lg' ⋙ Rg').obj K ≅ TB.obj (K, Lf.obj H))
    (hcompat : (pullbackPushforwardSquare adjg adjg' eg ef).natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (Rf.obj K, H) ≫ ι₂.inv)
    (hcounit : (Lg' ⋙ Rg').map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (adjf.counit.app K ×ₘ 𝟙 (Lf.obj H)))
    (h : IsIso (CategoryTheory.adjunctionTensorMap adjf TA TB α K H)) :
    IsIso (Rg.map (map adjf adjf' eg ef K)) := by
  rw [isIso_pushforward_map_iff adjf adjf' adjg adjg' eg ef K, projectionTwoSquare]
  exact isIso_mateEquiv_app_of_isIso_adjunctionTensorMap adjf
    (pullbackPushforwardSquare adjg adjg' eg ef) TA TB α H K ι₁ ι₂ ι₃ hcompat hcounit h

/-- **`Rg` applied to the base change map at `K` is invertible when the interchanged-order
projection-formula map at `K` is.**  The variant of
`Stacks.CategoryTheory.BaseChange.isIso_pushforward_map_of_isIso_adjunctionTensorMap_app` whose
three identifications put the fixed tensor factor on the left, which is the order
[Stacks, Tag 08I9] produces. -/
theorem isIso_pushforward_map_of_isIso_adjunctionTensorMapRight_app (K : B)
    (ι₁ : (Lg ⋙ Rg).obj (Rf.obj K) ≅ TA.obj (H, Rf.obj K))
    (ι₂ : (Lg' ⋙ Rg').obj (Lf.obj (Rf.obj K)) ≅ TB.obj (Lf.obj H, Lf.obj (Rf.obj K)))
    (ι₃ : (Lg' ⋙ Rg').obj K ≅ TB.obj (Lf.obj H, K))
    (hcompat : (pullbackPushforwardSquare adjg adjg' eg ef).natTrans.app (Rf.obj K) =
      Lf.map ι₁.hom ≫ α.app (H, Rf.obj K) ≫ ι₂.inv)
    (hcounit : (Lg' ⋙ Rg').map (adjf.counit.app K) ≫ ι₃.hom =
      ι₂.hom ≫ TB.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app K))
    (h : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight adjf TA TB α H K)) :
    IsIso (Rg.map (map adjf adjf' eg ef K)) := by
  rw [isIso_pushforward_map_iff adjf adjf' adjg adjg' eg ef K, projectionTwoSquare]
  exact isIso_mateEquiv_app_of_isIso_adjunctionTensorMapRight adjf
    (pullbackPushforwardSquare adjg adjg' eg ef) TA TB α H K ι₁ ι₂ ι₃ hcompat hcounit h

end Square

end Stacks.CategoryTheory.BaseChange

end
