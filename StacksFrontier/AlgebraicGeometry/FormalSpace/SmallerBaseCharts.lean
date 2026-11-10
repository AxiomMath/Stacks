module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseAlgebraicSpaces

/-!
# Charts of large-valued presheaves over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B`, and let `G` be a presheaf with values in
`Type (u + 1)` on the big fppf site of `V`, with attached presheaf
`AlgebraicGeometry.FormalSpace.smallerBaseULift` on the big fppf site of `S` (Stacks 04SG). This
file shows that the conditions on morphisms used for formal algebraic spaces — representability
by algebraic spaces, étaleness, the property of representable morphisms of being étale, and the
every-étale-chart conditions — do not see the change of base.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_smallerBaseChart_iff`: a property of a chart, tested on
  representable base changes, holds over `S` for the attached chart exactly when it holds over
  `V`.
* `AlgebraicGeometry.FormalSpace.isEtaleULift_smallerBaseULiftMap_iff`,
  `AlgebraicGeometry.FormalSpace.holdsOnEveryEtaleChartULift_smallerBaseULiftMap_iff`,
  `AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff`
  and `AlgebraicGeometry.FormalSpace.hasPropertyULift_isEtaleULift_smallerBaseULiftMap_iff`:
  the corresponding conditions on morphisms.

## Implementation notes

The proofs are those of the presheaf-level statements for values in `Type u`
(`AlgebraicGeometry.presheaf_relocalizeChart_iff`,
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`), read for the
universe-lifted Yoneda embedding: every chart of the attached presheaf is an attached chart
(`AlgebraicGeometry.FormalSpace.exists_smallerBaseChart`), the attached presheaf preserves and
reflects fibre products, and corresponding objects of the two sites have the same underlying
scheme.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-! ### Exactness -/

/-- The functor attaching to a presheaf on the big fppf site of `V` its presheaf on the big fppf
site of `S`. -/
abbrev smallerBaseULiftFunctor :
    ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  (smallerBasePresheafEquivalenceULift B V S hV hS g).functor ⋙ Over.forget _

/-- The functor `smallerBaseULiftFunctor` preserves fibre products. -/
instance : PreservesLimitsOfShape WalkingCospan (smallerBaseULiftFunctor B V S hV hS g) := by
  dsimp only [smallerBaseULiftFunctor]
  infer_instance

/-- The functor `smallerBaseULiftFunctor` is faithful. -/
instance : (smallerBaseULiftFunctor B V S hV hS g).Faithful := by
  dsimp only [smallerBaseULiftFunctor]
  infer_instance

/-- The functor `smallerBaseULiftFunctor` reflects isomorphisms. -/
instance : (smallerBaseULiftFunctor B V S hV hS g).ReflectsIsomorphisms := by
  dsimp only [smallerBaseULiftFunctor]
  infer_instance

/-- The functor `smallerBaseULiftFunctor` reflects fibre products. -/
instance : ReflectsLimitsOfShape WalkingCospan (smallerBaseULiftFunctor B V S hV hS g) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

/-- Induced morphisms of attached presheaves are injective. -/
theorem smallerBaseULiftMap_injective {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {f f' : G ⟶ G'}
    (h : smallerBaseULiftMap B V S hV hS g f = smallerBaseULiftMap B V S hV hS g f') :
    f = f' :=
  (smallerBaseULiftFunctor B V S hV hS g).map_injective h

/-- **The attached presheaf preserves fibre products.** -/
theorem isPullback_smallerBaseULiftMap {P G G' K : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {p : P ⟶ G} {q : P ⟶ G'} {a : G ⟶ K} {b : G' ⟶ K} (h : IsPullback p q a b) :
    IsPullback (smallerBaseULiftMap B V S hV hS g p) (smallerBaseULiftMap B V S hV hS g q)
      (smallerBaseULiftMap B V S hV hS g a) (smallerBaseULiftMap B V S hV hS g b) :=
  h.map (smallerBaseULiftFunctor B V S hV hS g)

/-- **The attached presheaf reflects fibre products.** -/
theorem isPullback_of_isPullback_smallerBaseULiftMap
    {P G G' K : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {p : P ⟶ G} {q : P ⟶ G'} {a : G ⟶ K} {b : G' ⟶ K}
    (h : IsPullback (smallerBaseULiftMap B V S hV hS g p) (smallerBaseULiftMap B V S hV hS g q)
      (smallerBaseULiftMap B V S hV hS g a) (smallerBaseULiftMap B V S hV hS g b)) :
    IsPullback p q a b := by
  refine IsPullback.of_map (smallerBaseULiftFunctor B V S hV hS g)
    (smallerBaseULiftMap_injective B V S hV hS g ?_) h
  simpa only [← smallerBaseULiftMap_comp] using h.w

/-! ### Representable base changes of a chart -/

/-- **The attached presheaf of a representable base change of a chart is a representable base
change of the attached chart.** -/
theorem isPullback_smallerBaseChart {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ V₀ T₀ : BigFppfOver B V hV} {a : uliftYoneda.{u + 1}.obj U₀ ⟶ G}
    {e : uliftYoneda.{u + 1}.obj V₀ ⟶ G} {p : T₀ ⟶ U₀} {r : T₀ ⟶ V₀}
    (hp : IsPullback (uliftYoneda.{u + 1}.map p) (uliftYoneda.{u + 1}.map r) a e) :
    IsPullback (uliftYoneda.{u + 1}.map ((Over.map g).map p))
      (uliftYoneda.{u + 1}.map ((Over.map g).map r))
      (smallerBaseChart B V S hV hS g a) (smallerBaseChart B V S hV hS g e) := by
  refine (isPullback_smallerBaseULiftMap B V S hV hS g hp).of_iso
    (smallerBaseULiftYonedaIso B V S hV hS g T₀)
    (smallerBaseULiftYonedaIso B V S hV hS g U₀)
    (smallerBaseULiftYonedaIso B V S hV hS g V₀)
    (Iso.refl _) (smallerBaseULiftYonedaIso_hom_naturality B V S hV hS g p)
    (smallerBaseULiftYonedaIso_hom_naturality B V S hV hS g r)
    (by simp [smallerBaseChart]) (by simp [smallerBaseChart])

/-- The converse of `AlgebraicGeometry.FormalSpace.isPullback_smallerBaseChart`. -/
theorem isPullback_of_isPullback_smallerBaseChart {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    {U₀ V₀ T₀ : BigFppfOver B V hV} {a : uliftYoneda.{u + 1}.obj U₀ ⟶ G}
    {e : uliftYoneda.{u + 1}.obj V₀ ⟶ G} {p : T₀ ⟶ U₀} {r : T₀ ⟶ V₀}
    (hp : IsPullback (uliftYoneda.{u + 1}.map ((Over.map g).map p))
      (uliftYoneda.{u + 1}.map ((Over.map g).map r))
      (smallerBaseChart B V S hV hS g a) (smallerBaseChart B V S hV hS g e)) :
    IsPullback (uliftYoneda.{u + 1}.map p) (uliftYoneda.{u + 1}.map r) a e := by
  have key : ∀ {X Y : BigFppfOver B V hV} (m : X ⟶ Y),
      uliftYoneda.{u + 1}.map ((Over.map g).map m) ≫
          (smallerBaseULiftYonedaIso B V S hV hS g Y).inv =
        (smallerBaseULiftYonedaIso B V S hV hS g X).inv ≫
          smallerBaseULiftMap B V S hV hS g (uliftYoneda.{u + 1}.map m) := fun m ↦ by
    rw [Iso.comp_inv_eq, Category.assoc, smallerBaseULiftYonedaIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  refine isPullback_of_isPullback_smallerBaseULiftMap B V S hV hS g ?_
  refine hp.of_iso
    (smallerBaseULiftYonedaIso B V S hV hS g T₀).symm
    (smallerBaseULiftYonedaIso B V S hV hS g U₀).symm
    (smallerBaseULiftYonedaIso B V S hV hS g V₀).symm
    (Iso.refl _) (key p) (key r) (by simp [smallerBaseChart]) (by simp [smallerBaseChart])

/-- A property of a chart, tested on representable base changes, holds over `V` when it holds
for the attached chart over `S`. -/
theorem relative_of_relative_smallerBaseChart (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} {U₀ : BigFppfOver B V hV}
    (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G)
    (ha' : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative
      uliftYoneda.{u + 1} (smallerBaseChart B V S hV hS g a)) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
      uliftYoneda.{u + 1} a := by
  refine MorphismProperty.relative.of_exists (F := uliftYoneda.{u + 1}) fun V₀ e₀ ↦ ?_
  have hQ' := ha'.2 (smallerBaseChart B V S hV hS g e₀)
    (ha'.1.fst (smallerBaseChart B V S hV hS g e₀))
    (ha'.1.snd (smallerBaseChart B V S hV hS g e₀))
    (ha'.1.isPullback (smallerBaseChart B V S hV hS g e₀))
  set T' := ha'.1.pullback (smallerBaseChart B V S hV hS g e₀)
  set snd' := ha'.1.snd (smallerBaseChart B V S hV hS g e₀)
  set φ' : T' ⟶ (Over.map g).obj U₀ :=
    uliftYoneda.{u + 1}.preimage (ha'.1.fst (smallerBaseChart B V S hV hS g e₀))
  have hφ' : uliftYoneda.{u + 1}.map φ' = ha'.1.fst (smallerBaseChart B V S hV hS g e₀) :=
    uliftYoneda.{u + 1}.map_preimage _
  have hsq : IsPullback (uliftYoneda.{u + 1}.map φ') (uliftYoneda.{u + 1}.map snd')
      (smallerBaseChart B V S hV hS g a) (smallerBaseChart B V S hV hS g e₀) := by
    rw [hφ']
    exact ha'.1.isPullback _
  have hbase : φ' ≫ relocalizeOverHom B V S hV hS g U₀
      = snd' ≫ relocalizeOverHom B V S hV hS g V₀ := by
    apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, Functor.map_comp,
      ← smallerBaseChart_comp_hom B V S hV hS g a,
      ← smallerBaseChart_comp_hom B V S hV hS g e₀,
      ← Category.assoc, ← Category.assoc, hsq.w]
  have hτ : (snd'.left ≫ V₀.hom) ≫ g = T'.hom := by
    rw [Category.assoc]
    exact Over.w snd'
  set T₀ : BigFppfOver B V hV := Over.mk (snd'.left ≫ V₀.hom)
  set r₀ : T₀ ⟶ V₀ := Over.homMk snd'.left rfl
  set p₀ : T₀ ⟶ U₀ := Over.homMk φ'.left (congrArg Over.Hom.left hbase)
  set ιT := relocalizeBaseHom B V S hV hS g hτ
  have h1 : ιT ≫ (Over.map g).map p₀ = φ' := Over.OverMorphism.ext (Category.id_comp _)
  have h2 : ιT ≫ (Over.map g).map r₀ = snd' := Over.OverMorphism.ext (Category.id_comp _)
  have hpullS : IsPullback (uliftYoneda.{u + 1}.map ((Over.map g).map p₀))
      (uliftYoneda.{u + 1}.map ((Over.map g).map r₀))
      (smallerBaseChart B V S hV hS g a) (smallerBaseChart B V S hV hS g e₀) := by
    refine hsq.of_iso (uliftYoneda.{u + 1}.mapIso (asIso ιT)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp) <;>
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, asIso_hom,
        ← Functor.map_comp, h1, h2]
  exact ⟨T₀, uliftYoneda.{u + 1}.map p₀, r₀,
    isPullback_of_isPullback_smallerBaseChart B V S hV hS g hpullS, hQ'⟩

/-- A property of a chart, tested on representable base changes, holds for the attached chart over
`S` when it holds over `V`. -/
theorem relative_smallerBaseChart_of_relative (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} {U₀ : BigFppfOver B V hV}
    (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G)
    (ha : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
      uliftYoneda.{u + 1} a) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
      (smallerBaseChart B V S hV hS g a) := by
  refine MorphismProperty.relative.of_exists (F := uliftYoneda.{u + 1}) fun V' e' ↦ ?_
  obtain ⟨ψ, hψ, e₀, he⟩ := exists_smallerBaseChart B V S hV hS g V' e'
  have hQr₀ := ha.2 e₀ (ha.1.fst e₀) (ha.1.snd e₀) (ha.1.isPullback e₀)
  set T₀ := ha.1.pullback e₀
  set r₀ := ha.1.snd e₀
  set p₀ : T₀ ⟶ U₀ := uliftYoneda.{u + 1}.preimage (ha.1.fst e₀)
  have hp₀ : uliftYoneda.{u + 1}.map p₀ = ha.1.fst e₀ := uliftYoneda.{u + 1}.map_preimage _
  have hpullW : IsPullback (uliftYoneda.{u + 1}.map p₀) (uliftYoneda.{u + 1}.map r₀) a e₀ := by
    rw [hp₀]
    exact ha.1.isPullback e₀
  set ι := relocalizeBaseHom B V S hV hS g hψ
  refine ⟨(Over.map g).obj T₀, uliftYoneda.{u + 1}.map ((Over.map g).map p₀),
    (Over.map g).map r₀ ≫ inv ι,
    (isPullback_smallerBaseChart B V S hV hS g hpullW).of_iso (Iso.refl _) (Iso.refl _)
      (uliftYoneda.{u + 1}.mapIso (asIso ι)).symm (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [he]), ?_⟩
  exact MorphismProperty.RespectsIso.postcomp Q
    ((BigFppfOver.toScheme B S hS).map (inv ι))
    ((BigFppfOver.toScheme B S hS).map ((Over.map g).map r₀)) hQr₀

/-- **A property of a chart, tested on representable base changes, does not see the change of
base.** This is the large-valued form of `AlgebraicGeometry.presheaf_relocalizeChart_iff`, with
the same proof. -/
theorem relative_smallerBaseChart_iff (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} {U₀ : BigFppfOver B V hV}
    (a : uliftYoneda.{u + 1}.obj U₀ ⟶ G) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (smallerBaseChart B V S hV hS g a) ↔
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
        uliftYoneda.{u + 1} a :=
  ⟨relative_of_relative_smallerBaseChart B V S hV hS g Q a,
    relative_smallerBaseChart_of_relative B V S hV hS g Q a⟩

/-- A relative property of morphisms out of universe-lifted representable presheaves is unchanged
by precomposition with the universe lift of an isomorphism of the site. -/
theorem relative_uliftYoneda_map_iso_comp_iff (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q] {U U' : BigFppfOver B S hS} (ι : U ⟶ U') [IsIso ι]
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : uliftYoneda.{u + 1}.obj U' ⟶ G) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (uliftYoneda.{u + 1}.map ι ≫ a) ↔
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative
        uliftYoneda.{u + 1} a := by
  have _ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.cancel_left_of_respectsIso _ _ _

/-! ### Conditions on morphisms -/

/-- A relative property of an attached chart, precomposed with the comparison of its source, is
equivalent to the same property over `V` of the original chart. -/
private theorem relative_relocalizeBaseHom_comp_smallerBaseChart_iff
    (Q : MorphismProperty Scheme.{u}) [MorphismProperty.RespectsIso Q]
    {G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} {U : BigFppfOver B S hS} {ψ : U.left ⟶ B.obj hV}
    (hψ : ψ ≫ g = U.hom) (a : uliftYoneda.{u + 1}.obj (Over.mk ψ : BigFppfOver B V hV) ⟶ G) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (uliftYoneda.{u + 1}.map (relocalizeBaseHom B V S hV hS g hψ) ≫
          smallerBaseChart B V S hV hS g a) ↔
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B V hV)).relative
        uliftYoneda.{u + 1} a :=
  (relative_uliftYoneda_map_iso_comp_iff B S hS Q _ _).trans
    (relative_smallerBaseChart_iff B V S hV hS g Q a)

/-- **Étaleness does not see the change of base.** A morphism of presheaves with values in
`Type (u + 1)` on the big fppf site of `V` is étale exactly when the induced morphism of attached
presheaves is étale over `S`. -/
theorem isEtaleULift_smallerBaseULiftMap_iff {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (k : G ⟶ G') :
    Space.IsEtaleULift.{u + 1} B S hS (smallerBaseULiftMap B V S hV hS g k) ↔
      Space.IsEtaleULift.{u + 1} B V hV k := by
  refine ⟨fun h U₀ φ hφ ↦ ?_, fun h U φ hφ ↦ ?_⟩
  · have h' := h _ (smallerBaseChart B V S hV hS g φ)
      ((relative_smallerBaseChart_iff B V S hV hS g _ φ).mpr hφ)
    rw [smallerBaseChart_comp] at h'
    exact (relative_smallerBaseChart_iff B V S hV hS g _ _).mp h'
  · obtain ⟨ψ, hψ, φ₀, rfl⟩ := exists_smallerBaseChart B V S hV hS g U φ
    rw [Category.assoc, smallerBaseChart_comp,
      relative_relocalizeBaseHom_comp_smallerBaseChart_iff B V S hV hS g (@Etale.{u}) hψ]
    exact h _ φ₀
      ((relative_relocalizeBaseHom_comp_smallerBaseChart_iff B V S hV hS g _ hψ _).mp hφ)

/-- The every-étale-chart condition over `V` passes to the induced morphism of attached
presheaves over `S`. -/
theorem holdsOnEveryEtaleChartULift_smallerBaseULiftMap (P : MorphismProperty Scheme.{u})
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (k : G ⟶ G')
    (hsmall : Space.HoldsOnEveryEtaleChartULift.{u + 1} B V hV P k) :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P (smallerBaseULiftMap B V S hV hS g k) := by
  intro U' V' a' b' m' ha' hb' hsq'
  obtain ⟨ψU, hψU, a, hae⟩ := exists_smallerBaseChart B V S hV hS g U' a'
  obtain ⟨ψV, hψV, b, hbe⟩ := exists_smallerBaseChart B V S hV hS g V' b'
  set ιU := relocalizeBaseHom B V S hV hS g hψU
  set ιV := relocalizeBaseHom B V S hV hS g hψV
  set n : (Over.map g).obj (Over.mk ψU) ⟶ (Over.map g).obj (Over.mk ψV) :=
    inv ιU ≫ m' ≫ ιV with hndef
  have hnleft : n.left = m'.left := by
    rw [hndef, Over.comp_left, Over.comp_left, inv_relocalizeBaseHom_left,
      relocalizeBaseHom_left]
    simp
  have hnsq : uliftYoneda.{u + 1}.map n ≫ smallerBaseChart B V S hV hS g b =
      smallerBaseChart B V S hV hS g a ≫ smallerBaseULiftMap B V S hV hS g k := by
    rw [hndef, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      show uliftYoneda.{u + 1}.map ιV ≫ smallerBaseChart B V S hV hS g b = b' from hbe.symm,
      hsq', hae, Category.assoc, ← Category.assoc (uliftYoneda.{u + 1}.map (inv ιU)),
      ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hfac : n ≫ relocalizeOverHom B V S hV hS g (Over.mk ψV)
      = relocalizeOverHom B V S hV hS g (Over.mk ψU) := by
    apply uliftYoneda.{u + 1}.map_injective
    rw [Functor.map_comp, ← smallerBaseChart_comp_hom B V S hV hS g b,
      ← Category.assoc, hnsq, Category.assoc, smallerBaseULiftMap_comp_hom,
      smallerBaseChart_comp_hom]
  set m₀ : (Over.mk ψU : BigFppfOver B V hV) ⟶ Over.mk ψV :=
    Over.homMk n.left (congrArg Over.Hom.left hfac)
  have hmap : (Over.map g).map m₀ = n := Over.OverMorphism.ext rfl
  have hsq₀ : uliftYoneda.{u + 1}.map m₀ ≫ b = a ≫ k := by
    apply smallerBaseULiftMap_injective B V S hV hS g
    have h1 : smallerBaseChart B V S hV hS g (uliftYoneda.{u + 1}.map m₀ ≫ b) =
        smallerBaseChart B V S hV hS g (a ≫ k) := by
      rw [← smallerBaseChart_naturality, ← smallerBaseChart_comp, hmap, hnsq]
    simp only [smallerBaseChart] at h1
    rw [← smallerBaseULiftMap_comp, ← smallerBaseULiftMap_comp] at h1 ⊢
    exact (Iso.cancel_iso_inv_left _ _ _).1 h1
  have hconc := hsmall (Over.mk ψU) (Over.mk ψV) a b m₀
    ((relative_relocalizeBaseHom_comp_smallerBaseChart_iff B V S hV hS g _ hψU a).1 (hae ▸ ha'))
    ((relative_relocalizeBaseHom_comp_smallerBaseChart_iff B V S hV hS g _ hψV b).1 (hbe ▸ hb'))
    hsq₀
  rwa [show (BigFppfOver.toScheme B V hV).map m₀ = (BigFppfOver.toScheme B S hS).map m' from
    congrArg B.inclusion.map hnleft] at hconc

/-- **The every-étale-chart condition does not see the change of base.** This is the
large-valued form of `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`, with the
same proof. -/
theorem holdsOnEveryEtaleChartULift_smallerBaseULiftMap_iff (P : MorphismProperty Scheme.{u})
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (k : G ⟶ G') :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P (smallerBaseULiftMap B V S hV hS g k) ↔
      Space.HoldsOnEveryEtaleChartULift.{u + 1} B V hV P k := by
  refine ⟨fun hbig U₀ V₀ a b m ha hb hsq ↦ ?_,
    holdsOnEveryEtaleChartULift_smallerBaseULiftMap B V S hV hS g P k⟩
  refine hbig ((Over.map g).obj U₀) ((Over.map g).obj V₀)
    (smallerBaseChart B V S hV hS g a) (smallerBaseChart B V S hV hS g b)
    ((Over.map g).map m)
    ((relative_smallerBaseChart_iff B V S hV hS g _ a).2 ha)
    ((relative_smallerBaseChart_iff B V S hV hS g _ b).2 hb) ?_
  rw [smallerBaseChart_naturality, smallerBaseChart_comp, hsq]

/-- Local finite type does not see the change of base. -/
theorem isLocallyOfFiniteTypeULift_smallerBaseULiftMap_iff
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (k : G ⟶ G') :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (smallerBaseULiftMap B V S hV hS g k) ↔
      Space.IsLocallyOfFiniteTypeULift.{u + 1} B V hV k :=
  holdsOnEveryEtaleChartULift_smallerBaseULiftMap_iff B V S hV hS g _ k

/-! ### Representable morphisms -/

/-- The attached presheaf of a base change along a chart is a base change along the attached
chart. -/
theorem isPullback_smallerBaseChart_pullback {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (f : G ⟶ G') {U₀ : BigFppfOver B V hV} (ξ₀ : uliftYoneda.{u + 1}.obj U₀ ⟶ G') :
    IsPullback (smallerBaseULiftMap B V S hV hS g (pullback.fst ξ₀ f) ≫
        (smallerBaseULiftYonedaIso B V S hV hS g U₀).hom)
      (smallerBaseULiftMap B V S hV hS g (pullback.snd ξ₀ f))
      (smallerBaseChart B V S hV hS g ξ₀) (smallerBaseULiftMap B V S hV hS g f) :=
  (isPullback_smallerBaseULiftMap B V S hV hS g (IsPullback.of_hasPullback ξ₀ f)).of_iso
    (Iso.refl _) (smallerBaseULiftYonedaIso B V S hV hS g U₀) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp [smallerBaseChart]) (by simp)

/-- The attached presheaf of a base change along a chart is a base change along a chart of the
attached presheaf, written as in `AlgebraicGeometry.FormalSpace.exists_smallerBaseChart`. -/
theorem isPullback_smallerBaseChart_pullback_relocalize
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)}
    (f : G ⟶ G') {U : BigFppfOver B S hS} {ψ : U.left ⟶ B.obj hV} (hψ : ψ ≫ g = U.hom)
    (ξ₀ : uliftYoneda.{u + 1}.obj (Over.mk ψ : BigFppfOver B V hV) ⟶ G') :
    IsPullback (smallerBaseULiftMap B V S hV hS g (pullback.fst ξ₀ f) ≫
        (smallerBaseULiftYonedaIso B V S hV hS g (Over.mk ψ)).hom ≫
          uliftYoneda.{u + 1}.map (inv (relocalizeBaseHom B V S hV hS g hψ)))
      (smallerBaseULiftMap B V S hV hS g (pullback.snd ξ₀ f))
      (uliftYoneda.{u + 1}.map (relocalizeBaseHom B V S hV hS g hψ) ≫
        smallerBaseChart B V S hV hS g ξ₀) (smallerBaseULiftMap B V S hV hS g f) :=
  (isPullback_smallerBaseChart_pullback B V S hV hS g f ξ₀).of_iso
    (Iso.refl _) (uliftYoneda.{u + 1}.mapIso (asIso (relocalizeBaseHom B V S hV hS g hψ))).symm
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **Representability by algebraic spaces does not see the change of base.** -/
theorem isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G') :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (smallerBaseULiftMap B V S hV hS g f) ↔
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV f := by
  refine ⟨fun h U₀ ξ₀ ↦ ?_, fun h U ξ ↦ ?_⟩
  · refine (isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g _).mp ?_
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      (isPullback_smallerBaseChart_pullback B V S hV hS g f ξ₀).isoPullback.symm (h _ _)
  · obtain ⟨ψ, hψ, ξ₀, rfl⟩ := exists_smallerBaseChart B V S hV hS g U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      (isPullback_smallerBaseChart_pullback_relocalize B V S hV hS g f hψ ξ₀).isoPullback
      ((isAlgebraicSpaceULift_smallerBaseULift_iff B V S hV hS g _).mpr (h _ ξ₀))

/-- Étaleness of a morphism of presheaves with values in `Type (u + 1)` is unchanged by
precomposition with an isomorphism. -/
theorem isEtaleULift_iso_comp_iff {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (e : F ≅ F') (f : F' ⟶ G) :
    Space.IsEtaleULift.{u + 1} B S hS (e.hom ≫ f) ↔ Space.IsEtaleULift.{u + 1} B S hS f := by
  refine ⟨fun h => ?_, isEtaleULift_precomp_iso B S hS e f⟩
  simpa using isEtaleULift_precomp_iso B S hS e.symm _ h

/-- The two projections of base changes of the same morphism along the same map are étale
together. -/
theorem isEtaleULift_fst_iff_of_isPullback {P P' X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {p : P ⟶ X} {q : P ⟶ Y} {p' : P' ⟶ X} {q' : P' ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback p q a b) (h' : IsPullback p' q' a b) :
    Space.IsEtaleULift.{u + 1} B S hS p ↔ Space.IsEtaleULift.{u + 1} B S hS p' := by
  rw [← isEtaleULift_iso_comp_iff B S hS (h'.isoIsPullback _ _ h) p,
    IsPullback.isoIsPullback_hom_fst]

/-- **Representable étale morphisms do not see the change of base.** A morphism of presheaves
with values in `Type (u + 1)` on the big fppf site of `V` is representable by algebraic spaces
and étale, in the sense of Stacks 0AIM, exactly when the induced morphism of attached presheaves
is. -/
theorem representableEtale_smallerBaseULiftMap_iff
    {G G' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)} (f : G ⟶ G') :
    (∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (smallerBaseULiftMap B V S hV hS g f),
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom)
        (smallerBaseULiftMap B V S hV hS g f) hf) ↔
      ∃ hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V hV f,
        Space.HasPropertyULift.{u + 1} B V hV
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B V hV k.hom) f hf := by
  constructor
  · rintro ⟨hf, he⟩
    refine ⟨(isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g f).mp hf,
      fun U₀ ξ₀ ↦ ?_⟩
    have h1 : Space.IsEtaleULift.{u + 1} B S hS
        (pullback.fst (smallerBaseChart B V S hV hS g ξ₀) (smallerBaseULiftMap B V S hV hS g f)) :=
      he _ _
    rwa [isEtaleULift_fst_iff_of_isPullback B S hS (IsPullback.of_hasPullback _ _)
      (isPullback_smallerBaseChart_pullback B V S hV hS g f ξ₀),
      Space.isEtaleULift_comp_isIso_iff, isEtaleULift_smallerBaseULiftMap_iff] at h1
  · rintro ⟨hf, he⟩
    refine ⟨(isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V S hV hS g f).mpr hf,
      fun U ξ ↦ ?_⟩
    obtain ⟨ψ, hψ, ξ₀, rfl⟩ := exists_smallerBaseChart B V S hV hS g U ξ
    change Space.IsEtaleULift.{u + 1} B S hS (pullback.fst _ _)
    rw [isEtaleULift_fst_iff_of_isPullback B S hS (IsPullback.of_hasPullback _ _)
      (isPullback_smallerBaseChart_pullback_relocalize B V S hV hS g f hψ ξ₀), ← Category.assoc,
      Space.isEtaleULift_comp_isIso_iff, Space.isEtaleULift_comp_isIso_iff,
      isEtaleULift_smallerBaseULiftMap_iff]
    exact he _ _

end AlgebraicGeometry.FormalSpace

end
