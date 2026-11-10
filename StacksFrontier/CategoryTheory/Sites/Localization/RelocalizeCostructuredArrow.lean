module

public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# Scheme charts of a lower-shriek extension

Let `f : V ⟶ U` be a morphism of a category `C` and let `G` be a presheaf of sets on `C/V`, with
lower-shriek extension `Λ G = CategoryTheory.OverShriek.relocalizePresheafFunctor f G` on `C/U`.
A morphism `h_W ⟶ G` from a representable presheaf is a section of `G` over `W`, and a morphism
`h_{W'} ⟶ Λ G` is a factorization `ψ : W'.left ⟶ V` of `W'.hom` through `f` together with a
section of `G` over `(W'.left, ψ)`. So the two categories of representable charts are equivalent:
a chart `(W, x)` of `G` goes to the chart `(j W, (W.hom, x))` of `Λ G`, `j = Over.map f`, and a
chart `(W', (ψ, x))` of `Λ G` comes back as `((W'.left, ψ), x)`. Both functors leave the
underlying object of `C` unchanged.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeChart`: the functor on charts.
* `CategoryTheory.OverShriek.relocalizeChartInv`: the functor in the other direction.
* `CategoryTheory.OverShriek.relocalizeChartEquivalence`: the two form an equivalence.

## Main results

* `CategoryTheory.OverShriek.relocalizeChart_hom`: the chart `j W ⟶ Λ G` attached to a chart
  `x : h_W ⟶ G` is `Λ x` read through the tautological identification `h_{j W} ≅ Λ h_W`.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) (G : (Over V)ᵒᵖ ⥤ Type v)

/-- Two sections of the coproduct presheaf which are equal as pairs have components related by
restriction along a morphism of `C/V` with identity underlying morphism. -/
lemma map_eq_of_sigmaMk_eq {W : C} {ψ ψ' : W ⟶ V} {t : G.obj (op (Over.mk ψ))}
    {t' : G.obj (op (Over.mk ψ'))}
    (h : (⟨ψ, t⟩ : Σ χ : W ⟶ V, G.obj (op (Over.mk χ))) = ⟨ψ', t'⟩)
    (e : Over.mk ψ' ⟶ Over.mk ψ) (he : e.left = 𝟙 W) : G.map e.op t = t' := by
  obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : e = 𝟙 _ := Over.OverMorphism.ext he
  rw [op_id, G.map_id]
  exact eq_of_heq h'

/-- Restriction along an endomorphism of `C/V` whose underlying morphism is the identity is the
identity. -/
lemma map_eq_self {W : C} {ψ : W ⟶ V} (e : Over.mk ψ ⟶ Over.mk ψ) (he : e.left = 𝟙 W)
    (t : G.obj (op (Over.mk ψ))) : G.map e.op t = t := by
  obtain rfl : e = 𝟙 _ := Over.OverMorphism.ext he
  rw [op_id, G.map_id]
  rfl

/-- The section of `Λ G` over `j W` named by a chart `x : h_W ⟶ G`: the factorization is the
structure morphism of `W` and the section is the one `x` names. -/
def relocalizeChartSection (A : CostructuredArrow yoneda G) :
    ((relocalizePresheafFunctor f).obj G).obj (op ((Over.map f).obj A.left)) :=
  relocalizeMk f G (W := op ((Over.map f).obj A.left)) A.left.hom (yonedaEquiv A.hom) rfl

/-- The element named by a chart is the restriction of the one named by its target. -/
private theorem yonedaEquiv_hom_eq_map {F : (Over V)ᵒᵖ ⥤ Type v}
    {A B : CostructuredArrow yoneda F} (k : A ⟶ B) :
    yonedaEquiv A.hom = F.map k.left.op (yonedaEquiv B.hom) := by
  rw [yonedaEquiv_naturality, CostructuredArrow.w k]

/-- The chart of `Λ G` attached to a chart of `G`, on morphisms. -/
lemma relocalizeChart_w {A B : CostructuredArrow yoneda G} (k : A ⟶ B) :
    yoneda.map ((Over.map f).map k.left) ≫ yonedaEquiv.symm (relocalizeChartSection f G B) =
      yonedaEquiv.symm (relocalizeChartSection f G A) := by
  rw [yonedaEquiv_symm_naturality_left]
  congr 1
  refine Subtype.ext ?_
  have hA := yonedaEquiv_hom_eq_map k
  change (⟨k.left.left ≫ B.left.hom, G.map (Over.homMk k.left.left rfl :
      Over.mk (k.left.left ≫ B.left.hom) ⟶ Over.mk B.left.hom).op (yonedaEquiv B.hom)⟩ :
      Σ χ : A.left.left ⟶ V, G.obj (op (Over.mk χ))) = ⟨A.left.hom, yonedaEquiv A.hom⟩
  rw [hA]
  exact sigmaMk_eq G (yonedaEquiv B.hom) _ k.left rfl

/-- **The charts of `G` give charts of `Λ G`**: a chart `x : h_W ⟶ G` goes to the chart
`h_{j W} ⟶ Λ G` naming the section `(W.hom, x)`. -/
@[simps]
def relocalizeChart :
    CostructuredArrow yoneda G ⥤
      CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G) where
  obj A := CostructuredArrow.mk (yonedaEquiv.symm (relocalizeChartSection f G A))
  map {A B} k := CostructuredArrow.homMk ((Over.map f).map k.left) (relocalizeChart_w f G k)
  map_id _ := CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (by simp))
  map_comp _ _ := CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (by simp))

/-- The factorization through `f` carried by a chart of `Λ G`. -/
abbrev chartFactor (A : CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)) :
    A.left.left ⟶ V :=
  (yonedaEquiv A.hom).1.1

/-- The section of `G` carried by a chart of `Λ G`. -/
abbrev chartSection (A : CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)) :
    G.obj (op (Over.mk (chartFactor f G A))) :=
  (yonedaEquiv A.hom).1.2

/-- The section carried by the chart `k ≫ B` of `Λ G` is the restriction of the one carried by
`B`. -/
lemma yonedaEquiv_hom_of_hom {A B : CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)}
    (k : A ⟶ B) :
    yonedaEquiv A.hom =
      ((relocalizePresheafFunctor f).obj G).map k.left.op (yonedaEquiv B.hom) :=
  yonedaEquiv_hom_eq_map k

/-- A morphism of charts of `Λ G` is compatible with the two factorizations. -/
lemma chartFactor_comp {A B : CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)}
    (k : A ⟶ B) : k.left.left ≫ chartFactor f G B = chartFactor f G A :=
  (congrArg (fun x => x.1.1) (yonedaEquiv_hom_of_hom f G k)).symm

/-- A morphism of charts of `Λ G` is compatible with the two sections. -/
lemma chartSection_map {A B : CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)}
    (k : A ⟶ B) :
    G.map (Over.homMk k.left.left (chartFactor_comp f G k) :
        Over.mk (chartFactor f G A) ⟶ Over.mk (chartFactor f G B)).op (chartSection f G B) =
      chartSection f G A := by
  have h := congrArg Subtype.val (yonedaEquiv_hom_of_hom f G k)
  change (⟨chartFactor f G A, chartSection f G A⟩ :
      Σ χ : A.left.left ⟶ V, G.obj (op (Over.mk χ))) =
    ⟨k.left.left ≫ chartFactor f G B, G.map (Over.homMk k.left.left rfl :
      Over.mk (k.left.left ≫ chartFactor f G B) ⟶ Over.mk (chartFactor f G B)).op
        (chartSection f G B)⟩ at h
  have h' := map_eq_of_sigmaMk_eq G h.symm
    (Over.homMk (𝟙 _) (by simpa using chartFactor_comp f G k)) rfl
  rw [map_op_comp] at h'
  rw [← h']
  exact congrArg (fun e : Over.mk (chartFactor f G A) ⟶ Over.mk (chartFactor f G B) =>
    G.map e.op (chartSection f G B)) (Over.OverMorphism.ext (Category.id_comp _).symm)

/-- **The charts of `Λ G` give charts of `G`**: a chart naming the section `(ψ, x)` over `W'`
goes to the chart of `G` over `(W'.left, ψ)` naming `x`. -/
@[simps]
def relocalizeChartInv :
    CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G) ⥤
      CostructuredArrow yoneda G where
  obj A := CostructuredArrow.mk (yonedaEquiv.symm (chartSection f G A))
  map {A B} k := CostructuredArrow.homMk (Over.homMk k.left.left (chartFactor_comp f G k)) (by
    change yoneda.map _ ≫ yonedaEquiv.symm _ = yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left]
    exact congrArg yonedaEquiv.symm (chartSection_map f G k))
  map_id _ := CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (by simp))
  map_comp _ _ := CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (by simp))

/-- The unit of the chart equivalence: the identity of the underlying object. -/
def relocalizeChartUnitIso :
    𝟭 (CostructuredArrow yoneda G) ≅ relocalizeChart f G ⋙ relocalizeChartInv f G :=
  NatIso.ofComponents (fun A => CostructuredArrow.isoMk
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (𝟙 _ ≫ A.left.hom) = _
      simp)) (by
      refine yonedaEquiv.injective ?_
      exact (map_op_comp G _ _ _).trans
        (map_eq_self G _ ((Category.comp_id _).trans (Category.comp_id _)) _)))
    (by
      intro X Y k
      exact CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- The counit of the chart equivalence: the identity of the underlying object. -/
def relocalizeChartCounitIso :
    relocalizeChartInv f G ⋙ relocalizeChart f G ≅
      𝟭 (CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)) :=
  NatIso.ofComponents (fun A => CostructuredArrow.isoMk
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ A.left.hom = chartFactor f G A ≫ f
      rw [Category.id_comp]
      exact (yonedaEquiv A.hom).2.symm)) (by
      refine yonedaEquiv.injective ?_
      refine (yonedaEquiv_naturality _ _).symm.trans ?_
      have h1 : yonedaEquiv ((relocalizeChart f G).obj ((relocalizeChartInv f G).obj A)).hom =
          relocalizeChartSection f G ((relocalizeChartInv f G).obj A) :=
        Equiv.apply_symm_apply _ _
      have h2 : yonedaEquiv ((relocalizeChartInv f G).obj A).hom = chartSection f G A :=
        Equiv.apply_symm_apply _ _
      refine Eq.trans ?_ h1.symm
      refine Subtype.ext ?_
      refine (sigmaMk_eq_self G _ _ rfl).trans ?_
      change _ = (⟨chartFactor f G A, yonedaEquiv ((relocalizeChartInv f G).obj A).hom⟩ :
        Σ χ : A.left.left ⟶ V, G.obj (op (Over.mk χ)))
      exact congrArg (Sigma.mk _) h2.symm))
    (by
      intro X Y k
      exact CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **The charts of `G` and of its lower-shriek extension `Λ G` are equivalent categories.** -/
def relocalizeChartEquivalence :
    CostructuredArrow yoneda G ≌ CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj G)
    where
  functor := relocalizeChart f G
  inverse := relocalizeChartInv f G
  unitIso := relocalizeChartUnitIso f G
  counitIso := relocalizeChartCounitIso f G
  functor_unitIso_comp _ :=
    CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (Category.comp_id _))

/-- The chart `h_{j W} ⟶ Λ G` attached to a chart `x : h_W ⟶ G` is `Λ x`, read through the
tautological identification of `h_{j W}` with `Λ h_W`. -/
lemma relocalizeChart_hom (A : CostructuredArrow yoneda G) :
    yonedaEquiv.symm (relocalizeChartSection f G A) =
      relocalizeYonedaFactorHom f (W := (Over.map f).obj A.left) (ψ := A.left.hom) rfl ≫
        (relocalizePresheafFunctor f).map A.hom := by
  refine yonedaEquiv.injective ?_
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp]
  have h : yonedaEquiv (relocalizeYonedaFactorHom f (W := (Over.map f).obj A.left)
      (ψ := A.left.hom) rfl) = ⟨⟨A.left.hom, 𝟙 (Over.mk A.left.hom)⟩, rfl⟩ :=
    yonedaEquiv.apply_symm_apply _
  rw [h]
  rfl

end CategoryTheory.OverShriek

end
