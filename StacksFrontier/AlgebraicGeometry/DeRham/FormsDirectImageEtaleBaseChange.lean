module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules

/-!
# The direct image of differential forms under étale base change

Let `g : Y ⟶ X` be a morphism of schemes over `π : X ⟶ S`, and let

```
Y₁ --ε'--> Y
|g₁        |g
X₁ --ε---> X
```

be a cartesian square with `ε` étale. The canonical map
`Ω^d_{X/S} ⟶ g_*Ω^d_{Y/S}` (`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`) and the
canonical map `Ω^d_{X₁/S} ⟶ g₁_*Ω^d_{Y₁/S}` of the base change are related by the base change
isomorphisms: the inverse image along `ε` of the first is the second, read through

* `ε^*Ω^d_{X/S} ≅ Ω^d_{X₁/S}`, the canonical map of [Stacks, Tag 0FLV], and
* `ε^*g_*Ω^d_{Y/S} ≅ g₁_*(ε')^*Ω^d_{Y/S} ≅ g₁_*Ω^d_{Y₁/S}`, flat base change in degree zero
  ([Stacks, Tag 02KH]) followed by `g₁_*` of the canonical map of [Stacks, Tag 0FLV] for `ε'`.

The second needs `g` quasi-compact and quasi-separated. The base may change too, along an étale
`e : S₁ ⟶ S` under the structure morphisms, the forms upstairs being taken relative to `S₁`. So
invertibility of the comparison map passes from `g` to `g₁`, and is detected on `g₁` after
pulling back along `ε`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pullback_map_formsDirectImageComparison_comp`: the square above,
  as an equation of morphisms, for an arbitrary commutative square.
* `AlgebraicGeometry.Scheme.Hom.isIso_formsDirectImageComparison_of_isPullback`: invertibility
  of the comparison map passes to an étale base change.
* `AlgebraicGeometry.Scheme.Hom.isIso_pullback_map_formsDirectImageComparison_of_isPullback`: the
  inverse image along `ε` of the comparison map is invertible as soon as the comparison map of
  the base change is.

## References

* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map on relative differential forms along a morphism which is equal to another
one is the canonical map of the other, read through the identification of the two inverse image
functors. -/
theorem relativeDifferentialFormsMap_congr {X' X S' S : Scheme.{u}} {f f' : X' ⟶ X} (h : f = f')
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    (hcomm' : f' ≫ p = p' ≫ g) (n : ℤ) :
    relativeDifferentialFormsMap f p p' g hcomm n =
      (Scheme.Modules.pullbackCongr h).hom.app (relativeDifferentialForms p n) ≫
        relativeDifferentialFormsMap f' p p' g hcomm' n := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

variable {X Y X₁ Y₁ S S₁ : Scheme.{u}} {g : Y ⟶ X} {g₁ : Y₁ ⟶ X₁} {ε : X₁ ⟶ X} {ε' : Y₁ ⟶ Y}

/-- The two canonical maps `g₁^*ε^*Ω^d_{X/S} ⟶ Ω^d_{Y₁/S₁}` of a commutative cube agree: the
identification `g₁^*ε^* ≅ ε'^*g^*` followed by the canonical maps for `g` and then `ε'` is the
canonical map for `ε` followed by the one for `g₁`. Both are the canonical map of the diagonal of
the square. -/
theorem pullbackSquareIso_hom_app_comp_relativeDifferentialFormsMap (H : ε' ≫ g = g₁ ≫ ε)
    (π : X ⟶ S) (π₁ : X₁ ⟶ S₁) (e : S₁ ⟶ S) (he : ε ≫ π = π₁ ≫ e) (d : ℤ) :
    (Stacks.Modules.pullbackSquareIso g g₁ ε ε' H).hom.app (relativeDifferentialForms π d) ≫
        (Scheme.Modules.pullback ε').map
          (relativeDifferentialFormsMap g π (g ≫ π) (𝟙 S) (by simp) d) ≫
        relativeDifferentialFormsMap ε' (g ≫ π) (g₁ ≫ π₁) e
          (by rw [← Category.assoc, H, Category.assoc, he, Category.assoc]) d =
      (Scheme.Modules.pullback g₁).map (relativeDifferentialFormsMap ε π π₁ e he d) ≫
        relativeDifferentialFormsMap g₁ π₁ (g₁ ≫ π₁) (𝟙 S₁) (by simp) d := by
  have h₁ := relativeDifferentialFormsMap_comp g ε' π (g ≫ π) (g₁ ≫ π₁) (𝟙 S) e e
    (by simp) (by rw [← Category.assoc, H, Category.assoc, he, Category.assoc])
    (by rw [H, Category.assoc, he, Category.assoc]) d
  have h₂ := relativeDifferentialFormsMap_comp ε g₁ π π₁ (g₁ ≫ π₁) e (𝟙 S₁) e
    he (by simp) (by rw [Category.assoc, he, Category.assoc]) d
  have h₃ := relativeDifferentialFormsMap_congr H.symm π (g₁ ≫ π₁) e
    (by rw [Category.assoc, he, Category.assoc]) (by rw [H, Category.assoc, he, Category.assoc]) d
  rw [← cancel_epi ((Scheme.Modules.pullbackComp g₁ ε).inv.app (relativeDifferentialForms π d)),
    ← h₂, h₃, h₁]
  simp [Stacks.Modules.pullbackSquareIso, Scheme.Modules.pullbackCongr]

/-- **The comparison map on direct images of forms commutes with base change**, as an equation of
morphisms `ε^*Ω^d_{X/S} ⟶ g₁_*Ω^d_{Y₁/S₁}`, for a commutative square `ε' ≫ g = g₁ ≫ ε` over a
commutative square `ε ≫ π = π₁ ≫ e` of structure morphisms: the inverse image along `ε` of the
comparison map for `g`, followed by the degree-zero base change map and by `g₁_*` of the
canonical map of `ε'`, is the canonical map of `ε` followed by the comparison map for `g₁`. -/
theorem pullback_map_formsDirectImageComparison_comp (H : ε' ≫ g = g₁ ≫ ε) (π : X ⟶ S)
    (π₁ : X₁ ⟶ S₁) (e : S₁ ⟶ S) (he : ε ≫ π = π₁ ≫ e) (d : ℤ) :
    (Scheme.Modules.pullback ε).map (formsDirectImageComparison g π d) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H).app
          (relativeDifferentialForms (g ≫ π) d) ≫
        (Scheme.Modules.pushforward g₁).map
          (relativeDifferentialFormsMap ε' (g ≫ π) (g₁ ≫ π₁) e
            (by rw [← Category.assoc, H, Category.assoc, he, Category.assoc]) d) =
      relativeDifferentialFormsMap ε π π₁ e he d ≫ formsDirectImageComparison g₁ π₁ d := by
  have hnat := (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H).naturality
    (relativeDifferentialFormsMap g π (g ≫ π) (𝟙 S) (by simp) d)
  have hunit := Stacks.Modules.map_unit_comp_baseChangeNatTrans_app H
    (relativeDifferentialForms π d)
  have hunit₁ := (Scheme.Modules.pullbackPushforwardAdjunction g₁).unit.naturality
    (relativeDifferentialFormsMap ε π π₁ e he d)
  simp only [Functor.comp_map, Functor.id_map] at hnat hunit₁
  simp only [formsDirectImageComparison, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hunit, reassoc_of% hunit₁, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp,
    pullbackSquareIso_hom_app_comp_relativeDifferentialFormsMap H π π₁ e he d]

variable (H : IsPullback ε' g₁ g ε) [Etale ε] [QuasiCompact g] [QuasiSeparated g] (π : X ⟶ S)
  (π₁ : X₁ ⟶ S₁) (e : S₁ ⟶ S) [Etale e] (he : ε ≫ π = π₁ ≫ e) (d : ℕ)

/-- **The comparison square of `pullback_map_formsDirectImageComparison_comp` has invertible
vertical sides** in a cartesian square with `ε` étale and `g` quasi-compact and quasi-separated,
over an étale `e`: the canonical map of `ε` by [Stacks, Tag 0FLV], the base change map by flat
base change in degree zero, and `g₁_*` of the canonical map of `ε'` by [Stacks, Tag 0FLV] again,
`ε'` being étale as a base change of `ε`. -/
theorem isIso_baseChange_comp_pushforward_map_relativeDifferentialFormsMap :
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
          (relativeDifferentialForms (g ≫ π) (d : ℤ)) ≫
        (Scheme.Modules.pushforward g₁).map
          (relativeDifferentialFormsMap ε' (g ≫ π) (g₁ ≫ π₁) e
            (by rw [← Category.assoc, H.w, Category.assoc, he, Category.assoc]) (d : ℤ))) := by
  have : Etale ε' := MorphismProperty.of_isPullback H.flip inferInstance
  have := isQuasicoherent_relativeDifferentialForms (g ≫ π) d
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H
    (relativeDifferentialForms (g ≫ π) (d : ℤ))
  have := isIso_relativeDifferentialFormsMap_of_etale ε' (g ≫ π) (g₁ ≫ π₁) e
    (by rw [← Category.assoc, H.w, Category.assoc, he, Category.assoc]) (d : ℤ)
  infer_instance

include H e he in
/-- **Invertibility of the comparison map on direct images of forms passes to an étale base
change**: in a cartesian square with `ε` étale and `g` quasi-compact and quasi-separated, over an
étale morphism of bases `e`, if `Ω^d_{X/S} ⟶ g_*Ω^d_{Y/S}` is an isomorphism then so is
`Ω^d_{X₁/S₁} ⟶ g₁_*Ω^d_{Y₁/S₁}`. -/
theorem isIso_formsDirectImageComparison_of_isPullback
    [IsIso (formsDirectImageComparison g π (d : ℤ))] :
    IsIso (formsDirectImageComparison g₁ π₁ (d : ℤ)) := by
  have hα := isIso_relativeDifferentialFormsMap_of_etale ε π π₁ e he (d : ℤ)
  have hβ := isIso_baseChange_comp_pushforward_map_relativeDifferentialFormsMap H π π₁ e he d
  have hsq := pullback_map_formsDirectImageComparison_comp H.w π π₁ e he (d : ℤ)
  have : IsIso (relativeDifferentialFormsMap ε π π₁ e he (d : ℤ) ≫
      formsDirectImageComparison g₁ π₁ (d : ℤ)) := by
    rw [← hsq]
    infer_instance
  exact IsIso.of_isIso_comp_left (relativeDifferentialFormsMap ε π π₁ e he (d : ℤ)) _

include H e he in
/-- **The comparison map on direct images of forms is detected after an étale base change**: in a
cartesian square with `ε` étale and `g` quasi-compact and quasi-separated, over an étale morphism
of bases `e`, if `Ω^d_{X₁/S₁} ⟶ g₁_*Ω^d_{Y₁/S₁}` is an isomorphism then so is the inverse image
along `ε` of `Ω^d_{X/S} ⟶ g_*Ω^d_{Y/S}`. -/
theorem isIso_pullback_map_formsDirectImageComparison_of_isPullback
    [IsIso (formsDirectImageComparison g₁ π₁ (d : ℤ))] :
    IsIso ((Scheme.Modules.pullback ε).map (formsDirectImageComparison g π (d : ℤ))) := by
  have hα := isIso_relativeDifferentialFormsMap_of_etale ε π π₁ e he (d : ℤ)
  have hβ := isIso_baseChange_comp_pushforward_map_relativeDifferentialFormsMap H π π₁ e he d
  have hsq := pullback_map_formsDirectImageComparison_comp H.w π π₁ e he (d : ℤ)
  have : IsIso ((Scheme.Modules.pullback ε).map (formsDirectImageComparison g π (d : ℤ)) ≫
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans H.w).app
          (relativeDifferentialForms (g ≫ π) (d : ℤ)) ≫
        (Scheme.Modules.pushforward g₁).map
          (relativeDifferentialFormsMap ε' (g ≫ π) (g₁ ≫ π₁) e
            (by rw [← Category.assoc, H.w, Category.assoc, he, Category.assoc]) (d : ℤ))) := by
    rw [hsq]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hβ this

end AlgebraicGeometry.Scheme.Hom

end
