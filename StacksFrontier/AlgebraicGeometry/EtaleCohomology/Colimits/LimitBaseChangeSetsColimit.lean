module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageSetsColimit

/-!
# Base change for sheaves of sets passes to the limit

Let `I` be a directed set and let

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

be an inverse system of cartesian squares of schemes with affine transition morphisms and with
`g_i` quasi-compact and quasi-separated, with limit square `(X, Y, S, T, f, h, e, g)` and
projections `r_i : X ⟶ X_i`, `s_i : S ⟶ S_i`, `p_i : T ⟶ T_i`, `q_i : Y ⟶ Y_i`. Let
`(ℱ_i, φ_{i'i})` be a system of sheaves of sets on `(T_i)` and `ℱ = colim p_i⁻¹ℱ_i`. Conclusion (1)
of [Stacks, Tag 0EZT] asserts: if the base change map `f_i⁻¹g_{i, *}ℱ_i ⟶ h_{i, *}e_i⁻¹ℱ_i` is an
isomorphism for every `i`, then so is `f⁻¹g_*ℱ ⟶ h_*e⁻¹ℱ`.

The source omits the proof; it is the one of conclusion (2) in degree zero. By the degree zero
case of [Stacks, Tag 0EYM] for sheaves of sets, `g_*ℱ = colim s_i⁻¹g_{i, *}ℱ_i`, and inverse image
along `f` preserves this colimit, being a left adjoint. The inverse images `e_i⁻¹ℱ_i` form a system
on `(Y_i)` whose colimit is `e⁻¹ℱ`, so `h_*e⁻¹ℱ = colim r_i⁻¹h_{i, *}e_i⁻¹ℱ_i`. The base change
maps of the levels, pulled back to `X` along `r_i`, are a map of the two systems compatible with
the base change map of the limit square, by the pasting of base change maps; a map of colimits
which is invertible on every level is invertible.

## Main definitions

* `Stacks.EtaleCohomology.LimitBaseChange.sheafStageComparison`: the base change map of the `i`-th
  square, pulled back to `X`, as a map `f⁻¹s_i⁻¹g_{i, *}ℱ_i ⟶ r_i⁻¹h_{i, *}e_i⁻¹ℱ_i`.

## Main results

* `Stacks.EtaleCohomology.LimitBaseChange.isIso_smallEtaleSheafBaseChange_of_isColimit`: for
  arbitrary coefficients, the base change map of the limit square is invertible as soon as it is at
  every level and the two colimit presentations hold.
* `Stacks.EtaleCohomology.LimitBaseChange.isIso_smallEtaleSheafBaseChange_limit`: conclusion (1)
  of [Stacks, Tag 0EZT].

## Implementation notes

The base change map is `Stacks.EtaleCohomology.smallEtaleSheafBaseChange` at the coefficients
`Type (u + 1)` of sheaves of sets on the small étale sites, the mate of the identification of the
two composite direct images under the inverse-image/direct-image adjunctions. The compatibilities
of the level comparisons with the legs and with the transition maps are first proved for
arbitrary morphisms of schemes subject to the equations of the projection and transition squares,
with the composites along which inverse images are compared given as variables with their
factorisations, and with arbitrary coefficients.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' u

namespace Stacks.EtaleCohomology.LimitBaseChange

open LimitHigherDirectImage LimitDirectImage

variable (A : Type w) [Category.{w'} A]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint]

local notation "App" => smallEtaleSheafPullbackCompApp

/-! ### The two compatibilities for arbitrary morphisms -/

section Generic

variable {X S T Y X₀ S₀ T₀ Y₀ : Scheme.{u}} (fL : X ⟶ S) (gL : T ⟶ S) (hL : Y ⟶ X) (eL : Y ⟶ T)
  (r : X ⟶ X₀) (s : S ⟶ S₀) (p : T ⟶ T₀) (t : Y ⟶ Y₀)
  (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀)
  (u : X ⟶ S₀) (v : Y ⟶ T₀) (hu₁ : u = fL ≫ s) (hu₂ : u = r ≫ f₀) (hv₁ : v = eL ≫ p)
  (hv₂ : v = t ≫ e₀) (hgL : gL ≫ s = p ≫ g₀) (hhL : hL ≫ r = t ≫ h₀)
  (w₀ : h₀ ≫ f₀ = e₀ ≫ g₀) (wL : hL ≫ fL = eL ≫ gL)
  (G : Sheaf (smallEtaleTopology T₀) A) {𝓕 : Sheaf (smallEtaleTopology T) A}
  (ι : (smallEtaleSheafPullback A p).obj G ⟶ 𝓕)

include hu₂ hv₂ hhL w₀ in
private theorem legs_rectangle_comm : hL ≫ u = v ≫ g₀ := by
  rw [hu₂, hv₂, ← Category.assoc, hhL, Category.assoc, w₀, Category.assoc]

/-- The compatibility of the base change maps of a level square and of the limit square with
the legs, for arbitrary morphisms subject to the equations of the projection squares. -/
theorem smallEtaleSheafBaseChange_legs :
    (smallEtaleSheafPullback A fL).map ((smallEtaleSheafBaseChange A s g₀ gL p hgL).app G ≫
        (smallEtalePushforward gL A).map ι) ≫
        (smallEtaleSheafBaseChange A fL gL hL eL wL).app 𝓕 =
      ((App A fL s u hu₁ ((smallEtalePushforward g₀ A).obj G)).hom ≫
        (App A r f₀ u hu₂ ((smallEtalePushforward g₀ A).obj G)).inv ≫
        (smallEtaleSheafPullback A r).map ((smallEtaleSheafBaseChange A f₀ g₀ h₀ e₀ w₀).app G)) ≫
      ((smallEtaleSheafBaseChange A r h₀ hL t hhL).app ((smallEtaleSheafPullback A e₀).obj G) ≫
        (smallEtalePushforward hL A).map ((App A t e₀ v hv₂ G).hom ≫
          (App A eL p v hv₁ G).inv ≫ (smallEtaleSheafPullback A eL).map ι)) := by
  have hrect := legs_rectangle_comm hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀
  have hP₁ := smallEtaleSheafBaseChange_paste_app_named A g₀ gL hL s fL p eL hgL wL u hu₁ v hv₁
    hrect G
  have hP₂ := smallEtaleSheafBaseChange_paste_app_named A g₀ h₀ hL f₀ r e₀ t w₀ hhL u hu₂ v hv₂
    hrect G
  have hcancel : (smallEtalePushforward hL A).map (App A eL p v hv₁ G).hom ≫
      (smallEtalePushforward hL A).map (App A eL p v hv₁ G).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [Functor.map_comp, Category.assoc, smallEtaleSheafBaseChange_naturality A fL gL hL eL wL ι]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hP₂, reassoc_of% hP₁, Iso.hom_inv_id_assoc, reassoc_of% hcancel]

end Generic

section GenericDiagram

variable {X S Xi Xj Si Sj Ti Tj Yi Yj : Scheme.{u}} (fL : X ⟶ S)
  (ri : X ⟶ Xi) (rj : X ⟶ Xj) (si : S ⟶ Si) (sj : S ⟶ Sj)
  (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj) (gi : Ti ⟶ Si) (gj : Tj ⟶ Sj) (hi : Yi ⟶ Xi) (hj : Yj ⟶ Xj)
  (ei : Yi ⟶ Ti) (ej : Yj ⟶ Tj)
  (xa : Xi ⟶ Xj) (sa : Si ⟶ Sj) (ta : Ti ⟶ Tj) (ya : Yi ⟶ Yj)
  (hrj : rj = ri ≫ xa) (hsj : sj = si ≫ sa)
  (hgt : gi ≫ sa = ta ≫ gj) (hht : hi ≫ xa = ya ≫ hj)
  (wi : hi ≫ fi = ei ≫ gi) (wj : hj ≫ fj = ej ≫ gj)
  (ui : X ⟶ Si) (uj : X ⟶ Sj) (hui₁ : ui = fL ≫ si) (hui₂ : ui = ri ≫ fi)
  (huj₁ : uj = fL ≫ sj) (huj₂ : uj = rj ≫ fj)
  (U : Xi ⟶ Sj) (hU₁ : U = xa ≫ fj) (hU₂ : U = fi ≫ sa)
  (V : Yi ⟶ Tj) (hV₁ : V = ya ≫ ej) (hV₂ : V = ei ≫ ta)
  (Gj : Sheaf (smallEtaleTopology Tj) A)
  (Gi : Sheaf (smallEtaleTopology Ti) A) (φ : (smallEtaleSheafPullback A ta).obj Gj ⟶ Gi)

include hU₁ hV₁ hht wj in
private theorem diagram_rectangle_comm : hi ≫ U = V ≫ gj :=
  legs_rectangle_comm hi xa ya fj gj hj ej U V hU₁ hV₁ hht wj

include hui₁ huj₁ hsj in
private theorem diagram_uj_eq₁ : uj = ui ≫ sa := by
  rw [huj₁, hsj, hui₁, Category.assoc]

include huj₂ hrj hU₁ in
private theorem diagram_uj_eq₂ : uj = ri ≫ U := by
  rw [huj₂, hrj, hU₁, Category.assoc]

/-- The coherence of the comparisons of inverse images in the naturality of the level
comparisons: both composites are the comparison `f⁻¹s_j⁻¹ ≅ (r_i ≫ U)⁻¹` along the two
factorisations of `X ⟶ S_j`. -/
private theorem diagram_coherence (M : Sheaf (smallEtaleTopology Sj) A) :
    (smallEtaleSheafPullback A fL).map (App A si sa sj hsj M).inv ≫
        (App A fL si ui hui₁ ((smallEtaleSheafPullback A sa).obj M)).hom ≫
        (App A ri fi ui hui₂ ((smallEtaleSheafPullback A sa).obj M)).inv ≫
        (smallEtaleSheafPullback A ri).map (App A fi sa U hU₂ M).hom =
      (App A fL sj uj huj₁ M).hom ≫ (App A rj fj uj huj₂ M).inv ≫
        (App A ri xa rj hrj ((smallEtaleSheafPullback A fj).obj M)).inv ≫
        (smallEtaleSheafPullback A ri).map (App A xa fj U hU₁ M).hom := by
  have h₁ := diagram_uj_eq₁ fL si sj sa hsj ui uj hui₁ huj₁
  have h₂ := diagram_uj_eq₂ ri rj fj xa hrj uj huj₂ U hU₁
  rw [← cancel_mono (App A ri U uj h₂ M).hom]
  simp only [Category.assoc]
  rw [← smallEtaleSheafPullbackCompApp_assoc A ri fi sa ui hui₂ U hU₂ uj h₁ h₂ M,
    Iso.inv_hom_id_assoc,
    smallEtaleSheafPullbackCompApp_assoc A fL si sa ui hui₁ sj hsj uj h₁ huj₁ M,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← smallEtaleSheafPullbackCompApp_assoc A ri xa fj rj hrj U hU₁ uj huj₂ h₂ M,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The first decomposition of the base change map of the rectangle `U = f_i ≫ s_{ji}`, under
inverse image along `r_i`. -/
private theorem diagram_pasteLeft :
    (smallEtaleSheafPullback A ri).map ((smallEtaleSheafPullback A fi).map
        ((smallEtaleSheafBaseChange A sa gj gi ta hgt).app Gj)) ≫
        (smallEtaleSheafPullback A ri).map ((smallEtaleSheafBaseChange A fi gi hi ei wi).app
          ((smallEtaleSheafPullback A ta).obj Gj)) =
      (smallEtaleSheafPullback A ri).map
          (App A fi sa U hU₂ ((smallEtalePushforward gj A).obj Gj)).hom ≫
        (smallEtaleSheafPullback A ri).map
          ((smallEtaleSheafBaseChange A U gj hi V
            (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁)).app Gj) ≫
        (smallEtaleSheafPullback A ri).map
          ((smallEtalePushforward hi A).map (App A ei ta V hV₂ Gj).inv) := by
  have key : (smallEtaleSheafPullback A fi).map
        ((smallEtaleSheafBaseChange A sa gj gi ta hgt).app Gj) ≫
        (smallEtaleSheafBaseChange A fi gi hi ei wi).app ((smallEtaleSheafPullback A ta).obj Gj) =
      (App A fi sa U hU₂ ((smallEtalePushforward gj A).obj Gj)).hom ≫
        (smallEtaleSheafBaseChange A U gj hi V
          (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁)).app Gj ≫
        (smallEtalePushforward hi A).map (App A ei ta V hV₂ Gj).inv := by
    rw [smallEtaleSheafBaseChange_paste_app_named A gj gi hi sa fi ta ei hgt wi U hU₂ V hV₂ _ Gj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    simp
  rw [← Functor.map_comp, key, Functor.map_comp, Functor.map_comp]

/-- The second decomposition of the base change map of the rectangle `U = f_{ji} ≫ f_j`, under
inverse image along `r_i`. -/
private theorem diagram_pasteRight :
    (smallEtaleSheafPullback A ri).map ((smallEtaleSheafPullback A xa).map
        ((smallEtaleSheafBaseChange A fj gj hj ej wj).app Gj)) ≫
        (smallEtaleSheafPullback A ri).map ((smallEtaleSheafBaseChange A xa hj hi ya hht).app
          ((smallEtaleSheafPullback A ej).obj Gj)) ≫
        (smallEtaleSheafPullback A ri).map
          ((smallEtalePushforward hi A).map (App A ya ej V hV₁ Gj).hom) =
      (smallEtaleSheafPullback A ri).map
          (App A xa fj U hU₁ ((smallEtalePushforward gj A).obj Gj)).hom ≫
        (smallEtaleSheafPullback A ri).map
          ((smallEtaleSheafBaseChange A U gj hi V
            (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁)).app Gj) := by
  have key : (smallEtaleSheafPullback A xa).map
        ((smallEtaleSheafBaseChange A fj gj hj ej wj).app Gj) ≫
        (smallEtaleSheafBaseChange A xa hj hi ya hht).app ((smallEtaleSheafPullback A ej).obj Gj) ≫
        (smallEtalePushforward hi A).map (App A ya ej V hV₁ Gj).hom =
      (App A xa fj U hU₁ ((smallEtalePushforward gj A).obj Gj)).hom ≫
        (smallEtaleSheafBaseChange A U gj hi V
          (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁)).app Gj := by
    rw [smallEtaleSheafBaseChange_paste_app_named A gj hj hi fj xa ej ya wj hht U hU₁ V hV₁ _ Gj,
      Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, key, Functor.map_comp]

/-- The naturality of the base change map of the `i`-th square at `φ`, under inverse image along
`r_i`. -/
private theorem diagram_naturality :
    (smallEtaleSheafPullback A ri).map
        ((smallEtaleSheafPullback A fi).map ((smallEtalePushforward gi A).map φ)) ≫
        (smallEtaleSheafPullback A ri).map ((smallEtaleSheafBaseChange A fi gi hi ei wi).app Gi) =
      (smallEtaleSheafPullback A ri).map ((smallEtaleSheafBaseChange A fi gi hi ei wi).app
          ((smallEtaleSheafPullback A ta).obj Gj)) ≫
        (smallEtaleSheafPullback A ri).map
          ((smallEtalePushforward hi A).map ((smallEtaleSheafPullback A ei).map φ)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, smallEtaleSheafBaseChange_naturality]

include U hU₁ hU₂ in
/-- **The naturality of the level comparisons**, for arbitrary morphisms subject to the
equations of the projection and transition squares. -/
theorem smallEtaleSheafBaseChange_diagram :
    (smallEtaleSheafPullback A fL).map
        ((App A si sa sj hsj ((smallEtalePushforward gj A).obj Gj)).inv ≫
          (smallEtaleSheafPullback A si).map
            ((smallEtaleSheafBaseChange A sa gj gi ta hgt).app Gj ≫
              (smallEtalePushforward gi A).map φ)) ≫
        ((App A fL si ui hui₁ ((smallEtalePushforward gi A).obj Gi)).hom ≫
          (App A ri fi ui hui₂ ((smallEtalePushforward gi A).obj Gi)).inv ≫
          (smallEtaleSheafPullback A ri).map
            ((smallEtaleSheafBaseChange A fi gi hi ei wi).app Gi)) =
      ((App A fL sj uj huj₁ ((smallEtalePushforward gj A).obj Gj)).hom ≫
          (App A rj fj uj huj₂ ((smallEtalePushforward gj A).obj Gj)).inv ≫
          (smallEtaleSheafPullback A rj).map
            ((smallEtaleSheafBaseChange A fj gj hj ej wj).app Gj)) ≫
        (App A ri xa rj hrj ((smallEtalePushforward hj A).obj
            ((smallEtaleSheafPullback A ej).obj Gj))).inv ≫
          (smallEtaleSheafPullback A ri).map
            ((smallEtaleSheafBaseChange A xa hj hi ya hht).app
                ((smallEtaleSheafPullback A ej).obj Gj) ≫
            (smallEtalePushforward hi A).map ((App A ya ej V hV₁ Gj).hom ≫
              (App A ei ta V hV₂ Gj).inv ≫ (smallEtaleSheafPullback A ei).map φ)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafPullbackCompApp_hom_naturality A fL si ui hui₁
      ((smallEtalePushforward gi A).map φ)),
    reassoc_of% (smallEtaleSheafPullbackCompApp_hom_naturality A fL si ui hui₁
      ((smallEtaleSheafBaseChange A sa gj gi ta hgt).app Gj)),
    reassoc_of% (smallEtaleSheafPullbackCompApp_inv_naturality A ri fi ui hui₂
      ((smallEtalePushforward gi A).map φ)),
    reassoc_of% (smallEtaleSheafPullbackCompApp_inv_naturality A ri fi ui hui₂
      ((smallEtaleSheafBaseChange A sa gj gi ta hgt).app Gj)),
    diagram_naturality A ri fi gi hi ei ta wi Gj Gi φ,
    reassoc_of% (diagram_pasteLeft A ri fi fj gi gj hi hj ei ej xa sa ta ya hgt hht wi wj U hU₁
      hU₂ V hV₁ hV₂ Gj),
    reassoc_of% (smallEtaleSheafPullbackCompApp_inv_naturality A ri xa rj hrj
      ((smallEtaleSheafBaseChange A fj gj hj ej wj).app Gj)),
    reassoc_of% (diagram_pasteRight A ri fj gj hi hj ej xa ya hht wj U hU₁ V hV₁ Gj),
    reassoc_of% (diagram_coherence A fL ri rj si sj fi fj xa sa hrj hsj ui uj hui₁ hui₂ huj₁ huj₂
      U hU₁ hU₂ ((smallEtalePushforward gj A).obj Gj))]

end GenericDiagram

/-! ### The comparison of the two systems -/

section Comparison

variable {I : Type u} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (fL : cX.pt ⟶ cS.pt) (eL : cY.pt ⟶ cT.pt)
  (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
  (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  (F : EtaleSheafSystem DT A)

/-- **The comparison of the two colimit diagrams at a level**: the base change map
`f_i⁻¹g_{i, *}ℱ_i ⟶ h_{i, *}e_i⁻¹ℱ_i` of the `i`-th square, pulled back to `X` along `r_i` and read
on the source through the comparison `f⁻¹s_i⁻¹ ≅ r_i⁻¹f_i⁻¹` of the two composite inverse images
along `f ≫ s_i = r_i ≫ f_i`. -/
def sheafStageComparison (i : Iᵒᵖ) :
    (smallEtaleSheafPullback A fL).obj ((smallEtaleSheafPullback A (X := cS.pt) (cS.π.app i)).obj
        ((smallEtalePushforward (g.app i) A).obj (F.obj i))) ⟶
      (smallEtaleSheafPullback A (X := cX.pt) (cX.π.app i)).obj
        ((smallEtalePushforward (h.app i) A).obj
          ((smallEtaleSheafPullback A (e.app i)).obj (F.obj i))) :=
  (App A fL (cS.π.app i) (cX.π.app i ≫ f.app i) (hfL i).symm
      ((smallEtalePushforward (g.app i) A).obj (F.obj i))).hom ≫
    (App A (X := cX.pt) (cX.π.app i) (f.app i) (cX.π.app i ≫ f.app i) rfl
      ((smallEtalePushforward (g.app i) A).obj (F.obj i))).inv ≫
    (smallEtaleSheafPullback A (X := cX.pt) (cX.π.app i)).map
      ((smallEtaleSheafBaseChange A (f.app i) (g.app i) (h.app i) (e.app i) (w i)).app (F.obj i))

/-- The level comparison is invertible as soon as the base change map of the `i`-th square is. -/
theorem isIso_sheafStageComparison (i : Iᵒᵖ)
    (hi : IsIso ((smallEtaleSheafBaseChange A (f.app i) (g.app i) (h.app i) (e.app i) (w i)).app
      (F.obj i))) :
    IsIso (sheafStageComparison A f g h e fL hfL w F i) := by
  unfold sheafStageComparison
  infer_instance

/-- **The level comparisons commute with the maps of the two diagrams**: the inverse image along
`f` of the map `s_{i'}⁻¹g_{i', *}ℱ_{i'} ⟶ s_i⁻¹g_{i, *}ℱ_i` followed by the comparison at `i` is
the comparison at `i'` followed by the map of the diagram `r_i⁻¹h_{i, *}e_i⁻¹ℱ_i`. -/
theorem map_sheafPullbackDiagramMap_comp_sheafStageComparison {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtaleSheafPullback A fL).map
        ((pushforwardSystem A g F).sheafPullbackDiagramMap cS (i := i) (j := j) a) ≫
        sheafStageComparison A f g h e fL hfL w F i =
      sheafStageComparison A f g h e fL hfL w F j ≫
        (pushforwardSystem A h (F.sheafPullback e)).sheafPullbackDiagramMap cX
          (i := i) (j := j) a := by
  have key := smallEtaleSheafBaseChange_diagram A fL (cX.π.app i) (cX.π.app j) (cS.π.app i)
    (cS.π.app j) (f.app i) (f.app j) (g.app i) (g.app j) (h.app i) (h.app j) (e.app i) (e.app j)
    (DX.map a) (DS.map a) (DT.map a) (DY.map a) (cX.w a).symm (cS.w a).symm (transition_comm g a)
    (transition_comm h a) (w i) (w j) (cX.π.app i ≫ f.app i) (cX.π.app j ≫ f.app j) (hfL i).symm
    rfl (hfL j).symm rfl (DX.map a ≫ f.app j) rfl (f.naturality a) (DY.map a ≫ e.app j) rfl
    (e.naturality a) (F.obj j) (F.obj i) (F.sheafMap a)
  rw [pushforwardSystem_sheafPullbackDiagramMap, pushforwardSystem_sheafPullbackDiagramMap]
  simp only [sheafStageComparison, EtaleSheafSystem.sheafMap, EtaleSheafSystem.sheafPullbackMap,
    Functor.map_comp, Category.assoc] at key ⊢
  exact key

variable (hcX : IsLimit cX) (hcS : IsLimit cS)
  (wL : limitMorphism h cY cX hcX ≫ fL = eL ≫ limitMorphism g cT cS hcS)
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) A}
  (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback A (X := cT.pt) (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)

/-- **The level comparisons are compatible with the base change map of the limit square.** The
inverse image along `f` of the leg `s_i⁻¹g_{i, *}ℱ_i ⟶ g_*ℱ`, followed by the base change map of
the limit square, is the level comparison followed by the leg `r_i⁻¹h_{i, *}e_i⁻¹ℱ_i ⟶ h_*e⁻¹ℱ`:
both are decompositions of the base change map of the rectangle with sides `r_i ≫ f_i` and
`q_i ≫ e_i`, by the pasting of base change maps. -/
theorem map_projectionMap_comp_smallEtaleSheafBaseChange (i : Iᵒᵖ) :
    (smallEtaleSheafPullback A fL).map (baseChangeProjectionMap A g cT hcS F ι i) ≫
        (smallEtaleSheafBaseChange A fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL
          wL).app 𝓕 =
      sheafStageComparison A f g h e fL hfL w F i ≫
        baseChangeProjectionMap A h cY hcX (F.sheafPullback e) (F.sheafPullbackLeg e eL heL ι) i :=
  smallEtaleSheafBaseChange_legs A fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL
    (cX.π.app i) (cS.π.app i) (cT.π.app i) (cY.π.app i) (f.app i) (g.app i) (h.app i) (e.app i)
    (cX.π.app i ≫ f.app i) (cY.π.app i ≫ e.app i) (hfL i).symm rfl (heL i).symm rfl
    (limitMorphism_comp_π g cT cS hcS i) (limitMorphism_comp_π h cY cX hcX i) (w i) wL
    (F.obj i) (ι i)

include hfL in
/-- **Base change passes to the limit, for any coefficients, given the two colimit
presentations.** If the inverse images `s_i⁻¹g_{i, *}ℱ_i` present `g_*ℱ` and the inverse images
`r_i⁻¹h_{i, *}e_i⁻¹ℱ_i` present `h_*e⁻¹ℱ`, through the maps of
`Stacks.EtaleCohomology.LimitDirectImage.baseChangeProjectionMap`, and the base change map of every
level is an isomorphism, then so is the base change map of the limit square. -/
theorem isIso_smallEtaleSheafBaseChange_of_isColimit
    (hι : F.IsSheafPullbackCocone cT ι)
    (hS : (pushforwardSystem A g F).IsSheafPullbackColimitPresentation cS
      ((smallEtalePushforward (limitMorphism g cT cS hcS) A).obj 𝓕)
      (baseChangeProjectionMap A g cT hcS F ι))
    (hX : (pushforwardSystem A h (F.sheafPullback e)).IsSheafPullbackColimitPresentation cX
      ((smallEtalePushforward (limitMorphism h cY cX hcX) A).obj
        ((smallEtaleSheafPullback A eL).obj 𝓕))
      (baseChangeProjectionMap A h cY hcX (F.sheafPullback e) (F.sheafPullbackLeg e eL heL ι)))
    (hstage : ∀ i : Iᵒᵖ, IsIso ((smallEtaleSheafBaseChange A (f.app i) (g.app i) (h.app i)
      (e.app i) (w i)).app (F.obj i))) :
    IsIso ((smallEtaleSheafBaseChange A fL (limitMorphism g cT cS hcS)
      (limitMorphism h cY cX hcX) eL wL).app 𝓕) := by
  have : ∀ i, IsIso (sheafStageComparison A f g h e fL hfL w F i) := fun i =>
    isIso_sheafStageComparison A f g h e fL hfL w F i (hstage i)
  have hιY : (F.sheafPullback e).IsSheafPullbackCocone cY (F.sheafPullbackLeg e eL heL ι) :=
    F.isSheafPullbackCocone_sheafPullback e eL heL ι hι
  refine (hS.map_of_isLeftAdjoint (smallEtaleSheafAdjunction A fL)).isIso_of_isIso_app
    (fun {i j} a => ?_) hX (fun {i j} a => ?_) (sheafStageComparison A f g h e fL hfL w F)
    (fun {i j} a => map_sheafPullbackDiagramMap_comp_sheafStageComparison A f g h e fL hfL w F a)
    _ (fun i => map_projectionMap_comp_smallEtaleSheafBaseChange A f g h e fL eL hfL heL w F hcX
      hcS wL ι i)
  · rw [← Functor.map_comp, isSheafPullbackCocone_baseChangeProjectionMap A g cT hcS F ι hι a]
  · exact isSheafPullbackCocone_baseChangeProjectionMap A h cY hcX (F.sheafPullback e) _ hιY a

end Comparison

/-! ### Conclusion (1) of Stacks 0EZT -/

/-- **Conclusion (1) of Stacks 0EZT.** Let `I` be a directed set and let
`(X_i, Y_i, S_i, T_i, f_i, h_i, e_i, g_i)` be an inverse system of cartesian squares of schemes
with affine transition morphisms and with `g_i` quasi-compact and quasi-separated, with limit
square `(X, Y, S, T, f, h, e, g)`. Let `(ℱ_i, φ_{i'i})` be a system of sheaves of sets on `(T_i)`
and `ℱ = colim p_i⁻¹ℱ_i`. If the base change map `f_i⁻¹g_{i, *}ℱ_i ⟶ h_{i, *}e_i⁻¹ℱ_i` is an
isomorphism for every `i`, then so is `f⁻¹g_*ℱ ⟶ h_*e⁻¹ℱ`.

The limit morphisms are any morphisms `f`, `g`, `h`, `e` satisfying the equations of the
projection squares, and `ℱ = colim p_i⁻¹ℱ_i` is given by maps `ι_i : p_i⁻¹ℱ_i ⟶ ℱ` compatible with
the transition maps and enjoying the universal property of the colimit. -/
@[stacks 0EZT "conclusion (1): if base change for sheaves of sets holds at every level of the \
system of cartesian squares, it holds for the limit square"]
theorem isIso_smallEtaleSheafBaseChange_limit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
    (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i))
    {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
    (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT) (hcY : IsLimit cY)
    (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (F : EtaleSheafSystem DT (Type (u + 1))) (𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1)))
    (ι : ∀ i : Iᵒᵖ, (smallEtaleSheafPullback (Type (u + 1)) (X := cT.pt) (cT.π.app i)).obj
      (F.obj i) ⟶ 𝓕)
    (hι : F.IsSheafPullbackCocone cT ι) (hpres : F.IsSheafPullbackColimitPresentation cT 𝓕 ι)
    (hstage : ∀ i : Iᵒᵖ, IsIso ((smallEtaleSheafBaseChange (Type (u + 1)) (f.app i) (g.app i)
      (h.app i) (e.app i) (hsq i).w).app (F.obj i))) :
    IsIso ((smallEtaleSheafBaseChange (Type (u + 1)) fL gL hL eL
      (limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL
        fun i => (hsq i).w)).app 𝓕) := by
  obtain rfl : gL = limitMorphism g cT cS hcS :=
    hcS.hom_ext fun i => by rw [hgL, limitMorphism_comp_π]
  obtain rfl : hL = limitMorphism h cY cX hcX :=
    hcX.hom_ext fun i => by rw [hhL, limitMorphism_comp_π]
  have : ∀ i, QuasiCompact (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hsq i).flip inferInstance
  have : ∀ i, QuasiSeparated (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hsq i).flip inferInstance
  exact isIso_smallEtaleSheafBaseChange_of_isColimit (Type (u + 1)) f g h e fL eL hfL heL
    (fun i => (hsq i).w) F hcX hcS _ ι hι
    (Sets.isSheafPullbackColimitPresentation_projectionMap g hcT hcS F ι hι hpres)
    (Sets.isSheafPullbackColimitPresentation_projectionMap h hcY hcX (F.sheafPullback e) _
      (F.isSheafPullbackCocone_sheafPullback e eL heL ι hι)
      (F.isSheafPullbackColimitPresentation_sheafPullback e eL heL ι hpres))
    hstage

end Stacks.EtaleCohomology.LimitBaseChange

end
