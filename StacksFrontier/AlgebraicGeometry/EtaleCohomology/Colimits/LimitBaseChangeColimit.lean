module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystemPresentation

/-!
# Base change for higher direct images passes to the limit

Let `I` be a directed set and let

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

be an inverse system of cartesian squares of schemes with affine transition morphisms and with
`g_i` quasi-compact and quasi-separated, with limit square `(X, Y, S, T, f, h, e, g)` and
projections `r_i : X ⟶ X_i`, `s_i : S ⟶ S_i`, `p_i : T ⟶ T_i`, `q_i : Y ⟶ Y_i`. Let
`(ℱ_i, φ_{i'i})` be a system of abelian sheaves on `(T_i)` and `ℱ = colim p_i⁻¹ℱ_i`. Conclusion (2)
of [Stacks, Tag 0EZT] asserts: if `f_i⁻¹R^q g_{i, *}ℱ_i ⟶ R^q h_{i, *}e_i⁻¹ℱ_i` is an
isomorphism for every `i`, then so is `f⁻¹R^q g_*ℱ ⟶ R^q h_*e⁻¹ℱ`.

The proof is the source's. By [Stacks, Tag 0EYM] applied to `g` and the system `ℱ_i`,
`R^q g_*ℱ = colim s_i⁻¹R^q g_{i, *}ℱ_i`, and inverse image along `f` preserves this colimit, being
a left adjoint. The inverse images `e_i⁻¹ℱ_i` form a system on `(Y_i)` whose colimit is `e⁻¹ℱ`, so
[Stacks, Tag 0EYM] applied to `h` gives `R^q h_*e⁻¹ℱ = colim r_i⁻¹R^q h_{i, *}e_i⁻¹ℱ_i`. The base
change maps of the levels, pulled back to `X` along `r_i`, are a map of the two systems
compatible with the base change map of the limit square, by the pasting of base change maps
([Stacks, Tag 0E47]); a map of colimits which is invertible on every level is invertible.

## Main definitions

* `Stacks.EtaleCohomology.LimitBaseChange.levelComparison`: the base change map of the `i`-th
  square, pulled back to `X`, as a map `f⁻¹s_i⁻¹R^q g_{i, *}ℱ_i ⟶ r_i⁻¹R^q h_{i, *}e_i⁻¹ℱ_i`.

## Main results

* `Stacks.EtaleCohomology.LimitBaseChange.map_higherDirectImageDiagramMap_comp_levelComparison`:
  the level comparisons commute with the transition maps of the two systems of [Stacks, Tag 0EYM].
* `Stacks.EtaleCohomology.LimitBaseChange.map_projectionMap_comp_higherBaseChangeMapAb`: the
  level comparisons are compatible with the base change map of the limit square.
* `Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit_of_isLimit`:
  conclusion (2) of [Stacks, Tag 0EZT], from the limit properties of the four cones; the colimit
  presentations that `Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_limit`
  takes as inputs are constructed here from [Stacks, Tag 0EYM].

## Implementation notes

The four limit morphisms are given as morphisms together with the equations
`f ≫ s_i = r_i ≫ f_i` (and so on) characterising them, as in
`Stacks.EtaleCohomology.LimitBaseChange.isPullback_limitSquare`. The colimit
`ℱ = colim p_i⁻¹ℱ_i` is given, as in [Stacks, Tag 0EYM], by a sheaf `ℱ` with maps
`ι_i : p_i⁻¹ℱ_i ⟶ ℱ` compatible with the transition maps and enjoying the universal property of
the colimit of the system.

The two compatibilities of the level comparisons are first proved for arbitrary morphisms of
schemes subject to the equations of the projection and transition squares, with each composite
along which inverse images are compared given as a separate morphism together with its
factorisations; they are then specialised to the projections of the cones. The comparisons of
inverse images along composites are written on components with iterated inverse images as
sources (`Stacks.EtaleCohomology.smallEtalePullbackAbCompApp`).

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitBaseChange

open LimitHigherDirectImage

local notation "App" => smallEtalePullbackAbCompApp

/-! ### The two compatibilities for arbitrary morphisms

The compatibilities of the level comparisons with the legs and with the transition maps are
first proved for arbitrary morphisms of schemes subject to the equations of the projection and
transition squares; the composites the comparisons of inverse images are taken along are
variables with their factorisations as hypotheses. -/

section Generic

variable {X S T Y X₀ S₀ T₀ Y₀ : Scheme.{u}} (fL : X ⟶ S) (gL : T ⟶ S) (hL : Y ⟶ X) (eL : Y ⟶ T)
  (r : X ⟶ X₀) (s : S ⟶ S₀) (p : T ⟶ T₀) (t : Y ⟶ Y₀)
  (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀)
  (u : X ⟶ S₀) (v : Y ⟶ T₀) (hu₁ : u = fL ≫ s) (hu₂ : u = r ≫ f₀) (hv₁ : v = eL ≫ p)
  (hv₂ : v = t ≫ e₀) (hgL : gL ≫ s = p ≫ g₀) (hhL : hL ≫ r = t ≫ h₀)
  (w₀ : h₀ ≫ f₀ = e₀ ≫ g₀) (wL : hL ≫ fL = eL ≫ gL)
  (q : ℕ) (G : Sheaf (smallEtaleTopology T₀) Ab.{u + 1})
  {𝓕 : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (ι : (smallEtalePullbackAb p).obj G ⟶ 𝓕)

include hu₂ hv₂ hhL w₀ in
private theorem legs_rectangle_comm : hL ≫ u = v ≫ g₀ := by
  rw [hu₂, hv₂, ← Category.assoc, hhL, Category.assoc, w₀, Category.assoc]

private theorem legs_paste₁ :
    (higherBaseChangeMapAb u g₀ hL v (legs_rectangle_comm hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀)
        q).app G =
      (App fL s u hu₁ (((smallEtalePushforwardAb g₀).rightDerived q).obj G)).inv ≫
        (smallEtalePullbackAb fL).map ((higherBaseChangeMapAb s g₀ gL p hgL q).app G) ≫
        (higherBaseChangeMapAb fL gL hL eL wL q).app ((smallEtalePullbackAb p).obj G) ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map (App eL p v hv₁ G).hom :=
  higherBaseChangeMapAb_paste_app_named g₀ gL hL s fL p eL u hu₁ v hv₁
    (legs_rectangle_comm hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀) hgL wL q G

private theorem legs_paste₂ :
    (higherBaseChangeMapAb u g₀ hL v (legs_rectangle_comm hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀)
        q).app G =
      (App r f₀ u hu₂ (((smallEtalePushforwardAb g₀).rightDerived q).obj G)).inv ≫
        (smallEtalePullbackAb r).map ((higherBaseChangeMapAb f₀ g₀ h₀ e₀ w₀ q).app G) ≫
        (higherBaseChangeMapAb r h₀ hL t hhL q).app ((smallEtalePullbackAb e₀).obj G) ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map (App t e₀ v hv₂ G).hom :=
  higherBaseChangeMapAb_paste_app_named g₀ h₀ hL f₀ r e₀ t u hu₂ v hv₂
    (legs_rectangle_comm hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀) w₀ hhL q G

private theorem legs_mapComp :
    (smallEtalePullbackAb fL).map ((higherBaseChangeMapAb s g₀ gL p hgL q).app G ≫
        ((smallEtalePushforwardAb gL).rightDerived q).map ι) =
      (smallEtalePullbackAb fL).map ((higherBaseChangeMapAb s g₀ gL p hgL q).app G) ≫
        (smallEtalePullbackAb fL).map (((smallEtalePushforwardAb gL).rightDerived q).map ι) :=
  (smallEtalePullbackAb fL).map_comp _ _

private theorem legs_naturality :
    (smallEtalePullbackAb fL).map (((smallEtalePushforwardAb gL).rightDerived q).map ι) ≫
        (higherBaseChangeMapAb fL gL hL eL wL q).app 𝓕 =
      (higherBaseChangeMapAb fL gL hL eL wL q).app ((smallEtalePullbackAb p).obj G) ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map ((smallEtalePullbackAb eL).map ι) :=
  (higherBaseChangeMapAb fL gL hL eL wL q).naturality ι

private theorem legs_cancel :
    ((smallEtalePushforwardAb hL).rightDerived q).map (App eL p v hv₁ G).hom ≫
      ((smallEtalePushforwardAb hL).rightDerived q).map (App eL p v hv₁ G).inv = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

private theorem legs_leg :
    ((smallEtalePushforwardAb hL).rightDerived q).map ((App t e₀ v hv₂ G).hom ≫
        (App eL p v hv₁ G).inv ≫ (smallEtalePullbackAb eL).map ι) =
      ((smallEtalePushforwardAb hL).rightDerived q).map (App t e₀ v hv₂ G).hom ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map (App eL p v hv₁ G).inv ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map ((smallEtalePullbackAb eL).map ι) :=
  (Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))

/-- The compatibility of the base change maps of a level square and of the limit square with
the legs, for arbitrary morphisms subject to the equations of the projection squares. -/
private theorem legs_generic :
    (smallEtalePullbackAb fL).map ((higherBaseChangeMapAb s g₀ gL p hgL q).app G ≫
        ((smallEtalePushforwardAb gL).rightDerived q).map ι) ≫
        (higherBaseChangeMapAb fL gL hL eL wL q).app 𝓕 =
      ((App fL s u hu₁ (((smallEtalePushforwardAb g₀).rightDerived q).obj G)).hom ≫
        (App r f₀ u hu₂ (((smallEtalePushforwardAb g₀).rightDerived q).obj G)).inv ≫
        (smallEtalePullbackAb r).map ((higherBaseChangeMapAb f₀ g₀ h₀ e₀ w₀ q).app G)) ≫
      ((higherBaseChangeMapAb r h₀ hL t hhL q).app ((smallEtalePullbackAb e₀).obj G) ≫
        ((smallEtalePushforwardAb hL).rightDerived q).map ((App t e₀ v hv₂ G).hom ≫
          (App eL p v hv₁ G).inv ≫ (smallEtalePullbackAb eL).map ι)) := by
  rw [legs_mapComp, Category.assoc, legs_naturality, legs_leg]
  simp only [Category.assoc]
  rw [← reassoc_of% (legs_paste₂ hL r t f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀ q G),
    reassoc_of% (legs_paste₁ fL gL hL eL r s p t f₀ g₀ h₀ e₀ u v hu₁ hu₂ hv₁ hv₂ hgL hhL w₀ wL q G),
    Iso.hom_inv_id_assoc, reassoc_of% (legs_cancel hL eL p v hv₁ q G)]

end Generic

/-! ### The base change map on components -/

/-- The component of the base change map on higher direct images at a sheaf, with source and
target written as iterated functors. -/
private def bcApp {X' Y' S' T' : Scheme.{u}} (f' : X' ⟶ S') (g' : T' ⟶ S') (h' : Y' ⟶ X')
    (e' : Y' ⟶ T') (w' : h' ≫ f' = e' ≫ g') (q : ℕ) (G : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    (smallEtalePullbackAb f').obj (((smallEtalePushforwardAb g').rightDerived q).obj G) ⟶
      ((smallEtalePushforwardAb h').rightDerived q).obj ((smallEtalePullbackAb e').obj G) :=
  (higherBaseChangeMapAb f' g' h' e' w' q).app G

private theorem bcApp_naturality {X' Y' S' T' : Scheme.{u}} (f' : X' ⟶ S') (g' : T' ⟶ S')
    (h' : Y' ⟶ X') (e' : Y' ⟶ T') (w' : h' ≫ f' = e' ≫ g') (q : ℕ)
    {G G' : Sheaf (smallEtaleTopology T') Ab.{u + 1}} (φ : G ⟶ G') :
    (smallEtalePullbackAb f').map (((smallEtalePushforwardAb g').rightDerived q).map φ) ≫
        bcApp f' g' h' e' w' q G' =
      bcApp f' g' h' e' w' q G ≫
        ((smallEtalePushforwardAb h').rightDerived q).map ((smallEtalePullbackAb e').map φ) :=
  (higherBaseChangeMapAb f' g' h' e' w' q).naturality φ

/-- The pasting of base change maps, on components. -/
private theorem bcApp_paste {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
    (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂) (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀)
    (v₂ : X₂ ⟶ X₁) (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁)
    (w : g₂ ≫ u = v ≫ g₀) (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (G : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    bcApp u g₀ g₂ v w q G =
      (App u₂ u₁ u hu (((smallEtalePushforwardAb g₀).rightDerived q).obj G)).inv ≫
        (smallEtalePullbackAb u₂).map (bcApp u₁ g₀ g₁ v₁ w₁ q G) ≫
          bcApp u₂ g₁ g₂ v₂ w₂ q ((smallEtalePullbackAb v₁).obj G) ≫
            ((smallEtalePushforwardAb g₂).rightDerived q).map (App v₂ v₁ v hv G).hom :=
  higherBaseChangeMapAb_paste_app_named g₀ g₁ g₂ u₁ u₂ v₁ v₂ u hu v hv w w₁ w₂ q G

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
  (q : ℕ) (Gj : Sheaf (smallEtaleTopology Tj) Ab.{u + 1})
  (Gi : Sheaf (smallEtaleTopology Ti) Ab.{u + 1}) (φ : (smallEtalePullbackAb ta).obj Gj ⟶ Gi)

include hU₁ hV₁ hht wj in
/-- The rectangle `Y_i ⟶ X_i ⟶ S_j`, `Y_i ⟶ T_j ⟶ S_j` commutes: `h_i ≫ U = V ≫ g_j`. -/
theorem diagram_rectangle_comm : hi ≫ U = V ≫ gj := by
  rw [hU₁, hV₁, ← Category.assoc, hht, Category.assoc, wj, Category.assoc]

include hui₁ huj₁ hsj in
private theorem diagram_uj_eq₁ : uj = ui ≫ sa := by
  rw [huj₁, hsj, hui₁, Category.assoc]

include huj₂ hrj hU₁ in
private theorem diagram_uj_eq₂ : uj = ri ≫ U := by
  rw [huj₂, hrj, hU₁, Category.assoc]

/-- **The coherence of the comparisons of inverse images** in the naturality of the level
comparisons: both composites are the comparison `f⁻¹s_j⁻¹ ≅ (r_i ≫ U)⁻¹` along the two
factorisations of `X ⟶ S_j`. -/
theorem pullbackComparison_coherence (M : Sheaf (smallEtaleTopology Sj) Ab.{u + 1}) :
    (smallEtalePullbackAb fL).map (App si sa sj hsj M).inv ≫
        (App fL si ui hui₁ ((smallEtalePullbackAb sa).obj M)).hom ≫
        (App ri fi ui hui₂ ((smallEtalePullbackAb sa).obj M)).inv ≫
        (smallEtalePullbackAb ri).map (App fi sa U hU₂ M).hom =
      (App fL sj uj huj₁ M).hom ≫ (App rj fj uj huj₂ M).inv ≫
        (App ri xa rj hrj ((smallEtalePullbackAb fj).obj M)).inv ≫
        (smallEtalePullbackAb ri).map (App xa fj U hU₁ M).hom := by
  have h₁ := diagram_uj_eq₁ fL si sj sa hsj ui uj hui₁ huj₁
  have h₂ := diagram_uj_eq₂ ri rj fj xa hrj uj huj₂ U hU₁
  rw [← cancel_mono (App ri U uj h₂ M).hom]
  simp only [Category.assoc]
  rw [← smallEtalePullbackAbCompApp_assoc ri fi sa ui hui₂ U hU₂ uj h₁ h₂ M,
    Iso.inv_hom_id_assoc, smallEtalePullbackAbCompApp_assoc fL si sa ui hui₁ sj hsj uj h₁ huj₁ M,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← smallEtalePullbackAbCompApp_assoc ri xa fj rj hrj U hU₁ uj huj₂ h₂ M,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The first decomposition of the base change map of the rectangle `U = f_i ≫ s_{ji}`, under
inverse image along `r_i`. -/
private theorem diagram_pasteLeft :
    (smallEtalePullbackAb ri).map ((smallEtalePullbackAb fi).map (bcApp sa gj gi ta hgt q Gj)) ≫
        (smallEtalePullbackAb ri).map (bcApp fi gi hi ei wi q ((smallEtalePullbackAb ta).obj Gj)) =
      (smallEtalePullbackAb ri).map
          (App fi sa U hU₂ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).hom ≫
        (smallEtalePullbackAb ri).map
          (bcApp U gj hi V (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁) q Gj) ≫
        (smallEtalePullbackAb ri).map
          (((smallEtalePushforwardAb hi).rightDerived q).map (App ei ta V hV₂ Gj).inv) := by
  have key : (smallEtalePullbackAb fi).map (bcApp sa gj gi ta hgt q Gj) ≫
        bcApp fi gi hi ei wi q ((smallEtalePullbackAb ta).obj Gj) =
      (App fi sa U hU₂ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).hom ≫
        bcApp U gj hi V (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁) q Gj ≫
        ((smallEtalePushforwardAb hi).rightDerived q).map (App ei ta V hV₂ Gj).inv := by
    rw [bcApp_paste gj gi hi sa fi ta ei U hU₂ V hV₂ _ hgt wi q Gj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Functor.map_comp, key, Functor.map_comp, Functor.map_comp]

/-- The second decomposition of the base change map of the rectangle `U = f_{ji} ≫ f_j`, under
inverse image along `r_i`. -/
private theorem diagram_pasteRight :
    (smallEtalePullbackAb ri).map ((smallEtalePullbackAb xa).map (bcApp fj gj hj ej wj q Gj)) ≫
        (smallEtalePullbackAb ri).map (bcApp xa hj hi ya hht q ((smallEtalePullbackAb ej).obj Gj)) ≫
        (smallEtalePullbackAb ri).map
          (((smallEtalePushforwardAb hi).rightDerived q).map (App ya ej V hV₁ Gj).hom) =
      (smallEtalePullbackAb ri).map
          (App xa fj U hU₁ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).hom ≫
        (smallEtalePullbackAb ri).map
          (bcApp U gj hi V
            (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁) q Gj) := by
  have key : (smallEtalePullbackAb xa).map (bcApp fj gj hj ej wj q Gj) ≫
        bcApp xa hj hi ya hht q ((smallEtalePullbackAb ej).obj Gj) ≫
        ((smallEtalePushforwardAb hi).rightDerived q).map (App ya ej V hV₁ Gj).hom =
      (App xa fj U hU₁ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).hom ≫
        bcApp U gj hi V (diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁) q Gj := by
    rw [bcApp_paste gj hj hi fj xa ej ya U hU₁ V hV₁ _ wj hht q Gj, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, key, Functor.map_comp]

/-- The naturality of the base change map of the `i`-th square at `φ`, under inverse image along
`r_i`. -/
private theorem diagram_naturality :
    (smallEtalePullbackAb ri).map
        ((smallEtalePullbackAb fi).map (((smallEtalePushforwardAb gi).rightDerived q).map φ)) ≫
        (smallEtalePullbackAb ri).map (bcApp fi gi hi ei wi q Gi) =
      (smallEtalePullbackAb ri).map (bcApp fi gi hi ei wi q ((smallEtalePullbackAb ta).obj Gj)) ≫
        (smallEtalePullbackAb ri).map
          (((smallEtalePushforwardAb hi).rightDerived q).map
            ((smallEtalePullbackAb ei).map φ)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, bcApp_naturality]

include U hU₁ hU₂ in
/-- **The naturality of the level comparisons**, for arbitrary morphisms subject to the
equations of the projection and transition squares. -/
private theorem diagram_generic :
    (smallEtalePullbackAb fL).map
        ((App si sa sj hsj (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).inv ≫
          (smallEtalePullbackAb si).map (bcApp sa gj gi ta hgt q Gj ≫
            ((smallEtalePushforwardAb gi).rightDerived q).map φ)) ≫
        ((App fL si ui hui₁ (((smallEtalePushforwardAb gi).rightDerived q).obj Gi)).hom ≫
          (App ri fi ui hui₂ (((smallEtalePushforwardAb gi).rightDerived q).obj Gi)).inv ≫
          (smallEtalePullbackAb ri).map (bcApp fi gi hi ei wi q Gi)) =
      ((App fL sj uj huj₁ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).hom ≫
          (App rj fj uj huj₂ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj)).inv ≫
          (smallEtalePullbackAb rj).map (bcApp fj gj hj ej wj q Gj)) ≫
        (App ri xa rj hrj (((smallEtalePushforwardAb hj).rightDerived q).obj
            ((smallEtalePullbackAb ej).obj Gj))).inv ≫
          (smallEtalePullbackAb ri).map
            (bcApp xa hj hi ya hht q ((smallEtalePullbackAb ej).obj Gj) ≫
              ((smallEtalePushforwardAb hi).rightDerived q).map ((App ya ej V hV₁ Gj).hom ≫
                (App ei ta V hV₂ Gj).inv ≫ (smallEtalePullbackAb ei).map φ)) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtalePullbackAbCompApp_hom_naturality fL si ui hui₁
      (((smallEtalePushforwardAb gi).rightDerived q).map φ)),
    reassoc_of% (smallEtalePullbackAbCompApp_hom_naturality fL si ui hui₁
      (bcApp sa gj gi ta hgt q Gj)),
    reassoc_of% (smallEtalePullbackAbCompApp_inv_naturality ri fi ui hui₂
      (((smallEtalePushforwardAb gi).rightDerived q).map φ)),
    reassoc_of% (smallEtalePullbackAbCompApp_inv_naturality ri fi ui hui₂
      (bcApp sa gj gi ta hgt q Gj)),
    diagram_naturality ri fi gi hi ei ta wi q Gj Gi φ,
    reassoc_of% (diagram_pasteLeft ri fi fj gi gj hi hj ei ej xa sa ta ya hgt hht wi wj U hU₁ hU₂
      V hV₁ hV₂ q Gj),
    reassoc_of% (smallEtalePullbackAbCompApp_inv_naturality ri xa rj hrj
      (bcApp fj gj hj ej wj q Gj)),
    reassoc_of% (diagram_pasteRight ri fj gj hi hj ej xa ya hht wj U hU₁ V hV₁ q Gj),
    reassoc_of% (pullbackComparison_coherence fL ri rj si sj fi fj xa sa hrj hsj ui uj hui₁ hui₂
      huj₁ huj₂ U hU₁ hU₂ (((smallEtalePushforwardAb gj).rightDerived q).obj Gj))]

end GenericDiagram

/-! ### The comparison of the two systems -/

variable {I : Type u} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (fL : cX.pt ⟶ cS.pt) (eL : cY.pt ⟶ cT.pt)
  (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
  (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  (F : EtaleSheafSystem DT Ab.{u + 1}) (q : ℕ)

/-- **The comparison of the two colimit diagrams at a level**: the base change map
`f_i⁻¹R^q g_{i, *}ℱ_i ⟶ R^q h_{i, *}e_i⁻¹ℱ_i` of the `i`-th square, pulled back to `X` along
`r_i` and read on the source through the comparison `f⁻¹s_i⁻¹ ≅ r_i⁻¹f_i⁻¹` of the two composite
inverse images along `f ≫ s_i = r_i ≫ f_i`. -/
def levelComparison (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).obj ((smallEtalePullbackAb (cS.π.app i)).obj
        (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))) ⟶
      (smallEtalePullbackAb (cX.π.app i)).obj
        (((smallEtalePushforwardAb (h.app i)).rightDerived q).obj
          ((smallEtalePullbackAb (e.app i)).obj (F.obj i))) :=
  (App fL (cS.π.app i) (cX.π.app i ≫ f.app i) (hfL i).symm
      (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
    (App (cX.π.app i) (f.app i) (cX.π.app i ≫ f.app i) rfl
      (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).inv ≫
    (smallEtalePullbackAb (cX.π.app i)).map
      ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i))

/-- The level comparison is invertible as soon as the base change map of the `i`-th square is:
the other two factors are isomorphisms. -/
theorem isIso_levelComparison (i : Iᵒᵖ)
    (hi : IsIso ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app
      (F.obj i))) :
    IsIso (levelComparison f g h e fL hfL w F q i) := by
  unfold levelComparison
  infer_instance


/-! ### The two compatibilities -/

section Compatibilities

/-- The level comparison in terms of the comparisons of inverse images with the vertex of the
cone as source. -/
private theorem levelComparison_eq (i : Iᵒᵖ) :
    levelComparison f g h e fL hfL w F q i =
      (App fL (cS.π.app i) (cX.π.app i ≫ f.app i) (hfL i).symm
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
        (@smallEtalePullbackAbCompApp cX.pt (DX.obj i) (DS.obj i) (cX.π.app i) (f.app i)
            (cX.π.app i ≫ f.app i) rfl
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).inv ≫
        (smallEtalePullbackAb (X := cX.pt) (cX.π.app i)).map
          (bcApp (f.app i) (g.app i) (h.app i) (e.app i) (w i) q (F.obj i)) :=
  rfl

private theorem diagramMap_g_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    higherDirectImageDiagramMap g q cS F a =
      (@smallEtalePullbackAbCompApp cS.pt (DS.obj i) (DS.obj j) (cS.π.app i) (DS.map a)
          (cS.π.app j) (cS.w a).symm
          (((smallEtalePushforwardAb (g.app j)).rightDerived q).obj (F.obj j))).inv ≫
        (smallEtalePullbackAb (X := cS.pt) (cS.π.app i)).map
          (bcApp (DS.map a) (g.app j) (g.app i) (DT.map a) (transition_comm g a) q (F.obj j) ≫
            ((smallEtalePushforwardAb (g.app i)).rightDerived q).map
              (EtaleSheafSystem.smallEtaleMap F a)) := by
  rw [higherDirectImageDiagramMap, conePullbackComp_inv_app_eq]
  rfl

private theorem diagramMap_h_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    higherDirectImageDiagramMap h q cX (EtaleSheafSystem.pullback e F) a =
      (@smallEtalePullbackAbCompApp cX.pt (DX.obj i) (DX.obj j) (cX.π.app i) (DX.map a)
          (cX.π.app j) (cX.w a).symm
          (((smallEtalePushforwardAb (h.app j)).rightDerived q).obj
            ((smallEtalePullbackAb (e.app j)).obj (F.obj j)))).inv ≫
        (smallEtalePullbackAb (X := cX.pt) (cX.π.app i)).map
          (bcApp (DX.map a) (h.app j) (h.app i) (DY.map a) (transition_comm h a) q
              ((smallEtalePullbackAb (e.app j)).obj (F.obj j)) ≫
            ((smallEtalePushforwardAb (h.app i)).rightDerived q).map
              ((App (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl (F.obj j)).hom ≫
                (App (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a) (F.obj j)).inv ≫
                (smallEtalePullbackAb (e.app i)).map (EtaleSheafSystem.smallEtaleMap F a))) := by
  rw [higherDirectImageDiagramMap, conePullbackComp_inv_app_eq]
  rfl

/-- **The level comparisons commute with the transition maps** of the two systems of
[Stacks, Tag 0EYM]: the inverse image along `f` of the transition map
`s_{i'}⁻¹R^q g_{i', *}ℱ_{i'} ⟶ s_i⁻¹R^q g_{i, *}ℱ_i` followed by the comparison at `i` is the
comparison at `i'` followed by the transition map of the system `r_i⁻¹R^q h_{i, *}e_i⁻¹ℱ_i`. -/
theorem map_higherDirectImageDiagramMap_comp_levelComparison {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb fL).map (higherDirectImageDiagramMap g q cS F a) ≫
        levelComparison f g h e fL hfL w F q i =
      levelComparison f g h e fL hfL w F q j ≫
        higherDirectImageDiagramMap h q cX (EtaleSheafSystem.pullback e F) a := by
  rw [diagramMap_g_eq, diagramMap_h_eq, levelComparison_eq, levelComparison_eq]
  exact diagram_generic fL (cX.π.app i) (cX.π.app j) (cS.π.app i) (cS.π.app j) (f.app i)
    (f.app j) (g.app i) (g.app j) (h.app i) (h.app j) (e.app i) (e.app j) (DX.map a) (DS.map a)
    (DT.map a) (DY.map a) (cX.w a).symm (cS.w a).symm (transition_comm g a) (transition_comm h a)
    (w i) (w j) (cX.π.app i ≫ f.app i) (cX.π.app j ≫ f.app j) (hfL i).symm rfl (hfL j).symm rfl
    (DX.map a ≫ f.app j) rfl (f.naturality a) (DY.map a ≫ e.app j) rfl (e.naturality a) q
    (F.obj j) (F.obj i) (EtaleSheafSystem.smallEtaleMap F a)

variable (hcX : IsLimit cX) (hcS : IsLimit cS)
  (wL : limitMorphism h cY cX hcX ≫ fL = eL ≫ limitMorphism g cT cS hcS)
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1}}
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)

private theorem levelComparison_eq_app (i : Iᵒᵖ) :
    levelComparison f g h e fL hfL w F q i =
      (App fL (cS.π.app i) (cX.π.app i ≫ f.app i) (hfL i).symm
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).hom ≫
        (@smallEtalePullbackAbCompApp cX.pt (DX.obj i) (DS.obj i) (cX.π.app i) (f.app i)
          (cX.π.app i ≫ f.app i) rfl
          (((smallEtalePushforwardAb (g.app i)).rightDerived q).obj (F.obj i))).inv ≫
        (smallEtalePullbackAb (X := cX.pt) (cX.π.app i)).map
          ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i) (w i) q).app (F.obj i)) :=
  rfl

private theorem projectionMap_g_eq (i : Iᵒᵖ) :
    projectionMap g cT cS hcS q 𝓕 F ι i =
      (higherBaseChangeMapAb (X' := cS.pt) (cS.π.app i) (g.app i) (limitMorphism g cT cS hcS)
          (cT.π.app i) (limitMorphism_comp_π g cT cS hcS i) q).app (F.obj i) ≫
        ((smallEtalePushforwardAb (limitMorphism g cT cS hcS)).rightDerived q).map
          (X := (smallEtalePullbackAb (X := cT.pt) (cT.π.app i)).obj (F.obj i)) (ι i) :=
  rfl

private theorem projectionMap_h_eq (i : Iᵒᵖ) :
    projectionMap h cY cX hcX q ((smallEtalePullbackAb eL).obj 𝓕) (EtaleSheafSystem.pullback e F)
        (EtaleSheafSystem.pullbackLeg e eL heL F ι) i =
      (higherBaseChangeMapAb (X' := cX.pt) (cX.π.app i) (h.app i) (limitMorphism h cY cX hcX)
          (cY.π.app i) (limitMorphism_comp_π h cY cX hcX i) q).app
          ((smallEtalePullbackAb (e.app i)).obj (F.obj i)) ≫
        ((smallEtalePushforwardAb (limitMorphism h cY cX hcX)).rightDerived q).map
          ((@smallEtalePullbackAbCompApp cY.pt (DY.obj i) (DT.obj i) (cY.π.app i) (e.app i)
              (cY.π.app i ≫ e.app i) rfl (F.obj i)).hom ≫
            (App eL (cT.π.app i) (cY.π.app i ≫ e.app i) (heL i).symm (F.obj i)).inv ≫
            (smallEtalePullbackAb eL).map
              (X := (smallEtalePullbackAb (X := cT.pt) (cT.π.app i)).obj (F.obj i)) (ι i)) :=
  rfl

/-- **The level comparisons are compatible with the base change map of the limit square.** The
inverse image along `f` of the leg `s_i⁻¹R^q g_{i, *}ℱ_i ⟶ R^q g_*ℱ` of [Stacks, Tag 0EYM],
followed by the base change map of the limit square, is the level comparison followed by the leg
`r_i⁻¹R^q h_{i, *}e_i⁻¹ℱ_i ⟶ R^q h_*e⁻¹ℱ`: both are decompositions of the base change map of the
rectangle with sides `r_i ≫ f_i` and `q_i ≫ e_i`, by the pasting of base change maps. -/
theorem map_projectionMap_comp_higherBaseChangeMapAb (i : Iᵒᵖ) :
    (smallEtalePullbackAb fL).map (projectionMap g cT cS hcS q 𝓕 F ι i) ≫
        (higherBaseChangeMapAb fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
          q).app 𝓕 =
      levelComparison f g h e fL hfL w F q i ≫
        projectionMap h cY cX hcX q ((smallEtalePullbackAb eL).obj 𝓕)
          (EtaleSheafSystem.pullback e F) (EtaleSheafSystem.pullbackLeg e eL heL F ι) i := by
  rw [projectionMap_g_eq, projectionMap_h_eq, levelComparison_eq_app]
  exact legs_generic fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL (cX.π.app i)
    (cS.π.app i) (cT.π.app i) (cY.π.app i) (f.app i) (g.app i) (h.app i) (e.app i)
    (cX.π.app i ≫ f.app i) (cY.π.app i ≫ e.app i) (hfL i).symm rfl (heL i).symm rfl
    (limitMorphism_comp_π g cT cS hcS i) (limitMorphism_comp_π h cY cX hcX i) (w i) wL q
    (F.obj i) (ι i)

end Compatibilities

/-! ### Conclusion (2) of Stacks 0EZT -/

/-- **Conclusion (2) of Stacks 0EZT.** Let `I` be a directed set and let
`(X_i, Y_i, S_i, T_i, f_i, h_i, e_i, g_i)` be an inverse system of cartesian squares of schemes
with affine transition morphisms and with `g_i` quasi-compact and quasi-separated, with limit
square `(X, Y, S, T, f, h, e, g)`. Let `(ℱ_i, φ_{i'i})` be a system of abelian sheaves on
`(T_i)` and `ℱ = colim p_i⁻¹ℱ_i`. If the base change map
`f_i⁻¹R^q g_{i, *}ℱ_i ⟶ R^q h_{i, *}e_i⁻¹ℱ_i` is an isomorphism for every `i`, then so is
`f⁻¹R^q g_*ℱ ⟶ R^q h_*e⁻¹ℱ`.

The limit morphisms are any morphisms `f`, `g`, `h`, `e` satisfying the equations of the
projection squares, and `ℱ = colim p_i⁻¹ℱ_i` is given by maps `ι_i : p_i⁻¹ℱ_i ⟶ ℱ` compatible with
the transition maps and enjoying the universal property of the colimit. -/
@[stacks 0EZT "conclusion (2): if base change for `R^q` holds at every level of the system of \
cartesian squares, it holds for the limit square"]
theorem isIso_higherBaseChangeMapAb_limit_of_isLimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i))
    (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT) (hcY : IsLimit cY)
    (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cT.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : IsPullbackCocone cT F ι) (hpres : IsPullbackColimitPresentation cT 𝓕 F ι)
    (hstage : ∀ i : Iᵒᵖ, IsIso ((higherBaseChangeMapAb (f.app i) (g.app i) (h.app i) (e.app i)
      (hsq i).w q).app (F.obj i))) :
    IsIso ((higherBaseChangeMapAb fL gL hL eL
      (limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL fun i => (hsq i).w)
        q).app 𝓕) := by
  obtain rfl : gL = limitMorphism g cT cS hcS :=
    hcS.hom_ext fun i => by rw [hgL, limitMorphism_comp_π]
  obtain rfl : hL = limitMorphism h cY cX hcX :=
    hcX.hom_ext fun i => by rw [hhL, limitMorphism_comp_π]
  have : ∀ i, QuasiCompact (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hsq i).flip inferInstance
  have : ∀ i, QuasiSeparated (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hsq i).flip inferInstance
  have : ∀ i, IsIso (levelComparison f g h e fL hfL (fun i => (hsq i).w) F q i) := fun i =>
    isIso_levelComparison f g h e fL hfL _ F q i (hstage i)
  have hιY : IsPullbackCocone cY (EtaleSheafSystem.pullback e F)
      (EtaleSheafSystem.pullbackLeg e eL heL F ι) :=
    EtaleSheafSystem.isPullbackCocone_pullback e eL heL F ι hι
  have hT := (isHigherDirectImageColimit g hcT hcS q F 𝓕 ι hι hpres).isSystemColimit
  refine (hT.map_of_isLeftAdjoint (smallEtaleAdjunctionAb fL)).isIso_of_isIso_app (fun a => ?_)
    (isHigherDirectImageColimit h hcY hcX q (EtaleSheafSystem.pullback e F) _ _ hιY
      (EtaleSheafSystem.isPullbackColimitPresentation_pullback e eL heL F ι hpres)).isSystemColimit
    (fun a => ?_) (levelComparison f g h e fL hfL (fun i => (hsq i).w) F q)
    (fun a => map_higherDirectImageDiagramMap_comp_levelComparison f g h e fL hfL _ F q a) _
    (fun i => map_projectionMap_comp_higherBaseChangeMapAb f g h e fL eL hfL heL _ F q hcX hcS _
      ι i)
  · exact ((smallEtalePullbackAb fL).map_comp _ _).symm.trans (congrArg _
      ((Category.assoc _ _ _).trans (projectionMap_cocone g q cT cS hcS 𝓕 F ι a
        (by rw [← hι a, Iso.hom_inv_id_app_assoc]))))
  · exact (Category.assoc _ _ _).trans (projectionMap_cocone h q cY cX hcX _ _ _ a
      (by rw [← hιY a, Iso.hom_inv_id_app_assoc]))

end Stacks.EtaleCohomology.LimitBaseChange

end
