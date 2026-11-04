module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.MayerVietorisUnits
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.CoverInductionStep
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange

/-!
# The Mayer--Vietoris step of Stacks 0DJ9

Let

```
Y' --g_Y--> Y
|           |
f'          f
v           v
S' --g----> S
```

be a commutative square of schemes, `Y = A ∪ B` a cover by two opens and `A' = g_Y^{-1}A`,
`B' = g_Y^{-1}B` the preimages.  For `K ∈ D(𝒪_Y)`, `K' ∈ D(𝒪_{Y'})` and `φ : L(g_Y)^*K ⟶ K'` the
composition `Lg^*Rf_*K ⟶ Rf'_*L(g_Y)^*K ⟶ Rf'_*K'` is invertible as soon as the corresponding
compositions for the restrictions of the data to `A`, `B` and `A ∩ B` are.

The proof compares the Mayer--Vietoris triangles of `K` on `Y` and of `K'` on `Y'`, whose first
maps are the units of the derived adjunctions of the open immersions.  The comparison of the
second vertices is assembled from base change along the open immersions; the comparison of the
third vertices is supplied by the axiom of completion of morphisms of triangles and identified
with base change along the inclusion of the intersection, because a morphism into
`Rj_{W'*} M` is determined by its restriction to `W'` and the restriction of the second map of
the triangle to `W'` is a split epimorphism.  The derived base change map commutes with the shift,
so it carries a morphism of triangles to a morphism of triangles, and the two-out-of-three
property of distinguished triangles concludes.

## Main results

* `Stacks.Cohomology.BaseChangeCover.pullback_map_unit_comp_restrictBaseChange`: the base change
  along an open immersion carries the unit to the unit.
* `Stacks.Cohomology.BaseChangeCover.isIso_derivedBaseChangeComp_of_cover`: **the Mayer--Vietoris
  step**.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 0ATL](https://stacks.math.columbia.edu/tag/0ATL)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.BaseChangeCover

section Abstract

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} {G : C ⥤ E} {H : D ⥤ F} {Lc : C ⥤ F}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (eg : G ⋙ L₂ ≅ Lc) (ef : L₁ ⋙ H ≅ Lc)

/-- **The base change along an open immersion carries the unit to the unit**, abstractly: let
`β : R₁ ⋙ G ⟶ H ⋙ R₂` be the mate of `α = eg ≫ ef⁻¹`, characterized by its transpose.  Then `G`
of the unit of `L₁ ⊣ R₁` at `K`, followed by `β` and by `R₂ (σ ≫ L₂ φ)` for
`σ = ef ≫ eg⁻¹`, is `φ` followed by the unit of `L₂ ⊣ R₂`. -/
theorem map_unit_comp_mate (K : C) (b : G.obj (R₁.obj (L₁.obj K)) ⟶ R₂.obj (H.obj (L₁.obj K)))
    (hb : L₂.map b ≫ adj₂.counit.app (H.obj (L₁.obj K)) =
      eg.hom.app (R₁.obj (L₁.obj K)) ≫ ef.inv.app (R₁.obj (L₁.obj K)) ≫
        H.map (adj₁.counit.app (L₁.obj K)))
    {K' : E} (φ : G.obj K ⟶ K') :
    G.map (adj₁.unit.app K) ≫ b ≫ R₂.map (ef.hom.app K ≫ eg.inv.app K ≫ L₂.map φ) =
      φ ≫ adj₂.unit.app K' := by
  apply (adj₂.homEquiv _ _).symm.injective
  have hR : L₂.map (φ ≫ adj₂.unit.app K') ≫ adj₂.counit.app (L₂.obj K') = L₂.map φ := by
    rw [Functor.map_comp, Category.assoc, adj₂.left_triangle_components, Category.comp_id]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, hR, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, adj₂.counit_naturality,
    ← Category.assoc (L₂.map b), hb]
  simp only [Category.assoc]
  have hα : L₂.map (G.map (adj₁.unit.app K)) ≫ eg.hom.app (R₁.obj (L₁.obj K)) =
      eg.hom.app K ≫ Lc.map (adj₁.unit.app K) := eg.hom.naturality (adj₁.unit.app K)
  have hα' : Lc.map (adj₁.unit.app K) ≫ ef.inv.app (R₁.obj (L₁.obj K)) =
      ef.inv.app K ≫ H.map (L₁.map (adj₁.unit.app K)) := ef.inv.naturality (adj₁.unit.app K)
  have ht : H.map (L₁.map (adj₁.unit.app K)) ≫ H.map (adj₁.counit.app (L₁.obj K)) = 𝟙 _ := by
    rw [← H.map_comp, adj₁.left_triangle_components K]
    exact H.map_id _
  rw [reassoc_of% hα, reassoc_of% hα', reassoc_of% ht, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app_assoc]

end Abstract

section Ladder

variable {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
  [HasShift C ℤ] [HasShift C' ℤ] [HasShift D ℤ]
  [HasZeroObject C] [HasZeroObject C'] [HasZeroObject D]
  [Preadditive C] [Preadditive C'] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated C'] [Pretriangulated D]
  {F : C ⥤ D} {P : C ⥤ C'} {G : C' ⥤ D} [F.CommShift ℤ] [P.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [P.IsTriangulated] [G.IsTriangulated]

/-- **Two out of three for a twisted comparison, with the third component completed.**  Let
`τ : F ⟶ P ⋙ G` be a natural transformation compatible with the shifts between triangulated
functors, `T` a distinguished triangle in the source of `P` and `T'` one in its target, and `a`,
`b` comparisons of the first two vertices making the first square commute.  If the twisted
comparison is invertible at the second vertex, and at the third vertex for every completion `c`
of the first two components making the second square commute, then it is invertible at the
first vertex. -/
theorem isIso_comp_app_of_completion (τ : F ⟶ P ⋙ G) [NatTrans.CommShift τ ℤ]
    {T : Triangle C} {T' : Triangle C'} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C')
    (a : P.obj T.obj₁ ⟶ T'.obj₁) (b : P.obj T.obj₂ ⟶ T'.obj₂)
    (h₁ : P.map T.mor₁ ≫ b = a ≫ T'.mor₁) (hb : IsIso (τ.app T.obj₂ ≫ G.map b))
    (hc : ∀ c : P.obj T.obj₃ ⟶ T'.obj₃, P.map T.mor₂ ≫ c = b ≫ T'.mor₂ →
      IsIso (τ.app T.obj₃ ≫ G.map c)) :
    IsIso (τ.app T.obj₁ ≫ G.map a) := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism (P.mapTriangle.obj T) T'
    (P.map_distinguished T hT) hT' a b h₁
  let ψ : P.mapTriangle.obj T ⟶ T' := Triangle.homMk _ _ a b c h₁ hc₂ hc₃
  exact isIso_comp_app_obj₁ τ hT hT' ψ (boundary_square_comp τ ψ) hb (hc c hc₂)

/-- `isIso_comp_app_of_completion` for triangles given by their three morphisms. -/
theorem isIso_comp_app_of_completion_mk (τ : F ⟶ P ⋙ G) [NatTrans.CommShift τ ℤ]
    {L M N : C} (u : L ⟶ M) (v : M ⟶ N) (d : N ⟶ L⟦(1 : ℤ)⟧)
    {L' M' N' : C'} (u' : L' ⟶ M') (v' : M' ⟶ N') (d' : N' ⟶ L'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v d ∈ distTriang C) (hT' : Triangle.mk u' v' d' ∈ distTriang C')
    (a : P.obj L ⟶ L') (b : P.obj M ⟶ M') (h₁ : P.map u ≫ b = a ≫ u')
    (hb : IsIso (τ.app M ≫ G.map b))
    (hc : ∀ c : P.obj N ⟶ N', P.map v ≫ c = b ≫ v' → IsIso (τ.app N ≫ G.map c)) :
    IsIso (τ.app L ≫ G.map a) :=
  isIso_comp_app_of_completion τ hT hT' a b h₁ hb hc

end Ladder

section Restriction

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedMayerVietoris
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The transpose of the derived base change map, through the counit. -/
theorem derivedBaseChangeMap_counit {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (d : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback f').map (derivedBaseChangeMap g' f' f g sq d) ≫
        (derivedAdjunction f').counit.app ((derivedPullback g').obj d) =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app ((derivedPushforward f).obj d) ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app ((derivedPushforward f).obj d) ≫
          (derivedPullback g').map ((derivedAdjunction f).counit.app d) :=
  (Adjunction.homEquiv_counit _ _ _ _).symm.trans (derivedBaseChangeMap_adjoint g' f' f g sq d)

variable {Y Y' : Scheme.{u}} (gY : Y' ⟶ Y) (Z : Y.Opens) (Z' : Y'.Opens) (e : Z' ≤ gY ⁻¹ᵁ Z)

/-- The restriction of `g_Y` to an open `Z'` of `Y'` lying over an open `Z` of `Y`, as a morphism
of ringed spaces. -/
abbrev resMap : Z'.toScheme.toSheafedSpace ⟶ Z.toScheme.toSheafedSpace :=
  (gY.resLE Z Z' e).toLRSHom.toShHom

/-- The restriction of `g_Y` followed by the inclusion of `Z` is the inclusion of `Z'` followed by
`g_Y`. -/
theorem resMap_comp : resMap gY Z Z' e ≫ incl Z = incl Z' ≫ gY.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : Z'.toScheme ⟶ Y => k.toLRSHom.toShHom) (gY.resLE_comp_ι e)

/-- The restriction to `Z'` of a morphism `L(g_Y)^* K ⟶ K'`, as a morphism out of the derived
pullback of the restriction of `K` to `Z`. -/
def restrictDatum (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback (resMap gY Z Z' e)).obj ((derivedPullback (incl Z)).obj K) ⟶
      (derivedPullback (incl Z')).obj K' :=
  (derivedPullbackCompIsoCanonical (resMap gY Z Z' e) (incl Z)).hom.app K ≫
    (derivedPullbackCompIsoLeft (resMap gY Z Z' e) (incl Z') (incl Z) gY.toLRSHom.toShHom
      (resMap_comp gY Z Z' e)).inv.app K ≫ (derivedPullback (incl Z')).map φ

/-- **The comparison of `Rj_{Z*}Lj_Z^*K` with `Rj_{Z'*}Lj_{Z'}^*K'`**: base change along the open
immersion followed by the direct image of the restricted datum. -/
def restrictBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback gY.toLRSHom.toShHom).obj ((restrictPush (incl Z)).obj K) ⟶
      (restrictPush (incl Z')).obj K' :=
  derivedBaseChangeMap (resMap gY Z Z' e) (incl Z') (incl Z) gY.toLRSHom.toShHom
      (resMap_comp gY Z Z' e) ((derivedPullback (incl Z)).obj K) ≫
    (derivedPushforward (incl Z')).map (restrictDatum gY Z Z' e K K' φ)

/-- **The comparison carries the unit to the unit.** -/
theorem pullback_map_unit_comp_restrictBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback gY.toLRSHom.toShHom).map ((unit (incl Z)).app K) ≫
        restrictBaseChange gY Z Z' e K K' φ =
      φ ≫ (unit (incl Z')).app K' :=
  map_unit_comp_mate (derivedAdjunction (incl Z)) (derivedAdjunction (incl Z'))
    (derivedPullbackCompIsoLeft (resMap gY Z Z' e) (incl Z') (incl Z) gY.toLRSHom.toShHom
      (resMap_comp gY Z Z' e))
    (derivedPullbackCompIsoCanonical (resMap gY Z Z' e) (incl Z)) K _
    (derivedBaseChangeMap_counit _ _ _ _ _ _) φ

include e in
/-- Restricting along `Z'` the derived pullback along `g_Y` of a morphism whose restriction along
`Z` is invertible gives an isomorphism. -/
theorem isIso_derivedPullback_map_pullback_map
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))} (x : A ⟶ B)
    (hx : IsIso ((derivedPullback (incl Z)).map x)) :
    IsIso ((derivedPullback (incl Z')).map ((derivedPullback gY.toLRSHom.toShHom).map x)) := by
  have h₁ : IsIso ((derivedPullback (incl Z) ⋙ derivedPullback (resMap gY Z Z' e)).map x) :=
    (inferInstance : IsIso ((derivedPullback (resMap gY Z Z' e)).map
      ((derivedPullback (incl Z)).map x)))
  have h₂ := (NatIso.isIso_map_iff
    (derivedPullbackCompIsoCanonical (resMap gY Z Z' e) (incl Z)) x).1 h₁
  exact (NatIso.isIso_map_iff (derivedPullbackCompIsoLeft (resMap gY Z Z' e) (incl Z') (incl Z)
    gY.toLRSHom.toShHom (resMap_comp gY Z Z' e)) x).2 h₂

/-- Two morphisms into `Rj_{Z'*} M` agree when they agree after precomposing with a morphism
that becomes invertible on restriction to `Z`, pulled back along `g_Y`. -/
private theorem eq_of_pullback_map_comp_eq
    (e : Z' ≤ gY ⁻¹ᵁ Z)
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))}
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'.toScheme.toSheafedSpace))}
    (x : A ⟶ B) (hx : IsIso ((derivedPullback (incl Z)).map x))
    (y z : (derivedPullback gY.toLRSHom.toShHom).obj B ⟶ (derivedPushforward (incl Z')).obj M)
    (h : (derivedPullback gY.toLRSHom.toShHom).map x ≫ y =
      (derivedPullback gY.toLRSHom.toShHom).map x ≫ z) : y = z := by
  apply hom_ext_of_derivedPullback
  have := isIso_derivedPullback_map_pullback_map gY Z Z' e x hx
  rw [← cancel_epi ((derivedPullback (incl Z')).map ((derivedPullback gY.toLRSHom.toShHom).map x)),
    ← Functor.map_comp, ← Functor.map_comp, h]

end Restriction

section Transition

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Y Y' : Scheme.{u}} (gY : Y' ⟶ Y) {Z₁ Z₂ : Y.Opens} {Z₁' Z₂' : Y'.Opens}
  (h : Z₂ ≤ Z₁) (h' : Z₂' ≤ Z₁') (e₁ : Z₁' ≤ gY ⁻¹ᵁ Z₁) (e₂ : Z₂' ≤ gY ⁻¹ᵁ Z₂)

/-- **The comparisons are compatible with the transitions.** -/
theorem pullback_map_transition_comp_restrictBaseChange
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback gY.toLRSHom.toShHom).map
        ((transition (inclLE h) (incl Z₁) (incl Z₂) (inclLE_comp h)).app K) ≫
        restrictBaseChange gY Z₂ Z₂' e₂ K K' φ =
      restrictBaseChange gY Z₁ Z₁' e₁ K K' φ ≫
        (transition (inclLE h') (incl Z₁') (incl Z₂') (inclLE_comp h')).app K' := by
  have hη := isIso_derivedPullback_map_unit_of_comp (inclLE h) (incl Z₁) (incl Z₂)
    (inclLE_comp h) K
  refine eq_of_pullback_map_comp_eq gY Z₂ Z₂' e₂ _ hη _ _ ?_
  exact transition_bookkeeping _ _ _ _ _ _ _ _
    (by rw [← CategoryTheory.Functor.map_comp, transition_app, unit_comp_transitionApp])
    (pullback_map_unit_comp_restrictBaseChange gY Z₂ Z₂' e₂ K K' φ)
    (pullback_map_unit_comp_restrictBaseChange gY Z₁ Z₁' e₁ K K' φ)
    (by rw [Category.assoc, transition_app, unit_comp_transitionApp])

end Transition

section Paste

/-- Invertibility is unchanged by pasting with isomorphisms. -/
theorem isIso_comp_iff_of_paste {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ Q₄ Q₅ : C}
    (x₁ : P₀ ⟶ P₁) (t : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (e : P₃ ⟶ P₄) (r : P₀ ⟶ P₄) (q : P₄ ⟶ Q₅)
    (b' : P₃ ⟶ Q₄) (e' : Q₄ ⟶ Q₅) (u : P₂ ⟶ Q₄) [IsIso x₁] [IsIso e']
    (h : x₁ ≫ t ≫ b ≫ e = r) (hn : e ≫ q = b' ≫ e') (hu : u = b ≫ b') :
    IsIso (t ≫ u) ↔ IsIso (r ≫ q) := by
  have hr : r ≫ q = x₁ ≫ (t ≫ u) ≫ e' := by
    rw [← h, hu]
    simp only [Category.assoc, hn]
  rw [hr, isIso_comp_left_iff x₁, isIso_comp_right_iff (t ≫ u) e']

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

variable {Y Y' S S' : Scheme.{u}} (fY : Y ⟶ S) (g : S' ⟶ S) (fY' : Y' ⟶ S') (gY : Y' ⟶ Y)
  (w : gY.toLRSHom.toShHom ≫ fY.toLRSHom.toShHom = fY'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
  (Z : Y.Opens) (Z' : Y'.Opens) (e : Z' ≤ gY ⁻¹ᵁ Z)

/-- **The composition over a restricted square.** For opens `Z ⊆ Y` and `Z' ⊆ g_Y^{-1}(Z)`, the
composition `Lg^*R(f|_Z)_*K|_Z ⟶ R(f'|_{Z'})_*K'|_{Z'}` for the square `Z' ⟶ Z` over `g`. -/
def rectComp (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward (incl Z ≫ fY.toLRSHom.toShHom)).obj
          ((derivedPullback (incl Z)).obj K)) ⟶
      (derivedPushforward (incl Z' ≫ fY'.toLRSHom.toShHom)).obj
        ((derivedPullback (incl Z')).obj K') :=
  derivedBaseChangeMap (resMap gY Z Z' e) (incl Z' ≫ fY'.toLRSHom.toShHom)
      (incl Z ≫ fY.toLRSHom.toShHom) g.toLRSHom.toShHom
      (comp_square _ _ _ _ _ _ _ (resMap_comp gY Z Z' e) w) ((derivedPullback (incl Z)).obj K) ≫
    (derivedPushforward (incl Z' ≫ fY'.toLRSHom.toShHom)).map (restrictDatum gY Z Z' e K K' φ)

/-- **Vertical pasting for the restricted comparison.** The comparison of the square at
`Rj_{Z*}K|_Z` followed by the pushforward of the comparison along the open immersions is
invertible exactly when the composition over the restricted square is. -/
theorem isIso_restrictBaseChange_iff
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    IsIso (derivedBaseChangeMap gY.toLRSHom.toShHom fY'.toLRSHom.toShHom fY.toLRSHom.toShHom
        g.toLRSHom.toShHom w ((restrictPush (incl Z)).obj K) ≫
        (derivedPushforward fY'.toLRSHom.toShHom).map (restrictBaseChange gY Z Z' e K K' φ)) ↔
      IsIso (rectComp fY g fY' gY w Z Z' e K K' φ) :=
  isIso_comp_iff_of_paste _ _ _ _ _ _ _ _ _
    (derivedBaseChangeMap_comp (resMap gY Z Z' e) (incl Z') (incl Z) gY.toLRSHom.toShHom
      fY'.toLRSHom.toShHom fY.toLRSHom.toShHom g.toLRSHom.toShHom (resMap_comp gY Z Z' e) w
      ((derivedPullback (incl Z)).obj K))
    ((derivedPushforwardCompIso (incl Z') fY'.toLRSHom.toShHom).hom.naturality
      (restrictDatum gY Z Z' e K K' φ)).symm
    ((derivedPushforward fY'.toLRSHom.toShHom).map_comp _ _)

end Paste

section Cover

/-- On the first leg, a completion of the comparisons agrees with any comparison making the
first transition square commute. -/
theorem comp_eq_of_comp_desc {C C' : Type*} [Category* C] [Category* C'] [Preadditive C]
    [Preadditive C'] (P : C ⥤ C') [P.Additive] {A B W : C} [HasBinaryBiproduct A B]
    {A' B' W' : C'} [HasBinaryBiproduct A' B'] (bA : P.obj A ⟶ A') (bB : P.obj B ⟶ B')
    (tA : A ⟶ W) (tB : B ⟶ W) (tA' : A' ⟶ W') (tB' : B' ⟶ W') (c c₀ : P.obj W ⟶ W')
    (hc : P.map (biprod.desc tA tB) ≫ c = coverMiddleMap P bA bB ≫ biprod.desc tA' tB')
    (h₀ : P.map tA ≫ c₀ = bA ≫ tA') : P.map tA ≫ c = P.map tA ≫ c₀ := by
  rw [h₀, ← biprod.inl_desc tA tB, P.map_comp, Category.assoc, hc, ← Category.assoc,
    map_inl_comp_coverMiddleMap, Category.assoc, biprod.inl_desc]

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange Stacks.Cohomology.DerivedMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard derivedPushforwardCommShift

variable {Y Y' S S' : Scheme.{u}} (fY : Y ⟶ S) (g : S' ⟶ S) (fY' : Y' ⟶ S') (gY : Y' ⟶ Y)
  (w : gY.toLRSHom.toShHom ≫ fY.toLRSHom.toShHom = fY'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
  (A B : Y.Opens)

/-- The comparison of the third vertices of the two Mayer--Vietoris triangles is forced: a
completion of the comparisons of the first two vertices is the base change along the inclusion
of the intersection. -/
theorem eq_restrictBaseChange_of_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K')
    (c : (derivedPullback gY.toLRSHom.toShHom).obj ((restrictPush (incl (A ⊓ B))).obj K) ⟶
      (restrictPush (incl (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B))).obj K')
    (hc : (derivedPullback gY.toLRSHom.toShHom).map
        (biprod.desc ((transitionFst A B).app K) (-(transitionSnd A B).app K)) ≫ c =
      coverMiddleMap (derivedPullback gY.toLRSHom.toShHom)
          (restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
          (restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ) ≫
        biprod.desc ((transitionFst (gY ⁻¹ᵁ A) (gY ⁻¹ᵁ B)).app K')
          (-(transitionSnd (gY ⁻¹ᵁ A) (gY ⁻¹ᵁ B)).app K')) :
    c = restrictBaseChange gY (A ⊓ B) (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B) le_rfl K K' φ := by
  have ht := isIso_derivedPullback_map_transitionApp (inclLE (inf_le_left : A ⊓ B ≤ A))
    (incl A) (incl (A ⊓ B)) (inclLE_comp _) K
  refine eq_of_pullback_map_comp_eq gY (A ⊓ B) (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B) le_rfl _ ht _ _ ?_
  exact comp_eq_of_comp_desc _ _ _ _ _ _ _ _ _ hc
    (pullback_map_transition_comp_restrictBaseChange gY (inf_le_left : A ⊓ B ≤ A)
      (inf_le_left : gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B ≤ gY ⁻¹ᵁ A) le_rfl le_rfl K K' φ)

/-- The base-change transformation of Stacks 08HY, `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`. -/
def bcNatTrans {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ T') (f : X ⟶ T)
    (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h) :
    (derivedPushforward f ⋙ derivedPullback h) ⟶ (derivedPullback g' ⋙ derivedPushforward f') :=
  derivedBaseChangeNatTrans g' f' f h sq

/-- The base-change transformation `bcNatTrans` commutes with the shift by `ℤ`. -/
instance {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ T') (f : X ⟶ T)
    (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h) : NatTrans.CommShift (bcNatTrans g' f' f h sq) ℤ :=
  commShift_derivedBaseChangeNatTrans g' f' f h sq

/-- The component of `bcNatTrans` at `K` is the derived base change map at `K`. -/
theorem bcNatTrans_app {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ T')
    (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (bcNatTrans g' f' f h sq).app K = derivedBaseChangeMap g' f' f h sq K := rfl

/-- `isIso_restrictBaseChange_iff` read at the component of the base-change transformation. -/
theorem isIso_app_restrictBaseChange_iff (Z : Y.Opens) (Z' : Y'.Opens) (e : Z' ≤ gY ⁻¹ᵁ Z)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    IsIso ((bcNatTrans gY.toLRSHom.toShHom fY'.toLRSHom.toShHom
        fY.toLRSHom.toShHom g.toLRSHom.toShHom w).app ((restrictPush (incl Z)).obj K) ≫
        (derivedPushforward fY'.toLRSHom.toShHom).map (restrictBaseChange gY Z Z' e K K' φ)) ↔
      IsIso (rectComp fY g fY' gY w Z Z' e K K' φ) :=
  isIso_restrictBaseChange_iff fY g fY' gY w Z Z' e K K' φ

/-- The derived pushforward along a morphism of ringed spaces is additive. -/
theorem additive_derivedPushforward {X T : RingedSpace.{u, u}} (f : X ⟶ T) :
    (derivedPushforward f).Additive := by
  have := derivedPushforward_isTriangulated f
  infer_instance

/-- The derived pullback along a morphism of ringed spaces is additive. -/
theorem additive_derivedPullback {X T : RingedSpace.{u, u}} (f : X ⟶ T) :
    (derivedPullback f).Additive :=
  inferInstance

/-- The derived pushforward along `f` followed by the derived pullback along `h` is additive. -/
theorem additive_derivedPushforward_comp {X T T' : RingedSpace.{u, u}} (f : X ⟶ T) (h : T' ⟶ T) :
    (derivedPushforward f ⋙ derivedPullback h).Additive := by
  have := additive_derivedPushforward f
  infer_instance

/-- The comparison at a biproduct is invertible when it is on both summands. -/
theorem isIso_bcNatTrans_coverMiddleMap {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ T') (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    {A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} [HasBinaryBiproduct A B]
    {A' B' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    [HasBinaryBiproduct A' B']
    (bA : (derivedPullback g').obj A ⟶ A') (bB : (derivedPullback g').obj B ⟶ B')
    (hA : IsIso ((bcNatTrans g' f' f h sq).app A ≫ (derivedPushforward f').map bA))
    (hB : IsIso ((bcNatTrans g' f' f h sq).app B ≫ (derivedPushforward f').map bB)) :
    IsIso ((bcNatTrans g' f' f h sq).app (A ⊞ B) ≫
      (derivedPushforward f').map (coverMiddleMap (derivedPullback g') bA bB)) := by
  have := additive_derivedPullback g'
  have := additive_derivedPushforward_comp f h
  have := additive_derivedPushforward f'
  exact isIso_comp_app_coverMiddleMap _ _ _ _ hA hB

/-- `isIso_comp_app_of_completion` for the base-change transformation. -/
theorem isIso_bcNatTrans_of_completion {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ T') (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    {T₁ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))}
    {T₂ : Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))}
    (hT : T₁ ∈ distTriang _) (hT' : T₂ ∈ distTriang _)
    (a : (derivedPullback g').obj T₁.obj₁ ⟶ T₂.obj₁)
    (b : (derivedPullback g').obj T₁.obj₂ ⟶ T₂.obj₂)
    (h₁ : (derivedPullback g').map T₁.mor₁ ≫ b = a ≫ T₂.mor₁)
    (hb : IsIso ((bcNatTrans g' f' f h sq).app T₁.obj₂ ≫ (derivedPushforward f').map b))
    (hc : ∀ c : (derivedPullback g').obj T₁.obj₃ ⟶ T₂.obj₃,
      (derivedPullback g').map T₁.mor₂ ≫ c = b ≫ T₂.mor₂ →
        IsIso ((bcNatTrans g' f' f h sq).app T₁.obj₃ ≫ (derivedPushforward f').map c)) :
    IsIso ((bcNatTrans g' f' f h sq).app T₁.obj₁ ≫ (derivedPushforward f').map a) := by
  have := derivedBaseChangeSource_isTriangulated f h
  have := derivedPushforward_isTriangulated f'
  exact isIso_comp_app_of_completion _ hT hT' a b h₁ hb hc

/-- `isIso_bcNatTrans_of_completion` for triangles given by their three morphisms. -/
theorem isIso_bcNatTrans_of_completion_mk {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ T') (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    {L M N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : L ⟶ M) (v : M ⟶ N) (d : N ⟶ L⟦(1 : ℤ)⟧)
    {L' M' N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (u' : L' ⟶ M') (v' : M' ⟶ N') (d' : N' ⟶ L'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u v d ∈ distTriang _) (hT' : Triangle.mk u' v' d' ∈ distTriang _)
    (a : (derivedPullback g').obj L ⟶ L') (b : (derivedPullback g').obj M ⟶ M')
    (h₁ : (derivedPullback g').map u ≫ b = a ≫ u')
    (hb : IsIso ((bcNatTrans g' f' f h sq).app M ≫ (derivedPushforward f').map b))
    (hc : ∀ c : (derivedPullback g').obj N ⟶ N',
      (derivedPullback g').map v ≫ c = b ≫ v' →
        IsIso ((bcNatTrans g' f' f h sq).app N ≫ (derivedPushforward f').map c)) :
    IsIso ((bcNatTrans g' f' f h sq).app L ≫ (derivedPushforward f').map a) := by
  have := derivedBaseChangeSource_isTriangulated f h
  have := derivedPushforward_isTriangulated f'
  exact isIso_comp_app_of_completion_mk _ u v d u' v' d' hT hT' a b h₁ hb hc

/-- The comparison at the middle vertex of the Mayer--Vietoris triangles. -/
theorem isIso_cover_middle
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K')
    (hA : IsIso (rectComp fY g fY' gY w A (gY ⁻¹ᵁ A) le_rfl K K' φ))
    (hB : IsIso (rectComp fY g fY' gY w B (gY ⁻¹ᵁ B) le_rfl K K' φ)) :
    IsIso ((bcNatTrans gY.toLRSHom.toShHom fY'.toLRSHom.toShHom
        fY.toLRSHom.toShHom g.toLRSHom.toShHom w).app
          ((restrictPush (incl A)).obj K ⊞ (restrictPush (incl B)).obj K) ≫
        (derivedPushforward fY'.toLRSHom.toShHom).map
          (coverMiddleMap (derivedPullback gY.toLRSHom.toShHom)
            (restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
            (restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ))) :=
  isIso_bcNatTrans_coverMiddleMap _ _ _ _ _ _ _
    ((isIso_app_restrictBaseChange_iff fY g fY' gY w A (gY ⁻¹ᵁ A) le_rfl K K' φ).2 hA)
    ((isIso_app_restrictBaseChange_iff fY g fY' gY w B (gY ⁻¹ᵁ B) le_rfl K K' φ).2 hB)

/-- The comparison at the third vertex of the Mayer--Vietoris triangles. -/
theorem isIso_cover_third
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K')
    (hW : IsIso (rectComp fY g fY' gY w (A ⊓ B) (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B) le_rfl K K' φ))
    (c : (derivedPullback gY.toLRSHom.toShHom).obj ((restrictPush (incl (A ⊓ B))).obj K) ⟶
      (restrictPush (incl (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B))).obj K')
    (hc : (derivedPullback gY.toLRSHom.toShHom).map
        (biprod.desc ((transitionFst A B).app K) (-(transitionSnd A B).app K)) ≫ c =
      coverMiddleMap (derivedPullback gY.toLRSHom.toShHom)
          (restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
          (restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ) ≫
        biprod.desc ((transitionFst (gY ⁻¹ᵁ A) (gY ⁻¹ᵁ B)).app K')
          (-(transitionSnd (gY ⁻¹ᵁ A) (gY ⁻¹ᵁ B)).app K')) :
    IsIso ((bcNatTrans gY.toLRSHom.toShHom fY'.toLRSHom.toShHom
        fY.toLRSHom.toShHom g.toLRSHom.toShHom w).app ((restrictPush (incl (A ⊓ B))).obj K) ≫
        (derivedPushforward fY'.toLRSHom.toShHom).map c) := by
  rw [eq_restrictBaseChange_of_comp gY A B K K' φ c hc]
  exact (isIso_app_restrictBaseChange_iff fY g fY' gY w (A ⊓ B) (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B)
    le_rfl K K' φ).2 hW

/-- The comparison of the first maps of the Mayer--Vietoris triangles. -/
theorem cover_first_square
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K') :
    (derivedPullback gY.toLRSHom.toShHom).map
        (biprod.lift ((unit (incl A)).app K) ((unit (incl B)).app K) : K ⟶ _) ≫
      coverMiddleMap (derivedPullback gY.toLRSHom.toShHom)
          (restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
          (restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ) =
      φ ≫ (biprod.lift ((unit (incl (gY ⁻¹ᵁ A))).app K') ((unit (incl (gY ⁻¹ᵁ B))).app K') :
        K' ⟶ _) :=
  coverSquare_one _ _ _ _ _ _ _ _
    (pullback_map_unit_comp_restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
    (pullback_map_unit_comp_restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ)

/-- The Mayer--Vietoris ladder for the base-change transformation, with the comparison of the
middle vertices assembled from the comparisons on the two legs of the cover. -/
theorem isIso_bcNatTrans_of_cover {X' X T' T : RingedSpace.{u, u}} (g' : X' ⟶ X)
    (f' : X' ⟶ T') (f : X ⟶ T) (h : T' ⟶ T) (sq : g' ≫ f = f' ≫ h)
    {L A B N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    [HasBinaryBiproduct A B]
    (rA : L ⟶ A) (rB : L ⟶ B) (v : A ⊞ B ⟶ N) (d : N ⟶ L⟦(1 : ℤ)⟧)
    {L' A' B' N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    [HasBinaryBiproduct A' B']
    (rA' : L' ⟶ A') (rB' : L' ⟶ B') (v' : A' ⊞ B' ⟶ N') (d' : N' ⟶ L'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift rA rB) v d ∈ distTriang _)
    (hT' : Triangle.mk (biprod.lift rA' rB') v' d' ∈ distTriang _)
    (a : (derivedPullback g').obj L ⟶ L') (bA : (derivedPullback g').obj A ⟶ A')
    (bB : (derivedPullback g').obj B ⟶ B')
    (hrA : (derivedPullback g').map rA ≫ bA = a ≫ rA')
    (hrB : (derivedPullback g').map rB ≫ bB = a ≫ rB')
    (hA : IsIso ((bcNatTrans g' f' f h sq).app A ≫ (derivedPushforward f').map bA))
    (hB : IsIso ((bcNatTrans g' f' f h sq).app B ≫ (derivedPushforward f').map bB))
    (hc : ∀ c : (derivedPullback g').obj N ⟶ N',
      (derivedPullback g').map v ≫ c = coverMiddleMap (derivedPullback g') bA bB ≫ v' →
        IsIso ((bcNatTrans g' f' f h sq).app N ≫ (derivedPushforward f').map c)) :
    IsIso ((bcNatTrans g' f' f h sq).app L ≫ (derivedPushforward f').map a) :=
  isIso_bcNatTrans_of_completion_mk g' f' f h sq _ v d _ v' d' hT hT' a
    (coverMiddleMap (derivedPullback g') bA bB)
    (coverSquare_one _ _ _ _ _ _ _ _ hrA hrB)
    (isIso_bcNatTrans_coverMiddleMap g' f' f h sq bA bB hA hB) hc

/-- The Mayer--Vietoris triangle of a cover by two opens, with the units as first map. -/
theorem exists_distinguished_mvTri {Z : Scheme.{u}} (A₀ B₀ : Z.Opens) (hAB : A₀ ⊔ B₀ = ⊤)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace))) :
    ∃ δ : (restrictPush (incl (A₀ ⊓ B₀))).obj K ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift ((unit (incl A₀)).app K) ((unit (incl B₀)).app K) :
          K ⟶ (restrictPush (incl A₀)).obj K ⊞ (restrictPush (incl B₀)).obj K)
        (biprod.desc ((transitionFst A₀ B₀).app K) (-(transitionSnd A₀ B₀).app K)) δ ∈
          distTriang _ :=
  exists_distinguished_mvTriangle A₀ B₀ hAB K

/-- **The Mayer--Vietoris step.** For a cover `Y = A ∪ B` and the preimages `A'`, `B'` in `Y'`,
the composition `Lg^*Rf_*K ⟶ Rf'_*L(g_Y)^*K ⟶ Rf'_*K'` is invertible as soon as the compositions
over the restricted squares on `A`, `B` and `A ∩ B` are. -/
theorem isIso_of_cover (hAB : A ⊔ B = ⊤)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'.toSheafedSpace)))
    (φ : (derivedPullback gY.toLRSHom.toShHom).obj K ⟶ K')
    (hA : IsIso (rectComp fY g fY' gY w A (gY ⁻¹ᵁ A) le_rfl K K' φ))
    (hB : IsIso (rectComp fY g fY' gY w B (gY ⁻¹ᵁ B) le_rfl K K' φ))
    (hW : IsIso (rectComp fY g fY' gY w (A ⊓ B) (gY ⁻¹ᵁ A ⊓ gY ⁻¹ᵁ B) le_rfl K K' φ)) :
    IsIso ((bcNatTrans gY.toLRSHom.toShHom fY'.toLRSHom.toShHom fY.toLRSHom.toShHom
        g.toLRSHom.toShHom w).app K ≫ (derivedPushforward fY'.toLRSHom.toShHom).map φ) := by
  obtain ⟨δ, hT⟩ := exists_distinguished_mvTri A B hAB K
  have hAB' : gY ⁻¹ᵁ A ⊔ gY ⁻¹ᵁ B = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hAB, Scheme.Hom.preimage_top]
  obtain ⟨δ', hT'⟩ := exists_distinguished_mvTri (gY ⁻¹ᵁ A) (gY ⁻¹ᵁ B) hAB' K'
  exact isIso_bcNatTrans_of_cover _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' φ
    (restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
    (restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ)
    (pullback_map_unit_comp_restrictBaseChange gY A (gY ⁻¹ᵁ A) le_rfl K K' φ)
    (pullback_map_unit_comp_restrictBaseChange gY B (gY ⁻¹ᵁ B) le_rfl K K' φ)
    ((isIso_app_restrictBaseChange_iff fY g fY' gY w A (gY ⁻¹ᵁ A) le_rfl K K' φ).2 hA)
    ((isIso_app_restrictBaseChange_iff fY g fY' gY w B (gY ⁻¹ᵁ B) le_rfl K K' φ).2 hB)
    (isIso_cover_third fY g fY' gY w A B K K' φ hW)

end Cover

end Stacks.Cohomology.BaseChangeCover

end
