module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Two morphisms of topoi agreeing on representable sheaves are 2-isomorphic

Let `(C, J)` and `(D, K)` be sites with `K` subcanonical, so that every object `V` of `D` has a
representable sheaf `h_V = K.yoneda.obj V` on `D`, and let

```
  f, g : Sh(C) ⟶ Sh(D)
```

be morphisms of topoi.  Yoneda and the adjunction `f⁻¹ ⊣ f_*` identify the sections of `f_*F`
over `V` with the maps `f⁻¹h_V ⟶ F`:

`Γ(V, f_*F) ≃ Mor_{Sh(D)}(h_V, f_*F) ≃ Mor_{Sh(C)}(f⁻¹h_V, F)`.

Consequently an isomorphism `f⁻¹h_V ≅ g⁻¹h_V`, natural in `V`, gives an isomorphism
`Γ(V, f_*F) ≅ Γ(V, g_*F)` natural in both `V` and `F`, hence — the inclusion of sheaves into
presheaves being fully faithful — an isomorphism `f_* ≅ g_*` of the direct image functors.  That
is `MorphismOfTopoi.pushforwardIsoOfInverseImageYonedaIso`.

The comparison `f⁻¹h_V ≅ g⁻¹h_V` is in practice available only for `V` in a *subcategory* of
`D`: in the proof of [Stacks Project, Tag 04I6] it is constructed for the affine objects of the
small étale site, which form a dense subsite by [Stacks Project, Tag 04HR].  So the main
statement is the one indexed by an arbitrary continuous functor `ι : (D', K') ⥤ (D, K)`, which
concludes `f_* ≅ g_*` as soon as restriction of sheaves along `ι` is fully faithful — and that
is exactly what being a dense subsite provides, by
`CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` and its faithful
companion.  The version over all of `D` is the case `ι = 𝟭 D`, where restriction is the
inclusion of sheaves into presheaves and the full faithfulness is automatic.

## Main definitions

* `MorphismOfTopoi.sectionsEquiv` — the identification
  `Mor(f⁻¹h_V, F) ≃ Γ(V, f_*F)`.
* `MorphismOfTopoi.sectionsCompare` — the bijection `Γ(ι V, f_*F) ≃
  Γ(ι V, g_*F)` induced by a comparison `f⁻¹h_{ι •} ≅ g⁻¹h_{ι •}`.
* `MorphismOfTopoi.restrictedPushforwardIso` — those bijections assembled into
  an isomorphism of the two direct image functors followed by restriction to `D'`.

## Main results

* `MorphismOfTopoi.pushforwardIsoOfInverseImageYonedaIsoOfRestriction` — the
  statement over a subsite `ι : (D', K') ⥤ (D, K)` along which restriction of sheaves is fully
  faithful: a comparison of the inverse images of the representable sheaves of the objects
  `ι V` gives `f_* ≅ g_*`.
* `MorphismOfTopoi.pushforwardIsoOfInverseImageYonedaIso` — the same with no
  subcategory and no hypothesis: a comparison over all of `D` gives `f_* ≅ g_*`.

## Implementation notes

The identification `Mor(f⁻¹h_V, F) ≃ Γ(V, f_*F)` and its two naturalities appear, for the
*sheafified* Yoneda embedding `Sheaf.sheafifiedYoneda` and at the universe `Type (max u v)` of
the objects of the site, inside the proof of [Stacks Project, Tag 03A2] in
`StacksFrontier/CategoryTheory/Sites/Topos/MorphismsOfTopoi.lean` (the private `natB` there).  That
one is not usable here: it is private, and its universe is wrong for the small étale site, whose
objects live one universe above its sheaves of sets.  The version below is for a *subcanonical*
topology, where no sheafification is needed and `K.yoneda` and the sheaves of sets live in the
universe of the morphisms of the site — which is the configuration of the small étale site.

Nothing here produces the comparison `f⁻¹h_V ≅ g⁻¹h_V`; it is the input.  For Stacks 04I6 that
comparison is the isomorphism `g⁻¹h_V ≅ h_{X ×_Y V}` of the source's step (3), checked on
stalks, and this file is its step (6).

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u₁ u₂ u₃

namespace MorphismOfTopoi

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v} D] {K : GrothendieckTopology D} [K.Subcanonical]

section Sections

variable (f : MorphismOfTopoi (Sheaf J (Type v)) (Sheaf K (Type v)))

/-- **Sections of a direct image are maps out of the inverse image of a representable.**  For a
morphism of topoi `f : Sh(C) ⟶ Sh(D)` with `K` subcanonical, the sections of `f_*F` over an
object `V` of `D` are the maps `f⁻¹h_V ⟶ F`: compose the adjunction `f⁻¹ ⊣ f_*` with Yoneda for
sheaves on `D`. -/
def sectionsEquiv (F : Sheaf J (Type v)) (V : D) :
    (f.inverseImage.obj (K.yoneda.obj V) ⟶ F) ≃ (f.pushforward.obj F).obj.obj (op V) :=
  (f.adj.homEquiv (K.yoneda.obj V) F).trans K.yonedaEquiv

/-- `MorphismOfTopoi.sectionsEquiv` is natural in the object of `D`:
restricting a section along `k : V' ⟶ V` precomposes the corresponding map with `f⁻¹h_k`. -/
theorem sectionsEquiv_map (F : Sheaf J (Type v)) {V V' : D} (k : V' ⟶ V)
    (φ : f.inverseImage.obj (K.yoneda.obj V) ⟶ F) :
    (f.pushforward.obj F).obj.map k.op (f.sectionsEquiv F V φ) =
      f.sectionsEquiv F V' (f.inverseImage.map (K.yoneda.map k) ≫ φ) := by
  simp only [sectionsEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left]
  exact K.yonedaEquiv_naturality _ _

/-- `MorphismOfTopoi.sectionsEquiv` is natural in the sheaf on `C`: the action
of `ψ : F ⟶ F'` on sections of the direct image is postcomposition with `ψ`. -/
theorem sectionsEquiv_comp {F F' : Sheaf J (Type v)} (ψ : F ⟶ F') (V : D)
    (φ : f.inverseImage.obj (K.yoneda.obj V) ⟶ F) :
    (f.pushforward.map ψ).hom.app (op V) (f.sectionsEquiv F V φ) =
      f.sectionsEquiv F' V (φ ≫ ψ) := by
  simp only [sectionsEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  exact (K.yonedaEquiv_comp _ _).symm

end Sections

section Comparison

variable {D' : Type u₃} [Category.{v} D'] (ι : D' ⥤ D)
  {f g : MorphismOfTopoi (Sheaf J (Type v)) (Sheaf K (Type v))}
  (e : (ι ⋙ K.yoneda) ⋙ f.inverseImage ≅ (ι ⋙ K.yoneda) ⋙ g.inverseImage)

/-- **The comparison of sections attached to a comparison of inverse images of representables.**
A comparison `f⁻¹h_{ι V} ≅ g⁻¹h_{ι V}` carries the sections of `f_*F` over `ι V` bijectively
onto those of `g_*F`, by `MorphismOfTopoi.sectionsEquiv` on both sides. -/
def sectionsCompare (F : Sheaf J (Type v)) (V : D') :
    (f.pushforward.obj F).obj.obj (op (ι.obj V)) ≃
      (g.pushforward.obj F).obj.obj (op (ι.obj V)) where
  toFun a := g.sectionsEquiv F (ι.obj V) (e.inv.app V ≫ (f.sectionsEquiv F (ι.obj V)).symm a)
  invFun b := f.sectionsEquiv F (ι.obj V) (e.hom.app V ≫ (g.sectionsEquiv F (ι.obj V)).symm b)
  left_inv a := by
    simp only [Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.id_comp, Equiv.apply_symm_apply]
  right_inv b := by
    simp only [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
      Category.id_comp, Equiv.apply_symm_apply]

/-- `MorphismOfTopoi.sectionsCompare` read on the map `f⁻¹h_{ι V} ⟶ F` naming a
section: it is precomposition with the comparison. -/
theorem sectionsCompare_apply (F : Sheaf J (Type v)) (V : D')
    (φ : f.inverseImage.obj (K.yoneda.obj (ι.obj V)) ⟶ F) :
    sectionsCompare ι e F V (f.sectionsEquiv F (ι.obj V) φ) =
      g.sectionsEquiv F (ι.obj V) (e.inv.app V ≫ φ) := by
  show g.sectionsEquiv F (ι.obj V) (e.inv.app V ≫ (f.sectionsEquiv F (ι.obj V)).symm
    (f.sectionsEquiv F (ι.obj V) φ)) = _
  rw [Equiv.symm_apply_apply]

/-- **The comparison of sections is natural in the object of `D'`.**  This is naturality of the
given comparison of inverse images, read through
`MorphismOfTopoi.sectionsEquiv`. -/
theorem sectionsCompare_map (F : Sheaf J (Type v)) {V V' : D'} (k : V' ⟶ V)
    (a : (f.pushforward.obj F).obj.obj (op (ι.obj V))) :
    sectionsCompare ι e F V' ((f.pushforward.obj F).obj.map (ι.map k).op a) =
      (g.pushforward.obj F).obj.map (ι.map k).op (sectionsCompare ι e F V a) := by
  obtain ⟨φ, rfl⟩ := (f.sectionsEquiv F (ι.obj V)).surjective a
  have hnat : e.inv.app V' ≫ f.inverseImage.map (K.yoneda.map (ι.map k)) =
      g.inverseImage.map (K.yoneda.map (ι.map k)) ≫ e.inv.app V := (e.inv.naturality k).symm
  rw [f.sectionsEquiv_map, sectionsCompare_apply, sectionsCompare_apply, g.sectionsEquiv_map]
  refine congrArg (g.sectionsEquiv F (ι.obj V')) ?_
  rw [← Category.assoc, ← Category.assoc, hnat]

/-- **The comparison of sections is natural in the sheaf on `C`.** -/
theorem sectionsCompare_naturality {F F' : Sheaf J (Type v)} (ψ : F ⟶ F') (V : D')
    (a : (f.pushforward.obj F).obj.obj (op (ι.obj V))) :
    sectionsCompare ι e F' V ((f.pushforward.map ψ).hom.app (op (ι.obj V)) a) =
      (g.pushforward.map ψ).hom.app (op (ι.obj V)) (sectionsCompare ι e F V a) := by
  obtain ⟨φ, rfl⟩ := (f.sectionsEquiv F (ι.obj V)).surjective a
  rw [f.sectionsEquiv_comp, sectionsCompare_apply, sectionsCompare_apply, g.sectionsEquiv_comp]
  exact congrArg (g.sectionsEquiv F' (ι.obj V)) (Category.assoc _ _ _).symm

/-- **The two direct image functors agree after restriction to `(D', K')`.**  The bijections of
`MorphismOfTopoi.sectionsCompare`, assembled over all objects of `D'` and all sheaves on `C`,
and read through the underlying presheaves of the restricted sheaves. -/
def restrictedPushforwardIso (K' : GrothendieckTopology D') [ι.IsContinuous K' K] :
    f.pushforward ⋙ ι.sheafPushforwardContinuous (Type v) K' K ⋙
        sheafToPresheaf K' (Type v) ≅
      g.pushforward ⋙ ι.sheafPushforwardContinuous (Type v) K' K ⋙
        sheafToPresheaf K' (Type v) :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents (fun V => Equiv.toIso (sectionsCompare ι e F V.unop))
      (by
        intro V V' m
        ext a
        exact sectionsCompare_map ι e F m.unop a))
    (by
      intro F F' ψ
      ext V a
      exact sectionsCompare_naturality ι e ψ V.unop a)

include e in
/-- **Two morphisms of topoi whose inverse images agree on the representable sheaves of a
subcategory along which sheaves are determined have isomorphic direct images.**  The hypothesis
on `ι : (D', K') ⥤ (D, K)` is that restriction of sheaves along `ι` be fully faithful, which is
what [Stacks Project, Tag 04HR] provides for the affine objects of the small étale site.

This is step (6) of the proof of [Stacks Project, Tag 04I6]: there `f` is the morphism of topoi
of a morphism of schemes, `g` the given morphism of topoi, and the comparison is the
isomorphism `g⁻¹h_V ≅ h_{X ×_Y V}` for affine `V` étale over `Y`. -/
def pushforwardIsoOfInverseImageYonedaIsoOfRestriction (K' : GrothendieckTopology D')
    [ι.IsContinuous K' K]
    [(ι.sheafPushforwardContinuous (Type v) K' K).Full]
    [(ι.sheafPushforwardContinuous (Type v) K' K).Faithful] :
    f.pushforward ≅ g.pushforward :=
  have := (fullyFaithfulSheafToPresheaf K' (Type v)).full
  have := (fullyFaithfulSheafToPresheaf K' (Type v)).faithful
  Functor.fullyFaithfulCancelRight
    (ι.sheafPushforwardContinuous (Type v) K' K ⋙ sheafToPresheaf K' (Type v))
    (restrictedPushforwardIso ι e K')

end Comparison

/-- **Two morphisms of topoi whose inverse images agree on all representable sheaves have
isomorphic direct images.**  For a subcanonical topology on `D` the sections of `f_*F` over `V`
are the maps `f⁻¹h_V ⟶ F`, so an isomorphism `f⁻¹h_V ≅ g⁻¹h_V` natural in `V` is an isomorphism
of the two direct images on sections, hence of the two direct images.

No hypothesis beyond subcanonicality of `K` is needed; the inclusion of sheaves into presheaves
is always fully faithful. -/
def pushforwardIsoOfInverseImageYonedaIso
    {f g : MorphismOfTopoi (Sheaf J (Type v)) (Sheaf K (Type v))}
    (e : K.yoneda ⋙ f.inverseImage ≅ K.yoneda ⋙ g.inverseImage) :
    f.pushforward ≅ g.pushforward :=
  have := (fullyFaithfulSheafToPresheaf K (Type v)).full
  have := (fullyFaithfulSheafToPresheaf K (Type v)).faithful
  Functor.fullyFaithfulCancelRight (sheafToPresheaf K (Type v))
    (NatIso.ofComponents
      (fun F => NatIso.ofComponents
        (fun V => Equiv.toIso (sectionsCompare (𝟭 D) e F V.unop))
        (by
          intro V V' m
          ext a
          exact sectionsCompare_map (𝟭 D) e F m.unop a))
      (by
        intro F F' ψ
        ext V a
        exact sectionsCompare_naturality (𝟭 D) e ψ V.unop a))

end MorphismOfTopoi

end
