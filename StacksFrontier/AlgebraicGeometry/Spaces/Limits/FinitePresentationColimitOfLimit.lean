module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalRingGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing

/-!
# Algebraic spaces of finite presentation over the vertex of a limit cone of the site

Let `W : I ⥤ BigFppfOver B S hS` be a cofiltered system of objects of the big fppf site of `S`
and let `p i : M ⟶ W i` be a cone over it whose image under the Yoneda embedding is a limit cone
of presheaves. When the system of represented presheaves satisfies the hypotheses of Stacks 07SK
— affine transitions, quasi-compact and quasi-separated stages — base change along the cone
exhibits the category `FP_M` of algebraic spaces of finite presentation over `M` as the filtered
`2`-colimit of the categories `FP_{W i}`, in the elementary form
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing`.

The size hypotheses are the cofinality-free ones of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent`: fewer stages than the
cutoff of the site, morphism types bounded by one cardinal below the cutoff, and uniformly bounded
base changes. They hold for the inverse systems of affine neighbourhoods of a point that present
the spectra of local and henselian local rings, whose number may exceed the cofinality of the
cutoff.

## Main definitions

* `AlgebraicGeometry.FinitePresentationSpacesOver.yonedaCone`: the cone of represented presheaves
  attached to a cone of the site.

## Main results

* `AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_of_isLimit`:
  **Stacks 07SK in the form of a filtered `2`-colimit over the vertex of a limit cone of the
  site.**
* `AlgebraicGeometry.FinitePresentationSpacesOver.exists_isIso_baseChange_map_of_isLimit`:
  a morphism of algebraic spaces of finite presentation over a stage which becomes an
  isomorphism over the vertex is an isomorphism over a later stage.

## Implementation notes

Stacks 07SK is stated in `FinitePresentationDescent` over the chosen limit `limit (W ⋙ yoneda)`
of presheaves. The vertex `yoneda M` is identified with it by the uniqueness of limits, and base
change along `yoneda (p i)` with base change along the limit projection followed by base change
along that identification, which is an equivalence of slice categories because it is the right
adjoint of the equivalence `Over.map` along an isomorphism. The comparison isomorphisms that
`IsFinitePresentationColimit` refers to are the pinned ones of
`CategoryTheory.Over.pullbackFactorObjIso`; that they match the comparisons produced by
Stacks 07SK is checked on the projections of the iterated fibre products.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C]

/-- Base change along an isomorphism is an equivalence of slice categories: it is right adjoint
to `Over.map` along that isomorphism, which is an equivalence. -/
instance isEquivalence_pullback_hom {P L : C} (e : P ≅ L) : (Over.pullback e.hom).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((Over.mapPullbackAdj e.hom).rightAdjointUniq (Over.mapIso e).toAdjunction).symm

end CategoryTheory.Over

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The cone of represented presheaves attached to a cone `p i : M ⟶ W i` of the big fppf site
of `S`. -/
@[simps]
def yonedaCone {I : Type u} [Category.{u} I] (W : I ⥤ BigFppfOver B S hS)
    (M : BigFppfOver B S hS) (p : (i : I) → (M ⟶ W.obj i))
    (hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i) : Cone (W ⋙ yoneda) where
  pt := yoneda.obj M
  π :=
    { app := fun i => yoneda.map (p i)
      naturality := fun i j e => by
        simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
          Category.id_comp, Functor.comp_map, ← Functor.map_comp, hp] }

section Limit

variable {B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I] {W : I ⥤ BigFppfOver B S hS}
  {M : BigFppfOver B S hS} {p : (i : I) → (M ⟶ W.obj i)}
  {hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i}
  (hlim : IsLimit (yonedaCone B S hS W M p hp))

/-- The vertex of the cone is the chosen limit of the represented presheaves. -/
def limitIso : yoneda.obj M ≅ limit (W ⋙ yoneda) :=
  hlim.conePointUniqueUpToIso (limit.isLimit _)

omit [IsCofiltered I] in
/-- The identification `limitIso` of the vertex with the limit commutes with the projections:
followed by the limit projection at `i` it is the represented cone map `yoneda.map (p i)`. -/
@[reassoc (attr := simp)]
theorem limitIso_hom_π (i : I) :
    (limitIso hlim).hom ≫ limit.π (W ⋙ yoneda) i = yoneda.map (p i) :=
  hlim.conePointUniqueUpToIso_hom_comp (limit.isLimit _) i

/-- Base change along `yoneda (p i)` is base change along the limit projection followed by base
change along the identification of the vertex with the limit. -/
def baseChangeLimitIso (i : I) :
    Over.pullback (yoneda.map (p i)) ≅
      Over.pullback (limit.π (W ⋙ yoneda) i) ⋙ Over.pullback (limitIso hlim).hom :=
  Over.pullbackFactorIso (limitIso_hom_π hlim i)

omit [IsCofiltered I] in
/-- **The cocycle of the comparison isomorphisms.** The comparison of a factorisation of a cone
map, followed by the identification of the base change along the later cone map with a base change
along the limit, is the comparison produced by Stacks 07SK. -/
theorem baseChangeLimitIso_cocycle {i j : I} (e : j ⟶ i)
    (X : Over (yoneda.obj (W.obj i)))
    (α : (Over.pullback (limit.π (W ⋙ yoneda) j)).obj
        ((Over.pullback ((W ⋙ yoneda).map e)).obj X) ≅
      (Over.pullback (limit.π (W ⋙ yoneda) i)).obj X)
    (hα : α.hom.left ≫ pullback.fst X.hom (limit.π (W ⋙ yoneda) i) =
      pullback.fst ((Over.pullback ((W ⋙ yoneda).map e)).obj X).hom
          (limit.π (W ⋙ yoneda) j) ≫ pullback.fst X.hom ((W ⋙ yoneda).map e)) :
    (Over.pullbackFactorIso (a := yoneda.map (p j)) (b := (W ⋙ yoneda).map e)
        (c := yoneda.map (p i)) (by rw [Functor.comp_map, ← Functor.map_comp, hp e])).hom.app X ≫
      (baseChangeLimitIso hlim j).hom.app ((Over.pullback ((W ⋙ yoneda).map e)).obj X) ≫
        (Over.pullback (limitIso hlim).hom).map α.hom =
      (baseChangeLimitIso hlim i).hom.app X := by
  have key : ∀ {A : Over (yoneda.obj M)}
      (u v : A ⟶ (Over.pullback (limitIso hlim).hom).obj
        ((Over.pullback (limit.π (W ⋙ yoneda) i)).obj X)),
      u.left ≫ pullback.fst (pullback.snd X.hom (limit.π (W ⋙ yoneda) i)) (limitIso hlim).hom ≫
          pullback.fst X.hom (limit.π (W ⋙ yoneda) i) =
        v.left ≫ pullback.fst (pullback.snd X.hom (limit.π (W ⋙ yoneda) i)) (limitIso hlim).hom ≫
          pullback.fst X.hom (limit.π (W ⋙ yoneda) i) → u = v := by
    intro A u v h
    have hu := Over.w u
    have hv := Over.w v
    simp only [Over.pullback_obj_hom] at hu hv
    have hc : pullback.fst (pullback.snd X.hom (limit.π (W ⋙ yoneda) i)) (limitIso hlim).hom ≫
          pullback.snd X.hom (limit.π (W ⋙ yoneda) i) =
        pullback.snd (pullback.snd X.hom (limit.π (W ⋙ yoneda) i)) (limitIso hlim).hom ≫
          (limitIso hlim).hom := pullback.condition
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · exact h
      · simp only [Over.pullback_obj_hom, Category.assoc]
        rw [hc, ← Category.assoc, ← Category.assoc, hu, hv]
    · simp only [Over.pullback_obj_hom]
      rw [hu, hv]
  apply key
  simp only [baseChangeLimitIso, Over.pullbackFactorIso_hom_app, Over.comp_left,
    Category.assoc, Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc,
    Over.pullbackFactorObjIso_hom_left_fst]
  rw [hα]
  simp only [Over.pullbackFactorObjIso_hom_left_fst_pullback_obj_assoc,
    Over.pullbackFactorObjIso_hom_left_fst, Over.pullback_obj_hom]

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  (hAffine : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS ((W ⋙ yoneda).map f))
  (hQc : ∀ i, Space.IsQuasiCompactSpace B S hS ((W ⋙ yoneda).obj i))
  (hQs : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS hZ ((W ⋙ yoneda).obj i))
  {ν : Cardinal.{u}} (hSizeB : Cardinal.mk I < B.cutoff) (hν : ν < B.cutoff)
  (hHomSizeB : ∀ i j : I, Cardinal.mk (i ⟶ j) ≤ ν)
  (hB : Space.BaseChangeSizeBounded B S hS (W ⋙ yoneda))

include hlim hAffine hQc hQs hSizeB hν hHomSizeB hB

omit hQs in
/-- **Faithfulness.** Two morphisms over a stage whose base changes to the vertex agree already
agree over a later stage. -/
theorem faithful_of_isLimit (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
    (f g : X ⟶ Y) (h : (baseChange B S hS (p i)).map f = (baseChange B S hS (p i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (baseChange B S hS (W.map e)).map f = (baseChange B S hS (W.map e)).map g := by
  have h₁ : (Over.pullback (yoneda.map (p i))).map f.hom =
      (Over.pullback (yoneda.map (p i))).map g.hom :=
    congrArg (fun k => (ObjectProperty.ι _).map k) h
  have h₂ : (Over.pullback (limitIso hlim).hom).map
        ((Over.pullback (limit.π (W ⋙ yoneda) i)).map f.hom) =
      (Over.pullback (limitIso hlim).hom).map
        ((Over.pullback (limit.π (W ⋙ yoneda) i)).map g.hom) := by
    have hf := (baseChangeLimitIso hlim i).hom.naturality f.hom
    have hg := (baseChangeLimitIso hlim i).hom.naturality g.hom
    simp only [Functor.comp_map] at hf hg
    rw [← Iso.cancel_iso_hom_left ((baseChangeLimitIso hlim i).app X.obj), Iso.app_hom, ← hf,
      ← hg, h₁]
  have h₃ := (Over.pullback (limitIso hlim).hom).map_injective h₂
  obtain ⟨j, e, he⟩ := Space.eventually_eq_of_baseChange_eq_of_baseChangeSizeBounded B S hS
    (W ⋙ yoneda) (fun i => isAlgebraicSpace_yoneda B S hS (W.obj i)) hAffine hQc hSizeB hν
    hHomSizeB hB i X.obj Y.obj X.property.1 Y.property.1 X.property.2 Y.property.2 f.hom g.hom h₃
  exact ⟨j, e, ObjectProperty.hom_ext _ he⟩

/-- **Essential surjectivity.** Every algebraic space of finite presentation over the vertex is,
up to isomorphism, the base change of one over a stage. -/
theorem essSurj_of_isLimit (Y : FinitePresentationSpacesOver B S hS M) :
    ∃ (i : I) (Yi : FinitePresentationSpacesOver B S hS (W.obj i)),
      Nonempty ((baseChange B S hS (p i)).obj Yi ≅ Y) := by
  let e := limitIso hlim
  have hL : IsAlgebraicSpace B S hS (limit (W ⋙ yoneda)) :=
    Space.isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS (W ⋙ yoneda) hSizeB hν
      hHomSizeB (fun i => isAlgebraicSpace_yoneda B S hS (W.obj i)) hAffine hB
  let Y' := (Over.pullback e.inv).obj Y.obj
  have hY' : IsAlgebraicSpace B S hS Y'.left :=
    isAlgebraicSpace_pullback B S hS Y.obj.hom e.inv Y.property.1 hL
      (isAlgebraicSpace_yoneda B S hS M)
  have hY'fp : Space.IsFinitePresentation B S hS Y'.hom :=
    Space.isFinitePresentation_pullback_snd B S hS Y.obj.hom e.inv Y.property.1
      (isAlgebraicSpace_yoneda B S hS M) hL Y.property.2
  obtain ⟨i, Yi, hYi, hYifp, ⟨ψ⟩⟩ :=
    Space.exists_model_of_finitePresentation_of_baseChangeSizeBounded B S hS hZ (W ⋙ yoneda)
      (fun i => isAlgebraicSpace_yoneda B S hS (W.obj i)) hAffine hQc hQs hSizeB hν hHomSizeB
      hB Y' hY' hY'fp
  refine ⟨i, ⟨Yi, hYi, hYifp⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso ?_⟩⟩
  exact (baseChangeLimitIso hlim i).app Yi ≪≫ (Over.pullback e.hom).mapIso ψ.symm ≪≫
    (Over.pullbackFactorIso e.hom_inv_id).symm.app Y.obj ≪≫ Over.pullbackId.app Y.obj

/-- **Fullness.** A morphism between the base changes to the vertex of two spaces over a stage
is the base change of a morphism over a later stage, through the comparisons of the
factorisations of the cone maps. -/
theorem full_of_isLimit (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
    (h : (baseChange B S hS (p i)).obj X ⟶ (baseChange B S hS (p i)).obj Y) :
    ∃ (j : I) (e : j ⟶ i) (h' : (baseChange B S hS (W.map e)).obj X ⟶
      (baseChange B S hS (W.map e)).obj Y),
      (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map h' =
        h ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y := by
  obtain ⟨hO, hhO⟩ : ∃ hO : (Over.pullback (yoneda.map (p i))).obj X.obj ⟶
      (Over.pullback (yoneda.map (p i))).obj Y.obj, hO = h.hom := ⟨h.hom, rfl⟩
  let f₀ : (Over.pullback (limit.π (W ⋙ yoneda) i)).obj X.obj ⟶
      (Over.pullback (limit.π (W ⋙ yoneda) i)).obj Y.obj :=
    (Over.pullback (limitIso hlim).hom).preimage
      ((baseChangeLimitIso hlim i).inv.app X.obj ≫ hO ≫
        (baseChangeLimitIso hlim i).hom.app Y.obj)
  have hf₀ : (Over.pullback (limitIso hlim).hom).map f₀ =
      (baseChangeLimitIso hlim i).inv.app X.obj ≫ hO ≫
        (baseChangeLimitIso hlim i).hom.app Y.obj := Functor.map_preimage _ _
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ :=
    Space.exists_morphism_after_baseChange_of_baseChangeSizeBounded B S hS hZ (W ⋙ yoneda)
      (fun i => isAlgebraicSpace_yoneda B S hS (W.obj i)) hAffine hQc hQs hSizeB hν hHomSizeB
      hB i X.obj Y.obj X.property.1 Y.property.1 X.property.2 Y.property.2 f₀
  refine ⟨j, e, ObjectProperty.homMk g, ?_⟩
  apply ObjectProperty.hom_ext
  have hX := baseChangeFactorIso_hom_app_left B S hS (hp e) X
  have hY := baseChangeFactorIso_hom_app_left B S hS (hp e) Y
  simp only [ObjectProperty.ι_map] at hX hY
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom, hX, hY]
  have hpe : yoneda.map (p j) ≫ (W ⋙ yoneda).map e = yoneda.map (p i) := by
    rw [Functor.comp_map, ← Functor.map_comp, hp e]
  have hcX := baseChangeLimitIso_cocycle hlim e X.obj α hα
  have hcY := baseChangeLimitIso_cocycle hlim e Y.obj β hβ
  have hnat := (baseChangeLimitIso hlim j).hom.naturality g
  rw [Functor.comp_map (Over.pullback (limit.π (W ⋙ yoneda) j))
    (Over.pullback (limitIso hlim).hom)] at hnat
  have hg' : (Over.pullback (limit.π (W ⋙ yoneda) j)).map g = α.hom ≫ f₀ ≫ β.inv := by
    rw [← Category.assoc, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hpj : (Over.pullback (yoneda.map (p j))).map g =
      (baseChangeLimitIso hlim j).hom.app ((Over.pullback ((W ⋙ yoneda).map e)).obj X.obj) ≫
      (Over.pullback (limitIso hlim).hom).map
        ((Over.pullback (limit.π (W ⋙ yoneda) j)).map g) ≫
      (baseChangeLimitIso hlim j).inv.app ((Over.pullback ((W ⋙ yoneda).map e)).obj Y.obj) := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have main : (Over.pullbackFactorIso (a := yoneda.map (p j)) (b := (W ⋙ yoneda).map e)
        (c := yoneda.map (p i)) hpe).hom.app X.obj ≫ (Over.pullback (yoneda.map (p j))).map g =
      hO ≫ (Over.pullbackFactorIso (a := yoneda.map (p j)) (b := (W ⋙ yoneda).map e)
        (c := yoneda.map (p i)) hpe).hom.app Y.obj := by
    have hcX' : ∀ {Z : Over (yoneda.obj M)} (k : (Over.pullback (limitIso hlim).hom).obj
        ((Over.pullback (limit.π (W ⋙ yoneda) i)).obj X.obj) ⟶ Z),
        (Over.pullbackFactorIso (a := yoneda.map (p j)) (b := (W ⋙ yoneda).map e)
          (c := yoneda.map (p i)) hpe).hom.app X.obj ≫
          (baseChangeLimitIso hlim j).hom.app ((Over.pullback ((W ⋙ yoneda).map e)).obj X.obj) ≫
            (Over.pullback (limitIso hlim).hom).map α.hom ≫ k =
          (baseChangeLimitIso hlim i).hom.app X.obj ≫ k := by
      intro Z k
      rw [← hcX]
      simp only [Category.assoc]
    rw [hpj, hg', Functor.map_comp, Functor.map_comp, hf₀]
    simp only [Category.assoc]
    have hY' : (baseChangeLimitIso hlim i).hom.app Y.obj ≫
        (Over.pullback (limitIso hlim).hom).map β.inv ≫
          (baseChangeLimitIso hlim j).inv.app ((Over.pullback ((W ⋙ yoneda).map e)).obj Y.obj) =
        (Over.pullbackFactorIso (a := yoneda.map (p j)) (b := (W ⋙ yoneda).map e)
          (c := yoneda.map (p i)) hpe).hom.app Y.obj := by
      rw [← hcY]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
      exact Category.comp_id _
    rw [hcX', Iso.hom_inv_id_app_assoc, hY']
  subst hhO
  exact main

/-- **Isomorphisms descend.** A morphism of spaces of finite presentation over a stage whose base
change to the vertex is an isomorphism is an isomorphism after base change to a later stage. -/
theorem exists_isIso_baseChange_map_of_isLimit (i : I)
    {X Y : FinitePresentationSpacesOver B S hS (W.obj i)} (f : X ⟶ Y)
    (hf : IsIso ((baseChange B S hS (p i)).map f)) :
    ∃ (j : I) (e : j ⟶ i), IsIso ((baseChange B S hS (W.map e)).map f) := by
  have h₁ : IsIso ((Over.pullback (yoneda.map (p i))).map f.hom) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map ((baseChange B S hS (p i)).map f)))
  have h₂ : IsIso ((Over.pullback (limitIso hlim).hom).map
      ((Over.pullback (limit.π (W ⋙ yoneda) i)).map f.hom)) := by
    have hnat := (baseChangeLimitIso hlim i).hom.naturality f.hom
    simp only [Functor.comp_map] at hnat
    have : (Over.pullback (limitIso hlim).hom).map
        ((Over.pullback (limit.π (W ⋙ yoneda) i)).map f.hom) =
        ((baseChangeLimitIso hlim i).app X.obj).inv ≫
          (Over.pullback (yoneda.map (p i))).map f.hom ≫
            ((baseChangeLimitIso hlim i).app Y.obj).hom := by
      rw [Iso.app_hom, hnat, Iso.app_inv, Iso.inv_hom_id_app_assoc]
    rw [this]
    infer_instance
  have h₃ : IsIso ((Over.pullback (limit.π (W ⋙ yoneda) i)).map f.hom) :=
    isIso_of_reflects_iso _ (Over.pullback (limitIso hlim).hom)
  obtain ⟨j, e, he⟩ := Space.exists_isIso_after_baseChange_of_baseChangeSizeBounded B S hS hZ
    (W ⋙ yoneda) (fun i => isAlgebraicSpace_yoneda B S hS (W.obj i)) hAffine hQc hQs hSizeB hν
    hHomSizeB hB i X.obj Y.obj X.property.1 Y.property.1 X.property.2 Y.property.2 f.hom
  refine ⟨j, e, ?_⟩
  have : IsIso ((ObjectProperty.ι _).map ((baseChange B S hS (W.map e)).map f)) := he
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

/-- **Stacks 07SK as a filtered `2`-colimit over the vertex of a limit cone of the site.** For a
cofiltered system of objects of the big fppf site whose represented presheaves have affine
transitions and quasi-compact, quasi-separated stages, and a cone over it which is a limit cone
of presheaves, base change along the cone exhibits the algebraic spaces of finite presentation
over the vertex as the filtered `2`-colimit of those over the stages. The size hypotheses are the
cofinality-free ones: fewer stages than the cutoff, morphism types bounded by one cardinal below
the cutoff, and uniformly bounded base changes. -/
theorem isFinitePresentationColimit_of_isLimit :
    IsFinitePresentationColimit B S hS W M p hp where
  essSurj Y := by
    obtain ⟨i, Yi, ⟨ψ⟩⟩ :=
      essSurj_of_isLimit hlim hZ hAffine hQc hQs hSizeB hν hHomSizeB hB Y
    exact ⟨i, Yi, ⟨ψ⟩⟩
  full i X Y h := full_of_isLimit hlim hZ hAffine hQc hQs hSizeB hν hHomSizeB hB i X Y h
  essIso i X Y Θ := by
    obtain ⟨j, e, h', hh'⟩ :=
      full_of_isLimit hlim hZ hAffine hQc hQs hSizeB hν hHomSizeB hB i X Y Θ.hom
    have hiso : IsIso ((baseChange B S hS (p j)).map h') := by
      have : (baseChange B S hS (p j)).map h' =
          (baseChangeFactorIso B S hS (hp e)).inv.app X ≫ Θ.hom ≫
            (baseChangeFactorIso B S hS (hp e)).hom.app Y := by
        rw [← hh', Iso.inv_hom_id_app_assoc]
      rw [this]
      infer_instance
    obtain ⟨k, e', he'⟩ := exists_isIso_baseChange_map_of_isLimit hlim hZ hAffine hQc hQs
      hSizeB hν hHomSizeB hB j h' hiso
    refine ⟨k, e' ≫ e, (baseChangeFactorIso B S hS (W.map_comp e' e).symm).app X ≪≫
      asIso ((baseChange B S hS (W.map e')).map h') ≪≫
      (baseChangeFactorIso B S hS (W.map_comp e' e).symm).symm.app Y, ?_⟩
    exact representsFactor_trans B S hS (hp e') (W.map_comp e' e).symm (hp (e' ≫ e)) (hp e)
      hh'
  faithful i X Y f g h := faithful_of_isLimit hlim hAffine hQc hSizeB hν hHomSizeB hB
    i X Y f g h

end Limit

end AlgebraicGeometry.FinitePresentationSpacesOver

end
