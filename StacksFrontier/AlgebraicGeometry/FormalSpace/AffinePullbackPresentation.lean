module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Pullback of an affine presentation

Let `S` be a scheme in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf sheaves on
the big fppf site of `S` which is representable and affine. If `Y` is the colimit of a directed
diagram `D` of affine schemes over `S`, then `X` is the colimit of the diagram `E` of the fibre
products `D i ×_Y X`, and if the transition morphisms of `D` are thickenings then so are those
of `E`. In particular, the source of a representable affine morphism to a countably indexed
sheaf is countably indexed.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation`: the pullback
  presentation, with its stages identified by cartesian squares.
* `AlgebraicGeometry.FormalSpace.isThickening_of_cartesian_presentation`: its transition
  morphisms are thickenings.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_relative_isAffineHom`: the source of a
  representable affine morphism to a countably indexed sheaf is countably indexed.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- A base change of a thickening of schemes is a thickening. -/
@[ega "I 4.3.2" "thickenings"]
instance isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) where
  of_isPullback h hg :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsClosedImmersion) h hg.1,
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.Surjective) h ⟨hg.2⟩).1⟩

end Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

/-- Composing the legs of the colimit cocone with an isomorphism keeps them compatible. -/
private theorem map_comp_colimit_ι_comp_inv {J C : Type*} [Category J] [Category C]
    (G : J ⥤ C) [HasColimit G] {Z : C} (h : Z ≅ colimit G) {i j : J} (g : i ⟶ j) :
    G.map g ≫ colimit.ι G j ≫ h.inv = colimit.ι G i ≫ h.inv := by
  rw [← Category.assoc, colimit.w]

/-- Pulling an affine presentation back along a representable affine morphism of fppf sheaves
gives an affine presentation of the source, whose stages are the fibre products with the stages
of the given presentation. -/
theorem exists_affine_pullback_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf :
      ((MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) f)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hY : Y ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    ∃ (E : I ⥤ BigAffineFppf B S hS) (p : E ⟶ D)
      (hX : X ≅ colimit
        (E ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))),
      (∀ i : I,
        IsPullback
          ((colimit.ι
            (E ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) ≫ hX.inv)
          ((BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (p.app i))
          f
          ((colimit.ι
            (D ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) ≫ hY.inv)) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let K := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda J
  let D₀ := D ⋙ K
  let G := D ⋙ K ⋙ F
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let gi (i : I) : F.obj (D₀.obj i) ⟶ Y :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ hY.inv
  have hgi (i j : I) (g : i ⟶ j) : G.map g ≫ gi j = gi i :=
    map_comp_colimit_ι_comp_inv G hY g
  let t (i j : I) (g : i ⟶ j) :
      hf.rep.pullback (gi i) ⟶ hf.rep.pullback (gi j) :=
    hf.rep.lift (hf.rep.fst (gi i))
      (hf.rep.snd (gi i) ≫ D₀.map g) (by
        calc
          hf.rep.fst (gi i) ≫ f = F.map (hf.rep.snd (gi i)) ≫ gi i := hf.rep.w (gi i)
          _ = F.map (hf.rep.snd (gi i)) ≫ G.map g ≫ gi j := by rw [hgi]
          _ = F.map (hf.rep.snd (gi i) ≫ D₀.map g) ≫ gi j := by
            simp [G, D₀, Functor.map_comp])
  let Eobj (i : I) : BigAffineFppf B S hS :=
    ⟨hf.rep.pullback (gi i), by
      let _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (gi i))) :=
        hf.property_snd (gi i)
      let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (D₀.obj i)) :=
        BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i)
      exact AlgebraicGeometry.isAffine_of_isAffineHom
        (f := (BigFppfOver.toScheme B S hS).map (hf.rep.snd (gi i)))⟩
  have ht_fst (i j : I) (g : i ⟶ j) :
      F.map (t i j g) ≫ hf.rep.fst (gi j) = hf.rep.fst (gi i) := by
    simp [t]
  have ht_snd (i j : I) (g : i ⟶ j) :
      t i j g ≫ hf.rep.snd (gi j) = hf.rep.snd (gi i) ≫ D₀.map g := by
    simp [t]
  let E : I ⥤ BigAffineFppf B S hS := {
    obj := Eobj
    map := fun {i j} g => InducedCategory.homMk (t i j g)
    map_id := by
      intro i
      apply InducedCategory.hom_ext
      dsimp only [Eobj]
      apply hf.rep.hom_ext (g := gi i)
      · calc
          F.map (t i i (𝟙 i)) ≫ hf.rep.fst (gi i) = hf.rep.fst (gi i) := ht_fst i i (𝟙 i)
          _ = F.map (𝟙 (hf.rep.pullback (gi i))) ≫ hf.rep.fst (gi i) := by
            simp only [F.map_id, Category.id_comp]
      · calc
          t i i (𝟙 i) ≫ hf.rep.snd (gi i) =
              hf.rep.snd (gi i) ≫ D₀.map (𝟙 i) := ht_snd i i (𝟙 i)
          _ = 𝟙 (hf.rep.pullback (gi i)) ≫ hf.rep.snd (gi i) := by simp
    map_comp := by
      intro i j k g h
      apply InducedCategory.hom_ext
      dsimp only [Eobj]
      simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.comp_hom]
      apply hf.rep.hom_ext (g := gi k)
      · rw [Functor.map_comp]
        calc
          F.map (t i k (g ≫ h)) ≫ hf.rep.fst (gi k) = hf.rep.fst (gi i) := ht_fst i k (g ≫ h)
          _ = F.map (t i j g) ≫ F.map (t j k h) ≫ hf.rep.fst (gi k) := by
            rw [ht_fst j k h, ht_fst i j g]
      · calc
          t i k (g ≫ h) ≫ hf.rep.snd (gi k) =
              hf.rep.snd (gi i) ≫ D₀.map g ≫ D₀.map h := by
            rw [ht_snd i k (g ≫ h), D₀.map_comp]
          _ = (t i j g ≫ hf.rep.snd (gi j)) ≫ D₀.map h := by rw [ht_snd i j g]; rfl
          _ = t i j g ≫ (hf.rep.snd (gi j) ≫ D₀.map h) := by rw [Category.assoc]
          _ = t i j g ≫ (t j k h ≫ hf.rep.snd (gi k)) := by rw [← ht_snd j k h]
          _ = (t i j g ≫ t j k h) ≫ hf.rep.snd (gi k) := by rw [← Category.assoc] }
  let p : E ⟶ D := {
    app i := InducedCategory.homMk (hf.rep.snd (gi i))
    naturality := by
      intro i j g
      apply InducedCategory.hom_ext
      exact ht_snd i j g }
  let α : E ⋙ K ⋙ F ⟶ G := Functor.whiskerRight p (K ⋙ F)
  let cX : Cocone (E ⋙ K ⋙ F) := {
    pt := X
    ι := {
      app i := hf.rep.fst (gi i)
      naturality := by
        intro i j g
        change F.map (t i j g) ≫ hf.rep.fst (gi j) = hf.rep.fst (gi i) ≫ 𝟙 X
        rw [Category.comp_id]
        exact ht_fst i j g } }
  let cY : Cocone G := {
    pt := Y
    ι := { app i := gi i, naturality := fun i j g => hgi i j g } }
  have eY : colimit.cocone
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ cY :=
    Cocone.ext hY.symm (by intro i; rfl)
  have hpapp (i : I) : (K ⋙ F).map (p.app i) = F.map (hf.rep.snd (gi i)) := rfl
  have hcomm : α ≫ cY.ι = cX.ι ≫ (Functor.const I).map f := by
    apply NatTrans.ext
    exact funext fun i => by
      change α.app i ≫ gi i = hf.rep.fst (gi i) ≫ f
      rw [Functor.whiskerRight_app, hpapp]
      exact (hf.rep.w (gi i)).symm
  have hα : NatTrans.Equifibered α := by
    intro i j g
    have houter : IsPullback
        (F.map (t i j g) ≫ hf.rep.fst (gi j))
        (F.map (hf.rep.snd (gi i))) f (G.map g ≫ gi j) := by
      simpa only [ht_fst i j g, hgi i j g] using hf.rep.isPullback (gi i)
    have hsq : (E ⋙ K ⋙ F).map g ≫ α.app j = α.app i ≫ G.map g := by
      change F.map (t i j g) ≫ F.map (hf.rep.snd (gi j)) =
        F.map (hf.rep.snd (gi i)) ≫ F.map (D₀.map g)
      rw [← Functor.map_comp, ← Functor.map_comp, ht_snd i j g]
    exact IsPullback.of_right houter hsq (hf.rep.isPullback (gi j))
  have hpb (i : I) : IsPullback (cX.ι.app i) (α.app i) f (cY.ι.app i) := by
    simpa [cX, cY, α, p, E, Eobj, F, K, D₀, G] using hf.rep.isPullback (gi i)
  have hU0 : IsUniversalColimit (colimit.cocone
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :=
    sheaf_filteredColimit_isUniversalColimit (C := C) (J := J) (F := G)
  have hUY : IsUniversalColimit cY := hU0.of_iso eY
  have hcX : IsColimit cX :=
    (hUY (F' := E ⋙ K ⋙ F) (c' := cX) (α := α) (f := f) hcomm hα hpb).some
  let hX : X ≅ colimit (E ⋙ K ⋙ F) :=
    hcX.coconePointUniqueUpToIso (colimit.isColimit (E ⋙ K ⋙ F))
  have hι (i : I) : colimit.ι (E ⋙ K ⋙ F) i ≫ hX.inv = hf.rep.fst (gi i) := by
    rw [colimit.comp_coconePointUniqueUpToIso_inv hcX i]
  refine ⟨E, p, hX, ?_⟩
  intro i
  rw [hι]
  simpa [cX, α, p, E, Eobj, gi, G, D₀, K, F] using hf.rep.isPullback (gi i)

/-- If the stages of a diagram `E` of affine schemes over `S` are cartesian over the stages of a
diagram `D` along a morphism `f` of fppf sheaves, and the transition morphisms of `D` are
thickenings, then so are the transition morphisms of `E`. -/
theorem isThickening_of_cartesian_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} [Preorder I]
    (D E : I ⥤ BigAffineFppf B S hS) (p : E ⟶ D)
    (hY : Y ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hX : X ≅ colimit
      (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (hcart : ∀ i : I,
      IsPullback
        ((colimit.ι
          (E ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) ≫ hX.inv)
        ((BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (p.app i))
        f
        ((colimit.ι
          (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i) ≫ hY.inv))
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map g))) :
    ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (E.map g)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let K := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda J
  let L := K ⋙ F
  let FE := E ⋙ K ⋙ F
  let FD := D ⋙ K ⋙ F
  let T := BigAffineFppf.toScheme B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let uE (i : I) : F.obj (K.obj (E.obj i)) ⟶ X := colimit.ι FE i ≫ hX.inv
  let uD (i : I) : F.obj (K.obj (D.obj i)) ⟶ Y := colimit.ι FD i ≫ hY.inv
  have huE {i j : I} (g : i ⟶ j) : FE.map g ≫ uE j = uE i :=
    map_comp_colimit_ι_comp_inv FE hX g
  have huD {i j : I} (g : i ⟶ j) : FD.map g ≫ uD j = uD i :=
    map_comp_colimit_ι_comp_inv FD hY g
  intro i j g
  have houter : IsPullback (FE.map g ≫ uE j) (L.map (p.app i)) f (FD.map g ≫ uD j) := by
    rw [huE g, huD g]
    simpa [uE, uD, FE, FD, L, K, F] using hcart i
  have hinner : IsPullback (uE j) (L.map (p.app j)) f (uD j) := by
    simpa [uE, uD, FE, FD, L, K, F] using hcart j
  have hsq : FE.map g ≫ L.map (p.app j) = L.map (p.app i) ≫ FD.map g := by
    change L.map (E.map g) ≫ L.map (p.app j) = L.map (p.app i) ≫ L.map (D.map g)
    rw [← Functor.map_comp, ← Functor.map_comp, p.naturality g]
  have hstage : IsPullback (E.map g) (p.app i) (p.app j) (D.map g) :=
    IsPullback.of_map L (p.naturality g) (IsPullback.of_right houter hsq hinner)
  have hstageScheme : IsPullback (T.map (E.map g)) (T.map (p.app i))
      (T.map (p.app j)) (T.map (D.map g)) := by
    simpa [T] using hstage.map T
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hstageScheme.flip (hD g)

/-- The source of a representable affine morphism of fppf sheaves whose target is countably
indexed is itself countably indexed. -/
@[stacks 0AKP "countably_indexed_source"]
theorem isCountablyIndexed_of_relative_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
    (hY : IsCountablyIndexed B S hS Y) :
    IsCountablyIndexed B S hS X := by
  obtain ⟨I, pre, hI, hd, hc, D, hD, ⟨hYiso⟩⟩ :=
    (isCountablyIndexed_iff_exists_countable_presentation B S hS Y).1 hY
  obtain ⟨E, p, hXiso, hcart⟩ := exists_affine_pullback_presentation B S hS f hf D hYiso
  exact (isCountablyIndexed_iff_exists_countable_presentation B S hS X).2
    ⟨I, pre, hI, hd, hc, E, isThickening_of_cartesian_presentation
      B S hS f D E p hYiso hXiso hcart hD, ⟨hXiso⟩⟩

end AlgebraicGeometry.FormalSpace

end
