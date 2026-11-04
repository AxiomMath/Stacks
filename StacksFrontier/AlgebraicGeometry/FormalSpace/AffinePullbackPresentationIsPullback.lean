module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation

/-!
# Pullback of an affine presentation along a morphism with affine cartesian squares

`AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation` pulls an affine presentation
of an fppf sheaf `Y` back along a representable affine morphism `f : X ⟶ Y`. The construction
uses representability of `f` only over the affine stages of the presentation, so it applies to
any morphism of fppf sheaves which has, over every affine object of the site, a cartesian square
with an affine object of the site. That is the form of representability which Stacks 0AKN
supplies for a morphism of affine formal algebraic spaces representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_pullback_presentation_of_isPullback`: the
  pullback presentation, with its stages identified by cartesian squares, along a morphism with
  affine cartesian squares over the affine objects of the site.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

/-- Pulling an affine presentation back along a morphism of fppf sheaves which has, over every
affine object of the site, a cartesian square with an affine object of the site, gives an affine
presentation of the source whose stages are those fibre products. This is the form of the pullback
presentation that needs representability only over the affine test objects, which is what
Stacks 0AKN supplies for a morphism of affine formal algebraic spaces representable by algebraic
spaces. -/
theorem exists_affine_pullback_presentation_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : ∀ (U : BigAffineFppf B S hS)
      (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj U) ⟶ Y),
      ∃ (V : BigAffineFppf B S hS)
        (a : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj V) ⟶ X)
        (q : (BigAffineFppf.inclusion B S hS).obj V ⟶ (BigAffineFppf.inclusion B S hS).obj U),
        IsPullback a ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g)
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
    congrArg (· ≫ hY.inv) ((colimit.cocone G).w g)
  choose V a q hpb using fun i => hf (D.obj i) (gi i)
  let t (i j : I) (g : i ⟶ j) : K.obj (V i) ⟶ K.obj (V j) :=
    F.preimage ((hpb j).lift (a i) (F.map (q i ≫ D₀.map g)) (by
      calc
        a i ≫ f = F.map (q i) ≫ gi i := (hpb i).w
        _ = F.map (q i) ≫ G.map g ≫ gi j := by rw [hgi]
        _ = F.map (q i ≫ D₀.map g) ≫ gi j := by
          simp [G, D₀, Functor.map_comp]))
  have ht_fst (i j : I) (g : i ⟶ j) : F.map (t i j g) ≫ a j = a i := by
    simp only [t, Functor.map_preimage, IsPullback.lift_fst]
  have ht_snd (i j : I) (g : i ⟶ j) : t i j g ≫ q j = q i ≫ D₀.map g := by
    apply F.map_injective
    simpa only [t, Functor.map_comp, Functor.map_preimage] using (hpb j).lift_snd _ _ _
  let E : I ⥤ BigAffineFppf B S hS := {
    obj := V
    map := fun {i j} g => InducedCategory.homMk (t i j g)
    map_id := by
      intro i
      apply InducedCategory.hom_ext
      apply F.map_injective
      apply (hpb i).hom_ext
      · simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.id_hom, F.map_id,
          Category.id_comp]
        exact ht_fst i i (𝟙 i)
      · simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.id_hom, F.map_id,
          Category.id_comp]
        show F.map (t i i (𝟙 i)) ≫ F.map (q i) = F.map (q i)
        rw [← Functor.map_comp, ht_snd i i (𝟙 i)]
        simp only [D₀, Functor.comp_map, CategoryTheory.Functor.map_id]
        rw [Category.comp_id]
    map_comp := by
      intro i j k g h
      apply InducedCategory.hom_ext
      simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.comp_hom]
      apply F.map_injective
      apply (hpb k).hom_ext
      · rw [Functor.map_comp, Category.assoc, ht_fst j k h, ht_fst i j g, ht_fst i k (g ≫ h)]
      · rw [← Functor.map_comp, ← Functor.map_comp, ht_snd i k (g ≫ h), Category.assoc,
          ht_snd j k h, ← Category.assoc, ht_snd i j g, Category.assoc, D₀.map_comp] }
  let p : E ⟶ D := {
    app i := InducedCategory.homMk (q i)
    naturality i j g := InducedCategory.hom_ext (ht_snd i j g) }
  let α : E ⋙ K ⋙ F ⟶ G := Functor.whiskerRight p (K ⋙ F)
  let cX : Cocone (E ⋙ K ⋙ F) := {
    pt := X
    ι := {
      app i := a i
      naturality i j g := by
        show F.map (t i j g) ≫ a j = a i ≫ 𝟙 X
        rw [Category.comp_id]
        exact ht_fst i j g } }
  let cY : Cocone G := {
    pt := Y
    ι := { app i := gi i, naturality := fun i j g => hgi i j g } }
  have eY : colimit.cocone
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ cY :=
    Cocone.ext hY.symm (fun _ => rfl)
  have hcomm : α ≫ cY.ι = cX.ι ≫ (Functor.const I).map f :=
    NatTrans.ext <| funext fun i => (hpb i).w.symm
  have hα : NatTrans.Equifibered α := by
    intro i j g
    have houter : IsPullback (F.map (t i j g) ≫ a j) (F.map (q i)) f (G.map g ≫ gi j) := by
      simpa only [ht_fst i j g, hgi i j g] using hpb i
    have hsq : (E ⋙ K ⋙ F).map g ≫ α.app j = α.app i ≫ G.map g := by
      show F.map (t i j g) ≫ F.map (q j) = F.map (q i) ≫ F.map (D₀.map g)
      rw [← Functor.map_comp, ← Functor.map_comp, ht_snd i j g]
    exact IsPullback.of_right houter hsq (hpb j)
  have hpb' (i : I) : IsPullback (cX.ι.app i) (α.app i) f (cY.ι.app i) := hpb i
  have hUY : IsUniversalColimit cY :=
    (sheaf_filteredColimit_isUniversalColimit (C := C) (J := J) (F := G)).of_iso eY
  have hcX : IsColimit cX :=
    (hUY (F' := E ⋙ K ⋙ F) (c' := cX) (α := α) (f := f) hcomm hα hpb').some
  let hX : X ≅ colimit (E ⋙ K ⋙ F) :=
    hcX.coconePointUniqueUpToIso (colimit.isColimit (E ⋙ K ⋙ F))
  have hι (i : I) : colimit.ι (E ⋙ K ⋙ F) i ≫ hX.inv = a i :=
    colimit.comp_coconePointUniqueUpToIso_inv hcX i
  refine ⟨E, p, hX, fun i => ?_⟩
  rw [hι]
  exact hpb i

end AlgebraicGeometry.FormalSpace

end
