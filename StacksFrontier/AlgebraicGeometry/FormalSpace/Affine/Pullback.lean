module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Pulling an affine presentation back along a representable affine morphism

Let `Y` be a sheaf on the big fppf site of `S` presented as a directed colimit of sheaves
represented by affine schemes, and let `f : X ⟶ Y` be a representable morphism all of whose
representable base changes are affine. Pulling the presentation back along `f` presents `X`
as the directed colimit of the fibre products of `f` with the stages of the presentation of
`Y`; and if the transition morphisms of the given presentation are thickenings, so are those
of the pulled-back one.

## Main results

* `AlgebraicGeometry.exists_affine_pullback_presentation`: the pullback presentation, with
  its stages identified by cartesian squares.
* `AlgebraicGeometry.isThickening_of_cartesian_presentation`: the transition morphisms of a
  cartesian pullback of a thickening presentation are thickenings.

## Implementation notes

The presentation is recorded by an indexed diagram of affine stages together with an
isomorphism of the sheaf with the colimit of the represented sheaves; the pullback
presentation additionally comes with a natural transformation to the given diagram whose
components sit in cartesian squares over `f`. The set-theoretic condition in the definition
of an affine formal algebraic space plays no role: the construction works for any affine
thickening presentation.

That the pullback diagram really is a presentation of `X` is the statement that a filtered
colimit of sheaves of sets is a universal colimit. That is proved here in three steps —
for types, then for presheaves by evaluation, then for sheaves by transporting along the
sheafification adjunction, which is a reflective left-exact localization.

Identifying a morphism of stages from the morphism it induces on represented sheaves needs
the sheafified Yoneda embedding to be faithful, hence the chosen big fppf topology to be
subcanonical.

## References

* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace AlgebraicGeometry

/-- A base change of a thickening is a thickening: closed immersions and surjections are both
stable under base change. -/
private theorem isThickening_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (h : IsPullback f' g' g f)
    (hg : Stacks.Thickenings.IsThickening g) : Stacks.Thickenings.IsThickening g' := by
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback h hg.1, ?_⟩
  have hsurj : Surjective g := ⟨hg.2⟩
  exact (MorphismProperty.IsStableUnderBaseChange.of_isPullback h hsurj).surj

/-- Transition morphisms are compatible with the coprojections of a colimit, composed with the
inverse of an identification of an object with the colimit. -/
private theorem map_comp_colimit_ι_comp_inv {J : Type*} [Category J] {C : Type*} [Category C]
    {F : J ⥤ C} [HasColimit F] {Y : C} (e : Y ≅ colimit F) {i j : J} (g : i ⟶ j) :
    F.map g ≫ colimit.ι F j ≫ e.inv = colimit.ι F i ≫ e.inv := by
  rw [← Category.assoc, colimit.w]

/-- If two cartesian squares over `f` are connected by compatible morphisms, the square formed
by those morphisms is cartesian. -/
private theorem isPullback_of_comp_eq {C : Type*} [Category C]
    {X Z P₁ P₂ X₁ X₂ : C} {f : X ⟶ Z} {fst₁ : X₁ ⟶ X} {fst₂ : X₂ ⟶ X} {snd₁ : X₁ ⟶ P₁}
    {snd₂ : X₂ ⟶ P₂} {u₁ : P₁ ⟶ Z} {u₂ : P₂ ⟶ Z} (h₁ : IsPullback fst₁ snd₁ f u₁)
    (h₂ : IsPullback fst₂ snd₂ f u₂) {a : X₁ ⟶ X₂} {d : P₁ ⟶ P₂} (hfst : a ≫ fst₂ = fst₁)
    (hu : d ≫ u₂ = u₁) (hsq : a ≫ snd₂ = snd₁ ≫ d) : IsPullback a snd₁ snd₂ d := by
  subst hfst hu
  exact IsPullback.of_right h₁ hsq h₂

/-- Pulling an affine presentation of a sheaf back along a representable morphism with affine
representable base changes gives an affine presentation of the source, whose stages are
identified with the fibre products by cartesian squares. -/
theorem exists_affine_pullback_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    (hf :
      ((MorphismProperty.inverseImage
        (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS))) f)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hY : Y ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS))) :
    ∃ (E : I ⥤ BigAffineFppf B S hS) (p : E ⟶ D)
      (hX : X ≅ colimit
        (E ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS))),
      (∀ i : I,
        IsPullback
          ((colimit.ι
            (E ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda
                (BigFppfOver.topology B S hS)) i) ≫ hX.inv)
          ((BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)).map (p.app i))
          f
          ((colimit.ι
                (D ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda
                (BigFppfOver.topology B S hS)) i) ≫ hY.inv)) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let K := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda J
  let D₀ := D ⋙ K
  let G := D ⋙ K ⋙ F
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  let _ : F.FullyFaithful := Sheaf.fullyFaithfulSheafifiedYoneda J
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let gi (i : I) : F.obj (D₀.obj i) ⟶ Y :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ hY.inv
  have hgi (i j : I) (g : i ⟶ j) :
      G.map g ≫ gi j = gi i := by
    exact map_comp_colimit_ι_comp_inv hY g
  let t (i j : I) (g : i ⟶ j) :
      hf.rep.pullback (gi i) ⟶ hf.rep.pullback (gi j) :=
    hf.rep.lift (hf.rep.fst (gi i))
      (hf.rep.snd (gi i) ≫ D₀.map g) (by
        calc
          hf.rep.fst (gi i) ≫ f = F.map (hf.rep.snd (gi i)) ≫ gi i :=
            hf.rep.w (gi i)
          _ = F.map (hf.rep.snd (gi i)) ≫ G.map g ≫ gi j := by rw [hgi]
          _ = F.map (hf.rep.snd (gi i) ≫ D₀.map g) ≫ gi j := by
            simp [G, D₀, Functor.map_comp])
  let Eobj (i : I) : BigAffineFppf B S hS :=
    ⟨hf.rep.pullback (gi i), by
      let _ : IsAffineHom
          ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (gi i))) :=
        hf.property_snd (gi i)
      let _ : IsAffine
          ((BigFppfOver.toScheme B S hS).obj (D₀.obj i)) :=
        BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i)
      change IsAffine ((BigFppfOver.toScheme B S hS).obj
        (hf.rep.pullback (gi i)))
      exact isAffine_of_isAffineHom
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
          F.map (t i i (𝟙 i)) ≫ hf.rep.fst (gi i) = hf.rep.fst (gi i) :=
            ht_fst i i (𝟙 i)
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
      · change F.map (t i k (g ≫ h)) ≫ hf.rep.fst (gi k) =
          F.map (t i j g ≫ t j k h) ≫ hf.rep.fst (gi k)
        rw [Functor.map_comp, Category.assoc, ht_fst, ht_fst, ht_fst]
      · calc
          t i k (g ≫ h) ≫ hf.rep.snd (gi k) =
              hf.rep.snd (gi i) ≫ D₀.map g ≫ D₀.map h := by
            rw [ht_snd i k (g ≫ h), D₀.map_comp]
          _ = (t i j g ≫ t j k h) ≫ hf.rep.snd (gi k) := by
            calc
              hf.rep.snd (gi i) ≫ D₀.map g ≫ D₀.map h =
                  (t i j g ≫ hf.rep.snd (gi j)) ≫ D₀.map h := by
                rw [ht_snd i j g]
                rfl
              _ = t i j g ≫ (hf.rep.snd (gi j) ≫ D₀.map h) := by rw [Category.assoc]
              _ = t i j g ≫ (t j k h ≫ hf.rep.snd (gi k)) := by rw [← ht_snd j k h]
              _ = (t i j g ≫ t j k h) ≫ hf.rep.snd (gi k) := by
                rw [← Category.assoc] }
  let p : E ⟶ D := {
    app i := InducedCategory.homMk (hf.rep.snd (gi i))
    naturality _ _ g := InducedCategory.hom_ext (ht_snd _ _ g) }
  let α : E ⋙ K ⋙ F ⟶ G := Functor.whiskerRight p (K ⋙ F)
  let cX : Cocone (E ⋙ K ⋙ F) := {
    pt := X
    ι := {
      app i := hf.rep.fst (gi i)
      naturality i j g := by
        change F.map (t i j g) ≫ hf.rep.fst (gi j) = hf.rep.fst (gi i) ≫ 𝟙 X
        rw [Category.comp_id]
        exact ht_fst i j g } }
  let cY : Cocone G := {
    pt := Y
    ι := {
      app i := gi i
      naturality i j g := hgi i j g } }
  have eY : colimit.cocone
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ cY :=
    Cocone.ext hY.symm (fun _ => rfl)
  have hcY : IsColimit cY := (colimit.isColimit
    (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))).ofIsoColimit eY
  have hpapp (i : I) : (K ⋙ F).map (p.app i) = F.map (hf.rep.snd (gi i)) := rfl
  have hcomm : α ≫ cY.ι = cX.ι ≫ (Functor.const I).map f := by
    refine NatTrans.ext <| funext fun i => ?_
    change α.app i ≫ gi i = hf.rep.fst (gi i) ≫ f
    rw [Functor.whiskerRight_app, hpapp]
    exact (hf.rep.w (gi i)).symm
  have hα : NatTrans.Equifibered α := by
    intro i j g
    have hsq : (E ⋙ K ⋙ F).map g ≫ α.app j = α.app i ≫ G.map g := by
      change F.map (t i j g) ≫ F.map (hf.rep.snd (gi j)) =
        F.map (hf.rep.snd (gi i)) ≫ F.map (D₀.map g)
      rw [← Functor.map_comp, ← Functor.map_comp, ht_snd i j g]
    exact isPullback_of_comp_eq (hf.rep.isPullback (gi i)) (hf.rep.isPullback (gi j))
      (ht_fst i j g) (hgi i j g) hsq
  have hpb (i : I) : IsPullback (cX.ι.app i) (α.app i) f (cY.ι.app i) := by
    simpa [cX, cY, α, p, E, Eobj, F, K, D₀, G] using hf.rep.isPullback (gi i)
  have hU0 : IsUniversalColimit (colimit.cocone
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :=
    sheaf_filteredColimit_isUniversalColimit
      (C := C) (J := J) (F := G)
  have hUY : IsUniversalColimit cY := hU0.of_iso eY
  have hcX : IsColimit cX :=
    (hUY (F' := E ⋙ K ⋙ F) (c' := cX) (α := α) (f := f) hcomm hα hpb).some
  let hX : X ≅ colimit (E ⋙ K ⋙ F) :=
    hcX.coconePointUniqueUpToIso (colimit.isColimit (E ⋙ K ⋙ F))
  have hι (i : I) :
      colimit.ι (E ⋙ K ⋙ F) i ≫ hX.inv = hf.rep.fst (gi i) := by
    rw [colimit.comp_coconePointUniqueUpToIso_inv hcX i]
  refine ⟨E, p, hX, fun i => ?_⟩
  rw [hι]
  simpa [cX, α, p, E, Eobj, gi, G, D₀, K, F] using
    (hf.rep.isPullback (gi i))

/-- If every stage of a presentation sits in a cartesian square over a presentation whose
transition morphisms are thickenings, then its own transition morphisms are thickenings. -/
theorem isThickening_of_cartesian_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f : X ⟶ Y)
    {I : Type (u + 1)} [Preorder I]
    (D E : I ⥤ BigAffineFppf B S hS)
    (p : E ⟶ D)
    (hY : Y ≅ colimit
      (D ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)))
    (hX : X ≅ colimit
      (E ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda
          (BigFppfOver.topology B S hS)))
    (hcart : ∀ i : I,
      IsPullback
        ((colimit.ι
          (E ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)) i) ≫ hX.inv)
        ((BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda
            (BigFppfOver.topology B S hS)).map (p.app i))
        f
        ((colimit.ι
          (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda
              (BigFppfOver.topology B S hS)) i) ≫ hY.inv))
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (D.map g))) :
    ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening
        ((BigAffineFppf.toScheme B S hS).map (E.map g)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let K := BigAffineFppf.inclusion B S hS
  let F := Sheaf.sheafifiedYoneda J
  let L := K ⋙ F
  let FE := E ⋙ K ⋙ F
  let FD := D ⋙ K ⋙ F
  let T := BigAffineFppf.toScheme B S hS
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : J.Subcanonical := inferInstance
  let _ : F.FullyFaithful := Sheaf.fullyFaithfulSheafifiedYoneda J
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let _ : K.Full := inferInstance
  let _ : K.Faithful := inferInstance
  let _ : L.Full := inferInstance
  let _ : L.Faithful := inferInstance
  let uE (i : I) : F.obj (K.obj (E.obj i)) ⟶ X :=
    colimit.ι FE i ≫ hX.inv
  let uD (i : I) : F.obj (K.obj (D.obj i)) ⟶ Y :=
    colimit.ι FD i ≫ hY.inv
  have huE {i j : I} (g : i ⟶ j) : FE.map g ≫ uE j = uE i := by
    exact map_comp_colimit_ι_comp_inv hX g
  have huD {i j : I} (g : i ⟶ j) : FD.map g ≫ uD j = uD i := by
    exact map_comp_colimit_ι_comp_inv hY g
  intro i j g
  have hcart' (k : I) : IsPullback (uE k) (L.map (p.app k)) f (uD k) := by
    simpa [uE, uD, FE, FD, L, K, F] using hcart k
  have hsq : FE.map g ≫ L.map (p.app j) =
      L.map (p.app i) ≫ FD.map g := by
    change L.map (E.map g) ≫ L.map (p.app j) =
      L.map (p.app i) ≫ L.map (D.map g)
    rw [← Functor.map_comp, ← Functor.map_comp, p.naturality g]
  have hstageSheaf : IsPullback (FE.map g) (L.map (p.app i))
      (L.map (p.app j)) (FD.map g) :=
    isPullback_of_comp_eq (hcart' i) (hcart' j) (huE g) (huD g) hsq
  have hstage : IsPullback (E.map g) (p.app i) (p.app j) (D.map g) :=
    IsPullback.of_map L (p.naturality g) hstageSheaf
  have hstageScheme : IsPullback (T.map (E.map g)) (T.map (p.app i))
      (T.map (p.app j)) (T.map (D.map g)) := by
    simpa [T] using hstage.map T
  exact isThickening_of_isPullback hstageScheme.flip (hD g)

end AlgebraicGeometry
