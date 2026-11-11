module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# Sheaves representable by algebraic spaces over an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `Y` be an affine formal algebraic
space over `S` and let `f : X ⟶ Y` be a map of fppf sheaves on the big fppf site of `S` which
is representable by algebraic spaces. **Stacks 0AJH** says that `X` is then a formal algebraic
space over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_affineFormal`:
  the source's proof of Stacks 0AJH, reducing it to Stacks 0AIU, which it takes in the
  argument `h0AIU`.

The registered, unconditional form of **Stacks 0AJH** is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_isAffineFormal`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineCharts`.

## Implementation notes

The argument `h0AIU` has the shape of the corrected Stacks 0AIU, which the library proves as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`
(in `StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaceThickenings`): for a
directed diagram of fppf sheaves whose objects are algebraic spaces and whose transition
morphisms are representable thickenings, any sheaf isomorphic to the colimit and satisfying the
set-theoretic condition of Stacks 0AIS is a formal algebraic space. This file sits below that
one in the import graph, so the reduction is stated for an arbitrary such argument. The
set-theoretic condition on `X` is an argument `hXset` as in
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_etaleCover`; the library proves it
from the other data as
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_representable_over_affineFormal`.

The pullback presentation is built directly in the category of fppf sheaves: the stage of
index `i` is the fibre product of `f` with the `i`-th stage of the given presentation of `Y`,
and the transition morphisms are the induced maps of fibre products. That this really presents
`X` is the statement that a filtered colimit of sheaves of sets is a universal colimit, proved
here for types, then for presheaves by evaluation, then for sheaves by transporting along the
sheafification adjunction; these three steps are the ones of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Pullback`, where they are private.

A stage of the presentation of `Y` is a sheafified Yoneda presheaf, while representability by
algebraic spaces is tested against universe-lifted Yoneda presheaves; the two are identified
by `CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, the chosen big fppf topology being
subcanonical. The same identification turns a thickening of the site into a representable
thickening of sheaves, which then base changes to the transition morphisms of the pullback
presentation.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace AlgebraicGeometry.FormalSpace

/-! ### Representable thickenings out of the site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Thickenings of schemes, read as a property of the morphisms of the big fppf site of `S`,
are stable under base change, since that site's structure functor to schemes preserves fibre
products. -/
public instance inverseImage_isThickening_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  refine ⟨?_⟩
  intro X₁ X₂ Y₂ X₃ p q p' q' hsq hq
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Stacks.Thickenings.IsThickening.{u}) (hsq.map (BigFppfOver.toScheme B S hS)) hq

/-- The sheafified Yoneda image of a morphism of the big fppf site of `S` whose underlying
morphism of schemes is a thickening is a representable thickening of fppf sheaves: the
sheafified Yoneda embedding agrees with the universe-lifted Yoneda embedding, the chosen big
fppf topology being subcanonical, and a Yoneda image is representable with the property of its
represented base changes. -/
theorem isRepresentableThickeningULift_sheafifiedYoneda_map
    {T T' : BigFppfOver B S hS} (m : T ⟶ T')
    (hm : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map m)) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m).hom := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  let J := BigFppfOver.topology B S hS
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let ee : Sheaf.sheafifiedYoneda J ⋙ sheafToPresheaf J (Type (u + 1)) ≅
      uliftYoneda.{u + 1} :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' J) (sheafToPresheaf J _) ≪≫
      GrothendieckTopology.uliftYonedaCompSheafToPresheaf J
  have hmap : P.relative (uliftYoneda.{u + 1}) ((uliftYoneda.{u + 1}).map m) :=
    MorphismProperty.relative_map hm
  have hsq : IsPullback (ee.hom.app T) (((Sheaf.sheafifiedYoneda J).map m).hom)
      ((uliftYoneda.{u + 1}).map m) (ee.hom.app T') :=
    IsPullback.of_horiz_isIso ⟨(ee.hom.naturality m).symm⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback hsq hmap

/-! ### Stacks 0AJH -/

/-- The source's proof of Stacks 0AJH, as a reduction to Stacks 0AIU. If `Y` is an affine
formal algebraic space over `S` and `f : X ⟶ Y` is a map of fppf sheaves representable by
algebraic spaces, then `X` is a formal algebraic space over `S`, given the corrected Stacks 0AIU
as `h0AIU` (proved in the library as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_isRepresentableThickeningULift`)
and the set-theoretic condition on `X` as `hXset` (proved in the library as
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_representable_over_affineFormal`).
The registered Stacks 0AJH, with neither argument, is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_isAffineFormal`.

Writing `Y` as the directed colimit of its affine stages, each fibre product of `X` with a
stage over `Y` is an algebraic space, the transition morphisms of these fibre products are
representable thickenings, and `X` is their colimit; `h0AIU` is applied to that
presentation. -/
theorem isFormalAlgebraicSpace_of_representable_over_affineFormal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
        Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z) :
    IsFormalAlgebraicSpace B S hS X := by
  classical
  obtain ⟨-, Λ, pre, hne, hdir, D, hthick, ⟨eY⟩⟩ := hY
  let _ : Preorder Λ := pre
  let _ : Nonempty Λ := hne
  let _ : IsDirected Λ (· ≤ ·) := hdir
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  let J := BigFppfOver.topology B S hS
  let K := BigAffineFppf.inclusion B S hS
  let Fy := Sheaf.sheafifiedYoneda J
  let G : Λ ⥤ FppfSheaf B S hS := D ⋙ K ⋙ Fy
  let gi (i : Λ) : G.obj i ⟶ Y := colimit.ι G i ≫ eY.inv
  have hgi {i j : Λ} (g : i ⟶ j) : G.map g ≫ gi j = gi i := by
    dsimp only [gi]
    rw [← Category.assoc]
    exact congrArg (fun z => z ≫ eY.inv) ((colimit.cocone G).w g)
  -- the pullback presentation of `X`
  let E : Λ ⥤ FppfSheaf B S hS :=
    { obj := fun i => pullback (gi i) f
      map := fun {i j} g => pullback.lift (pullback.fst (gi i) f ≫ G.map g)
        (pullback.snd (gi i) f) (by rw [Category.assoc, hgi g]; exact pullback.condition)
      map_id := fun i => by
        refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst, Category.id_comp]
          simp only [CategoryTheory.Functor.map_id, Category.comp_id]
        · simp only [pullback.lift_snd, Category.id_comp]
      map_comp := fun {i j k} g h => by
        refine pullback.hom_ext ?_ ?_
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
            CategoryTheory.Functor.map_comp]
        · simp only [Category.assoc, pullback.lift_snd] }
  have hEfst {i j : Λ} (g : i ⟶ j) :
      E.map g ≫ pullback.fst (gi j) f = pullback.fst (gi i) f ≫ G.map g :=
    pullback.lift_fst _ _ _
  have hEsnd {i j : Λ} (g : i ⟶ j) :
      E.map g ≫ pullback.snd (gi j) f = pullback.snd (gi i) f :=
    pullback.lift_snd _ _ _
  let α : E ⟶ G := { app := fun i => pullback.fst (gi i) f, naturality := fun i j g => hEfst g }
  let cX : Cocone E :=
    { pt := X
      ι := { app := fun i => pullback.snd (gi i) f
             naturality := fun i j g => by simpa using hEsnd g } }
  let cY : Cocone G :=
    { pt := Y
      ι := { app := gi, naturality := fun i j g => by simpa using hgi g } }
  have hcomm : α ≫ cY.ι = cX.ι ≫ (Functor.const Λ).map f := by
    apply NatTrans.ext
    exact funext fun i => pullback.condition
  have hα : NatTrans.Equifibered α := by
    intro i j g
    refine IsPullback.of_right ?_ (hEfst g) (IsPullback.of_hasPullback (gi j) f).flip
    rw [hEsnd g, hgi g]
    exact (IsPullback.of_hasPullback (gi i) f).flip
  have hpb (i : Λ) : IsPullback (cX.ι.app i) (α.app i) f (cY.ι.app i) :=
    (IsPullback.of_hasPullback (gi i) f).flip
  have hU0 : IsUniversalColimit (colimit.cocone G) :=
    sheaf_filteredColimit_isUniversalColimit J G
  have eYc : colimit.cocone G ≅ cY := Cocone.ext eY.symm (by intro i; rfl)
  have hcX : IsColimit cX := (hU0.of_iso eYc cX α f hcomm hα hpb).some
  have eX : X ≅ colimit E := hcX.coconePointUniqueUpToIso (colimit.isColimit E)
  -- the stages are algebraic spaces
  let ee : Fy ⋙ sheafToPresheaf J (Type (u + 1)) ≅ uliftYoneda.{u + 1} :=
    Functor.isoWhiskerRight (Sheaf.sheafifiedYonedaIsoUliftYoneda' J) (sheafToPresheaf J _) ≪≫
      GrothendieckTopology.uliftYonedaCompSheafToPresheaf J
  have halg : ∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj := by
    intro i
    let T : BigFppfOver B S hS := K.obj (D.obj i)
    let ξ : (uliftYoneda.{u + 1}).obj T ⟶ Y.obj := (ee.inv.app T) ≫ (gi i).hom
    have h0 : IsPullback (pullback.fst (gi i) f).hom (pullback.snd (gi i) f).hom
        (gi i).hom f.hom :=
      (IsPullback.of_hasPullback (gi i) f).map (sheafToPresheaf J (Type (u + 1)))
    have hbot : IsPullback ((gi i).hom) (ee.hom.app T) (𝟙 Y.obj) ξ :=
      IsPullback.of_vert_isIso ⟨by simp [ξ]⟩
    have hv := h0.flip.paste_vert hbot
    rw [Category.comp_id] at hv
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hv.flip.isoPullback.symm (hf T ξ)
  -- the transition morphisms are representable thickenings
  have hEthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom := by
    intro i j g
    have hG : Space.IsRepresentableThickeningULift.{u + 1} B S hS (G.map g).hom :=
      isRepresentableThickeningULift_sheafifiedYoneda_map B S hS (K.map (D.map g)) (hthick g)
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      ((hα g).flip.map (sheafToPresheaf J (Type (u + 1)))) hG
  exact h0AIU Λ E halg hEthick X hXset ⟨eX⟩

end AlgebraicGeometry.FormalSpace

end
