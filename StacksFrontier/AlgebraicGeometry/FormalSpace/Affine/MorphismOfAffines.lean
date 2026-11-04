module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSupplement

/-!
# Affine morphisms of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces. **Stacks
0AKN** asserts that `f` is then representable by schemes and affine. This file proves that
assertion, over every test object of the site.

The assertion is proved first over the test objects whose underlying scheme is affine, where it
comes with more: the fibre product of `X` with such a test object over `Y` is represented by an
object of the site whose underlying scheme is again affine. It is then extended to an arbitrary
test object, where no affineness of the representing object can be expected, by affine-locality
of affineness on the target.

The step that makes the affine case work, and which is of independent use, is that an affine
formal algebraic space whose underlying presheaf is an algebraic space is already represented by
an affine object of the site: one of the inclusions of a thickening stage into it is an
isomorphism.

Everything here consumes only the *presentations* of `X` and `Y` as directed colimits of affine
objects of the site along thickenings — `AlgebraicGeometry.FormalSpace.HasThickeningPresentation`
— and not the set-theoretic condition of Stacks 0AIS which together with them makes them affine
formal algebraic spaces. So the hypotheses are stated with the presentation alone. This matters
for a formal spectrum: its presentation is its construction, whereas the set-theoretic condition
asks the site to contain the coproduct of all its quotient spectra.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sheafifiedYoneda'`: the sheaf
  represented by an affine object of the site is an affine formal algebraic space -- the
  converse direction, and the base case of the notion.
* `AlgebraicGeometry.FormalSpace.exists_isIso_colimitι_of_isAlgebraicSpaceULift`: a sheaf
  presented by affine thickenings which is an algebraic space is represented by an affine object
  of the site, in the form that some stage inclusion of the presentation is an isomorphism.
* `AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isAffine_source`: a morphism to a sheaf
  presented by affine thickenings from a sheaf represented by an affine object of the site is
  representable by schemes and affine.
* `AlgebraicGeometry.FormalSpace.exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 0AKN** over the test objects with affine underlying scheme, with the representing
  object affine as well.
* `AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 0AKN**, over every test object of the site.

## Implementation notes

The stage inclusions of a presentation of an affine formal algebraic space are representable
thickenings by Stacks 0AI9, and a morphism from a quasi-compact algebraic space factors through
one of the stages by Stacks 0AIA. Both conclusions of Stacks 0AKN come from combining these two
facts, but Stacks 0AIA takes the quasi-compact algebraic space in the value universe `Type u` of
the schemes, while an affine formal algebraic space is a sheaf of `Type (u + 1)`. The argument
therefore descends the sheaf to the value universe of the site, which is possible exactly
because it is assumed to be an algebraic space: its sections are then pointwise `u`-small.

Quasi-compactness of that model is Stacks 040W, part (1), applied to the descended stage
inclusion, which is surjective because a thickening of schemes is. With the model quasi-compact,
Stacks 0AIA makes the stage inclusion a split epimorphism; it is also a monomorphism, because a
thickening of schemes is a closed immersion and hence a monomorphism of the site, and a
monomorphism which is a split epimorphism is an isomorphism.

For a morphism `g` from a sheaf represented by an affine object `U` of the site to an affine
formal algebraic space `Y`, the quasi-compact algebraic space Stacks 0AIA is applied to is
`CategoryTheory.yoneda.obj U` itself, no descent being needed: `g` factors through a stage
`Y_μ`, the stage inclusion is a thickening hence affine, and the factoring morphism is a
morphism of affine objects of the site, so `g` is affine by multiplicativity.

The base change `pullback.fst f g` of such a `g` along `f` is then affine, so the fibre product
is an affine formal algebraic space by Stacks 0AKP, part (1), and an algebraic space by Stacks
03XY. The result above applies to it.

*Passing to an arbitrary test object.* The glueing of the representing affine objects over an
affine open covering of the test object is relative Tag 03JH, which the library has only for
presheaves of `Type u`. That is no obstruction, because the object being glued does not have to
be an affine formal algebraic space: it is enough that it be an algebraic space over `S`, which
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
asks for and which the fibre product with an arbitrary test object has, by Stacks 03XY again.
The fibre product is then pointwise `u`-small, hence the universe lift of an algebraic space in
the value universe of the site, and its projection to the test object descends with it; the
affine case above, read over each morphism of the site into the test object with affine source,
is exactly the affine-base-change condition that glueing consumes, affineness of a morphism of
schemes being Zariski-local at the target.

Descending the projection is where the universe lift has to be used as a functor rather than as
a universe-raising operation: the base change squares the affine case produces live among fppf
sheaves, and they become the squares the descended projection must have because the lift is
fully faithful and preserves fibre products.

## References

* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Relative representability of a morphism transports along a natural isomorphism of the
embedding functor: the fibre products that have to be represented are the same up to the
components of the isomorphism. -/
private theorem relativelyRepresentable_of_iso_embedding {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : D} (f : X ⟶ Y)
    (hf : F.relativelyRepresentable f) : G.relativelyRepresentable f := by
  intro U g
  obtain ⟨V, q, p, h⟩ := hf ((e.app U).hom ≫ g)
  exact ⟨V, q, (e.app V).inv ≫ p,
    h.of_iso (e.app V) (Iso.refl _) (e.app U) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

/-- Relative representability of a morphism transports along a natural isomorphism of the
embedding functor: the fibre products that have to be represented are the same up to the
components of the isomorphism. -/
alias relativelyRepresentable_of_iso_embedding' := relativelyRepresentable_of_iso_embedding

/-- A relative morphism property transports along a natural isomorphism of the embedding
functor, because the represented base changes it is tested against correspond. -/
private theorem relative_of_iso_embedding {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y)
    (hf : P.relative F f) : P.relative G f := by
  refine ⟨relativelyRepresentable_of_iso_embedding e f hf.rep, ?_⟩
  intro U V g p q hp
  exact hf.property ((e.app U).hom ≫ g) ((e.app V).hom ≫ p) q
    (hp.of_iso (e.app V).symm (Iso.refl _) (e.app U).symm (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp))

/-- A relative morphism property transports along a natural isomorphism of the embedding
functor, because the represented base changes it is tested against correspond. -/
alias relative_of_iso_embedding' := relative_of_iso_embedding

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying presheaf of a sheafified representable is the universe-lifted Yoneda
presheaf, because the big fppf site of `S` is subcanonical. -/
noncomputable def sheafifiedYonedaCompForgetIso' :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙
        sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) _ ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- **The sheaf represented by an affine object of the site is an affine formal algebraic
space.** The presentation is the constant one on a one-object index: that index is directed, its
only transition morphism is an identity and so a thickening, and the colimit of a constant
diagram on it is its value. The set-theoretic condition holds because the sheaf is itself
represented and the kernel pair of its identity is again itself.

This is the base case of the affine formal algebraic spaces: it is what makes the objects of
the diagram of lifts of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleLiftDiagram` satisfy the chart
hypothesis of Stacks 0GVN, and what recognises the affine étale atlas of a quasi-compact
algebraic space as an affine formal chart. -/
theorem isAffineFormalAlgebraicSpace_sheafifiedYoneda' (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffineFormalAlgebraicSpace B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V) := by
  classical
  set X := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V with hXdef
  refine ⟨⟨V, V, X, X, ⟨(sheafifiedYonedaCompForgetIso' B S hS).app V⟩,
    ⟨(sheafifiedYonedaCompForgetIso' B S hS).app V⟩, 𝟙 X, inferInstance,
    pullback.lift (𝟙 X) (𝟙 X) rfl, ?_⟩, PUnit.{u + 2}, inferInstance, inferInstance,
    inferInstance, (Functor.const PUnit.{u + 2}).obj (⟨V, hV⟩ : BigAffineFppf B S hS), ?_, ?_⟩
  · -- the kernel pair of an identity is an isomorphism, hence an epimorphism
    have hfst : IsIso (pullback.fst (𝟙 X) (𝟙 X)) :=
      (IsPullback.of_hasPullback (𝟙 X) (𝟙 X)).isIso_fst_of_isIso
    have hlift : pullback.lift (𝟙 X) (𝟙 X) rfl = inv (pullback.fst (𝟙 X) (𝟙 X)) := by
      refine (cancel_mono (pullback.fst (𝟙 X) (𝟙 X))).1 ?_
      rw [pullback.lift_fst, IsIso.inv_hom_id]
    have : IsIso (pullback.lift (𝟙 X) (𝟙 X) rfl : X ⟶ pullback (𝟙 X) (𝟙 X)) := by
      rw [hlift]; infer_instance
    infer_instance
  · -- the only transition morphism is an identity
    intro i j f
    have h : ((Functor.const PUnit.{u + 2}).obj
        (⟨V, hV⟩ : BigAffineFppf B S hS)).map f = 𝟙 _ := rfl
    rw [h, CategoryTheory.Functor.map_id]
    exact ⟨inferInstance, Function.surjective_id⟩
  · -- the colimit of a constant diagram on a one-object index is its value
    refine ⟨IsColimit.coconePointUniqueUpToIso (s := Cocone.mk X ⟨fun _ ↦ 𝟙 X, ?_⟩) ?_
      (colimit.isColimit _)⟩
    · intro i j f
      have h : (((Functor.const PUnit.{u + 2}).obj (⟨V, hV⟩ : BigAffineFppf B S hS)) ⋙
          BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f = 𝟙 X := by
        have h₀ : ((Functor.const PUnit.{u + 2}).obj
            (⟨V, hV⟩ : BigAffineFppf B S hS)).map f = 𝟙 _ := rfl
        rw [Functor.comp_map, h₀, CategoryTheory.Functor.map_id]
        rfl
      rw [h]
      rfl
    · exact ⟨fun s ↦ s.ι.app PUnit.unit, fun s j ↦ by cases j; exact Category.id_comp _,
        fun s m hm ↦ (Category.id_comp m).symm.trans (hm PUnit.unit)⟩

/-- A property of morphisms of the big fppf site of `S` holds relative to the sheafified Yoneda
embedding for a morphism of fppf sheaves exactly when it holds for the underlying morphism of
presheaves relative to the universe-lifted Yoneda embedding. -/
private theorem relative_sheafifiedYoneda_iff_uliftYoneda
    (P : MorphismProperty (BigFppfOver B S hS))
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y) :
    P.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f ↔
      P.relative (uliftYoneda.{u + 1}) f.hom := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let L := sheafToPresheaf J (Type (u + 1))
  let _ : (Sheaf.sheafifiedYoneda J).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : (Sheaf.sheafifiedYoneda J).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  exact ⟨fun h ↦ Space.relative_of_iso_embedding (sheafifiedYonedaCompForgetIso' B S hS) P (L.map f)
      ((Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) L P f).mpr h),
    fun h ↦ (Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) L P f).mp
      (Space.relative_of_iso_embedding (sheafifiedYonedaCompForgetIso' B S hS).symm P (L.map f) h)⟩

/-- A property of morphisms of the big fppf site of `S` holds relative to the sheafified Yoneda
embedding for a morphism of fppf sheaves exactly when it holds for the underlying morphism of
presheaves relative to the universe-lifted Yoneda embedding. -/
alias relative_sheafifiedYoneda_iff_uliftYoneda' := relative_sheafifiedYoneda_iff_uliftYoneda

/-- A thickening of schemes is surjective, being by definition a surjective closed
immersion. -/
private theorem isThickening_le_surjective :
    (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
  fun _ _ _ h ↦ ⟨h.2⟩

/-- A relative property of a morphism of fppf sheaves descends to the value universe of the
site: if the universe lift of a morphism of presheaves of `Type u` is, up to the given
isomorphisms, the underlying morphism of the sheaf morphism, then it inherits the property
relative to the Yoneda embedding of presheaves of `Type u`. -/
private theorem presheaf_of_relative_sheafifiedYoneda
    (P : MorphismProperty (BigFppfOver B S hS))
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    {X0 Y0 : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eX : X0 ⋙ uliftFunctor.{u + 1, u} ≅ X.obj)
    (eY : Y0 ⋙ uliftFunctor.{u + 1, u} ≅ Y.obj)
    (g : X0 ⟶ Y0)
    (hg : Functor.whiskerRight g uliftFunctor.{u + 1, u} = eX.hom ≫ f.hom ≫ eY.inv)
    (hf : P.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) :
    P.presheaf g := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  have h2 : P.relative (uliftYoneda.{u + 1}) (eX.hom ≫ f.hom ≫ eY.inv) :=
    MorphismProperty.RespectsIso.precomp _ eX.hom _
      (MorphismProperty.RespectsIso.postcomp _ eY.inv _
        ((relative_sheafifiedYoneda_iff_uliftYoneda B S hS P f).mp hf))
  rw [← hg] at h2
  exact (Space.relative_comp_map_iff yoneda H P g).mp h2

/-- The descent of a representable thickening into an fppf sheaf with a model in the value
universe of the site: the morphism of presheaves of `Type u` whose universe lift is the given
one, together with the thickening property it inherits. -/
private theorem exists_descended_isThickening'
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {X0 : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eX : X0 ⋙ uliftFunctor.{u + 1, u} ≅ X.obj)
    (T : BigFppfOver B S hS)
    (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hι : MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ι) :
    ∃ s : yoneda.obj T ⟶ X0,
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf s ∧
      Functor.whiskerRight s uliftFunctor.{u + 1, u} =
        ((sheafifiedYonedaCompForgetIso' B S hS).app T).inv ≫ ι.hom ≫ eX.inv := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  let eT : (yoneda.obj T) ⋙ uliftFunctor.{u + 1, u} ≅
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T).obj :=
    ((sheafifiedYonedaCompForgetIso' B S hS).app T).symm
  refine ⟨H.preimage (eT.hom ≫ ι.hom ≫ eX.inv), ?_, H.map_preimage _⟩
  exact presheaf_of_relative_sheafifiedYoneda B S hS _ ι eT eX _ (H.map_preimage _) hι

/-- A representable thickening into an fppf sheaf is a monomorphism of fppf sheaves, once the
target has a model in the value universe of the site: the descended morphism is a relative
monomorphism of presheaves, hence a monomorphism, and monomorphy travels back up the lift. -/
private theorem mono_of_relative_isThickening
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {X0 : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eX : X0 ⋙ uliftFunctor.{u + 1, u} ≅ X.obj)
    (T : BigFppfOver B S hS)
    (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hι : MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ι) :
    Mono ι := by
  obtain ⟨s, hs, hseq⟩ := exists_descended_isThickening' B S hS eX T ι hι
  have hle : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
        MorphismProperty.monomorphisms (BigFppfOver B S hS) := fun _ _ q h ↦ by
    have _ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) := h.1
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map
      (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map q)))
  have hmonos : Mono s := MorphismProperty.presheaf_mono_of_le hle hs
  have hmonoLift : Mono (Functor.whiskerRight s uliftFunctor.{u + 1, u}) := by
    rw [NatTrans.mono_iff_mono_app] at hmonos ⊢
    intro k
    rw [CategoryTheory.mono_iff_injective]
    have hk := hmonos k
    rw [CategoryTheory.mono_iff_injective] at hk
    exact fun a b hab ↦ congrArg ULift.up (hk (congrArg ULift.down hab))
  have hrw : inv ((sheafifiedYonedaCompForgetIso' B S hS).app T).inv ≫
      Functor.whiskerRight s uliftFunctor.{u + 1, u} ≫ eX.hom = ι.hom := by
    rw [hseq]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, IsIso.inv_hom_id_assoc]
  have hmonoHom : Mono ι.hom := by
    rw [← hrw]
    simp only [mono_comp_iff_of_isIso]
    exact MorphismProperty.RespectsIso.postcomp
      (MorphismProperty.monomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)))
      eX.hom _ hmonoLift
  exact (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mono_of_mono_map hmonoHom

/-- A sheaf presented by affine thickenings which is an algebraic space is represented by an
affine object of the site. -/
private theorem exists_isIso_colimitι_aux
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)
    (hXalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj) :
    ∃ i : I, IsIso (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let G := Sheaf.sheafifiedYoneda J
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  -- descend `X` to the value universe of the site
  have hsmall := Space.small_of_isAlgebraicSpaceULift B S hS hXalg
  let X0 := FunctorToTypes.shrink.{u} X.obj
  let eX : X0 ⋙ uliftFunctor.{u + 1, u} ≅ X.obj := Space.shrinkCompUliftFunctorIso X.obj
  have hX0 : _root_.AlgebraicGeometry.IsAlgebraicSpace B S hS X0 :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X0).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS eX.symm hXalg)
  -- a stage
  obtain ⟨i₀⟩ := ‹Nonempty I›
  let Xi : C := (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)
  let ι : G.obj Xi ⟶ X :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i₀ ≫ e.hom
  have hι : MorphismProperty.relative G
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ι :=
    isThickening_colimitι B S hS D hD X e i₀
  -- descend the stage inclusion
  let eXi : (yoneda.obj Xi) ⋙ uliftFunctor.{u + 1, u} ≅ (G.obj Xi).obj :=
    ((sheafifiedYonedaCompForgetIso' B S hS).app Xi).symm
  let σ : yoneda.obj Xi ⟶ X0 := H.preimage (eXi.hom ≫ ι.hom ≫ eX.inv)
  have hσ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf σ :=
    presheaf_of_relative_sheafifiedYoneda B S hS _ ι eXi eX σ (H.map_preimage _) hι
  -- surjectivity on points of the descended stage inclusion
  have hle : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
    MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) := fun _ _ _ h ↦ ⟨h.2⟩
  have hsurj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf σ :=
    MorphismProperty.relative_monotone hle _ hσ
  have hsurjpts : Space.IsSurjective B S hS σ :=
    Space.isSurjective_of_presheafSurjective B S hS σ hsurj
  -- the stage is affine, hence quasi-compact
  have hXiAff : IsAffine ((BigFppfOver.toScheme B S hS).obj Xi) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i₀)
  have hqcXi : Space.IsQuasiCompactSpace B S hS (yoneda.obj Xi) :=
    Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS Xi hXiAff
  have hqc : Space.IsQuasiCompactSpace B S hS X0 :=
    Space.IsQuasiCompactSpace.of_isSurjective B S hS
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Xi) hX0 hsurjpts hqcXi
  -- the model of `X` is already a sheaf, so sheafifying its universe lift returns `X`
  let fiso : (presheafToSheaf J (Type (u + 1))).obj (X0 ⋙ uliftFunctor.{u + 1, u}) ≅ X :=
    (presheafToSheaf J (Type (u + 1))).mapIso eX ≪≫
      (asIso ((sheafificationNatIso J (Type (u + 1))).hom.app X)).symm
  obtain ⟨i, g, hg⟩ :=
    exists_factor_through_thickening' B S hS I D (fun _ _ g ↦ (hD g).1) X e.symm X0 hqc
      fiso.hom
  refine ⟨i, ?_⟩
  have hmono : Mono (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ e.hom) :=
    mono_of_relative_isThickening B S hS eX _ _ (isThickening_colimitι B S hS D hD X e i)
  have hsplit : IsSplitEpi (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ e.hom) :=
    IsSplitEpi.mk' ⟨fiso.inv ≫ g, by
      rw [Category.assoc]
      simpa only [Iso.inv_hom_id, Iso.symm_inv] using congrArg (fun t ↦ fiso.inv ≫ t) hg⟩
  let _ : Mono (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ e.hom) := hmono
  let _ : IsSplitEpi (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ e.hom) := hsplit
  exact isIso_of_mono_of_isSplitEpi _

/-- An affine formal algebraic space whose underlying presheaf is an algebraic space over `S`
is represented by an affine object of the site: for a presentation of it by affine objects with
thickening transition morphisms, one of the stage inclusions is an isomorphism. The stage
inclusion is a representable thickening, hence a monomorphism, and Stacks 0AIA splits it once
the space is known to be quasi-compact. -/
theorem exists_isIso_colimitι_of_isAlgebraicSpaceULift
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)
    (hXalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj) :
    ∃ i : I, IsIso (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  have _ := hX
  exact exists_isIso_colimitι_aux B S hS D hD X e hXalg

/-- A sheaf presented as a directed colimit of affine objects of the site along thickenings
whose underlying presheaf is an algebraic space over `S` is represented by an affine object of
the site: one of the stage inclusions of the presentation is an isomorphism. The stage inclusion
is a representable thickening, hence a monomorphism, and Stacks 0AIA splits it once the space is
known to be quasi-compact.

Only the presentation is used, so no set-theoretic condition is assumed: the conclusion is in
any case that the sheaf is representable, which is far stronger than that condition. -/
theorem exists_isIso_colimitι_of_isAlgebraicSpaceULift'
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)
    (hXalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj) :
    ∃ i : I, IsIso (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  exact exists_isIso_colimitι_aux B S hS D hD X e hXalg

/-- A morphism from a sheaf represented by an affine object of the site to a sheaf presented
by affine thickenings is representable by schemes and affine. -/
private theorem relative_isAffineHom_aux
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hY : HasThickeningPresentation B S hS Y)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let G := Sheaf.sheafifiedYoneda J
  let P := MorphismProperty.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : G.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : G.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let _ : HasPullbacks C := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan G := by
    dsimp only [G, Sheaf.sheafifiedYoneda]
    infer_instance
  let _ : P.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  let _ : P.IsMultiplicative :=
    { id_mem := fun V ↦ by
        show IsAffineHom ((BigFppfOver.toScheme B S hS).map (𝟙 V))
        rw [(BigFppfOver.toScheme B S hS).map_id]
        infer_instance
      comp_mem := fun {V W Z} a b ha hb ↦ by
        show IsAffineHom ((BigFppfOver.toScheme B S hS).map (a ≫ b))
        rw [(BigFppfOver.toScheme B S hS).map_comp]
        have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map a) := ha
        have _ : IsAffineHom ((BigFppfOver.toScheme B S hS).map b) := hb
        infer_instance }
  obtain ⟨I, pre, hI, hd, D, hD, ⟨eY⟩⟩ := id hY
  let _ : Preorder I := pre
  let _ : Nonempty I := hI
  let _ : IsDirected I (· ≤ ·) := hd
  have hqcU : Space.IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  obtain ⟨μ, g', hfac⟩ :=
    exists_factor_through_thickening' B S hS I D (fun _ _ g ↦ (hD g).1) Y eY (yoneda.obj U) hqcU g
  -- the stage inclusion is a thickening, hence affine
  have hι : MorphismProperty.relative G
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) μ ≫ eY.symm.hom) :=
    isThickening_colimitι B S hS D hD Y eY.symm μ
  have hleAff : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ P := fun _ _ _ h ↦ by
    have _ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map _) := h.1
    exact inferInstanceAs (IsAffineHom _)
  have hιAff : MorphismProperty.relative G P
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) μ ≫ eY.symm.hom) :=
    MorphismProperty.relative_monotone hleAff _ hι
  -- the factoring morphism is a morphism of affine objects of the site
  obtain ⟨q, hq⟩ := G.map_surjective g'
  have hqAff : P q := by
    show IsAffineHom ((BigFppfOver.toScheme B S hS).map q)
    have _ := hU
    have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj μ))) :=
      BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj μ)
    infer_instance
  have hg'Aff : MorphismProperty.relative G P g' := by
    rw [← hq]
    exact MorphismProperty.relative_map hqAff
  have : g' ≫ (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) μ ≫ eY.symm.hom) = g := by
    simpa only [Iso.symm_hom] using hfac
  rw [← this]
  let _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.comp_mem _ _ _ hg'Aff hιAff

/-- A morphism to an affine formal algebraic space over `S` from a sheaf represented by an
object of the site whose underlying scheme is affine is representable by schemes and affine: by
Stacks 0AIA it factors through an affine thickening stage, the stage inclusion is a thickening
and hence affine, and the factoring morphism is a morphism of affine objects of the site. -/
theorem relative_isAffineHom_of_isAffine_source
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g := by
  exact relative_isAffineHom_aux B S hS Y hY.2 U hU g

/-- A morphism from a sheaf represented by an object of the site whose underlying scheme is
affine, to a sheaf presented as a directed colimit of affine objects of the site along
thickenings, is representable by schemes and affine: by Stacks 0AIA it factors through an affine
thickening stage, the stage inclusion is a thickening and hence affine, and the factoring
morphism is a morphism of affine objects of the site.

Only the presentation of the target is used, not the set-theoretic condition which together with
it makes the target an affine formal algebraic space. -/
theorem relative_isAffineHom_of_isAffine_source'
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hY : HasThickeningPresentation B S hS Y)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) g := by
  exact relative_isAffineHom_aux B S hS Y hY U hU g

/-- The fibre product of a morphism representable by algebraic spaces with a morphism from a
sheafified representable is an algebraic space. -/
private theorem isAlgebraicSpaceULift_pullback_obj
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (U : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback f g).obj := by
  have hmap := (IsPullback.of_hasPullback f g).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hUalg := Space.isAlgebraicSpaceULift_of_iso B S hS
    ((sheafifiedYonedaCompForgetIso' B S hS).app U).symm
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U)
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    (pullbackSymmetry g.hom f.hom ≪≫ hmap.isoPullback.symm)
    (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS f.hom g.hom hf hUalg)

/-- Stacks 0AKN over the test objects with affine underlying scheme, stated with the
presentations alone. -/
private theorem exists_affine_baseChange_aux
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : HasThickeningPresentation B S hS X)
    (hY : HasThickeningPresentation B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let G := Sheaf.sheafifiedYoneda J
  let P := MorphismProperty.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : G.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : G.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let _ : (MorphismProperty.relative G P).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  -- the test morphism is affine, hence so is its base change along `f`
  have hgAff : MorphismProperty.relative G P g :=
    relative_isAffineHom_aux B S hS Y hY U hU g
  have hpb : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hfstAff : MorphismProperty.relative G P (pullback.fst f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hgAff
  -- so the fibre product is presented by affine thickenings as well
  have hZ : HasThickeningPresentation B S hS (pullback f g) :=
    _root_.AlgebraicGeometry.hasThickeningPresentation_of_affine B S hS
      (pullback.fst f g) hX hfstAff
  -- and an algebraic space, since `f` is representable by algebraic spaces
  have hZalg := isAlgebraicSpaceULift_pullback_obj B S hS f hf U g
  -- the crux of the argument: it is therefore represented by an affine object of the site
  obtain ⟨I, pre, hI, hd, D, hD, ⟨eZ⟩⟩ := hZ
  let _ : Preorder I := pre
  let _ : Nonempty I := hI
  let _ : IsDirected I (· ≤ ·) := hd
  obtain ⟨i, hiso⟩ := exists_isIso_colimitι_aux B S hS D hD (pullback f g)
    eZ.symm hZalg
  let V : C := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let ι : G.obj V ⟶ pullback f g :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ eZ.symm.hom
  let _ : IsIso ι := hiso
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i)
  obtain ⟨q, hq⟩ := G.map_surjective (ι ≫ pullback.snd f g)
  refine ⟨V, ι ≫ pullback.fst f g, q, ?_, hVaff, ?_⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso ι) rfl (by rw [asIso_hom]; exact hq.symm)
    rw [hq, Category.assoc, Category.assoc, pullback.condition]
    simp only [ι, Category.assoc]
  · have _ := hU
    have _ := hVaff
    infer_instance

/-- **Stacks 0AKN** over the test objects with affine underlying scheme. Let `f : X ⟶ Y` be a
morphism of affine formal algebraic spaces over `S` which is representable by algebraic spaces,
and let `g` be a morphism to `Y` from a sheaf represented by an object `U` of the site with
affine underlying scheme. Then the fibre product of `f` and `g` is represented by an object of
the site with affine underlying scheme, and the induced morphism to `U` is an affine morphism of
schemes: `f` is representable by schemes and affine over `U`. -/
theorem exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := by
  exact exists_affine_baseChange_aux B S hS f hX.2 hY.2 hf U hU g

/-- **Stacks 0AKN** over the test objects with affine underlying scheme. Let `f : X ⟶ Y` be a
morphism of affine formal algebraic spaces over `S` which is representable by algebraic spaces,
and let `g` be a morphism to `Y` from a sheaf represented by an object `U` of the site with
affine underlying scheme. Then the fibre product of `f` and `g` is represented by an object of
the site with affine underlying scheme, and the induced morphism to `U` is an affine morphism of
schemes: `f` is representable by schemes and affine over `U`.

Of the two sheaves only the presentations by affine thickenings are used, not the set-theoretic
condition of Stacks 0AIS which together with them makes them affine formal algebraic spaces; so
the conclusion is available for the formal spectrum of a weakly admissible topological ring over
any site containing its quotient spectra, with no condition on the size of the site. -/
@[stacks 0AKN "representability by schemes together with affineness, over every test object of \
the site whose underlying scheme is affine"]
theorem exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces'
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : HasThickeningPresentation B S hS X)
    (hY : HasThickeningPresentation B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffineHom ((BigFppfOver.toScheme B S hS).map q) := by
  exact exists_affine_baseChange_aux B S hS f hX hY hf U hU g


/-! ### Stacks 0AKN over an arbitrary test object -/

/-- The affine-base-change condition of `AlgebraicGeometry.Space.HoldsOnAffineBaseChange` for a
descent of a morphism of fppf sheaves whose target is a sheafified representable.

The descent is given by a model `Z₀` of the source in the value universe of the site together
with a morphism `π₀` to the Yoneda presheaf of the test object whose universe lift is the given
morphism. The hypothesis is that the base change of the given morphism of sheaves along every
morphism of the site into the test object with affine source is represented by an object of the
site with affine underlying scheme whose projection has `Q`; those base changes become the base
changes `π₀` has to have, the universe lift being fully faithful and preserving fibre
products. -/
private theorem holdsOnAffineBaseChange_of_descended (Q : MorphismProperty Scheme.{u})
    {Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} {U : BigFppfOver B S hS}
    (π : Z ⟶ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U)
    {Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eZ : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).obj Z₀ ≅ Z.obj) (π₀ : Z₀ ⟶ yoneda.obj U)
    (hπ₀ : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).map π₀ =
      eZ.hom ≫ π.hom ≫ (sheafifiedYonedaCompForgetIso' B S hS).hom.app U)
    (hall : ∀ T : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ t : T ⟶ U, ∃ (W : BigFppfOver B S hS) (p : W ⟶ T)
        (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ Z),
        IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) π
            ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map t) ∧
          IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          Q ((BigFppfOver.toScheme B S hS).map p)) :
    Space.HoldsOnAffineBaseChange B S hS Q π₀ := by
  intro T hT t
  obtain ⟨t₀, rfl⟩ := yoneda.map_surjective t
  obtain ⟨W, p, r, hsq, hWaff, hQ⟩ := hall T hT t₀
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  let κ := sheafifiedYonedaCompForgetIso' B S hS
  -- the comparison isomorphism, with its components typed for the universe-lift functor
  let k : ∀ V : BigFppfOver B S hS, H.obj (yoneda.obj V) ≅ (G.obj V).obj := fun V =>
    { hom := (κ.app V).inv
      inv := (κ.app V).hom
      hom_inv_id := (κ.app V).inv_hom_id
      inv_hom_id := (κ.app V).hom_inv_id }
  have hk : ∀ {V V' : BigFppfOver B S hS} (a : V ⟶ V'),
      (k V).hom ≫ (G.map a).hom = H.map (yoneda.map a) ≫ (k V').hom :=
    fun a ↦ (κ.inv.naturality a).symm
  have hπ : H.map π₀ = eZ.hom ≫ π.hom ≫ (k U).inv := hπ₀
  have hsqP : IsPullback r.hom (G.map p).hom π.hom (G.map t₀).hom :=
    hsq.map (sheafToPresheaf J (Type (u + 1)))
  refine ⟨W, p, H.preimage ((k W).hom ≫ r.hom ≫ eZ.inv), ?_, hWaff, hQ⟩
  apply IsPullback.of_map_of_faithful (F := H)
  refine hsqP.of_iso' (k W) eZ (k T) (k U) ?_ ?_ ?_ ?_
  · rw [H.map_preimage, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact hk p
  · rw [hπ, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact hk t₀

/-- **Stacks 0AKN.** A morphism `f : X ⟶ Y` of affine formal algebraic spaces over `S` which is
representable by algebraic spaces is representable by schemes, and the morphism of schemes
underlying each of its represented base changes is affine. Nothing is assumed of the test
objects: this is the source's assertion over every object of the site.

Over a test object with affine underlying scheme the conclusion is
`AlgebraicGeometry.FormalSpace.exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces`,
and it carries in addition that the representing object is affine, which an arbitrary test
object cannot have. The passage to an arbitrary test object `U` is affine-locality on the
target, carried out in the value universe of the site: the fibre product `X ×_Y U` is an
algebraic space over `S`, because `f` is representable by algebraic spaces and `U` is
representable, hence pointwise `u`-small, so it is the universe lift of an algebraic space `Z₀`
in the value universe of the site and the projection to `U` descends with it. The affine form
above, read over each morphism of the site into `U` with affine source, is exactly the
affine-base-change condition of that descended projection, which relative Tag 03JH for a
morphism out of an algebraic space —
`AlgebraicGeometry.Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace`
— glues into a single object of the site with affine projection to `U`, affineness of a
morphism of schemes being Zariski-local at the target.

As in the affine form, of the two sheaves only the presentations by affine thickenings are used
and not the set-theoretic condition of Stacks 0AIS. -/
@[stacks 0AKN "both assertions of the source -- representability by schemes and affineness -- \
over an arbitrary test object of the site"]
theorem relative_isAffineHom_of_hasThickeningPresentation
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : HasThickeningPresentation B S hS X)
    (hY : HasThickeningPresentation B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  classical
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  let κ := sheafifiedYonedaCompForgetIso' B S hS
  let P := MorphismProperty.inverseImage
    (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : G.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : G.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let _ : P.IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  let _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- the comparison isomorphism, with its components typed for the universe-lift functor
  let k : ∀ V : BigFppfOver B S hS, H.obj (yoneda.obj V) ≅ (G.obj V).obj := fun V =>
    { hom := (κ.app V).inv
      inv := (κ.app V).hom
      hom_inv_id := (κ.app V).inv_hom_id
      inv_hom_id := (κ.app V).hom_inv_id }
  have hk : ∀ {V V' : BigFppfOver B S hS} (a : V ⟶ V'),
      (k V).hom ≫ (G.map a).hom = H.map (yoneda.map a) ≫ (k V').hom :=
    fun a ↦ (κ.inv.naturality a).symm
  apply MorphismProperty.relative.of_exists
  intro U g
  have hpb : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  -- the fibre product is an algebraic space, since `f` is representable by algebraic spaces
  have hZalg := isAlgebraicSpaceULift_pullback_obj B S hS f hf U g
  -- so it descends to the value universe of the site, and the projection to `U` with it
  have _ := Space.small_of_isAlgebraicSpaceULift B S hS hZalg
  let Z₀ := FunctorToTypes.shrink.{u} (pullback f g).obj
  let eZ : H.obj Z₀ ≅ (pullback f g).obj :=
    Space.shrinkCompUliftFunctorIso (pullback f g).obj
  have hZ₀ : _root_.AlgebraicGeometry.IsAlgebraicSpace B S hS Z₀ :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Z₀).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS eZ.symm hZalg)
  let π₀ : Z₀ ⟶ yoneda.obj U :=
    H.preimage (eZ.hom ≫ (pullback.snd f g).hom ≫ (k U).inv)
  -- the affine form of the tag is the affine-base-change condition of that projection
  have hπ₀ : Space.HoldsOnAffineBaseChange B S hS
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) π₀ := by
    refine holdsOnAffineBaseChange_of_descended B S hS _ (pullback.snd f g) eZ π₀
      (H.map_preimage _) ?_
    intro T hT t
    obtain ⟨V, pX, qV, hsq, hVaff, hqaff⟩ :=
      exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces' B S hS f hX hY hf T hT
        (G.map t ≫ g)
    exact ⟨V, qV, _, hsq.of_right' hpb, hVaff, hqaff⟩
  -- glueing in the value universe of the site produces the representing object
  obtain ⟨V, e, q, hq, hqaff⟩ :=
    Space.exists_representing_over_of_holdsOnAffineBaseChange_of_isAlgebraicSpace B S hS
      _root_.AlgebraicGeometry.isZariskiLocalAtTarget_isAffineHom hZ₀ π₀ hπ₀
  let ψ : (pullback f g).obj ≅ (G.obj V).obj := eZ.symm ≪≫ H.mapIso e ≪≫ k V
  let θ : pullback f g ≅ G.obj V :=
    (sheafToPresheaf J (Type (u + 1))).preimageIso ψ
  have hψ : ψ.inv ≫ (pullback.snd f g).hom = (G.map q).hom := by
    have h1 : H.map e.inv ≫ H.map π₀ = H.map (yoneda.map q) := by
      rw [← H.map_comp, hq]
    have h2 : H.map π₀ = eZ.hom ≫ (pullback.snd f g).hom ≫ (k U).inv := H.map_preimage _
    have h4 : (G.map q).hom = (k V).inv ≫ H.map (yoneda.map q) ≫ (k U).hom := by
      rw [← hk q, Iso.inv_hom_id_assoc]
    rw [h4, ← h1, h2]
    simp only [ψ, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hθhom : (sheafToPresheaf J (Type (u + 1))).map θ.inv = ψ.inv := by
    simp only [θ, Functor.preimageIso_inv, Functor.map_preimage]
  have hθ : θ.inv ≫ pullback.snd f g = G.map q :=
    (sheafToPresheaf J (Type (u + 1))).map_injective (by
      rw [Functor.map_comp, hθhom]
      exact hψ)
  refine ⟨V, θ.inv ≫ pullback.fst f g, q, ?_, hqaff⟩
  refine hpb.of_iso θ (Iso.refl X) (Iso.refl (G.obj U)) (Iso.refl Y) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Category.comp_id, ← hθ, Iso.hom_inv_id_assoc]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.FormalSpace

end
