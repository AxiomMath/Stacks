module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.CartesianColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined
public import StacksFrontier.CategoryTheory.PullbackCancelMonoRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines

/-!
# Stacks 0AKN at every test object of the site

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces.
**Stacks 0AKN** asserts that `f` is representable by schemes and affine, at every test object of
the site. As a consequence, a morphism of affine formal algebraic spaces which is locally of
finite type is of finite type.

## Main results

* `AlgebraicGeometry.FormalSpace.stage_size_le`: the stages of a presentation of an affine
  formal algebraic space are uniformly no larger than the object of the site which the
  set-theoretic condition of Stacks 0AIS supplies.
* `AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 0AKN**.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal`: a
  morphism of affine formal algebraic spaces over `S` which is locally of finite type is of
  finite type.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 04T6](https://stacks.math.columbia.edu/tag/04T6)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AJJ](https://stacks.math.columbia.edu/tag/0AJJ)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0ANV](https://stacks.math.columbia.edu/tag/0ANV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable thickening of the big fppf site of `S` is locally of finite type. -/
theorem inverseImage_isThickening_le_locallyOfFiniteType :
    MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := fun _ _ _ h ↦ by
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map _) := h.1
  exact inferInstanceAs (LocallyOfFiniteType _)

/-- **The stages of a presentation of an affine formal algebraic space are uniformly bounded
below the cutoff of the site.** For a presentation of `X` by affine objects of the site with
thickening transition morphisms, the sizes of the stages are all at most the size of the one
object of the site that the set-theoretic condition of **Stacks 0AIS** attaches to `X`. -/
theorem stage_size_le
    {X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)
    (hset : _root_.AlgebraicGeometry.SatisfiesSetTheoreticCondition B S hS X) :
    ∃ κ : Cardinal.{u}, κ < B.cutoff ∧ ∀ i : I,
      ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))).size ≤ κ := by
  classical
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  obtain ⟨U, R, hU, hR, ⟨eU⟩, -, t, ht, -⟩ := hset
  refine ⟨((BigFppfOver.toScheme B S hS).obj U).size, U.left.property, fun i => ?_⟩
  let t' : uliftYoneda.{u + 1}.obj U ⟶ X.obj := eU.inv ≫ t.hom
  have ht' : Presheaf.IsLocallySurjective J t' := by
    let : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    dsimp only [t']
    infer_instance
  let Xi : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let : IsAffine Xi.left.obj := BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj i)
  let ι : G.obj Xi ⟶ X := colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ G) i ≫ e.hom
  have hι : MorphismProperty.relative G
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ι :=
    MorphismProperty.relative_monotone
      (inverseImage_isThickening_le_locallyOfFiniteType B S hS) _
      (isThickening_colimitι B S hS D hD X e i)
  have hιp := (relative_sheafifiedYoneda_iff_uliftYoneda B S hS
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) ι).mp hι
  let c : uliftYoneda.{u + 1}.obj Xi ⟶ X.obj :=
    ((CartesianColimit.sheafifiedYonedaToUliftPresheafIso B S hS).app Xi).inv ≫ ι.hom
  have hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c := by
    let : MorphismProperty.RespectsIso
        ((MorphismProperty.inverseImage
          (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
    exact MorphismProperty.RespectsIso.precomp _ _ _ hιp
  exact affineChart_size_le' B S hS U Xi t' ht' c hc

/-- **The fibre product of a morphism of affine formal algebraic spaces with an affine test
object is no larger than the test object and the source together.** Let `f : X ⟶ Y` be a
morphism of affine formal algebraic spaces over `S` which is representable by algebraic spaces.
There is one cardinal `κ` below the cutoff of the site such that, over every test object `U` of
the site with affine underlying scheme, the fibre product of `f` and a morphism `U ⟶ Y` is
represented by an object `V` of the site with `V ⟶ U` affine and
`size V ≤ max κ (size U)`. -/
theorem exists_size_bound_affine_baseChange_of_isRepresentableByAlgebraicSpaces
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ ξ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y,
      ∃ (V : BigFppfOver B S hS)
        (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) (q : V ⟶ U),
        IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f ξ ∧
          IsAffineHom ((BigFppfOver.toScheme B S hS).map q) ∧
          ((BigFppfOver.toScheme B S hS).obj V).size ≤
            max κ ((BigFppfOver.toScheme B S hS).obj U).size := by
  classical
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let : G.Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let : G.Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan G := by
    dsimp only [G, Sheaf.sheafifiedYoneda]
    infer_instance
  let : ReflectsLimitsOfShape WalkingCospan G :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp only [BigFppfOver.toScheme]
    infer_instance
  obtain ⟨hXset, IX, preX, hIXne, hIXd, DX, hDX, ⟨eX⟩⟩ := id hX
  let : Preorder IX := preX
  let : Nonempty IX := hIXne
  let : IsDirected IX (· ≤ ·) := hIXd
  obtain ⟨hYset, IY, preY, hIYne, hIYd, DY, hDY, ⟨eY⟩⟩ := id hY
  let : Preorder IY := preY
  let : Nonempty IY := hIYne
  let : IsDirected IY (· ≤ ·) := hIYd
  obtain ⟨κ, hκ, hstage⟩ := stage_size_le B S hS DX hDX eX.symm hXset
  have : FunctorToTypes.Small.{u} X.obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS X hXset
  have : FunctorToTypes.Small.{u} Y.obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS Y hYset
  let eX0 : FunctorToTypes.shrink.{u} X.obj ⋙ uliftFunctor.{u + 1, u} ≅ X.obj :=
    Space.shrinkCompUliftFunctorIso.{u + 1} X.obj
  let eY0 : FunctorToTypes.shrink.{u} Y.obj ⋙ uliftFunctor.{u + 1, u} ≅ Y.obj :=
    Space.shrinkCompUliftFunctorIso.{u + 1} Y.obj
  refine ⟨κ, hκ, fun U hU ξ => ?_⟩
  obtain ⟨V, p, q, hpb, hVaff, hqaff⟩ :=
    exists_affine_baseChange_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf U hU ξ
  refine ⟨V, p, q, hpb, hqaff, ?_⟩
  have hqcV : Space.IsQuasiCompactSpace B S hS (yoneda.obj V) :=
    Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hVaff
  obtain ⟨lam, p0, hp0⟩ := exists_factor_through_thickening B S hS IX DX hDX X eX
    (yoneda.obj V) (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V) hqcV p
  let Xlam : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (DX.obj lam)
  let a : G.obj Xlam ⟶ X :=
    colimit.ι (DX ⋙ BigAffineFppf.inclusion B S hS ⋙ G) lam ≫ eX.symm.hom
  have : Mono a :=
    mono_of_relative_isThickening B S hS eX0 Xlam a
      (isThickening_colimitι B S hS DX hDX X eX.symm lam)
  have hXlamAff : IsAffine ((BigFppfOver.toScheme B S hS).obj Xlam) :=
    BigAffineFppf.isAffine_toScheme_obj B S hS (DX.obj lam)
  obtain ⟨p', hp'⟩ : ∃ p' : G.obj V ⟶ G.obj Xlam, p' ≫ a = p := ⟨p0, hp0⟩
  have factorY : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ z : G.obj T ⟶ Y, ∃ (m : IY) (z' : G.obj T ⟶ G.obj
        ((BigAffineFppf.inclusion B S hS).obj (DY.obj m))),
        z' ≫ (colimit.ι (DY ⋙ BigAffineFppf.inclusion B S hS ⋙ G) m ≫ eY.symm.hom) = z :=
    fun T hT z => exists_factor_through_thickening B S hS IY DY hDY Y eY (yoneda.obj T)
      (_root_.AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT) z
  obtain ⟨mu, xi, hxi⟩ := factorY U hU ξ
  obtain ⟨nu, cc, hcc⟩ := factorY Xlam hXlamAff (a ≫ f)
  obtain ⟨rho, hmr, hnr⟩ := directed_of (· ≤ ·) mu nu
  let b : G.obj ((BigAffineFppf.inclusion B S hS).obj (DY.obj rho)) ⟶ Y :=
    colimit.ι (DY ⋙ BigAffineFppf.inclusion B S hS ⋙ G) rho ≫ eY.symm.hom
  have : Mono b :=
    mono_of_relative_isThickening B S hS eY0 _ b
      (isThickening_colimitι B S hS DY hDY Y eY.symm rho)
  have push : ∀ (T : BigFppfOver B S hS) (z : G.obj T ⟶ Y) (m : IY) (hm : m ≤ rho)
      (w : G.obj T ⟶ G.obj ((BigAffineFppf.inclusion B S hS).obj (DY.obj m))),
      w ≫ (colimit.ι (DY ⋙ BigAffineFppf.inclusion B S hS ⋙ G) m ≫ eY.symm.hom) = z →
      ∃ z' : G.obj T ⟶ G.obj ((BigAffineFppf.inclusion B S hS).obj (DY.obj rho)),
        z' ≫ b = z := fun T z m hm w hw =>
    ⟨w ≫ (DY ⋙ BigAffineFppf.inclusion B S hS ⋙ G).map (homOfLE hm), by
      rw [Category.assoc, ← hw]; exact congrArg (w ≫ ·) (colimit.w_assoc _ _ _)⟩
  obtain ⟨xi', hxieq⟩ := push U ξ mu hmr xi hxi
  obtain ⟨cc', hcceq⟩ := push Xlam (a ≫ f) nu hnr cc hcc
  have hbig : IsPullback (p' ≫ a) (G.map q) f (xi' ≫ b) := by rwa [hp', hxieq]
  have hsq : IsPullback p' (G.map q) cc' xi' := by
    refine isPullback_of_comp_mono b ?_
    rw [hcceq]
    exact isPullback_of_fst_eq_comp_mono hbig
  obtain ⟨P, hP⟩ := G.map_surjective p'
  obtain ⟨Cc, hCc⟩ := G.map_surjective cc'
  obtain ⟨Xi, hXi⟩ := G.map_surjective xi'
  have hsiteSq : IsPullback P q Cc Xi :=
    IsPullback.of_map_of_faithful G (by rwa [hP, hCc, hXi])
  calc ((BigFppfOver.toScheme B S hS).obj V).size
      = (pullback ((BigFppfOver.toScheme B S hS).map Cc)
          ((BigFppfOver.toScheme B S hS).map Xi)).size :=
        Scheme.size_congr (hsiteSq.map (BigFppfOver.toScheme B S hS)).isoPullback
    _ ≤ max ((BigFppfOver.toScheme B S hS).obj Xlam).size
          ((BigFppfOver.toScheme B S hS).obj U).size :=
        Scheme.size_pullback_le _ _
    _ ≤ max κ ((BigFppfOver.toScheme B S hS).obj U).size :=
        max_le_max (hstage lam) le_rfl

/-- **Stacks 0AKN.** Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y`
be a morphism of affine formal algebraic spaces over `S` which is representable by algebraic
spaces. Then `f` is representable by schemes and affine: every base change of `f` along a
morphism to `Y` from a sheaf represented by an object of the site is represented by an object of
the site, and the induced morphism of underlying schemes is affine. -/
@[stacks 0AKN]
theorem relative_isAffineHom_of_isRepresentableByAlgebraicSpaces
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  have : FunctorToTypes.Small.{u} X.obj :=
    CartesianColimit.small_of_setTheoreticCondition B S hS X hX.1
  obtain ⟨κ, hκ, hbase⟩ :=
    exists_size_bound_affine_baseChange_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hf
  have hisoA : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact CartesianColimit.relative_of_affineBaseChanges B S hS (@IsAffineHom.{u})
    (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine)
    f hκ hbase

/-! ### From Stacks 0AKN to finite type -/

/-- A morphism of fppf sheaves on the big fppf site of `S` every represented base change of
which is a morphism of the site with a property `P` has an underlying morphism of presheaves
with the same property against universe-lifted scheme-valued points. -/
theorem relative_ulift_of_relative_sheaf
    (P : MorphismProperty (BigFppfOver B S hS)) [P.RespectsIso]
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : Y ⟶ X)
    (hf : P.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f) :
    P.relative (uliftYoneda.{u + 1}) f.hom := by
  let K := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let G := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let e := CartesianColimit.sheafifiedYonedaToUliftPresheafIso B S hS
  apply MorphismProperty.relative.of_exists
  intro U ξ
  let ξ' : G.obj U ⟶ X := K.preimage ((e.app U).hom ≫ ξ)
  have hξ : K.map ξ' = (e.app U).hom ≫ ξ := K.map_preimage _
  let V := hf.rep.pullback ξ'
  let p := hf.rep.fst ξ'
  let q := hf.rep.snd ξ'
  refine ⟨V, (e.app V).inv ≫ K.map p, q, ?_, hf.property_snd ξ'⟩
  apply ((hf.rep.isPullback ξ').map K).of_iso (e.app V) (Iso.refl _)
    (e.app U) (Iso.refl _)
  · rw [Iso.refl_hom, Category.comp_id]
    exact (Iso.hom_inv_id_assoc (e.app V) (K.map p)).symm
  · exact e.hom.naturality q
  · simp [K]
  · exact (Category.comp_id _).trans hξ

/-- **A morphism of affine formal algebraic spaces over `S` which is locally of finite type is
of finite type.** Here locally of finite type is part (1) of **Stacks 0AM4** and finite type is
part (2) of Stacks 0AM4, in the form of **Stacks 0AJJ**. -/
theorem IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal
    {X Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Y)
    (hX : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS X)
    (hY : _root_.AlgebraicGeometry.IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsFiniteType B S hS f := by
  have : MorphismProperty.RespectsIso (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let L := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  obtain ⟨hrep, hlft⟩ := hf
  have haff := relative_ulift_of_relative_sheaf B S hS
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f
    (relative_isAffineHom_of_isRepresentableByAlgebraicSpaces B S hS f hX hY hrep)
  refine ⟨hrep, fun U ξ ↦ ⟨hlft U ξ, ?_⟩⟩
  have : IsAffineHom ((BigFppfOver.toScheme B S hS).map (haff.rep.snd ξ)) :=
    haff.property_snd ξ
  have hqc : Space.IsQuasiCompactULift.{u + 1} B S hS (L.map (haff.rep.snd ξ)) :=
    Space.isQuasiCompactULift_uliftYoneda_map B S hS (haff.rep.snd ξ) inferInstance
  have hfst : (haff.rep.isPullback ξ).flip.isoPullback.hom ≫ pullback.fst ξ f.hom =
      L.map (haff.rep.snd ξ) := (haff.rep.isPullback ξ).flip.isoPullback_hom_fst
  have h2 : Space.IsQuasiCompactULift.{u + 1} B S hS
      ((haff.rep.isPullback ξ).flip.isoPullback.inv ≫ L.map (haff.rep.snd ξ)) :=
    Space.isQuasiCompactULift_precomp B S hS
      (haff.rep.isPullback ξ).flip.isoPullback.symm (L.map (haff.rep.snd ξ)) hqc
  rwa [(Iso.inv_comp_eq _).mpr hfst.symm] at h2

end AlgebraicGeometry.FormalSpace

end
