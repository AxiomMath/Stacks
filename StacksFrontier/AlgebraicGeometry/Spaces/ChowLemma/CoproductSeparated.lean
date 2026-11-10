module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproductSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae

/-!
# A morphism out of a coproduct of algebraic spaces is separated

Let a sheaf `P` on the big fppf site over `S` be the coproduct of a family of algebraic spaces
over `S` with legs `ι i`, and let `f : P ⟶ Y` be a morphism to an algebraic space over `S`. If
every restriction `ι i ≫ f` is separated in the sense of Stacks 03HL, then so is `f`.

The relative diagonal of `f` is tested over the Zariski covering of `P ×_Y P` by the clopen
pieces `F i ×_Y P`, the `i`-th being the base change of `ι i` along the first projection. Over
the `i`-th piece the base change of the diagonal of `f` is the graph `F i ⟶ F i ×_Y P` of
`ι i`, which factors as the diagonal of `ι i ≫ f` followed by the base change of `ι i` along
the second projection of `F i ×_Y P`; both factors are closed immersions, the first by
hypothesis and the second because a coproduct inclusion is a closed immersion (Stacks 0F15).

## Main definitions

* `AlgebraicGeometry.Space.cofanSelfProdInj` is the `i`-th piece `F i ×_Y P ⟶ P ×_Y P` of the
  decomposition of the self-product.
* `AlgebraicGeometry.Space.cofanGraph` is the graph `F i ⟶ F i ×_Y P` of `ι i`.
* `AlgebraicGeometry.Space.cofanDiagonalPiece` is the base change
  `F i ×_Y F i ⟶ F i ×_Y P` of `ι i`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isColimit_cofan`: a morphism out of a coproduct of
  algebraic spaces over `S` is separated as soon as its restrictions to the summands are. No
  finiteness of the index type is needed.
* `AlgebraicGeometry.Space.isProper_of_isColimit_cofan`: properness of such a morphism, with no
  hypothesis beyond properness of the restrictions. This is the space-level analogue of
  `AlgebraicGeometry.isProper_coprodDesc`, and it discharges the separatedness hypothesis
  `hsep` of `AlgebraicGeometry.Space.isProper_of_isColimit_cofan_of_isSeparated`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0F15](https://stacks.math.columbia.edu/tag/0F15)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance (priority := high) hasPullback_presheaf_coproductSeparated
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Pieces

variable {I : Type u} {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The `i`-th piece `F i ×_Y P ⟶ P ×_Y P` of the decomposition of the self-product of
`f : P ⟶ Y` along a coproduct decomposition of `P`: it is the base change of the leg `ι i`
along the first projection. -/
def cofanSelfProdInj (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    pullback ((ι i).hom ≫ f) f ⟶ pullback f f :=
  pullback.lift (pullback.fst ((ι i).hom ≫ f) f ≫ (ι i).hom)
    (pullback.snd ((ι i).hom ≫ f) f) (by rw [Category.assoc]; exact pullback.condition)

/-- The graph `F i ⟶ F i ×_Y P` of the leg `ι i`: the morphism whose first component is the
identity and whose second component is `ι i`. -/
def cofanGraph (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    (F i).obj ⟶ pullback ((ι i).hom ≫ f) f :=
  pullback.lift (𝟙 _) (ι i).hom (Category.id_comp _)

/-- The base change `F i ×_Y F i ⟶ F i ×_Y P` of the leg `ι i` along the second projection. -/
def cofanDiagonalPiece (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    pullback ((ι i).hom ≫ f) ((ι i).hom ≫ f) ⟶ pullback ((ι i).hom ≫ f) f :=
  pullback.lift (pullback.fst ((ι i).hom ≫ f) ((ι i).hom ≫ f))
    (pullback.snd ((ι i).hom ≫ f) ((ι i).hom ≫ f) ≫ (ι i).hom)
    (by rw [Category.assoc]; exact pullback.condition)

/-- **The `i`-th piece of the self-product is the base change of the `i`-th leg along the first
projection.** -/
theorem isPullback_cofanSelfProdInj (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    IsPullback (pullback.fst ((ι i).hom ≫ f) f) (cofanSelfProdInj B S hS ι f i)
      (ι i).hom (pullback.fst f f) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback f f)
  · simpa [cofanSelfProdInj, pullback.lift_snd] using IsPullback.of_hasPullback ((ι i).hom ≫ f) f
  · exact (pullback.lift_fst _ _ _).symm

/-- **The graph of the `i`-th leg is the base change of the diagonal of `f` over the `i`-th
piece of the self-product.** -/
theorem isPullback_cofanGraph (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    IsPullback (ι i).hom (cofanGraph B S hS ι f i) (pullback.diagonal f)
      (cofanSelfProdInj B S hS ι f i) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_cofanSelfProdInj B S hS ι f i).flip
  · have h : cofanGraph B S hS ι f i ≫ pullback.fst ((ι i).hom ≫ f) f = 𝟙 _ :=
      pullback.lift_fst _ _ _
    rw [h, pullback.diagonal_fst]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  · refine pullback.hom_ext ?_ ?_ <;>
      simp [cofanGraph, cofanSelfProdInj]

/-- **The `i`-th diagonal piece is the base change of the `i`-th leg along the second
projection.** -/
theorem isPullback_cofanDiagonalPiece (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    IsPullback (cofanDiagonalPiece B S hS ι f i)
      (pullback.snd ((ι i).hom ≫ f) ((ι i).hom ≫ f))
      (pullback.snd ((ι i).hom ≫ f) f) (ι i).hom := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback ((ι i).hom ≫ f) f)
  · simpa [cofanDiagonalPiece, pullback.lift_fst] using
      IsPullback.of_hasPullback ((ι i).hom ≫ f) ((ι i).hom ≫ f)
  · exact pullback.lift_snd _ _ _

/-- **The graph of the `i`-th leg factors through the `i`-th diagonal piece**, the first factor
being the relative diagonal of `ι i ≫ f`. -/
theorem cofanGraph_eq (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I) :
    cofanGraph B S hS ι f i
      = pullback.diagonal ((ι i).hom ≫ f) ≫ cofanDiagonalPiece B S hS ι f i := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [cofanGraph, cofanDiagonalPiece]

/-- **The graph of the `i`-th leg is a closed immersion** as soon as `ι i ≫ f` is separated and
the leg `ι i` is a closed immersion. -/
theorem isClosedImmersion_cofanGraph (ι : ∀ i, F i ⟶ P) (f : P.obj ⟶ Y) (i : I)
    (hsep : IsSeparated B S hS ((ι i).hom ≫ f))
    (hι : IsClosedImmersion B S hS (ι i).hom) :
    IsClosedImmersion B S hS (cofanGraph B S hS ι f i) := by
  have hpiece : IsClosedImmersion B S hS (cofanDiagonalPiece B S hS ι f i) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (isPullback_cofanDiagonalPiece B S hS ι f i).flip hι
  rw [cofanGraph_eq B S hS ι f i]
  exact isClosedImmersion_comp B S hS _ _ hsep hpiece

/-! ### Separatedness of a morphism out of a coproduct -/

/-- **A morphism out of a coproduct of algebraic spaces over `S` is separated as soon as its
restrictions to the summands are.** There is no finiteness hypothesis on the index type.

The self-product `P ×_Y P` is itself a coproduct, of the pieces
`AlgebraicGeometry.Space.cofanSelfProdInj`, by
`AlgebraicGeometry.Space.nonempty_isColimit_cofanMk_of_isPullback`, so the ranges of those
pieces are a Zariski covering of it
(`AlgebraicGeometry.Space.isZariskiCover_range_cofan_inj`). Closed immersions of schemes being
Zariski local at the target, it is enough to check the base change of the relative diagonal of
`f` over each piece, by the implication (5) ⇒ (1) of Stacks 03M4 in the form
`AlgebraicGeometry.Space.presheaf_of_zariskiCover_presheaf_pullback_snd`. That base change is
the graph `AlgebraicGeometry.Space.cofanGraph` of the `i`-th leg, a closed immersion by
`AlgebraicGeometry.Space.isClosedImmersion_cofanGraph`. -/
theorem isSeparated_of_isColimit_cofan {I : Type u}
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, IsSeparated B S hS ((ι i).hom ≫ f)) :
    IsSeparated B S hS f := by
  have hDalg : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS f f hPalg hPalg hY
  have hAalg : ∀ i, IsAlgebraicSpace B S hS (pullback ((ι i).hom ≫ f) f) := fun i =>
    isAlgebraicSpace_pullback B S hS ((ι i).hom ≫ f) f (hF i) hPalg hY
  -- the self-product and its pieces, read in the category of sheaves
  let A : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨pullback f f, hDalg.isSheaf⟩
  let As : I → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun i =>
    ⟨pullback ((ι i).hom ≫ f) f, (hAalg i).isSheaf⟩
  let t : A ⟶ P := ⟨pullback.fst f f⟩
  let pr : ∀ i, As i ⟶ A := fun i => ⟨cofanSelfProdInj B S hS ι f i⟩
  let qr : ∀ i, As i ⟶ F i := fun i => ⟨pullback.fst ((ι i).hom ≫ f) f⟩
  have hsq : ∀ i, IsPullback (pr i) (qr i) t (ι i) := fun i =>
    isPullback_sheaf_of_hom (isPullback_cofanSelfProdInj B S hS ι f i).flip
  have hcolim : IsColimit (Cofan.mk A pr) :=
    (nonempty_isColimit_cofanMk_of_isPullback B S hS ι hP t pr qr hsq).some
  have hcover : IsZariskiCover B S hS I
      fun i => Subfunctor.range (cofanSelfProdInj B S hS ι f i) :=
    isZariskiCover_range_cofan_inj pr hcolim hAalg
  refine presheaf_of_zariskiCover_presheaf_pullback_snd B S hS
    (inferInstance :
      IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}))
    hPalg hDalg hcover fun i => ?_
  have hmono : Mono (cofanSelfProdInj B S hS ι f i) :=
    Sheaf.mono_hom_cofan_inj pr hcolim i
  have hiso : IsIso (Subfunctor.toRange (cofanSelfProdInj B S hS ι f i)) := inferInstance
  have hbig : IsPullback (ι i).hom
      (cofanGraph B S hS ι f i ≫ Subfunctor.toRange (cofanSelfProdInj B S hS ι f i))
      (pullback.diagonal f)
      (Subfunctor.range (cofanSelfProdInj B S hS ι f i)).ι := by
    have h0 := (isPullback_cofanGraph B S hS ι f i).paste_vert
      (IsPullback.of_vert_isIso (f := 𝟙 (pullback f f))
        (g := (Subfunctor.range (cofanSelfProdInj B S hS ι f i)).ι)
        ⟨by rw [Category.comp_id, Subfunctor.toRange_ι]⟩)
    rwa [Category.comp_id] at h0
  rw [← hbig.isoPullback_inv_snd]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ _ _
      (isClosedImmersion_cofanGraph B S hS ι f i (hf i)
        (coproductIncl_isClosedImmersion B S hS F P ι hP i)))

/-! ### Properness of a morphism out of a finite coproduct -/

/-- **A morphism out of a finite coproduct of algebraic spaces over `S` whose restrictions to
the summands are proper is proper.** This is the space-level analogue of
`AlgebraicGeometry.isProper_coprodDesc`, with no hypothesis left over: the separatedness clause
of Stacks 03ZM is `AlgebraicGeometry.Space.isSeparated_of_isColimit_cofan`, the finite-type
clause is `AlgebraicGeometry.Space.isFiniteType_of_isColimit_cofan` and the universally-closed
clause is `AlgebraicGeometry.Space.universallyClosed_of_isColimit_cofan`.

It is `AlgebraicGeometry.Space.isProper_of_isColimit_cofan_of_isSeparated` with its hypothesis
`hsep` discharged. -/
theorem isProper_of_isColimit_cofan {I : Type u} [Finite I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, IsProper B S hS ((ι i).hom ≫ f)) :
    IsProper B S hS f :=
  isProper_of_isColimit_cofan_of_isSeparated B S hS ι hP hF hPalg hY f
    (isSeparated_of_isColimit_cofan B S hS ι hP hF hPalg hY f fun i => (hf i).1) hf

end Pieces

end AlgebraicGeometry.Space

end
