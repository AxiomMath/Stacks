module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductQuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints

/-!
# A morphism out of a finite coproduct of algebraic spaces is universally closed

Let a sheaf `P` on the big fppf site over `S` be the coproduct of finitely many algebraic
spaces over `S` with legs `ι i`, and let `f : P ⟶ Y` be a morphism to an algebraic space over
`S`. If every restriction `ι i ≫ f` is universally closed in the sense of Stacks 03HI, then so
is `f`.

Two steps. First, closedness on points: the ranges of the legs cover the point space of the
coproduct (`AlgebraicGeometry.Space.isZariskiCover_range_cofan_inj` together with
`AlgebraicGeometry.Space.isZariskiCover_iff_iUnion_points`), so the image of a closed set under
the map on points of `f` is the *finite* union of the images under the maps on points of the
restrictions, of the preimages of that closed set; each of those is closed, and a finite union
of closed sets is closed. Second, universality: a base change of the coproduct is the coproduct
of the base changes of the summands
(`AlgebraicGeometry.Space.isColimitCofanMkPullback`), so the first step applies to it.

## Main results

* `AlgebraicGeometry.Space.isClosedMorphism_of_isColimit_cofan`: a morphism out of a finite
  coproduct is closed on points as soon as its restrictions are.
* `AlgebraicGeometry.Space.universallyClosed_of_isColimit_cofan`: the same for universal
  closedness.
* `AlgebraicGeometry.Space.isProper_of_isColimit_cofan_of_isSeparated`: properness of such a
  morphism, with its *separatedness* carried as a hypothesis.

The scheme-level statement that `coprod.desc` of two proper morphisms is proper is
`AlgebraicGeometry.isProper_coprodDesc`. Of the three clauses of Stacks 03ZM for its analogue
for algebraic spaces, the finite-type clause is
`AlgebraicGeometry.Space.isFiniteType_of_isColimit_cofan` and the universally-closed clause is
`AlgebraicGeometry.Space.universallyClosed_of_isColimit_cofan`. The separatedness clause, that
the relative diagonal of the glued morphism is a closed immersion, is
`AlgebraicGeometry.Space.isSeparated_of_isColimit_cofan` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/CoproductSeparated.lean`, which combines the
three into `AlgebraicGeometry.Space.isProper_of_isColimit_cofan`.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology AlgebraicGeometry.BigFppfOver.hasSheafify_type

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_coproductUniversallyClosed
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of sheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_sheaf_coproductUniversallyClosed :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type u)) := inferInstance

private instance (priority := high) hasPullback_sheaf_coproductUniversallyClosed
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type u)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **A morphism out of a finite coproduct of algebraic spaces over `S` is closed on points as
soon as its restrictions to the summands are.** -/
theorem isClosedMorphism_of_isColimit_cofan {I : Type u} [Finite I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : P.obj ⟶ Z)
    (hm : ∀ i, IsClosedMorphism B S hS ((ι i).hom ≫ m)) :
    IsClosedMorphism B S hS m := by
  have hcover : IsZariskiCover B S hS I fun i ↦ Subfunctor.range (ι i).hom :=
    isZariskiCover_range_cofan_inj ι hP hF
  have hpoints := (isZariskiCover_iff_iUnion_points B S hS P.obj hPalg I _ hcover.1).mp hcover
  have hrange : ∀ i, Set.range (pointsMap B S hS (Subfunctor.range (ι i).hom).toFunctor
      (Subfunctor.range (ι i).hom).ι) =
      Set.range (pointsMap B S hS (F i).obj (ι i).hom) := by
    intro i
    have hmono : Mono (ι i).hom := Sheaf.mono_hom_cofan_inj ι hP i
    have h1 : pointsMap B S hS (F i).obj (ι i).hom =
        pointsMap B S hS (Subfunctor.range (ι i).hom).toFunctor
            (Subfunctor.range (ι i).hom).ι ∘
          pointsMap B S hS (F i).obj (Subfunctor.toRange (ι i).hom) := by
      rw [← pointsMap_comp, Subfunctor.toRange_ι]
    rw [h1, Set.range_comp, Set.range_eq_univ.mpr (pointsMap_surjective_of_isIso B S hS
      (Subfunctor.toRange (ι i).hom)), Set.image_univ]
  have hsurj : ∀ y : points B S hS P.obj,
      ∃ i, ∃ x, pointsMap B S hS (F i).obj (ι i).hom x = y := by
    intro y
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.1 hpoints y
    exact ⟨i, by rwa [hrange i] at hi⟩
  intro C hC
  have himg : pointsMap B S hS P.obj m '' C =
      ⋃ i, pointsMap B S hS (F i).obj ((ι i).hom ≫ m) ''
        (pointsMap B S hS (F i).obj (ι i).hom ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨i, x, hx⟩ := hsurj c
      exact Set.mem_iUnion.2 ⟨i, x, by rwa [Set.mem_preimage, hx],
        by simp only [pointsMap_comp, Function.comp_apply, hx]⟩
    · intro h
      obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.1 h
      refine ⟨pointsMap B S hS (F i).obj (ι i).hom x, hx, ?_⟩
      rw [pointsMap_comp]
      rfl
  rw [himg]
  exact isClosed_iUnion_of_finite fun i ↦
    hm i _ (hC.preimage (continuous_pointsMap B S hS (ι i).hom))

/-- If two pullback squares over the same cospan have closed map on points for the first
projection of one, then so does the other. -/
private theorem isClosedMap_of_isPullback_of_isPullback
    {A A' X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : A ⟶ Z} {b : A ⟶ X} {a' : A' ⟶ Z} {b' : A' ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback a b g f) (h' : IsPullback a' b' g f)
    (ha : IsClosedMap (pointsMap B S hS A' a')) : IsClosedMap (pointsMap B S hS A a) :=
  isClosedMap_pointsMap_of_comp_isIso B S hS (h.isoIsPullback _ _ h').hom
    (h.isoIsPullback_hom_fst _ _ h') ha

/-- **A morphism out of a finite coproduct of algebraic spaces over `S` is universally closed
as soon as its restrictions to the summands are.** A base change of the coproduct is the
coproduct of the base changes of the summands
(`AlgebraicGeometry.Space.isColimitCofanMkPullback`), on each of which the first projection is
closed on points by hypothesis, so
`AlgebraicGeometry.Space.isClosedMorphism_of_isColimit_cofan` applies. -/
theorem universallyClosed_of_isColimit_cofan {I : Type u} [Finite I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hf : ∀ i, UniversallyClosed B S hS ((ι i).hom ≫ f)) :
    UniversallyClosed B S hS f := by
  intro Z hZ g
  let gs : (⟨Z, hZ.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
    ⟨Y, hY.isSheaf⟩ := ObjectProperty.homMk g
  let fs : P ⟶ (⟨Y, hY.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    ObjectProperty.homMk f
  let t : pullback gs fs ⟶ P := pullback.snd gs fs
  have hsq : IsPullback (pullback.fst gs fs).hom t.hom g f :=
    isPullback_hom_of_sheaf (IsPullback.of_hasPullback gs fs)
  let eA : pullback g f ≅ (pullback gs fs).obj :=
    (IsPullback.of_hasPullback g f).isoIsPullback _ _ hsq
  have hpaste : ∀ i, IsPullback ((pullback.snd (ι i) t).hom ≫ (pullback.fst gs fs).hom)
      (pullback.fst (ι i) t).hom g ((ι i).hom ≫ f) := fun i ↦
    (isPullback_hom_of_sheaf (IsPullback.of_hasPullback (ι i) t)).flip.paste_horiz hsq
  let eP : ∀ i, pullback g ((ι i).hom ≫ f) ≅ (pullback (ι i) t).obj := fun i ↦
    (IsPullback.of_hasPullback g ((ι i).hom ≫ f)).isoIsPullback _ _ (hpaste i)
  have hialg : ∀ i, IsAlgebraicSpace B S hS (pullback (ι i) t).obj := fun i ↦
    (isAlgebraicSpace_pullback B S hS g ((ι i).hom ≫ f) hZ (hF i) hY).of_iso (eP i)
  have hAalg : IsAlgebraicSpace B S hS (pullback gs fs).obj :=
    (isAlgebraicSpace_pullback B S hS g f hZ hPalg hY).of_iso eA
  have hm : ∀ i, IsClosedMorphism B S hS
      ((pullback.snd (ι i) t).hom ≫ (pullback.fst gs fs).hom) := fun i ↦
    isClosedMap_of_isPullback_of_isPullback B S hS (hpaste i) (IsPullback.of_hasPullback _ _)
      (hf i Z hZ g)
  exact isClosedMap_of_isPullback_of_isPullback B S hS (IsPullback.of_hasPullback g f) hsq
    (isClosedMorphism_of_isColimit_cofan B S hS (fun i ↦ pullback.snd (ι i) t)
      (isColimitCofanMkPullback B S hS ι hP t) hialg hAalg (pullback.fst gs fs).hom hm)

/-- **A morphism out of a finite coproduct of algebraic spaces over `S` whose restrictions to
the summands are proper is proper, provided it is separated.** This is the space-level analogue
of `AlgebraicGeometry.isProper_coprodDesc`, with the separatedness clause of Stacks 03ZM
carried as a hypothesis: the finite-type clause is
`AlgebraicGeometry.Space.isFiniteType_of_isColimit_cofan` and the universally-closed clause is
`AlgebraicGeometry.Space.universallyClosed_of_isColimit_cofan`, both of which hold
unconditionally.

The hypothesis `hsep` is one of the three conjuncts of `AlgebraicGeometry.Space.IsProper`; what
is proved here is the conjunction of the other two. -/
theorem isProper_of_isColimit_cofan_of_isSeparated {I : Type u} [Finite I]
    {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι))
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i).obj)
    (hPalg : IsAlgebraicSpace B S hS P.obj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : P.obj ⟶ Y)
    (hsep : IsSeparated B S hS f) (hf : ∀ i, IsProper B S hS ((ι i).hom ≫ f)) :
    IsProper B S hS f :=
  ⟨hsep,
    isFiniteType_of_isColimit_cofan B S hS ι hP hF hPalg hY f fun i ↦ (hf i).2.1,
    universallyClosed_of_isColimit_cofan B S hS ι hP hF hPalg hY f fun i ↦ (hf i).2.2⟩

end AlgebraicGeometry.Space

end
