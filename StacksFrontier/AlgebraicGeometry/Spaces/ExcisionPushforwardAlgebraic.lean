module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerModification
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizedBlowupLiftFromNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcision
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The presheaf of pairs is an algebraic space

Keep the data of `StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforwardBaseChange.lean`: a
separated étale morphism `f : V ⟶ W` of algebraic spaces over a scheme `S`, a closed subspace
`T` of `W` whose preimage is carried isomorphically onto it, a subfunctor `W₀` containing the
open complement of `T`, and `h : Y ⟶ V` which becomes an isomorphism over `f^{-1}W₀`.

The presheaf of pairs `X` of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionPushforward.lean` is an algebraic space over `S`.
This is the last step of the proof of Stacks 0BGY, and with it the base-change functor of that
tag is essentially surjective.

The source covers `X` by `W⁰ ⨿ V`. Here the covering is by two *open* subspaces of `X`, namely
the inverse images of the open complement `W⁰` of `T` and of the open image `I` of `f`; that
replacement of the étale covering `{W⁰ → W, V → W}` by a Zariski one is
`AlgebraicGeometry.Space.exists_openImage_isZariskiCover_openComplement`. Over `W⁰` the
presheaf of pairs is `W⁰` itself, and over `I` it is covered by `Y ×_V U` for the scheme chart
`U ⟶ I` which that lemma carries.

## Main results

* `AlgebraicGeometry.Space.sheafify_iSup_preimage_eq_top`: a locally covering family of
  subfunctors of the target pulls back to a locally covering family of subfunctors of the
  source.
* `AlgebraicGeometry.Space.isSheaf_preimage`: the inverse image of a subfunctor which is a
  sheaf, inside a presheaf which is a sheaf, is a sheaf.
* `AlgebraicGeometry.Space.isAlgebraicSpace_preimage_of_isPullback`: a presheaf over `W` whose
  base change along `f` is an algebraic space is one over any open subspace of `W` carrying a
  surjective étale chart that factors through `f` — applied here to the open image of `f`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_excisionSpace`: **the presheaf of pairs is an
  algebraic space.**

## Implementation notes

The part lying over the open image is handled by the étale atlas criterion **Stacks 0BGR**
rather than by a second open cover. Its chart is `Y ×_V U`, and the morphism from it is
obtained by pasting three cartesian squares: the fibre product square of `h` with the chart
`a : U ⟶ V`, the identification `Y = X ×_{g, W} V` of
`AlgebraicGeometry.Space.isIso_excisionBaseChangeHom`, and the description of an inverse image
as a fibre product (**Stacks 083Q**). The last of the three is cancelled off with
`CategoryTheory.IsPullback.of_bot'`, whose conclusion *is* the morphism to the inverse image,
so that no comparison of two independently built morphisms is needed. Surjectivity and
étaleness of the chart `U ⟶ I` then transfer to it because the relative form of a morphism
property is stable under base change.

The two open pieces are assembled by **Stacks 02WR**,
`AlgebraicGeometry.isAlgebraicSpace_of_open_cover`, whose coproduct hypothesis is discharged
by `CategoryTheory.Limits.coproductIsCoproduct` and whose coproduct is an algebraic space by
**Stacks 040T**. Local surjectivity of the covering map is reduced to the statement that the
two inverse images cover `X` locally, which is the corresponding statement for `W⁰` and `I`
inside `W` transported along the projection: membership of a section in an inverse image is
membership of its image, so the two sieves cut out are literally equal.

Separatedness of `f` is not used by the covering; it enters only through
`AlgebraicGeometry.Space.excisionUnit`, which is built from the amalgamation over the fibre
square.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 040T](https://stacks.math.columbia.edu/tag/040T)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Covering families and their inverse images -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheafification of subfunctors is monotone. -/
theorem sheafify_le_sheafify {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G G' : Subfunctor F}
    (hle : G ≤ G') :
    G.sheafify (BigFppfOver.topology B S hS) ≤ G'.sheafify (BigFppfOver.topology B S hS) :=
  fun _ _ hx => (BigFppfOver.topology B S hS).superset_covering (fun _ _ hk => hle _ hk) hx

/-- **A Zariski covering family has locally covering supremum**: the supremum of the members
sheafifies to the whole of the covered presheaf.

The covering map out of the coproduct factors through the inclusion of the supremum, because
each member does, so its range is contained in the supremum. -/
theorem sheafify_iSup_eq_top_of_isZariskiCover {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (I : Type u) (Ui : I → Subfunctor F) (hUi : IsZariskiCover B S hS I Ui) :
    (⨆ i, Ui i).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  have hls := hUi.2
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top'] at hls
  have hrange (i : I) : Subfunctor.range (Ui i).ι ≤ ⨆ j, Ui j :=
    (Subfunctor.range_ι (Ui i)).le.trans (le_iSup Ui i)
  have hfac : (Limits.Sigma.desc fun i ↦ Subfunctor.lift (Ui i).ι (hrange i)) ≫ (⨆ j, Ui j).ι =
      Limits.Sigma.desc fun i ↦ (Ui i).ι := by
    refine Limits.Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc, Limits.Sigma.ι_comp_desc, Subfunctor.lift_ι]
  have hle : Subfunctor.range (Limits.Sigma.desc fun i ↦ (Ui i).ι) ≤ ⨆ j, Ui j := by
    rw [← hfac]
    exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le
  exact top_le_iff.1 (hls ▸ sheafify_le_sheafify B S hS hle)

/-- **Inverse images of a locally covering family are locally covering.** Membership of a
section in the inverse image of a subfunctor is membership of its image, so the two sieves cut
out by a section coincide. -/
theorem sheafify_iSup_preimage_eq_top {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F' ⟶ F)
    {I : Type*} (Ui : I → Subfunctor F)
    (hUi : (⨆ i, Ui i).sheafify (BigFppfOver.topology B S hS) = ⊤) :
    (⨆ i, (Ui i).preimage p).sheafify (BigFppfOver.topology B S hS) = ⊤ := by
  rw [eq_top_iff]
  intro A s _
  have hsieve : (⨆ i, (Ui i).preimage p).sieveOfSection s =
      (⨆ i, Ui i).sieveOfSection (p.app A s) := by
    ext C k
    change (F'.map k.op s ∈ (⨆ i, (Ui i).preimage p).obj (op C)) ↔
      (F.map k.op (p.app A s) ∈ (⨆ i, Ui i).obj (op C))
    simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.preimage_obj,
      Set.mem_preimage, NatTrans.naturality_apply]
  have hmem : p.app A s ∈ ((⨆ i, Ui i).sheafify (BigFppfOver.topology B S hS)).obj A := by
    rw [hUi]
    trivial
  change (⨆ i, (Ui i).preimage p).sieveOfSection s ∈ BigFppfOver.topology B S hS A.unop
  rw [hsieve]
  exact hmem

/-- **The inverse image of a subfunctor which is a sheaf is a sheaf.** A section of the source
lying locally in the inverse image has its image lying locally in the subfunctor, hence in it. -/
theorem isSheaf_preimage {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F' ⟶ F)
    (G : Subfunctor F) (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hF' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F')
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.toFunctor) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G.preimage p).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type] at hF hF' hG ⊢
  rw [Subfunctor.isSheaf_iff _ hF']
  rw [Subfunctor.isSheaf_iff _ hF] at hG
  intro A s hs
  change p.app A s ∈ G.obj A
  refine hG A (p.app A s)
    ((BigFppfOver.topology B S hS).superset_covering (fun C k hk => ?_) hs)
  have hk' : p.app (op C) (F'.map k.op s) ∈ G.obj (op C) := hk
  change F.map k.op (p.app A s) ∈ G.obj (op C)
  rwa [← NatTrans.naturality_apply p k.op s]

/-! ### Algebraicity from a Zariski covering of the base -/

/-- **A sheaf over a presheaf with a Zariski covering is an algebraic space as soon as the
inverse image of each member is.** The inverse images are open subspaces, because an inverse
image is a fibre product by **Stacks 083Q**, and they cover the sheaf locally because the
members cover the base locally; **Stacks 02WR** assembles them, its coproduct being an
algebraic space by **Stacks 040T**. -/
theorem isAlgebraicSpace_of_isZariskiCover_preimage
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (pr : X ⟶ F)
    (I : Type u) [Finite I] (Ui : I → Subfunctor F) (hUi : IsZariskiCover B S hS I Ui)
    (hC : ∀ i, IsAlgebraicSpace B S hS ((Ui i).preimage pr).toFunctor) :
    IsAlgebraicSpace B S hS X := by
  classical
  have _ : HasColimitsOfShape (Discrete I) (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ I
  have hcovX : (⨆ i, (Ui i).preimage pr).sheafify (BigFppfOver.topology B S hS) = ⊤ :=
    sheafify_iSup_preimage_eq_top B S hS pr Ui
      (sheafify_iSup_eq_top_of_isZariskiCover B S hS I Ui hUi)
  let Fs : I → Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    fun i ↦ ⟨((Ui i).preimage pr).toFunctor, (hC i).isSheaf⟩
  let Xs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨X, hX⟩
  let gsh : ∐ Fs ⟶ Xs :=
    Limits.Sigma.desc fun i ↦ (ObjectProperty.homMk ((Ui i).preimage pr).ι : Fs i ⟶ Xs)
  let gg : (∐ Fs).obj ⟶ X := gsh.hom
  have hfac : ∀ i, (Limits.Sigma.ι Fs i).hom ≫ gg = ((Ui i).preimage pr).ι := fun i =>
    congrArg (fun k : Fs i ⟶ Xs => k.hom)
      (Limits.Sigma.ι_comp_desc
        (fun i ↦ (ObjectProperty.homMk ((Ui i).preimage pr).ι : Fs i ⟶ Xs)) i)
  refine isAlgebraicSpace_of_open_cover B S hS X hX I Fs hC (∐ Fs) (Limits.Sigma.ι Fs)
    (coproductIsCoproduct Fs) gg (fun i => ?_) ?_
    (isAlgebraicSpace_finiteCoproduct B S hS (fun i ↦ ((Ui i).preimage pr).toFunctor) hC
      (∐ Fs) (Limits.Sigma.ι Fs) (coproductIsCoproduct Fs))
  · rw [hfac i]
    exact presheaf_of_isPullback B S hS (Subfunctor.isPullback_preimage pr (Ui i)) (hUi.1 i).2
  · rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
    refine top_le_iff.1 ?_
    rw [← hcovX]
    refine sheafify_le_sheafify B S hS (iSup_le fun i => ?_)
    calc (Ui i).preimage pr = Subfunctor.range ((Ui i).preimage pr).ι :=
          (Subfunctor.range_ι _).symm
      _ = Subfunctor.range ((Limits.Sigma.ι Fs i).hom ≫ gg) := by rw [hfac i]
      _ ≤ Subfunctor.range gg := Subfunctor.range_comp_le _ _

/-! ### Inverse images of an open subspace with an étale chart -/

variable {V W : AlgebraicSpaces B S hS} (f : V ⟶ W)

/-- **A presheaf over `W` whose base change along `f` is an algebraic space is an algebraic
space over any open subspace of `W` carrying a chart which factors through `f`.**

Let `pr : X ⟶ W` have base change `Y` along `f : V ⟶ W`, let `I` be an open subspace of `W`
and let `q : U ⟶ I` be a surjective étale chart of `I` by an object of the site which factors
through `f`. Then the inverse image of `I` in `X` is an algebraic space: `Y ×_V U` is one by
**Stacks 02X2**, the morphism from it to the inverse image is the base change of `q` along the
morphism from the inverse image to `I`, and **Stacks 0BGR** applies.

The morphism out of `Y ×_V U` is not constructed separately: the outer cartesian square over
`W` is the fibre product square of `h` with `a` pasted onto the one for `pr` and `f`, and
`CategoryTheory.IsPullback.of_bot'` cancels off the square **Stacks 083Q** exhibiting the
inverse image as a fibre product, producing the morphism together with the proof that it is a
base change of `q`. -/
theorem isAlgebraicSpace_preimage_of_isPullback
    {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (pr : X ⟶ W.obj) (eu : Z ⟶ X) (h : Z ⟶ V.obj) (hsq : IsPullback eu h pr f.hom)
    (hZ : IsAlgebraicSpace B S hS Z)
    (Im : Subfunctor W.obj) (hIm : IsOpenSubspace B S hS Im) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ V.obj) (q : yoneda.obj U ⟶ Im.toFunctor)
    (hq : q ≫ Im.ι = a ≫ f.hom) (hqsurj : IsSurjective B S hS q)
    (hqetale : IsEtale B S hS q) :
    IsAlgebraicSpace B S hS (Im.preimage pr).toFunctor := by
  have hs : IsPullback (pullback.snd h a) (pullback.fst h a ≫ eu) (q ≫ Im.ι) pr := by
    rw [hq]
    exact ((IsPullback.of_hasPullback h a).paste_horiz hsq).flip
  have hn := IsPullback.of_bot' hs (Subfunctor.isPullback_preimage pr Im)
  exact isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS
    (isAlgebraicSpace_pullback B S hS h a hZ (isAlgebraicSpace_yoneda B S hS U) V.property)
    (isSheaf_preimage B S hS pr Im W.property.isSheaf hX hIm.1.isSheaf) _
    (presheaf_of_isPullback B S hS hn
      ((presheafSurjective_iff_isSurjective_yoneda B S hS Im.toFunctor hIm.1 U q).mpr hqsurj))
    (presheaf_of_isPullback B S hS hn (presheaf_etale_of_isEtale B S hS hqetale))

/-! ### The presheaf of pairs is an algebraic space -/

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : Y ⟶ V.obj)
  (hY : IsAlgebraicSpace B S hS Y) (T W₀ : Subfunctor W.obj)
  (hT : IsIso (T.fromPreimage f.hom)) (hcompl : openComplement B S hS T ≤ W₀)
  (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
  (hiso : IsIso (pullback.snd h (W₀.preimage f.hom).ι))

include hT hcompl hf hsep hiso in
/-- **The square expressing `X ×_{g, W} V = Y` is cartesian.** This is
`AlgebraicGeometry.Space.isIso_excisionBaseChangeHom` read as a cartesian square. -/
theorem isPullback_excisionUnit :
    IsPullback
      (excisionUnit B S hS f.hom h V.property W.property hY T W₀ hT hcompl hf hsep hiso) h
      (excisionProj B S hS f.hom h V.property W.property hY) f.hom := by
  have := isIso_excisionBaseChangeHom B S hS f.hom h V.property W.property hY T W₀ hT hcompl
    hf hsep hiso
  exact IsPullback.of_iso_pullback
    ⟨excisionUnit_comp_excisionProj B S hS f.hom h V.property W.property hY T W₀ hT hcompl hf
      hsep hiso⟩
    (asIso (excisionBaseChangeHom B S hS f.hom h V.property W.property hY T W₀ hT hcompl hf
      hsep hiso))
    (excisionBaseChangeHom_fst B S hS f.hom h V.property W.property hY T W₀ hT hcompl hf
      hsep hiso)
    (excisionBaseChangeHom_snd B S hS f.hom h V.property W.property hY T W₀ hT hcompl hf
      hsep hiso)

include hcompl hiso in
/-- **The presheaf of pairs is unchanged over the open complement of `T`.** The projection out
of the inverse image of the open complement is an isomorphism, so that inverse image is an
algebraic space. -/
theorem isAlgebraicSpace_preimage_openComplement_excisionProj
    (hTcl : IsClosedSubspace B S hS T) :
    IsAlgebraicSpace B S hS ((openComplement B S hS T).preimage
      (excisionProj B S hS f.hom h V.property W.property hY)).toFunctor := by
  have hle : (openComplement B S hS T).preimage f.hom ≤ W₀.preimage f.hom :=
    fun _ _ hx => hcompl _ hx
  have := isIso_fromPreimage_of_isIso_pullback_snd
    (excisionProj B S hS f.hom h V.property W.property hY) (openComplement B S hS T)
    (isIso_pullback_snd_excisionProj B S hS f.hom h V.property W.property hY
      (openComplement B S hS T)
      (isIso_pullback_snd_of_factor h (Subfunctor.homOfLe hle)
        (Subfunctor.homOfLe_ι hle) hiso))
  exact (isOpenSubspace_openComplement B S hS W.property T hTcl).1.of_iso
    (asIso ((openComplement B S hS T).fromPreimage
      (excisionProj B S hS f.hom h V.property W.property hY))).symm

include hY hT hcompl hf hsep hiso in
/-- **The presheaf of pairs of the proof of Stacks 0BGY is an algebraic space.**

The open complement `W⁰` of `T` and the open image `I` of `f` form a Zariski covering of `W`,
so their inverse images form a locally covering family of open subspaces of the presheaf of
pairs. Over `W⁰` the presheaf of pairs is `W⁰` itself, by
`AlgebraicGeometry.Space.isAlgebraicSpace_preimage_openComplement_excisionProj`; over `I` it is
an algebraic space by `AlgebraicGeometry.Space.isAlgebraicSpace_preimage_of_isPullback`. -/
theorem isAlgebraicSpace_excisionSpace (hTcl : IsClosedSubspace B S hS T) :
    IsAlgebraicSpace B S hS (excisionSpace B S hS f.hom h V.property W.property hY) := by
  classical
  obtain ⟨Im, hImopen, U, a, q, hq, hqsurj, hqetale, hcov⟩ :=
    exists_openImage_isZariskiCover_openComplement B S hS f T hTcl hT hf
  obtain ⟨Wi, hWitrue, hWifalse, hcovW⟩ :
      ∃ Wi : ULift.{u} Bool → Subfunctor W.obj,
        Wi ⟨true⟩ = openComplement B S hS T ∧ Wi ⟨false⟩ = Im ∧
          IsZariskiCover B S hS (ULift.{u} Bool) Wi :=
    ⟨_, rfl, rfl, hcov⟩
  refine isAlgebraicSpace_of_isZariskiCover_preimage B S hS
    (isSheaf_excisionSpace B S hS f.hom h V.property W.property hY)
    (excisionProj B S hS f.hom h V.property W.property hY) (ULift.{u} Bool) Wi hcovW ?_
  rintro ⟨_ | _⟩
  · rw [hWifalse]
    exact isAlgebraicSpace_preimage_of_isPullback B S hS f
      (isSheaf_excisionSpace B S hS f.hom h V.property W.property hY) _ _ h
      (isPullback_excisionUnit B S hS f h hY T W₀ hT hcompl hf hsep hiso) hY
      Im hImopen U a q hq hqsurj hqetale
  · rw [hWitrue]
    exact isAlgebraicSpace_preimage_openComplement_excisionProj B S hS f h hY T W₀ hcompl hiso
      hTcl

end AlgebraicGeometry.Space

end
