module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ClosedImmersionPrincipalSquare
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.TwoGeneratorSquareInSite

/-!
# The image of an almost blowup square does not depend on the chosen square

This is step 4 of the proof of Stacks 0EVI.  Two almost blowup squares over the same base with
the same centre are dominated by a common one, by Stacks 0EVB, and the comparison morphism of
their modifications is a closed immersion of finite presentation which is an isomorphism away
from the exceptional subscheme.  The second step of the proof of Stacks 0EVI therefore applies
to the square relating the two modifications, so a presheaf satisfying conditions (1) and (3) of
Stacks 0EVI sends it to a cartesian square of sets; pasting that square under the square of the
bigger modification identifies cartesianness for the bigger modification with cartesianness for
the common refinement.  As the refinement is shared, cartesianness holds for one of the two given
squares exactly when it holds for the other.

## Main definitions

* `AlgebraicGeometry.BigHOver.homOfScheme`: a morphism of schemes of the site which commutes with
  the structure morphisms, as a morphism of the big h category over `S`.  The matching object
  constructor is the already available `AlgebraicGeometry.BigHOver.mk`, whose module is imported
  for its body: the side condition of `homOfScheme` at it holds by `rfl`.

## Main results

* `AlgebraicGeometry.BigHOver.isPullback_iff_of_isClosedImmersion_refinement`: cartesianness of
  the image of a square and of a square dominated by it, through a closed immersion of
  modifications which is an isomorphism away from a locally principal exceptional subscheme, are
  equivalent.
* `AlgebraicGeometry.BigHOver.isPullback_of_isAlmostBlowUpSquare_of_isPullback`: **step 4 of the
  proof of Stacks 0EVI**, the independence of the chosen almost blowup square.

## Implementation notes

The pasting is the one-line content of the step: the inner square is
`AlgebraicGeometry.BigHOver.isPullback_of_isClosedImmersion_of_restrict_isIso`, and
`CategoryTheory.IsPullback.paste_vert_iff` turns the composite of the two vertical legs into the
legs of the refinement, because the comparison morphism factors the modification and the centre
is shared.

That the comparison morphism is an isomorphism away from the exceptional subscheme is not part of
Stacks 0EVB.  It follows from `AlgebraicGeometry.isIso_restrict_compl_support` for the two
squares: restriction of morphisms is compatible with composition
(`AlgebraicGeometry.morphismRestrict_comp`), the preimage of the complement of the support of the
centre is the complement of the support of the exceptional subscheme
(`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`), and a factor of an isomorphism whose
other factor is an isomorphism is one.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVB](https://stacks.math.columbia.edu/tag/0EVB)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-! ### An isomorphism away from the centre, for a factor of the modification -/

/-- **A factor of a morphism which is an isomorphism away from a closed subset is an isomorphism
away from its preimage, provided the other factor is.** -/
public theorem isIso_morphismRestrict_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.Opens) (hfg : IsIso ((f ≫ g) ∣_ U)) (hg : IsIso (g ∣_ U)) :
    IsIso (f ∣_ g ⁻¹ᵁ U) :=
  @IsIso.of_isIso_fac_right _ _ _ _ _ (g ∣_ U) (f ∣_ g ⁻¹ᵁ U) ((f ≫ g) ∣_ U) hg hfg
    (morphismRestrict_comp f g U).symm

/-- The complement of the support of the inverse image of an ideal sheaf is the preimage of the
complement of its support. -/
public theorem preimage_compl_support_eq {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    f ⁻¹ᵁ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : Y.Opens) =
      (⟨(I.comap f).supportᶜ, (I.comap f).support.isClosed.isOpen_compl⟩ : X.Opens) := by
  refine TopologicalSpace.Opens.ext ?_
  change f.base ⁻¹' (I.support : Set Y)ᶜ = ((I.comap f).support : Set X)ᶜ
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- **The comparison morphism of two almost blowup squares with the same centre is an isomorphism
away from the exceptional subscheme.** -/
public theorem isIso_morphismRestrict_of_isAlmostBlowUpSquare {X X' X'' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) (b' : X'' ⟶ X) (i : X'' ⟶ X')
    (hb : IsAlmostBlowUpSquare I b) (hb' : IsAlmostBlowUpSquare I b')
    (hi : i ≫ b = b') :
    IsIso (i ∣_ (⟨(I.comap b).supportᶜ, (I.comap b).support.isClosed.isOpen_compl⟩ : X'.Opens)) :=
  preimage_compl_support_eq I b ▸ isIso_morphismRestrict_of_comp i b _
    (hi ▸ isIso_restrict_compl_support I b' hb') (isIso_restrict_compl_support I b hb)

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Objects and morphisms of the site from schemes and morphisms of schemes -/

/-- A morphism between the underlying schemes of two objects of the big h category over `S` which
commutes with their structure morphisms, as a morphism of the big h category over `S`. -/
public def homOfScheme {T T' : BigHOver B S hS}
    (f : (BigHOver.toScheme B S hS).obj T ⟶ (BigHOver.toScheme B S hS).obj T')
    (w : f ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) : T ⟶ T' :=
  Over.homMk (ObjectProperty.homMk f) (by apply ObjectProperty.hom_ext; exact w)

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigHOver.homOfScheme` is the given
one. -/
public theorem toScheme_map_homOfScheme {T T' : BigHOver B S hS}
    (f : (BigHOver.toScheme B S hS).obj T ⟶ (BigHOver.toScheme B S hS).obj T')
    (w : f ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) :
    (BigHOver.toScheme B S hS).map (homOfScheme B S hS f w) = f :=
  rfl

/-- The composite of the structure morphism of an object of the big h category over `S` to the
base with a morphism into it. -/
public theorem inclusion_map_hom_of_hom {T T' : BigHOver B S hS} (g : T ⟶ T') :
    (BigHOver.toScheme B S hS).map g ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom := by
  rw [show (BigHOver.toScheme B S hS).map g = B.inclusion.map g.left from rfl,
    ← B.inclusion.map_comp, Over.w g]

variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-! ### Cartesianness transfers along a closed-immersion refinement -/

/-- **Cartesianness of the image of a square and of a refinement of it are equivalent.** Let a
square of the big h category over `S` with modification `bk`, centre `z` and exceptional corner
`Ek` be dominated by a second square with the same centre, through a morphism `i` of the
modifications which is a closed immersion of finite presentation and an isomorphism away from a
locally principal ideal sheaf cutting out `Ek`.  Then a presheaf which is a sheaf for the Zariski
topology and satisfies condition (3) of Stacks 0EVI sends the first square to a cartesian square
of sets if and only if it does the second.

This is the mechanism of step 4 of the proof of Stacks 0EVI: both squares are dominated by one
common refinement, so cartesianness for either is cartesianness for that refinement. -/
public theorem isPullback_iff_of_isClosedImmersion_refinement
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    (h1 : BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    {X X' Z E Xk Ek : BigHOver B S hS}
    (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (bk : Xk ⟶ X) (dk : Ek ⟶ Xk) (ek : Ek ⟶ Z)
    (i : X' ⟶ Xk) (j : E ⟶ Ek)
    (hi : i ≫ bk = b) (hj : j ≫ ek = e) (hwk : ek ≫ z = dk ≫ bk)
    (Ik : ((BigHOver.toScheme B S hS).obj Xk).IdealSheafData)
    (hci : IsClosedImmersion ((BigHOver.toScheme B S hS).map i))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map i))
    (hprin : Stacks.Divisors.IsLocallyPrincipal Ik)
    (hiso : IsIso ((BigHOver.toScheme B S hS).map i ∣_
      (⟨Ik.supportᶜ, Ik.support.isClosed.isOpen_compl⟩ :
        ((BigHOver.toScheme B S hS).obj Xk).Opens)))
    (hEk : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map dk) ≅ Over.mk Ik.subschemeι))
    (hsq : IsPullback ((BigHOver.toScheme B S hS).map j) ((BigHOver.toScheme B S hS).map d)
      ((BigHOver.toScheme B S hS).map dk) ((BigHOver.toScheme B S hS).map i)) :
    IsPullback (F.map z.op) (F.map bk.op) (F.map ek.op) (F.map dk.op) ↔
      IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  have hinner := isPullback_of_isClosedImmersion_of_restrict_isIso B S hS F hzar h1
    Xk X' Ek E i dk d j Ik hci hfp hprin hiso hEk hsq
  have hb : F.map bk.op ≫ F.map i.op = F.map b.op := by
    rw [← F.map_comp, ← op_comp, hi]
  have he : F.map ek.op ≫ F.map j.op = F.map e.op := by
    rw [← F.map_comp, ← op_comp, hj]
  have hcomm : F.map z.op ≫ F.map ek.op = F.map bk.op ≫ F.map dk.op := by
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hwk]
  rw [← hb, ← he]
  exact (IsPullback.paste_vert_iff hinner hcomm).symm

/-! ### Independence of the chosen almost blowup square -/

/-- **Step 4 of the proof of Stacks 0EVI: the image of an almost blowup square is cartesian for
one square with a given centre exactly when it is for another.** Let `X` be an object of the big
h category over `S` whose underlying scheme is quasi-compact and quasi-separated, let `z` cut out
the closed subscheme attached to an ideal sheaf `I` on it, and let two almost blowup squares with
centre `I` be given, with their exceptional corners.  A presheaf which is a sheaf for the Zariski
topology and satisfies condition (3) of Stacks 0EVI sends the second square to a cartesian square
of sets as soon as it does the first.

By Stacks 0EVB the two modifications are dominated by the modification of a third almost blowup
square with centre `I` through closed immersions over `X`, and
`AlgebraicGeometry.BigHOver.isPullback_iff_of_isClosedImmersion_refinement` identifies
cartesianness for each of the two given squares with cartesianness for that common one. -/
public theorem isPullback_of_isAlmostBlowUpSquare_of_isPullback
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    (h1 : BigHOver.IsOneGeneratorAlmostBlowUpSheaf B S hS F)
    {X Z X'₁ E₁ X'₂ E₂ : BigHOver B S hS}
    [CompactSpace ((BigHOver.toScheme B S hS).obj X)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X)]
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (z : Z ⟶ X) (b₁ : X'₁ ⟶ X) (d₁ : E₁ ⟶ X'₁) (e₁ : E₁ ⟶ Z)
    (b₂ : X'₂ ⟶ X) (d₂ : E₂ ⟶ X'₂) (e₂ : E₂ ⟶ Z)
    (hb₁ : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b₁))
    (hb₂ : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b₂))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hsq₁ : IsPullback ((BigHOver.toScheme B S hS).map e₁) ((BigHOver.toScheme B S hS).map d₁)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b₁))
    (hsq₂ : IsPullback ((BigHOver.toScheme B S hS).map e₂) ((BigHOver.toScheme B S hS).map d₂)
      ((BigHOver.toScheme B S hS).map z) ((BigHOver.toScheme B S hS).map b₂))
    (hcart : IsPullback (F.map z.op) (F.map b₁.op) (F.map e₁.op) (F.map d₁.op)) :
    IsPullback (F.map z.op) (F.map b₂.op) (F.map e₂.op) (F.map d₂.op) := by
  classical
  have : HasPullbacks B.Schemes := inferInstance
  let _ := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let _ : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
    inferInstance
  obtain ⟨ez⟩ := hZ
  -- the common refinement of the two modifications
  have hI : Scheme.IdealSheafData.IsFiniteType I :=
    (Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hb₁.center_finitePresentation
  obtain ⟨W, bW, i₁, i₂, hbW, hci₁, hci₂, hcomp₁, hcomp₂, -, -⟩ :=
    exists_isAlmostBlowUpSquare_closedImmersion_to_both I hI
      ((BigHOver.toScheme B S hS).map b₁) ((BigHOver.toScheme B S hS).map b₂) hb₁ hb₂
  -- the refinement as an object of the site
  have : LocallyOfFinitePresentation bW := hbW.finitePresentation.1
  have : QuasiCompact bW := hbW.finitePresentation.2.1
  have hW : B.Contains W :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact bW X.left.property
  set XW : BigHOver B S hS := BigHOver.mk B S hS hW (bW ≫ B.inclusion.map X.hom) with hXW
  set bWs : XW ⟶ X := homOfScheme B S hS bW rfl with hbWs
  have hbWmap : (BigHOver.toScheme B S hS).map bWs = bW := rfl
  -- the exceptional corner of the refinement
  set EW : BigHOver B S hS := pullback bWs z with hEW
  set dW : EW ⟶ XW := pullback.fst bWs z with hdW
  set eW : EW ⟶ Z := pullback.snd bWs z with heW
  have hpbW : IsPullback dW eW bWs z := IsPullback.of_hasPullback bWs z
  -- the two squares of the site, read in the site
  have hsq₁s : IsPullback e₁ d₁ z b₁ := hsq₁.of_map_of_faithful (BigHOver.toScheme B S hS)
  have hsq₂s : IsPullback e₂ d₂ z b₂ := hsq₂.of_map_of_faithful (BigHOver.toScheme B S hS)
  -- the general step, applied to each of the two squares
  have key : ∀ (X' E' : BigHOver B S hS) (b' : X' ⟶ X) (d' : E' ⟶ X') (e' : E' ⟶ Z)
      (hb' : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b'))
      (hsq' : IsPullback e' d' z b')
      (i : W ⟶ (BigHOver.toScheme B S hS).obj X')
      (hcii : IsClosedImmersion i) (hcompi : i ≫ (BigHOver.toScheme B S hS).map b' = bW),
      IsPullback (F.map z.op) (F.map b'.op) (F.map e'.op) (F.map d'.op) ↔
        IsPullback (F.map z.op) (F.map bWs.op) (F.map eW.op) (F.map dW.op) := by
    intro X' E' b' d' e' hb' hsq' i hcii hcompi
    set bS := (BigHOver.toScheme B S hS).map b' with hbS
    -- the comparison morphism, in the site
    have hwi : i ≫ B.inclusion.map X'.hom = B.inclusion.map XW.hom := by
      rw [← inclusion_map_hom_of_hom B S hS b', ← Category.assoc, hcompi]
      exact (inclusion_map_hom_of_hom B S hS bWs).symm
    set iS : XW ⟶ X' := homOfScheme B S hS i hwi with hiS
    have hiSmap : (BigHOver.toScheme B S hS).map iS = i := rfl
    have hiSb : iS ≫ b' = bWs := by
      refine (BigHOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hiSmap, hbWmap]
      exact hcompi
    -- the comparison of the two exceptional corners
    have hwj : eW ≫ z = (dW ≫ iS) ≫ b' := by
      rw [Category.assoc, hiSb]
      exact hpbW.w.symm
    set jS : EW ⟶ E' := hsq'.lift eW (dW ≫ iS) hwj with hjS
    have hjfst : jS ≫ e' = eW := hsq'.lift_fst _ _ hwj
    have hjsnd : jS ≫ d' = dW ≫ iS := hsq'.lift_snd _ _ hwj
    -- the corner square of the comparison is cartesian
    have hcorner : IsPullback dW jS iS d' := by
      refine IsPullback.of_bot ?_ hjsnd.symm hsq'.flip
      rw [hjfst, hiSb]
      exact hpbW
    -- the data of the refinement step
    have := hcii
    have : LocallyOfFinitePresentation bS := hb'.finitePresentation.1
    have : QuasiCompact bS := hb'.finitePresentation.2.1
    have : QuasiSeparated bS := hb'.finitePresentation.2.2
    have hfpi : FinitePresentation i := by
      refine finitePresentation_of_comp i bS ?_
      rw [hcompi]
      exact hbW.finitePresentation
    refine isPullback_iff_of_isClosedImmersion_refinement B S hS F hzar h1
      bWs z dW eW b' d' e' iS jS hiSb hjfst hsq'.w (I.comap bS)
      (by rwa [hiSmap]) (by rwa [hiSmap]) hb'.exceptional_locallyPrincipal
      (by rw [hiSmap]
          exact isIso_morphismRestrict_of_isAlmostBlowUpSquare I bS bW i hb' hbW hcompi)
      ?_ (hcorner.flip.map (BigHOver.toScheme B S hS))
    -- the exceptional corner is the closed subscheme cut out by the inverse-image centre
    have h1' : Over.mk ((BigHOver.toScheme B S hS).map d') ≅
        Over.mk (pullback.fst bS ((BigHOver.toScheme B S hS).map z)) :=
      Over.isoMk (hsq'.map (BigHOver.toScheme B S hS)).flip.isoPullback
        ((hsq'.map (BigHOver.toScheme B S hS)).flip.isoPullback_hom_fst)
    have h3' : Over.mk (I.comap bS).subschemeι ≅ Over.mk (pullback.fst bS I.subschemeι) :=
      Over.isoMk (I.comapIso bS) (Scheme.IdealSheafData.comapIso_hom_fst I bS)
    exact ⟨h1' ≪≫ pullbackOverIso bS ((BigHOver.toScheme B S hS).map z) I.subschemeι ez ≪≫
      h3'.symm⟩
  exact (key X'₂ E₂ b₂ d₂ e₂ hb₂ hsq₂s i₂ hci₂ hcomp₂).2
    ((key X'₁ E₁ b₁ d₁ e₁ hb₁ hsq₁s i₁ hci₁ hcomp₁).1 hcart)

end BigHOver

end AlgebraicGeometry

end
