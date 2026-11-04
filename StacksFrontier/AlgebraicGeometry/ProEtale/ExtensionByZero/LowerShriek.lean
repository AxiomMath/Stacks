module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.WeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleWeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.Localization.ExistenceOfLowerShriek
public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksCore.Tactic.StacksAttribute

/-!
# A left adjoint of the pro-étale inverse image of a closed immersion of affine schemes

Let `i : Z ⟶ X` be a closed immersion of affine objects of a chosen big pro-étale site. The
inverse image `i^{-1}` on small pro-étale sheaves of sets has a left adjoint `i^{Sh}_!`, the unit
`id ⟶ i^{-1}i^{Sh}_!` is an isomorphism, and `i^{Sh}_!` is fully faithful. These are clauses (3),
(5) and (6) of [Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL) for sheaves of sets;
clauses (1), (2) and the parts of (5), (6) about the direct image are
`AlgebraicGeometry.ProEtale.proetaleInverseImage_sheafify_affineIndEtaleLift`,
`AlgebraicGeometry.ProEtale.proetaleInverseImage_sections_iso_affineIndEtaleLift`,
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_isAffine` and
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_pushforward_fullyFaithful_of_isAffine`.

The source's route is followed. On the affine ind-étale site `Z_app` of the closed fibre every
object is covered by weakly contractible ones (Stacks 0990), and over such an object the inverse
image is evaluation at the lift `v` of Stacks 09BK — clause (2) — so the functor
`F ↦ (i^{-1}F)(V)` is corepresented by the sheafified representable of `v(V)` by Yoneda for
sheaves. The criterion of Stacks 09YX then produces the left adjoint on the affine ind-étale
sites, and the restriction equivalences of Stacks 098X carry it to the small pro-étale sites.
Clause (5) for the unit and clause (6) for `i^{Sh}_!` are then formal: in an adjoint triple
`i^{Sh}_! ⊣ i^{-1} ⊣ i_*` the unit of the left adjunction is invertible exactly when the counit
of the right one is, and `i^{Sh}_!` is fully faithful exactly when `i_*` is.

## Main results

* `AlgebraicGeometry.ProEtale.isRightAdjoint_affineIndEtaleSheafPullback` and
  `AlgebraicGeometry.ProEtale.isRightAdjoint_smallProetaleMorphism_inverseImage`:
  **Stacks 09BL (3)**, the existence of `i^{Sh}_!`, on the affine ind-étale sites and on the
  small pro-étale sites.
* `AlgebraicGeometry.ProEtale.smallProetaleLowerShriek` and
  `AlgebraicGeometry.ProEtale.smallProetaleLowerShriekAdjunction`: the functor `i^{Sh}_!` and its
  adjunction to `i^{-1}`.
* `AlgebraicGeometry.ProEtale.smallProetaleLowerShriek_unit_isIso`: **Stacks 09BL (5)** for
  `id ⟶ i^{-1}i^{Sh}_!`.
* `AlgebraicGeometry.ProEtale.smallProetaleLowerShriek_fullyFaithful`: **Stacks 09BL (6)** for
  `i^{Sh}_!`.

## Implementation notes

The weakly contractible objects of the affine ind-étale site are used as the family `E` of
Stacks 09YX; `GrothendieckTopology.isCoverDense_ι_of_hasEnoughObjects` turns "every object is
covered by objects of `E`" (Stacks 0990, `GrothendieckTopology.HasEnoughObjects`) into Mathlib's
cover-density of the inclusion of the full subcategory on `E`, which is the form Stacks 09YX
takes its hypothesis in.

The transport along the restriction equivalences is `Functor.isRightAdjoint_of_isoCompEquivalence`
applied to `AlgebraicGeometry.ProEtale.affineIndEtaleSheafPullbackRestrictionIsoOfCategory`; the
inverse image of the morphism of topoi is identified with the sheafified left Kan extension by
uniqueness of left adjoints, both being left adjoint to the direct image.

Everything here is for a closed immersion of **affine** objects of a chosen big pro-étale site,
which is the hypothesis of the tag. It does not transport to the unrestricted site
`AlgebraicGeometry.Scheme.ProEt` of all weakly étale schemes over the base: the comparison of
that site with the affine ind-étale site is not available, as set out in
`StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.BaseChange`.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09YX](https://stacks.math.columbia.edu/tag/09YX)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.GrothendieckTopology

/-- If every object of a site has a covering by objects with `P`, then the inclusion of the full
subcategory of objects with `P` is cover dense: the sieve of arrows factoring through such an
object contains the generating family of that covering. -/
theorem isCoverDense_ι_of_hasEnoughObjects {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : ObjectProperty C) (hP : J.HasEnoughObjects P) :
    P.ι.IsCoverDense J where
  is_cover U := by
    obtain ⟨I, Ui, f, hf, hPU⟩ := hP U
    refine J.superset_covering ?_ hf
    rintro W g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact ⟨⟨⟨Ui j, hPU j⟩, a, f j, rfl⟩⟩

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Functor

/-- A commuting square `L ⋙ G ≅ F ⋙ M` with `G` an equivalence rewrites as a formula for `L`:
`L ≅ F ⋙ M ⋙ G^{-1}`. -/
def isoCompInverseOfCompIso {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] (L : A ⥤ B) (M : C ⥤ D) (F : A ⥤ C) (G : B ⥤ D)
    [G.IsEquivalence] (h : L ⋙ G ≅ F ⋙ M) :
    L ≅ F ⋙ M ⋙ G.asEquivalence.inverse :=
  (Functor.rightUnitor L).symm ≪≫
    Functor.isoWhiskerLeft L G.asEquivalence.unitIso ≪≫
    (Functor.associator L G G.asEquivalence.inverse).symm ≪≫
    Functor.isoWhiskerRight h G.asEquivalence.inverse ≪≫
    Functor.associator F M G.asEquivalence.inverse

/-- Having a left adjoint transports along equivalences: if `L ⋙ G ≅ F ⋙ M` with `F` and `G`
equivalences and `M` has a left adjoint, then `L` has a left adjoint, namely
`G ⋙ M_! ⋙ F^{-1}`. -/
theorem isRightAdjoint_of_isoCompEquivalence {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] (L : A ⥤ B) (M : C ⥤ D) (F : A ⥤ C) (G : B ⥤ D)
    [F.IsEquivalence] [G.IsEquivalence] [M.IsRightAdjoint] (h : L ⋙ G ≅ F ⋙ M) :
    L.IsRightAdjoint :=
  (((G.asEquivalence.toAdjunction.comp (Adjunction.ofIsRightAdjoint M)).comp
    F.asEquivalence.symm.toAdjunction).ofNatIsoRight
      (isoCompInverseOfCompIso L M F G h).symm).isRightAdjoint

/-- Full faithfulness of a right adjoint transports along equivalences: if `L ⋙ G ≅ F ⋙ M` with
`F` and `G` equivalences and the right adjoint of `M` is fully faithful, then the right adjoint
of `L` is fully faithful. The right adjoint of `L` is `G ⋙ M_* ⋙ F^{-1}`, a composite of a
fully faithful functor with two equivalences. -/
noncomputable def fullyFaithful_rightAdjoint_of_isoCompEquivalence {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] {L : A ⥤ B} {RL : B ⥤ A}
    {M : C ⥤ D} {RM : D ⥤ C} (adjL : L ⊣ RL) (adjM : M ⊣ RM) (F : A ⥤ C) (G : B ⥤ D)
    [F.IsEquivalence] [G.IsEquivalence] (h : L ⋙ G ≅ F ⋙ M) (hRM : RM.FullyFaithful) :
    RL.FullyFaithful := by
  have adj : (F ⋙ M) ⋙ G.asEquivalence.inverse ⊣ G ⋙ RM ⋙ F.asEquivalence.inverse :=
    ((F.asEquivalence.toAdjunction.comp adjM).comp G.asEquivalence.symm.toAdjunction)
  have e : RL ≅ G ⋙ RM ⋙ F.asEquivalence.inverse :=
    Adjunction.rightAdjointUniq adjL
      (adj.ofNatIsoLeft (isoCompInverseOfCompIso L M F G h).symm)
  have hG := Functor.FullyFaithful.ofFullyFaithful G
  have hF := Functor.FullyFaithful.ofFullyFaithful F.asEquivalence.inverse
  have : G.Full := hG.full
  have : G.Faithful := hG.faithful
  have : RM.Full := hRM.full
  have : RM.Faithful := hRM.faithful
  have : F.asEquivalence.inverse.Full := hF.full
  have : F.asEquivalence.inverse.Faithful := hF.faithful
  exact Functor.FullyFaithful.ofIso
    (Functor.FullyFaithful.ofFullyFaithful (G ⋙ RM ⋙ F.asEquivalence.inverse)) e.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-! ### Weakly contractible objects of the affine ind-étale site are cover dense -/

variable (B : BigProetaleSite.{u})

/-- **Stacks 0990**, in the form used below: the affine ind-étale pro-étale site of an affine
object has enough weakly contractible objects. -/
theorem affineIndEtaleProetale_hasEnough_weaklyContractible (S : B.Scheme) [IsAffine S.obj] :
    (AffineIndEtaleProetale.topology B S).HasEnoughObjects
      (AffineIndEtaleProetale.topology B S).IsWeaklyContractible := fun U => by
  obtain ⟨I, Ui, f, hf, hPU⟩ :=
    affineIndEtaleProetale_hasEnough_quasiCompact_weaklyContractible B S U
  exact ⟨I, Ui, f, hf, fun j => (hPU j).2⟩

/-- The inclusion of the weakly contractible objects of the affine ind-étale pro-étale site of
an affine object is cover dense. -/
instance isCoverDense_isWeaklyContractible_affineIndEtale (S : B.Scheme) [IsAffine S.obj] :
    (ObjectProperty.ι
        ((AffineIndEtaleProetale.topology B S).IsWeaklyContractible :
          ObjectProperty (AffineIndEtaleProetale B S))).IsCoverDense
      (AffineIndEtaleProetale.topology B S) :=
  GrothendieckTopology.isCoverDense_ι_of_hasEnoughObjects _ _
    (affineIndEtaleProetale_hasEnough_weaklyContractible B S)

/-! ### A left adjoint of the inverse image -/

variable {Z X : B.Scheme} (i : Z ⟶ X)
  [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]

/-- **Stacks 09BL (2) as a corepresentability statement.** At a weakly contractible object `V` of
the affine ind-étale site of `Z`, the functor `F ↦ (i^{-1}F)(V)` on sheaves of sets on the affine
ind-étale site of `X` is corepresented by the sheafified representable of the lift of `V`:
it is the functor `F ↦ F(v(V))` by Stacks 09BL (2), and that functor is corepresentable by
Yoneda for sheaves. -/
theorem isCorepresentable_affineIndEtaleSheafPullback_sections
    (V : AffineIndEtaleProetale B Z)
    (hV : (AffineIndEtaleProetale.topology B Z).IsWeaklyContractible V) :
    (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        (Type (u + 1)) (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ⋙
      (sheafSections (AffineIndEtaleProetale.topology B Z) (Type (u + 1))).obj
        (op V)).IsCorepresentable := by
  have e₁ := affineIndEtaleSheafPullbackIsoLiftOfCategory B i (Type (u + 1))
  have e₂ := affineIndEtaleSheafificationEvaluationIso.{u, u} B i V hV
  have e : (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
        (Type (u + 1)) (AffineIndEtaleProetale.topology B X)
        (AffineIndEtaleProetale.topology B Z) ⋙
      (sheafSections (AffineIndEtaleProetale.topology B Z) (Type (u + 1))).obj (op V)) ≅
      (sheafSections (AffineIndEtaleProetale.topology B X) (Type (u + 1))).obj
        (op ((affineIndEtaleLift B i).obj V)) :=
    Functor.isoWhiskerRight e₁ _ ≪≫ e₂
  have := Sheaf.isCorepresentable_sheafSections (AffineIndEtaleProetale.topology B X)
    ((affineIndEtaleLift B i).obj V)
  exact corepresentable_of_natIso _ e.symm

/-- **Stacks 09BL (3) on the affine ind-étale sites.** Inverse image along base change of the
affine ind-étale pro-étale sites has a left adjoint. -/
instance isRightAdjoint_affineIndEtaleSheafPullback :
    (Functor.sheafPullbackConstruction.sheafPullback (affineIndEtaleBaseChange B i)
      (Type (u + 1)) (AffineIndEtaleProetale.topology B X)
      (AffineIndEtaleProetale.topology B Z)).IsRightAdjoint :=
  Sheaf.isRightAdjoint_of_isCorepresentable_sections _
    ((AffineIndEtaleProetale.topology B Z).IsWeaklyContractible :
      ObjectProperty (AffineIndEtaleProetale B Z))
    (isCorepresentable_affineIndEtaleSheafPullback_sections B i)

/-- **Stacks 09BL (3).** The inverse image `i^{-1}` on small pro-étale sheaves of sets of a
closed immersion of affine schemes has a left adjoint `i^{Sh}_!`. -/
@[stacks 09BL "(3), the inverse image i^{-1} : Sh(X_proetale) -> Sh(Z_proetale) of a closed \
immersion of affine objects of a chosen big pro-etale site has a left adjoint i^{Sh}_!"]
instance isRightAdjoint_smallProetaleMorphism_inverseImage :
    (smallProetaleMorphism B Z X i).inverseImage.IsRightAdjoint := by
  have : ((AffineIndEtaleProetale.inclusion B X).sheafPushforwardContinuous (Type (u + 1))
      (AffineIndEtaleProetale.topology B X)
      (SmallProetale.topology B X.obj X.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B X
  have : ((AffineIndEtaleProetale.inclusion B Z).sheafPushforwardContinuous (Type (u + 1))
      (AffineIndEtaleProetale.topology B Z)
      (SmallProetale.topology B Z.obj Z.property)).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B Z
  have : (Functor.sheafPullbackConstruction.sheafPullback
      (smallProetaleBaseChange B Z X i) (Type (u + 1))
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_isoCompEquivalence _ _ _ _
      (affineIndEtaleSheafPullbackRestrictionIsoOfCategory B i (Type (u + 1)))
  exact ((Adjunction.ofIsRightAdjoint _).ofNatIsoRight
    (Adjunction.leftAdjointUniq (smallProetaleMorphism B Z X i).adj
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallProetaleBaseChange B Z X i) (Type (u + 1))
        (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property))).symm).isRightAdjoint

/-- **Stacks 09BL (3), the functor.** The left adjoint `i^{Sh}_!` of the inverse image on small
pro-étale sheaves of sets of a closed immersion of affine schemes. -/
def smallProetaleLowerShriek :
    Sheaf (SmallProetale.topology B Z.obj Z.property) (Type (u + 1)) ⥤
      Sheaf (SmallProetale.topology B X.obj X.property) (Type (u + 1)) :=
  (smallProetaleMorphism B Z X i).inverseImage.leftAdjoint

/-- The adjunction `i^{Sh}_! ⊣ i^{-1}` of Stacks 09BL (3). -/
def smallProetaleLowerShriekAdjunction :
    smallProetaleLowerShriek B i ⊣ (smallProetaleMorphism B Z X i).inverseImage :=
  Adjunction.ofIsRightAdjoint _

/-- The adjoint triple `i^{Sh}_! ⊣ i^{-1} ⊣ i_*` on small pro-étale sheaves of sets. -/
def smallProetaleLowerShriekTriple :
    Adjunction.Triple (smallProetaleLowerShriek B i)
      (smallProetaleMorphism B Z X i).inverseImage (smallProetaleMorphism B Z X i).pushforward where
  adj₁ := smallProetaleLowerShriekAdjunction B i
  adj₂ := (smallProetaleMorphism B Z X i).adj

/-- **Stacks 09BL (5), the unit of lower shriek.** For a closed immersion of affine schemes the
unit `id ⟶ i^{-1} i^{Sh}_!` of the adjunction `i^{Sh}_! ⊣ i^{-1}` on small pro-étale sheaves of
sets is an isomorphism.

In an adjoint triple `i^{Sh}_! ⊣ i^{-1} ⊣ i_*` the unit of the left adjunction is invertible
exactly when the counit of the right one is, and the latter is Stacks 09BL (5) for `i^{-1}i_*`. -/
@[stacks 09BL "(5), the map id -> i^{-1} i^{Sh}_! is an isomorphism, for sheaves of sets on the \
small pro-etale sites of a closed immersion of affine objects of a chosen big pro-etale site"]
theorem smallProetaleLowerShriek_unit_isIso :
    IsIso (smallProetaleLowerShriekAdjunction B i).unit :=
  (smallProetaleLowerShriekTriple B i).isIso_unit_iff_isIso_counit.mpr
    (smallProetaleMorphism_counit_isIso_of_isAffine B i)

/-- **Stacks 09BL (6) for lower shriek.** For a closed immersion of affine schemes the left
adjoint `i^{Sh}_!` of the inverse image on small pro-étale sheaves of sets is fully faithful. -/
@[stacks 09BL "(6), full faithfulness of i^{Sh}_!, for sheaves of sets on the small pro-etale \
sites of a closed immersion of affine objects of a chosen big pro-etale site"]
def smallProetaleLowerShriek_fullyFaithful :
    (smallProetaleLowerShriek B i).FullyFaithful :=
  (smallProetaleLowerShriekTriple B i).fullyFaithfulEquiv.symm
    (smallProetaleMorphism_pushforward_fullyFaithful_of_isAffine B i)

end AlgebraicGeometry.ProEtale

end
