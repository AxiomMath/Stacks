module

public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackColimit
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafComposeSupplement

/-!
# The pro-étale inverse image of an abelian étale sheaf

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale category into the small pro-étale category.  Inverse image `ε⁻¹`
of abelian sheaves commutes with passing to the underlying sheaf of sets (Stacks 00YT), so the
two results proved for sheaves of sets carry over to abelian sheaves:

* the adjunction map `ℱ ⟶ ε_*ε⁻¹ℱ` is an isomorphism (Stacks 099T);
* if `Y = lim Y_i` is the limit of a cofiltered inverse system of quasi-compact and
  quasi-separated objects of `X_proétale` with affine transition morphisms, then
  `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)` (Stacks 099S).

## Main results

* `AlgebraicGeometry.Scheme.proetaleUnderlyingSetIso`: the sheaf of sets underlying `ε⁻¹ℱ` is
  the inverse image of the sheaf of sets underlying `ℱ`.
* `AlgebraicGeometry.Scheme.isIso_unit_of_etaleToProetale_addCommGrp`: Stacks 099T for abelian
  sheaves, for an arbitrary left adjoint `ε⁻¹` of `ε_*`.
* `AlgebraicGeometry.Scheme.proetaleInverseImageIsColimitAddCommGrp` and
  `AlgebraicGeometry.Scheme.proetaleInverseImageIsColimitForget`: Stacks 099S for abelian
  sheaves, as a colimit of abelian groups and as a colimit of their underlying sets.

## Implementation notes

The comparison with sheaves of sets is
`CategoryTheory.Functor.sheafPullbackSheafComposeIso` for the forgetful functor: inverse image is
the sheafification of a pointwise left Kan extension, and the forgetful functor preserves the
colimits computing it, the comma categories being filtered because the inclusion of the small
étale category preserves finite limits.  Every statement is made for an arbitrary left adjoint
of `ε_*`, so that it does not depend on a model of `ε⁻¹`.

## References

* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

attribute [instance] ProEtale.hasSheafify_proetale

/-- The pointwise left Kan extensions along the inclusion of the small étale category exist for
abelian presheaves: the comma categories are essentially small in the coefficient universe. -/
instance hasPointwiseLeftKanExtension_etaleToProetale_addCommGrp
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :
    X.etaleToProetale.op.HasPointwiseLeftKanExtension P := fun Y => by
  have := hasColimitsOfShape_of_essentiallySmall.{max (u + 1) v}
    (CostructuredArrow X.etaleToProetale.op Y) AddCommGrpCat.{max (u + 1) v}
  infer_instance

/-- The pointwise left Kan extensions along the inclusion of the small étale category exist for
presheaves of sets. -/
instance hasPointwiseLeftKanExtension_etaleToProetale_type
    (P : X.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) :
    X.etaleToProetale.op.HasPointwiseLeftKanExtension P := fun Y => by
  have := hasColimitsOfShape_of_essentiallySmall.{max (u + 1) v}
    (CostructuredArrow X.etaleToProetale.op Y) (Type (max (u + 1) v))
  infer_instance

/-- The forgetful functor of abelian groups preserves the colimits computing the left Kan
extension along the inclusion of the small étale category: the comma categories are filtered,
the inclusion preserving finite limits. -/
instance preservesColimitsOfShape_costructuredArrow_etaleToProetale_forget
    (Y : X.ProEtᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have : IsFiltered (CostructuredArrow X.etaleToProetale.op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence X.etaleToProetale Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  exact PreservesFilteredColimitsOfSize.preserves_filtered_colimits _

/-- **Stacks 00YT for `ε`.** The sheaf of sets underlying the pro-étale inverse image of an
abelian étale sheaf `ℱ` is the inverse image of the sheaf of sets underlying `ℱ`.  The inverse
image of abelian sheaves is an arbitrary left adjoint of `ε_*`. -/
def proetaleUnderlyingSetIso
    {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
    (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (sheafCompose (Scheme.ProEt.topology X)
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj
        (L.obj F) ≅
      (Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale (Type (max (u + 1) v))
        X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
        ((sheafCompose X.smallEtaleTopology
            (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj F) :=
  (sheafCompose (Scheme.ProEt.topology X)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).mapIso
      (((X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology (Scheme.ProEt.topology X)).leftAdjointUniq adj).app F).symm ≪≫
    (X.etaleToProetale.sheafPullbackSheafComposeIso AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X)
          (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})
      F).symm ≪≫
    ((X.etaleToProetale.sheafAdjunctionContinuous (Type (max (u + 1) v)) X.smallEtaleTopology
      (Scheme.ProEt.topology X)).leftAdjointUniq
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X))).app _

/-- The unit of the chosen adjunction `ε⁻¹ ⊣ ε_*` on abelian sheaves is an isomorphism: after
passing to underlying sheaves of sets it is the unit for sheaves of sets, which is an
isomorphism by Stacks 099T, followed by the comparison isomorphism of Stacks 00YT. -/
private lemma isIso_sheafAdjunctionContinuous_unit_addCommGrp :
    IsIso (X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X)).unit := by
  have hT := Scheme.isIso_unit_of_etaleToProetale.{u, v} X
    (X.etaleToProetale.sheafAdjunctionContinuous (Type (max (u + 1) v)) X.smallEtaleTopology
      (Scheme.ProEt.topology X))
  suffices ∀ F, IsIso ((X.etaleToProetale.sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F) from
    NatIso.isIso_of_isIso_app _
  intro F
  have h := X.etaleToProetale.unit_comp_pushforward_map_sheafPullbackSheafComposeHom
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology (Scheme.ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) F
  have : IsIso ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).map
      ((X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F) ≫
      (X.etaleToProetale.sheafComposeSheafPushforwardIso AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology (Scheme.ProEt.topology X)
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).inv.app _) := by
    rw [← h]
    infer_instance
  have := (isIso_comp_right_iff _ _).1 this
  exact isIso_of_reflects_iso _
    (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}))

/-- **Stacks 099T for abelian sheaves.** For every abelian sheaf `ℱ` on the small étale site of
a scheme `X`, the adjunction map `ℱ ⟶ ε_*ε⁻¹ℱ` is an isomorphism, for an arbitrary left adjoint
`ε⁻¹` of `ε_*`. -/
theorem isIso_unit_of_etaleToProetale_addCommGrp
    {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
    (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology (Scheme.ProEt.topology X)) :
    IsIso adj.unit := by
  have := isIso_sheafAdjunctionContinuous_unit_addCommGrp.{u, v} X
  exact Stacks.Adjunction.isIso_unit_of_comp_iso_id adj
    (Functor.isoWhiskerRight
        ((X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
          X.smallEtaleTopology (Scheme.ProEt.topology X)).leftAdjointUniq adj).symm _ ≪≫
      (asIso (X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology (Scheme.ProEt.topology X)).unit).symm)

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (Y : I ⥤ X.ProEt) (c : Cone Y)
  (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
  [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
  {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}}
  (adj : L ⊣ X.etaleToProetale.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology (Scheme.ProEt.topology X))
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

include hc in
/-- **Stacks 099S for abelian sheaves, on underlying sets.** In the situation of
`AlgebraicGeometry.Scheme.proetaleInverseImageIsColimit`, the underlying sets of the sections of
`ε⁻¹ℱ` over the stages, with the restriction maps to `Y`, form a colimit cocone, for an abelian
sheaf `ℱ` and an arbitrary left adjoint `ε⁻¹` of `ε_*`. -/
def proetaleInverseImageIsColimitForget :
    IsColimit (((L.obj F).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}).mapCocone c.op) :=
  IsColimit.mapCoconeEquiv
    ((sheafToPresheaf _ _).mapIso (proetaleUnderlyingSetIso.{u, v} X adj F)).symm
    (Scheme.proetaleInverseImageIsColimit.{u, v} X Y c hc _)

include hc in
/-- **Stacks 099S for abelian sheaves.** Let `X` be a scheme, let `Y = lim Y_i` be the limit of a
cofiltered inverse system of quasi-compact and quasi-separated objects of `X_proétale` with
affine transition morphisms, and let `ℱ` be an abelian sheaf on `X_étale`.  Then
`ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)` as abelian groups, for an arbitrary left adjoint `ε⁻¹` of `ε_*`. -/
def proetaleInverseImageIsColimitAddCommGrp :
    IsColimit ((L.obj F).obj.mapCocone c.op) :=
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  have : ReflectsColimitsOfShape Iᵒᵖ (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})
    (proetaleInverseImageIsColimitForget.{u, v} X Y c hc adj F)

end Scheme

end AlgebraicGeometry

end
