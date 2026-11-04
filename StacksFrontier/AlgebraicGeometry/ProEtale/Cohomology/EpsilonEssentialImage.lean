module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ComparisonWithEtale
public import StacksFrontier.CategoryTheory.Sites.IsIsoOfBijectiveOnCoveringObjects
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.AdjunctionEssentialImage

/-!
# The essential image of the étale-to-pro-étale inverse image

Let `X` be a scheme and `ε : X_proétale → X_étale` the comparison morphism of sites. The inverse
image `ε⁻¹` is fully faithful on sheaves of sets, of abelian groups and of `Λ`-modules, so a
pro-étale sheaf `𝒢` lies in its essential image exactly when the counit `ε⁻¹ ε_* 𝒢 ⟶ 𝒢` is an
isomorphism. Since `ε⁻¹`, `ε_*` and the counit all commute with passing to underlying sheaves of
sets, membership in the essential image is a property of the underlying sheaf of sets.

For abelian sheaves the essential image is a weak Serre subcategory (Stacks 09B1 (1)): the
higher direct images `R^q ε_* ε⁻¹ ℱ` vanish (Stacks 099V (1)), so `ε_*` is exact on a short exact
sequence whose first term comes from `X_étale`.

## Main results

* `AlgebraicGeometry.Scheme.etaleInverseImageCompSheafPullbackIso`: inverse image along a
  morphism of schemes commutes with `ε⁻¹`, for any coefficients.
* `AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_iff_forget`: an abelian pro-étale
  sheaf lies in the essential image of `ε⁻¹` exactly when its underlying sheaf of sets does.
* `AlgebraicGeometry.ProEtale.isWeakSerreClass_epsilonInverseImage_essImage`: the essential image
  of `ε⁻¹` on abelian sheaves is a weak Serre subcategory.
* `AlgebraicGeometry.Scheme.isIso_etaleInverseImage_unit`: `ε⁻¹` on sheaves of `Λ`-modules,
  `AlgebraicGeometry.Scheme.etaleInverseImage`, is fully faithful (Stacks 099T for modules).
* `AlgebraicGeometry.Scheme.etaleInverseImage_essImage_iff_forget`: a pro-étale sheaf of
  `Λ`-modules lies in the essential image of `ε⁻¹` exactly when its underlying sheaf of sets
  does, hence exactly when its underlying abelian sheaf does
  (`AlgebraicGeometry.Scheme.etaleInverseImage_essImage_iff_forget₂`).

## References

* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

/-! ### Sheaves of sets -/

namespace Scheme

variable (X : Scheme.{u})

/-- The inverse image `ε⁻¹` of sheaves of sets along the étale-to-pro-étale comparison. -/
abbrev etaleTypeInverseImage :
    Sheaf X.smallEtaleTopology (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale (Type (max (u + 1) v))
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- If the unit of `L ⊣ R` is invertible and `L' ≅ L`, then an object lies in the essential image
of `L'` exactly when the counit of `L ⊣ R` is invertible at it. -/
private theorem essImage_iff_isIso_counit_app {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.unit] (e : L' ≅ L) (F : D) :
    L'.essImage F ↔ IsIso (adj.counit.app F) := by
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  rw [Functor.essImage_eq_of_natIso e, ← adj.isIso_counit_app_iff_mem_essImage]

/-- A sheaf of sets on `X_proétale` lies in the essential image of `ε⁻¹` exactly when the counit
of the chosen adjunction `ε⁻¹ ⊣ ε_*` is invertible at it. -/
theorem etaleTypeInverseImage_essImage_iff
    (F : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))) :
    (etaleTypeInverseImage.{v} X).essImage F ↔
      IsIso ((X.etaleToProetale.sheafAdjunctionContinuous (Type (max (u + 1) v))
        X.smallEtaleTopology (Scheme.ProEt.topology X)).counit.app F) := by
  let adj := X.etaleToProetale.sheafAdjunctionContinuous (Type (max (u + 1) v))
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := Scheme.isIso_unit_of_etaleToProetale.{u, v} X adj
  exact essImage_iff_isIso_counit_app adj
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).leftAdjointUniq
        adj) F

end Scheme

/-! ### Membership in the essential image from the colimit formula -/

namespace Scheme

variable (X : Scheme.{u})

/-- **The counit at a limit of étale objects.** Let `H` be a sheaf of sets on `X_proétale` and
`Y = lim Y_i` a cofiltered limit of quasi-compact and quasi-separated objects `Y_i` of
`X_étale` with affine transition morphisms. If the sections of `H` over the `Y_i` have colimit
`H(Y)`, then the counit `ε⁻¹ ε_* H ⟶ H` is bijective on sections over `Y`: both sides are the
colimit of the `H(Y_i)`, the left one by Stacks 099S. -/
theorem isIso_counit_app_app_of_isColimit {I : Type u} [SmallCategory I] [IsCofiltered I]
    (Y : I ⥤ X.Etale) (c : Cone (Y ⋙ X.etaleToProetale))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (H : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (hH : IsColimit (H.obj.mapCocone c.op)) :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).counit.app H).hom.app
        (op c.pt)) := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let R := X.etaleToProetale.sheafPushforwardContinuous (Type (max (u + 1) v))
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  let hA := Scheme.proetaleInverseImageIsColimitOfEtale.{u, v} X Y c hc (R.obj H)
  have hfac : ∀ j : Iᵒᵖ, ((Cocone.precompose (Functor.whiskerLeft Y.op
      (adj.unit.app (R.obj H)).hom)).obj
      (((etaleTypeInverseImage.{v} X).obj (R.obj H)).obj.mapCocone c.op)).ι.app j ≫
        (adj.counit.app H).hom.app (op c.pt) = (H.obj.mapCocone c.op).ι.app j := by
    intro j
    have htri := congrArg (fun f ↦ f.hom.app (op (Y.obj j.unop)))
      (adj.right_triangle_components H)
    have hnat := (adj.counit.app H).hom.naturality (c.π.app j.unop).op
    dsimp at htri hnat
    show ((adj.unit.app (R.obj H)).hom.app (op (Y.obj j.unop)) ≫
      ((etaleTypeInverseImage.{v} X).obj (R.obj H)).obj.map (c.π.app j.unop).op) ≫
        (adj.counit.app H).hom.app (op c.pt) = H.obj.map (c.π.app j.unop).op
    exact (Category.assoc _ _ _).trans
      ((congrArg ((adj.unit.app (R.obj H)).hom.app (op (Y.obj j.unop)) ≫ ·) hnat).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ H.obj.map (c.π.app j.unop).op) htri).trans (Category.id_comp _))))
  have heq : (adj.counit.app H).hom.app (op c.pt) = (hA.coconePointUniqueUpToIso hH).hom :=
    hA.hom_ext fun j ↦ (hfac j).trans (IsColimit.comp_coconePointUniqueUpToIso_hom hA hH j).symm
  rw [heq]
  infer_instance

/-- **A sheaf of sets on `X_proétale` comes from `X_étale` as soon as it satisfies the colimit
formula of Stacks 099S** over every cofiltered limit of affine objects of `X_étale`: the counit
`ε⁻¹ ε_* H ⟶ H` is then bijective on sections over every object ind-étale over an affine étale
`X`-scheme, and those cover every object. -/
theorem etaleTypeInverseImage_essImage_of_isColimit
    (H : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (hH : ∀ ⦃I : Type u⦄ [SmallCategory I] [IsCofiltered I] (Y : I ⥤ X.Etale)
      (c : Cone (Y ⋙ X.etaleToProetale)),
      IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c) →
        (∀ i, IsAffine (Y.obj i).left) → Nonempty (IsColimit (H.obj.mapCocone c.op))) :
    (etaleTypeInverseImage.{v} X).essImage H := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} X
  rw [essImage_iff_isIso_counit_app adj (Iso.refl _)]
  refine Sheaf.isIso_of_bijective_of_mem _ (ProEtale.IsAffineIndEtaleOverEtale X)
    (ProEtale.generate_isAffineIndEtaleOverEtale_mem X) fun V hV ↦ ?_
  obtain ⟨A, _, _, Ub, πU, hUa, ⟨hlim⟩⟩ := hV.exists_isLimit
  have : ∀ {a b : A} (f : a ⟶ b), IsAffineHom (Ub.map f).left := fun _ ↦ inferInstance
  obtain ⟨hcol⟩ := hH Ub (Cone.mk V πU) hlim hUa
  rw [← isIso_iff_bijective]
  exact isIso_counit_app_app_of_isColimit X Ub (Cone.mk V πU) hlim H hcol

/-- **Stacks 099S for sheaves in the essential image of `ε⁻¹`.** A sheaf of sets on `X_proétale`
coming from `X_étale` satisfies the colimit formula over every cofiltered limit of
quasi-compact and quasi-separated objects with affine transition morphisms. -/
theorem nonempty_isColimit_of_mem_essImage {I : Type u} [SmallCategory I] [IsCofiltered I]
    (Y : I ⥤ X.ProEt) (c : Cone Y)
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left] [∀ i : I, CompactSpace (Y.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (Y.obj i).left]
    (H : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (hH : (etaleTypeInverseImage.{v} X).essImage H) :
    Nonempty (IsColimit (H.obj.mapCocone c.op)) := by
  obtain ⟨F, ⟨e⟩⟩ := hH
  exact ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso e)
    (Scheme.proetaleInverseImageIsColimit.{u, v} X Y c hc F)⟩

/-- Base change along a morphism of schemes `i : Z ⟶ X` carries a cofiltered limit of objects of
`X_proétale`, taken on underlying schemes, to a cofiltered limit of objects of `Z_proétale`. -/
def isLimitMapConeProetaleBaseChange {Z : Scheme.{u}} (i : Z ⟶ X) {I : Type u}
    [SmallCategory I] [IsCofiltered I] {Y : I ⥤ X.ProEt} {c : Cone Y}
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c)) :
    IsLimit ((Scheme.ProEt.forget Z ⋙ Over.forget Z).mapCone
      ((Scheme.proetaleBaseChange i).mapCone c)) := by
  have : IsConnected I := IsCofiltered.isConnected I
  have h₁ : IsLimit ((Scheme.ProEt.forget X).mapCone c) :=
    isLimitOfReflects (Over.forget X) hc
  have h₂ : IsLimit ((Over.pullback i).mapCone ((Scheme.ProEt.forget X).mapCone c)) :=
    isLimitOfPreserves (Over.pullback i) h₁
  exact isLimitOfPreserves (Over.forget Z) h₂

/-- **Direct image along a quasi-compact quasi-separated morphism preserves the essential image
of `ε⁻¹`.** If a sheaf of sets `H` on `Z_proétale` comes from `Z_étale` and `i : Z ⟶ X` is
quasi-compact and quasi-separated, then the direct image `i_* H` comes from `X_étale`: it
satisfies the colimit formula of Stacks 099S because the base change of a cofiltered limit of
affine objects of `X_étale` is a cofiltered limit of quasi-compact quasi-separated objects of
`Z_proétale` with affine transition morphisms, over which `H` satisfies it. -/
theorem etaleTypeInverseImage_essImage_pushforward {Z : Scheme.{u}} (i : Z ⟶ X) [QuasiCompact i]
    [QuasiSeparated i] (H : Sheaf (Scheme.ProEt.topology Z) (Type (max (u + 1) v)))
    (hH : (etaleTypeInverseImage.{v} Z).essImage H) :
    (etaleTypeInverseImage.{v} X).essImage
      (((Scheme.proetaleBaseChange i).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)).obj H) := by
  refine etaleTypeInverseImage_essImage_of_isColimit X _ fun I _ _ Y c hc hY ↦ ?_
  let Y' := (Y ⋙ X.etaleToProetale) ⋙ Scheme.proetaleBaseChange i
  have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (Y'.map f).left := fun {a b} f ↦
    have := hY a
    have := hY b
    have : IsAffineHom (Y.map f).left := isAffineHom_of_isAffine _
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (overPullback_isPullback i _ _ ((Y ⋙ X.etaleToProetale ⋙ Scheme.ProEt.forget X).map f))
      this
  have : ∀ k, CompactSpace (Y'.obj k).left := fun k ↦
    have : IsAffine ((𝟭 Scheme.{u}).obj ((Y ⋙ X.etaleToProetale).obj k).left) := hY k
    have hq : QuasiCompact (pullback.fst ((Y ⋙ X.etaleToProetale).obj k).hom i) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (IsPullback.of_hasPullback ((Y ⋙ X.etaleToProetale).obj k).hom i).flip ‹_›
    @QuasiCompact.compactSpace_of_compactSpace _ _ _ hq _
  have : ∀ k, QuasiSeparatedSpace (Y'.obj k).left := fun k ↦
    have : IsAffine ((𝟭 Scheme.{u}).obj ((Y ⋙ X.etaleToProetale).obj k).left) := hY k
    have hq : QuasiSeparated (pullback.fst ((Y ⋙ X.etaleToProetale).obj k).hom i) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback ((Y ⋙ X.etaleToProetale).obj k).hom i).flip ‹_›
    @quasiSeparatedSpace_of_quasiSeparated _ _ _ _ hq
  obtain ⟨hcol⟩ := nonempty_isColimit_of_mem_essImage Z Y'
    ((Scheme.proetaleBaseChange i).mapCone c) (isLimitMapConeProetaleBaseChange X i hc) H hH
  exact ⟨hcol⟩

/-- **The étale-to-pro-étale comparison commutes with base change.** For a morphism of schemes
`g : Y ⟶ X`, the two composites `X_étale ⥤ Y_proétale` — view an étale `X`-scheme as a pro-étale
one and base change it, or base change it and view it as a pro-étale `Y`-scheme — agree. -/
def etaleToProetaleCompProetaleBaseChangeIso {Y : Scheme.{u}} (g : Y ⟶ X) :
    X.etaleToProetale ⋙ Scheme.proetaleBaseChange g ≅
      Stacks.EtaleCohomology.smallEtaleBaseChange g ⋙ Y.etaleToProetale :=
  NatIso.ofComponents (fun _ ↦ MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _))
    (fun f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Inverse image commutes with `ε⁻¹`.** For a morphism of schemes `g : Y ⟶ X` and any
coefficient category `A` in which the inverse images exist, inverse image along `g` on the
pro-étale sites after `ε_X⁻¹` is `ε_Y⁻¹` after inverse image along `g` on the étale sites: both
are left adjoint to `ε_{X,*} g_* = g_* ε_{Y,*}`. -/
def etaleInverseImageCompSheafPullbackIso (A : Type*) [Category* A] {Y : Scheme.{u}} (g : Y ⟶ X)
    [HasWeakSheafify (Scheme.ProEt.topology X) A] [HasWeakSheafify (Scheme.ProEt.topology Y) A]
    [HasWeakSheafify Y.smallEtaleTopology A]
    [∀ F : X.Etaleᵒᵖ ⥤ A, X.etaleToProetale.op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ A, Y.etaleToProetale.op.HasLeftKanExtension F]
    [∀ F : X.ProEtᵒᵖ ⥤ A, (Scheme.proetaleBaseChange g).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ A,
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale A
        X.smallEtaleTopology (Scheme.ProEt.topology X) ⋙
      Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange g) A
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) ≅
    Functor.sheafPullbackConstruction.sheafPullback
        (Stacks.EtaleCohomology.smallEtaleBaseChange g) A X.smallEtaleTopology
        Y.smallEtaleTopology ⋙
      Functor.sheafPullbackConstruction.sheafPullback Y.etaleToProetale A
        Y.smallEtaleTopology (Scheme.ProEt.topology Y) :=
  let adjX := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale A
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  let adjY := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous Y.etaleToProetale A
    Y.smallEtaleTopology (Scheme.ProEt.topology Y)
  let adjB := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.proetaleBaseChange g) A (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
  let adjE := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Stacks.EtaleCohomology.smallEtaleBaseChange g) A X.smallEtaleTopology Y.smallEtaleTopology
  have : (X.etaleToProetale ⋙ Scheme.proetaleBaseChange g).IsContinuous
      X.smallEtaleTopology (Scheme.ProEt.topology Y) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange g ⋙ Y.etaleToProetale).IsContinuous
      X.smallEtaleTopology (Scheme.ProEt.topology Y) :=
    Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _
  let eR : (Scheme.proetaleBaseChange g).sheafPushforwardContinuous A _ _ ⋙
        X.etaleToProetale.sheafPushforwardContinuous A _ _ ≅
      Y.etaleToProetale.sheafPushforwardContinuous A _ _ ⋙
        (Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous A _ _ :=
    Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A)
      (J := X.smallEtaleTopology) (K := Scheme.ProEt.topology X) (L := Scheme.ProEt.topology Y) ≪≫
      Functor.sheafPushforwardContinuousIso (etaleToProetaleCompProetaleBaseChangeIso X g) _ _ _ ≪≫
      (Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A)
        (J := X.smallEtaleTopology) (K := Y.smallEtaleTopology)
        (L := Scheme.ProEt.topology Y)).symm
  (adjX.comp adjB).leftAdjointUniq ((adjE.comp adjY).ofNatIsoRight eR.symm)

/-- **Inverse image preserves the essential image of `ε⁻¹`.** For a morphism of schemes
`g : Y ⟶ X` and a sheaf of sets `H` on `X_proétale` coming from `X_étale`, the inverse image of
`H` along `g` comes from `Y_étale`: `g⁻¹ ε⁻¹ = ε⁻¹ g⁻¹`
(`AlgebraicGeometry.Scheme.etaleInverseImageCompSheafPullbackIso`). -/
theorem etaleTypeInverseImage_essImage_sheafPullback {Y : Scheme.{u}} (g : Y ⟶ X)
    (H : Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))
    (hH : (etaleTypeInverseImage.{v} X).essImage H) :
    (etaleTypeInverseImage.{v} Y).essImage
      ((Scheme.proetaleBaseChange g).sheafPullback (Type (max (u + 1) v))
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) |>.obj H) := by
  obtain ⟨A, ⟨e⟩⟩ := hH
  let T := Type (max (u + 1) v)
  let adjB := (Scheme.proetaleBaseChange g).sheafAdjunctionContinuous T
    (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
  let adjB' := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.proetaleBaseChange g) T (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
  exact ⟨_, ⟨((etaleInverseImageCompSheafPullbackIso X T g).app A).symm ≪≫
    (adjB'.leftAdjointUniq adjB).app _ ≪≫ (Functor.sheafPullback _ _ _ _).mapIso e⟩⟩

end Scheme

/-! ### Abelian sheaves -/

namespace ProEtale

variable (X : Scheme.{u})

/-- **The essential image of `ε⁻¹` on abelian sheaves is detected on underlying sheaves of
sets.** An abelian sheaf on `X_proétale` comes from `X_étale` exactly when its underlying sheaf of
sets does. -/
theorem epsilonInverseImage_essImage_iff_forget
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) :
    (epsilonInverseImage.{u, v} X).essImage F ↔
      (Scheme.etaleTypeInverseImage.{v} X).essImage
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})).obj F) := by
  let adj := X.etaleToProetale.sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := Scheme.isIso_unit_of_etaleToProetale_addCommGrp.{u, v} X adj
  rw [Scheme.etaleTypeInverseImage_essImage_iff,
    Scheme.essImage_iff_isIso_counit_app adj ((epsilonAdjunction.{u, v} X).leftAdjointUniq adj)]
  exact X.etaleToProetale.isIso_sheafAdjunctionContinuous_counit_app_iff_sheafCompose
    AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology (Scheme.ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) F

attribute [local instance] isGrothendieckAbelian_sheaf_proetale enoughInjectives_sheaf_proetale

/-- **Stacks 09B1 (1) for abelian sheaves.** The essential image of the fully faithful exact
functor `ε⁻¹ : Ab(X_étale) ⥤ Ab(X_proétale)` is a weak Serre subcategory. -/
theorem isWeakSerreClass_epsilonInverseImage_essImage :
    (epsilonInverseImage.{u, v} X).essImage.IsWeakSerreClass := by
  have : IsIso (epsilonAdjunction.{u, v} X).unit := isIso_epsilonAdjunction_unit X
  refine (epsilonAdjunction.{u, v} X).isWeakSerreClass_essImage
    ((epsilonAdjunction.{u, v} X).shortExact_map_of_isZero_rightDerived_one fun A ↦ ?_)
  exact (isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage X A).2 1 one_pos

end ProEtale

/-! ### Sheaves of modules -/

namespace Scheme

variable (X : Scheme.{u}) (Λ : Type v) [Ring Λ]

attribute [local instance] Stacks.ConstantSheaf.preservesSheafification_forget_moduleCat_of_univLE

/-- The forgetful functor of modules preserves the colimits computing the left Kan extension
along the inclusion of the small étale category: the comma categories are filtered. -/
instance preservesColimitsOfShape_costructuredArrow_etaleToProetale_forget_moduleCat
    (Y : X.ProEtᵒᵖ) :
    PreservesColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ)) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have : IsFiltered (CostructuredArrow X.etaleToProetale.op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence X.etaleToProetale Y.unop)
  have h₁ : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v w, max (u + 1) v w, u, u + 1} _
  have h₁' : PreservesColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v w}) :=
    @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _ _ h₁ _ _ _
  have h₂ : PreservesColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v w, v, u, u + 1} Λ
  have h₂' : PreservesColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      (forget₂ (ModuleCat.{max (u + 1) v w} Λ) AddCommGrpCat.{max (u + 1) v w}) :=
    @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _ h₂ _ _
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h₂' h₁'

/-- The unit of the chosen adjunction `ε⁻¹ ⊣ ε_*` on sheaves of `Λ`-modules is an isomorphism:
it is so after passing to underlying sheaves of sets. -/
theorem isIso_sheafAdjunctionContinuous_unit_moduleCat :
    IsIso (X.etaleToProetale.sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v w} Λ)
      X.smallEtaleTopology (Scheme.ProEt.topology X)).unit := by
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_type.{u, max v w} X
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_addCommGrp.{u, max v w} X
  have : IsIso (X.etaleToProetale.sheafAdjunctionContinuous (Type (max (u + 1) v w))
      X.smallEtaleTopology (Scheme.ProEt.topology X)).unit :=
    Scheme.isIso_unit_of_etaleToProetale.{u, max v w} X _
  have : ∀ F, IsIso ((X.etaleToProetale.sheafAdjunctionContinuous
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F) :=
    fun F ↦ X.etaleToProetale.isIso_sheafAdjunctionContinuous_unit_app_of_sheafCompose
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ)) F inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 099T for sheaves of `Λ`-modules.** The unit `ℱ ⟶ ε_* ε⁻¹ ℱ` of the adjunction
`ε⁻¹ ⊣ ε_*` on sheaves of `Λ`-modules is an isomorphism, so `ε⁻¹` is fully faithful. -/
instance isIso_etaleInverseImage_unit :
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit := by
  let adj := X.etaleToProetale.sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v w} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := isIso_sheafAdjunctionContinuous_unit_moduleCat.{w, v} X Λ
  exact Stacks.Adjunction.isIso_unit_of_comp_iso_id _
    (Functor.isoWhiskerRight ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      X.etaleToProetale (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).leftAdjointUniq adj) _ ≪≫ (asIso adj.unit).symm)

/-- **The essential image of `ε⁻¹` on sheaves of `Λ`-modules is detected on underlying sheaves
of sets.** -/
theorem etaleInverseImage_essImage_iff_forget
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :
    (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage F ↔
      (Scheme.etaleTypeInverseImage.{max v w} X).essImage
        ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ))).obj F) := by
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_type.{u, max v w} X
  have := Scheme.hasPointwiseLeftKanExtension_etaleToProetale_addCommGrp.{u, max v w} X
  let adj := X.etaleToProetale.sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v w} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)
  have := isIso_sheafAdjunctionContinuous_unit_moduleCat.{w, v} X Λ
  rw [Scheme.etaleTypeInverseImage_essImage_iff, Scheme.essImage_iff_isIso_counit_app adj
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).leftAdjointUniq adj)]
  exact X.etaleToProetale.isIso_sheafAdjunctionContinuous_counit_app_iff_sheafCompose
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
    (CategoryTheory.forget (ModuleCat.{max (u + 1) v w} Λ)) F

/-- **The essential image of `ε⁻¹` on sheaves of `Λ`-modules is detected on underlying abelian
sheaves.** -/
theorem etaleInverseImage_essImage_iff_forget₂
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ)) :
    (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage F ↔
      (ProEtale.epsilonInverseImage.{u, max v w} X).essImage
        ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) v w} Λ)
          AddCommGrpCat.{max (u + 1) v w})).obj F) := by
  rw [etaleInverseImage_essImage_iff_forget, ProEtale.epsilonInverseImage_essImage_iff_forget]
  rfl

end Scheme

end AlgebraicGeometry

end
