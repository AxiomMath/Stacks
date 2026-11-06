module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonEssentialImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.InverseImageInjectiveLimit

/-!
# Direct images along a quasi-compact quasi-separated morphism and the pro-étale site

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and let
`ε : X_proétale → X_étale` be the comparison morphism of sites, with inverse image `ε⁻¹`.
For a sheaf `ℱ` on `X_étale` the pro-étale direct image of `ε⁻¹ℱ` is the inverse image of the
étale direct image of `ℱ`:

  `f_{proétale,*} ε⁻¹ℱ = ε⁻¹ f_{étale,*} ℱ`,

for sheaves of sets and for abelian sheaves (Stacks 09A6 (1)), and its derived form

  `R f_{proétale,*} ε⁻¹ℱ = ε⁻¹ R f_{étale,*} ℱ`

for abelian sheaves, indeed for bounded below complexes of them (Stacks 09A6 (2)).

## Main definitions

* `AlgebraicGeometry.Scheme.etaleToProetaleDirectImageIso`: the isomorphism
  `ε_* f_{proétale,*} ≅ f_{étale,*} ε_*` of direct images, for any coefficient category; the two
  composite functors of sites `Y_étale ⥤ X_proétale` agree.
* `AlgebraicGeometry.Scheme.proetaleDirectImageEtaleInverseImageIso`: **Stacks 09A6 (1)** for
  sheaves of sets.
* `AlgebraicGeometry.ProEtale.proetaleDirectImageEpsilonInverseImageIso`: the same isomorphism for
  abelian sheaves.
* `AlgebraicGeometry.ProEtale.proetaleDirectImageRightDerivedEpsilonInverseImageIso`:
  **Stacks 09A6 (2)**, `R f_{proétale,*} ∘ ε⁻¹ ≅ ε⁻¹ ∘ R f_{étale,*}` on `D⁺`.

## Main results

* `AlgebraicGeometry.Scheme.etaleTypeInverseImage_essImage_proetaleDirectImage`: the pro-étale
  direct image of `ε⁻¹ℱ` lies in the essential image of `ε⁻¹`.
* `ProEtale.isZero_rightDerived_sheafSections_proetaleBaseChange_epsilonInverseImage`:
  `H^q(X ×_Y V, ε⁻¹ℐ) = 0` for `q > 0`, an injective abelian sheaf `ℐ` on `X_étale` and `V`
  ind-étale over an affine object of `Y_étale`.

## Implementation notes

The source evaluates the canonical map `ε⁻¹ f_{étale,*} ℱ ⟶ f_{proétale,*} ε⁻¹ℱ` on objects
`V = lim V_i` of `Y_proétale` which are limits of affine schemes étale over `Y`, where both
sides are `colim Γ(X ×_Y V_i, ℱ)` by Stacks 099S. Here the same colimit computation is used to
show that `f_{proétale,*} ε⁻¹ℱ` lies in the essential image of the fully faithful functor `ε⁻¹`
(`AlgebraicGeometry.Scheme.etaleTypeInverseImage_essImage_pushforward`): the stages
`X ×_Y V_i` are quasi-compact and quasi-separated with affine transition morphisms because `f` is
quasi-compact and quasi-separated. A pro-étale sheaf `𝒢` in that essential image is
`ε⁻¹ ε_* 𝒢` through the counit, and
`ε_* f_{proétale,*} ε⁻¹ℱ = f_{étale,*} ε_* ε⁻¹ℱ = f_{étale,*} ℱ` by Stacks 099T, which gives the
isomorphism. For abelian sheaves membership in the essential image is read off the underlying
sheaf of sets (`AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_iff_forget`).

For part (2) the source compares `colim H^q(X ×_Y V_i, ℱ)` with `H^q(X ×_Y V, ε⁻¹ℱ)` through
Stacks 09YQ. Here it is derived from part (1) by acyclicity instead: `ε⁻¹` is exact and
`f_{proétale,*} ε⁻¹ ≅ ε⁻¹ f_{étale,*}`, so the derived comparison holds as soon as `ε⁻¹ℐ` is
acyclic for `f_{proétale,*}` for every injective `ℐ` (Stacks 015M); the higher direct images of
`ε⁻¹ℐ` are the sheafifications of `V ↦ H^q(X ×_Y V, ε⁻¹ℐ)`, and these groups vanish because
`X ×_Y V` is a limit of quasi-compact quasi-separated étale `X`-schemes with affine transition
morphisms (`ProEtale.isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit`).
The statement is for bounded below complexes, which contains the source's statement for an
abelian sheaf placed in degree zero.

## References

* [Stacks Project, Tag 09A6](https://stacks.math.columbia.edu/tag/09A6)
* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The two composite functors of sites `Y_étale ⥤ X_proétale` agree: viewing an étale
`Y`-scheme as a pro-étale one and base changing it to `X` is base changing it to `X` and viewing
it as a pro-étale `X`-scheme. Consequently `ε_* f_{proétale,*} ≅ f_{étale,*} ε_*` on sheaves
with values in any category. -/
def etaleToProetaleDirectImageIso (A : Type w) [Category A] :
    (Scheme.proetaleBaseChange f).sheafPushforwardContinuous A (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology X) ⋙
      Y.etaleToProetale.sheafPushforwardContinuous A Y.smallEtaleTopology
        (Scheme.ProEt.topology Y) ≅
    X.etaleToProetale.sheafPushforwardContinuous A X.smallEtaleTopology
        (Scheme.ProEt.topology X) ⋙
      (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology :=
  have : (Y.etaleToProetale ⋙ Scheme.proetaleBaseChange f).IsContinuous
      Y.smallEtaleTopology (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Y) _
  have : (Stacks.EtaleCohomology.smallEtaleBaseChange f ⋙ X.etaleToProetale).IsContinuous
      Y.smallEtaleTopology (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _
  Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A)
      (J := Y.smallEtaleTopology) (K := Scheme.ProEt.topology Y) (L := Scheme.ProEt.topology X) ≪≫
    Functor.sheafPushforwardContinuousIso (etaleToProetaleCompProetaleBaseChangeIso Y f) _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _) (A := A)
      (J := Y.smallEtaleTopology) (K := X.smallEtaleTopology)
      (L := Scheme.ProEt.topology X)).symm

/-- **The comparison isomorphism of a pro-étale direct image with an étale one.** Let
`L_X ⊣ ε_*` and `L_Y ⊣ ε_*` be adjunctions between sheaves on the small étale and the small
pro-étale sites of `X` and `Y`, whose units are isomorphisms, and suppose that for every sheaf
`ℱ` on `X_étale` the counit of `L_Y ⊣ ε_*` is an isomorphism at `f_{proétale,*} L_X ℱ`. Then
`L_Y f_{étale,*} ≅ f_{proétale,*} L_X`: the composite
`L_Y f_{étale,*} ≅ L_Y f_{étale,*} ε_* L_X ≅ L_Y ε_* f_{proétale,*} L_X ≅ f_{proétale,*} L_X`. -/
def proetaleDirectImageCompIsoOfIsIsoCounit {A : Type w} [Category A]
    {LX : Sheaf X.smallEtaleTopology A ⥤ Sheaf (Scheme.ProEt.topology X) A}
    {LY : Sheaf Y.smallEtaleTopology A ⥤ Sheaf (Scheme.ProEt.topology Y) A}
    (adjX : LX ⊣ X.etaleToProetale.sheafPushforwardContinuous A X.smallEtaleTopology
      (Scheme.ProEt.topology X))
    (adjY : LY ⊣ Y.etaleToProetale.sheafPushforwardContinuous A Y.smallEtaleTopology
      (Scheme.ProEt.topology Y)) [IsIso adjX.unit]
    (hY : ∀ F, IsIso (adjY.counit.app (((Scheme.proetaleBaseChange f).sheafPushforwardContinuous A
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (LX.obj F)))) :
    (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology ⋙ LY ≅
      LX ⋙ (Scheme.proetaleBaseChange f).sheafPushforwardContinuous A (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology X) :=
  have : IsIso (Functor.whiskerLeft (LX ⋙ (Scheme.proetaleBaseChange f).sheafPushforwardContinuous
      A (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) adjY.counit) :=
    have : ∀ F, IsIso ((Functor.whiskerLeft (LX ⋙
        (Scheme.proetaleBaseChange f).sheafPushforwardContinuous A (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)) adjY.counit).app F) := hY
    NatIso.isIso_of_isIso_app _
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso adjX.unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft LX (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft LX
      (Functor.isoWhiskerRight (etaleToProetaleDirectImageIso f A).symm LY) ≪≫
    Functor.isoWhiskerLeft LX (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    asIso (Functor.whiskerLeft (LX ⋙ (Scheme.proetaleBaseChange f).sheafPushforwardContinuous
      A (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) adjY.counit) ≪≫
    Functor.rightUnitor _

variable [QuasiCompact f] [QuasiSeparated f]

/-- The pro-étale direct image of the inverse image `ε⁻¹ℱ` of a sheaf of sets on `X_étale`
lies in the essential image of `ε⁻¹`. -/
theorem etaleTypeInverseImage_essImage_proetaleDirectImage
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) :
    (etaleTypeInverseImage.{v} Y).essImage
      (((Scheme.proetaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          ((etaleTypeInverseImage.{v} X).obj F)) :=
  etaleTypeInverseImage_essImage_pushforward Y f _
    ((etaleTypeInverseImage.{v} X).obj_mem_essImage F)

/-- **Stacks 09A6 (1).** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes. For a sheaf of sets `ℱ` on `X_étale`,
`f_{proétale,*} ε⁻¹ℱ = ε⁻¹ f_{étale,*} ℱ`, naturally in `ℱ`. -/
def proetaleDirectImageEtaleInverseImageIso :
    (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) Y.smallEtaleTopology X.smallEtaleTopology ⋙
        etaleTypeInverseImage.{v} Y ≅
      etaleTypeInverseImage.{v} X ⋙
        (Scheme.proetaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} X
  have := Scheme.isIso_proetaleInverseImageAdjunction_unit.{u, v} Y
  let adjY := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous Y.etaleToProetale
    (Type (max (u + 1) v)) Y.smallEtaleTopology (Scheme.ProEt.topology Y)
  have hff := adjY.fullyFaithfulLOfIsIsoUnit
  have : (etaleTypeInverseImage.{v} Y).Full := hff.full
  have : (etaleTypeInverseImage.{v} Y).Faithful := hff.faithful
  proetaleDirectImageCompIsoOfIsIsoCounit f
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)) adjY
    (fun F ↦ (adjY.isIso_counit_app_iff_mem_essImage).2
      (etaleTypeInverseImage_essImage_proetaleDirectImage f F))

end Scheme

namespace ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The pro-étale direct image of `ε⁻¹ℱ` for an abelian sheaf `ℱ` on `X_étale` lies in the
essential image of `ε⁻¹`: its underlying sheaf of sets is the pro-étale direct image of the
inverse image of the underlying sheaf of sets of `ℱ`. -/
theorem epsilonInverseImage_essImage_proetaleDirectImage
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (epsilonInverseImage.{u, v} Y).essImage
      (((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          ((epsilonInverseImage.{u, v} X).obj F)) := by
  rw [epsilonInverseImage_essImage_iff_forget]
  exact (Scheme.etaleTypeInverseImage.{v} Y).essImage.prop_of_iso
    (((Scheme.proetaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).mapIso
        (Scheme.proetaleUnderlyingSetIso.{u, v} X (epsilonAdjunction.{u, v} X) F)).symm
    (Scheme.etaleTypeInverseImage_essImage_proetaleDirectImage f _)

/-- **Stacks 09A6 (1) for abelian sheaves.** Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes. For an abelian sheaf `ℱ` on `X_étale`,
`f_{proétale,*} ε⁻¹ℱ = ε⁻¹ f_{étale,*} ℱ`, naturally in `ℱ`. -/
def proetaleDirectImageEpsilonInverseImageIso :
    (Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) v} Y.smallEtaleTopology X.smallEtaleTopology ⋙
        epsilonInverseImage.{u, v} Y ≅
      epsilonInverseImage.{u, v} X ⋙
        (Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  have hff := (epsilonAdjunction.{u, v} Y).fullyFaithfulLOfIsIsoUnit
  have : (epsilonInverseImage.{u, v} Y).Full := hff.full
  have : (epsilonInverseImage.{u, v} Y).Faithful := hff.faithful
  Scheme.proetaleDirectImageCompIsoOfIsIsoCounit f (epsilonAdjunction.{u, v} X)
    (epsilonAdjunction.{u, v} Y)
    (fun F ↦ ((epsilonAdjunction.{u, v} Y).isIso_counit_app_iff_mem_essImage).2
      (epsilonInverseImage_essImage_proetaleDirectImage f F))

/-! ### The derived form -/

section Derived

attribute [local instance] HasDerivedCategory.standard isGrothendieckAbelian_sheaf_proetale
  enoughInjectives_sheaf_proetale

/-- Abelian sheaves on the small étale site of `Z` admit sheafification. -/
local instance (Z : Scheme.{u}) : HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Scheme.hasSheafify_smallEtaleTopology Z

/-- The category of abelian sheaves on the small étale site of `Z` is abelian. -/
local instance (Z : Scheme.{u}) :
    Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) := sheafIsAbelian

/-- The category of abelian sheaves on the small étale site of `Z` has enough injectives. -/
local instance (Z : Scheme.{u}) :
    EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  Stacks.EtaleCohomology.enoughInjectives_sheaf_smallEtale.{u, v} Z

/-- The pro-étale direct image functor on abelian sheaves along `f` is additive. -/
instance : ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).Additive :=
  ((Scheme.proetaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).right_adjoint_additive

/-- The pro-étale direct image of abelian sheaves along `f` has a right derived functor on
bounded below complexes, with unit `Functor.rightDerivedFunctorPlusUnith`. -/
local instance : (((Scheme.proetaleBaseChange f).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (Scheme.ProEt.topology X)
        AddCommGrpCat.{max (u + 1) v})) :=
  Functor.HasRightDerivedFunctor.mk'
    (RF := ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightDerivedFunctorPlus)
    (α := ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightDerivedFunctorPlusUnith)

/-- **The derived comparison from acyclicity.** If `ε⁻¹ℐ` is acyclic for the pro-étale direct
image along `f` for every injective abelian sheaf `ℐ` on `X_étale`, then
`R f_{proétale,*} ∘ ε⁻¹ ≅ ε⁻¹ ∘ R f_{étale,*}` on bounded below derived categories, where `ε⁻¹`
on `D⁺` is `ε⁻¹` applied termwise (its right derived functor, `ε⁻¹` being exact). It is the
composite of `R(f_{proétale,*} ∘ ε⁻¹) ≅ R f_{proétale,*} ∘ ε⁻¹` (Stacks 015M), of the
isomorphism `f_{proétale,*} ε⁻¹ ≅ ε⁻¹ f_{étale,*}` of Stacks 09A6 (1) for abelian sheaves, and of
`R(ε⁻¹ ∘ f_{étale,*}) ≅ ε⁻¹ ∘ R f_{étale,*}`, `ε⁻¹` being exact. -/
def proetaleDirectImageRightDerivedIsoOfRightAcyclic
    (h : ∀ I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, Injective I →
      ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightAcyclic
          ((epsilonInverseImage.{u, v} X).obj I)) :
    (epsilonInverseImage.{u, v} X).rightDerivedFunctorPlus ⋙
        ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightDerivedFunctorPlus ≅
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} Y.smallEtaleTopology
            X.smallEtaleTopology).rightDerivedFunctorPlus ⋙
        (epsilonInverseImage.{u, v} Y).rightDerivedFunctorPlus :=
  (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ _ h).symm ≪≫
    Functor.rightDerivedFunctorPlusNatIso (proetaleDirectImageEpsilonInverseImageIso f).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfExact _ _ _ (Iso.refl _)).symm

omit [QuasiCompact f] [QuasiSeparated f] in
/-- **Acyclicity of `ε⁻¹ℐ` for the pro-étale direct image, from the vanishing of cohomology over
`X ×_Y V`.** If for every injective abelian sheaf `ℐ` on `X_étale`, every object `V` of
`Y_proétale` ind-étale over an affine object of `Y_étale` and every `q > 0` the cohomology
`H^q(X ×_Y V, ε⁻¹ℐ)` vanishes, then `ε⁻¹ℐ` is acyclic for `f_{proétale,*}`: its higher direct
images are the sheafifications of `V ↦ H^q(X ×_Y V, ε⁻¹ℐ)`, and those objects cover
`Y_proétale`. -/
theorem rightAcyclic_epsilonInverseImage_of_isZero
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ (V : Y.ProEt), IsAffineIndEtaleOverEtale Y V → ∀ q : ℕ, 0 < q →
      IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
        (op ((Scheme.proetaleBaseChange f).obj V))).rightDerived q).obj
          ((epsilonInverseImage.{u, v} X).obj I))) :
    ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightAcyclic
        ((epsilonInverseImage.{u, v} X).obj I) := by
  have := ((Scheme.proetaleBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).isRightAdjoint
  rw [(((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _).2
        inferInstance]
  intro i hi
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _).symm
  refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (Scheme.proetaleBaseChange f) q _ (fun V ↦ ?_)
  refine ⟨fun (W : Y.ProEt) (_ : W ⟶ V) ↦ IsAffineIndEtaleOverEtale Y W,
    generate_isAffineIndEtaleOverEtale_mem Y V, fun W _ hW ↦ h W hW q (by exact_mod_cast hi)⟩

/-- **The cohomology of `ε⁻¹ℐ` over `X ×_Y V` vanishes.** Let `f : X ⟶ Y` be quasi-compact and
quasi-separated, let `ℐ` be an injective abelian sheaf on `X_étale` and let `V` be an object of
`Y_proétale` ind-étale over an affine object of `Y_étale`. Then `H^q(X ×_Y V, ε⁻¹ℐ) = 0` for
`q > 0`: writing `V = lim V_a` with `V_a` affine and étale over `Y`, the object `X ×_Y V` of
`X_proétale` is the limit of the quasi-compact and quasi-separated étale `X`-schemes
`X ×_Y V_a`, with affine transition morphisms. -/
theorem isZero_rightDerived_sheafSections_proetaleBaseChange_epsilonInverseImage
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I] (V : Y.ProEt)
    (hV : IsAffineIndEtaleOverEtale Y V) (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}).obj
      (op ((Scheme.proetaleBaseChange f).obj V))).rightDerived q).obj
        ((epsilonInverseImage.{u, v} X).obj I)) := by
  let : Category.{u} (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ X) :=
    inferInstanceAs (Category X.Etale)
  obtain ⟨A, _, _, Vb, πV, hVa, ⟨hVlim⟩⟩ := hV.exists_isLimit
  let D : A ⥤ X.ProEt := (Vb ⋙ Y.etaleToProetale) ⋙ Scheme.proetaleBaseChange f
  have hDe (a : A) : Etale (D.obj a).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback ((Vb ⋙ Y.etaleToProetale).obj a).hom f) (Vb.obj a).prop
  let Ub : A ⥤ X.Etale := MorphismProperty.Comma.lift
    (D ⋙ MorphismProperty.Comma.forget _ _ _ _ _) hDe (fun _ ↦ trivial) (fun _ ↦ trivial)
  have : ∀ {a b : A} (g : a ⟶ b), IsAffineHom (Ub.map g).left := fun {a b} g ↦
    have := hVa a
    have := hVa b
    have : IsAffineHom (Vb.map g).left := isAffineHom_of_isAffine _
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (overPullback_isPullback f _ _ ((Vb ⋙ Y.etaleToProetale ⋙ Scheme.ProEt.forget Y).map g))
      this
  have : ∀ a, CompactSpace (Ub.obj a).left := fun a ↦
    have : IsAffine ((𝟭 Scheme.{u}).obj ((Vb ⋙ Y.etaleToProetale).obj a).left) := hVa a
    have hq : QuasiCompact (pullback.fst ((Vb ⋙ Y.etaleToProetale).obj a).hom f) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (IsPullback.of_hasPullback ((Vb ⋙ Y.etaleToProetale).obj a).hom f).flip ‹_›
    @QuasiCompact.compactSpace_of_compactSpace _ _ _ hq _
  have : ∀ a, QuasiSeparatedSpace (Ub.obj a).left := fun a ↦
    have : IsAffine ((𝟭 Scheme.{u}).obj ((Vb ⋙ Y.etaleToProetale).obj a).left) := hVa a
    have hq : QuasiSeparated (pullback.fst ((Vb ⋙ Y.etaleToProetale).obj a).hom f) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback ((Vb ⋙ Y.etaleToProetale).obj a).hom f).flip ‹_›
    @quasiSeparatedSpace_of_quasiSeparated _ _ _ _ hq
  exact isZero_rightDerived_sheafSections_epsilonInverseImage_of_isLimit I Ub
    ((Scheme.proetaleBaseChange f).mapCone (Cone.mk V πV)).π
    (Scheme.isLimitMapConeProetaleBaseChange Y f hVlim) q hq

/-- **Stacks 09A6 (2).** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes. Then `R f_{proétale,*} ∘ ε⁻¹ ≅ ε⁻¹ ∘ R f_{étale,*}` on bounded below derived categories
of abelian sheaves, where `ε⁻¹` on `D⁺` is `ε⁻¹` applied termwise (its right derived functor,
`ε⁻¹` being exact); at an abelian sheaf `ℱ` on `X_étale`, placed in degree zero, this is
`R f_{proétale,*} ε⁻¹ℱ = ε⁻¹ R f_{étale,*} ℱ`.

It is `AlgebraicGeometry.ProEtale.proetaleDirectImageRightDerivedIsoOfRightAcyclic`: for an
injective abelian sheaf `ℐ` on `X_étale` the higher direct images of `ε⁻¹ℐ` along `f` are the
sheafifications of `V ↦ H^q(X ×_Y V, ε⁻¹ℐ)`, which vanish on the objects `V` ind-étale over an
affine object of `Y_étale`
(`ProEtale.isZero_rightDerived_sheafSections_proetaleBaseChange_epsilonInverseImage`),
and those objects cover `Y_proétale`. -/
def proetaleDirectImageRightDerivedEpsilonInverseImageIso :
    (epsilonInverseImage.{u, v} X).rightDerivedFunctorPlus ⋙
        ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).rightDerivedFunctorPlus ≅
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} Y.smallEtaleTopology
            X.smallEtaleTopology).rightDerivedFunctorPlus ⋙
        (epsilonInverseImage.{u, v} Y).rightDerivedFunctorPlus :=
  proetaleDirectImageRightDerivedIsoOfRightAcyclic f fun I _ ↦
    rightAcyclic_epsilonInverseImage_of_isZero f I fun V hV q hq ↦
      isZero_rightDerived_sheafSections_proetaleBaseChange_epsilonInverseImage f I V hV q hq

end Derived

end ProEtale

end AlgebraicGeometry

end
