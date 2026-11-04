module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.DirectImageGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# The Leray spectral sequence on small étale sites, read as a vanishing criterion

For a morphism of schemes `f : X ⟶ Y` and an abelian sheaf `𝓕` on `X_étale`, the Leray spectral
sequence `E₂^{p,q} = H^p(Y, R^qf_*𝓕) ⟹ H^{p+q}(X, 𝓕)` (Stacks 0732) shows that `H^n(X, 𝓕) = 0`
as soon as `H^{n-q}(Y, R^qf_*𝓕) = 0` for every `q ≤ n`; its relative version
`R^pg_*R^qf_*𝓕 ⟹ R^{p+q}(g ∘ f)_*𝓕` shows the same for higher direct images along a composite.
Both are the antidiagonal vanishing of the Grothendieck spectral sequence,
`Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero`, applied to
`f_* : Ab(X_étale) ⥤ Ab(Y_étale)`, which preserves injective objects, followed by global
sections or by a further direct image.

These are the forms of the Leray spectral sequence that the cohomological dimension estimates of
Stacks 0F0S, 0F0V and 0F0X use.

## Main results

* `subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived`:
  `H^n(X, 𝓕) = 0` if `H^{n-q}(Y, R^qf_*𝓕) = 0` for every `q ≤ n`.
* `isZero_rightDerived_comp_of_forall_isZero`:
  `R^n(g ∘ f)_*𝓕 = 0` if `R^{n-q}g_*(R^qf_*𝓕) = 0` for every `q ≤ n`.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology.LerayVanishing

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

variable {X Y Z : Scheme.{u}}

/-- Direct image of abelian sheaves on the small étale sites preserves injective objects, in the
spelling `smallEtaleDirectImageAb`. -/
local instance preservesInjectiveObjects_smallEtaleDirectImageAb (f : X ⟶ Y) :
    (smallEtaleDirectImageAb.{u + 1} f).PreservesInjectiveObjects :=
  smallEtalePushforwardAb_preservesInjectiveObjects f

/-- **Leray, as a vanishing criterion** (Stacks 0732), at the coefficients
`AddCommGrpCat.{max (u + 1) v}`. For `f : X ⟶ Y` and an abelian sheaf `𝓕` on `X_étale`,
`H^n(X, 𝓕) = 0` as soon as `H^{n-q}(Y, R^qf_*𝓕) = 0` for every `q ≤ n`. -/
public theorem subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{max (u + 1) v} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n → Subsingleton (Sheaf.H.{max (u + 1) v}
      (((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj F) (n - q))) :
    Subsingleton (Sheaf.H.{max (u + 1) v} F n) := by
  have : (etaleAbelianDirectImage.{u, v} f).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
  have : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).Additive :=
    Stacks.Cohomology.GlobalSections.additive_Γ _
  have : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).Additive :=
    Stacks.Cohomology.GlobalSections.additive_Γ _
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}]
  have hc := Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero
    (etaleAbelianDirectImage.{u, v} f)
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) F n
    (fun q hq => (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
      _ _ _).1 (h q hq))
  exact hc.of_iso ((Functor.rightDerivedIsoOfNatIso
    (etaleAbelianDirectImageCompΓIso.{u, v} f) n).app F).symm

/-- **Leray, as a vanishing criterion** (Stacks 0732). For `f : X ⟶ Y` and an abelian sheaf `𝓕`
on `X_étale`, `H^n(X, 𝓕) = 0` as soon as `H^{n-q}(Y, R^qf_*𝓕) = 0` for every `q ≤ n`. This is
`subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage` at the coefficients
`AddCommGrpCat.{u + 1}`. -/
public theorem subsingleton_sheafH_of_forall_subsingleton_sheafH_rightDerived (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n → Subsingleton (Sheaf.H.{u + 1, u + 1}
      (((smallEtaleDirectImageAb.{u + 1} f).rightDerived q).obj F) (n - q))) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F n) :=
  subsingleton_sheafH_of_forall_rightDerived_etaleAbelianDirectImage.{u, 0} f F n h

/-- **Relative Leray, as a vanishing criterion.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and an abelian
sheaf `𝓕` on `X_étale`, `R^n(g ∘ f)_*𝓕 = 0` as soon as `R^{n-q}g_*(R^qf_*𝓕) = 0` for every
`q ≤ n`. -/
public theorem isZero_rightDerived_comp_of_forall_isZero (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n → IsZero (((smallEtaleDirectImageAb.{u + 1} g).rightDerived (n - q)).obj
      (((smallEtaleDirectImageAb.{u + 1} f).rightDerived q).obj F))) :
    IsZero (((smallEtaleDirectImageAb.{u + 1} (f ≫ g)).rightDerived n).obj F) :=
  (Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero
    (smallEtaleDirectImageAb.{u + 1} f) (smallEtaleDirectImageAb.{u + 1} g) F n h).of_iso
    ((Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbCompIso f g) n).app F).symm

/-- **Relative Leray at a geometric point, as a vanishing criterion.** For `f : X ⟶ Y`,
`g : Y ⟶ Z`, an abelian sheaf `𝓕` on `X_étale` and a geometric point `z` of `Z`, the stalk of
`R^n(g ∘ f)_*𝓕` at `z` vanishes as soon as the stalks at `z` of `R^{n-q}g_*(R^qf_*𝓕)` vanish
for every `q ≤ n`: the stalk functor is exact, so it commutes with the right derived functors of
`g_*`, and the antidiagonal criterion applies to `f_*` followed by `g_*` and the stalk. -/
public theorem isZero_stalk_rightDerived_comp_of_forall_isZero (f : X ⟶ Y) (g : Y ⟶ Z)
    (z : GeometricPoint Z) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n → IsZero ((smallEtaleStalkAb z.hom).obj
      (((smallEtaleDirectImageAb.{u + 1} g).rightDerived (n - q)).obj
        (((smallEtaleDirectImageAb.{u + 1} f).rightDerived q).obj F)))) :
    IsZero ((smallEtaleStalkAb z.hom).obj
      (((smallEtaleDirectImageAb.{u + 1} (f ≫ g)).rightDerived n).obj F)) := by
  let E := smallEtaleStalkAb z.hom
  have hc := Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero
    (smallEtaleDirectImageAb.{u + 1} f) (smallEtaleDirectImageAb.{u + 1} g ⋙ E) F n
    (fun q hq => (h q hq).of_iso
      (((smallEtaleDirectImageAb.{u + 1} g).rightDerivedCompIso E (n - q)).app _))
  exact hc.of_iso <|
    E.mapIso ((Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbCompIso f g) n).app
      F).symm ≪≫
    (((smallEtaleDirectImageAb.{u + 1} f ⋙ smallEtaleDirectImageAb.{u + 1} g).rightDerivedCompIso
      E n).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (Functor.associator _ _ _) n).app F

end Stacks.EtaleCohomology.LerayVanishing

end
