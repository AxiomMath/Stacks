module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RelativeMayerVietoris
public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.NormalSepClosedConstantDirectImage

/-!
# The multiplicative group on a scheme étale over a field

Let `k` be a field and `W` a scheme étale over `Spec k`. Then `W` is a disjoint union of spectra
of finite separable extensions of `k` ([Stacks, Tag 02GL]), so if the positive-degree étale
cohomology of `𝐆_m` vanishes over every finite separable extension of `k` then it vanishes over
`W`, the sections of a sheaf over a coproduct being the product of the sections. Sheafifying, the
higher direct images of `𝐆_m` along any morphism out of `Spec k` vanish: the higher direct image
is the sheafification of `V ↦ H^q(Spec k ×_Y V, 𝐆_m)` ([Stacks, Tag 03Q8]) and every base change
of `Spec k` along an étale `V ⟶ Y` is a scheme étale over `k`.

## Main results

* `etaleRestriction_obj_multiplicativeSheaf`: the restriction of `𝐆_m` along an étale morphism
  `j : U ⟶ X` is `𝐆_m` on `U`.
* `isZero_rightDerived_etaleSections_multiplicativeSheaf`: the derived sections of `𝐆_{m,X}` over
  a scheme étale over `X` are the étale cohomology of `𝐆_m` on that scheme.
* `isZero_rightDerived_etaleSections_multiplicativeSheaf_over_field`: the derived sections of
  `𝐆_m` over an arbitrary object of the small étale site of a field vanish, given the vanishing
  over the finite separable extensions.
* `isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field`: the higher direct
  images of `𝐆_m` along a morphism out of the spectrum of a field vanish, given the same.

## Implementation notes

**Why no hypothesis beyond the vanishing over the finite separable extensions.** The three steps
are each unconditional in this library. [Stacks, Tag 03Q8] in the
`AlgebraicGeometry.Scheme.Etale` model, together with density of the objects with affine source,
is `Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforward_of_affine_sections`, so the
sheaf-level statement follows from the levelwise one with no condition on the degree or on the
target. The identification of the derived sections over an object `W` of `X_étale` with the
derived global sections on `W`'s own small étale site is [Stacks, Tag 03YU] (2) through
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardRightDerivedSectionsIso`, at
`u := AlgebraicGeometry.Scheme.Etale.smallEtaleCompose W.hom`; its two side conditions,
exactness and preservation of injectives by the restriction, are
`Stacks.EtaleCohomology.etaleRestriction_preservesColimits` and
`Stacks.EtaleCohomology.etaleRestriction_preservesInjectiveObjects`. And the passage from a
coproduct to its summands is
`Stacks.EtaleCohomology.isZero_rightDerived_etaleCoproduct_of_components`, whose index type is
arbitrary in the universe of the schemes, so *no quasi-compactness* of `W` is needed and
[Stacks, Tag 02GL] is used in the form that counts no summands,
`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable`.

**That `𝐆_m` restricts to `𝐆_m` is definitional.** Restriction along `j : U ⟶ X` is
precomposition with `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose j`, which does not change
the underlying scheme of an object, and `𝐆_m` on `X_étale` is the invertible global functions of
that underlying scheme (`Stacks.EtaleCohomology.multiplicativePresheaf_eq`). So the two sheaves
have the same underlying presheaf on the nose.

**Coefficients and universes.** Abelian sheaves are taken in `AddCommGrpCat.{u + 1}` for schemes
in `Scheme.{u}` and cohomology is `CategoryTheory.Sheaf.H.{u + 1, u + 1}`. The Grothendieck
abelian structure is taken with its coefficient universe pinned, as
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse`, because the
general instance is indexed by `max (u + 1) v` and instance search cannot solve
`max (u + 1) ?v = u + 1`; that is what makes `HasExt.{u + 1}` available.

## References

* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-! ### Restriction of `𝐆_m` along an étale morphism -/

/-- The restriction of `𝐆_m` along an étale morphism `j : U ⟶ X` is `𝐆_m` on `U`, on the
nose. -/
theorem etaleRestriction_obj_multiplicativeSheaf {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleRestriction.{u, v} j).obj (Stacks.Kummer.multiplicativeSheaf.{u, v} X) =
      Stacks.Kummer.multiplicativeSheaf.{u, v} U :=
  rfl

/-! ### Derived sections of `𝐆_m` over an object of the small étale site -/

/-- **The derived sections of `𝐆_{m,X}` over a scheme `U` étale over `X` are the étale cohomology
of `𝐆_m` on `U`.** So if the latter vanishes in degree `q`, so do the former. -/
theorem isZero_rightDerived_etaleSections_multiplicativeSheaf {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (q : ℕ) (h : Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} U) q)) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk j))).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X)) := by
  let : PreservesFiniteColimits ((smallEtaleCompose j).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} U.smallEtaleTopology X.smallEtaleTopology) :=
    have : PreservesColimitsOfSize.{0, 0} (etaleRestriction.{u, u + 1} j) :=
      (etaleDirectImageAdj.{u, u + 1} j).leftAdjoint_preservesColimits
    PreservesColimitsOfSize.preservesFiniteColimits _
  let : ((smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology).PreservesInjectiveObjects :=
    RelativeMayerVietoris.etaleRestriction_preservesInjectiveObjects.{u, u + 1} j
  let : IsIso (Scheme.Etale.mk (𝟙 U)).hom := inferInstanceAs (IsIso (𝟙 U))
  let T : U.Etale := Scheme.Etale.mk (𝟙 U)
  let eW : Scheme.Etale.mk j ≅ (smallEtaleCompose j).obj T :=
    MorphismProperty.Over.isoMk (Iso.refl U) (by change 𝟙 U ≫ 𝟙 U ≫ j = j; simp)
  let S := sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
  refine IsZero.of_iso ?_
    ((Stacks.DerivedFunctor.rightDerivedIso (S.mapIso eW.op) q).symm.app _ ≪≫
      (pushforwardRightDerivedSectionsIso (J := U.smallEtaleTopology) (K := X.smallEtaleTopology)
        AddCommGrpCat.{u + 1} (smallEtaleCompose j) q T).symm.app _ ≪≫
      (Stacks.DerivedFunctor.rightDerivedIso (Sheaf.ΓNatIsoSheafSections U.smallEtaleTopology
        AddCommGrpCat.{u + 1} (isTerminalOfIsIsoHom T)) q).symm.app _)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    U.smallEtaleTopology _ q).1 h

/-! ### The small étale site of a field -/

/-- **The positive-degree derived sections of `𝐆_m` over any object of the small étale site of a
field vanish**, as soon as the positive-degree étale cohomology of `𝐆_m` vanishes over every
finite separable extension of that field. -/
theorem isZero_rightDerived_etaleSections_multiplicativeSheaf_over_field (k : Type u) [Field k]
    (W : (Spec (.of k)).Etale) (q : ℕ) (hq : 0 < q)
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L],
      Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q)) :
    IsZero ((((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op W)).rightDerived q).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of k)))) := by
  obtain ⟨I, L, hL, hAlg, hFin, hSep, e, -⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k W.hom).mp inferInstance
  let (i : I) : Field (L i) := hL i
  let (i : I) : Algebra k (L i) := hAlg i
  let (i : I) : Module.Finite k (L i) := hFin i
  let (i : I) : Algebra.IsSeparable k (L i) := hSep i
  let (i : I) : Etale (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) := inferInstance
  let U (i : I) : (Spec (.of k)).Etale :=
    .mk (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom)
  let eW : W ≅ etaleCoproduct U :=
    MorphismProperty.Over.isoMk e (by
      change e.hom ≫ (Sigma.desc fun i ↦ Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) =
        W.hom
      rw [show (Sigma.desc fun i ↦ Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) =
        e.inv ≫ W.hom from Sigma.hom_ext _ _ fun i ↦ by simp]
      simp)
  let S := sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}
  apply IsZero.of_iso _ ((Stacks.DerivedFunctor.rightDerivedIso (S.mapIso eW.op) q).symm.app _)
  refine isZero_rightDerived_etaleCoproduct_of_components.{u, u + 1} U _ q hq fun i ↦ ?_
  exact isZero_rightDerived_etaleSections_multiplicativeSheaf
    (Sigma.ι (fun i ↦ Spec (.of (L i))) i ≫ e.inv ≫ W.hom) q (h (L i))

/-- **The positive-degree higher direct images of `𝐆_m` along a morphism out of the spectrum of a
field vanish**, as soon as the positive-degree étale cohomology of `𝐆_m` vanishes over every
finite separable extension of that field. -/
theorem isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field
    (k : Type u) [Field k] {Y : Scheme.{u}} (f : Spec (.of k) ⟶ Y) (q : ℕ) (hq : 0 < q)
    (h : ∀ (L : Type u) [Field L] [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L],
      Subsingleton (Sheaf.H.{u + 1, u + 1}
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of L))) q)) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived q).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of k)))) :=
  isZero_rightDerived_smallEtalePushforward_of_affine_sections.{u, u + 1} f _ q fun V _ ↦
    isZero_rightDerived_etaleSections_multiplicativeSheaf_over_field k
      ((smallEtaleBaseChange f).obj V) q hq h

end Stacks.EtaleCohomology

end
