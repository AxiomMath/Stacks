module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of two perfect objects, at every universe

Let `(C, O)` be a ringed site whose objects, morphisms and sections all lie in one universe
`u`. If `K` and `L` are perfect objects of `D(O)`, then so is `K ⊗^{𝐋}_O L`. This is
Stacks 09JB.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_tensor_of_isPerfect`: **Stacks 09JB** for an
  arbitrary derived tensor product of Stacks 06YU on a ringed site `RingedSite.{u, u, u}`.
* `AlgebraicGeometry.RingedSite.isPerfect_canonicalDerivedTensorProduct_of_isPerfect`: the same
  at the canonical derived tensor product.

## Implementation notes

The argument is the one of `AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct`, which
is stated for `RingedSite.{0, 0, 0}`. Both factors are replaced by resolutions `A` and `B` which
are K-flat on the site and on every slice of it (the colimit presentation of the resolution of
Stacks 06YS: a sequential colimit of bounded above complexes of flat modules, which restriction
to a slice preserves), so that `K ⊗^{𝐋} L` is the class of `Tot(A ⊗_O B)`. Above an object of
the site lying under a member of each of the two coverings that perfectness of the factors
supplies, the total tensor complex of the two strictly perfect models is strictly perfect
(Stacks 09J8) and is a local model of `Tot(A ⊗_O B)`; Stacks 08G6 (1) assembles the local
models.

Nothing in that argument needs the universe `0`. The two places where the statement at `0` used
it are replaced here: restriction along an arrow of the site preserves finite limits and
colimits at every universe of the sections
(`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits` and
`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits`), and so does strict
perfectness (`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general`); the
preservation of sequential colimits by restriction to a slice is obtained from the preservation
of colimits of size `u` by `CategoryTheory.Limits.preservesColimitsOfSize_shrink`. The universe
of the objects and the morphisms of the site must still agree, because Stacks 08G6 (1) rests on
Stacks 08FR, which needs it; the sections are put in the same universe because the derived
tensor product of Stacks 06YU on a ringed site is constructed there.

## References

* [Stacks Project, Tag 09JB](https://stacks.math.columbia.edu/tag/09JB)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 09J8](https://stacks.math.columbia.edu/tag/09J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

universe u d

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
variable [HasSheafify X.J AddCommGrpCat.{u}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits

/-! ### A representative which is K-flat on the site and on every slice -/

/-- **The restriction to a slice of a sequential colimit of bounded above complexes of flat
`O`-modules is K-flat**: restriction commutes with the colimit degreewise, and each stage
restricts to a bounded above complex of flat `O|_V`-modules.

This is `Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit` without the
hypothesis that the site have binary products; see the implementation notes. -/
private theorem kFlat_restrictComplex_of_isColimit (V : X.C)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.O) ((D.obj n).X i)) :
    Stacks.SheafOfModules.KFlat (X.O.over V) (restrictComplex X c.pt V) := by
  have h₁ : PreservesColimitsOfSize.{u, u}
      (Stacks.SheafOfModules.KFlatRestriction.restriction X.O V) :=
    Stacks.SheafOfModules.pushforward_preservesColimits
      (J := X.J.over V) (K := X.J) (Over.forget V)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  have h₀ : PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.KFlatRestriction.restriction X.O V) :=
    preservesColimitsOfSize_shrink _
  have hp := CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
    (Stacks.SheafOfModules.KFlatRestriction.restriction X.O V)
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit (sheafTensor (X.O.over V))
    ((Stacks.SheafOfModules.KFlatRestriction.restrictionComplexFunctor X.O V).mapCocone c)
    (hp.preserves hc).some
    (Stacks.SheafOfModules.KFlatResolution.hF_sheafTensor (X.O.over V))
    (Stacks.SheafOfModules.KFlatResolution.hexact_sheafOfModules (X.O.over V)) fun n => ?_
  obtain ⟨b, _⟩ := hLE n
  exact Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isStrictlyLE X.O V
    (D.obj n) b (hflat n)

/-- **Every complex of `O`-modules receives a quasi-isomorphism from one which is K-flat and
whose restriction to every slice of the site is K-flat.**

This is the resolution of Stacks 06YS in its colimit presentation: a sequential colimit of
bounded above complexes of flat `O`-modules is K-flat by Stacks 06YQ, and so is its restriction
to any slice, each stage restricting to a bounded above complex of flat modules there. -/
private theorem exists_sliceKFlat_resolution
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (f : A ⟶ E),
      QuasiIso f ∧ Stacks.SheafOfModules.KFlat X.O A ∧
        ∀ V : X.C, Stacks.SheafOfModules.KFlat (X.O.over V) (restrictComplex X A V) := by
  obtain ⟨D, f, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit X.O E
  exact ⟨colimit D, f, hqis,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat X.O D
      hLE hflat,
    fun V => kFlat_restrictComplex_of_isColimit X V D (colimit.cocone D) (colimit.isColimit D)
      hLE hflat⟩

/-! ### The local model of the derived tensor product -/

variable [(sheafTensor X.O).Additive] [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ K₁ K₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.O) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
variable [∀ V : X.C, (sheafTensor (X.O.over V)).Additive]
  [∀ (V : X.C) (M : Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)),
    ((sheafTensor (X.O.over V)).obj M).Additive]
  [∀ (V : X.C) (K₁ K₂ : CochainComplex
      (Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over V)) (ComplexShape.up ℤ)]

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hTensorOfPerfectDer : ∀ V : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]

/-- The derived category of a slice, at the spelling the derived tensor product is stated at.
It is the same category as `SheafOfModules.{u} (O|_V)`, by `rfl`, but instance search does not
cross the two spellings of the structure sheaf of rings. -/
local instance tensorOfPerfectSliceDerived (V : X.C) :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)) :=
  hTensorOfPerfectDer V

/-- **A strictly perfect model over an object of the site descends along an arrow into it.**
Restriction along an arrow is exact, so it preserves strict perfectness and carries a model of
`M|_V` to a model of `M|_W`. -/
private def modelOfArrow
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V)
    (P : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (restrictComplex X M V)) :
    DerivedCategory.Q.obj ((restrictCochainAlong X g).obj P) ≅
      DerivedCategory.Q.obj (restrictComplex X M W) :=
  ((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      g).mapDerivedCategoryFactors.app P).symm ≪≫
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      g).mapDerivedCategory.mapIso e ≪≫
    restrictComplexOverMapIso X M g

/-- **The restriction to a slice of a quasi-isomorphism of complexes of `O`-modules**, read in
the derived category of the slice.  Restriction to a slice is exact. -/
private def restrictDerivedIsoOfQuasiIso
    {M N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : M ⟶ N) (hφ : QuasiIso φ)
    (V : X.C) :
    DerivedCategory.Q.obj (restrictComplex X M V) ≅
      DerivedCategory.Q.obj (restrictComplex X N V) :=
  ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app M).symm ≪≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategory.mapIso (_root_.CochainComplex.derivedIsoOfQuasiIso φ hφ) ≪≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app N

/-- **The total tensor complex of two strictly perfect models is a model of the restriction of
`Tot(A ⊗_O B)`.**

The two models are strictly perfect, hence K-flat, so the comparison of Stacks 06YU on the
slice turns their total tensor complex into the derived tensor product of their classes; those
classes are the classes of `A|_V` and `B|_V`; the derived tensor product of those is the class
of `Tot(A|_V ⊗ B|_V)` by the same comparison, the restrictions being K-flat; and that is the
class of `Tot(A ⊗_O B)|_V` because restriction commutes with the total tensor complex. -/
private def localModelIso (V : X.C)
    (TV : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over V))
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hAV : Stacks.SheafOfModules.KFlat (X.O.over V) (restrictComplex X A V))
    (hBV : Stacks.SheafOfModules.KFlat (X.O.over V) (restrictComplex X B V))
    (P₁ P₂ : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP₁ : Stacks.SheafOfModules.KFlat (X.O.over V) P₁)
    (hP₂ : Stacks.SheafOfModules.KFlat (X.O.over V) P₂)
    (e₁ : DerivedCategory.Q.obj P₁ ≅ DerivedCategory.Q.obj (restrictComplex X A V))
    (e₂ : DerivedCategory.Q.obj P₂ ≅ DerivedCategory.Q.obj (restrictComplex X B V)) :
    DerivedCategory.Q.obj (((tensorComplex (X.O.over V)).obj P₁).obj P₂) ≅
      DerivedCategory.Q.obj (restrictComplex X (((tensorComplex X.O).obj A).obj B) V) :=
  (TV.comparison P₁ P₂ hP₁ hP₂).symm ≪≫
    (TV.tensor.mapIso e₁).app (DerivedCategory.Q.obj P₂) ≪≫
    (TV.tensor.obj (DerivedCategory.Q.obj (restrictComplex X A V))).mapIso e₂ ≪≫
    TV.comparison (restrictComplex X A V) (restrictComplex X B V) hAV hBV ≪≫
    (DerivedCategory.Q.mapIso (tensorComplexOverIso X V A B)).symm

/-! ### Stacks 09JB -/

/-- **Stacks 09JB.** Let `(C, O)` be a ringed site whose objects, morphisms and sections lie in
one universe.  If `K` and `L` are perfect objects of `D(O)`, then so is `K ⊗^{𝐋}_O L`.

Representatives of the two objects are replaced by resolutions `A` and `B` which are K-flat on
the site and on every slice of it, so that `K ⊗^{𝐋} L` is the class of `Tot(A ⊗_O B)`.  Above
an object of the site lying under a member of the covering that the perfectness of the first
factor supplies and a member of the one the second supplies, both factors have strictly perfect
models; the total tensor complex of those models is strictly perfect and is a local model of
`Tot(A ⊗_O B)`.  Stacks 08G6 (1) turns that family of local models into perfectness.

Stated for an arbitrary derived tensor product of Stacks 06YU, since only its `comparison`
field is used. -/
@[stacks 09JB "if K, L are perfect objects of D(O), then so is K ⊗^L_O L, on any ringed site \
  RingedSite.{u,u,u}"]
theorem isPerfect_tensor_of_isPerfect
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) (hL : X.IsPerfect L) :
    X.IsPerfect ((T.tensor.obj K).obj L) := by
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  obtain ⟨F, hF, ⟨eL⟩⟩ := hL
  obtain ⟨A, p, hpq, hA, hAV⟩ := exists_sliceKFlat_resolution X E
  obtain ⟨B, q, hqq, hB, hBV⟩ := exists_sliceKFlat_resolution X F
  have eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hA hB).symm ≪≫
      (T.tensor.mapIso
          (_root_.CochainComplex.derivedIsoOfQuasiIso p hpq ≪≫ eK)).app
        (DerivedCategory.Q.obj B) ≪≫
      (T.tensor.obj K).mapIso (_root_.CochainComplex.derivedIsoOfQuasiIso q hqq ≪≫ eL)
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect X _ fun U => ?_
  obtain ⟨S₁, hS₁, hd₁⟩ := hE U
  obtain ⟨S₂, hS₂, hd₂⟩ := hF U
  refine ⟨(Sieve.generate S₁ ⊓ Sieve.generate S₂).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact X.J.intersection_covering hS₁ hS₂
  · rintro V g ⟨⟨V₁, u₁, f₁, hf₁, -⟩, ⟨V₂, u₂, f₂, hf₂, -⟩⟩
    obtain ⟨P₁, hP₁, α, hα⟩ := hd₁ f₁ hf₁
    obtain ⟨P₂, hP₂, β, hβ⟩ := hd₂ f₂ hf₂
    let Q₁ := (restrictCochainAlong X u₁).obj P₁
    let Q₂ := (restrictCochainAlong X u₂).obj P₂
    have hQ₁ : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q₁ :=
      Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) u₁ hP₁
    have hQ₂ : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q₂ :=
      Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) u₂ hP₂
    have e₁ : DerivedCategory.Q.obj Q₁ ≅ DerivedCategory.Q.obj (restrictComplex X A V) :=
      modelOfArrow X E u₁ P₁ (_root_.CochainComplex.derivedIsoOfQuasiIso α hα) ≪≫
        (restrictDerivedIsoOfQuasiIso X p hpq V).symm
    have e₂ : DerivedCategory.Q.obj Q₂ ≅ DerivedCategory.Q.obj (restrictComplex X B V) :=
      modelOfArrow X F u₂ P₂ (_root_.CochainComplex.derivedIsoOfQuasiIso β hβ) ≪≫
        (restrictDerivedIsoOfQuasiIso X q hqq V).symm
    exact ⟨((tensorComplex (X.O.over V)).obj Q₁).obj Q₂,
      Stacks.SheafOfModules.Tensor.isStrictlyPerfect_tensorComplex (X.O.over V) Q₁ Q₂ hQ₁ hQ₂,
      ⟨localModelIso X V
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (X.O.over V)) A B
          (hAV V) (hBV V) Q₁ Q₂ (Stacks.SheafOfModules.kFlat_over_of_isStrictlyPerfect X V Q₁ hQ₁)
          (Stacks.SheafOfModules.kFlat_over_of_isStrictlyPerfect X V Q₂ hQ₂) e₁ e₂ ≪≫
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategoryFactors.app (((tensorComplex X.O).obj A).obj B)).symm ≪≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.mapIso eG⟩⟩

/-- **The derived tensor product of Stacks 06YU of two perfect objects of `D(O)` is perfect.**
`AlgebraicGeometry.RingedSite.isPerfect_tensor_of_isPerfect` at the canonical derived tensor
product. -/
theorem isPerfect_canonicalDerivedTensorProduct_of_isPerfect
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) (hL : X.IsPerfect L) :
    X.IsPerfect
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj K).obj L) :=
  isPerfect_tensor_of_isPerfect X _ K L hK hL

end AlgebraicGeometry.RingedSite

end
