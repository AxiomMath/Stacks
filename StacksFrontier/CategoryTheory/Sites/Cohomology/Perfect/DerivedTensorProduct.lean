module

public import StacksCore.Tactic.StacksAttribute
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
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The derived tensor product of two perfect objects on a ringed site

Let `(C, O)` be a ringed site.  If `K` and `L` are perfect objects of `D(O)`, then so is
`K ⊗^{𝐋}_O L`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct`: **Stacks 09JB.**
* `AlgebraicGeometry.RingedSite.isPerfect_canonicalDerivedTensorProduct`: the same at the
  derived tensor product of Stacks 06YU.

## Implementation notes

**The route.**  Both factors are replaced by representatives `A` and `B` which are K-flat and
stay K-flat after restriction to every slice of the site, so that the comparison of Stacks 06YU
identifies `K ⊗^{𝐋} L` with `Tot(A ⊗_O B)` on `C` and, after restricting, identifies
`Tot(A|_V ⊗ B|_V)` with `K|_V ⊗^{𝐋} L|_V` on each slice; the two are matched by
`AlgebraicGeometry.RingedSite.tensorComplexOverIso`, restriction commuting with the total tensor
complex.  Above an object of the site carrying a strictly perfect model of each factor, the
total tensor complex of the two models is strictly perfect (Stacks 09J8) and is, by that chain,
a local model of `K ⊗^{𝐋} L`; Stacks 08G6 (1) assembles the local models.

**The common covering.**  Perfectness of the two factors produces two coverings of an object of
the site, and a strictly perfect model exists over the members of each.  Their intersection is
covering, and a member of it factors through a member of each; the models are carried to it by
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong`, restriction along an arrow of
the site being exact, so it preserves strict perfectness and quasi-isomorphisms.

**The slice-K-flat representative.**  K-flatness does not transport along restriction to a
slice — it quantifies over the acyclic complexes of the site, and those on `C/V` are not
restrictions of those on `C`.  What transports is the colimit presentation of the resolution of
Stacks 06YS, `Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit`: a sequential
colimit of bounded above complexes of flat `O`-modules.  Restriction commutes with the colimit
degreewise and preserves each clause, which is
`Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit` without the hypothesis
that the site have binary products; that hypothesis enters there through the left adjoint of
restriction, and the colimit preservation needed here comes instead from the cocontinuity of the
pushforward, `Stacks.SheafOfModules.pushforward_preservesColimits`.

**The statement is for an arbitrary derived tensor product** of Stacks 06YU rather than for the
canonical one: only the `comparison` field is used, so this is the natural generality, and
`isPerfect_canonicalDerivedTensorProduct` is the specialization a consumer holding the canonical
datum needs.

**The universes are the diagonal `RingedSite.{0, 0, 0}`,** which is forced.  Perfectness pins
the sections of the structure sheaf to `Type`, while the derived tensor product of Stacks 06YU
on a ringed site is available only for a small site whose objects, morphisms and sections live
in one universe.  The derived category's own hom universe stays free, as `HasDerivedCategory.{d}`.

## References

* [Stacks Project, Tag 09JB](https://stacks.math.columbia.edu/tag/09JB)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 09J8](https://stacks.math.columbia.edu/tag/09J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor

namespace AlgebraicGeometry.RingedSite

universe d

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{0, 0, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor
  preservesFiniteLimitsOverMap' preservesFiniteColimitsOverMap'

/-! ### A representative which is K-flat on the site and on every slice -/

/-- **The restriction to a slice of a sequential colimit of bounded above complexes of flat
`O`-modules is K-flat**: restriction commutes with the colimit degreewise, and each stage
restricts to a bounded above complex of flat `O|_V`-modules.

This is `Stacks.SheafOfModules.KFlatRestriction.kFlat_restriction_of_isColimit` without the
hypothesis that the site have binary products; see the implementation notes. -/
private theorem kFlat_restrictComplex_of_isColimit (V : X.C)
    (D : ℕ ⥤ CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (c : Cocone D) (hc : IsColimit c)
    (hLE : ∀ n : ℕ, ∃ b : ℤ, (D.obj n).IsStrictlyLE b)
    (hflat : ∀ (n : ℕ) (i : ℤ), AlgebraicGeometry.SheafOfModules.IsFlat.{0, 0, 0, 0}
      (O := X.O) ((D.obj n).X i)) :
    Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X c.pt V) := by
  have : PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.KFlatRestriction.restriction X.O V) :=
    Stacks.SheafOfModules.pushforward_preservesColimits
      (J := X.J.over V) (K := X.J) (Over.forget V)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit (sheafTensor (X.O.over V))
    ((Stacks.SheafOfModules.KFlatRestriction.restrictionComplexFunctor X.O V).mapCocone c)
    ((CochainComplex.KFlat.preservesColimit_mapHomologicalComplex D
      (Stacks.SheafOfModules.KFlatRestriction.restriction X.O V)).preserves hc).some
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
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ (A : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        (f : A ⟶ E),
      QuasiIso f ∧ Stacks.SheafOfModules.KFlat.KFlat X.O A ∧
        ∀ V : X.C, Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X A V) := by
  obtain ⟨D, f, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit X.O E
  exact ⟨colimit D, f, hqis,
    Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat X.O D
      hLE hflat,
    fun V => kFlat_restrictComplex_of_isColimit X V D (colimit.cocone D) (colimit.isColimit D)
      hLE hflat⟩

/-! ### The local model of the derived tensor product -/

/-- **A strictly perfect model of `E|_V₁` gives one of `A|_V` along an arrow `V ⟶ V₁`**, where
`A ⟶ E` is a quasi-isomorphism. -/
private theorem exists_strictlyPerfect_restrictedModel
    [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [∀ V : X.C, HasDerivedCategory.{d}
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]
    {E A : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (p : A ⟶ E) (hpq : QuasiIso p) {V₁ V : X.C} (u : V ⟶ V₁)
    (hd : ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V₁)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V₁) P ∧
        ∃ α : P ⟶ restrictComplex X E V₁, QuasiIso α) :
    ∃ Q : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q ∧
        Nonempty (DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj (restrictComplex X A V)) := by
  obtain ⟨P, hP, α, hα⟩ := hd
  exact ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) u hP,
    ⟨((SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        u).mapDerivedCategoryFactors.app P).symm ≪≫
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        u).mapDerivedCategory.mapIso (_root_.CochainComplex.derivedIsoOfQuasiIso α hα) ≪≫
      restrictComplexOverMapIso X E u ≪≫
      ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app E).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso (_root_.CochainComplex.derivedIsoOfQuasiIso p hpq).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app A⟩⟩

variable [(sheafTensor X.O).Additive] [∀ M, ((sheafTensor X.O).obj M).Additive]
  [∀ K₁ K₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules X.O) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
variable [∀ V : X.C, (sheafTensor (X.O.over V)).Additive]
  [∀ (V : X.C) (M : Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)),
    ((sheafTensor (X.O.over V)).obj M).Additive]
  [∀ (V : X.C) (K₁ K₂ : CochainComplex
      (Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over V)) (ComplexShape.up ℤ)]

variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hPerfTensorDer : ∀ V : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))]

/-- The derived category of a slice, at the spelling the derived tensor product is stated at.
It is the same category as `SheafOfModules.{0} (O|_V)`, by `rfl`, but instance search does not
cross the two spellings of the structure sheaf of rings. -/
local instance perfTensorSliceDerived (V : X.C) :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules (X.O.over V)) :=
  hPerfTensorDer V

/-- **The total tensor complex of two strictly perfect models is a model of the restriction of
`Tot(A ⊗_O B)`.**

The two models are strictly perfect, hence K-flat, so the comparison of Stacks 06YU on the
slice turns their total tensor complex into the derived tensor product of their classes; those
classes are the classes of `A|_V` and `B|_V`; the derived tensor product of those is the class
of `Tot(A|_V ⊗ B|_V)` by the same comparison, the restrictions being K-flat; and that is the
class of `Tot(A ⊗_O B)|_V` because restriction commutes with the total tensor complex. -/
private def localModelIso (V : X.C)
    (TV : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over V))
    (A B : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hAV : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X A V))
    (hBV : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X B V))
    (P₁ P₂ : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)
    (hP₁ : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) P₁)
    (hP₂ : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) P₂)
    (e₁ : DerivedCategory.Q.obj P₁ ≅ DerivedCategory.Q.obj (restrictComplex X A V))
    (e₂ : DerivedCategory.Q.obj P₂ ≅ DerivedCategory.Q.obj (restrictComplex X B V)) :
    DerivedCategory.Q.obj (((tensorComplex (X.O.over V)).obj P₁).obj P₂) ≅
      DerivedCategory.Q.obj (restrictComplex X (((tensorComplex X.O).obj A).obj B) V) :=
  (TV.comparison P₁ P₂ hP₁ hP₂).symm ≪≫
    (TV.tensor.mapIso e₁).app (DerivedCategory.Q.obj P₂) ≪≫
    (TV.tensor.obj (DerivedCategory.Q.obj (restrictComplex X A V))).mapIso e₂ ≪≫
    TV.comparison (restrictComplex X A V) (restrictComplex X B V) hAV hBV ≪≫
    (DerivedCategory.Q.mapIso (tensorComplexOverIso X V A B)).symm

/-- **Strictly perfect models of `A|_V` and `B|_V` give a strictly perfect local model of any
object isomorphic to the class of `Tot(A ⊗_O B)`**, namely their total tensor complex. -/
private theorem exists_strictlyPerfect_localModel (V : X.C)
    (A B : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hAV : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X A V))
    (hBV : Stacks.SheafOfModules.KFlat.KFlat (X.O.over V) (restrictComplex X B V))
    {G : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eG : DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj B) ≅ G)
    (h₁ : ∃ Q : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q ∧
        Nonempty (DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj (restrictComplex X A V)))
    (h₂ : ∃ Q : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) Q ∧
        Nonempty (DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj (restrictComplex X B V))) :
    ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅
          (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.obj G) := by
  obtain ⟨Q₁, hQ₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨Q₂, hQ₂, ⟨e₂⟩⟩ := h₂
  exact ⟨((tensorComplex (X.O.over V)).obj Q₁).obj Q₂,
    Stacks.SheafOfModules.Tensor.isStrictlyPerfect_tensorComplex (X.O.over V) Q₁ Q₂ hQ₁ hQ₂,
    ⟨localModelIso X V
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (X.O.over V)) A B
        hAV hBV Q₁ Q₂ (Stacks.SheafOfModules.kFlat_over_of_isStrictlyPerfect X V Q₁ hQ₁)
        (Stacks.SheafOfModules.kFlat_over_of_isStrictlyPerfect X V Q₂ hQ₂) e₁ e₂ ≪≫
      ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
        ).mapDerivedCategoryFactors.app (((tensorComplex X.O).obj A).obj B)).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
        ).mapDerivedCategory.mapIso eG⟩⟩

/-! ### Stacks 09JB -/

/-- **Stacks 09JB.** Let `(C, O)` be a ringed site.  If `K` and `L` are perfect objects of
`D(O)`, then so is `K ⊗^{𝐋}_O L`.

Representatives of the two objects are replaced by resolutions `A` and `B` which are K-flat on
the site and on every slice of it, so that `K ⊗^{𝐋} L` is the class of `Tot(A ⊗_O B)`.  Above
an object of the site lying under a member of the covering that the perfectness of the first
factor supplies and a member of the one the second supplies, both factors have strictly perfect
models; the total tensor complex of those models is strictly perfect and is a local model of
`Tot(A ⊗_O B)`.  Stacks 08G6 (1) turns that family of local models into perfectness.

Stated for an arbitrary derived tensor product of Stacks 06YU, since only its `comparison`
field is used. -/
@[stacks 09JB]
theorem isPerfect_derivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
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
    exact exists_strictlyPerfect_localModel X V A B (hAV V) (hBV V) eG
      (exists_strictlyPerfect_restrictedModel X p hpq u₁ (hd₁ f₁ hf₁))
      (exists_strictlyPerfect_restrictedModel X q hqq u₂ (hd₂ f₂ hf₂))

/-- **The derived tensor product of Stacks 06YU of two perfect objects of `D(O)` is perfect.**
`AlgebraicGeometry.RingedSite.isPerfect_derivedTensorProduct` at the canonical derived tensor
product. -/
theorem isPerfect_canonicalDerivedTensorProduct
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K) (hL : X.IsPerfect L) :
    X.IsPerfect
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj K).obj L) :=
  isPerfect_derivedTensorProduct X _ K L hK hL

end AlgebraicGeometry.RingedSite

end
