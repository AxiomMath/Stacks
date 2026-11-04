module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalPrecompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologySheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.LowerShriekDegreeZero
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek is the fibre homology of Stacks 08PI

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
the standing data of Stacks 08P8, with small fibres, and let `Lπ_!` be the left derived
lower-shriek functor of the induced morphism of topoi. For an abelian sheaf `F` on the total
category and `n ≥ 0`, Stacks 08PJ identifies

```
L_n π_!(F) = H^{-n}(Lπ_! F)   with   L_n(F),
```

the sheaf on the base associated to the presheaf `V ↦ H_n(C_V, F|_{C_V})` of Stacks 08PI. This
file proves that identification, degreewise and naturally in `F`.

Both sides are homological δ-functors, already built and already known universal: the left-hand
side by
`Stacks.Sites.FibredCategory.FibredCategorySituation.isUniversal_derivedLowerShriekHomology` and
the right-hand side by `Stacks.Sites.FibredCategory.isUniversal_fiberHomologySheafDeltaFunctor`,
and they agree in degree zero by
`FibredCategorySituation.derivedLowerShriekHomologyZeroIsoFiberHomologySheaf` in the same
namespace. The dual of Stacks 010U then extends the degree-zero comparison to a unique isomorphism
of δ-functors, whose degree-`n` component is the comparison of Stacks 08PJ.

All the declarations below live in the namespace
`Stacks.Sites.FibredCategory.FibredCategorySituation`, except the generic
`Stacks.Sites.FibredCategory.isoWhiskerLeft_conj_isoId`, and are named without that prefix here.

## Main definitions

* `UliftFreeCoverLowerShriekAcyclic`: the hypothesis that `Lπ_!` is acyclic on the sheafification
  of the canonical presentation of an abelian presheaf by free abelian presheaves on
  representables.
* `derivedLowerShriekHomologyPresheafDeltaFunctor`: the δ-functor `F ↦ H^{-n}(Lπ_!(F^#))` on
  abelian *presheaves* on the total category, the common source on which the two δ-functors of
  Stacks 08PJ can be compared.
* `derivedLowerShriekHomologyPresheafDeltaIso`: the isomorphism of δ-functors between it and the
  δ-functor of the sheaves `L_n` of Stacks 08PI.

## Main results

* `isUniversal_derivedLowerShriekHomologyPresheafDeltaFunctor`: the δ-functor of derived lower
  shriek on abelian presheaves is universal.
* `derivedLowerShriekHomologyIso`: the comparison of Stacks 08PJ for a given `Lπ_!` and given
  its acyclicity inputs. For every `n ≥ 0` the functor `F ↦ H^{-n}(Lπ_! F)` on abelian sheaves on
  the total category is isomorphic to `F ↦ L_n(F)`, the sheaf of fibre homology of the underlying
  presheaf of `F`, naturally in `F`. Both inputs are proved for every fibred situation, and
  Stacks 08PJ itself, with no hypothesis, is
  `derivedLowerShriekHomologyIsoFiberHomology` in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/UliftFreeCoverGenerators.lean`,
  which this file cannot import.
* `derivedLowerShriekHomologyIso_zero`: in degree zero that isomorphism is the already-known
  comparison of `H^0(Lπ_!)` with `π_!`, so the whole family is determined by it.
* `derivedLowerShriekHomologyObjIso`: the same statement read at a single abelian sheaf.

## Implementation notes

**Why the comparison is made on presheaves.** The δ-functor of `Lπ_!` has abelian sheaves on the
total category as its source, the δ-functor of fibre homology has abelian presheaves, so neither
isomorphism statement typechecks before one of them is moved. Moving the fibre side to sheaves by
`Stacks.CategoryHomology.HomologicalDeltaFunctor.precomp (sheafToPresheaf …)` is impossible:
precomposition needs an exact functor, and the inclusion of sheaves into presheaves is only left
exact. Moving the lower-shriek side to presheaves by `precomp (presheafToSheaf …)` does work —
sheafification is additive, left exact because the site has sheafification, and right exact as a
left adjoint — so the comparison is made on presheaves and then descended to sheaves through the
counit of the sheafification adjunction, which is an isomorphism because the inclusion of sheaves
is fully faithful.

**Where Stacks 08PI's sheafification invariance is used.** After the move the two degree-zero
functors are `F ↦ π_!(F^#)` and `F ↦ L_0(F)`; the known comparison identifies the first with
`F ↦ L_0(F^#)`. The identification of `L_0(F^#)` with `L_0(F)` is exactly 08PI's
`Stacks.Sites.FibredCategory.fiberHomologySheaf_sheafify`, and it is used here as a natural
isomorphism of functors — `fiberHomologySheafFunctorSheafifyIso` — the components being the
morphisms induced by the unit of the sheafification adjunction, whose naturality is the
naturality of that unit.

**The acyclicity hypothesis that is carried.** Universality of the moved δ-functor needs, for an
abelian presheaf `X`, an epimorphism onto `X` whose sheafification is `Lπ_!`-acyclic in positive
degrees. The epimorphism is the canonical presentation `Stacks.CategoryHomology.uliftFreeCoverHom`
by universe-lifted free abelian presheaves on representables. Its sheafification *is* a direct sum
of the free abelian sheaves `j_{U!} ℤ_U`, which is the class on which
`AbelianLowerShriekGeneratorsAcyclic` asserts acyclicity, but that identification needs the
sectionwise direct sum of presheaves to be recognized as a coproduct and the sheafification of a
free abelian presheaf on a representable to be recognized as a free abelian sheaf — neither of
which is available here. So the acyclicity of the sheafified presentation is carried as the
hypothesis `UliftFreeCoverLowerShriekAcyclic`, exactly as `AbelianLowerShriekAcyclic` and
`AbelianLowerShriekGeneratorsAcyclic` are carried in the files this one builds on. Two lemmas
discharge it: `uliftFreeCoverLowerShriekAcyclic_of_isSumOfExtensionByZeroUnitsAb` reduces it to
that missing identification together with `AbelianLowerShriekGeneratorsAcyclic`, and
`uliftFreeCoverLowerShriekAcyclic_of_preservesFiniteLimits` proves it outright whenever lower
shriek is exact, so the hypothesis is not vacuous. All three hypotheses are discharged downstream,
for every fibred situation: `AbelianLowerShriekAcyclic` by `abelianLowerShriekAcyclic`
(`ProjectionLowerShriekAcyclic.lean`), and `AbelianLowerShriekGeneratorsAcyclic` together with the
identification of the sheafified presentation in `UliftFreeCoverGenerators.lean`.

**Universes.** The situation is taken at `vC = uC` with coefficients
`AddCommGrpCat.{max w uD vD uC}`, the generality in which Stacks 08PI, the degree-zero comparison
and the universe-lifted cover all live. Every call writes its universes out: the level unifier
cannot solve `max uC ?v =?= max w uD vD uC`, as recorded at
`StacksFrontier/CategoryTheory/Sites/Cohomology/CategoryHomology/Functoriality.lean`, and
`uliftFreeRepresentablePresheaf` has its value universe occurring alone inside a `ULift`, so two
instantiations with the same coefficient category can still be different types. The instantiation
matching the cover used here is `.{uC, max w uD vD uC}`, as in
`DerivedLowerShriekFibreHomology.lean`. `HasDerivedCategory.standard` is a local instance of the
derived section, as in every lower-shriek file, so that all of them speak about the same derived
categories.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

namespace Stacks.Sites.FibredCategory

universe uD vD uC w

section Conjugation

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- **Conjugating a natural isomorphism by an isomorphism `K ≅ 𝟭` recovers it.** For functors
`E₁, E₂ : A ⥤ B` and an isomorphism `α : K ≅ 𝟭 A`, transporting `e : E₁ ≅ E₂` along `α` on both
sides gives back `e`, by the naturality of `e` at the components of `α`. -/
theorem isoWhiskerLeft_conj_isoId {K : A ⥤ A} (α : K ≅ 𝟭 A) {E₁ E₂ : A ⥤ B} (e : E₁ ≅ E₂) :
    (Functor.isoWhiskerRight α E₁).symm ≪≫ Functor.isoWhiskerLeft K e ≪≫
        Functor.isoWhiskerRight α E₂ = e := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  change E₁.map (α.inv.app X) ≫ e.hom.app (K.obj X) ≫ E₂.map (α.hom.app X) = e.hom.app X
  rw [← e.hom.naturality (α.hom.app X), ← Category.assoc, ← E₁.map_comp,
    show α.inv.app X ≫ α.hom.app X = 𝟙 X from congrFun (congrArg NatTrans.app α.inv_hom_id) X]
  simp

end Conjugation

namespace FibredCategorySituation

section Sheafify

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-- **Stacks 08PI's sheafification invariance, as an isomorphism of functors.** The sheaf `L_n(F)`
of fibre homology does not change when the coefficient presheaf `F` is replaced by its
sheafification on the total category, naturally in `F`: the comparison is induced by the unit of
the sheafification adjunction, whose naturality is the naturality of that unit. -/
def fiberHomologySheafFunctorSheafifyIso (n : ℕ) :
    fiberHomologyPresheafFunctor s n ⋙
        presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} ≅
      presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
          fiberHomologyPresheafFunctor s n ⋙
            presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  NatIso.ofComponents (fun F => fiberHomologySheafSheafifyIso s F n) fun {_F _G} α =>
    (Functor.whiskerRight
      (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit
      (fiberHomologyPresheafFunctor s n ⋙
        presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC})).naturality α

/-- **The sheafification invariance of `L_n`, read on abelian sheaves, is the counit.** At the
underlying presheaf of an abelian sheaf `F` the comparison `L_n(F) ≅ L_n(F^#)` is induced by the
counit of the sheafification adjunction, because the unit at a sheaf is inverse to the underlying
morphism of that counit. -/
theorem isoWhiskerLeft_fiberHomologySheafFunctorSheafifyIso (n : ℕ) :
    Functor.isoWhiskerLeft (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC})
        (s.fiberHomologySheafFunctorSheafifyIso n) =
      (Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).counit)
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
          fiberHomologyPresheafFunctor s n ⋙
            presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC})).symm := by
  refine Iso.ext (NatTrans.ext (funext fun F => ?_))
  have hU : (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).map
        ((asIso (sheafificationAdjunction s.topology
          AddCommGrpCat.{max w uD vD uC}).counit).inv.app F) =
      (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app
        ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F) := by
    simp only [asIso_inv, NatIso.isIso_inv_app, Functor.map_inv]
    exact IsIso.inv_eq_of_inv_hom_id
      ((sheafificationAdjunction s.topology
        AddCommGrpCat.{max w uD vD uC}).right_triangle_components F)
  change (fiberHomologyPresheafFunctor s n ⋙
      presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map _ =
    (fiberHomologyPresheafFunctor s n ⋙
      presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map _
  rw [hU]

end Sheafify

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC})
    (ComplexShape.up ℤ))]

/-- **The acyclicity of the sheafified canonical presentation for `Lπ_!`.** The sheafification of
the presentation of an abelian presheaf by universe-lifted free abelian presheaves on
representables is carried by `Lπ_!` to a complex with no cohomology in negative degrees, that is
`L_m π_!` vanishes on it for `m ≥ 1`. -/
abbrev UliftFreeCoverLowerShriekAcyclic : Prop :=
  ∀ X : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC},
    (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj
      ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
        (uliftFreeCover.{uC, max w uD vD uC} X)))).IsGE 0

/-- **The sheafified presentation is `Lπ_!`-acyclic once it is recognized as a direct sum of free
abelian sheaves.** Granted that identification, the acyclicity is the acyclicity of the generators
`j_{U!} ℤ_U` with which Stacks 07AC runs the criterion of Stacks 0794. -/
theorem uliftFreeCoverLowerShriekAcyclic_of_isSumOfExtensionByZeroUnitsAb
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic)
    (hcov : ∀ X : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC},
      Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC, uC, uC}
        s.topology ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          (uliftFreeCover.{uC, max w uD vD uC} X))) :
    s.UliftFreeCoverLowerShriekAcyclic :=
  fun X => hgen _ (hcov X)

/-- **The sheafified presentation is `Lπ_!`-acyclic when lower shriek is exact**, in which case
`Lπ_!` carries every abelian sheaf placed in degree zero to a complex concentrated in degree
zero. So the hypothesis of the comparison below is not vacuous. -/
theorem uliftFreeCoverLowerShriekAcyclic_of_preservesFiniteLimits
    [PreservesFiniteLimits s.abelianLowerShriek] :
    s.UliftFreeCoverLowerShriekAcyclic :=
  fun _X => s.isGE_derivedAbelianLowerShriek_obj_single_of_preservesFiniteLimits _

/-- **The δ-functor of derived lower shriek on abelian presheaves**, that is
`F ↦ H^{-n}(Lπ_!(F^#))` for `F` an abelian presheaf on the total category. It is the δ-functor of
Stacks 08PJ precomposed with sheafification, which is exact, and it is the common source on which
the two δ-functors of Stacks 08PJ can be compared. -/
abbrev derivedLowerShriekHomologyPresheafDeltaFunctor (h : s.AbelianLowerShriekAcyclic) :
    Stacks.CategoryHomology.HomologicalDeltaFunctor
      (s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC}) :=
  (s.derivedLowerShriekHomologyDeltaFunctor h).precomp
    (presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC})

/-- The degree-`n` functor of the δ-functor of derived lower shriek on abelian presheaves is
sheafification followed by `H^{-n}(Lπ_! -)`. Deliberately not a `simp` lemma: it rewrites a whole
functor. -/
theorem derivedLowerShriekHomologyPresheafDeltaFunctor_functor
    (h : s.AbelianLowerShriekAcyclic) (n : ℕ) :
    (s.derivedLowerShriekHomologyPresheafDeltaFunctor h).functor n =
      presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        s.derivedAbelianLowerShriekHomology n :=
  rfl

/-- **The δ-functor of derived lower shriek on abelian presheaves is coeffaceable.** Every abelian
presheaf on the total category is an epimorphic image of the canonical presentation by
universe-lifted free abelian presheaves on representables, and the hypothesis says that `Lπ_!`
kills the sheafification of that presentation in every positive degree. -/
theorem coeffaceable_derivedLowerShriekHomologyPresheafDeltaFunctor
    (h : s.AbelianLowerShriekAcyclic) (hcov : s.UliftFreeCoverLowerShriekAcyclic) :
    (s.derivedLowerShriekHomologyPresheafDeltaFunctor h).Coeffaceable := by
  refine Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero _
    fun X n => ⟨uliftFreeCover.{uC, max w uD vD uC} X,
      uliftFreeCoverHom.{uC, max w uD vD uC} X, inferInstance, ?_⟩
  have _ := hcov X
  exact DerivedCategory.isZero_of_isGE
    (s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj
      ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
        (uliftFreeCover.{uC, max w uD vD uC} X)))) 0
    (-((n + 1 : ℕ) : ℤ)) (by push_cast; omega)

/-- **The δ-functor of derived lower shriek on abelian presheaves is universal**, by the dual of
Stacks 010T: every morphism of δ-functors into it is determined by, and can be prescribed
arbitrarily in, degree zero. -/
theorem isUniversal_derivedLowerShriekHomologyPresheafDeltaFunctor
    (h : s.AbelianLowerShriekAcyclic) (hcov : s.UliftFreeCoverLowerShriekAcyclic) :
    (s.derivedLowerShriekHomologyPresheafDeltaFunctor h).IsUniversal :=
  have := s.coeffaceable_derivedLowerShriekHomologyPresheafDeltaFunctor h hcov
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_of_coeffaceable _

/-- **The degree-zero comparison of Stacks 08PJ on abelian presheaves.** For an abelian presheaf
`F` on the total category, `H^0(Lπ_!(F^#))` is `π_!(F^#)`, which is the sheaf `L_0(F^#)` of
degree-zero fibre homology, which by Stacks 08PI is `L_0(F)`. -/
def derivedLowerShriekHomologyPresheafZeroIso (h : s.AbelianLowerShriekAcyclic) :
    (s.derivedLowerShriekHomologyPresheafDeltaFunctor h).functor 0 ≅
      (fiberHomologySheafDeltaFunctor s).functor 0 :=
  Functor.isoWhiskerLeft (presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC})
      (s.derivedLowerShriekHomologyZeroIsoFiberHomologySheaf h) ≪≫
    (s.fiberHomologySheafFunctorSheafifyIso 0).symm

/-- **Stacks 08PJ, the isomorphism of δ-functors on abelian presheaves.** The δ-functor
`F ↦ H^{-n}(Lπ_!(F^#))` and the δ-functor of the sheaves `L_n` of Stacks 08PI are both universal
and agree in degree zero, so by the dual of Stacks 010U they are isomorphic, by the unique
isomorphism extending the degree-zero comparison. -/
def derivedLowerShriekHomologyPresheafDeltaIso (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) :
    s.derivedLowerShriekHomologyPresheafDeltaFunctor h ≅ fiberHomologySheafDeltaFunctor s :=
  have := s.isUniversal_derivedLowerShriekHomologyPresheafDeltaFunctor h hcov
  have := isUniversal_fiberHomologySheafDeltaFunctor s
  Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso
    (s.derivedLowerShriekHomologyPresheafZeroIso h)

/-- **Stacks 08PJ in degree `n`, on abelian presheaves.** For an abelian presheaf `F` on the total
category, `H^{-n}(Lπ_!(F^#))` is the sheaf `L_n(F)` of fibre homology, naturally in `F`. -/
def derivedLowerShriekHomologyPresheafNatIso (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) (n : ℕ) :
    presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        s.derivedAbelianLowerShriekHomology n ≅
      fiberHomologyPresheafFunctor s n ⋙
        presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  Stacks.CategoryHomology.HomologicalDeltaFunctor.isoApp
    (s.derivedLowerShriekHomologyPresheafDeltaIso h hcov) n

/-- **The comparison of Stacks 08PJ is the degree-zero one in degree zero**, on abelian
presheaves. This is the uniqueness half of the dual of Stacks 010U: a morphism into a universal
δ-functor is determined by its degree-zero component. -/
theorem derivedLowerShriekHomologyPresheafNatIso_zero (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) :
    s.derivedLowerShriekHomologyPresheafNatIso h hcov 0 =
      s.derivedLowerShriekHomologyPresheafZeroIso h :=
  have := s.isUniversal_derivedLowerShriekHomologyPresheafDeltaFunctor h hcov
  have := isUniversal_fiberHomologySheafDeltaFunctor s
  Iso.ext
    (Stacks.CategoryHomology.HomologicalDeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
      (s.derivedLowerShriekHomologyPresheafZeroIso h))

/-- **The comparison of Stacks 08PJ, for a given `Lπ_!` and given its two acyclicity inputs.** For
every `n ≥ 0`, the functor `F ↦ H^{-n}(Lπ_! F) = L_n π_!(F)` on abelian sheaves on the total
category is the functor `F ↦ L_n(F)` of Stacks 08PI, the sheaf on the base associated to
`V ↦ H_n(C_V, F|_{C_V})`, naturally in `F`. The comparison is the presheaf-level one read at the
underlying presheaf of a sheaf, which is legitimate because sheafifying the underlying presheaf of
a sheaf gives the sheaf back. Both acyclicity inputs are proved for every fibred situation, and
the statement with neither is
`Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyIsoFiberHomology`
in `StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/UliftFreeCoverGenerators.lean`. -/
def derivedLowerShriekHomologyIso (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) (n : ℕ) :
    s.derivedAbelianLowerShriekHomology n ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        fiberHomologyPresheafFunctor s n ⋙
          presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  (Functor.isoWhiskerRight
      (asIso (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).counit)
      (s.derivedAbelianLowerShriekHomology n)).symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC})
      (s.derivedLowerShriekHomologyPresheafNatIso h hcov n)

/-- **The comparison of Stacks 08PJ is the degree-zero comparison in degree zero.** So the whole
family is determined by the identification of `H^0(Lπ_!)` with `π_!`, and nothing about it was
chosen. -/
theorem derivedLowerShriekHomologyIso_zero (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) :
    s.derivedLowerShriekHomologyIso h hcov 0 =
      s.derivedLowerShriekHomologyZeroIsoFiberHomologySheaf h := by
  have hw := s.isoWhiskerLeft_fiberHomologySheafFunctorSheafifyIso 0
  have key :
      Functor.isoWhiskerLeft (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC})
          (show presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
                s.derivedAbelianLowerShriekHomology 0 ≅
              fiberHomologyPresheafFunctor s 0 ⋙
                presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} from
            s.derivedLowerShriekHomologyPresheafZeroIso h) =
        Functor.isoWhiskerLeft
            (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
              presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC})
            (s.derivedLowerShriekHomologyZeroIsoFiberHomologySheaf h) ≪≫
          Functor.isoWhiskerRight
            (asIso (sheafificationAdjunction s.topology
              AddCommGrpCat.{max w uD vD uC}).counit)
            (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
              fiberHomologyPresheafFunctor s 0 ⋙
                presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}) := by
    refine Iso.ext (NatTrans.ext (funext fun F => ?_))
    change _ ≫ (s.fiberHomologySheafFunctorSheafifyIso 0).inv.app _ = _ ≫ _
    congr 1
    exact congrFun (congrArg NatTrans.app (congrArg Iso.inv hw)) F
  rw [derivedLowerShriekHomologyIso, s.derivedLowerShriekHomologyPresheafNatIso_zero h hcov, key]
  exact isoWhiskerLeft_conj_isoId _ _

/-- **Stacks 08PJ at a single abelian sheaf.** For an abelian sheaf `F` on the total category and
`n ≥ 0`, the `n`th derived lower shriek `L_n π_!(F) = H^{-n}(Lπ_! F)` is the sheaf `L_n(F)` of
fibre homology of Stacks 08PI, formed from the underlying presheaf of `F`. -/
def derivedLowerShriekHomologyObjIso (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) (n : ℕ)
    (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC}) :
    (s.derivedAbelianLowerShriekHomology n).obj F ≅ fiberHomologySheaf s F.obj n :=
  (s.derivedLowerShriekHomologyIso h hcov n).app F

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
