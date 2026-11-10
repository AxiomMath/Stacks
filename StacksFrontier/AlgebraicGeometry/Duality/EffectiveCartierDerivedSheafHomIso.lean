module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierBifunctorTrace
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexSingleSource
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived sheaf Hom along an effective Cartier divisor is the shifted normal sheaf

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with closed immersion
`i : D ⟶ X`, ideal sheaf `ℐ_D`, associated invertible sheaf `𝒪_X(D) = ℐ_D^∨` and normal sheaf
`𝒩 = 𝒩_{D/X} = i^* 𝒪_X(D)`. [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
asserts that there is an isomorphism

`R ℰom(𝒪_D, 𝒪_X) ≅ 𝒩[-1]` in `D(𝒪_D)`,

where `R ℰom(𝒪_D, -) : D(𝒪_X) ⥤ D(𝒪_D)` is the right adjoint of derived pushforward of
[Stacks, Tag 0A76] — derived sheaf Hom *with exact support* — and `[-1]` is the cohomological
shift that places `𝒩` in degree `1`. **This file proves that isomorphism.**

The canonical comparison morphism `𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` of the same tag is
`Stacks.Divisors.normalSheafShiftToDerivedSheafHomExactSupport`; nothing here depends on it.

## The proof

The source applies `i_*` and uses that `i_*` is exact and fully faithful
([Stacks, Tag 08KS]). Applying `i_*` is `CategoryTheory.Functor.isoSingleOfFullyFaithful`: an
exact functor commutes with the cohomology of the derived category, and a faithful exact functor
therefore detects that an object is concentrated in a single degree, after which full
faithfulness descends the identification of that single cohomology sheaf. So it is enough to
compute `Ri_* R ℰom(𝒪_D, 𝒪_X)`, and by [Stacks, Tag 0A77] — here the bifunctor model
`…derivedSheafHomExactSupportPushforwardNatIso` — that is `R ℰom_{𝒪_X}(Ri_* 𝒪_D, 𝒪_X)`, with
`Ri_* 𝒪_D = (i_* 𝒪_D)[0]` because `i_*` is exact.

`R ℰom_{𝒪_X}((i_* 𝒪_D)[0], 𝒪_X)` is computed from the ideal sequence
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` of [Stacks, Tag 0C6K]. Contravariant exactness of the derived
internal Hom ([Stacks, Tag 08I0]) turns it into a distinguished triangle whose two other terms
are `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X)` and `R ℰom_{𝒪_X}(ℐ_D, 𝒪_X)`; an invertible sheaf is its own derived
dual (`AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible`, [Stacks, Tag 08JH]
for a locally finite free summand), so those two are `𝒪_X` and `𝒪_X(D)` placed in degree zero.
The map between them is precomposition with the ideal inclusion, which under
`ℰom(𝒪_X, 𝒪_X) ≅ 𝒪_X` is multiplication by the canonical section `1_D` of `𝒪_X(D)`
(`Stacks.Divisors.internalHomPre_divisorIdealMap_eq`) — that is, the first map of the normal
short exact sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩 ⟶ 0`. The rotated triangle and the normal
sequence therefore agree on their first two terms and their first map, so
`CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` identifies their third terms, which is the
computation sought.

## Main definitions

* `Stacks.Divisors.idealShortComplex`: the ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`.
* `Stacks.Divisors.derivedDual`: the functor `R ℰom_{𝒪_X}(-, 𝒪_X)` on `D(𝒪_X)`.
* `Stacks.Divisors.idealDerivedSheafHomIso`: the ambient computation
  `R ℰom_{𝒪_X}((i_* 𝒪_D)[0], 𝒪_X) ≅ (i_* 𝒩)[-1]`.
* `Stacks.Divisors.derivedSheafHomExactSupportIsoNormalShift`: [Stacks, Tag 0B4B] at the
  description `𝒩 = i^* 𝒪_X(D)` of the normal sheaf.
* `Stacks.Divisors.normalSheafShiftIsoDerivedSheafHomExactSupport`: **[Stacks, Tag 0B4B]**,
  written with the normal sheaf of the closed immersion.
* `CategoryTheory.Functor.isoSingleOfFullyFaithful`: an object of a derived category whose image
  under an exact, fully faithful functor is concentrated in a single degree is itself
  concentrated in that degree, on the object the functor's image names.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexSingleIso_naturality_source` and
  `AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible_naturality_source`: the
  identification `R ℰom(A[0], B[0]) ≅ ℰom(A, B)[0]` for `A` invertible is natural in the source
  variable `A`. This is what carries the ideal inclusion through it.
* `Stacks.Divisors.internalHomPre_divisorIdealMap_eq`: precomposition with the ideal inclusion
  `ℐ_D ⟶ 𝒪_X`, read through `ℰom(𝒪_X, 𝒪_X) ≅ 𝒪_X`, is the canonical section of `𝒪_X(D)`.
* `Stacks.Divisors.structureDualIso_comp`: the resulting square, which is the hypothesis of
  `CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂`.

## Implementation notes

The bifunctor model of [Stacks, Tag 0A77] brings the global locally small instances
`SheafOfModules.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
into scope, and they would be preferred to `HasDerivedCategory.standard`; here
`HasDerivedCategory.standard` is pinned at a priority that outranks them.

The structure sheaf of `X` as a module over itself occurs under three spellings —
`(Stacks.Divisors.normalShortComplex D).X₁`, `SheafOfModules.unit (structureSheafRing _)` and
the unit of the ring sheaf of the ringed site of `X` — which are equal by `rfl` but not at the
`instances` transparency that instance search uses, so its invertibility is supplied as a local
instance at two of them. For the same reason the proofs below are written in term mode wherever
the goal mixes the ringed-space and ringed-site spellings: `rewrite` refuses a target that is
not type-correct at `implicit` transparency, which such a goal is not.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
    {A A' B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-! ### Naturality of the single-complex Hom identification in the source -/

/-- **The collapse `SheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` is natural in the source.** The
map of internal Hom complexes induced by `ι : A' ⟶ A` becomes, after the collapse, the
precomposition map `ℰom(A, B) ⟶ ℰom(A', B)`.

Both complexes are concentrated in degree zero, so only that degree has to be checked, and
there the collapse is `AlgebraicGeometry.RingedSite.homComponent`: reading off the unique
possibly nonzero component of a Hom cochain. That component of the induced map is pre- and
postcomposition by `AlgebraicGeometry.RingedSite.sectionsIso_homMap_v`, which is exactly what
precomposition on the internal Hom sheaf does on sections. -/
theorem sheafHomComplexSingleIso_naturality_source (ι : A' ⟶ A) :
    homMap X ((HomologicalComplex.single (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map ι) (𝟙 (sgl X B)) ≫
        (sheafHomComplexSingleIso X A' B).hom =
      (sheafHomComplexSingleIso X A B).hom ≫
        (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (internalHomPre X ι) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨U⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change ((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X (sgl X A') (sgl X B)).sectionsIso U).hom.f 0)
        (((homMap X ((HomologicalComplex.single (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map ι) (𝟙 (sgl X B))).f 0).val.app (op U) s)).v 0 (0 + 0)
        rfl).val = _
    rw [sectionsIso_homMap_v]
    rfl
  · exact (isZero_sgl_X X (internalHomSheaf X A' B) n hn).eq_of_tgt _ _

section Derived

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (Hd : DerivedInternalHom.{u, d} X)

/-- **An invertible sheaf is its own derived dual, naturally in the source.** For `ι : A' ⟶ A` a
morphism of invertible sheaves of modules, the identification
`R SheafHom(A[0], B[0]) ≅ SheafHom(A, B)[0]` of
`AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible` carries the derived
precomposition map to the underived one.

The comparison from the internal Hom complex to the derived internal Hom is natural in the
source (`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality_source`) and is
invertible at an invertible single-degree source, so this is the naturality of the collapse
`sheafHomComplexSingleIso_naturality_source` conjugated by it. -/
theorem derivedSheafHomSingleIsoOfIsInvertible_naturality_source
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property A]
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property A'] (ι : A' ⟶ A) :
    (Hd.hom.map (DerivedCategory.Q.map
            ((HomologicalComplex.single (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ) 0).map ι)).op).app (DerivedCategory.Q.obj (sgl X B)) ≫
        (derivedSheafHomSingleIsoOfIsInvertible X A' B Hd).hom =
      (derivedSheafHomSingleIsoOfIsInvertible X A B Hd).hom ≫
        DerivedCategory.Q.map ((HomologicalComplex.single (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (internalHomPre X ι)) := by
  have _ : ∀ (C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      [Stacks.SheafOfModules.IsInvertible X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property C],
      IsIso (strictlyPerfectHomComparison X Hd (sgl X C) (sgl X B)) := fun C _ =>
    strictlyPerfectHomComparison_isIso_of_isInvertible X Hd 0 C (sgl X B)
  have hnat := strictlyPerfectHomComparison_naturality_source X Hd (sgl X A) (sgl X A')
    (sgl X B) ((HomologicalComplex.single (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) 0).map ι)
  have hdeg : DerivedCategory.Q.map (homMap X
          ((HomologicalComplex.single (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map ι) (𝟙 (sgl X B))) ≫
        DerivedCategory.Q.map (sheafHomComplexSingleIso X A' B).hom =
      DerivedCategory.Q.map (sheafHomComplexSingleIso X A B).hom ≫
        DerivedCategory.Q.map ((HomologicalComplex.single (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) 0).map (internalHomPre X ι)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sheafHomComplexSingleIso_naturality_source]
  dsimp only [derivedSheafHomSingleIsoOfIsInvertible, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_inv]
  rw [← cancel_epi (strictlyPerfectHomComparison X Hd (sgl X A) (sgl X B)),
    ← Category.assoc, ← hnat, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, hdeg,
    IsIso.hom_inv_id_assoc]

end Derived

end AlgebraicGeometry.RingedSite

namespace CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]

/-- **Descent of a single-degree conclusion along an exact, fully faithful functor.** If `F` is
exact and fully faithful and `F` carries `K` to `F(N)` placed in degree `n`, then `K` is `N`
placed in degree `n`.

`F` is exact, so it commutes with the cohomology of the derived category
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`); being faithful it reflects zero
objects, so the cohomology of `K` vanishes outside degree `n` and `K` is its own `n`-th
cohomology placed in degree `n`. That cohomology has the same image under `F` as `N` does, so
full faithfulness identifies the two. -/
def isoSingleOfFullyFaithful [F.Full] [F.Faithful]
    (K : DerivedCategory C₁) (N : C₁) (n : ℤ)
    (e : F.mapDerivedCategory.obj K ≅ (DerivedCategory.singleFunctor C₂ n).obj (F.obj N)) :
    K ≅ (DerivedCategory.singleFunctor C₁ n).obj N := by
  have key : ∀ j : ℤ, IsZero ((DerivedCategory.homologyFunctor C₂ j).obj
      ((DerivedCategory.singleFunctor C₂ n).obj (F.obj N))) →
      IsZero ((DerivedCategory.homologyFunctor C₁ j).obj K) := by
    intro j hj
    have h : IsZero (F.obj ((DerivedCategory.homologyFunctor C₁ j).obj K)) :=
      (hj.of_iso ((DerivedCategory.homologyFunctor C₂ j).mapIso e)).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso j).app K).symm
    exact (IsZero.iff_id_eq_zero _).2 (F.map_injective (h.eq_of_src _ _))
  have hz : ∀ j : ℤ, j ≠ n → IsZero ((DerivedCategory.homologyFunctor C₁ j).obj K) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · exact key j (((DerivedCategory.singleFunctor C₂ n).obj (F.obj N)).isZero_of_isGE n j h)
    · exact key j (((DerivedCategory.singleFunctor C₂ n).obj (F.obj N)).isZero_of_isLE n j h)
  refine Classical.choice (K.nonempty_iso_singleFunctor_homologyFunctor_of_isZero n hz) ≪≫
    (DerivedCategory.singleFunctor C₁ n).mapIso (F.preimageIso ?_)
  exact ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm ≪≫
    (DerivedCategory.homologyFunctor C₂ n).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C₂ n).app (F.obj N)

end CategoryTheory.Functor

/-! ### The internal Hom sheaf out of the structure sheaf, at the unit section -/

section UnitIso

variable {Y : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} Y)
  (U : TopologicalSpace.Opens Y)

/-- The morphism `𝒪_U ⟶ 𝒪_U` attached to the unit section is the identity: both take the unit
section to itself, and a morphism out of the structure sheaf is its value at the unit
section. -/
theorem unitOverAddEquiv_symm_one :
    (Stacks.SheafOfModules.unitOverAddEquiv Rc (SheafOfModules.unit (structureSheaf Rc)) U).symm
        (1 : (structureSheaf Rc).obj.obj (op U)) =
      𝟙 ((SheafOfModules.unit (structureSheaf Rc)).over U) :=
  (Stacks.SheafOfModules.unitOverAddEquiv Rc
      (SheafOfModules.unit (structureSheaf Rc)) U).injective
    (((Stacks.SheafOfModules.unitOverAddEquiv Rc
      (SheafOfModules.unit (structureSheaf Rc)) U).apply_symm_apply _).trans rfl)

/-- **The inverse of `ℰom(𝒪_X, 𝒪_X) ≅ 𝒪_X` takes the unit section to the identity**, read
through the identification of the sections of the internal Hom sheaf with morphisms of
restrictions.

The inverse is the comparison of two objects satisfying the characterisation of Stacks 01CO, so
it acts on sections as the identity; the section identification of the target one is evaluation
at the unit section. -/
theorem internalHomSheafUnitIso_inv_app_one :
    (Stacks.SheafOfModules.internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc))
          (SheafOfModules.unit (structureSheaf Rc))).sectionsEquiv U
        (((Stacks.SheafOfModules.internalHomSheafUnitIso Rc
            (SheafOfModules.unit (structureSheaf Rc))).inv.val.app (op U))
          (1 : (structureSheaf Rc).obj.obj (op U))) =
      𝟙 ((SheafOfModules.unit (structureSheaf Rc)).over U) := by
  refine (SheafHom.isPostcomp_postcomp (𝟙 (SheafOfModules.unit (structureSheaf Rc)))
    (Stacks.SheafOfModules.unitSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)))
    (Stacks.SheafOfModules.internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc))
      (SheafOfModules.unit (structureSheaf Rc))) U
    (1 : (structureSheaf Rc).obj.obj (op U))).trans ?_
  rw [show SheafOfModules.Hom.over (𝟙 (SheafOfModules.unit (structureSheaf Rc))) U = 𝟙 _ from
    (SheafOfModules.overFunctor (structureSheaf Rc) U).map_id _, Category.comp_id]
  exact unitOverAddEquiv_symm_one Rc U

/-- `internalHomSheafUnitIso_inv_app_one` with the wrapper of the section
identification stripped: the section of `ℰom(𝒪_X, 𝒪_X)` over `U` named by the unit section is
the identity natural family. -/
theorem internalHomSheafUnitIso_inv_val_app_one :
    ((Stacks.SheafOfModules.internalHomSheafUnitIso Rc
          (SheafOfModules.unit (structureSheaf Rc))).inv.val.app (op U))
        (1 : (structureSheaf Rc).obj.obj (op U)) =
      𝟙 (((SheafOfModules.unit (structureSheaf Rc)).over U).val) :=
  (congrArg SheafOfModules.Hom.val (internalHomSheafUnitIso_inv_app_one Rc U)).trans rfl

end UnitIso

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-! ### The ideal inclusion as the canonical section -/

/-- **Precomposition with the ideal inclusion is multiplication by the canonical section.** The
map `ℰom(𝒪_X, 𝒪_X) ⟶ ℰom(ℐ_D, 𝒪_X) = 𝒪_X(D)` induced by `ℐ_D ⟶ 𝒪_X`, read through
`𝒪_X ≅ ℰom(𝒪_X, 𝒪_X)`, is the first map `𝒪_X ⟶ 𝒪_X(D)` of the normal short exact sequence,
that is, multiplication by the canonical section `1_D` of [Stacks, Tag 01WX].

A morphism out of the structure sheaf is its value at the unit section, so both sides are
determined by where they send `1`; the left one sends it to the ideal inclusion read over every
open, which is exactly `Stacks.Divisors.canonicalSectionComponent`. -/
theorem internalHomPre_divisorIdealMap_eq :
    (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf
        ((normalShortComplex D).X₁)).inv ≫
      AlgebraicGeometry.RingedSite.internalHomPre (Stacks.SheafOfModules.ringedSite X.sheaf)
        (C := (normalShortComplex D).X₁) (Stacks.IdealSheafSequence.divisorIdealMap D) =
      (normalShortComplex D).f :=
  (invertibleSheaf' D).unitHomEquiv.injective
    (Eq.trans
      (PresheafOfModules.sections_ext _ _ (fun U =>
        (congrArg (fun t => (AlgebraicGeometry.RingedSite.internalHomPre
              (Stacks.SheafOfModules.ringedSite X.sheaf) (C := (normalShortComplex D).X₁)
              (Stacks.IdealSheafSequence.divisorIdealMap D)).val.app U t)
          (internalHomSheafUnitIso_inv_val_app_one X.sheaf U.unop)).trans rfl))
      ((invertibleSheaf' D).unitHomEquiv.apply_symm_apply (canonicalSection' D)).symm)

/-- The structure sheaf of `X`, as a module over itself, is invertible. -/
local instance isInvertible_unitModule :
    Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.ringedSite X.sheaf).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).property
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-- The structure sheaf of `X`, as a module over itself, is invertible; at the spelling in which
the first term of the normal short complex presents it. -/
local instance isInvertible_normalShortComplex_X₁ :
    Stacks.SheafOfModules.IsInvertible (Stacks.SheafOfModules.ringedSite X.sheaf).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite X.sheaf).O).property
      ((normalShortComplex D).X₁) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

/-! ### The ideal sequence and the triangle it gives -/

/-- The ideal short complex `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` of [Stacks, Tag 0C6K]. -/
def idealShortComplex : ShortComplex X.Modules :=
  ShortComplex.mk (Stacks.IdealSheafSequence.divisorIdealMap D)
    (Stacks.IdealSheafSequence.divisorQuotientMap D)
    (Stacks.IdealSheafSequence.divisorIdeal_shortExact D).choose

omit [IsEffectiveCartierDivisor D] in
/-- The ideal sequence of a closed subscheme is short exact, [Stacks, Tag 0C6K]. -/
@[sga "6 X 5.2.2"]
theorem idealShortComplex_shortExact : (idealShortComplex D).ShortExact :=
  (Stacks.IdealSheafSequence.divisorIdeal_shortExact D).choose_spec

/-- `R ℰom_{𝒪_X}(-, 𝒪_X)`, the contravariant functor [Stacks, Tag 08I0] is applied to. -/
abbrev derivedDual : (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules :=
  (Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁))

/-- **`R ℰom_{𝒪_X}(ℐ_D, 𝒪_X) ≅ 𝒪_X(D)`:** the ideal sheaf of an effective Cartier divisor is
invertible, so it is its own derived dual. -/
def idealDualIso :
    (derivedDual D).obj (op ((DerivedCategory.singleFunctor X.Modules 0).obj
        (negativeTwist' D))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (normalShortComplex D).X₂ :=
  AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible
    (Stacks.SheafOfModules.ringedSite X.sheaf) (negativeTwist' D) ((normalShortComplex D).X₁)
    (Stacks.SheafOfModules.derivedInternalHom X.sheaf)

/-- `R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ ℰom_{𝒪_X}(𝒪_X, 𝒪_X)[0]`, before the source is evaluated away. -/
def structureDualIsoAux :
    (derivedDual D).obj (op ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((normalShortComplex D).X₁))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (AlgebraicGeometry.RingedSite.internalHomSheaf
          (Stacks.SheafOfModules.ringedSite X.sheaf) ((normalShortComplex D).X₁)
          ((normalShortComplex D).X₁)) :=
  AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible
    (Stacks.SheafOfModules.ringedSite X.sheaf) ((normalShortComplex D).X₁)
    ((normalShortComplex D).X₁) (Stacks.SheafOfModules.derivedInternalHom X.sheaf)

/-- **`R ℰom_{𝒪_X}(𝒪_X, 𝒪_X) ≅ 𝒪_X`:** the structure sheaf is its own derived dual, and the
internal Hom sheaf out of the structure sheaf is its target. -/
def structureDualIso :
    (derivedDual D).obj (op ((DerivedCategory.singleFunctor X.Modules 0).obj
        ((normalShortComplex D).X₁))) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (normalShortComplex D).X₁ :=
  structureDualIsoAux D ≪≫ (DerivedCategory.singleFunctor X.Modules 0).mapIso
    (Stacks.SheafOfModules.internalHomSheafUnitIso X.sheaf ((normalShortComplex D).X₁))

/-- **The triangle of [Stacks, Tag 08I0] and the normal short exact sequence share their first
map.** Applying `R ℰom_{𝒪_X}(-, 𝒪_X)` to the ideal inclusion `ℐ_D ⟶ 𝒪_X` and identifying both
sides with `𝒪_X` and `𝒪_X(D)` in degree zero gives the first map `𝒪_X ⟶ 𝒪_X(D)` of the normal
short exact sequence.

This is naturality of the derived dual of an invertible sheaf in its source
(`AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible_naturality_source`)
followed by `Stacks.Divisors.internalHomPre_divisorIdealMap_eq`. -/
theorem structureDualIso_comp :
    (derivedDual D).map ((DerivedCategory.singleFunctor X.Modules 0).map
          (idealShortComplex D).f).op ≫ (idealDualIso D).hom =
      (structureDualIso D).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0).map (normalShortComplex D).f := by
  have h := (Iso.inv_comp_eq _).mp (internalHomPre_divisorIdealMap_eq D)
  exact Eq.trans
    (AlgebraicGeometry.RingedSite.derivedSheafHomSingleIsoOfIsInvertible_naturality_source
      (Stacks.SheafOfModules.ringedSite X.sheaf) (B := (normalShortComplex D).X₁)
      (Stacks.SheafOfModules.derivedInternalHom X.sheaf)
      (Stacks.IdealSheafSequence.divisorIdealMap D))
    (Eq.trans
      (congrArg (fun t => (structureDualIsoAux D).hom ≫
        (DerivedCategory.singleFunctor X.Modules 0).map t) h)
      (Eq.trans
        (congrArg (fun t => (structureDualIsoAux D).hom ≫ t)
          ((DerivedCategory.singleFunctor X.Modules 0).map_comp _ _))
        (Category.assoc _ _ _).symm))

/-- **[Stacks, Tag 0B4B], the ambient computation.** `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` is `i_* 𝒩`
placed in degree one.

[Stacks, Tag 08I0] turns the ideal sequence into a distinguished triangle; rotated, its first
two terms and its first map are those of the normal short exact sequence, by
`Stacks.Divisors.structureDualIso_comp`, so
`CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂` identifies the third terms. -/
def idealDerivedSheafHomIso :
    (derivedDual D).obj (op ((DerivedCategory.singleFunctor X.Modules 0).obj
        (idealShortComplex D).X₃)) ≅
      (DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₃ := by
  have hR := (Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁))
    (idealShortComplex_shortExact D).singleTriangle
    (idealShortComplex_shortExact D).singleTriangle_distinguished).choose_spec
  have e := isoTriangleOfIso₁₂ _ (normalShortComplex_shortExact D).singleTriangle
    (rot_of_distTriang _ hR)
    (normalShortComplex_shortExact D).singleTriangle_distinguished
    (structureDualIso D) (idealDualIso D) (structureDualIso_comp D)
  exact ((shiftFunctorCompIsoId (DerivedCategory X.Modules) (1 : ℤ) (-1)
      (by ring)).app _).symm ≪≫
    (shiftFunctor (DerivedCategory X.Modules) (-1 : ℤ)).mapIso (Triangle.π₃.mapIso e) ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (-1) 1 0 (by ring)).app _

/-! ### Descending along the closed immersion -/

/-- `Ri_* 𝒪_D` is `i_* 𝒪_D` placed in degree zero: pushforward along a closed immersion is
exact, so derived pushforward carries a single complex to a single complex. -/
def pushforwardStructureSheafIso :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        (AlgebraicGeometry.RingedSite.derivedStructureSheaf
          (Stacks.SheafOfModules.ringedSite (closedQuotient D).Z.sheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (idealShortComplex D).X₃ :=
  ((modulePushforward (closedQuotient D).i).mapDerivedCategorySingleFunctor 0).app
    (SheafOfModules.unit (structureSheafRing D.subscheme.toRingedSpace))

/-- **[Stacks, Tag 0B4B], pushed forward to `X`.** `Ri_* R ℰom(𝒪_D, 𝒪_X)` is `i_* 𝒩` placed in
degree one.

The bifunctor model of [Stacks, Tag 0A77] identifies the left-hand side with
`R ℰom_{𝒪_X}(Ri_* 𝒪_D, 𝒪_X)`, and `Ri_* 𝒪_D` is `i_* 𝒪_D` in degree zero, so this is
`Stacks.Divisors.idealDerivedSheafHomIso`. -/
def pushforwardDerivedSheafHomExactSupportIso :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((closedQuotient D).derivedSheafHomExactSupport.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁))) ≅
      (DerivedCategory.singleFunctor X.Modules 1).obj (normalShortComplex D).X₃ :=
  (closedQuotient D).derivedSheafHomExactSupportPushforwardNatIso.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁)) ≪≫
    ((derivedDual D).mapIso (pushforwardStructureSheafIso D).op).symm ≪≫
    idealDerivedSheafHomIso D

/-- **[Stacks, Tag 0B4B]**, at the description `𝒩 = i^* 𝒪_X(D)` of the normal sheaf:

`R ℰom(𝒪_D, 𝒪_X) ≅ (i^* 𝒪_X(D))[-1]` in `D(𝒪_D)`.

Pushforward of modules along the closed immersion of `D` is exact and fully faithful
([Stacks, Tag 08KS]), and `Stacks.Divisors.pushforwardDerivedSheafHomExactSupportIso` says that
it carries the left-hand side to `i_* 𝒩` placed in degree one, so
`CategoryTheory.Functor.isoSingleOfFullyFaithful` descends the conclusion to `D`. -/
def derivedSheafHomExactSupportIsoNormalShift :
    (closedQuotient D).derivedSheafHomExactSupport.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ((normalShortComplex D).X₁)) ≅
      (DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) :=
  (modulePushforward (closedQuotient D).i).isoSingleOfFullyFaithful _ _ 1
    (pushforwardDerivedSheafHomExactSupportIso D)

/-- **[Stacks, Tag 0B4B].** For `X` a scheme and `D ⊆ X` an effective Cartier divisor with
closed immersion `i : D ⟶ X` and normal sheaf `𝒩 = 𝒩_{D/X}`, there is an isomorphism

`𝒩[-1] ≅ R ℰom(𝒪_D, 𝒪_X)` in `D(𝒪_D)`,

where `R ℰom(𝒪_D, -)` is the right adjoint of derived pushforward of [Stacks, Tag 0A76].

This is `Stacks.Divisors.derivedSheafHomExactSupportIsoNormalShift` precomposed with the
normal-sheaf clause of [Stacks, Tag 0B3P] (`Stacks.Divisors.normalSheafIsoInvertibleSheaf`),
which identifies `𝒩_{D/X}` with `i^* 𝒪_X(D)` — the description of `𝒩` the source fixes before
stating the lemma. See the module documentation for the proof.

This isomorphism is constructed independently of the canonical comparison morphism
`Stacks.Divisors.normalSheafShiftToDerivedSheafHomExactSupport`; that the comparison morphism is
itself invertible is `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport`. -/
@[stacks 0B4B "the isomorphism 𝒩[-1] ≅ R ℰom(𝒪_D, 𝒪_X), which is what the tag asserts; it is \
not identified with the canonical comparison morphism \
Stacks.Divisors.normalSheafShiftToDerivedSheafHomExactSupport"]
def normalSheafShiftIsoDerivedSheafHomExactSupport :
    (DerivedCategory.singleFunctor D.subscheme.Modules 1).obj (normalSheaf D.subschemeι) ≅
      (closedQuotient D).derivedSheafHomExactSupport.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) :=
  (DerivedCategory.singleFunctor D.subscheme.Modules 1).mapIso
      (normalSheafIsoInvertibleSheaf D) ≪≫
    (derivedSheafHomExactSupportIsoNormalShift D).symm

end Stacks.Divisors

end
