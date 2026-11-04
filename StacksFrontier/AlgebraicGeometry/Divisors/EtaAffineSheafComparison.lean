module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaAffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import StacksCore.Tactic.StacksAttribute

/-!
# The Berthelot–Ogus décalage on an affine scheme, as an identification of sheaves

Let `R` be a commutative ring, let `D ⊆ Spec R` be an effective Cartier divisor whose ideal
sheaf `I` is generated over `Spec R` by a section `g` — this is the hypothesis `D = V(f)` of
[Stacks, Tag 0GTV], with `f ∈ Γ(Spec R, ⊤)` the image of `g` — and let `F^•` be a complex of
quasi-coherent `𝒪_{Spec R}`-modules whose terms are `I`-torsion free. Then the sheaf-theoretic
décalage `η_I F^•` of [Stacks, Tag 0GT2] is the complex of quasi-coherent modules attached to
the ordinary décalage `η_f (Γ(Spec R, F^•))` of More on Algebra, [Stacks, Tag 0F7N]:

`η_I F^• ≅ (η_f Γ(Spec R, F^•))^~`.

This lifts the second assertion of [Stacks, Tag 0F8M] from *sections* to *sheaves*. That
assertion, `Stacks.Divisors.Eta.etaSectionsIso`, identifies the complex of sections of `η_I F^•`
over an affine open with `η_f` of the complex of sections of `F^•`; the identification of sheaves
follows from the equivalence between `R`-modules and quasi-coherent `𝒪_{Spec R}`-modules.

## Main results

* `Stacks.Divisors.Eta.tildeGammaIso`: a quasi-coherent `𝒪_{Spec R}`-module is the sheaf
  attached to its `R`-module of global sections.
* `Stacks.Divisors.Eta.gammaTildeComplexIso`: the same for a complex of quasi-coherent modules,
  naturally in the complex.
* `Stacks.Divisors.Eta.etaObjTildeIso`: **the identification `η_I F^• ≅ (η_f Γ F^•)^~` of
  complexes of sheaves.**

## Implementation notes

The equivalence used is the *abelian* equivalence `AlgebraicGeometry.tildeEquiv` between
`R`-modules and quasi-coherent `𝒪_{Spec R}`-modules, not the derived equivalence
`D(R) ≌ D_QCoh(𝒪_X)` of [Stacks, Tag 06Z0]: the statement is a chain-level identification of
complexes, degree by degree and compatibly with the differentials. Only the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ : (Γ M)^~ ⟶ M` is used, which is invertible exactly
when `M` is quasi-coherent by `AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`; its
naturality gives the compatibility of `gammaTildeComplexIso` with the differentials.

`Stacks.Divisors.Eta.etaSectionsIso` is stated at a single affine open, with no compatibility
with restriction to smaller opens. None is needed: the single isomorphism of global sections is
transported along the equivalence, and compatibility with restriction is supplied by the
naturality of its counit.

`Stacks.IdealTorsion.Eta.sectionsComplex` takes sections over `⊤` and so produces a complex of
modules over `Γ(Spec R, ⊤)`, whereas `AlgebraicGeometry.tilde.functor` is indexed by `R`. The two
rings are identified by `AlgebraicGeometry.Scheme.ΓSpecIso`, and
`AlgebraicGeometry.moduleSpecΓFunctor` is by definition evaluation at `⊤` followed by restriction
of scalars along it (`moduleSpecGammaFunctor_eq`). The statement of `etaObjTildeIso` therefore
carries that restriction of scalars explicitly, applied to `η_f` formed over `Γ(Spec R, ⊤)`, the
ring in which the generating section lives.

`Stacks.IdealTorsion.Eta.etaObj` is indexed by `structureSheaf (Spec R).toRingedSpace.sheaf`
while `AlgebraicGeometry.tilde.functor` lands in
`(Spec R).Modules = SheafOfModules (Spec R).ringCatSheaf`. These are the same type but are not
interchangeable by instance search; `tildeGammaIso` and `gammaTildeComplexIso` are stated in the
second spelling, and the invertibility of the counit is taken from the theorem
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` rather than from an instance.

## References

* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GT2](https://stacks.math.columbia.edu/tag/0GT2)
* [Stacks Project, Tag 0F7N](https://stacks.math.columbia.edu/tag/0F7N)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.IdealTorsion (IsIdealTorsionFree GeneratesIdealOn)
open Stacks.IdealTorsion.Eta (etaObj sectionsComplex sectionsFunctor generatorSection)

universe u

namespace Stacks.Divisors.Eta

variable (R : CommRingCat.{u})

/-- Global sections on `Spec R`, as a functor to `R`-modules, is evaluation at `⊤` followed by
restriction of scalars along `Γ(Spec R, ⊤) ≅ R`. -/
theorem moduleSpecGammaFunctor_eq :
    AlgebraicGeometry.moduleSpecΓFunctor (R := R) =
      sectionsFunctor (Spec R).toRingedSpace ⊤ ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom := rfl

/-- Global sections on `Spec R` is an additive functor, being evaluation at `⊤` followed by a
restriction of scalars. -/
instance moduleSpecGammaFunctor_additive :
    (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).Additive :=
  inferInstanceAs ((sectionsFunctor (Spec R).toRingedSpace ⊤ ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).Additive)

/-- The complex of `R`-modules of global sections of a complex of `𝒪_{Spec R}`-modules is the
complex of its modules of sections over `⊤`, with scalars restricted along
`Γ(Spec R, ⊤) ≅ R`. -/
theorem moduleSpecGammaFunctor_mapHomologicalComplex_eq
    (G : CochainComplex
      (SheafOfModules.{u} (structureSheaf (Spec R).toRingedSpace.sheaf)) ℤ) :
    ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G =
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (sectionsComplex (Spec R).toRingedSpace G ⊤) := rfl

/-- **A quasi-coherent `𝒪_{Spec R}`-module is the sheaf attached to its module of global
sections.** The comparison is the counit `(Γ M)^~ ⟶ M` of the `~`–`Γ` adjunction, which is
invertible exactly on the quasi-coherent modules. -/
noncomputable def tildeGammaIso (M : (Spec R).Modules) (hM : M.IsQuasicoherent) :
    (AlgebraicGeometry.tilde.functor R).obj
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj M) ≅ M :=
  @asIso _ _ _ _ (AlgebraicGeometry.Scheme.Modules.fromTildeΓ M)
    ((AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ M).mp hM)

/-- **A complex of quasi-coherent `𝒪_{Spec R}`-modules is the complex of sheaves attached to its
complex of modules of global sections.** The isomorphism is given degreewise by the counit of
the `~`–`Γ` adjunction. -/
noncomputable def gammaTildeComplexIso (G : CochainComplex (Spec R).Modules ℤ)
    (hqc : ∀ n : ℤ, (G.X n).IsQuasicoherent) :
    ((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ≅ G :=
  HomologicalComplex.Hom.isoOfComponents (fun n => tildeGammaIso R (G.X n) (hqc n))
    (fun i j _ => by
      exact ((AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality
        (G.d i j)).symm)

/-- **The décalage of a complex of quasi-coherent modules on an affine scheme is the sheaf
complex attached to the décalage of its complex of global sections.** Let `D ⊆ Spec R` be an
effective Cartier divisor with ideal sheaf `I`, generated over `Spec R` by a section `g` with
image `f ∈ Γ(Spec R, ⊤)` — the hypothesis `D = V(f)` — and let `F^•` be a complex of
quasi-coherent `𝒪_{Spec R}`-modules whose terms are `I`-torsion free. Then

`η_I F^• ≅ (η_f Γ(Spec R, F^•))^~`. -/
noncomputable def etaObjTildeIso
    (D : (Spec R).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (F : CochainComplex
      (SheafOfModules.{u} (structureSheaf (Spec R).toRingedSpace.sheaf)) ℤ)
    (hqc : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (htf : ∀ n : ℤ, IsIdealTorsionFree (Spec R).toRingedSpace (idealSheafι D) (F.X n))
    (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))
    (hg : GeneratesIdealOn (Spec R).toRingedSpace ⊤ g) :
    etaObj (Spec R).toRingedSpace (idealSheaf D) (idealSheafι D) F htf ≅
      ((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (EtaComplex.etaObject
            (generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g)
            (sectionsComplex (Spec R).toRingedSpace F ⊤))) :=
  (gammaTildeComplexIso R (etaObj (Spec R).toRingedSpace (idealSheaf D) (idealSheafι D) F htf)
      (fun n => isQuasicoherent_etaObj D F hqc htf n)).symm ≪≫
    ((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
        (etaSectionsIso D F hqc htf ⊤ (isAffineOpen_top (Spec R)) g hg).symm)

end Stacks.Divisors.Eta

end
