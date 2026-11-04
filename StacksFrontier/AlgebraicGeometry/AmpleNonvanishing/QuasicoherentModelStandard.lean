module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.AmpleAffineDiagonal
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.NonzeroHomology

/-!
# Stacks 08DB at the standard model of the derived category

`Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso_of_isAmple` presents an object of
`D_QCoh(𝒪_X)` by a complex of quasi-coherent modules, at the *locally small* model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the only model [Stacks, Tag 06Z0], and
hence [Stacks, Tag 08DB], is available at. The hypercohomology identification of
[Stacks, Tag 08JA] that the conclusion of [Stacks, Tag 0BQR] is stated through is available only
at `CategoryTheory.HasDerivedCategory.standard`. This file carries the presentation across.

Nothing is transported by hand: `Stacks.Injectives.grothendieckModelEquiv` is the identity on
objects and carries `DerivedCategory.Q` of the standard model to `DerivedCategory.Q` of the
locally small one *on the nose*
(`Stacks.Injectives.grothendieckModelEquiv_comp_Q`), so the isomorphism of the locally small model
is carried over by applying the inverse functor and cancelling the unit of the equivalence.

## Main results

* `Stacks.AmpleNonvanishing.exists_quasicoherentComplex_isoStandard_of_isAmple`:
  **[Stacks, Tag 08DB] at the hypotheses of [Stacks, Tag 0BQR], read at the standard model.** On a
  scheme carrying an ample invertible `𝒪_X`-module, the image of every object of `D_QCoh(𝒪_X)`
  under the comparison of the two models of `D(𝒪_X)` is isomorphic, in the standard model, to the
  class of a cochain complex of quasi-coherent `𝒪_X`-modules.

## Implementation notes

No `HasDerivedCategory` instance is left to search here: the locally small model is the global
instance and the standard one is named by `@`-application, which is the discipline of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`.

## References

* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishing

/-- **[Stacks, Tag 08DB] at the hypotheses of [Stacks, Tag 0BQR], at the standard model.** For `K`
an object of `D_QCoh(𝒪_X)` — taken at the locally small model, which is where
[Stacks, Tag 08DB] lives — the object of the standard model of `D(𝒪_X)` corresponding to it under
`Stacks.Injectives.grothendieckModelEquiv` is isomorphic to the class of a cochain complex `G` of
quasi-coherent `𝒪_X`-modules. The isomorphism at the locally small model is returned alongside,
at the *same* `G`, because a consumer needs both: the cohomology sheaves of `K` are read off at
the locally small model, where `D_QCoh(𝒪_X)` lives, and the derived tensor product and the
hypercohomology at the standard one. -/
theorem exists_quasicoherentComplex_isoStandard_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L)
    (K : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) :
    ∃ G : CochainComplex
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ,
      Nonempty (K.1 ≅ DerivedCategory.Q.obj
          (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G)) ∧
      Nonempty ((Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.obj K.1 ≅
        (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)).obj
          (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G)) := by
  obtain ⟨G, ⟨e⟩⟩ := exists_quasicoherentComplex_iso_of_isAmple X L hL K
  refine ⟨G, ⟨e⟩, ⟨(Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.mapIso
    (e ≪≫ eqToIso (Functor.congr_obj
      (Stacks.Injectives.grothendieckModelEquiv_comp_Q X.Modules) _).symm) ≪≫
    ((Stacks.Injectives.grothendieckModelEquiv X.Modules).unitIso.app _).symm⟩⟩

/-- **The first two lines of the argument of [Stacks, Tag 0BQR], bundled.** A nonzero object `K`
of `D_QCoh(𝒪_X)` on a scheme carrying an ample invertible module is the class of a cochain complex
`G` of quasi-coherent `𝒪_X`-modules *some cohomology sheaf of which is nonzero*, and the
isomorphism is available at the standard model of the derived category.

The two readings of `K` are bundled into one statement on purpose: the nonvanishing of the
cohomology sheaf has to be read at the locally small model — the model `D_QCoh(𝒪_X)` and
[Stacks, Tag 08DB] live at — and the isomorphism has to be delivered at the standard model, the
model [Stacks, Tag 08JA] lives at. A consumer that wanted both separately would have to install
both `HasDerivedCategory` instances in one module, where the two spellings of `D(𝒪_X)` become
ambiguous. -/
theorem exists_quasicoherentComplex_nonzeroHomology_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L)
    (K : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) (hK : ¬ IsZero K) :
    ∃ (G : CochainComplex
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ) (p : ℤ),
      ¬ IsZero ((((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G).homology p) ∧
      Nonempty ((Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.obj K.1 ≅
        (@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)).obj
          (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G)) := by
  have hKobj : ¬ IsZero K.1 := fun h => hK ((IsZero.iff_id_eq_zero K).2
    ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map_injective
        (by simpa using (IsZero.iff_id_eq_zero K.1).1 h)))
  obtain ⟨p, hp⟩ := StacksDraft.DerivedCategoryHomology.exists_nonzero_homology K.1 hKobj
  obtain ⟨G, ⟨eSmall⟩, hStd⟩ := exists_quasicoherentComplex_isoStandard_of_isAmple X L hL K
  refine ⟨G, p, fun h => hp (IsZero.of_iso h ?_), hStd⟩
  exact ((DerivedCategory.homologyFunctor X.Modules p).mapIso eSmall).trans
    ((DerivedCategory.homologyFunctorFactors X.Modules p).app _)

end Stacks.AmpleNonvanishing

end
