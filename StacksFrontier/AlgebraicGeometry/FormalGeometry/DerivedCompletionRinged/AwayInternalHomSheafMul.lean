module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomTensorCurrying
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex

/-!
# Internal Hom out of two localizations, for a single sheaf of modules

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. For every sheaf `H` of
`𝒪`-modules,

`SheafHom_𝒪(𝒪_f, SheafHom_𝒪(𝒪_g, H)) = SheafHom_𝒪(𝒪_{g f}, H)`,

over `𝒪` throughout. This is the displayed identity in the proof of [Stacks, Tag 0996(3)] read
at the level of single sheaves, which is how the source states it; the form of it that clause
actually uses, with a complex in place of `H`, is
`AlgebraicGeometry.RingedSite.awaySheafHomComplexMulIso` of `AwayInternalHomMul.lean`.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayInternalHomSheafMulIso`: **the identity above**.

## Implementation notes

Stacks 03EO for sheaves, `Stacks.SheafOfModules.InternalHom.sheafCurryIso`, is
`SheafHom_𝒪(F ⊗_𝒪 G, H) ≅ SheafHom_𝒪(F, SheafHom_𝒪(G, H))`; taking `F = 𝒪_f` and `G = 𝒪_g` and
transporting the first variable along `AlgebraicGeometry.RingedSite.awayTensorSheafIso` is the
whole proof. The transport is `Stacks.SheafOfModules.InternalHom.siteInternalHomFirstFunctor`,
which is internal Hom in its first variable as a functor into the opposite category, so the
isomorphism it produces has to be turned round twice — once by `Iso.unop` and once by
`Iso.symm`.

`AlgebraicGeometry.RingedSite.internalHomSheaf` and
`Stacks.SheafOfModules.InternalHom.siteSheafInternalHom` are the same construction at the two
spellings of the ring sheaf — `AlgebraicGeometry.RingedSite.ringSheaf` and
`Stacks.SheafOfModules.TensorColimits.underlyingRingSheaf` — which instance search does not
connect but terms cross freely, by `rfl`. The statement is at the ringed-site spelling, which is
the one the rest of the derived-completion development uses.

Nothing here carries a `stacks` attribute: this is the identity displayed inside the proof of
Tag 0996(3), not that clause, which is
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayMulIso`.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.SheafOfModules
open Stacks.SheafOfModules.InternalHom

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The internal Hom sheaf of the derived-completion development and the one of the
internal-Hom-and-flatness development are the same sheaf; they differ only in the spelling of
the sheaf of rings. -/
theorem internalHomSheaf_eq_siteSheafInternalHom
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSheaf X A B = siteSheafInternalHom X.J X.O A B :=
  rfl

/-- **`SheafHom_𝒪(𝒪_f, SheafHom_𝒪(𝒪_g, H)) = SheafHom_𝒪(𝒪_{g f}, H)`**, the identity displayed
in the proof of Stacks Tag 0996(3), for a single sheaf `H` of `𝒪`-modules and with both internal
Homs taken over `𝒪`. -/
def awayInternalHomSheafMulIso
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSheaf X (awayModule X f) (internalHomSheaf X (awayModule X g) H) ≅
      internalHomSheaf X (awayModule X (mulGlobalSection X f g)) H :=
  (sheafCurryIso X.O (awayModule X f) (awayModule X g) H).symm ≪≫
    ((siteInternalHomFirstFunctor X.J X.O H).mapIso (awayTensorSheafIso X f g)).unop.symm

end AlgebraicGeometry.RingedSite

end
