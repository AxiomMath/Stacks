module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# K-flat complexes of sheaves of modules on a ringed site

For a ringed site `(C, O)`, a complex `K` of `O`-modules is *K-flat* when the total tensor
complex `Tot(F ⊗_O K)` is acyclic for every acyclic complex `F` of `O`-modules.

## Main definitions

* `Stacks.SheafOfModules.KFlat.KFlat`: K-flatness of a complex of sheaves of `O`-modules.

## Main results

* `Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor`: the definition agrees with the general
  bifunctor-relative K-flatness of `CochainComplex.KFlatBifunctor.KFlat` taken at the tensor
  bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`.

## Implementation notes

The tensor product is the canonical sheafified tensor bifunctor
  `Stacks.SheafOfModules.Tensor.sheafTensor`
and the total tensor complex is `Stacks.SheafOfModules.Tensor.tensorComplex` (Stacks Tag 06YM), the
direct-sum total complex of the tensor double complex with the Koszul-sign differential.
Acyclicity is Mathlib's `HomologicalComplex.Acyclic`, the vanishing of every cohomology
sheaf.

The definition is written out in the shape the Stacks statement has, rather than as a
specialization of `CochainComplex.KFlatBifunctor.KFlat`, so that the tagged declaration says
on its face what Tag 06YN says.  The two are definitionally equal, which is the content of
`kFlat_iff_kFlatBifunctor` and is why its proof is `Iff.rfl`:
  `Stacks.SheafOfModules.Tensor.tensorComplex` is
`Stacks.SheafOfModules.Tensor.sheafTensor |>.map₂HomologicalComplex` and the bifunctor-relative
  total complex
`CochainComplex.KFlatBifunctor.totalComplex` is that same functor applied in the same order.
So the two spellings may be used interchangeably, and in particular every result about
`CochainComplex.KFlatBifunctor.KFlat` at `Stacks.SheafOfModules.Tensor.sheafTensor` — Stacks Tags
  06YP, 06YQ
and 07A3 — is a result about `KFlat` here.

`HasSheafify` (rather than merely `HasWeakSheafify`) is assumed because it is what makes
`Mod(O)` abelian, and abelianness is what supplies the cohomology sheaves that acyclicity
speaks of.

**Universes.**  `Stacks.SheafOfModules.Tensor.sheafTensor` forces the universe of the sections
  of
the ring sheaf to agree with the universe of the sections of the module sheaves, and nothing
else: the object universe `u` and the morphism universe `v` of the site are both independent
of that common ring-and-module universe `w`.  So K-flatness is available on a site whose
objects live above its structure sheaf — in particular on an
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, the shape of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`.

This definition used to be read at a ring-and-module universe `max u v w`, with a note
attributing the constraint to the monoidal structure on presheaves of modules that
`Stacks.SheafOfModules.Tensor.presheafTensor` uses.  That attribution was wrong:
`Stacks.SheafOfModules.Tensor.sheafTensor` and `Stacks.SheafOfModules.Tensor.ringSheaf` are
each stated with their three universes independent, and the one theorem here holds by
definitional unfolding alone, so nothing in the file ever saw the constraint.  Setting `w` to
`max u v w` recovers the former statement unchanged.

## References

* [The Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
* [The Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules.KFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{w})
variable [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- A cochain complex `K` of sheaves of `O`-modules on a ringed site `(C, O)` is **K-flat**
when the total tensor complex `Tot(F ⊗_O K)` is acyclic for every acyclic cochain complex `F`
of sheaves of `O`-modules. -/
@[stacks 06YN]
abbrev KFlat
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
      Prop :=
  ∀ F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    F.Acyclic → (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj F).obj K).Acyclic

/-- K-flatness on a ringed site is the general bifunctor-relative K-flatness of
`CochainComplex.KFlatBifunctor.KFlat` read at the tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`: the two predicates are definitionally equal, since the
  total
tensor complex `Stacks.SheafOfModules.Tensor.tensorComplex` is by definition the bifunctor-relative
  total
complex of that bifunctor. -/
theorem kFlat_iff_kFlatBifunctor
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    KFlat R K ↔ CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      :=
  Iff.rfl

end Stacks.SheafOfModules.KFlat

end
