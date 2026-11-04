module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictScalars
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsLocallyQuasicoherent

/-!
# `Ω^i_{X/S}` restricted to `T`, over the restriction of `𝒪_{X/S}`

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of the big
crystalline category `CRIS(X/S)`.  The coefficient sheaf of [Stacks, Tag 07LF] is
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, and the two factors of its restriction to `T` are quasi-coherent over
two *different* spellings of the structure sheaf of `T`:

* the restriction `F_T` is quasi-coherent over
  `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf`, the restriction of
  `𝒪_{X/S}` to the opens of `T`, which is what
  `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` gives;
* the restriction of `Ω^i_{X/S}` is quasi-coherent over `𝒪_T`, which is what
  `...crysDifferentialForms_isLocallyQuasiCoherent` gives, through
  `...restrictedCrysDifferentialFormsSheaf`.

To run [Stacks, Tag 05NA] (sheafifying a presheaf tensor product gives the tensor product of the
sheafifications) and [Stacks, Tag 03L6] (a tensor product of quasi-coherent modules is
quasi-coherent) on the restricted coefficient sheaf, both factors must sit over one sheaf of
rings.  This module moves the `Ω^i_{X/S}` factor onto the side `F_T` is on.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysDifferentialFormsRestriction` — the restriction of
  `Ω^i_{X/S}` to the ambient scheme of an object, as a presheaf of modules over the restriction of
  `𝒪_{X/S}` to the opens of `T` rather than over `𝒪_T`.  This is
  `...Thickening.moduleRestriction` at `Ω^i_{X/S}`, which is the spelling in which
  `...IsLocallyQuasiCoherent` states its conclusion for `F`.

## Main results

* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_crysDifferentialFormsRestriction`
  — **the sheaf of modules over the restriction of `𝒪_{X/S}` to `T` associated with the
  restriction of `Ω^i_{X/S}` is quasi-coherent**, for every `i` and every object of `CRIS(X/S)`,
  with no hypothesis.  Together with
  `...isQuasicoherentOnSite_moduleRestrictionSheaf` for `F` this places both factors of the
  coefficient sheaf of [Stacks, Tag 07LF] over one and the same sheaf of rings.

## What is and is not proved

The statement above is proved in full, for every `i : ℕ` and every object of `CRIS(X/S)`, **with
no hypothesis carried at all** — no affineness, no finiteness, no local freeness, nothing about
the crystal condition, and nothing about `F`.  It is the exterior-power case of
[Stacks, Tag 07KM] clause (1) read at the *other* of the two spellings of `T`'s structure sheaf,
and it is deduced from the `𝒪_T` spelling, `...crysDifferentialForms_isLocallyQuasiCoherent`, by
the general comparison
`PresheafOfModules.sheafifyRestrictScalarsCompIso`: sheafification of presheaves of modules
commutes with restriction of scalars along an isomorphism of presheaves of rings.

**No tag attribute is placed.**  [Stacks, Tag 07KM] clause (1) is already carried by
`Crystalline.GlobalCrystallineSituation.crysDifferentials_isLocallyQuasiCoherent`, and this is a
restatement of an existing result at a different spelling, not a new clause.

### What remains for [Stacks, Tag 07LF]

With this module all three *ingredients* that input (1) of [Stacks, Tag 07LF] was missing are in
the library: the other two are
`...crysDifferentialForms_isLocallyQuasiCoherent` (clause (1) of [Stacks, Tag 07KM] for every
exterior power) and
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`
([Stacks, Tag 03L6], quasi-coherence of a tensor product, for an arbitrary ringed site).
Assembling them is a separate matter, and is **not** done here: this module does not discharge the
hypothesis `h` of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology`, and therefore
does not make `...SmallSite.Vanishing07JJ` unconditional for the tensor sheaf.  What is still
owed, with the library declarations each step would use, is:

1. that restriction to `T` commutes with the objectwise tensor product of presheaves of modules
   over the restricted structure sheaf.  The library has exactly this, by `rfl`, for the
   mixed-universe objectwise tensor product `Stacks.tensorObj`:
   `Stacks.DenseSubsiteModules.presheafRestrict_tensorObj` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteTensor.lean`.  What is owed is the
   same statement for Mathlib's monoidal `PresheafOfModules.Monoidal.tensorObj`, which is the
   tensor product `...SmallSite.tensorDifferentialForms` is defined with, and the bridge between
   the two objectwise tensor products;
2. [Stacks, Tag 05NA] at the restricted spelling:
   `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso` applied with
   `𝒪 := Thickening.restriction (structureSheaf S) A` and `h𝒪` its sheaf condition;
3. the comparison of the tensor sheaf of [Stacks, Tag 05NA], which is
   `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, with the tensor sheaf
   [Stacks, Tag 03L6] is stated for, which is
   `PresheafOfModules.tensorSheafBifunctor` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationTensor.lean`: the two are built
   from different objectwise tensor products, the second allowing the two factors to live in
   different module universes;
4. the passage from the module universe `u` of [Stacks, Tag 01X9],
   `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover`, to the coefficient
   universe `u + 1` of `...SmallSite.tensorDifferentialFormsPresheaf`, for which
   `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_uliftFunctor` and its surjective
   sibling, together with
   `Stacks.CategoryTheory.CechComplex.isZero_homology_mapCoeff_iff`, are the inputs —
   the pattern is carried out for `...SmallSite.abelianSheaf` at
   `...SmallSite.isZero_cechCohomology_abelianSheaf_of_isStandardOpenCover`.

None of these four is proved here.

### Notes elsewhere that this invalidates

The docstring of
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf_of_isZero_cechHomology` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SheafifySections.lean` said of the two
factors of the coefficient sheaf that they are quasi-coherent "the restriction `F_T` by hypothesis
(1) of [Stacks, Tag 07JN] and the associated sheaf of the restriction of `Ω^i_{X/S}` by the
exterior-power form of [Stacks, Tag 07KM] part (1), which the library does not have for `i ≠ 1`".
The second half of that is false, since
`...crysDifferentialForms_isLocallyQuasiCoherent` is proved, and the sentence is false in a
second way as well: the quasi-coherence of the two factors is available over one and the same
sheaf of rings, which is what the sentence needs it for.

The "What is and is not proved" note of the same file lists three pieces still owed for input (1)
of [Stacks, Tag 07LF]; the first of them, the exterior-power form of [Stacks, Tag 07KM] part (1),
is closed, and the change of scalars that it needed in order to be usable is this module.  The
remaining two are the second and third items of that list, refined into the four steps above.

## Implementation notes

`Crystalline.GlobalCrystallineSituation.crysDifferentialFormsRestriction` writes
`crysDifferentialForms S i` at the type `PresheafOfModules (crisRing S)` by an ascription.  The
two presheaves of rings `crisRing S` and
`Crystalline.GlobalCrystallineSituation.structureRingCatPresheaf S` are definitionally equal —
`Crystalline.GlobalCrystallineSituation.structureSheaf` and
`Crystalline.GlobalCrystallineSituation.structureRingPresheaf` have the same body — but they are
different constants, so the identification is not visible to unification at the transparency
instance search uses.  Paying it once in a definition, and never inside a proof, is the practice
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ExteriorPowerComparisonSurjectivity.lean`
record for this pair; the ascription here is the same one
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` uses on `M.val`.

The comparison of sheaves of rings handed to
`PresheafOfModules.sheafifyRestrictScalarsCompIso` is built from
`Crystalline.GlobalCrystallineSituation.restrictOpenRingHomInv`, not from
`...Thickening.ringRestrictionSheafStructureIso`.  The two are the same isomorphism, but proving
that would mean identifying `Crystalline.openTopResInv` with
`AlgebraicGeometry.Scheme.Opens.topIso`, and nothing here needs it: the quasi-coherence of a
restriction of scalars along *any* isomorphism
of sheaves of rings is `Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso`, and
the pointwise round-trip identity that the comparison lemma asks for is
`...restrictOpenRingHom_app_inv_app`, already proved for `restrictOpenRingHomInv`.

## References

* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-- **The restriction of `Ω^i_{X/S}` to the ambient scheme of an object, over the restriction of
`𝒪_{X/S}`.**  Its sections over an open `W` of `T` are the sections of `Ω^i_{X/S}` over the
restriction of `(U, T, δ)` to `W`, viewed as a module over the ring of global sections of the open
subscheme `W`.  This is the spelling of the restriction in which
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` states its conclusion, and it
differs from `...restrictedCrysDifferentialForms` only by the change of scalars to `𝒪_T`. -/
def crysDifferentialFormsRestriction (A : Thickening S) (i : ℕ) :
    PresheafOfModules.{u} A.ringRestrictionSheaf.obj :=
  Thickening.moduleRestriction
    (crysDifferentialForms S i : PresheafOfModules.{u} (crisRing S)) A

/-- `...restrictedCrysDifferentialForms` is the change of scalars of
`crysDifferentialFormsRestriction` from the restriction of `𝒪_{X/S}` to `𝒪_T`: the restriction of
a presheaf of modules along a morphism of presheaves of rings over a functor is the restriction of
scalars of the restriction along the functor alone. -/
theorem restrictScalars_crysDifferentialFormsRestriction (A : Thickening S) (i : ℕ) :
    (PresheafOfModules.restrictScalars (Thickening.restrictOpenRingHom A)).obj
        (crysDifferentialFormsRestriction S A i) =
      restrictedCrysDifferentialForms S A i :=
  rfl

/-- **The sheaf of modules over the restriction of `𝒪_{X/S}` to `T` associated with the
restriction of `Ω^i_{X/S}` is quasi-coherent**, for every `i : ℕ` and every object `(U, T, δ)` of
`CRIS(X/S)`, with no hypothesis.

This is `...crysDifferentialForms_isLocallyQuasiCoherent` — clause (1) of [Stacks, Tag 07KM] for
`Ω^i_{X/S}` — carried across the change of scalars from `𝒪_T` to the restriction of `𝒪_{X/S}`
*before* sheafification rather than after.  The restriction of `Ω^i_{X/S}` is only a presheaf of
modules, so the two sides are two different sheafifications, and the identification is
`PresheafOfModules.sheafifyRestrictScalarsCompIso`: sheafification commutes with restriction of
scalars along an isomorphism of presheaves of rings.

Its point is that `Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` gives the
quasi-coherence of a restriction `F_T` over this sheaf of rings and not over `𝒪_T`, so this is the
form in which the two factors of the coefficient sheaf of [Stacks, Tag 07LF] can be handed
together to [Stacks, Tag 05NA] and [Stacks, Tag 03L6]. -/
theorem isQuasicoherentOnSite_crysDifferentialFormsRestriction (A : Thickening S) (i : ℕ) :
    ((PresheafOfModules.sheafification (𝟙 A.ringRestrictionSheaf.obj)).obj
      (crysDifferentialFormsRestriction S A i)).IsQuasicoherentOnSite := by
  let e : A.ringRestrictionSheaf ≅ A.thickening.target.scheme.ringCatSheaf :=
    { hom := ⟨restrictOpenRingHomInv S A⟩
      inv := ⟨Thickening.restrictOpenRingHom A⟩
      hom_inv_id := Sheaf.hom_ext (IsIso.inv_hom_id (Thickening.restrictOpenRingHom A))
      inv_hom_id := Sheaf.hom_ext (IsIso.hom_inv_id (Thickening.restrictOpenRingHom A)) }
  have : IsIso e.hom := Iso.isIso_hom e
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (PresheafOfModules.sheafifyRestrictScalarsCompIso (𝟙 A.ringRestrictionSheaf.obj)
      (𝟙 A.thickening.target.scheme.ringCatSheaf.obj) e.hom (restrictOpenRingHomInv S A)
      (Thickening.restrictOpenRingHom A)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
        (crysDifferentialFormsRestriction S A i).presheaf)
      (fun _ _ ↦ rfl) (restrictOpenRingHom_app_inv_app S A))
    (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso e.hom
      (restrictedCrysDifferentialFormsSheaf S A i)
      (restrictedCrysDifferentialFormsSheaf_isQuasicoherentOnSite S A i))

end Crystalline.GlobalCrystallineSituation

end
