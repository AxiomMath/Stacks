module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic

/-!
# Vanishing of the higher direct images at a point with finite fibre

Let `f : X ⟶ Y` be a proper morphism of schemes and let `y : Y` be a point whose set-theoretic
fibre `f ⁻¹' {y}` is finite. Then for every quasi-coherent `𝒪_X`-module `F` and every `p > 0` the
stalk at `y` of the higher direct image `R ᵖ f_* F` vanishes. This is **[Stacks, Tag 02OE]**,
whose own hypotheses are that `Y` be locally Noetherian and `F` be coherent; neither is used, so
both forms are stated and the tagged one is the source's.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.FormalFunctions.isZero_stalk_higherDirectImage_of_finite_preimage`: the vanishing for a
  proper morphism, a point with finite fibre and a *quasi-coherent* module, with **no hypothesis
  on `Y`**.
* `Stacks.FormalFunctions.isZero_stalk_higherDirectImage_of_finite_fibre`: **[Stacks, Tag 02OE]**
  itself, with `Y` locally Noetherian and `F` coherent.
* `Stacks.FormalFunctions.exists_isFinite_morphismRestrict_of_finite_fibre`: **[Stacks, Tag
  02OH]**, that a proper morphism with finite fibre over `y` is finite over a neighbourhood of
  `y` — the geometric input of Tag 02OE, recorded here under its own tag.

## Implementation notes

**The route taken, and why it is not the source's.** The source deduces Tag 02OE from the theorem
on formal functions [Stacks, Tag 02OD]: the infinitesimal neighbourhoods `X_n` of the fibre have
`f ⁻¹' {y}` as underlying space, which is finite and discrete, so `H ᵖ (X_n, F_n) = 0` for
`p > 0`; Tag 02OD identifies the `𝔪_y`-adic completion of `(R ᵖ f_* F)_y` with `lim_n H ᵖ (X_n,
F_n)`, hence that completion vanishes, and Nakayama ([Stacks, Tag 00DV]) finishes because
`(R ᵖ f_* F)_y` is a finite `𝒪_{Y,y}`-module by [Stacks, Tag 02O5]. **Both of those inputs are
missing from this repository**: the conclusion of Tag 02OD is explicitly not stated in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalNeighbourhood.lean` (only the
geometric system `X_n` is built there), and Tag 02O5 for a general proper morphism is reduced to
Chow's lemma and never discharged — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FiniteDirectImageCoherent/Basic.lean`.

What is used instead is Zariski's main theorem. A proper morphism with finite fibre over `y` is
finite over an open neighbourhood `V` of `y`, which is [Stacks, Tag 02UP]
(`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`, in Mathlib,
via [Stacks, Tag 02LS]); the higher direct images along a finite morphism vanish in positive
degrees, which is [Stacks, Tag 01Y6]
(`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite`, from
[Stacks, Tag 01XC]); higher direct images commute with restriction to an open of the base, which
is [Stacks, Tag 01E5]
(`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`); and a stalk is
computed on any neighbourhood of the point, which is
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`. Along this route neither local
Noetherianness of `Y` nor coherence of `F` is needed — only quasi-coherence, and that only to
invoke Tag 01XC.

**Degrees are integers.** `R ᵖ f_*` is `(Scheme.Modules.pushforward f).rightDerivedPlus p` with
`p : ℤ`, so "for all `p > 0`" is quantified over the positive integers. Tag 01E5 is available in
this library only in a degree presented as a natural number
(`higherDirectImageRestrictObjIso` takes `p : ℕ`), so the integer degree is replaced by
`p.toNat` at the start of the proof.

**The shape of the conclusion.** Vanishing of the stalk is the categorical predicate
`CategoryTheory.Limits.IsZero` on `TopCat.Presheaf.stalk` of the underlying `AddCommGrpCat`-valued
presheaf of the sheaf of modules, which is the object `restrictStalkNatIso` compares; there is no
`𝒪_{Y,y}`-module-valued stalk of a sheaf of modules in the library to state it on.

## References

* [Stacks Project, Tag 02OE](https://stacks.math.columbia.edu/tag/02OE)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 02UP](https://stacks.math.columbia.edu/tag/02UP)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.FormalFunctions

/-- **[Stacks, Tag 02OE] with neither of its hypotheses on `Y` or on `F`.** Let `f : X ⟶ Y` be
proper and let `y : Y` have finite set-theoretic fibre. Then for every quasi-coherent
`𝒪_X`-module `F` and every `p > 0` the stalk of `R ᵖ f_* F` at `y` is zero.

`f` is finite over an open neighbourhood `V` of `y` by [Stacks, Tag 02UP]; the higher direct
images along `f ∣_ V` of the restriction of `F` vanish by [Stacks, Tag 01Y6]; that higher direct
image is the restriction to `V` of `R ᵖ f_* F` by [Stacks, Tag 01E5]; and the stalk at `y` of a
sheaf of modules on `Y` is the stalk of its restriction to `V` at the corresponding point of `V`.

No local Noetherianness of `Y` and no coherence of `F` is used; see the implementation notes of
this file for the comparison with the source's proof. -/
theorem isZero_stalk_higherDirectImage_of_finite_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (y : Y) (hfin : (f ⁻¹' {y}).Finite) (F : X.Modules) [F.IsQuasicoherent]
    (p : ℤ) (hp : 0 < p) :
    IsZero
      ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp.le).symm⟩
  obtain ⟨V, hyV, hVfin⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hfin
  have := hVfin
  -- `R ⁿ f_* F` restricted to `V` is `R ⁿ (f ∣_ V)_*` of the restriction of `F`, and that
  -- vanishes because `f ∣_ V` is finite.
  have hres : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)) :=
    IsZero.of_iso
      (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite
        (f ∣_ V) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F) (n : ℤ) hp)
      (ProjectiveCoherentImage.higherDirectImageRestrictObjIso f V F n).symm
  -- Taking the stalk at `y`, viewed as a point of `V`, kills nothing.
  obtain ⟨x, hx⟩ : ∃ x : V.toScheme, V.ι x = y := ⟨⟨y, hyV⟩, rfl⟩
  rw [← hx]
  exact IsZero.of_iso
    (Functor.map_isZero
      (Scheme.Modules.toPresheaf V.toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hres)
    ((Scheme.Modules.restrictStalkNatIso V.ι x).app
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F)).symm

/-- **Stacks Project, Tag 02OE.** Let `f : X ⟶ Y` be a morphism of schemes and let `y : Y`.
Assume `Y` is locally Noetherian, `f` is proper, and the fibre `f ⁻¹' {y}` is finite. Then for
every coherent `𝒪_X`-module `F` and every `p > 0` the stalk `(R ᵖ f_* F)_y` vanishes.

This is `isZero_stalk_higherDirectImage_of_finite_preimage`, which needs neither hypothesis;
coherence of `F` gives quasi-coherence through [Stacks, Tag 01BW]
(`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`), for which
no hypothesis on `Y` is needed either. Both hypotheses are kept here because the tag states
them. -/
@[stacks 02OE]
theorem isZero_stalk_higherDirectImage_of_finite_fibre {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [IsProper f] (y : Y) (hfin : (f ⁻¹' {y}).Finite) (F : X.Modules)
    [F.IsCoherent] (p : ℤ) (hp : 0 < p) :
    IsZero
      ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) :=
  have := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  isZero_stalk_higherDirectImage_of_finite_preimage f y hfin F p hp

/-- **Stacks Project, Tag 02OH.** Let `f : X ⟶ Y` be a morphism of schemes and let `y : Y`.
Assume `Y` is locally Noetherian, `f` is proper, and the fibre `f ⁻¹' {y}` is finite. Then `y` has
an open neighbourhood `V` over which `f` is finite, that is, `f ∣_ V : f ⁻¹ᵁ V ⟶ V` is finite.

This is Zariski's main theorem in the form of [Stacks, Tag 02UP]
(`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`), which needs
no hypothesis on `Y`; local Noetherianness is kept here because the tag states it. The source
instead deduces the lemma from Tag 02OG, finiteness being equivalent to properness with finite
fibres over a locally Noetherian base; that route is unavailable here, and it would in any case be
circular, since Tag 02OG rests on Tag 02OE above. -/
@[stacks 02OH, ega "III 4.8.11" "ordinary schemes"]
theorem exists_isFinite_morphismRestrict_of_finite_fibre {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [IsProper f] (y : Y) (hfin : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) :=
  exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y hfin

end Stacks.FormalFunctions

end
