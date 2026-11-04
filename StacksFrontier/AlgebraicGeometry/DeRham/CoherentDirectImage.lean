module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.NoetherianSource
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the derived direct image of the relative de Rham complex

For a morphism of schemes `p : X ⟶ S` which is locally of finite type over a locally Noetherian
base, each sheaf `Ω^n_{X/S}` of relative differential `n`-forms is a coherent `𝒪_X`-module. If
moreover every higher direct image `R^b p_* Ω^a_{X/S}` is coherent, then so is every cohomology
sheaf of `Rp_*Ω^•_{X/S}`, which is to say that `Rp_*Ω^•_{X/S}` is an object of `D_Coh(𝒪_S)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentials` and
  `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentialForms`: over a locally Noetherian
  base the sheaves `Ω_{X/S}` and `Ω^n_{X/S}` of a morphism locally of finite type are coherent.
In the namespace `AlgebraicGeometry.DeRhamCoherentDirectImage`:

* `isCoherent_relativePushforward_higher`: coherence of `R^q p_* M` is coherence of the higher
  direct image computed in `Mod(p^{-1}𝒪_S)`.
* `isCoherent_homology_derivedDeRhamDirectImage_of_forall` and
  `derivedCategoryB_derivedDeRhamDirectImage_of_forall`: coherence of every `R^b p_* Ω^a_{X/S}`
  gives `Rp_*Ω^•_{X/S} ∈ D_Coh(𝒪_S)`, degreewise and in membership form.
* `isCoherent_homology_derivedDeRhamDirectImage_of_isProper` and
  `derivedCategoryB_derivedDeRhamDirectImage_of_isProper`: **[Stacks, Tag 0FLY]** for a proper
  morphism, unconditionally, degreewise and in membership form.
* `isCoherent_homology_derivedDeRhamDirectImage_of_isFinite`: the same conclusion for a finite
  morphism, by the elementary vanishing of the higher direct images along a finite morphism
  rather than by [Stacks, Tag 02O5].

## Implementation notes

The argument is the one of [Stacks, Tag 0FLX], which is proved in
`StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean`, with coherence in place of
quasi-coherence: a Cartan--Eilenberg resolution of the de Rham complex gives a diagonally finite
double complex whose columnwise cohomology is `R^b p_* Ω^a_{X/S}` and whose total complex
computes `Rp_*Ω^•_{X/S}`, and coherent sheaves of modules form a weak Serre subcategory, so
`Stacks.DeRhamDirectImage.weakSerre_homology_total` transfers the property from the columns to
the total complex. The weak Serre instance for the coherence predicate that `F.IsCoherent` means
for `F : X.Modules` is `SheafOfModules.coherentModules_isWeakSerreClass`.

What replaces [Stacks, Tag 01XJ] in the source's proof is [Stacks, Tag 02O5], coherence of the
higher direct images along a proper morphism. That tag is proved in this library, with no
hypothesis: `StacksFrontier/AlgebraicGeometry/ProperCoherentImage/Basic.lean` reduces it to its
affine-base case `HigherDirectImageIsCoherentOverAffineBase` and proves the two equivalent, and
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` of
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean` discharges that affine
case outright. So the proper case below takes no hypothesis of its own: it instantiates
`AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_isProper` at that
witness, and `@[stacks 0FLY]` is attached with no suffix.
`derivedCategoryB_derivedDeRhamDirectImage_of_isProper` is the tag's own phrasing of the
conclusion — `Rp_*Ω^•_{X/S}` is an object of `D_Coh(𝒪_S)` — and carries the attribute, while its
degreewise sibling states the same content one degree at a time and does not.

The finite case is kept because it needs none of that machinery: [Stacks, Tag 02O5] for a finite
morphism is already available as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_of_isFinite`.
It is untagged, following the precedent of that declaration, which declines `@[stacks 02O5]`
because `IsFinite` is strictly stronger than the `IsProper` the tag asserts.

Coherence of `Ω^n_{X/S}` is unconditional and is the first step of the source's proof. The
source cites [Stacks, Tag 01V2] for it; in this library that tag gives finiteness of type of
`Ω_{X/S}`, and coherence is obtained from it by (2) ⇒ (1) of [Stacks, Tag 01XZ] on the source,
which is locally Noetherian by [Stacks, Tag 01T6].

The namespace deliberately avoids a `Stacks.` prefix. Inside one, `SheafOfModules.IsCoherent`
resolves to `Stacks.SheafOfModules.IsCoherent`, a different constant from the one `F.IsCoherent`
means for `F : X.Modules`, and the object property carrying the weak Serre instance used here
would silently become the other one. The three local instances on `Modules` are restated from
`StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean`, where they are file-local,
instance search not crossing the `Modules` abbreviation on its own.

The raised priority of `CategoryTheory.HasDerivedCategory.standard` is restated from there too,
and it is load-bearing rather than cosmetic. Two models of the derived category are in scope
here and they are competing instances at different universe levels. Everything this file has to
join is baked at the standard one: `Stacks.DeRhamDirectImage.derivedDeRhamDirectImage` and
`relativePushforwardHigherIso`, which carry it in their types, and the coherence of the higher
direct images supplied by
`AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_isProper` and
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_of_isFinite`.
Without the priority raised, the other model is selected for `S.Modules` and none of those
types match the goals. For the same reason the hypothesis of
`isCoherent_homology_derivedDeRhamDirectImage_of_forall` is phrased with `relativePushforward`
and a restriction of scalars rather than directly with `Scheme.Modules.pushforward`: that is the
spelling `relativePushforwardHigherIso` pins, so the hypothesis cannot drift to the other model,
and `isCoherent_relativePushforward_higher` is the one place the two spellings are crossed.

## References

* [Stacks Project, Tag 0FLY](https://stacks.math.columbia.edu/tag/0FLY)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The sheaf of relative differentials of a morphism locally of finite type over a locally
Noetherian base is coherent.** The source is locally Noetherian by [Stacks, Tag 01T6], and there
a quasi-coherent module of finite type is coherent by (2) ⇒ (1) of [Stacks, Tag 01XZ]; finiteness
of type is [Stacks, Tag 01V2]. -/
@[ega "IV 16.3.9" "special case", ega "IV 17.4.1.2" "special case"]
theorem isCoherent_relativeDifferentials [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    (relativeDifferentials f).IsCoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **The sheaf `Ω^n_{X/S}` of relative differential `n`-forms of a morphism locally of finite
type over a locally Noetherian base is coherent**, in every degree. It is the `n`-th exterior
power of the coherent module `Ω_{X/S}`, and on a locally Noetherian scheme the exterior powers of
a coherent module are coherent. -/
@[ega "IV 17.4.1.2" "special case"]
theorem isCoherent_relativeDifferentialForms [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (n : ℕ) : (relativeDifferentialForms f (n : ℤ)).IsCoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (relativeDifferentials f).IsCoherent := isCoherent_relativeDifferentials f
  Scheme.Modules.isCoherent_exteriorPower (relativeDifferentials f) n

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.DeRhamCoherentDirectImage

open Stacks.DeRhamDirectImage

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Sheaves of modules on a ringed space form a (Grothendieck) abelian category; instance search
does not cross the abbreviation, so the instances restated at these binders in
`StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean` are put back in scope. -/
attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules
  Stacks.DeRhamDirectImage.isGrothendieckAbelian_modules

/-- **The higher direct images of a coherent `𝒪_X`-module, taken in `Mod(f^{-1}𝒪_S)`, are
coherent.** By `Stacks.DeRhamDirectImage.relativePushforwardHigherIso` they are the usual higher
direct images, whose coherence is the hypothesis. -/
theorem isCoherent_relativePushforward_higher (M : X.Modules) (q : ℤ)
    (h : (((Scheme.Modules.pushforward f).rightDerivedPlus q).obj M).IsCoherent) :
    (((relativePushforward f).rightDerivedPlus q).obj
      ((pushforward (toInverseImageBase f)).obj M)).IsCoherent :=
  have := h
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    (relativePushforwardHigherIso f M q)

/-- **`Rp_*Ω^•_{X/S}` has coherent cohomology as soon as every `R^b p_* Ω^a_{X/S}` is
coherent.** The de Rham complex is bounded below, so a Cartan--Eilenberg resolution gives a
diagonally finite double complex whose columnwise cohomology is `R^b p_* Ω^a_{X/S}` and whose
total complex computes the derived direct image; coherent sheaves of modules form a weak Serre
subcategory, so the property passes from the columns to the total complex. -/
theorem isCoherent_homology_derivedDeRhamDirectImage_of_forall [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ (a : ℕ) (b : ℤ),
      (((relativePushforward f).rightDerivedPlus b).obj
        ((pushforward (toInverseImageBase f)).obj
          (Scheme.Hom.relativeDifferentialForms f (a : ℤ)))).IsCoherent)
    (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (derivedDeRhamDirectImage f)).IsCoherent := by
  let F := relativePushforward f
  let K := deRhamCochainComplex f
  obtain ⟨I, hI⟩ := CochainComplex.exists_cartanEilenbergResolution K 0
  have := hI
  let L := ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I.bicomplex
  have hp (a : ℤ) (ha : a < 0) : IsZero (L.X a) :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE I.bicomplex 0 a ha)
  have hq (a b : ℤ) (hb : b < 0) : IsZero ((L.X a).X b) :=
    F.map_isZero (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X a) 0 b hb)
  have hfinite := StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L 0 hq hp
  have : HomologicalComplex₂.HasTotal L (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ hfinite
  have hSS := I.exists_homologyIso_rightDerivedPlus F ⟨0, inferInstance⟩
  -- The columns `L.X a` live in `Modules S.toRingedSpace`, that is over
  -- `Stacks.SheafOfModules.Tensor.ringSheaf S.toRingedSpace.sheaf`, where the abelian instance and
  -- `Stacks.SheafOfModules.coherentModules_isWeakSerreClass` are reachable.
  -- `AlgebraicGeometry.Scheme.ringCatSheaf` is the same sheaf of rings only after unfolding that
  -- definition, which instance search will not do, so the property is named at the spelling the
  -- columns are stated at.
  let P : ObjectProperty (_root_.SheafOfModules.{u} (ringCatSheaf S.toRingedSpace)) :=
    fun M => M.IsCoherent
  have hcol (a b : ℤ) : P ((L.X a).homology b) := by
    by_cases ha : 0 ≤ a
    · obtain ⟨e, -⟩ := hSS.1 b
      refine P.prop_of_iso (e a).symm ?_
      lift a to ℕ using ha
      refine P.prop_of_iso ((F.rightDerivedPlus b).mapIso
        ((show CochainComplex (Modules (inverseImageBase f)) ℕ from
            Scheme.Hom.deRhamComplex f).extendXIso
          ComplexShape.embeddingUpNat (i := a) rfl)).symm ?_
      rw [Scheme.Hom.deRhamComplex_X]
      exact h a b
    · exact P.prop_of_isZero
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) b).map_isZero
          (hp a (lt_of_not_ge ha)))
  obtain ⟨e⟩ := hSS.2.2 i
  exact P.prop_of_iso e (weakSerre_homology_total L hfinite P hcol i)

/-- **`Rp_*Ω^•_{X/S}` is an object of `D_Coh(𝒪_S)` as soon as every `R^b p_* Ω^a_{X/S}` is
coherent**, in the membership form: the object property on `D(𝒪_S)` cutting out the complexes
with coherent cohomology holds of it. Since the relative de Rham complex is bounded below the
derived direct image is read in `D⁺(𝒪_S)` and compared with `D(𝒪_S)` along the inclusion, under
which the cohomology functors agree. -/
theorem derivedCategoryB_derivedDeRhamDirectImage_of_forall [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ (a : ℕ) (b : ℤ),
      (((relativePushforward f).rightDerivedPlus b).obj
        ((pushforward (toInverseImageBase f)).obj
          (Scheme.Hom.relativeDifferentialForms f (a : ℤ)))).IsCoherent) :
    DerivedCategoryB.derivedCategoryB
      (fun M => M.IsCoherent) (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) :=
  fun i => isCoherent_homology_derivedDeRhamDirectImage_of_forall f h i

/-- If the higher direct images of each coherent `Ω^a_{X/S}` are coherent, so is every cohomology
sheaf of `Rp_*Ω^•_{X/S}`. -/
private theorem isCoherent_homology_derivedDeRhamDirectImage_of_forall_isCoherent
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ (a : ℕ) (b : ℤ), (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).IsCoherent →
      (((Scheme.Modules.pushforward f).rightDerivedPlus b).obj
        (Scheme.Hom.relativeDifferentialForms f (a : ℤ))).IsCoherent)
    (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (derivedDeRhamDirectImage f)).IsCoherent :=
  isCoherent_homology_derivedDeRhamDirectImage_of_forall f (fun a b =>
    isCoherent_relativePushforward_higher f _ b
      (h a b (Scheme.Hom.isCoherent_relativeDifferentialForms f a))) i

/-- **[Stacks, Tag 0FLY] degreewise.** For a proper morphism `p : X ⟶ S` of schemes with `S`
locally Noetherian, every cohomology sheaf of `Rp_*Ω^•_{X/S}` is coherent. The sheaves
`Ω^a_{X/S}` are coherent because a proper morphism is locally of finite type, and coherence of
the `R^b p_* Ω^a_{X/S}` is [Stacks, Tag 02O5], supplied with no hypothesis by
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`.

The attribute sits on `derivedCategoryB_derivedDeRhamDirectImage_of_isProper`, which states the
same content in the tag's own membership phrasing. -/
theorem isCoherent_homology_derivedDeRhamDirectImage_of_isProper
    [IsLocallyNoetherian S] [IsProper f] (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (derivedDeRhamDirectImage f)).IsCoherent := by
  refine isCoherent_homology_derivedDeRhamDirectImage_of_forall_isCoherent f
    (fun a b _ => ?_) i
  rcases lt_or_ge b 0 with hb | hb
  · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero (R := S.ringCatSheaf)
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f _ b hb)
  · lift b to ℕ using hb
    exact ProperCoherentImage.isCoherent_higherDirectImage_of_isProper
      ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase f
      (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) b

/-- **[Stacks, Tag 0FLY].** For a proper morphism `p : X ⟶ S` with `S` locally Noetherian,
`Rp_*Ω^•_{X/S}` is an object of `D_Coh(𝒪_S)`.

Coherence of the higher direct images `R^b p_* Ω^a_{X/S}` is [Stacks, Tag 02O5]; this library
proves it with no hypothesis, in the affine-base form
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase` that
`StacksFrontier/AlgebraicGeometry/ProperCoherentImage/Basic.lean` shows equivalent to it. -/
@[stacks 0FLY]
theorem derivedCategoryB_derivedDeRhamDirectImage_of_isProper
    [IsLocallyNoetherian S] [IsProper f] :
    DerivedCategoryB.derivedCategoryB
      (fun M => M.IsCoherent) (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) :=
  fun i => isCoherent_homology_derivedDeRhamDirectImage_of_isProper f i

/-- **[Stacks, Tag 0FLY] for a finite morphism**, unconditionally: for a finite morphism
`p : X ⟶ S` with `S` locally Noetherian every cohomology sheaf of `Rp_*Ω^•_{X/S}` is coherent.
The higher direct images along a finite morphism vanish above degree `0` and are the direct
image in degree `0`, which is coherent by [Stacks, Tag 01Y6].

A finite morphism is proper, so this is the conclusion of [Stacks, Tag 0FLY] under the strictly
stronger hypothesis `IsFinite p` in place of `IsProper p`. Its label is **not** attached, as it
is not attached to
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_of_isFinite`
for the same reason. -/
theorem isCoherent_homology_derivedDeRhamDirectImage_of_isFinite [IsLocallyNoetherian S]
    [IsFinite f] (i : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor S.Modules i).obj
      (derivedDeRhamDirectImage f)).IsCoherent :=
  isCoherent_homology_derivedDeRhamDirectImage_of_forall_isCoherent f (fun a b _ =>
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_higherDirectImage_of_isFinite
      f (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) b) i

/-- **[Stacks, Tag 0FLY] for a finite morphism, in the membership form**, unconditionally:
`Rp_*Ω^•_{X/S}` is an object of `D_Coh(𝒪_S)`. Its label is **not** attached, for the reason
given on `isCoherent_homology_derivedDeRhamDirectImage_of_isFinite`. -/
theorem derivedCategoryB_derivedDeRhamDirectImage_of_isFinite [IsLocallyNoetherian S]
    [IsFinite f] :
    DerivedCategoryB.derivedCategoryB
      (fun M => M.IsCoherent) (DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage f)) :=
  fun i => isCoherent_homology_derivedDeRhamDirectImage_of_isFinite f i

end AlgebraicGeometry.DeRhamCoherentDirectImage

end
