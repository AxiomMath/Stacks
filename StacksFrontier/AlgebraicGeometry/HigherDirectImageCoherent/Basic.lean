module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic

/-!
# Coherence transport, and the degree-zero higher direct image

[Stacks, Tag 02O5] asserts that for a proper morphism `f : X ⟶ S` to a locally Noetherian
scheme and a coherent `𝒪_X`-module `F`, every higher direct image `R ⁱ f_* F` is coherent.
That statement is **not** proved here; see the implementation notes for exactly what blocks it.

What this file provides is the transport layer that the source's proof (and every other
argument about `SheafOfModules.IsCoherent`) needs before it can begin, together with the
degree-zero and negative-degree reductions of the higher direct image:

* coherence and finite type are invariant under isomorphism of sheaves of modules;
* a free sheaf of modules on a finite index type is of finite type;
* a zero sheaf of modules is coherent;
* `R ⁱ f_* F` is coherent for `i < 0`, with no hypothesis on `f` or `F` whatsoever;
* `R ⁰ f_* F` is coherent if and only if `f_* F` is, again with no hypothesis on `f`.

The last item reduces the `i = 0` case of [Stacks, Tag 02O5] to the statement about the
ordinary direct image, so that only the degrees `i > 0` carry genuinely cohomological content.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isFiniteType_of_iso`: finite type is
  invariant under isomorphism, on an arbitrary site.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isFiniteType_free`: `free I` is of
  finite type for `I` finite.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isZero_over_of_isZero`: restriction to
  an open preserves zero sheaves of modules.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_of_iso`: coherence is
  invariant under isomorphism.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_of_isZero`: a zero sheaf of
  modules is coherent.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_of_neg`:
  `R ⁱ f_* F` is coherent for `i < 0`.
* `Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_higherDirectImage_zero_iff`:
  `R ⁰ f_* F` is coherent if and only if `f_* F` is.

## Implementation notes

`SheafOfModules.IsCoherent` is, on this branch, declared only for `M : SheafOfModules.{0} R`
with `R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}` and `X : Type`. Consequently every
statement here that mentions coherence is confined to `Scheme.{0}`, and the source's statement
for `Scheme.{u}` cannot even be elaborated: `F.IsCoherent` for `F : X.Modules` with
`X : Scheme.{u}` is an application type mismatch, `X.Modules` having sort `Type (u + 1)` where
`SheafOfModules ?R` of sort `Type 1` is expected. This is a narrowing of the predicate, not of
the mathematics; the universe restriction is recorded explicitly in each statement below rather
than hidden behind a smallness hypothesis.

Beyond that, the mathematical content of [Stacks, Tag 02O5] is still out of reach, but the
inventory of what is missing is narrower than when this file was written. Closure of coherence
under kernels, cokernels and extensions is
`Stacks.SheafOfModules.coherentModules_isWeakSerreClass` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentWeakSerre.lean`, with locality of coherence
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean`; the identification of
coherence with quasi-coherence plus
finite type on a locally Noetherian scheme is
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_iff_isQuasicoherent_and_isFiniteType` in
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/NoetherianCoherent.lean`; and coherence over a
ringed space with coherent structure sheaf is Stacks 01BZ,
`Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation`. What remains absent is the
cohomological input: dévissage for coherent sheaves, Chow's lemma, the relative Leray spectral
sequence, and vanishing for relatively ample invertible sheaves. The degree-zero reduction proved
here is what the source's statement gives up without those.

`isFiniteType_of_iso` transports a `SheafOfModules.LocalGeneratorsData` across the restriction
of the isomorphism to each open of the covering, using `SheafOfModules.GeneratingSections.ofEpi`
(packaged as `SheafOfModules.GeneratingSections.equivOfIso`). `isCoherent_of_iso` additionally
transports the kernel condition: postcomposing a map out of a free sheaf with an isomorphism
does not change its kernel, by `CategoryTheory.Limits.kernelCompMono`.

`isZero_over_of_isZero` goes through `SheafOfModules.mapFreeIso` rather than additivity of the
restriction functor: the restriction functor has no `Functor.PreservesZeroMorphisms` instance at
this pin, whereas it does preserve the free sheaf on the empty index type, which is a zero
object.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
* [Stacks Project, Tag 05U4](https://stacks.math.columbia.edu/tag/05U4)
-/

@[expose] public section

open CategoryTheory SheafOfModules Limits TopologicalSpace
open AlgebraicGeometry

universe u v' u'

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageCoherent

/-! ### Transport of finite type along isomorphisms, on an arbitrary site -/

section Site

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Finite type is invariant under isomorphism.** A sheaf of modules isomorphic to one of
finite type is of finite type: restrict the isomorphism to each open of a covering by
finite generators and transport the generators along it. -/
theorem isFiniteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [N.IsFiniteType] :
    M.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData N
    refine ⟨⟨σ.I, σ.X, σ.coversTop, fun i =>
      (GeneratingSections.equivOfIso ((overFunctor R (σ.X i)).mapIso e)).symm
        (σ.generators i)⟩, ⟨fun i => ?_⟩⟩
    have := hσ.isFiniteType i
    dsimp [GeneratingSections.equivOfIso]
    infer_instance

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}] [HasBinaryProducts C]

/-- **A free sheaf of modules on a finite index type is of finite type.** Its tautological
family of generating sections is indexed by that finite type. -/
instance isFiniteType_free (I : Type u) [Finite I] : (free (R := R) I).IsFiniteType := by
  have : (free.generatingSections (R := R) I).IsFiniteType := ⟨‹Finite I›⟩
  refine ⟨(free.generatingSections (R := R) I).localGeneratorsData, ⟨fun x => ⟨?_⟩⟩⟩
  dsimp [GeneratingSections.localGeneratorsData, GeneratingSections.map]
  infer_instance

end Site

/-! ### Coherence is invariant under isomorphism, and zero sheaves are coherent -/

section Space

variable {X : Type} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- **Restriction to an open preserves zero sheaves of modules.** A zero sheaf of modules is
the free sheaf on the empty index type, which the restriction functor preserves because that
functor preserves coproducts. -/
theorem isZero_over_of_isZero {M : SheafOfModules.{0} R} (hM : IsZero M) (U : Opens X) :
    IsZero (M.over U) := by
  have h1 : PreservesColimitsOfSize.{0, 0} (overFunctor R U) :=
    (SheafOfModules.overPushforwardOverAdj.{0} (R := R) U).leftAdjoint_preservesColimits
  exact IsZero.of_iso HigherDirectImage.isZero_free_pempty
    ((overFunctor R U).mapIso (hM.iso HigherDirectImage.isZero_free_pempty) ≪≫
      (mapFreeIso (overFunctor R U) PEmpty.{1} (Iso.refl _)).symm)

/-- **Coherence is invariant under isomorphism.** Both conditions of
[Stacks, Tag 01BV] transport: finite type by `isFiniteType_of_iso`, and the finite-type kernel
condition because postcomposing a map out of a free sheaf with an isomorphism leaves its kernel
unchanged. -/
theorem isCoherent_of_iso {M N : SheafOfModules.{0} R} (e : M ≅ N) [N.IsCoherent] :
    M.IsCoherent where
  isFiniteType :=
    have := SheafOfModules.IsCoherent.isFiniteType (M := N)
    isFiniteType_of_iso e
  kernel_isFiniteType U I hI φ := by
    have := SheafOfModules.IsCoherent.kernel_isFiniteType (M := N) U I hI
      (φ ≫ ((overFunctor R U).mapIso e).hom)
    exact isFiniteType_of_iso (kernelCompMono φ ((overFunctor R U).mapIso e).hom).symm

/-- **A zero sheaf of modules is coherent.** It is of finite type, being the free sheaf on the
empty index type, and every map out of a free sheaf into it is zero, so the kernels occurring
in the coherence condition are the free sheaves themselves, which are of finite type. -/
theorem isCoherent_of_isZero {M : SheafOfModules.{0} R} (hM : IsZero M) : M.IsCoherent where
  isFiniteType := isFiniteType_of_iso (hM.iso HigherDirectImage.isZero_free_pempty)
  kernel_isFiniteType U I hI φ := by
    have : Finite I := hI
    exact isFiniteType_of_iso
      ((kernelIsoOfEq ((isZero_over_of_isZero hM U).eq_of_tgt φ 0)).trans kernelZeroIsoSource)

end Space

/-! ### Higher direct images in non-positive degrees -/

section Scheme

variable {X S : Scheme.{0}} (f : X ⟶ S) (F : X.Modules)

/-- **Higher direct images are coherent in negative degrees**, for the trivial reason that they
vanish: this needs no hypothesis on the morphism `f` nor on the module `F`.

Stated for `Scheme.{0}` only, because `SheafOfModules.IsCoherent` is declared only there on
this branch. -/
theorem isCoherent_higherDirectImage_of_neg (p : ℤ) (hp : p < 0) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent :=
  isCoherent_of_isZero (R := S.ringCatSheaf)
    (HigherDirectImage.isZero_higherDirectImage_of_neg f F p hp)

/-- **Coherence of `R ⁰ f_* F` is coherence of `f_* F`.** The pushforward functor on sheaves of
modules over schemes is a right adjoint, hence left exact, so it agrees with its own zeroth
right derived functor; coherence then transports along that isomorphism.

This reduces the degree-`0` case of [Stacks, Tag 02O5] to the assertion about ordinary direct
images, leaving the degrees `i > 0` as the genuinely cohomological content. No hypothesis on
`f` is used. Stated for `Scheme.{0}` only, because `SheafOfModules.IsCoherent` is declared only
there on this branch. -/
theorem isCoherent_higherDirectImage_zero_iff :
    (((Scheme.Modules.pushforward f).rightDerivedPlus 0).obj F).IsCoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  ⟨fun _ => isCoherent_of_iso (HigherDirectImage.higherDirectImageZeroIso f F).symm,
    fun _ => isCoherent_of_iso (HigherDirectImage.higherDirectImageZeroIso f F)⟩

end Scheme

end Stacks.AlgebraicGeometry.HigherDirectImageCoherent

end
