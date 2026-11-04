module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeLeray.Basic
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Collapse
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Acyclicity of the terms of the relative Čech complex for the pushforward

Let `j : U ⟶ X` and `f : X ⟶ S` be morphisms of schemes with `j` affine and `j ≫ f` affine, and
let `F` be a quasi-coherent `𝒪_U`-module.  Then `R ᵠ f_*(j_* F) = 0` for every `q > 0`, so
`j_* F` is right acyclic for `f_*`.  This is the step

> Using `f ∘ j_{i_0 … i_p} = f_{i_0 … i_p}` and the spectral sequence of Cohomology, Lemma
> 01F6 we conclude that `R ᵠ f_*(j_{i_0 … i_p *} ℱ_{i_0 … i_p}) = 0` for `q > 0`

of the proof of [Stacks, Tag 01XL], and it is the predicate that Leray's acyclicity lemma
([Stacks, Tag 015E], `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`)
consumes.

**No spectral sequence is used.** The source invokes the composition spectral sequence
[Stacks, Tag 01F6] only to kill `R ᵠ f_*(j_* F)` from the vanishing of `R ᵠ j_*` and of
`R ᵠ (j ≫ f)_*`.  That consequence is the *collapse* of the derived functor of a composite at an
acyclic object, which is [Stacks, Tag 089W] and is `Stacks.AcyclicCollapse.objIso`:
`R ⁿ(G ⋙ T)(A) ≅ R ⁿ T(G A)` whenever `G` carries injectives to `T`-acyclics and `A` is
`G`-acyclic.  Read at `G = j_*`, `T = f_*`, `A = F`, and with `j_* ⋙ f_* = (j ≫ f)_*` on the
nose (`pushforward_comp`), the left-hand side is `R ⁿ(j ≫ f)_* F`, which [Stacks, Tag 01XC]
kills.  So nothing below depends on [Stacks, Tag 01F6].

## Main results

* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.pushforward_comp`: `j_* ⋙ f_* = (j ≫ f)_*` as
  functors on sheaves of modules, by `rfl`.
* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_obj_injective`: the
  pushforward of an injective module sheaf along a morphism of schemes is right acyclic for the
  pushforward along any further morphism.  This is the hypothesis `hacyc` of
  `Stacks.AcyclicCollapse`, and it is the acyclicity input of [Stacks, Tag 01F6] read at
  schemes.
* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.isZero_rightDerived_pushforward_comp` and
  `isZero_rightDerivedPlus_pushforward_comp`: `R ᵠ f_*(j_* F) = 0` for `q > 0`, in the `ℕ`- and
  the `ℤ`-indexed spelling of the higher direct images.
* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_comp`: therefore
  `j_* F` is right acyclic for `f_*`.
* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.relativeCechPresheaf_obj_obj_eq_pushforward`:
  `Č ᵖ(𝒰, f, ℱ) = f_* 𝔠 ᵖ(𝒰, ℱ)` factor by factor — the value of the relative Čech coefficient
  presheaf of [Stacks, Tag 01XL] at `A : Over X` is `f_*` applied to `A.hom_* A.hom ^* ℱ`, by
  `rfl`.
* `Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_relativeCechFactor`: that
  `𝒪_X`-module is right acyclic for `f_*` whenever `A.left` is affine.  No hypothesis is placed
  on `f`: the two affine-diagonal hypotheses of the statement do all the work, through
  `Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source`.

## Implementation notes

`rightAcyclic_pushforward_obj_injective` is the ringed-space statement
`Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective` read at the morphisms of
ringed spaces underlying the two morphisms of schemes; every identification is `rfl`, by
`Stacks.SchemeCohomology.modulePushforward_hom`.  The instance `Injective I` has to be passed
positionally rather than found: `AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own
`Category` instance, definitionally equal to but not syntactically the one on
`SheafOfModules (structureSheafRing (ringedSpace U))`, and instance *search* for `Injective`
across the two spellings exhausts its heartbeats where checking a supplied term against the
expected type does not.  This is the same obstruction met in the formalization of
[Stacks, Tag 089W], and the same cure.  For the same
reason the injectivity is an explicit hypothesis of the statement here, as it is in
`Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj`.

`rightAcyclic_relativeCechPresheaf_obj` is stated at `((relativeCechPresheaf f).obj F).obj (op
A)` rather than at the pushforward it unfolds to, so that it is directly about the
coefficient presheaf of [Stacks, Tag 01XL];
`Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf_obj_obj` holds by `rfl`, so the two
are interchangeable by `exact` and not by `rw`.

**What this file does not do.** The last part of [Stacks, Tag 01XL] asks for the derived
isomorphism, and Leray's acyclicity lemma needs the acyclicity of *every term* of the complex,
not of the single pushforwards the terms are assembled from.  The degree-`n` term of
`CategoryTheory.cechComplexFunctor` is the product, over `x : Fin (n + 1) → ι`, of the value of
the coefficient presheaf at the product of the `Over.mk (T.f (x a))`, and the missing step is
that `Functor.rightAcyclic` is closed under finite products — the exact analogue, for
acyclicity, of `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi`, which is
what carries the quasi-coherence of the terms over the same product.  Nothing in this
repository or in pinned Mathlib states that closure: pinned Mathlib declares no `Functor.Additive`
instance for `Functor.rightDerived` and no `IsZero (∏ᶜ _)` from pointwise vanishing.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechAcyclic

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {U X S : Scheme.{u}}

/-- **Pushforward of modules along morphisms of schemes is strictly functorial.** For
composable `j : U ⟶ X` and `f : X ⟶ S`, the functors `j_* ⋙ f_*` and `(j ≫ f)_*` are *equal*,
not merely isomorphic: both are `SheafOfModules.pushforward` of the same data, so
`Stacks.RelativeLeray.modulePushforward_comp` reads here with no transport. -/
public theorem pushforward_comp (j : U ⟶ X) (f : X ⟶ S) :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward f =
      Scheme.Modules.pushforward (j ≫ f) :=
  rfl

/-- **The acyclicity input of [Stacks, Tag 01F6], read at morphisms of schemes.** The
pushforward along `j` of an injective `𝒪_U`-module is right acyclic for the pushforward
along `f`.

This is `Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective` at the underlying
morphisms of ringed spaces, and it is the hypothesis `hacyc` that `Stacks.AcyclicCollapse`
and `CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]) ask of the pair `(j_*, f_*)`. -/
@[ega "0 12.2.4" "special case"]
public theorem rightAcyclic_pushforward_obj_injective (j : U ⟶ X) (f : X ⟶ S) (I : U.Modules)
    (hI : Injective I) :
    (Scheme.Modules.pushforward f).rightAcyclic ((Scheme.Modules.pushforward j).obj I) :=
  @Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective.{u} _ _ _
    (Stacks.SchemeCohomology.hom j) (Stacks.SchemeCohomology.hom f) I hI

/-- **`R ᵠ f_*(j_* F) = 0` for `q > 0`**, when `j` and `j ≫ f` are affine and `F` is
quasi-coherent, in Mathlib's `ℕ`-indexed spelling `Functor.rightDerived`.

The collapse [Stacks, Tag 089W] identifies `R ⁿ(j_* ⋙ f_*)(F)` with `R ⁿ f_*(j_* F)`: its two
hypotheses are `rightAcyclic_pushforward_obj_injective` and the vanishing of `R ⁿ j_* F`, which
is [Stacks, Tag 01XC] for the affine morphism `j`.  By `pushforward_comp` the left-hand side is
`R ⁿ (j ≫ f)_* F`, which is [Stacks, Tag 01XC] again, now for the affine morphism `j ≫ f`. -/
public theorem isZero_rightDerived_pushforward_comp (j : U ⟶ X) (f : X ⟶ S) [IsAffineHom j]
    [IsAffineHom (j ≫ f)] (F : U.Modules) [F.IsQuasicoherent] (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      ((Scheme.Modules.pushforward j).obj F)) :=
  (Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward (j ≫ f) F n hn).of_iso
    (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward j) (Scheme.Modules.pushforward f)
      (fun I hI ↦ rightAcyclic_pushforward_obj_injective j f I hI)
      (fun m hm ↦
        Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward j F m hm) n).symm

/-- **`R ᵠ f_*(j_* F) = 0` for `q > 0`**, in the `ℤ`-indexed spelling
`Functor.rightDerivedPlus`. -/
public theorem isZero_rightDerivedPlus_pushforward_comp (j : U ⟶ X) (f : X ⟶ S) [IsAffineHom j]
    [IsAffineHom (j ≫ f)] (F : U.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj
      ((Scheme.Modules.pushforward j).obj F)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (Scheme.Modules.pushforward f) hn _]
  exact isZero_rightDerived_pushforward_comp j f F n (by omega)

/-- **The pushforward of a quasi-coherent module along an affine morphism whose composite with
`f` is affine is right acyclic for `f_*`.** This is the predicate that Leray's acyclicity lemma
[Stacks, Tag 015E] (`CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`)
asks of each term of a bounded below complex.

The pushforward is a right adjoint, hence left exact, so part (2) of [Stacks, Tag 015C] turns
the vanishing of `isZero_rightDerivedPlus_pushforward_comp` into right acyclicity. -/
public theorem rightAcyclic_pushforward_comp (j : U ⟶ X) (f : X ⟶ S) [IsAffineHom j]
    [IsAffineHom (j ≫ f)] (F : U.Modules) [F.IsQuasicoherent] :
    (Scheme.Modules.pushforward f).rightAcyclic ((Scheme.Modules.pushforward j).obj F) :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus (Scheme.Modules.pushforward f)
      ((Scheme.Modules.pushforward j).obj F)).2 inferInstance).2
    fun i hi ↦ isZero_rightDerivedPlus_pushforward_comp j f F i hi

/-- **The value of the relative Čech coefficient presheaf of [Stacks, Tag 01XL] is the
pushforward along `f` of the corresponding term of the absolute Čech resolution.**  That is,
`Č ᵖ(𝒰, f, ℱ) = f_* 𝔠 ᵖ(𝒰, ℱ)` factor by factor: the value at `A : Over X` is `f_*` applied to
the `𝒪_X`-module `A.hom_* A.hom ^* ℱ`, which is the factor of `𝔠 ᵖ(𝒰, ℱ)` attached to `A`.

This is the equality of complexes that the proof of [Stacks, Tag 01XL] asserts, read on one
factor of one term; it holds by `rfl`, because `pushforward_comp` is an equality of functors
and the value of the coefficient presheaf is `(A.hom ≫ f)_* A.hom ^* ℱ` by
`Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf_obj_obj`, also `rfl`. -/
public theorem relativeCechPresheaf_obj_obj_eq_pushforward (f : X ⟶ S) (A : Over X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    ((Stacks.AlgebraicGeometry.RelativeCech.relativeCechPresheaf f).obj F).obj (op A) =
      (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward A.hom).obj
          ((Scheme.Modules.pullback A.hom).obj F.obj)) :=
  rfl

/-- **Each factor of a term of the absolute Čech resolution of [Stacks, Tag 01XL] is right
acyclic for `f_*`.**  The factor attached to `A : Over X` with affine source is
`A.hom_* A.hom ^* ℱ`, which is `j_{i_0 … i_p *} ℱ_{i_0 … i_p}` in the notation of the source,
and `relativeCechPresheaf_obj_obj_eq_pushforward` identifies `f_*` of it with the value of the
relative Čech coefficient presheaf there.

No hypothesis is placed on `f`.  Affineness of the diagonal of `X` makes `A.hom` an affine
morphism and affineness of the diagonal of `S` makes `A.hom ≫ f` one, both by
`Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source`, because the
source is affine; and `A.hom ^* ℱ` is quasi-coherent for an arbitrary morphism by
[Stacks, Tag 01BG].  These are the same three inputs that carry the quasi-coherence of
the terms, `Stacks.AlgebraicGeometry.RelativeCechComplex.isQuasicoherent_presheaf_obj`. -/
public theorem rightAcyclic_relativeCechFactor (f : X ⟶ S) (A : Over X) [IsAffine A.left]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pushforward f).rightAcyclic
      ((Scheme.Modules.pushforward A.hom).obj
        ((Scheme.Modules.pullback A.hom).obj F.obj)) := by
  have hj : IsAffineHom A.hom :=
    Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
  have hjf : IsAffineHom (A.hom ≫ f) :=
    Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
  have hpb : ((Scheme.Modules.pullback A.hom).obj F.obj).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback A.hom F.obj F.property
  exact rightAcyclic_pushforward_comp A.hom f ((Scheme.Modules.pullback A.hom).obj F.obj)

end Stacks.AlgebraicGeometry.RelativeCechAcyclic

end
