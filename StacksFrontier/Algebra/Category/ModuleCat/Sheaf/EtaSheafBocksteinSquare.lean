module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafBocksteinStalk

import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0GT9's differential square follows from its comparison square

Let `(X, O_X)` be a ringed space, `ι : I ⟶ O_X` an invertible ideal subsheaf, and `F` a cochain
complex of `I`-torsion-free `O_X`-modules.  `EtaSheafReductionStalkModel.lean` reduces
Tag 0GT9's quasi-isomorphism to `Reduction.HasStalkBocksteinComparison`: at every point, an
isomorphism
`β` *of complexes* from the stalk of the chain-level Bockstein complex `H^•(F/I)` to the
algebraic Bockstein complex of `F_x/f`, carrying the stalk of the comparison of Tag 0GT9 to the
algebraic comparison of Tag 0F7T.  `EtaSheafBocksteinStalk.lean` builds `β`'s degreewise
components, `Reduction.bocksteinChainStalkTermIso`, and leaves two squares: that the components
commute with the differentials, and the square with the comparison.

This file proves that **the first square is a consequence of the second**, so that the second is
the only square a caller must supply.  `EtaSheafBocksteinStalk.lean` proves it, as
`Reduction.map_reductionComparison_comp_bocksteinChainStalkTermIso`.

## Main results

* `epi_stalk_reductionComparison`: the stalk of the comparison of Tag 0GT9 is an epimorphism in
  every degree, the stalk functor being exact and the comparison degreewise epi.
* `HasStalkBocksteinSquare`: the degreewise comparison square — the only square a caller must
  supply, and proved in Situation 0GT4 by
  `Reduction.hasStalkBocksteinSquare_of_isLocallyGeneratedByRegular`.
* `bocksteinChainStalkIso`: from that square, `β` itself, as an isomorphism of complexes.
* `hasStalkBocksteinComparison_of_hasStalkBocksteinSquare`: hence
  `Reduction.HasStalkBocksteinComparison`, and so, through
  `EtaSheafReductionStalkModel.lean`, the quasi-isomorphism of Tag 0GT9
  (`quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinSquare`) and the acyclicity of
  `EtaSheafReductionQuasiIso.lean`'s kernel complex
  (`acyclic_reductionComparisonKernel_of_hasStalkBocksteinSquare`).

## Implementation notes

### Why the differential square is free

The note at the head of `EtaSheafBocksteinStalk.lean` records the differential square as needing
the identification of two short exact sequences of complexes at a stalk — the `gradedComplex₂`
analogue of `gradedStalkIso` — *together with* the compatibility of an exact functor with
`ShortComplex.ShortExact.δ`, which Mathlib does not have.  That is not so.  Write `c` for the
stalk of the comparison of Tag 0GT9, `e` for `etaModIdealStalkIso` and `q` for Tag 0F7T's
comparison, so that the comparison square reads `c.f n ≫ β n = e.f n ≫ q.f n` in every degree.
Then `c`, `e` and `q` are already known to be morphisms of complexes, and `c.f n` is an
*epimorphism*; cancelling it turns the differential square for `β` into the three squares for
`c`, `e` and `q` and the comparison square in degrees `n` and `n + 1`.  So neither the
`gradedComplex₂` comparison nor the missing `δ` lemma is on the critical path: the Bockstein
operator never has to be computed at a stalk at all.

That is `comm_of_epi_of_squares` below, stated with every object and morphism a variable — the
chase is pure category theory, and at that generality the application performs one `isDefEq`
rather than a dozen keyed matches inside the stalk of a complex of sheaves of modules.

### What this does not do

Nothing here carries `@[stacks 0GT9]`.  Tag 0GT9 asserts that
`Lη_I M ⊗^L O_X/I ⟶ H^•(M/I)` is an isomorphism in `D(O_X)`; everything here is a step of the
*proof* of that.  The tag's own conclusion is proved in Situation 0GT4 in
`EtaSheafReductionDerivedIsoRegular.lean`, as
`Reduction.isIso_reductionComparisonQ_of_isLocallyGeneratedByRegular` and
`Reduction.reductionComparisonQIsoOfRegular`.

## References

* [Stacks Project, Tag 0GT9](https://stacks.math.columbia.edu/tag/0GT9)
* [Stacks Project, Tag 0GT6](https://stacks.math.columbia.edu/tag/0GT6)
* [Stacks Project, Tag 0GT8](https://stacks.math.columbia.edu/tag/0GT8)
* [Stacks Project, Tag 0F7T](https://stacks.math.columbia.edu/tag/0F7T)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk)

universe u

namespace Stacks.IdealTorsion.Reduction

open Stacks.IdealTorsion.Eta

/-! ### The chase, with every object and morphism a variable -/

/-- **A square of comparisons transported along an epimorphism.**  Given three commuting squares
`c`, `e`, `q` and two comparison triangles `c₀ ≫ b₀ = e₀ ≫ q₀`, `c₁ ≫ b₁ = e₁ ≫ q₁`, the
comparison `b` commutes with the two remaining arrows as soon as `c₀` is an epimorphism.

This is the whole of why the differential square for Tag 0GT9's Bockstein model isomorphism is
free: `c₀` is the stalk of the comparison of Tag 0GT9 in degree `n`, which is an epimorphism,
and `b` is the model isomorphism, whose compatibility with the Bockstein operator would
otherwise have to be computed from the connecting map of a short exact sequence of complexes.

Everything is a variable, so the application performs one `isDefEq` rather than a dozen keyed
matches inside the stalk of a complex of sheaves of modules. -/
public lemma comm_of_epi_of_squares {C : Type*} [Category C]
    {A₀ A₁ B₀ B₁ Q₀ Q₁ R₀ R₁ : C}
    {c₀ : A₀ ⟶ B₀} {c₁ : A₁ ⟶ B₁} {dA : A₀ ⟶ A₁} {dB : B₀ ⟶ B₁}
    {e₀ : A₀ ⟶ Q₀} {e₁ : A₁ ⟶ Q₁} {dQ : Q₀ ⟶ Q₁}
    {q₀ : Q₀ ⟶ R₀} {q₁ : Q₁ ⟶ R₁} {dR : R₀ ⟶ R₁}
    {b₀ : B₀ ⟶ R₀} {b₁ : B₁ ⟶ R₁} [Epi c₀]
    (hc : c₀ ≫ dB = dA ≫ c₁) (he : e₀ ≫ dQ = dA ≫ e₁) (hq : q₀ ≫ dR = dQ ≫ q₁)
    (hb₀ : c₀ ≫ b₀ = e₀ ≫ q₀) (hb₁ : c₁ ≫ b₁ = e₁ ≫ q₁) :
    b₀ ≫ dR = dB ≫ b₁ := by
  rw [← cancel_epi c₀, ← Category.assoc, hb₀, Category.assoc, hq, ← Category.assoc, he,
    Category.assoc, ← hb₁, ← Category.assoc, ← hc, Category.assoc]

variable (X : RingedSpace.{u, u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ### The stalk of the comparison is an epimorphism -/

/-- **The stalk of the comparison of Tag 0GT9 is an epimorphism in every degree.**  The
comparison is degreewise epi (`epi_reductionComparison`) and the module-valued stalk functor
preserves finite colimits (`preservesFiniteColimits_stalkModuleFunctor`), hence epimorphisms. -/
public theorem epi_stalk_reductionComparison
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (x : X) (n : ℤ) :
    Epi ((stalkModuleFunctor X x).map (reductionComparison X I ι F n)) := by
  let := preservesFiniteColimits_stalkModuleFunctor X x
  have := epi_reductionComparison X I ι F hF n
  exact (stalkModuleFunctor X x).map_epi _

/-- The degree-`n` component of the stalk of Tag 0GT9's comparison of complexes is the stalk of
its degree-`n` component.  Stated once, where it is `rfl`, so that neither the epimorphism
instance below nor a consumer has to cross the two spellings again. -/
public theorem stalkComplexFunctor_map_reductionComparisonChainMap_f
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) (x : X) (n : ℤ) :
    ((stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF)).f n =
      (stalkModuleFunctor X x).map (reductionComparison X I ι F n) := rfl

/-! ### The comparison square -/

/-- **The degreewise comparison square of Tag 0GT9's last step.**  At every point `x` of `X`
there are a generator `f` of the stalk ideal `I_x` which is a
nonzerodivisor of `O_{X,x}` and regular on every term of the stalk complex, such that in every
degree the stalk of the comparison of Tag 0GT9, followed by the Bockstein model comparison
`bocksteinChainStalkTermIso`, agrees with Tag 0GT6's comparison of the reduced décalages
(`etaModIdealStalkIso`) followed by the algebraic comparison of Tag 0F7T.

This is the source's last sentence — "on stalks this construction matches the maps built in More
on Algebra, Lemma 15.97.6" — read in a single degree, and nothing more.  It is weaker than
`HasStalkBocksteinComparison` in three ways, all of which are discharged below: the model
comparison is not required to be a morphism of complexes, it is pinned to the *named* components
`bocksteinChainStalkTermIso` rather than existentially quantified, and the square is asked
degreewise rather than at the level of complexes.

As in `HasStalkModelComparison`, the first four data are not themselves the obligation: on a
space whose structure-sheaf stalks are local rings `exists_stalkGenerator` supplies `f` with its
nonzerodivisor property and `isSMulRegular_stalkComplex` its regularity.  They stay inside the
existential so that the statements consuming this hold in the generality of
`EtaSheafReductionQuasiIso.lean` — condition (2) of Tag 0GT3 alone.

Nothing here can be satisfied degenerately: the two outer arrows of the square are the *named*
isomorphisms `bocksteinChainStalkTermIso` and `etaModIdealStalkIso`, so there is no datum left
for a zero map to inhabit. -/
public def HasStalkBocksteinSquare
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k)) : Prop :=
  ∀ x : X, ∃ (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
      (hf : f ∈ nonZeroDivisors (ringStalk X x))
      (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f), ∀ n : ℤ,
      (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
          (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
        (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg).f n

/-- **The Bockstein model comparison is a morphism of complexes as soon as the comparison square
holds.**  Cancel the epimorphism `epi_stalk_reductionComparison` and the square becomes the three
squares saying that the stalk of Tag 0GT9's comparison, Tag 0GT6's comparison of the reduced
décalages, and Tag 0F7T's algebraic comparison are morphisms of complexes, together with the
comparison square in degrees `n` and `n + 1`.

In particular the chain-level Bockstein operator never has to be computed at a stalk: the
identification of the two short exact sequences of complexes and the compatibility of an exact
functor with `ShortComplex.ShortExact.δ` are not needed. -/
private lemma bocksteinChainStalkTermIso_comm_of_square
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f)
    (hsq : ∀ n : ℤ,
      (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
          (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
        (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg).f n) (n : ℤ) :
    (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom ≫
        (EtaPow.Bockstein.bocksteinComplex f hf (stalkComplex X x F) hreg).d n (n + 1) =
      ((stalkComplexFunctor X x).obj (bocksteinChainComplex X I ι F hF)).d n (n + 1) ≫
        (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg (n + 1)).hom := by
  have : Epi (((stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF)).f n) := by
    rw [stalkComplexFunctor_map_reductionComparisonChainMap_f]
    exact epi_stalk_reductionComparison X I ι F hF x n
  exact comm_of_epi_of_squares
    (((stalkComplexFunctor X x).map (reductionComparisonChainMap X I ι F hF)).comm n (n + 1))
    ((etaModIdealStalkIso X I ι F hF x f hgen).hom.comm n (n + 1))
    ((Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
      (stalkComplex X x F) hreg).comm n (n + 1))
    (hsq n) (hsq (n + 1))

/-- **The Bockstein model isomorphism `β` of Tag 0GT9's stalkwise comparison**, built from the
comparison square `hsq`: its components are `bocksteinChainStalkTermIso` and they commute with
the differentials by `bocksteinChainStalkTermIso_comm_of_square`.  The square itself is
`Reduction.map_reductionComparison_comp_bocksteinChainStalkTermIso` in
`EtaSheafBocksteinStalk.lean`. -/
@[no_expose]
public noncomputable def bocksteinChainStalkIso
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
    (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f)
    (hsq : ∀ n : ℤ,
      (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
          (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
        (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg).f n) :
    (stalkComplexFunctor X x).obj (bocksteinChainComplex X I ι F hF) ≅
      EtaPow.Bockstein.bocksteinComplex f hf (stalkComplex X x F) hreg :=
  HomologicalComplex.Hom.isoOfComponents
    (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg)
    (fun n m h => by
      subst h
      exact bocksteinChainStalkTermIso_comm_of_square X I ι F hF x f hgen hf hreg hsq n)

/-- **The degreewise comparison square gives the full Bockstein model identification.**  The
isomorphism of complexes is `bocksteinChainStalkIso`, whose components are the degreewise
comparisons, so the square at the level of complexes is the degreewise square. -/
public theorem hasStalkBocksteinComparison_of_hasStalkBocksteinSquare
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinSquare X I ι F hF) :
    HasStalkBocksteinComparison X I ι F hF := by
  intro x
  obtain ⟨f, hgen, hf, hreg, hsq⟩ := h x
  refine ⟨f, hgen, hf, hreg,
    bocksteinChainStalkIso X I ι F hF x f hgen hf hreg hsq, ?_⟩
  exact HomologicalComplex.hom_ext _ _ (fun n => hsq n)

/-- **Tag 0GT9's quasi-isomorphism, modulo the degreewise comparison square alone.** -/
public theorem quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinSquare
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinSquare X I ι F hF) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) :=
  quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinComparison X I ι F hF
    (hasStalkBocksteinComparison_of_hasStalkBocksteinSquare X I ι F hF h)

/-- **The acyclicity of Tag 0GT9's kernel complex, from the degreewise comparison square
alone.**  This is `EtaSheafReductionQuasiIso.lean`'s chain-level form of the tag, with
`HasStalkBocksteinSquare` the whole of what it rests on. -/
public theorem acyclic_reductionComparisonKernel_of_hasStalkBocksteinSquare
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (h : HasStalkBocksteinSquare X I ι F hF) :
    (reductionComparisonKernel X I ι F hF).Acyclic :=
  acyclic_reductionComparisonKernel_of_hasStalkBocksteinComparison X I ι F hF
    (hasStalkBocksteinComparison_of_hasStalkBocksteinSquare X I ι F hF h)

/-! ### The residue with the generator data discharged -/

/-- **Tag 0GT9 on a space whose structure-sheaf stalks are local rings, modulo the comparison
square and nothing else.**  Every datum of `HasStalkBocksteinSquare` except the square itself is
supplied here from declarations that assume nothing further: the generator `f` of the stalk ideal
and its nonzerodivisor property by `exists_stalkGenerator`, its regularity on the stalk complex
by `isSMulRegular_stalkComplex`.  So on such a space the whole of Tag 0GT9's remaining
obligation is the displayed equation — the source's "on stalks this construction matches the maps
built in More on Algebra, Lemma 15.97.6".

Two things this is not.  It is *not* the tag: it carries
`[∀ z : X, IsLocalRing (X.presheaf.stalk z)]`, which is no part of Situation 0GT4, and so it does
not carry `@[stacks 0GT9]`; `HasStalkBocksteinSquare` keeps the generality of
`EtaSheafReductionQuasiIso.lean`.  And its hypothesis is *formally stronger* than
`HasStalkBocksteinSquare`'s, the generator being universally rather than existentially
quantified — type-forced, because `exists_stalkGenerator` produces its generator through a
`Nonempty.some` that cannot be named at the call site.  That is the faithful reading all the
same: the source chooses an arbitrary local generator and asserts the square for it. -/
public theorem quasiIso_reductionComparisonChainMap_of_square
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    [∀ z : X, IsLocalRing (X.presheaf.stalk z)]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ k : ℤ, IsIdealTorsionFree X ι (F.X k))
    (hsq : ∀ (x : X) (f : ringStalk X x) (hgen : GeneratesStalkIdeal X ι x f)
      (hf : f ∈ nonZeroDivisors (ringStalk X x))
      (hreg : ∀ k : ℤ, IsSMulRegular ((stalkComplex X x F).X k) f) (n : ℤ),
      (stalkModuleFunctor X x).map (reductionComparison X I ι F n) ≫
          (bocksteinChainStalkTermIso X I ι F hF x f hgen hf hreg n).hom =
        (etaModIdealStalkIso X I ι F hF x f hgen).hom.f n ≫
          (Stacks.EtaComplex.ModNonzerodivisor.etaQuotientToBockstein f hf
            (stalkComplex X x F) hreg).f n) :
    QuasiIso (reductionComparisonChainMap X I ι F hF) := by
  refine quasiIso_reductionComparisonChainMap_of_hasStalkBocksteinSquare X I ι F hF fun x => ?_
  obtain ⟨f, hgen, hf⟩ := exists_stalkGenerator X I ι x
  have hreg := isSMulRegular_stalkComplex X I ι F hF x f hgen
  exact ⟨f, hgen, hf, hreg, hsq x f hgen hf hreg⟩

end Stacks.IdealTorsion.Reduction

end
