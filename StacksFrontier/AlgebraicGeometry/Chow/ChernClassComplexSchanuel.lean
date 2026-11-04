module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Extension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre

/-!
# The Schanuel module of two presentations of the same cohomology

This file constructs the comparison datum `Stacks.Chow.ComplexCohomologyComparison` out of the
two presentations of the cohomology alone, which is the last step of the proof of
[Stacks, Tag 0ESZ].

Given two surjections `g₁ : Z' ⟶ H` and `g₂ : Z'' ⟶ H` onto one object of an abelian category,
with kernels `B'` and `B''`, the fibre product `𝒢 = Z' ×_H Z''` sits in two short exact sequences

  `0 ⟶ B' ⟶ 𝒢 ⟶ Z'' ⟶ 0`,   `0 ⟶ B'' ⟶ 𝒢 ⟶ Z' ⟶ 0`,

because a pullback of an epimorphism is an epimorphism and the kernel of one projection is the
kernel of the opposite surjection.  This is the diagram chase of Schanuel's lemma,
[Stacks, Tag 00O3], carried out categorically rather than with elements.

## Main definitions

* `Stacks.Chow.kerToPullbackSnd` and `Stacks.Chow.kerToPullbackFst`: the two inclusions of a
  kernel into the fibre product.  That each is a kernel of the opposite projection is already
  `Stacks.SheafOfModules.isLimitKernelForkPullbackSnd` and `...Fst`, which are used here.
* `Stacks.Chow.ComplexCohomologyComparison.ofCohomologyPresentations`: **the comparison datum**,
  built from two presentations of one family of cohomology modules.

## Main results

* `Stacks.Chow.exact_kerToPullbackSnd` and `Stacks.Chow.exact_kerToPullbackFst`: the two short
  exact sequences above.
* `Stacks.Chow.isFiniteLocallyFree_pullback_of_exact`: the fibre product of two surjections onto
  one sheaf of modules is finite locally free as soon as the kernel of one of them and the source
  of the other are.

## Implementation notes

**What this discharges and what it carries.**  In the source the fibre product is seen to be
finite locally free from the quotient being perfect of tor dimension at most one, which is the
sheaf-level form of [Stacks, Tag 0F8J] and is not available here.  It is obtained instead from
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact`: both ends of the first of the two
sequences above are finite locally free, being a coboundary module and a cocycle module of a
`Stacks.Chow.BoundedComplexSplitting`, so the middle term is.  No tor-dimension hypothesis is
needed, and none is assumed.

What remains a hypothesis is the statement that the two complexes have the same cohomology, in
the form of the two presentations `0 ⟶ B'^n ⟶ Z'^n ⟶ H^n ⟶ 0` and `0 ⟶ B''^n ⟶ Z''^n ⟶ H^n ⟶ 0`.
That is the input of the last step of the source's proof, produced upstream from an isomorphism
`ℰ^• ≅ ℱ^•` in `D(𝒪_X)` by the reductions of [Stacks, Tag 02UC] and [Stacks, Tag 0ESR]; it is
not produced here.  Nothing about the Schanuel module itself is assumed.

**Why the categorical route.**  Schanuel's lemma in the repository, `schanuel`, is a statement
about modules over a ring and produces a linear equivalence `K ⊕ P₂ ≃ P₁ ⊕ L` from projectivity
of the two presenting modules.  Neither the elementwise chase nor projectivity is available for
sheaves of modules on a scheme — a locally free sheaf is not a projective object — so the fibre
product is used directly, which needs only that `𝒪_X`-modules form an abelian category.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 00O3](https://stacks.math.columbia.edu/tag/00O3)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The fibre product of two surjections onto one object -/

section Abelian

variable {C : Type*} [Category C] [Abelian C] {K L A B H : C}

/-- **The inclusion of the kernel of `g₁` into the fibre product of `g₁` and `g₂`**, as the
kernel of the projection onto the source of `g₂`.  Its components are the given inclusion and
zero. -/
def kerToPullbackSnd (ι : K ⟶ A) {g₁ : A ⟶ H} (w : ι ≫ g₁ = 0) (g₂ : B ⟶ H) :
    K ⟶ pullback g₁ g₂ :=
  pullback.lift ι 0 (by rw [w, zero_comp])

/-- The component of `kerToPullbackSnd` along the projection to the source of `g₁` is the given
inclusion. -/
@[reassoc (attr := simp)]
lemma kerToPullbackSnd_fst (ι : K ⟶ A) {g₁ : A ⟶ H} (w : ι ≫ g₁ = 0) (g₂ : B ⟶ H) :
    kerToPullbackSnd ι w g₂ ≫ pullback.fst g₁ g₂ = ι :=
  pullback.lift_fst _ _ _

/-- The component of `kerToPullbackSnd` along the projection to the source of `g₂` is zero. -/
@[reassoc (attr := simp)]
lemma kerToPullbackSnd_snd (ι : K ⟶ A) {g₁ : A ⟶ H} (w : ι ≫ g₁ = 0) (g₂ : B ⟶ H) :
    kerToPullbackSnd ι w g₂ ≫ pullback.snd g₁ g₂ = 0 :=
  pullback.lift_snd _ _ _

/-- The inclusion of the kernel of `g₁` into the fibre product is a monomorphism as soon as the
given inclusion is one, since the latter factors through it. -/
instance mono_kerToPullbackSnd (ι : K ⟶ A) {g₁ : A ⟶ H} (w : ι ≫ g₁ = 0) (g₂ : B ⟶ H)
    [Mono ι] : Mono (kerToPullbackSnd ι w g₂) :=
  mono_of_mono_fac (kerToPullbackSnd_fst ι w g₂)

/-- **The first Schanuel sequence `0 ⟶ Ker(g₁) ⟶ A ×_H B ⟶ B ⟶ 0` is exact.**  That the inclusion
of the kernel is a kernel of the projection is
`Stacks.SheafOfModules.isLimitKernelForkPullbackSnd`. -/
theorem exact_kerToPullbackSnd (ι : K ⟶ A) {g₁ : A ⟶ H} (w : ι ≫ g₁ = 0) [Mono ι]
    (hex : (ShortComplex.mk ι g₁ w).Exact) (g₂ : B ⟶ H) :
    (ShortComplex.mk (kerToPullbackSnd ι w g₂) (pullback.snd g₁ g₂)
      (kerToPullbackSnd_snd ι w g₂)).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (Stacks.SheafOfModules.isLimitKernelForkPullbackSnd g₂ hex.fIsKernel _
      (kerToPullbackSnd_fst ι w g₂) (kerToPullbackSnd_snd ι w g₂))

/-- **The inclusion of the kernel of `g₂` into the fibre product of `g₁` and `g₂`**, as the
kernel of the projection onto the source of `g₁`.  Its components are zero and the given
inclusion. -/
def kerToPullbackFst (g₁ : A ⟶ H) (κ : L ⟶ B) {g₂ : B ⟶ H} (w : κ ≫ g₂ = 0) :
    L ⟶ pullback g₁ g₂ :=
  pullback.lift 0 κ (by rw [w, zero_comp])

/-- The component of `kerToPullbackFst` along the projection to the source of `g₂` is the given
inclusion. -/
@[reassoc (attr := simp)]
lemma kerToPullbackFst_snd (g₁ : A ⟶ H) (κ : L ⟶ B) {g₂ : B ⟶ H} (w : κ ≫ g₂ = 0) :
    kerToPullbackFst g₁ κ w ≫ pullback.snd g₁ g₂ = κ :=
  pullback.lift_snd _ _ _

/-- The component of `kerToPullbackFst` along the projection to the source of `g₁` is zero. -/
@[reassoc (attr := simp)]
lemma kerToPullbackFst_fst (g₁ : A ⟶ H) (κ : L ⟶ B) {g₂ : B ⟶ H} (w : κ ≫ g₂ = 0) :
    kerToPullbackFst g₁ κ w ≫ pullback.fst g₁ g₂ = 0 :=
  pullback.lift_fst _ _ _

/-- The inclusion of the kernel of `g₂` into the fibre product is a monomorphism as soon as the
given inclusion is one, since the latter factors through it. -/
instance mono_kerToPullbackFst (g₁ : A ⟶ H) (κ : L ⟶ B) {g₂ : B ⟶ H} (w : κ ≫ g₂ = 0)
    [Mono κ] : Mono (kerToPullbackFst g₁ κ w) :=
  mono_of_mono_fac (kerToPullbackFst_snd g₁ κ w)

/-- **The second Schanuel sequence `0 ⟶ Ker(g₂) ⟶ A ×_H B ⟶ A ⟶ 0` is exact.**  That the inclusion
of the kernel is a kernel of the projection is
`Stacks.SheafOfModules.isLimitKernelForkPullbackFst`. -/
theorem exact_kerToPullbackFst (g₁ : A ⟶ H) (κ : L ⟶ B) {g₂ : B ⟶ H} (w : κ ≫ g₂ = 0)
    [Mono κ] (hex : (ShortComplex.mk κ g₂ w).Exact) :
    (ShortComplex.mk (kerToPullbackFst g₁ κ w) (pullback.fst g₁ g₂)
      (kerToPullbackFst_fst g₁ κ w)).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (Stacks.SheafOfModules.isLimitKernelForkPullbackFst g₁ g₂ hex.fIsKernel _
      (kerToPullbackFst_fst g₁ κ w) (kerToPullbackFst_snd g₁ κ w))

end Abelian

/-! ### Finite local freeness of the fibre product -/

variable {X : Scheme.{u}}

/-- **The fibre product of two surjections of `𝒪_X`-modules onto one module is finite locally
free** as soon as the kernel of the first and the source of the second are.  This replaces the
appeal to the sheaf-level form of [Stacks, Tag 0F8J] in the source, which deduces it from the
quotient being perfect of tor dimension at most one: here the first Schanuel sequence already has
both ends finite locally free, and finite locally free modules are closed under extensions. -/
theorem isFiniteLocallyFree_pullback_of_exact {K A B H : X.Modules} (ι : K ⟶ A) {g₁ : A ⟶ H}
    (w : ι ≫ g₁ = 0) [Mono ι] (hex : (ShortComplex.mk ι g₁ w).Exact) (g₂ : B ⟶ H) [Epi g₁]
    (hK : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) K)
    (hB : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) B) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (pullback g₁ g₂) :=
  Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact
    (ShortComplex.mk (kerToPullbackSnd ι w g₂) (pullback.snd g₁ g₂) (kerToPullbackSnd_snd ι w g₂))
    { exact := exact_kerToPullbackSnd ι w hex g₂
      mono_f := mono_kerToPullbackSnd ι w g₂
      epi_g := Abelian.epi_pullback_of_epi_f g₁ g₂ }
    hK hB

/-! ### The comparison datum -/

/-- **The degreewise comparison datum of [Stacks, Tag 0ESZ], built from two presentations of one
family of cohomology modules.**

The hypotheses are exactly that the two complexes have the same cohomology: for each degree `n` a
module `H n` presented both as `Z'^n/B'^n` and as `Z''^n/B''^n`, by short exact sequences whose
outer terms are the cocycle and coboundary modules of the two given splittings.  The Schanuel
module is then the fibre product `Z'^n ×_{H^n} Z''^n`, and its finite local freeness comes from
the first of its two short exact sequences, whose ends are a coboundary module and a cocycle
module and hence finite locally free.

No tor-dimension hypothesis on `H n` is used, and nothing about the Schanuel module is assumed.
What is not produced here is the presentations themselves: those come from an isomorphism of the
two complexes in `D(𝒪_X)`, through the reductions of [Stacks, Tag 02UC] and [Stacks, Tag 0ESR]. -/
def ComplexCohomologyComparison.ofCohomologyPresentations
    {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (H : ℤ → X.Modules)
    (fι : ∀ n : ℤ, S.coboundaries n ⟶ S.cocycles n)
    (fι_comp : ∀ n : ℤ, fι n ≫ S.cocyclesι n = S.coboundariesι n)
    (fπ : ∀ n : ℤ, S.cocycles n ⟶ H n)
    (fw : ∀ n : ℤ, fι n ≫ fπ n = 0)
    (fmono : ∀ n : ℤ, Mono (fι n)) (fepi : ∀ n : ℤ, Epi (fπ n))
    (fex : ∀ n : ℤ, (ShortComplex.mk (fι n) (fπ n) (fw n)).Exact)
    (sι : ∀ n : ℤ, T.coboundaries n ⟶ T.cocycles n)
    (sι_comp : ∀ n : ℤ, sι n ≫ T.cocyclesι n = T.coboundariesι n)
    (sπ : ∀ n : ℤ, T.cocycles n ⟶ H n)
    (sw : ∀ n : ℤ, sι n ≫ sπ n = 0)
    (smono : ∀ n : ℤ, Mono (sι n)) (sepi : ∀ n : ℤ, Epi (sπ n))
    (sex : ∀ n : ℤ, (ShortComplex.mk (sι n) (sπ n) (sw n)).Exact) :
    ComplexCohomologyComparison S T where
  cohomology := H
  firstCoboundariesι := fι
  firstCoboundariesι_comp := fι_comp
  firstπ := fπ
  firstw := fw
  mono_firstCoboundariesι := fmono
  epi_firstπ := fepi
  firstExact := fex
  secondCoboundariesι := sι
  secondCoboundariesι_comp := sι_comp
  secondπ := sπ
  secondw := sw
  mono_secondCoboundariesι := smono
  epi_secondπ := sepi
  secondExact := sex
  schanuel n := pullback (fπ n) (sπ n)
  isFiniteLocallyFree_schanuel n :=
    have := fmono n
    have := fepi n
    isFiniteLocallyFree_pullback_of_exact (fι n) (fw n) (fex n) (sπ n)
      (S.isFiniteLocallyFree_coboundaries n) (T.isFiniteLocallyFree_cocycles n)
  firstSchanuelι n := kerToPullbackSnd (fι n) (fw n) (sπ n)
  firstSchanuelπ n := pullback.snd (fπ n) (sπ n)
  firstSchanuelw n := kerToPullbackSnd_snd (fι n) (fw n) (sπ n)
  mono_firstSchanuelι n :=
    have := fmono n
    mono_kerToPullbackSnd (fι n) (fw n) (sπ n)
  epi_firstSchanuelπ n :=
    have := fepi n
    Abelian.epi_pullback_of_epi_f (fπ n) (sπ n)
  firstSchanuelExact n :=
    have := fmono n
    exact_kerToPullbackSnd (fι n) (fw n) (fex n) (sπ n)
  secondSchanuelι n := kerToPullbackFst (fπ n) (sι n) (sw n)
  secondSchanuelπ n := pullback.fst (fπ n) (sπ n)
  secondSchanuelw n := kerToPullbackFst_fst (fπ n) (sι n) (sw n)
  mono_secondSchanuelι n :=
    have := smono n
    mono_kerToPullbackFst (fπ n) (sι n) (sw n)
  epi_secondSchanuelπ n :=
    have := sepi n
    Abelian.epi_pullback_of_epi_g (fπ n) (sπ n)
  secondSchanuelExact n :=
    have := smono n
    exact_kerToPullbackFst (fπ n) (sι n) (sw n) (sex n)

/-- **The degreewise comparison datum of [Stacks, Tag 0ESZ] from an identification of the two
cohomologies.**  Each complex presents its own cohomology by its cocycles modulo its
coboundaries, and the two families of cohomology modules are identified degreewise.  This is the
shape in which the hypothesis arises: the presentations of a single complex's cohomology are
intrinsic to it, and what an isomorphism `ℰ^• ≅ ℱ^•` in `D(𝒪_X)` supplies is the identification
`H^n(ℰ^•) ≅ H^n(ℱ^•)`.

It reduces to `Stacks.Chow.ComplexCohomologyComparison.ofCohomologyPresentations` by composing
the first projection with the identification, which preserves exactness and epimorphy. -/
def ComplexCohomologyComparison.ofCohomologyIso
    {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (HP HQ : ℤ → X.Modules) (e : ∀ n : ℤ, HP n ≅ HQ n)
    (fι : ∀ n : ℤ, S.coboundaries n ⟶ S.cocycles n)
    (fι_comp : ∀ n : ℤ, fι n ≫ S.cocyclesι n = S.coboundariesι n)
    (fπ : ∀ n : ℤ, S.cocycles n ⟶ HP n)
    (fw : ∀ n : ℤ, fι n ≫ fπ n = 0)
    (fmono : ∀ n : ℤ, Mono (fι n)) (fepi : ∀ n : ℤ, Epi (fπ n))
    (fex : ∀ n : ℤ, (ShortComplex.mk (fι n) (fπ n) (fw n)).Exact)
    (sι : ∀ n : ℤ, T.coboundaries n ⟶ T.cocycles n)
    (sι_comp : ∀ n : ℤ, sι n ≫ T.cocyclesι n = T.coboundariesι n)
    (sπ : ∀ n : ℤ, T.cocycles n ⟶ HQ n)
    (sw : ∀ n : ℤ, sι n ≫ sπ n = 0)
    (smono : ∀ n : ℤ, Mono (sι n)) (sepi : ∀ n : ℤ, Epi (sπ n))
    (sex : ∀ n : ℤ, (ShortComplex.mk (sι n) (sπ n) (sw n)).Exact) :
    ComplexCohomologyComparison S T :=
  ComplexCohomologyComparison.ofCohomologyPresentations S T HQ
    fι fι_comp (fun n => fπ n ≫ (e n).hom)
    (fun n => by rw [← Category.assoc, fw n, zero_comp]) fmono
    (fun n => have := fepi n; epi_comp _ _)
    (fun n => by
      refine ShortComplex.exact_of_iso (ShortComplex.isoMk (Iso.refl (S.coboundaries n))
        (Iso.refl (S.cocycles n)) (e n) ?_ ?_) (fex n)
      · simp
      · simp)
    sι sι_comp sπ sw smono sepi sex

end Stacks.Chow

end
