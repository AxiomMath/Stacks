module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriple
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PrincipalIdealExtension
public import StacksFrontier.CategoryTheory.SheafOfModules.LocalMono

/-!
# `f`-torsion-freeness is monicity, and the snake lemma that reduces it one quotient down

The second clause of `Stacks.Algebraization.HasHilbertInductionStep` — the short exact sequences
of the induction step of [Stacks, Tag 0F27] — needs, besides the monicity of multiplication by a
section, that the *quotient* be `f`-torsion-free: that is the hypothesis `htf` of
`Stacks.Algebraization.CoherentTriple.cokernelTriple`. In the source that is the snake-lemma
output of the choice of section off `Ass(F) ∪ Ass(F/fF)`, and this file supplies both halves of
the mechanism.

## Why it needed anything at all

`Stacks.Algebraization.IsFTorsionFree` is a condition on the *sections over every open*, and for
a sheaf cokernel those are not the quotient of the sections, so the module-level snake input
`Module.linearMapSnakeInput` cannot be applied to it directly. Turning `IsFTorsionFree` into the vanishing of a kernel
is nevertheless short: multiplication by `f` *is* a morphism of sheaves of modules
(`Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom`, which is a natural transformation
of the identity functor evaluated at the module), a morphism of sheaves of modules is a
monomorphism exactly when it is injective on sections over every open
(`PresheafOfModules.mono_iff_surjective` in one direction, `SheafOfModules.forget`'s preservation
of monomorphisms in the other), and `IsSMulRegular` on sections is that injectivity. So
`Stacks.Algebraization.isFTorsionFree_iff_mono_smulPowHom` below holds, and the clause becomes a
statement about monomorphisms in an abelian category, where the snake lemma lives.

## Main definitions

* `Stacks.Algebraization.scalarGlobal`: the image of `f` as a *global* section of the structure
  sheaf of the punctured spectrum. Its restriction to an open is
  `Stacks.Algebraization.scalarOnOpen` on the nose.
* `Stacks.Algebraization.smulSnakeInput`: **the snake input of multiplication by a global section
  of `𝒪_X` on the cokernel sequence of a monomorphism of `𝒪_X`-modules.** This is
  `Module.linearMapSnakeInput`'s construction carried out for sheaves of modules: the rows are
  `0 → M → N → N/M → 0` twice and the vertical map is multiplication by the section, which
  commutes with everything by naturality.

## Main results

* `Stacks.Algebraization.isFTorsionFree_iff_mono_smulPowHom`: **`f`-torsion-freeness is monicity
  of multiplication by `f`.**
* `Stacks.Algebraization.mono_smulPowHom_cokernel_of_mono`: **the snake step.** If multiplication
  by the section is a monomorphism on `N`, and the map it induces on the cokernels of
  multiplication by the section — `M/cM ⟶ N/cN`, the third row's left map of the snake input — is
  a monomorphism, then multiplication by the section is a monomorphism on `N/M`.
* `Stacks.Algebraization.isFTorsionFree_cokernel_of_mono`: the two combined, at the shape
  `Stacks.Algebraization.CoherentTriple.cokernelTriple` asks for.

## Where the hypothesis of the snake step is discharged

The hypothesis of `mono_smulPowHom_cokernel_of_mono` is monicity of
`(smulSnakeInput φ c).L₃.f`, the induced map on the two cokernels of multiplication by `c`. For
the induction step of [Stacks, Tag 0F27] that map is multiplication by the chosen section `σ` on
`F/fF`, and its monicity is
`Stacks.Algebraization.mono_tensorModulesMap_id_mulSectionPowScheme` with `F` replaced by `F/fF` —
which is exactly why the source chooses `σ` off `Ass(F) ∪ Ass(F/fF)` and not merely off `Ass(F)`,
and both halves of that union are what
`Stacks.Algebraization.exists_section_nonvanishing_on_associatedPoints` delivers.

Two identifications stand between the two statements, and both are made in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTorsionFreeTensor`:
`Stacks.Algebraization.mono_smulSnakeInput_L₃_f` is the result, and the fifth clause of
`Stacks.Algebraization.HasHilbertInductionStep` follows from it as
`Stacks.Algebraization.CoherentTriple.isFTorsionFree_cokernel_onPunctured_mulSectionTwistZ`.

* `(smulSnakeInput φ c).L₃.f` is the left map of a cokernel taken in `ShortComplex`, not
  `CategoryTheory.Limits.cokernel.map` of the two multiplications. The comparison needs no
  construction: `Stacks.Algebraization.mono_of_isColimit_cokernelCofork` says that monicity of
  the map induced on two cokernels is independent of the presentations it is read through, so
  `h₃τ₁` and `h₃τ₂` can simply be played against any other pair of presentations.
* The domain of the induction step's map is `F ⊗ L^{⊗ n}`, so what the snake produces is
  monicity on `(F ⊗ L^{⊗ n})/f(F ⊗ L^{⊗ n})`, while the available hypothesis is about
  `Ass(F/fF)`; identifying `(F/fF) ⊗ L^{⊗ n}` with `(F ⊗ L^{⊗ n})/f(F ⊗ L^{⊗ n})` is exactness of
  `- ⊗ L^{⊗ n}`, which is available for this spelling of the tensor product. The functor
  spelling of `Stacks.RelativeVeryAmple.tensorModules` is
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules`, by `rfl`
  (`Stacks.Algebraization.tensorRightModules_map`), and that functor *is*
  `AlgebraicGeometry.SheafOfModules.sheafTensorRight X.sheaf`, again by `rfl`; so right
  exactness is `Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits`
  ([Stacks, Tag 05NB]) with no hypothesis on `L` at all, and the commutation of the functor with
  multiplication by `f` is
  `AlgebraicGeometry.SheafOfModules.sheafTensorRight_map_globalSectionToEnd`. Invertibility of
  `L` is not needed for either, though it gives the first independently through
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules_preservesFiniteColimits`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom smulPowHom_app restrictTop)

universe u

namespace Stacks.Algebraization

/-! ### `f`-torsion-freeness as monicity -/

variable (A : Type u) [CommRing A] [IsLocalRing A] (f : A)

/-- **The image of `f` as a global section of the structure sheaf of the punctured spectrum.**
`Stacks.Algebraization.scalarOnOpen` is its restriction to an open, on the nose, which is what
lets multiplication by `f` on sections be read off the global-section action
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.smulPowHom`. -/
public noncomputable abbrev scalarGlobal :
    Γ((Stacks.Divisors.puncturedSpectrum A).toScheme, ⊤) :=
  (Stacks.Divisors.puncturedSpectrum A).ι.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)

/-- The scalar `Stacks.Algebraization.scalarOnOpen` acting on the sections over an open is the
restriction of the global scalar. -/
public theorem restrictTop_scalarGlobal
    (V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens) :
    restrictTop (scalarGlobal A f) V = scalarOnOpen A f V :=
  rfl

/-- Multiplication by the global scalar reads on sections as multiplication by
`Stacks.Algebraization.scalarOnOpen`. -/
public theorem smulPowHom_scalarGlobal_app
    (M : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens) (g : Γ(M, V)) :
    (smulPowHom M (scalarGlobal A f) 1).val.app (op V) g = scalarOnOpen A f V • g := by
  rw [show (smulPowHom M (scalarGlobal A f) 1).val.app (op V) g
      = (smulPowHom M (scalarGlobal A f) 1).app V g from rfl,
    smulPowHom_app, pow_one, restrictTop_scalarGlobal]

/-- **`f`-torsion-freeness is monicity of multiplication by `f`.** A morphism of sheaves of
modules is a monomorphism exactly when it is injective on the sections over every open, and
`Stacks.Algebraization.IsFTorsionFree` asks for exactly that injectivity for multiplication by
`f`. This is what carries the clause out of the sections and into the abelian category, where the
snake lemma applies. -/
public theorem isFTorsionFree_iff_mono_smulPowHom
    (M : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules) :
    IsFTorsionFree A f M ↔ Mono (smulPowHom M (scalarGlobal A f) 1) := by
  have h := smulPowHom_scalarGlobal_app A f M
  refine ⟨fun hM => ?_, fun hmono V x y hxy => ?_⟩
  · exact (SheafOfModules.forget _).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (f := (smulPowHom M (scalarGlobal A f) 1).val)
        fun W x y hxy => hM (unop W) ((h _ x).symm.trans (hxy.trans (h _ y))))
  · have : Mono (C := SheafOfModules
        (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf)
        (smulPowHom M (scalarGlobal A f) 1) := hmono
    have : Mono (smulPowHom M (scalarGlobal A f) 1).val :=
      (SheafOfModules.forget
        (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf).map_mono
        (smulPowHom M (scalarGlobal A f) 1)
    exact PresheafOfModules.injective_of_mono (smulPowHom M (scalarGlobal A f) 1).val (op V)
      ((h _ x).trans (hxy.trans (h _ y).symm))

/-! ### The snake input of multiplication by a global section -/

section Snake

variable {X : Scheme.{u}}

open Stacks.SheafOfModules (terminalSectionToEnd)

/-- **The snake input of multiplication by a global section of `𝒪_X` on the cokernel sequence of
a monomorphism.** The first and second rows are both the short exact sequence
`0 → M → N → N/M → 0` of [Stacks, Tag 0F27]'s step, the vertical morphism between them is
multiplication by `c` on each term — which commutes with both maps because multiplication by a
global section is a natural transformation of the identity functor — and the zeroth and third
rows are its kernel and cokernel. This is the construction of
`Module.linearMapSnakeInput` carried out in the abelian category of `𝒪_X`-modules, so that it
applies to `Stacks.Algebraization.IsFTorsionFree`, which is about a sheaf and not about one
module. -/
public noncomputable def smulSnakeInput {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (c : Γ(X, ⊤)) :
    ShortComplex.SnakeInput X.Modules :=
  let S : ShortComplex X.Modules := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hShort : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))
      inferInstance inferInstance
  let τ : CategoryTheory.End (𝟭 _) :=
    terminalSectionToEnd X.ringCatSheaf (⊤ : X.Opens) isTerminalTop c
  let v : S ⟶ S :=
    ShortComplex.Hom.mk (smulPowHom M c 1) (smulPowHom N c 1) (smulPowHom (cokernel φ) c 1)
      (((τ ^ 1).naturality φ).symm) (((τ ^ 1).naturality (cokernel.π φ)).symm)
  { L₀ := kernel v
    L₁ := S
    L₂ := S
    L₃ := cokernel v
    v₀₁ := kernel.ι v
    v₁₂ := v
    v₂₃ := cokernel.π v
    h₀ := kernelIsKernel v
    h₃ := cokernelIsCokernel v
    L₁_exact := hShort.exact
    epi_L₁_g := hShort.epi_g
    L₂_exact := hShort.exact
    mono_L₂_f := hShort.mono_f }

/-- **The snake step.** Multiplication by `c` is a monomorphism on the cokernel of `φ` as soon as
it is one on `N` and the map it induces on the cokernels, `M/cM ⟶ N/cN`, is one.

The six-term exact sequence of `smulSnakeInput φ c` reads
`0 → N/M[c] → M/cM → N/cN`, because its zeroth row's middle term is the kernel of multiplication
by `c` on `N`, which vanishes: so the connecting morphism `δ` is a monomorphism, and if
`M/cM ⟶ N/cN` is a monomorphism then `δ` is also zero, forcing its source — the kernel of
multiplication by `c` on `N/M` — to vanish. -/
public theorem mono_smulPowHom_cokernel_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (c : Γ(X, ⊤)) (hN : Mono (smulPowHom N c 1))
    (hquot : Mono (smulSnakeInput φ c).L₃.f) :
    Mono (smulPowHom (cokernel φ) c 1) := by
  set S := smulSnakeInput φ c
  have : Mono S.v₁₂.τ₂ := hN
  have := S.mono_δ (KernelFork.IsLimit.isZero_of_mono S.h₀τ₂)
  have hδ : S.δ = 0 := (cancel_mono S.L₃.f).mp (by rw [S.δ_L₃_f, zero_comp])
  exact Preadditive.mono_of_isZero_kernel' _ S.h₀τ₃ (IsZero.of_mono_eq_zero S.δ hδ)

end Snake

/-- **The quotient of a monomorphism is `f`-torsion-free as soon as the induced map on the
quotients by `f` is a monomorphism.** This is the hypothesis `htf` of
`Stacks.Algebraization.CoherentTriple.cokernelTriple`, reduced — through
`isFTorsionFree_iff_mono_smulPowHom` and the snake lemma — to monicity of `M/fM ⟶ N/fN`, which in
the induction step of [Stacks, Tag 0F27] is multiplication by the chosen section on `F/fF`. -/
public theorem isFTorsionFree_cokernel_of_mono
    {M N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (φ : M ⟶ N) [Mono φ]
    (hN : IsFTorsionFree A f N)
    (hquot : Mono (smulSnakeInput φ (scalarGlobal A f)).L₃.f) :
    IsFTorsionFree A f (cokernel φ) :=
  (isFTorsionFree_iff_mono_smulPowHom A f (cokernel φ)).2
    (mono_smulPowHom_cokernel_of_mono φ (scalarGlobal A f)
      ((isFTorsionFree_iff_mono_smulPowHom A f N).1 hN) hquot)

end Stacks.Algebraization

end
