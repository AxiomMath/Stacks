module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Noetherian.Defs
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Monoidal.Mon
import StacksFrontier.Algebra.Homology.ProjectiveDimension
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe v u

/-!
# Finite projective resolutions of a finite module over a Noetherian ring

Let `R` be a (left) Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`. This file
proves that `M` has projective dimension at most `d` if and only if `M` admits a resolution

`0 → P_d → P_{d-1} → ⋯ → P₀ → M → 0`

by *finite projective* modules, that is, a left resolution of `M` (Stacks 00LQ) by modules that are
projective and finite over `R` and whose terms vanish in degrees `> d`.

Only finiteness separates this from the resolution by projectives of Stacks 0CXC: a finite
projective module is projective, so one direction only forgets finiteness. Conversely one
resolves `M` step by step by finite free modules, which is possible because `M` is finite and,
`R` being Noetherian, the kernel of a surjection from a finite free module onto a finite module is
again finite; the induction on `d` is dimension shifting along the short exact sequence
`0 → Ker(P₀ → M) → P₀ → M → 0`, whose kernel has projective dimension at most `d - 1`, and the
resolution of the kernel is prepended to `P₀`.

## Main results

* `Stacks.FiniteProjectiveResolution.solution`: Stacks 0CXE, the equivalence of condition `(6)` of
  the source with item 1 of Stacks 0CXC.

## Implementation notes

Splicing a resolution onto a short exact sequence is `Stacks.FiniteProjectiveResolution.prepend`:
for a short exact sequence `0 → Z → P → Y → 0` and a resolution `F` of `Z` whose terms lie in a
class `Q` to which `P` also belongs, the complex `⋯ → F₁ → F₀ → P` with the augmentation `P → Y` is
a resolution of `Y` by objects of `Q`. It is stated for a resolution of `Z` whose terms are
projective, which is what makes Mathlib's `CategoryTheory.ProjectiveResolution` API available for
the exactness of `F₁ → F₀ → Z`, and is the class-aware form of the splicing that Stacks 0CXC
performs internally.

Finite free covers: `Stacks.FiniteProjectiveResolution.exists_surjective_of_free_of_finite` is
Mathlib's `Module.exists_finite_presentation` with commutativity of `R` dropped, which its proof
never uses.

## References

* [StacksProject 0CXE](https://stacks.math.columbia.edu/tag/0CXE)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 00LP](https://stacks.math.columbia.edu/tag/00LP)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

namespace Stacks.FiniteProjectiveResolution

open CategoryTheory Limits ChainComplex HomologicalComplex StacksDraft.ProjectiveDimension

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Splicing a resolution onto a short exact sequence -/

section Splice

variable {S : ShortComplex C} (F : ProjectiveResolution S.X₁)

/-- The complex `⋯ → F₁ → F₀ → P` built from a short exact sequence `S : 0 → Z → P → Y → 0` and a
projective resolution `F` of `Z`: it is `P` in degree `0` and `F.complex.X i` in degree `i + 1`,
the differential in degree `1` being the composite `F₀ → Z → P`. -/
private noncomputable def spliceComplex : ChainComplex C ℕ :=
  F.complex.augment (πZero F ≫ S.f) (by rw [← Category.assoc, d_comp_πZero, zero_comp])

private lemma πZero_comp_f_comp_g : (πZero F ≫ S.f) ≫ S.g = 0 := by
  rw [Category.assoc, S.zero, comp_zero]

/-- The augmentation of the spliced complex is `P → Y`. -/
private noncomputable def spliceπ : spliceComplex F ⟶ (single₀ C).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, πZero_comp_f_comp_g F⟩

private lemma spliceπ_f_zero : (spliceπ F).f 0 = S.g :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The spliced complex is exact in the positive degrees: in degree `1` because `F₀ → Z` is a
cokernel of `F₁ → F₀` and `Z → P` is a monomorphism, and above that by exactness of `F`. -/
private lemma exactAt_spliceComplex_succ (hS : S.ShortExact) (n : ℕ) :
    (spliceComplex F).ExactAt (n + 1) := by
  have := hS.mono_f
  match n with
  | 0 => exact (exactAt_augment_one _ _ _).2 (exact_of_comp_mono (exact₀' F) _)
  | (n + 1) => exact (exactAt_augment_succ_succ _ _ _ n).2 (F.complex_exactAt_succ n)

/-- **Splicing.** Let `0 → Z → P → Y → 0` be a short exact sequence and let `Q` be a class of
objects containing `P`. A resolution `F` of `Z` by projective objects of `Q` is prepended to `P` to
give a resolution of `Y` by objects of `Q`, whose complex is `P` in degree `0` and
`F.complex.X i` in degree `i + 1`. -/
private noncomputable def prepend {Q : ObjectProperty C} (hS : S.ShortExact)
    (hQ : ∀ n, Q (F.complex.X n)) (hP : Q S.X₂) : Q.LeftResolution S.X₃ where
  complex := spliceComplex F
  property n := match n with
    | 0 => hP
    | (n + 1) => hQ n
  π := spliceπ F
  quasiIso := ⟨fun n => by
    match n with
    | 0 =>
        have := epi_πZero F
        exact quasiIsoAt_zero_of _ (spliceπ_f_zero F)
          (πZero_comp_f_comp_g F)
          (exact_of_epi_comp (p := πZero F) hS.exact _) hS.epi_g
    | (n + 1) =>
        rw [quasiIsoAt_iff_exactAt']
        · exact exactAt_spliceComplex_succ F hS n
        · apply ChainComplex.exactAt_succ_single_obj⟩

private lemma prepend_complex_X_succ {Q : ObjectProperty C} (hS : S.ShortExact)
    (hQ : ∀ n, Q (F.complex.X n)) (hP : Q S.X₂) (i : ℕ) :
    (prepend F hS hQ hP).complex.X (i + 1) = F.complex.X i := rfl

/-- Splicing raises by exactly one the degree above which the terms of the resolution vanish. -/
private lemma isZero_prepend_complex_X {Q : ObjectProperty C} (hS : S.ShortExact)
    (hQ : ∀ n, Q (F.complex.X n)) (hP : Q S.X₂) {d : ℕ}
    (hF : ∀ i, d < i → IsZero (F.complex.X i)) (i : ℕ) (hi : d + 1 < i) :
    IsZero ((prepend F hS hQ hP).complex.X i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [prepend_complex_X_succ]
  exact hF j (by omega)

end Splice

end Helpers

section Modules

variable {R : Type u} [Ring R]

/-- A finite module over a ring `R` small in the universe `v` is a quotient of a finite free module
in that universe. This is `Module.exists_finite_presentation` with the commutativity of `R`
dropped, which its proof does not use. -/
private lemma exists_surjective_of_free_of_finite (R : Type u) [Ring R] [Small.{v} R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Free R P)
      (_ : Module.Finite R P) (f : P →ₗ[R] M), Function.Surjective f := by
  obtain ⟨m, f', hf'⟩ := Module.Finite.exists_fin' R M
  refine ⟨Fin m →₀ Shrink.{v, u} R, inferInstance, inferInstance, inferInstance, inferInstance,
    f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1, ?_⟩
  simpa using hf'

/-- A zero module is finite and projective. -/
private lemma projective_and_finite_of_isZero {N : ModuleCat.{v} R} (h : IsZero N) :
    Projective N ∧ Module.Finite R N := by
  refine ⟨h.projective, ?_⟩
  rw [ModuleCat.isZero_iff_subsingleton] at h
  infer_instance

/-- The terms of the resolution of a finite projective module `M` by itself are finite projective:
they are `M` in degree `0` and zero above it. -/
private lemma projective_and_finite_single₀ (M : ModuleCat.{v} R) [Projective M]
    [Module.Finite R M] (n : ℕ) :
    Projective (((single₀ (ModuleCat.{v} R)).obj M).X n) ∧
      Module.Finite R (((single₀ (ModuleCat.{v} R)).obj M).X n) := by
  match n with
  | 0 => exact ⟨inferInstance, inferInstanceAs (Module.Finite R M)⟩
  | (n + 1) =>
      exact projective_and_finite_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))

/-- Over a Noetherian ring, a finite module of projective dimension at most `d` admits a resolution
of length `d` by finite projective modules. The induction on `d` is dimension shifting along
`0 → Ker(P₀ → M) → P₀ → M → 0` for a finite free `P₀` covering `M`: the kernel is finite because
`R` is Noetherian, has projective dimension at most `d - 1`, and its resolution is prepended to
`P₀`. -/
@[ega "0 17.2.1" "One direction", ega "0 17.2.2"]
private lemma exists_leftResolution_projective_finite [IsNoetherianRing R] [Small.{v} R] (d : ℕ) :
    ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M d →
      ∃ F : ObjectProperty.LeftResolution
          (fun N : ModuleCat.{v} R => Projective N ∧ Module.Finite R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) := by
  induction d with
  | zero =>
      intro M hM h
      have : Projective M := projective_iff_hasProjectiveDimensionLT_one.2 h
      exact ⟨leftResolutionOfProjectiveResolution (ProjectiveResolution.self M)
        (projective_and_finite_single₀ M),
        fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  | succ d ih =>
      intro M hM h
      obtain ⟨P, _, _, _, _, f, hf⟩ := exists_surjective_of_free_of_finite.{v} R M
      let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
      have hP : Projective S.X₂ ∧ Module.Finite R S.X₂ :=
        ⟨ModuleCat.projective_of_free (Module.Free.chooseBasis R P),
          inferInstanceAs (Module.Finite R P)⟩
      obtain ⟨G, hG⟩ := ih S.X₁ (inferInstanceAs (Module.Finite R (LinearMap.ker f)))
        ((hS.hasProjectiveDimensionLT_X₃_iff d hP.1).1 h)
      exact ⟨prepend (G.toProjectiveResolution (fun n => (G.property n).1)) hS G.property hP,
        isZero_prepend_complex_X _ hS G.property hP hG⟩

end Modules

@[expose] public section

/-- **Stacks 0CXE.** Let `R` be a Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`.
Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, `M` admits a
resolution of length `d` by projectives — if and only if `M` admits a resolution
`0 → P_d → ⋯ → P₀ → M → 0` by finite projective modules. -/
@[ega "0 17.2.1" "partial", ega "0 17.2.2"]
public theorem solution {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution
          (fun N : ModuleCat.{v} R => Projective N ∧ Module.Finite R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) := by
  refine ⟨exists_leftResolution_projective_finite d M inferInstance, fun ⟨F, hF⟩ => ?_⟩
  have h : ∃ G : ObjectProperty.LeftResolution (isProjective (ModuleCat.{v} R)) M,
      ∀ i, d < i → IsZero (G.complex.X i) :=
    ⟨leftResolutionOfProjectiveResolution (F.toProjectiveResolution fun n => (F.property n).1)
      (fun n => (F.property n).1), hF⟩
  exact ((CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution M d).out 2 1).mp h

end

end Stacks.FiniteProjectiveResolution

/-!
# Finite projective resolutions and projective dimension over a Noetherian ring

Let `R` be a (left) Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`. The four
equivalent conditions of Lemma 0CXC — that `M` has projective dimension at most `d`, that `M`
admits a resolution `0 → P_d → ⋯ → P₀ → M → 0` by projectives, and the two conditions on the
`d`-th syzygy of a resolution by projectives — are, for a finite module over a Noetherian ring,
also equivalent to

`(6)` there is a resolution `0 → P_d → P_{d-1} → ⋯ → P₀ → M → 0` with all `Pᵢ` finite projective.

Only finiteness separates `(6)` from item 2 of Lemma 0CXC, and Noetherianness is what supplies
it: a resolution by finite projectives is one by projectives, so `(6)` implies item 2 over any
ring, while conversely one resolves `M` by finite free modules (possible because `R` is Noetherian
and `M` is finite) and truncates at the `d`-th syzygy, which is projective by Lemma 0CXC and is
finite because it is a submodule of a finite free module over a Noetherian ring.

## Main results

* `ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite`: over a
  Noetherian ring, a finite module has projective dimension at most `d` if and only if it admits
  a resolution of length `d` by finite projective modules.

## Implementation notes

The source adds `(6)` to a list of four conditions already known to be equivalent, so what is
stated here is the equivalence of `(6)` with the first of them,
`CategoryTheory.HasProjectiveDimensionLE M d`. Together with
`CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution` (Stacks 0CXC) this is the source's
five-fold equivalence; restating the other three items would only duplicate that lemma's `TFAE`.

A resolution by finite projective modules is the resolution of Stacks 00LQ for the class of
objects of `ModuleCat R` that are projective and finite over `R`: a
`CategoryTheory.ObjectProperty.LeftResolution (fun N => Projective N ∧ Module.Finite R N) M`,
that is, an `ℕ`-indexed chain complex `F.complex` of finite projective modules together with a
quasi-isomorphism `F.π` to `M` placed in degree `0`, which is exactness of `⋯ → P₁ → P₀ → M → 0`.
This is the shape in which Stacks 0CXC, 0CXD and 00O7 state resolutions, with
`Module.Free R N ∧ Module.Finite R N` there in place of `Projective N ∧ Module.Finite R N` here.
Projectivity is the categorical `CategoryTheory.Projective N`, the property `isProjective` in
which Stacks 0CXC states item 2, so that `(6)` visibly strengthens that item; it agrees with
`Module.Projective R N`, by `ModuleCat.projective_of_categoryTheory_projective` in one direction
and `ModuleCat.projective_of_module_projective` in the other.
That the resolution has *length `d`* is the vanishing of its terms in degrees `> d`; exactness in
degree `d` then makes `P_d → P_{d-1}` a monomorphism, which is the source's leading `0 →`, and
`P_d` is allowed to be zero, so `≤ d` is the source's assertion and not a weakening of it.

Generality beyond the source: the source's `R` is commutative, but neither side of the equivalence
and no step of the argument uses commutativity, so `R` is an arbitrary ring, `IsNoetherianRing R`
being left Noetherianness and `ModuleCat R` the category of left `R`-modules. Modules are objects
of `ModuleCat.{v} R` for `R : Type u` and `Small.{v} R`, which is where Mathlib puts the
smallness needed for `ModuleCat.enoughProjectives`, hence for finite free covers to exist in that
universe; the source's situation is `v = u`, where `Small.{u} R` is automatic.

Noetherianness enters only through the finiteness of the syzygies of `M`, so the natural
generality is a coherent ring and a finitely presented module. Mathlib has no class of coherent
rings, so the source's hypothesis is kept; over it `Module.Finite R M` and
`Module.FinitePresentation R M` agree, by `Module.finitePresentation_iff_finite`.

Faithfulness. (1) No hypothesis is dead. `Module.Finite R M` is used already at `d = 0`: an
infinite-dimensional vector space over a field is projective, so it satisfies the left-hand side
with `d = 0`, but a resolution of it of length `0` by finite projectives would exhibit it as a
finite module. Noetherianness is used for the forward implication and cannot be dropped from it as
stated: the right-hand side forces `Module.FinitePresentation R M`, the kernel of `P₀ → M` being
the image of the finite module `P₁`, whereas over a ring that is not Noetherian a finite module
need not be finitely presented. Smallness is what makes finite free modules available in the
category at all, and `d` and `M` are used by both sides. (2) The scalars and the base are the
source's: `M` is a module over the Noetherian ring `R` itself, the resolving modules are
projective and finite over that same `R`, the differentials are `R`-linear and the `Ext` groups
behind `HasProjectiveDimensionLE` are computed in `ModuleCat R`; no localisation or change of
rings occurs. (3) The map the source names is pinned: a `LeftResolution` carries its augmentation
`P₀ → M` as the field `F.π`, and exactness of `⋯ → P₁ → P₀ → M → 0` is a condition on that map,
so the complex resolves `M` along a given morphism rather than being merely exact. (4) The
instantiation is not degenerate: for `R = ℤ`, `M = ℤ ⧸ 2ℤ` and `d = 1` both sides hold, the
resolution being `0 → ℤ → ℤ → M → 0` with the first map multiplication by `2`; whereas over the
Noetherian ring `k[x]/(x²)` the finite module `k = R/(x)` satisfies neither side for any `d`,
having no finite resolution by projectives (Stacks 0A5Q). So neither direction is vacuous.

## References

* [StacksProject 0CXE](https://stacks.math.columbia.edu/tag/0CXE)
* [StacksProject 0CXC](https://stacks.math.columbia.edu/tag/0CXC)
* [StacksProject 00LP](https://stacks.math.columbia.edu/tag/00LP)
* [StacksProject 00LQ](https://stacks.math.columbia.edu/tag/00LQ)
-/

@[expose] public section

open CategoryTheory Limits in
/-- **Stacks 0CXE.** Let `R` be a Noetherian ring, let `M` be a finite `R`-module and let `d : ℕ`.
Then `M` has projective dimension at most `d` — equivalently, by Stacks 0CXC, `M` has a resolution
of length `d` by projectives — if and only if `M` has a resolution `0 → P_d → ⋯ → P₀ → M → 0` by
*finite projective* modules, that is, a left resolution `F` of `M` by projective modules that are
finite over `R`, with `F.complex.X i = 0` for `i > d`. -/
@[stacks 0CXE "Condition (6) is added to Lemma 0CXC by stating its equivalence with item 1 of
that lemma's `TFAE`. A resolution `0 → P_d → ⋯ → P₀ → M → 0` by finite projectives is an
`ObjectProperty.LeftResolution` for the class of finite projective modules (00LQ), the notion
0CXC, 0CXD and 00O7 use, vanishing in degrees `> d`; stated for a not necessarily commutative
ring. See the module docstring.", ega "0 17.2.2"]
public theorem ModuleCat.hasProjectiveDimensionLE_iff_exists_leftResolution_projective_finite
    {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R] (M : ModuleCat.{v} R)
    [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔
      ∃ F : ObjectProperty.LeftResolution
          (fun N : ModuleCat.{v} R => Projective N ∧ Module.Finite R N) M,
        ∀ i, d < i → IsZero (F.complex.X i) :=
  Stacks.FiniteProjectiveResolution.solution M d

end
