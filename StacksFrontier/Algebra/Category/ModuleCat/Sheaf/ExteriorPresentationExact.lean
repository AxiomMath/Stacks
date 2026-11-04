module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 01CJ for exterior powers

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and
`M₂ --q--> M₁ --p--> M ⟶ 0` a presentation of sheaves of `O♯`-modules. Stacks Tag 01CJ asserts
that in every degree `n ≥ 1` the two sequences

`M₂ ⊗ ⋀^{n-1}(M₁) ⟶ ⋀ⁿ(M₁) ⟶ ⋀ⁿ(M) ⟶ 0` and
`M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

are exact, and the proof the source gives is a single citation to the module-level Tag 00DO. The
symmetric half is already on this branch — `SheafOfModules.SymPresentation.epi_symDesc_app` and
`SheafOfModules.SymPresentation.symmetricPresentation_exact`. **This file proves the exterior
half, both clauses**, and with it Tag 01CJ in full.

It is the symmetric argument transcribed, and a large part of that argument transfers *verbatim*
rather than being restated: the following are used from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact`, where they are stated
for an abstract sheaf of graded algebras or for a bare presentation and mention no symmetry at
all.

* `SheafOfModules.SymPresentation.valHom` and `epi_iff_surjective_stalkMapL`: a morphism of
  sheaves of modules read as one of the underlying presheaves of modules, and epimorphy as
  surjectivity of the stalk maps.
* `SheafOfModules.SymPresentation.exists_common_germ` and `exists_common_germ₂`: a finite family
  of germs, and one germ of `P` together with `Fin n` germs of `Q`, represented over a single
  open.
* `Stacks.GradedAlgebra.homogeneousProd_succ`: the ordered product of `k + 1` degree-one local
  sections peeled on the **left**, with the transport from degree `1 + k` to degree `k + 1`.
* `SheafOfModules.SymPresentation.eqToHom_val_app`: the complex's categorical `eqToHom` degree
  transport acts on local sections as `Stacks.degCast`.
* `SheafOfModules.SymPresentation.range_stalkMapL_eq_ker_stalkMapL`: exactness of a
  presentation read on a stalk. (Its own input
  `SheafOfModules.SymPresentation.stalkMapL_comp_eq_zero` — a composite of morphisms of sheaves
  of modules which is zero is zero on every stalk — is therefore reused too, though not named
  below.)

What is exterior-specific is the four inputs the germ computation is composed with: the exterior
clause of Tag 01CG (`SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`) and of Tag 01CH, bundled as
`SheafOfModules.exteriorPowerStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`;
`exterior_power_presentation` in place of `symmetric_power_presentation`; and
`ExteriorAlgebra.powExtₛₗ` in place of `SymPow.ext_of_prod_ι` as the extension principle.
`SheafOfModules.GradedAlgebra.presentationShortComplex` is already the construction common to the
two halves, with `exteriorPresentationShortComplex` and `symmetricPresentationShortComplex` its
two instances, and `PresheafOfModules.tensorSheafStalkEquiv` (Tag 01CB) is algebra-agnostic.

## Main definitions

* `SheafOfModules.ExtPresentation.extDesc`: the homomorphism of sheaves of graded algebras
  induced by `p : M₁ ⟶ M` between an exterior algebra of `M₁` and one of `M`. Its degree-`n`
  component is the second map of the sequence; it is
  `SheafOfModules.GradedAlgebra.IsUniversal.descComp`.
* `SheafOfModules.ExtPresentation.extComplex`: the three-term complex of Tag 01CJ for exterior
  powers in degree `k + 1`, namely
  `SheafOfModules.GradedAlgebra.exteriorPresentationShortComplex` with the target degree fixed at
  `((k + 1 : ℕ) : ℤ)`. The abbreviation exists to keep that degree, and the proof of
  `1 + k = k + 1` it is transported along, out of every statement below.
* `SheafOfModules.ExtPresentation.extTensorStalkEquiv`: **the stalk of the first term of the
  sequence**, `(M₂ ⊗ ⋀^k(M₁))ₓ ≃ₗ[O_x] M₂ₓ ⊗ ⋀^k(M₁ₓ)`: the stalk of a tensor product
  (Tag 01CB) followed by the exterior clause of Tag 01CH in the second factor.

## Main results

* `ExteriorAlgebra.ιMulti_succ_head`: Mathlib's `ExteriorAlgebra.ιMulti_succ_apply` with the tail
  spelled `fun i => v i.succ` instead of `Matrix.vecTail v`, which is the spelling the degree
  bookkeeping produces.
* `SheafOfModules.ExtPresentation.exteriorPowerStalkEquiv_extDesc`: **the second map of the
  sequence is `⋀ⁿ` of the stalk of `p`**, read through the exterior clause of Tag 01CH. Proved on
  wedges of germs, then on wedges of arbitrary stalk elements, then everywhere by
  `ExteriorAlgebra.powExtₛₗ`.
* `SheafOfModules.ExtPresentation.epi_extDesc_app`: **the surjectivity clause of Tag 01CJ for
  exterior powers.** If `p` is an epimorphism then so is `⋀ⁿ(p)`, in every degree.
* `SheafOfModules.ExtPresentation.range_beta_eq_ker_extMap`: **Tag 00DO on a stalk**, the
  exterior half of `exterior_power_presentation` applied to the stalk maps.
* `SheafOfModules.ExtPresentation.stalkMapL_extDesc_eq_zero_iff`: **the kernel of the second map
  on each stalk** is the image of `m ⊗ y ↦ qₓ(m) ∧ y`.
* `SheafOfModules.ExtPresentation.stalkMapL_extComplex_f_germ` and
  `exteriorPowerStalkEquiv_extComplex_f_germ`: the stalk of the first map on the germ of
  `m ⊗ s₁ ∧ ⋯ ∧ s_k`, before and after the identifications of Tag 01CH.
* `SheafOfModules.ExtPresentation.exteriorPowerStalkEquiv_extComplex_f`: **the stalk of the first
  map of the sequence is `ExtPow.beta`**, the algebraic map `m ⊗ y ↦ qₓ(m) ∧ y` of Stacks 00DO.
* `SheafOfModules.ExtPresentation.exteriorPresentation_exact`: **Stacks Tag 01CJ for exterior
  powers.** The sequence is exact at the middle term and its second map is an epimorphism.

## Implementation notes

**What the tag now covers.** Tag 01CJ is the conjunction of two clauses for each of the symmetric
and the exterior powers: the second map is surjective, and the sequence is exact at the middle
term. All four are now proved, and the covering set is the four declarations
`SheafOfModules.SymPresentation.epi_symDesc_app`,
`SheafOfModules.SymPresentation.symmetricPresentation_exact`,
`SheafOfModules.ExtPresentation.epi_extDesc_app` and
`SheafOfModules.ExtPresentation.exteriorPresentation_exact`. Within each pair neither member
subsumes the other: the surjectivity clause holds in every degree and needs no exactness
hypothesis, while the exactness statement states the sequence of the source.

**The degree is reindexed once, in `extComplex`, and never again.** This is the symmetric file's
note verbatim, and it is the reason that file's two transport lemmas transfer.
`SheafOfModules.GradedAlgebra.generatorMul` lands in `A.piece (1 + k)` on the nose, while the
comparison of Tag 01CH is indexed by a natural number and so lives at `A.piece ((k + 1 : ℕ) : ℤ)`;
the two degrees are equal but not definitionally so, since `Nat.add` recurses on its second
argument. `extComplex` fixes the target degree and
`SheafOfModules.SymPresentation.eqToHom_val_app` turns the complex's `eqToHom` transport into the
`Stacks.degCast` that `Stacks.GradedAlgebra.homogeneousProdLeft` is defined with. Both transport
lemmas are proved by `subst` on an equality of degrees whose right-hand side is a *variable*,
which is the only way either is provable: with the degree a numeral neither `eqToHom` nor
`degCast` reduces.

**No statement below writes a numeral degree.** `ExteriorAlgebra` is a `CliffordAlgebra` quotient
of `TensorAlgebra`, so with a numeral degree `whnf` unfolds the exterior power through
`Submodule.mul` and `Submodule.span` into that quotient and exhausts the heartbeat limit while
elaborating the *statement*. Every degree here is `k`, `k + 1` or `n` for a variable; the one
numeral that appears, in `ι : M₁ ⟶ A'.piece 1`, is the degree of a piece of an abstract sheaf of
graded algebras, where there is nothing to unfold.

**`Fin.cons` appears only inside a proof.** `stalkMapL_extComplex_f_germ` and
`exteriorPowerStalkEquiv_extComplex_f_germ` take the family of `k + 1` sections as a variable
`s'` together with its two defining equations `s' 0 = q(m)` and `s' i.succ = s i`, rather than
being stated at `Fin.cons (q m) s`: in a statement `Fin.cons` leaves its motive a metavariable.
The instance `Fin.cons (q.val.app _ m) ss` is supplied at the point of use inside
`exteriorPowerStalkEquiv_extComplex_f`, where `Fin.cons_zero` and `Fin.cons_succ` discharge the
two equations.

**Named implicit arguments at `exteriorPresentationShortComplex`.** `extComplex` passes
`(Osharp := …)`, `(A := …)` and the rest by name. Left to unification those implicits stay
metavariables — `presentationShortComplex` carries three instance arguments
(`HasSheafCompose`, `WEqualsLocallyBijective`, `HasWeakSheafify`) whose synthesis is postponed
with the site still unknown — and the application then fails with the site universes defaulted to
`0`. This is a bookkeeping wart, not a mathematical constraint, and it is the symmetric file's
wart too.

**The module argument of `ExteriorAlgebra.ι` has to be pinned.** In
`exteriorPowerStalkEquiv_extComplex_f_germ` the generator is written
`ExteriorAlgebra.ι (M := ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) …`. `ExteriorAlgebra.ι` takes
its module implicitly, and the argument it is applied to is a value of
`PresheafOfModules.stalkMapL x (valHom q)`, whose codomain is spelled as the stalk of
`(PresheafOfModules.restrictScalars …).obj M₁.val`. That is the same type as the stalk of `M₁.val`
but not the same term, so without the ascription the two factors of the product land in two
spellings of one exterior algebra and `HMul` fails to synthesize. The symmetric file does not hit
this because `SymmetricAlgebra.ι` takes its module explicitly.

**Wedges, not products, and `ExtPow.beta` wedges on the left.** `ExteriorAlgebra` is not
commutative, so the spanning family is the ordered product `ExteriorAlgebra.ιMulti`, and
`ExtPow.beta k g` sends `m ⊗ y` to `ι(g m) * y` — the new factor on the **left**. That is the same
side `Stacks.GradedAlgebra.homogeneousProd_succ` peels on, so no reordering appears anywhere and
`ExteriorAlgebra.ιMulti_succ_head` is the only bridge needed. Nothing here uses
`ExteriorAlgebra.ιMulti_succ_last`.

**`rw` and `simp` are avoided in favour of `congrArg`, `congrArg₂` and `Eq.trans`.** The terms
below contain the stalk colimit and the `CliffordAlgebra` quotient, and `kabstract` — which `rw`
uses to build its motive, and which calls `whnf` on subterms — exhausts the heartbeat limit on
them. For the same reason the existentials of `exists_common_germ₂` and of
`exists_common_germ` are eliminated with `Exists.elim` rather than with `obtain` whenever the
ambient goal is one of these equations.

**Universes.** The single universe `u` carries the space, the sheaf of rings and the modules, and
the ring universe and the module universe of the graded algebras are equal. Both are inherited,
not chosen: Mathlib's module structure on the stalk of a presheaf of modules
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) exists only for `X : TopCat.{u}`,
`R : X.Presheaf CommRingCat.{u}` and modules in `u`; the development of Tag 01CB that
`PresheafOfModules.tensorSheafStalkEquiv` transports is stated for
`AlgebraicGeometry.RingedSpace.{u, u}`; and `SheafOfModules.sectionwiseExteriorAlgebra`, which
the comparison of Tag 01CG is built against, exists only at `GradedAlgebra.{u, u}`. Tag 01CJ is
stated in the equal-universe case, so nothing the source says is narrowed.
`ExteriorAlgebra.ιMulti_succ_head`, which mentions no sheaf, is universe-polymorphic.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open SheafOfModules.SymPresentation
open scoped TensorProduct

universe u

namespace ExteriorAlgebra

/-- **Peeling the first factor off a wedge**, with the tail written as a reindexing rather than
as `Matrix.vecTail`. This is Mathlib's `ExteriorAlgebra.ιMulti_succ_apply` with
`Matrix.vecTail v` spelled `fun i => v i.succ`, which is the spelling the degree bookkeeping of
`Stacks.GradedAlgebra.homogeneousProd_succ` produces. -/
theorem ιMulti_succ_head {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (n : ℕ) (v : Fin (n + 1) → M) :
    ιMulti R (n + 1) v = ι R (v 0) * ιMulti R n fun i => v i.succ :=
  ιMulti_succ_apply v

end ExteriorAlgebra

namespace SheafOfModules.ExtPresentation

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M₂ M₁ M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A' B' : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ι : M₁ ⟶ A'.piece 1) (κ : M ⟶ B'.piece 1)
  (hA' : GradedAlgebra.IsExteriorAlgebra A' ι) (hB' : GradedAlgebra.IsExteriorAlgebra B' κ)
  (p : M₁ ⟶ M)

/-! ### The second map of the presentation sequence -/

/-- The homomorphism of sheaves of graded algebras induced by `p : M₁ ⟶ M` between an exterior
algebra of `M₁` and an exterior algebra of `M`: the second map of the sequence of Tag 01CJ is its
degree-`n` component. -/
noncomputable abbrev extDesc : GradedAlgebra.UnitalHom A' B' :=
  hA'.isUniversal.descComp p κ (GradedAlgebra.squareZero_comp p hB'.1)

/-- In degree one, `extDesc` sends the image under `ι` of a local section `y` of `M₁` to the
image under `κ` of `p y`. -/
theorem extDesc_app_one (U : (Opens ↥X)ᵒᵖ) (y : M₁.val.obj U) :
    ((extDesc ι κ hA' hB' p).app 1).val.app U (ι.val.app U y) =
      κ.val.app U (p.val.app U y) :=
  hom_congr_app_apply
    (hA'.isUniversal.descComp_extends p κ (GradedAlgebra.squareZero_comp p hB'.1)) U y

/-- `SheafOfModules.exteriorPowerStalkEquiv` read backwards: the wedge of the degree-one
generators of `n` germs is the germ of the ordered product of the images of `n` representing
local sections. -/
theorem exteriorPowerStalkEquiv_symm_ιMulti (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M₁.val.obj (op U)) :
    (exteriorPowerStalkEquiv A' ι hA' n x).symm
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
          fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)) =
      TopCat.Presheaf.germ (A'.piece (n : ℤ)).val.presheaf U x hx
        (A'.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => ι.val.app (op U) (s i)) :=
  ((exteriorPowerStalkEquiv A' ι hA' n x).symm_apply_eq).2
    (exteriorPowerStalkEquiv_germ_homogeneousProd A' ι hA' n x U hx s).symm

/-- **The comparison homomorphism is `⋀ⁿ` of `p` on stalks, on a wedge of germs.** -/
theorem exteriorPowerStalkEquiv_extDesc_ιMulti_germ (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M₁.val.obj (op U)) :
    exteriorPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ)))
          ((exteriorPowerStalkEquiv A' ι hA' n x).symm
            (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
              fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)))) =
      exteriorPower.map n (PresheafOfModules.stalkMapL x (valHom p))
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
          fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)) := by
  have step1 : PresheafOfModules.stalkMapL x (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ)))
        ((exteriorPowerStalkEquiv A' ι hA' n x).symm
          (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
            fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i))) =
      TopCat.Presheaf.germ (B'.piece (n : ℤ)).val.presheaf U x hx
        (B'.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => κ.val.app (op U) (p.val.app (op U) (s i))) := by
    refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x
        (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ))))
      (exteriorPowerStalkEquiv_symm_ιMulti ι hA' n x U hx s)) ?_
    refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hx _) ?_
    refine congrArg (TopCat.Presheaf.germ (B'.piece (n : ℤ)).val.presheaf U x hx) ?_
    refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
      (extDesc ι κ hA' hB' p) (op U) n fun i => ι.val.app (op U) (s i)) ?_
    exact congrArg (B'.toPresheafGradedAlgebra.homogeneousProd (op U) n)
      (funext fun i => extDesc_app_one ι κ hA' hB' p (op U) (s i))
  refine Eq.trans (congrArg (exteriorPowerStalkEquiv B' κ hB' n x) step1) ?_
  refine Eq.trans (exteriorPowerStalkEquiv_germ_homogeneousProd B' κ hB' n x U hx
    fun i => p.val.app (op U) (s i)) (Eq.symm ?_)
  refine Eq.trans (exteriorPower.map_apply_ιMulti
    (PresheafOfModules.stalkMapL x (valHom p)) _) ?_
  exact congrArg (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n)
    (funext fun i => PresheafOfModules.stalkMapL_germ x (valHom p) U hx (s i))

/-- The same comparison on a wedge of arbitrary stalk elements: a finite family of germs is
represented by sections over one open neighbourhood. -/
theorem exteriorPowerStalkEquiv_extDesc_ιMulti (n : ℕ) (x : ↥X)
    (m : Fin n → ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) :
    exteriorPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ)))
          ((exteriorPowerStalkEquiv A' ι hA' n x).symm
            (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n m))) =
      exteriorPower.map n (PresheafOfModules.stalkMapL x (valHom p))
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n m) := by
  refine (SymPresentation.exists_common_germ M₁.val.presheaf x n m).elim fun U hU =>
    hU.elim fun hx hU' => hU'.elim fun s hs => ?_
  have hm : m = fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i) := (funext hs).symm
  subst hm
  exact exteriorPowerStalkEquiv_extDesc_ιMulti_germ ι κ hA' hB' p n x U hx s

/-- If `e₂ ∘ f ∘ e₁⁻¹ = g` for linear equivalences `e₁`, `e₂`, then `e₂ (f t) = g (e₁ t)`. -/
private theorem equiv_comp_apply_eq {R M N P Q : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N] [Module R P]
    [Module R Q] (e₁ : M ≃ₗ[R] N) (e₂ : P ≃ₗ[R] Q) (f : M →ₗ[R] P) (g : N →ₗ[R] Q)
    (h : e₂.toLinearMap.comp (f.comp e₁.symm.toLinearMap) = g) (t : M) : e₂ (f t) = g (e₁ t) :=
  (congrArg (fun z => e₂ (f z)) (e₁.symm_apply_apply t).symm).trans (DFunLike.congr_fun h _)

/-- **The comparison homomorphism is `⋀ⁿ` of `p` on stalks.** The stalk at `x` of the second map
of the sequence of Tag 01CJ is the `n`-th exterior power of the stalk of `p`, read through the
identification `SheafOfModules.exteriorPowerStalkEquiv` of the stalks of the exterior powers with
the exterior powers of the stalks. -/
theorem exteriorPowerStalkEquiv_extDesc (n : ℕ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk (A'.piece (n : ℤ)).val.presheaf x)) :
    exteriorPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ))) t) =
      exteriorPower.map n (PresheafOfModules.stalkMapL x (valHom p))
        (exteriorPowerStalkEquiv A' ι hA' n x t) := by
  have key : (exteriorPowerStalkEquiv B' κ hB' n x).toLinearMap.comp
        ((PresheafOfModules.stalkMapL x (valHom ((extDesc ι κ hA' hB' p).app (n : ℤ)))).comp
          (exteriorPowerStalkEquiv A' ι hA' n x).symm.toLinearMap) =
      exteriorPower.map n (PresheafOfModules.stalkMapL x (valHom p)) :=
    ExteriorAlgebra.powExtₛₗ fun m =>
      exteriorPowerStalkEquiv_extDesc_ιMulti ι κ hA' hB' p n x m
  exact equiv_comp_apply_eq _ _ _ _ key t

/-- **The surjectivity clause of Stacks Tag 01CJ for exterior powers.** If `p : M₁ ⟶ M` is an
epimorphism of sheaves of modules on a space, `A'` is an exterior algebra of `M₁` and `B'` an
exterior algebra of `M`, then the induced map `⋀ⁿ(M₁) ⟶ ⋀ⁿ(M)` is an epimorphism in every degree.
This is the clause `⟶ 0` of the sequence Tag 01CJ asserts.

The hypothesis `n ≥ 1` of the source is not needed: the statement holds in degree `0` too, where
both powers are the structure sheaf. -/
@[stacks 01CJ "exterior case, surjectivity clause: the second map of the sequence is an \
epimorphism, in every degree and with no exactness hypothesis. Exactness at the middle term is \
covered, by `SheafOfModules.ExtPresentation.exteriorPresentation_exact` below, which carries \
that clause and states the sequence of the source. The symmetric counterparts are \
`SheafOfModules.SymPresentation.epi_symDesc_app` and \
`SheafOfModules.SymPresentation.symmetricPresentation_exact`."]
theorem epi_extDesc_app [Epi p] (n : ℕ) : Epi ((extDesc ι κ hA' hB' p).app (n : ℤ)) := by
  refine (SymPresentation.epi_iff_surjective_stalkMapL
    ((extDesc ι κ hA' hB' p).app (n : ℤ))).2 fun x w => ?_
  have hp : Function.Surjective (PresheafOfModules.stalkMapL x (valHom p)) :=
    (SymPresentation.epi_iff_surjective_stalkMapL p).1 inferInstance x
  obtain ⟨v, hv⟩ := exteriorPower.map_surjective (n := n) hp
    (exteriorPowerStalkEquiv B' κ hB' n x w)
  refine ⟨(exteriorPowerStalkEquiv A' ι hA' n x).symm v,
    (exteriorPowerStalkEquiv B' κ hB' n x).injective ?_⟩
  refine Eq.trans (exteriorPowerStalkEquiv_extDesc ι κ hA' hB' p n x _) ?_
  exact Eq.trans (congrArg (exteriorPower.map n (PresheafOfModules.stalkMapL x (valHom p)))
    ((exteriorPowerStalkEquiv A' ι hA' n x).apply_symm_apply v)) hv

/-! ### Stacks 00DO transported across the stalk -/

variable (q : M₂ ⟶ M₁)

/-- **Stacks Tag 00DO on a stalk, exterior half.** If the sequence of stalk modules
`M₂ₓ ⟶ M₁ₓ ⟶ Mₓ ⟶ 0` is exact, then the image of `m ⊗ y ↦ qₓ(m) ∧ y` is the kernel of
`⋀^{k+1}(pₓ)`. This is `exterior_power_presentation` — the exterior half of Stacks 00DO —
applied to the stalk maps. -/
theorem range_beta_eq_ker_extMap [Epi p] (k : ℕ) (x : ↥X)
    (hq : LinearMap.range (PresheafOfModules.stalkMapL x (valHom q)) =
      LinearMap.ker (PresheafOfModules.stalkMapL x (valHom p))) :
    LinearMap.range (ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q))) =
      LinearMap.ker (exteriorPower.map (k + 1)
        (PresheafOfModules.stalkMapL x (valHom p))) :=
  (exterior_power_presentation (PresheafOfModules.stalkMapL x (valHom q))
    (PresheafOfModules.stalkMapL x (valHom p))
    ((SymPresentation.epi_iff_surjective_stalkMapL p).1 inferInstance x) hq k).2

/-- **The kernel of the second map of the sequence of Tag 01CJ, on a stalk.** A germ of a local
section of `⋀^{k+1}(M₁)` is killed by the comparison homomorphism exactly when the corresponding
element of `⋀^{k+1}(M₁ₓ)` is a sum of wedges of a germ in the image of `qₓ` with an element of
`⋀^k(M₁ₓ)`. -/
theorem stalkMapL_extDesc_eq_zero_iff [Epi p] (k : ℕ) (x : ↥X)
    (hq : LinearMap.range (PresheafOfModules.stalkMapL x (valHom q)) =
      LinearMap.ker (PresheafOfModules.stalkMapL x (valHom p)))
    (t : ↑(TopCat.Presheaf.stalk (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf x)) :
    PresheafOfModules.stalkMapL x
          (valHom ((extDesc ι κ hA' hB' p).app ((k + 1 : ℕ) : ℤ))) t = 0 ↔
      exteriorPowerStalkEquiv A' ι hA' (k + 1) x t ∈
        LinearMap.range (ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q))) := by
  have hker := range_beta_eq_ker_extMap p q k x hq
  have hcomp := exteriorPowerStalkEquiv_extDesc ι κ hA' hB' p (k + 1) x t
  have hmem_iff := SetLike.ext_iff.mp hker (exteriorPowerStalkEquiv A' ι hA' (k + 1) x t)
  refine ⟨fun h0 => hmem_iff.mpr (LinearMap.mem_ker.2 (hcomp.symm.trans
    ((congrArg (exteriorPowerStalkEquiv B' κ hB' (k + 1) x) h0).trans (map_zero _)))),
    fun hmem => ?_⟩
  exact (exteriorPowerStalkEquiv B' κ hB' (k + 1) x).injective
    (hcomp.trans ((LinearMap.mem_ker.1 (hmem_iff.mp hmem)).trans (map_zero _).symm))

/-! ### The complex of Tag 01CJ in degree `k + 1` -/

variable (hqp : q ≫ p = 0)

/-- The three-term complex of Tag 01CJ for exterior powers in degree `k + 1`:
`M₂ ⊗ ⋀^k(M₁) ⟶ ⋀^{k+1}(M₁) ⟶ ⋀^{k+1}(M)`. -/
noncomputable abbrev extComplex (k : ℕ) :
    ShortComplex (SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  GradedAlgebra.exteriorPresentationShortComplex
    (Osharp := Osharp) (M₂ := M₂) (M₁ := M₁) (M := M) (A := A') (B := B') (ι := ι) (κ := κ)
    hA' hB'.1 q p hqp (k : ℤ) ((k + 1 : ℕ) : ℤ) (by omega)

/-- The stalk of the first term of the sequence of Tag 01CJ: the stalk of `M₂ ⊗ ⋀^k(M₁)` is
`M₂ₓ ⊗ ⋀^k(M₁ₓ)`. This is the stalk of a tensor product
(`PresheafOfModules.tensorSheafStalkEquiv`, Tag 01CB) followed by the exterior clause of Tag 01CH
in the second factor. -/
noncomputable def extTensorStalkEquiv (k : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp M₂ (A'.piece (k : ℤ))).presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
    ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^k
        ↑(TopCat.Presheaf.stalk M₁.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp M₂ (A'.piece (k : ℤ)) x).trans
    (TensorProduct.congr (LinearEquiv.refl _ _) (exteriorPowerStalkEquiv A' ι hA' k x))

/-- `extTensorStalkEquiv` sends the germ of `m ⊗ (ι s₀ ⋯ ι sₖ₋₁)` to the tensor product of the
germ of `m` with the wedge of the germs of the `sᵢ`. -/
theorem extTensorStalkEquiv_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U)) :
    extTensorStalkEquiv ι hA' k x
        (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
          (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
            fun i => ι.val.app (op U) (s i))) =
      TopCat.Presheaf.germ M₂.val.presheaf U x hx m ⊗ₜ
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) k
          fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i) := by
  refine Eq.trans (congrArg
    (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M₂.val.presheaf x)) (exteriorPowerStalkEquiv A' ι hA' k x))
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x
      U hx m _)) ?_
  refine Eq.trans (TensorProduct.congr_tmul _ _ _ _) ?_
  exact congrArg (fun y => TopCat.Presheaf.germ M₂.val.presheaf U x hx m ⊗ₜ y)
    (exteriorPowerStalkEquiv_germ_homogeneousProd A' ι hA' k x U hx s)

/-! ### The first map of the complex, on the germ of a pure tensor -/

/-- **The first map of the sequence of Tag 01CJ on a germ.** The stalk of
`SheafOfModules.GradedAlgebra.generatorMul (q ≫ ι) k` carries the germ of the image of
`m ⊗ s₁ ⋯ s_k` to the germ of the ordered product `q(m) · s₁ ⋯ s_k`, in degree `k + 1`.

The degree bookkeeping is the whole content, and it is the symmetric file's verbatim: `A.mul 1 k`
lands in `A.piece (1 + k)`, the complex transports that to `A.piece ((k + 1 : ℕ) : ℤ)` along
`eqToHom`, and the result is the *left*-handed ordered product
`Stacks.GradedAlgebra.homogeneousProdLeft`, which agrees with the right-handed
`Stacks.GradedAlgebra.homogeneousProd` that the germ formula of Tag 01CH is stated with. -/
theorem stalkMapL_extComplex_f_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U))
    (s' : Fin (k + 1) → M₁.val.obj (op U)) (hs0 : s' 0 = q.val.app (op U) m)
    (hs : ∀ i : Fin k, s' i.succ = s i) :
    PresheafOfModules.stalkMapL x (valHom (extComplex ι κ hA' hB' p q hqp k).f)
        (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
          (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
            fun i => ι.val.app (op U) (s i))) =
      TopCat.Presheaf.germ (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf U x hx
        (A'.toPresheafGradedAlgebra.homogeneousProd (op U) (k + 1)
          fun i => ι.val.app (op U) (s' i)) := by
  have hk : (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ) := by omega
  refine Eq.trans (congrArg
    (PresheafOfModules.stalkMapL x (valHom (extComplex ι κ hA' hB' p q hqp k).f))
    (PresheafOfModules.tensorSheafGerm_eq Osharp M₂ (A'.piece (k : ℤ)) x U hx m _)) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hx _) ?_
  refine congrArg (TopCat.Presheaf.germ (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf U x hx) ?_
  refine Eq.trans (GradedAlgebra.presentationShortComplex_f_unit hA'.isUniversal q p
    (GradedAlgebra.squareZero_comp p hB'.1) hqp (k : ℤ) ((k + 1 : ℕ) : ℤ) hk (op U) m _) ?_
  refine Eq.trans (SymPresentation.eqToHom_val_app A'.piece hk (op U) _) ?_
  refine Eq.symm (Eq.trans (A'.toPresheafGradedAlgebra.homogeneousProd_succ (op U) k hk
    (fun i => ι.val.app (op U) (s' i))) ?_)
  exact congrArg₂
    (fun z y => Stacks.degCast
      (F := fun l : ℤ => ((A'.piece l).val.obj (op U) : Type u)) hk
      ((A'.mul 1 (k : ℤ)).app (op U) z y))
    (congrArg (ι.val.app (op U)) hs0)
    (congrArg (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k)
      (funext fun i => congrArg (ι.val.app (op U)) (hs i)))

/-- **The first map of the sequence of Tag 01CJ read through the stalk identifications, on a
germ.** Under the exterior clause of Tag 01CH the stalk of the first map carries
`germ m ⊗ germ s₁ ∧ ⋯ ∧ germ s_k` to `qₓ(germ m) ∧ germ s₁ ∧ ⋯ ∧ germ s_k`, which is what
`ExtPow.beta` does. -/
theorem exteriorPowerStalkEquiv_extComplex_f_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U))
    (s' : Fin (k + 1) → M₁.val.obj (op U)) (hs0 : s' 0 = q.val.app (op U) m)
    (hs : ∀ i : Fin k, s' i.succ = s i) :
    (exteriorPowerStalkEquiv A' ι hA' (k + 1) x
          (PresheafOfModules.stalkMapL x (valHom (extComplex ι κ hA' hB' p q hqp k).f)
            (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
              (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
                fun i => ι.val.app (op U) (s i)))) :
        ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) =
      ExteriorAlgebra.ι (M := ↑(TopCat.Presheaf.stalk M₁.val.presheaf x))
            ↑(TopCat.Presheaf.stalk Osharp.obj x)
            (PresheafOfModules.stalkMapL x (valHom q)
              (TopCat.Presheaf.germ M₂.val.presheaf U x hx m)) *
        ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) k
          fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i) := by
  refine Eq.trans (congrArg (fun t => ((exteriorPowerStalkEquiv A' ι hA' (k + 1) x t :
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
        ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) :
      ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)))
    (stalkMapL_extComplex_f_germ ι κ hA' hB' p q hqp k x U hx m s s' hs0 hs)) ?_
  refine Eq.trans (congrArg Subtype.val
    (exteriorPowerStalkEquiv_germ_homogeneousProd A' ι hA' (k + 1) x U hx s')) ?_
  refine Eq.trans (exteriorPower.ιMulti_apply_coe
    ↑(TopCat.Presheaf.stalk Osharp.obj x) (k + 1) _) ?_
  refine Eq.trans (ExteriorAlgebra.ιMulti_succ_head k
    fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s' i)) ?_
  refine congrArg₂ (· * ·) ?_ ?_
  · exact congrArg _ ((congrArg (TopCat.Presheaf.germ M₁.val.presheaf U x hx) hs0).trans
      (PresheafOfModules.stalkMapL_germ x (valHom q) U hx m).symm)
  · exact congrArg (ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) k)
      (funext fun i => congrArg (TopCat.Presheaf.germ M₁.val.presheaf U x hx) (hs i))

/-! ### The first map of the complex on every stalk element -/

/-- **The stalk of the first map of the sequence of Tag 01CJ is `ExtPow.beta`.** Read through the
identification of the stalk of `M₂ ⊗ ⋀^k(M₁)` with `M₂ₓ ⊗ ⋀^k(M₁ₓ)` on the source and the
exterior clause of Tag 01CH on the target, the stalk at `x` of
`SheafOfModules.GradedAlgebra.generatorMul (q ≫ ι) k` is the algebraic map
`m ⊗ y ↦ qₓ(m) ∧ y` of Stacks 00DO.

The identification of Tag 01CH is pinned down only on wedges of degree-one generators, so the
proof is the germ computation `exteriorPowerStalkEquiv_extComplex_f_germ` extended by
`ExteriorAlgebra.powExtₛₗ` in the second tensor factor and by `TensorProduct.ext'` in the
first. -/
theorem exteriorPowerStalkEquiv_extComplex_f (k : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp M₂ (A'.piece (k : ℤ))).presheaf x)) :
    exteriorPowerStalkEquiv A' ι hA' (k + 1) x
        (PresheafOfModules.stalkMapL x (valHom (extComplex ι κ hA' hB' p q hqp k).f) z) =
      ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q))
        (extTensorStalkEquiv ι hA' k x z) := by
  have key : (exteriorPowerStalkEquiv A' ι hA' (k + 1) x).toLinearMap.comp
        ((PresheafOfModules.stalkMapL x
            (valHom (extComplex ι κ hA' hB' p q hqp k).f)).comp
          (extTensorStalkEquiv ι hA' k x).symm.toLinearMap) =
      ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q)) := by
    refine TensorProduct.ext' fun mbar ybar => ?_
    have hlin : ((exteriorPowerStalkEquiv A' ι hA' (k + 1) x).toLinearMap.comp
          ((PresheafOfModules.stalkMapL x
              (valHom (extComplex ι κ hA' hB' p q hqp k).f)).comp
            (extTensorStalkEquiv ι hA' k x).symm.toLinearMap)).comp
            (TensorProduct.mk ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) _ mbar) =
        (ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q))).comp
          (TensorProduct.mk ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) _ mbar) := by
      refine ExteriorAlgebra.powExtₛₗ fun sbar => ?_
      refine (SymPresentation.exists_common_germ₂ M₂.val.presheaf M₁.val.presheaf x k
        mbar sbar).elim fun U hU => hU.elim fun hx hU' => hU'.elim fun mm hU'' =>
          hU''.elim fun ss hss => ?_
      have hm : mbar = TopCat.Presheaf.germ M₂.val.presheaf U x hx mm := hss.1.symm
      have hs : sbar = fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i) :=
        (funext hss.2).symm
      subst hm
      subst hs
      have hsymm : (extTensorStalkEquiv ι hA' k x).symm
            (TopCat.Presheaf.germ M₂.val.presheaf U x hx mm ⊗ₜ
              exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) k
                fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i)) =
          PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx mm
            (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
              fun i => ι.val.app (op U) (ss i)) :=
        (extTensorStalkEquiv ι hA' k x).symm_apply_eq.2
          (extTensorStalkEquiv_germ ι hA' k x U hx mm ss).symm
      refine Subtype.ext (Eq.trans (congrArg
        (fun y => ((exteriorPowerStalkEquiv A' ι hA' (k + 1) x
          (PresheafOfModules.stalkMapL x
            (valHom (extComplex ι κ hA' hB' p q hqp k).f) y) :
            ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(k + 1)
              ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) :
            ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk M₁.val.presheaf x))) hsymm) ?_)
      refine Eq.trans (exteriorPowerStalkEquiv_extComplex_f_germ ι κ hA' hB' p q hqp k x U hx
        mm ss (Fin.cons (q.val.app (op U) mm) ss) (Fin.cons_zero _ _)
        fun i => Fin.cons_succ _ _ i) ?_
      exact (ExtPow.beta_tmul k (PresheafOfModules.stalkMapL x (valHom q))
        (TopCat.Presheaf.germ M₂.val.presheaf U x hx mm)
        (exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) k
          fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i))).symm
    exact DFunLike.congr_fun hlin ybar
  exact equiv_comp_apply_eq _ _ _ _ key z

/-! ### Exactness -/

/-- **Stacks Tag 01CJ for exterior powers.** Let `M₂ --q--> M₁ --p--> M ⟶ 0` be a presentation of
a sheaf of modules on a topological space with a sheaf of commutative rings — `p` an epimorphism
and the complex exact at `M₁` — let `A'` be an exterior algebra of `M₁` and `B'` one of `M`. Then
for every `k` the three-term sequence

`M₂ ⊗ ⋀^k(M₁) ⟶ ⋀^{k+1}(M₁) ⟶ ⋀^{k+1}(M) ⟶ 0`

is exact at the middle term and its second map is an epimorphism, which is the exactness the
source asserts in every degree `n = k + 1 ≥ 1`. -/
@[stacks 01CJ "exterior case, in full: the sequence `M₂ ⊗ ⋀^k(M₁) ⟶ ⋀^{k+1}(M₁) ⟶ \
⋀^{k+1}(M) ⟶ 0` is exact at the middle term and its second map is an epimorphism. The \
surjectivity clause alone, in every degree and with no exactness hypothesis, is \
`SheafOfModules.ExtPresentation.epi_extDesc_app`. With the symmetric pair \
`SheafOfModules.SymPresentation.epi_symDesc_app` and \
`SheafOfModules.SymPresentation.symmetricPresentation_exact` this completes the tag: the source \
states the two clauses for the symmetric and the exterior powers and nothing else."]
theorem exteriorPresentation_exact (hS : (ShortComplex.mk q p hqp).Exact) [Epi p] (k : ℕ) :
    (extComplex ι κ hA' hB' p q hqp k).Exact ∧
      Epi (extComplex ι κ hA' hB' p q hqp k).g := by
  refine ⟨?_, epi_extDesc_app ι κ hA' hB' p (k + 1)⟩
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun t ht => ?_
  refine ((stalkMapL_extDesc_eq_zero_iff ι κ hA' hB' p q k x
    (SymPresentation.range_stalkMapL_eq_ker_stalkMapL q p hqp hS x) t).1 ht).elim
    fun w hw => ?_
  refine ⟨(extTensorStalkEquiv ι hA' k x).symm w,
    (exteriorPowerStalkEquiv A' ι hA' (k + 1) x).injective ?_⟩
  refine Eq.trans (exteriorPowerStalkEquiv_extComplex_f ι κ hA' hB' p q hqp k x _) ?_
  exact Eq.trans (congrArg (ExtPow.beta k (PresheafOfModules.stalkMapL x (valHom q)))
    ((extTensorStalkEquiv ι hA' k x).apply_symm_apply w)) hw

end SheafOfModules.ExtPresentation

end
