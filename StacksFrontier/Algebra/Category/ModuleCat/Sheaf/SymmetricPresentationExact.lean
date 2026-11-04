module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The exactness clause of Stacks Tag 01CJ for symmetric powers

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and
`M₂ --q--> M₁ --p--> M ⟶ 0` a presentation of sheaves of `O♯`-modules. Stacks Tag 01CJ asserts
that in every degree `n ≥ 1` the sequence

`M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

is exact, and the proof the source gives is a single citation to the module-level Tag 00DO. The
surjectivity clause is already on this branch
(`SheafOfModules.SymPresentation.epi_symDesc_app`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerPresentation`). **This file proves the
exactness clause**, and with it the symmetric half of Tag 01CJ in full.

What was left to do, and is done here, is the identification of the stalk of the *first* map of
the sequence. Everything it rests on was already available:

* the stalk of `Symⁿ(M₁)` is `Symⁿ` of the stalk, computed on the germ of an ordered product of
  degree-one generators — Tag 01CH, as `SheafOfModules.symmetricPowerStalkEquiv` and
  `SheafOfModules.symmetricPowerStalkEquiv_germ_homogeneousProd`;
* the stalk of `M₂ ⊗ Sym^k(M₁)` is `M₂ₓ ⊗ Sym^k(M₁ₓ)`, computed on the germ of a pure tensor —
  Tag 01CB, as `PresheafOfModules.tensorSheafStalkEquiv`;
* Tag 00DO on the stalk modules, as
  `SheafOfModules.SymPresentation.range_symMulMap_eq_ker_symMap`, and the kernel of the second map
  on every stalk, as `SheafOfModules.SymPresentation.stalkMapL_symDesc_eq_zero_iff`;
* exactness of a short complex of sheaves of modules is a stalkwise condition, as
  `AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact`.

## Main definitions

* `SheafOfModules.SymPresentation.symComplex`: the three-term complex of Tag 01CJ for symmetric
  powers in degree `k + 1`, namely
  `SheafOfModules.GradedAlgebra.symmetricPresentationShortComplex` with the target degree fixed at
  `((k + 1 : ℕ) : ℤ)`. The abbreviation exists to keep that degree, and the proof of
  `1 + k = k + 1` it is transported along, out of every statement below.
* `SheafOfModules.SymPresentation.symTensorStalkEquiv`: **the stalk of the first term of the
  sequence**, `(M₂ ⊗ Sym^k(M₁))ₓ ≃ₗ[O_x] M₂ₓ ⊗ Sym^k(M₁ₓ)`: the stalk of a tensor product
  (Tag 01CB) followed by Tag 01CH in the second factor.

## Main results

* `Stacks.GradedAlgebra.homogeneousProd_succ`: the ordered product of `k + 1` degree-one local
  sections peeled on the **left** — the first factor times the ordered product of the remaining
  `k`, transported from degree `1 + k` to degree `k + 1`. This is
  `Stacks.GradedAlgebra.homogeneousProdLeft` read through
  `Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`, and it is what makes the two
  degree conventions meet.
* `SheafOfModules.SymPresentation.eqToHom_val_app`: the categorical transport of a degreewise
  family of sheaves of modules along an equality of degrees acts on local sections as
  `Stacks.degCast`.
* `SheafOfModules.SymPresentation.exists_common_germ₂`: a germ of one presheaf together with a
  finite family of germs of another are represented over a single open neighbourhood.
* `SheafOfModules.SymPresentation.symTensorStalkEquiv_germ`: the stalk identification of the first
  term on the germ of `m ⊗ s₁ ⋯ s_k`.
* `SheafOfModules.SymPresentation.stalkMapL_symComplex_f_germ` and
  `SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symComplex_f_germ`: the stalk of the
  first map on that germ, before and after the identifications of Tag 01CH.
* `SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symComplex_f_comp`: that stalk
  identification as an equality of *linear maps* out of `M₂ₓ ⊗ Sym^k(M₁ₓ)`, which is the form
  `TensorProduct.ext'` proves.
* `SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symComplex_f`: **the stalk of the first
  map of the sequence is `SymPow.symMulMap`**, the algebraic map `m ⊗ y ↦ ι(qₓ m) · y` of
  Stacks 00DO. This is the step the exactness clause was waiting on. It is
  `symmetricPowerStalkEquiv_symComplex_f_comp` applied to a stalk element.
* `SheafOfModules.SymPresentation.stalkMapL_comp_eq_zero` and
  `SheafOfModules.SymPresentation.range_stalkMapL_eq_ker_stalkMapL`: exactness of the presentation
  read on a stalk, in the `CommRingCat`-linear spelling that `range_symMulMap_eq_ker_symMap`
  consumes.
* `SheafOfModules.SymPresentation.symmetricPresentation_exact`: **Stacks Tag 01CJ for symmetric
  powers.** The sequence is exact at the middle term and its second map is an epimorphism.

## Implementation notes

**What the tag now covers, and what it does not.** Tag 01CJ is the conjunction of two clauses for
each of the symmetric and the exterior powers: the second map is surjective, and the sequence is
exact at the middle term. Both symmetric clauses are now proved. The covering set for the
symmetric half is the pair `SheafOfModules.SymPresentation.epi_symDesc_app` — the surjectivity
clause, at strictly greater generality than it is needed here, since it holds in every degree and
needs no exactness hypothesis — and `symmetricPresentation_exact` below, which states the
sequence of the source. **The exterior half is not covered here**, and nothing below is stated
for it; it is covered in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact`, by
`SheafOfModules.ExtPresentation.epi_extDesc_app` and
`SheafOfModules.ExtPresentation.exteriorPresentation_exact`, so the tag's covering set is those
four declarations.

**How much of this file transferred to the exterior half, and what it was composed with.** The
degree bookkeeping transferred verbatim, and it is what cost this file its work.
`Stacks.GradedAlgebra.homogeneousProd_succ` and
`SheafOfModules.SymPresentation.eqToHom_val_app` are statements about an *abstract* sheaf of
graded algebras and mention no symmetry whatever, so they apply unchanged to an exterior algebra;
so do `SheafOfModules.SymPresentation.exists_common_germ₂` and
`range_stalkMapL_eq_ker_stalkMapL` (and with it `stalkMapL_comp_eq_zero`, which is its input);
and `SheafOfModules.GradedAlgebra.presentationShortComplex` is already the construction common to
the two halves, with `SheafOfModules.GradedAlgebra.exteriorPresentationShortComplex` its other
instance. All of those are used, unchanged, by
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact`. What did *not* transfer
is everything the germ computation is composed with: the exterior Tag 01CG and Tag 01CH in place
of `SheafOfModules.symmetricPowerStalkEquiv` and its germ formula,
`exterior_power_presentation` in place of `symmetric_power_presentation`, and an extension
principle off wedges in place of `SymPow.ext_of_prod_ι`. Those are
`SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`, `PresheafOfModules.extPowStalkEquiv` with
`PresheafOfModules.extPowStalkL_germ_ιMulti` (bundled for a sheaf of graded algebras as
`SheafOfModules.exteriorPowerStalkEquiv`), and `ExteriorAlgebra.powExtₛₗ`.

**The degree is reindexed once, in `symComplex`, and never again.**
`SheafOfModules.GradedAlgebra.generatorMul` lands in `A.piece (1 + k)` on the nose, while
`SheafOfModules.symmetricPowerStalkEquiv` is indexed by a natural number and so lives at
`A.piece ((k + 1 : ℕ) : ℤ)`; the two degrees are equal but not definitionally so, since `Nat.add`
recurses on its second argument. `symComplex` fixes the target degree at `((k + 1 : ℕ) : ℤ)` and
`eqToHom_val_app` turns the complex's `eqToHom` transport into the `Stacks.degCast` that
`Stacks.GradedAlgebra.homogeneousProdLeft` is defined with, after which the two conventions are
the same term. Both transport lemmas are proved by `subst` on an equality of degrees whose
right-hand side is a *variable*, which is the only way either is provable: with the degree a
numeral neither `eqToHom` nor `degCast` reduces.

**No statement below writes a numeral degree.** `SymPow.symmetricPower` sits over the reducible
`SymmetricAlgebra`, a `RingCon` quotient of `TensorAlgebra`, so with a numeral degree `whnf`
unfolds `symmetricPower (1 + 1)` through `Submodule.mul` and `Submodule.span` into that quotient
and exhausts the heartbeat limit while elaborating the *statement*. Every degree here is `k` or
`k + 1` for a variable `k : ℕ`; the one numeral that appears, in `ι : M₁ ⟶ A'.piece 1`, is the
degree of a piece of an abstract sheaf of graded algebras, where there is nothing to unfold.

**One spelling for the stalk map of `q`, and the map-level identity is its own declaration.**
`valHom` lands in the presheaf of modules restricted along `𝟙 Osharp.obj`, so the source and
target of `PresheafOfModules.stalkMapL x (valHom q)` are the stalks of
`(PresheafOfModules.restrictScalars (toRingCatMap _ (𝟙 Osharp.obj))).obj M₂.val` and of the same
for `M₁`, while `symTensorStalkEquiv` and `SymPow.symMulMap` are stated at the stalks of
`M₂.val.presheaf` and `M₁.val.presheaf`. The two are definitionally equal, but seeing it costs
`whnf` an unfolding of `restrictScalars` through `ModuleCat.RestrictScalars.obj'`, and
`symmetricPowerStalkEquiv_symComplex_f_comp` would pay it at four separate subterms. So that
lemma ascribes the unrestricted spelling to `PresheafOfModules.stalkMapL x (valHom q)` and is
stated entirely in it, and the crossing is made once, where the pointwise
`symmetricPowerStalkEquiv_symComplex_f` applies it. Splitting the two statements also gives each
its own heartbeat budget: stated as a single declaration with `have key`, the proof needs more
than the default limit.

**`rw` and `simp` are avoided in favour of `congrArg`, `congrArg₂` and `Eq.trans`.** The terms
below contain the stalk colimit and the symmetric-algebra quotient, and `kabstract` — which `rw`
uses to build its motive, and which calls `whnf` on subterms — exhausts the heartbeat limit on
them. For the same reason the existentials of `exists_common_germ₂` and of
`TopCat.Presheaf.exists_germ_eq` are eliminated with `Exists.elim` rather than with `obtain`
whenever the ambient goal is one of these equations.

**Why `SymPow.ext_of_prod_ι` is the extension principle, and `TensorProduct.ext'` the other
half.** `symmetricPowerStalkEquiv` is pinned down only on germs of ordered products of degree-one
generators, so the compatibility of the first map with `SymPow.symMulMap` can only be proved on
`germ m ⊗ germ s₁ ⋯ germ s_k`. `TensorProduct.ext'` reduces an equality of linear maps out of
`M₂ₓ ⊗ Sym^k(M₁ₓ)` to pure tensors, and `SymPow.ext_of_prod_ι` reduces the second factor to
products of degree-one generators; `exists_common_germ₂` then represents all `k + 1` stalk
elements over one open neighbourhood. No general-element argument is used anywhere.

**Named implicit arguments at `symmetricPresentationShortComplex`.** `symComplex` passes
`(Osharp := ...)`, `(A := ...)` and the rest by name. Left to unification those implicits stay
metavariables — `symmetricPresentationShortComplex` carries three instance arguments
(`HasSheafCompose`, `WEqualsLocallyBijective`, `HasWeakSheafify`) whose synthesis is postponed
with the site still unknown — and the application then fails with the site universes defaulted to
`0`. This is a bookkeeping wart, not a mathematical constraint.

**`stalkMapL_comp_eq_zero` is proved through germs rather than from the complex.** The fact that
the stalk maps of `q` and `p` compose to zero is immediate from
`ShortComplex.moduleCat_zero_apply` applied to the complex of stalk modules, but writing that
complex out requires synthesizing `(stalkFunctor O x).PreservesZeroMorphisms`, which times out at
this file's import closure. Applying
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact` does not: the instance is part
of that lemma's already-elaborated statement. The germ proof needs no instance at all, so it is
the one used and no limit is raised.

**Universes.** The single universe `u` carries the space, the sheaf of rings and the modules, and
the ring universe and the module universe of the graded algebras are equal. Both are inherited,
not chosen: Mathlib's module structure on the stalk of a presheaf of modules
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) exists only for `X : TopCat.{u}`,
`R : X.Presheaf CommRingCat.{u}` and modules in `u`, and the whole development of Tag 01CB that
`PresheafOfModules.tensorSheafStalkEquiv` transports is stated for
`AlgebraicGeometry.RingedSpace.{u, u}`. Tag 01CJ is stated in the equal-universe case, so nothing
the source says is narrowed. `Stacks.GradedAlgebra.homogeneousProd_succ`, which mentions no
stalk, keeps the site universes and the two algebra universes independent.

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
open scoped TensorProduct

universe u v w a

namespace Stacks.GradedAlgebra

/-! ### Peeling the ordered product of degree-one sections on the left -/

/-- The ordered product of `k + 1` degree-one local sections, peeled on the **left**: it is the
product of the first factor with the ordered product of the remaining `k`, transported from degree
`1 + k` to degree `k + 1`. This is `Stacks.GradedAlgebra.homogeneousProdLeft` read through
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd`. -/
theorem homogeneousProd_succ {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
    (A : Stacks.GradedAlgebra Pc) (Y : Cᵒᵖ) (k : ℕ)
    (hk : (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ)) (z : Fin (k + 1) → (Pc 1).obj Y) :
    A.homogeneousProd Y (k + 1) z =
      Stacks.degCast (F := fun l : ℤ => ((Pc l).obj Y : Type (max w a))) hk
        ((A.mul 1 (k : ℤ)).app Y (z 0) (A.homogeneousProd Y k fun i => z i.succ)) := by
  refine Eq.trans (A.homogeneousProdLeft_eq_homogeneousProd Y (k + 1) z).symm ?_
  show Stacks.degCast (F := fun l : ℤ => ((Pc l).obj Y : Type (max w a))) hk
      ((A.mul 1 (k : ℤ)).app Y (z 0) (A.homogeneousProdLeft Y k fun i => z i.succ)) = _
  exact congrArg
    (fun y => Stacks.degCast (F := fun l : ℤ => ((Pc l).obj Y : Type (max w a))) hk
      ((A.mul 1 (k : ℤ)).app Y (z 0) y))
    (A.homogeneousProdLeft_eq_homogeneousProd Y k fun i => z i.succ)

end Stacks.GradedAlgebra

namespace SheafOfModules.SymPresentation

/-! ### Two families of germs represented over one open -/

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- A germ of one presheaf and a finite family of germs of another are represented by sections
over a single open neighbourhood. -/
theorem exists_common_germ₂ (P Q : TopCat.Presheaf AddCommGrpCat.{u} X) (x : ↥X) (n : ℕ)
    (b : ↑(TopCat.Presheaf.stalk P x)) (m : Fin n → ↑(TopCat.Presheaf.stalk Q x)) :
    ∃ (U : Opens ↥X) (hx : x ∈ U) (t : P.obj (op U)) (s : Fin n → Q.obj (op U)),
      TopCat.Presheaf.germ P U x hx t = b ∧
        ∀ i, TopCat.Presheaf.germ Q U x hx (s i) = m i := by
  obtain ⟨U₁, h₁, t₁, ht₁⟩ := TopCat.Presheaf.exists_germ_eq P b
  obtain ⟨U₂, h₂, s₂, hs₂⟩ := exists_common_germ Q x n m
  refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, P.map (homOfLE inf_le_left).op t₁,
    fun i => Q.map (homOfLE inf_le_right).op (s₂ i), ?_, fun i => ?_⟩
  · exact (TopCat.Presheaf.germ_res_apply P (homOfLE inf_le_left) x ⟨h₁, h₂⟩ t₁).trans ht₁
  · exact (TopCat.Presheaf.germ_res_apply Q (homOfLE inf_le_right) x ⟨h₁, h₂⟩ (s₂ i)).trans
      (hs₂ i)

/-! ### Transport along an equality of degrees -/

/-- The categorical transport of a degreewise family of sheaves of modules along an equality of
degrees acts on local sections as `Stacks.degCast`. -/
theorem eqToHom_val_app {O : Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u}}
    (Y : ℤ → SheafOfModules.{u} O) {i j : ℤ} (h : i = j) (U : (Opens ↥X)ᵒᵖ)
    (y : (Y i).val.obj U) :
    (eqToHom (congrArg Y h)).val.app U y =
      Stacks.degCast (F := fun l : ℤ => ((Y l).val.obj U : Type u)) h y := by
  subst h; rfl

/-! ### The complex of Tag 01CJ in degree `k + 1` -/

variable {M₂ M₁ M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A' B' : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ι : M₁ ⟶ A'.piece 1) (κ : M ⟶ B'.piece 1)
  (hA' : GradedAlgebra.IsSymmetricAlgebra A' ι) (hB' : GradedAlgebra.IsSymmetricAlgebra B' κ)
  (q : M₂ ⟶ M₁) (p : M₁ ⟶ M) (hqp : q ≫ p = 0)

/-- The three-term complex of Tag 01CJ for symmetric powers in degree `k + 1`:
`M₂ ⊗ Sym^k(M₁) ⟶ Sym^{k+1}(M₁) ⟶ Sym^{k+1}(M)`. -/
noncomputable abbrev symComplex (k : ℕ) :
    ShortComplex (SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  GradedAlgebra.symmetricPresentationShortComplex
    (Osharp := Osharp) (M₂ := M₂) (M₁ := M₁) (M := M) (A := A') (B := B') (ι := ι) (κ := κ)
    hA' hB'.1 q p hqp (k : ℤ) ((k + 1 : ℕ) : ℤ) (by omega)

/-- The stalk of the first term of the sequence of Tag 01CJ: the stalk of `M₂ ⊗ Sym^k(M₁)` is
`M₂ₓ ⊗ Sym^k(M₁ₓ)`. This is the stalk of a tensor product
(`PresheafOfModules.tensorSheafStalkEquiv`) followed by Tag 01CH in the second factor. -/
noncomputable def symTensorStalkEquiv (k : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp M₂ (A'.piece (k : ℤ))).presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
    ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower k ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M₁.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp M₂ (A'.piece (k : ℤ)) x).trans
    (TensorProduct.congr (LinearEquiv.refl _ _) (symmetricPowerStalkEquiv A' ι hA' k x))

/-- `symTensorStalkEquiv` sends the germ at `x` of `m ⊗ s₁ ⋯ s_k`, for local sections `m` of `M₂`
and `sᵢ` of `M₁` over `U`, to `mₓ ⊗ (s₁)ₓ ⋯ (s_k)ₓ` in `M₂ₓ ⊗ Sym^k(M₁ₓ)`. -/
theorem symTensorStalkEquiv_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U)) :
    symTensorStalkEquiv ι hA' k x
        (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
          (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
            fun i => ι.val.app (op U) (s i))) =
      TopCat.Presheaf.germ M₂.val.presheaf U x hx m ⊗ₜ
        ⟨∏ i : Fin k, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
            (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)),
          SymmetricAlgebra.prod_ι_mem _ _⟩ := by
  refine Eq.trans (congrArg
    (TensorProduct.congr (LinearEquiv.refl ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M₂.val.presheaf x)) (symmetricPowerStalkEquiv A' ι hA' k x))
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x
      U hx m _)) ?_
  refine Eq.trans (TensorProduct.congr_tmul _ _ _ _) ?_
  exact congrArg (fun y => TopCat.Presheaf.germ M₂.val.presheaf U x hx m ⊗ₜ y)
    (Subtype.ext (symmetricPowerStalkEquiv_germ_homogeneousProd A' ι hA' k x U hx s))

/-! ### The first map of the complex, on the germ of a pure tensor -/

/-- **The first map of the sequence of Tag 01CJ on a germ.** The stalk of
`SheafOfModules.GradedAlgebra.generatorMul (q ≫ ι) k` carries the germ of the image of
`m ⊗ s₁ ⋯ s_k` to the germ of the ordered product `q(m) · s₁ ⋯ s_k`, in degree `k + 1`.

The degree bookkeeping is the whole content: `A.mul 1 k` lands in `A.piece (1 + k)`, the complex
transports that to `A.piece ((k + 1 : ℕ) : ℤ)` along `eqToHom`, and the result is the
*left*-handed ordered product `Stacks.GradedAlgebra.homogeneousProdLeft`, which agrees with the
right-handed `Stacks.GradedAlgebra.homogeneousProd` that Tag 01CH's germ formula is stated
with. -/
theorem stalkMapL_symComplex_f_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U))
    (s' : Fin (k + 1) → M₁.val.obj (op U)) (hs0 : s' 0 = q.val.app (op U) m)
    (hs : ∀ i : Fin k, s' i.succ = s i) :
    PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f)
        (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
          (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
            fun i => ι.val.app (op U) (s i))) =
      TopCat.Presheaf.germ (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf U x hx
        (A'.toPresheafGradedAlgebra.homogeneousProd (op U) (k + 1)
          fun i => ι.val.app (op U) (s' i)) := by
  have hk : (1 : ℤ) + (k : ℤ) = ((k + 1 : ℕ) : ℤ) := by omega
  refine Eq.trans (congrArg
    (PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f))
    (PresheafOfModules.tensorSheafGerm_eq Osharp M₂ (A'.piece (k : ℤ)) x U hx m _)) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hx _) ?_
  refine congrArg (TopCat.Presheaf.germ (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf U x hx) ?_
  refine Eq.trans (GradedAlgebra.presentationShortComplex_f_unit hA'.isUniversal q p
    (GradedAlgebra.pairwiseCommutes_comp p hB'.1) hqp (k : ℤ) ((k + 1 : ℕ) : ℤ) hk (op U) m _) ?_
  refine Eq.trans (eqToHom_val_app A'.piece hk (op U) _) ?_
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
germ.** Under Tag 01CH the stalk of the first map carries `germ m ⊗ germ s₁ ⋯ germ s_k` to
`ι(qₓ(germ m)) · germ s₁ ⋯ germ s_k`, which is what `SymPow.symMulMap` does. -/
theorem symmetricPowerStalkEquiv_symComplex_f_germ (k : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (m : M₂.val.obj (op U)) (s : Fin k → M₁.val.obj (op U))
    (s' : Fin (k + 1) → M₁.val.obj (op U)) (hs0 : s' 0 = q.val.app (op U) m)
    (hs : ∀ i : Fin k, s' i.succ = s i) :
    (symmetricPowerStalkEquiv A' ι hA' (k + 1) x
          (PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f)
            (PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx m
              (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
                fun i => ι.val.app (op U) (s i)))) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) =
      SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
            (PresheafOfModules.stalkMapL x (valHom q)
              (TopCat.Presheaf.germ M₂.val.presheaf U x hx m)) *
        ∏ i : Fin k, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
          (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)) := by
  refine Eq.trans (congrArg (fun t => (symmetricPowerStalkEquiv A' ι hA' (k + 1) x t).1)
    (stalkMapL_symComplex_f_germ ι κ hA' hB' q p hqp k x U hx m s s' hs0 hs)) ?_
  refine Eq.trans (symmetricPowerStalkEquiv_germ_homogeneousProd A' ι hA' (k + 1) x U hx s') ?_
  refine Eq.trans (Fin.prod_univ_succ fun i => SymmetricAlgebra.ι
    ↑(TopCat.Presheaf.stalk Osharp.obj x) ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
    (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s' i))) ?_
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun i _ => ?_)
  · exact congrArg _ ((congrArg (TopCat.Presheaf.germ M₁.val.presheaf U x hx) hs0).trans
      (PresheafOfModules.stalkMapL_germ x (valHom q) U hx m).symm)
  · exact congrArg _ (congrArg (TopCat.Presheaf.germ M₁.val.presheaf U x hx) (hs i))

/-! ### The first map of the complex on every stalk element -/

/-- **The stalk of the first map of the sequence of Tag 01CJ is `SymPow.symMulMap`, as an identity
of linear maps.** This is `symmetricPowerStalkEquiv_symComplex_f` read as an equality of linear
maps out of `M₂ₓ ⊗ Sym^k(M₁ₓ)`, which is the form `TensorProduct.ext'` proves; the pointwise
statement is that equality applied to a stalk element.

The identification of Tag 01CH is pinned down only on products of degree-one generators, so the
proof is the germ computation `symmetricPowerStalkEquiv_symComplex_f_germ` extended by
`SymPow.ext_of_prod_ι` in the second tensor factor and by `TensorProduct.ext'` in the first. -/
theorem symmetricPowerStalkEquiv_symComplex_f_comp (k : ℕ) (x : ↥X) :
    (symmetricPowerStalkEquiv A' ι hA' (k + 1) x).toLinearMap.comp
        ((PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f)).comp
          (symTensorStalkEquiv ι hA' k x).symm.toLinearMap) =
      SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q) :
          ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) := by
  refine TensorProduct.ext' fun mbar ybar => ?_
  have hlin : ((symmetricPowerStalkEquiv A' ι hA' (k + 1) x).toLinearMap.comp
        ((PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f)).comp
          (symTensorStalkEquiv ι hA' k x).symm.toLinearMap)).comp
          (TensorProduct.mk ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) _ mbar) =
      (SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q) :
          ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x))).comp
        (TensorProduct.mk ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) _ mbar) := by
    refine SymPow.ext_of_prod_ι fun sbar => ?_
    refine (exists_common_germ₂ M₂.val.presheaf M₁.val.presheaf x k mbar sbar).elim
      fun U hU => hU.elim fun hx hU' => hU'.elim fun mm hU'' =>
        hU''.elim fun ss hss => ?_
    have hm : mbar = TopCat.Presheaf.germ M₂.val.presheaf U x hx mm := hss.1.symm
    have hs : sbar = fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i) :=
      (funext hss.2).symm
    subst hm
    subst hs
    have hsymm : (symTensorStalkEquiv ι hA' k x).symm
          (TopCat.Presheaf.germ M₂.val.presheaf U x hx mm ⊗ₜ
            ⟨∏ i : Fin k, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
                ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
                (TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i)),
              SymmetricAlgebra.prod_ι_mem _ _⟩) =
        PresheafOfModules.tensorSheafGerm Osharp M₂ (A'.piece (k : ℤ)) x U hx mm
          (A'.toPresheafGradedAlgebra.homogeneousProd (op U) k
            fun i => ι.val.app (op U) (ss i)) :=
      (symTensorStalkEquiv ι hA' k x).symm_apply_eq.2
        (symTensorStalkEquiv_germ ι hA' k x U hx mm ss).symm
    refine Subtype.ext (Eq.trans (congrArg (fun y => (symmetricPowerStalkEquiv A' ι hA' (k + 1) x
        (PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f) y)).1)
      hsymm) ?_)
    refine Eq.trans (symmetricPowerStalkEquiv_symComplex_f_germ ι κ hA' hB' q p hqp k x U hx
      mm ss (Fin.cons (q.val.app (op U) mm) ss) (Fin.cons_zero _ _)
      fun i => Fin.cons_succ _ _ i) ?_
    exact (SymPow.symMulMap_tmul k (PresheafOfModules.stalkMapL x (valHom q) :
          ↑(TopCat.Presheaf.stalk M₂.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x))
      (TopCat.Presheaf.germ M₂.val.presheaf U x hx mm)
      ⟨∏ i : Fin k, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
          (TopCat.Presheaf.germ M₁.val.presheaf U x hx (ss i)),
        SymmetricAlgebra.prod_ι_mem _ _⟩).symm
  exact DFunLike.congr_fun hlin ybar

/-- **The stalk of the first map of the sequence of Tag 01CJ is `SymPow.symMulMap`.** Read through
the identification of the stalk of `M₂ ⊗ Sym^k(M₁)` with `M₂ₓ ⊗ Sym^k(M₁ₓ)` on the source and
Tag 01CH on the target, the stalk at `x` of
`SheafOfModules.GradedAlgebra.generatorMul (q ≫ ι) k` is the algebraic map
`m ⊗ y ↦ ι(qₓ m) · y` of Stacks 00DO.

This is `symmetricPowerStalkEquiv_symComplex_f_comp` applied to `z`, after replacing `z` by
`(symTensorStalkEquiv ι hA' k x).symm (symTensorStalkEquiv ι hA' k x z)` so that the composite
there is the one being applied. -/
theorem symmetricPowerStalkEquiv_symComplex_f (k : ℕ) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp M₂ (A'.piece (k : ℤ))).presheaf x)) :
    symmetricPowerStalkEquiv A' ι hA' (k + 1) x
        (PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f) z) =
      SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q))
        (symTensorStalkEquiv ι hA' k x z) := by
  refine Eq.trans (congrArg (fun y => symmetricPowerStalkEquiv A' ι hA' (k + 1) x
    (PresheafOfModules.stalkMapL x (valHom (symComplex ι κ hA' hB' q p hqp k).f) y))
    ((symTensorStalkEquiv ι hA' k x).symm_apply_apply z).symm) ?_
  exact DFunLike.congr_fun
    (symmetricPowerStalkEquiv_symComplex_f_comp ι κ hA' hB' q p hqp k x)
    (symTensorStalkEquiv ι hA' k x z)

/-! ### Exactness -/

include hqp in
/-- A composite of morphisms of sheaves of modules which is zero is zero on every stalk. Proved
through germs, since every element of a stalk is a germ. -/
theorem stalkMapL_comp_eq_zero (x : ↥X) (w : ↑(TopCat.Presheaf.stalk M₂.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (valHom p)
      (PresheafOfModules.stalkMapL x (valHom q) w) = 0 := by
  refine (TopCat.Presheaf.exists_germ_eq M₂.val.presheaf w).elim fun U hU =>
    hU.elim fun hx hU' => hU'.elim fun w₀ hw₀ => ?_
  refine Eq.trans (congrArg (fun y => PresheafOfModules.stalkMapL x (valHom p)
    (PresheafOfModules.stalkMapL x (valHom q) y)) hw₀.symm) ?_
  refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x (valHom p))
    (PresheafOfModules.stalkMapL_germ x (valHom q) U hx w₀)) ?_
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x (valHom p) U hx _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ M.val.presheaf U x hx) ?_) (map_zero _)
  exact ((comp_val_app_apply q p (op U) w₀).symm.trans
    (congrArg (fun g : M₂ ⟶ M => g.val.app (op U) w₀) hqp)).trans
    (zero_val_app_apply (op U) w₀)

/-- The stalkwise form of an exact presentation `M₂ ⟶ M₁ ⟶ M`: the image of `qₓ` is the kernel
of `pₓ`, in the `CommRingCat`-linear spelling of the stalk maps. This is
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact` read through
`SheafOfModules.SymPresentation.stalkMap_apply`. -/
theorem range_stalkMapL_eq_ker_stalkMapL (hS : (ShortComplex.mk q p hqp).Exact) (x : ↥X) :
    LinearMap.range (PresheafOfModules.stalkMapL x (valHom q)) =
      LinearMap.ker (PresheafOfModules.stalkMapL x (valHom p)) := by
  have hstalk := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact
    (ShortComplex.mk q p hqp)).1 hS x
  refine SetLike.ext fun t => ⟨fun ht => ?_, fun ht => ?_⟩
  · refine LinearMap.mem_ker.2 ((LinearMap.mem_range.1 ht).elim fun w hw => ?_)
    exact Eq.trans (congrArg (PresheafOfModules.stalkMapL x (valHom p)) hw.symm)
      (stalkMapL_comp_eq_zero q p hqp x w)
  · exact ((ShortComplex.moduleCat_exact_iff _).1 hstalk t (LinearMap.mem_ker.1 ht)).elim
      fun w hw => ⟨w, hw⟩

/-- **Stacks Tag 01CJ for symmetric powers.** Let `M₂ --q--> M₁ --p--> M ⟶ 0` be a presentation of
a sheaf of modules on a topological space with a sheaf of commutative rings — `p` an epimorphism
and the complex exact at `M₁` — let `A'` be a symmetric algebra of `M₁` and `B'` one of `M`. Then
for every `k` the three-term sequence

`M₂ ⊗ Sym^k(M₁) ⟶ Sym^{k+1}(M₁) ⟶ Sym^{k+1}(M) ⟶ 0`

is exact at the middle term and its second map is an epimorphism, which is the exactness the
source asserts in every degree `n = k + 1 ≥ 1`.

The tag carries a clause comment: the surjectivity clause is also carried, at greater generality,
by `SheafOfModules.SymPresentation.epi_symDesc_app`, and the exterior half of Tag 01CJ is not
proved anywhere. See this file's implementation notes. -/
@[stacks 01CJ "symmetric case, in full: the sequence `M₂ ⊗ Sym^k(M₁) ⟶ Sym^{k+1}(M₁) ⟶ \
Sym^{k+1}(M) ⟶ 0` is exact at the middle term and its second map is an epimorphism. The \
surjectivity clause alone, in every degree and with no exactness hypothesis, is \
`SheafOfModules.SymPresentation.epi_symDesc_app`. The exterior case is covered too, by \
`SheafOfModules.ExtPresentation.epi_extDesc_app` and \
`SheafOfModules.ExtPresentation.exteriorPresentation_exact` in \
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact`; those four \
declarations are the tag's covering set", ega "0 19.5.1" "more general"]
theorem symmetricPresentation_exact (hS : (ShortComplex.mk q p hqp).Exact) [Epi p] (k : ℕ) :
    (symComplex ι κ hA' hB' q p hqp k).Exact ∧ Epi (symComplex ι κ hA' hB' q p hqp k).g := by
  refine ⟨?_, epi_symDesc_app ι κ hA' hB' p (k + 1)⟩
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun x => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun t ht => ?_
  refine ((stalkMapL_symDesc_eq_zero_iff ι κ hA' hB' p q k x
    (range_stalkMapL_eq_ker_stalkMapL q p hqp hS x) t).1 ht).elim fun w hw => ?_
  refine ⟨(symTensorStalkEquiv ι hA' k x).symm w,
    (symmetricPowerStalkEquiv A' ι hA' (k + 1) x).injective ?_⟩
  refine Eq.trans (symmetricPowerStalkEquiv_symComplex_f ι κ hA' hB' q p hqp k x _) ?_
  exact Eq.trans (congrArg (SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q)))
    ((symTensorStalkEquiv ι hA' k x).apply_symm_apply w)) hw

end SheafOfModules.SymPresentation

end
