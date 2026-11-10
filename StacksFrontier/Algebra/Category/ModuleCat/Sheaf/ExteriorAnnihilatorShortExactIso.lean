module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactSummand
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdStalk
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0B38: `det(E') ⊗ det(E'') ≅ det(E)` for finite locally free sheaves

Let `(X, O_X)` be a ringed space and let `0 → E' → E → E'' → 0` be a short exact sequence of
sheaves of `O_X`-modules with `E'` and `E''` **finite locally free of no particular rank**. The
canonical map

`det(E') ⊗_{O_X} det(E'') ⟶ det(E)`

of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactSummand` — with
`det` the determinant of [Stacks, Tag 0FJN] — is an **isomorphism**. This completes
[Stacks, Tag 0B38]: the constant-rank form of the statement is
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIso`, and what is proved here is the
general case, where the ranks are only locally constant.

## Main definitions

* `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree`: **the
  canonical isomorphism `det(E') ⊗ det(E'') ≅ det(E)`** of [Stacks, Tag 0B38], with no
  constant-rank hypothesis.
* `Stacks.SheafOfModules.TopWedge.stalkDeterminantTopBasis` and
  `Stacks.SheafOfModules.TopWedge.stalkDeterminantTopBasisOfNbhd`: the rank-one basis of the
  stalk of `det(F)` at a point where the stalk of `F` is free.
* `Stacks.SheafOfModules.TopWedge.stalkTensorDeterminantTopBasis`: the rank-one basis of the
  stalk of a tensor product of two determinants.

## Main results

* `Stacks.SheafOfModules.TopWedge.isIso_determinantTensorDeterminantHom`: **the canonical map is
  an isomorphism.**
* `Stacks.SheafOfModules.TopWedge.detSummandComparison_ι_unit_wedge`: **the wedge-and-lift
  formula in the general case** — the comparison between determinant summands carries the image
  of `(s₁ ∧ ⋯ ∧ s_n) ⊗ (g(l₁) ∧ ⋯ ∧ g(l_m))` to `f(s₁) ∧ ⋯ ∧ f(s_n) ∧ l₁ ∧ ⋯ ∧ l_m`, for
  arbitrary local lifts `lⱼ`.
* `Stacks.SheafOfModules.TopWedge.eq_determinantTensorDeterminantHom` and
  `Stacks.SheafOfModules.TopWedge.eq_detTensorAnnComparison`: **uniqueness** — the canonical map
  is the only one with those restrictions to the summands.
* `Stacks.SheafOfModules.TopWedge.surjective_stalkMapL_exteriorAnnihilator_ι`: the inclusion
  `det(E)_d ⟶ ⋀ᵈ E` is surjective on the stalk at a point around which `⋀ᵈ⁺¹` of every stalk of
  `E` vanishes. This is the step that replaces the stalk description of the annihilator, which
  carries a finite-presentation hypothesis the source does not make.
* `Stacks.SheafOfModules.TopWedge.bijective_stalkMapL_determinantSummand`: the inclusion of the
  degree-`r` summand of `det(E)` is bijective on the stalk at a point where the stalk of `E` is
  free of rank `r`.
* `Stacks.SheafOfModules.TopWedge.exists_chart_of_stalkExact`: the chart at a point — a
  neighbourhood on which the two outer ranks are constant, together with sections realising a
  basis of `E'_x` and a complement of its image in `E_x`.

## Implementation notes

**The shape of the argument.** Isomorphy is stalkwise
(`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`). Fix `x` and let `r'`, `r''` be
the ranks of `E'`, `E''` there. Three things are needed.

*The surviving summands.* `det(F)` is the coproduct of its degreewise annihilators and the stalk
of a coproduct is the direct sum of the stalks, so at `x` every summand but the one in degree
equal to the rank has vanishing stalk and the inclusion of that one is bijective on the stalk
(`bijective_stalkMapL_determinantSummand`). On the target this identifies `det(E)_x` with
`det(E)_{r'+r''}` at `x`, the rank of `E` there being `r' + r''` because the stalk sequence is
short exact with free ends.

*Surjectivity.* The two defining equations of the assembled map say that its restriction to the
summand `det(E')_{r'} ⊗ det(E'')_{r''}` is the comparison between summands followed by the
inclusion of `det(E)_{r'+r''}`. Both of those are surjective on the stalk at `x`: the second by
the previous paragraph, and the first because its composite with the inclusion into
`⋀^{r'+r''} E` hits, by the wedge-and-lift formula, a single wedge which generates
`⋀^{r'+r''}(E_x)` — and that inclusion is injective on stalks. So the assembled map is surjective
on the stalk at `x`.

*Injectivity* is then free: source and target are free of rank one over the stalk ring, so a
surjection between them is injective by the Orzech property
(`Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one`).

**Why a neighbourhood, and not just the point.** Two steps need the rank to be constant on a
whole neighbourhood rather than only at `x`. First, the sections of `⋀^{r'} E'` and `⋀^{r''} E''`
that the wedge-and-lift formula is applied to have to lie in the determinant, which is a
condition quantified over all smaller opens; it holds over a neighbourhood on which the rank is
constant because there `⋀^{r+1}` of every stalk vanishes
(`isExteriorAnnihilated_of_forall_subsingleton_stalk`). Second, for the same reason the inclusion
`det(F)_r ⟶ ⋀ʳ F` is surjective on the stalk at `x`
(`surjective_stalkMapL_exteriorAnnihilator_ι`). Both avoid the stalk description of the
annihilator of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk`, which carries a
finite-presentation hypothesis; the neighbourhood is produced by
`Stacks.SheafOfModules.TopWedge.exists_nbhd_forall_nonempty_stalkLinearEquiv_finsupp`.

**Why the argument is cut into so many declarations.** As in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso`, every mention of
`PresheafOfModules.stalkMapL` or of a stalk comparison makes the elaborator re-solve the module
structure on a stalk and unify a functor composition against `CategoryTheory.Sheaf.toRingCat`,
and two such steps in one declaration exhaust the heartbeat budget although either alone is
comfortable. The facts are therefore passed between declarations as explicit hypotheses, and
`exists_chart_of_stalkExact` is a term-mode composition of two lemmas for exactly that reason.

**The two spellings of the sheaf of rings.** As explained in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactSummand`,
`CategoryTheory.Sheaf.toRingCat Osharp` and
`Stacks.SheafOfModules.Tensor.ringSheaf Osharp` are reducibly but not
syntactically equal. A composite spanning the two spellings can be *elaborated* but not
*rewritten with*: `rw` checks type-correctness at a lower transparency and fails. The two
defining equations of the assembled map are therefore used one at a time, through
`Stacks.SheafOfModules.TopWedge.surjective_stalkMapL_of_eq`, rather than combined into a single
equation for the twofold composite.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open scoped TensorProduct DirectSum

universe u

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### Sections over a neighbourhood of small rank are exterior annihilated -/

section LocalAnnihilated

variable {E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)

/-- **The product of a degree-one section with a section of `⋀ᵈ E` over an open on which
`⋀ᵈ⁺¹` of every stalk of `E` vanishes is zero.** Vanishing of a section of a sheaf is local, so
it is enough that every germ vanish, and every germ does for the given reason. -/
theorem wedgeGen_eq_zero_of_forall_subsingleton_stalk (d : ℕ) {W : Opens ↥X}
    (hW : ∀ y ∈ W, Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y)))
    (V : Opens ↥X) (hVW : V ≤ W) (a : ToType (E.val.obj (op V)))
    (z : ToType ((A.exteriorPower d).val.obj (op V))) :
    A.wedgeGen d (op V) a z = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := (A.exteriorPower (d + 1)).val.presheaf) (A.exteriorPower (d + 1)).isSheaf ?_
  intro y hy
  obtain ⟨W', fW, hyW, hres⟩ := Stacks.SheafOfModules.exists_res_eq y hy
    (A.wedgeGen d (op V) a z) 0
    ((germ_eq_zero_of_subsingleton_exteriorPower A y (d + 1) (hW y (hVW hy)) hy _).trans
      (Stacks.SheafOfModules.germ_zero y hy).symm)
  exact ⟨W', fW.le, hyW, hres⟩

/-- **Every section of `⋀ᵈ E` over an open on which `⋀ᵈ⁺¹` of every stalk of `E` vanishes is
exterior annihilated.** This is the local replacement for
`SheafOfModules.TensorExteriorSymmetricAlgebras.isExteriorAnnihilated_of_rank`, which needs the
rank of `E` to be globally constant and equal to `d`. -/
theorem isExteriorAnnihilated_of_forall_subsingleton_stalk (d : ℕ) {W : Opens ↥X}
    (hW : ∀ y ∈ W, Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y)))
    (V : Opens ↥X) (hVW : V ≤ W) (s : ToType ((A.exteriorPower d).val.obj (op V))) :
    A.IsExteriorAnnihilated d s := by
  intro T h a
  refine (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.wedgeGen_eq_zero_iff
    d T a _).mp ?_
  exact wedgeGen_eq_zero_of_forall_subsingleton_stalk A d hW T.unop
    (le_trans (leOfHom h.unop) hVW) a _

/-- **The inclusion of the degree-`d` determinant summand into `⋀ᵈ E` is surjective on the stalk
at a point having a neighbourhood on which `⋀ᵈ⁺¹` of every stalk of `E` vanishes.** Every germ
is the germ of a section over such a neighbourhood, and every such section is already exterior
annihilated. -/
theorem surjective_stalkMapL_exteriorAnnihilator_ι (d : ℕ) (x : ↥X) {W : Opens ↥X}
    (hxW : x ∈ W)
    (hW : ∀ y ∈ W, Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y))) :
    Function.Surjective (PresheafOfModules.stalkMapL x (A.exteriorAnnihilator d).ι.val) := by
  intro ξ
  obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (A.exteriorPower d).val.presheaf ξ
  have hxV : x ∈ U ⊓ W := ⟨hx, hxW⟩
  have hle : U ⊓ W ≤ U := inf_le_left
  have hann : A.IsExteriorAnnihilated d
      ((A.exteriorPower d).val.presheaf.map (homOfLE hle).op t) :=
    isExteriorAnnihilated_of_forall_subsingleton_stalk A d hW (U ⊓ W) inf_le_right _
  refine ⟨TopCat.Presheaf.germ (A.exteriorAnnihilator d).toSheafOfModules.val.presheaf
    (U ⊓ W) x hxV
    (show ToType ((A.exteriorAnnihilator d).toSheafOfModules.val.presheaf.obj (op (U ⊓ W))) from
      ⟨(A.exteriorPower d).val.presheaf.map (homOfLE hle).op t, hann⟩), ?_⟩
  refine Eq.trans (PresheafOfModules.stalkMapL_germ x (A.exteriorAnnihilator d).ι.val
    (U ⊓ W) hxV _) ?_
  exact TopCat.Presheaf.germ_res_apply (A.exteriorPower d).val.presheaf (homOfLE hle) x hxV t

end LocalAnnihilated

/-! ### The surviving summand of a coproduct, on a stalk -/

section Summand

/-- **The inclusion of a summand of a direct sum all of whose other summands vanish is
bijective.** -/
theorem bijective_directSum_of {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] (r : ι) (h : ∀ i, i ≠ r → Subsingleton (β i)) :
    Function.Bijective (DirectSum.of β r) := by
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · have hr := congrArg (fun w : DirectSum ι β => w r) hab
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same] at hr
    exact hr
  · refine ⟨z r, DFinsupp.ext fun i => ?_⟩
    by_cases hi : i = r
    · subst hi
      exact DirectSum.of_eq_same i (z i)
    · rw [DirectSum.of_eq_of_ne r i (z r) hi]
      have := h i hi
      exact Subsingleton.elim _ _

/-- **The inclusion of a summand of an `ℕ`-indexed coproduct of sheaves of modules all of whose
other summands have vanishing stalk at `x` is bijective on the stalk at `x`.** The stalk of a
coproduct is the direct sum of the stalks ([Stacks, Tag 01AH],
`SheafOfModules.natStalkCoprodEquiv`), and that comparison carries the inclusion of the `n`-th
summand of the direct sum to the stalk map of the `n`-th coproduct injection. -/
theorem bijective_stalkMapL_sigmaι_of_subsingleton
    (Q : ℕ → _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    [Limits.HasCoproduct Q] (x : ↥X) (r : ℕ)
    (h : ∀ n, n ≠ r →
      Subsingleton (ToType (TopCat.Presheaf.stalk (Q n).val.presheaf x))) :
    Function.Bijective (PresheafOfModules.stalkMapL x (Limits.Sigma.ι Q r).val) := by
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · refine (bijective_directSum_of r h).1
      ((_root_.SheafOfModules.natStalkCoprodEquiv Q x).injective ?_)
    exact (_root_.SheafOfModules.natStalkCoprodEquiv_of Q x r a).trans
      (hab.trans (_root_.SheafOfModules.natStalkCoprodEquiv_of Q x r b).symm)
  · obtain ⟨t, ht⟩ := (bijective_directSum_of r h).2
      ((_root_.SheafOfModules.natStalkCoprodEquiv Q x).symm z)
    refine ⟨t, ?_⟩
    rw [← _root_.SheafOfModules.natStalkCoprodEquiv_of Q x r t, ht,
      LinearEquiv.apply_symm_apply]

variable {E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)

/-- **The inclusion of the degree-`r` summand of `det(E)` is bijective on the stalk at a point
where the stalk of `E` is free of rank `r`.** Away from the rank the degreewise annihilator has
vanishing stalk there. -/
theorem bijective_stalkMapL_determinantSummand (x : ↥X) (r : ℕ)
    (b : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :
    Function.Bijective (PresheafOfModules.stalkMapL x (A.determinantSummand r).val) :=
  bijective_stalkMapL_sigmaι_of_subsingleton
    (fun n : ℕ => (A.exteriorAnnihilator n).toSheafOfModules) x r
    fun n hn => subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv A x r b.repr n hn

end Summand

/-! ### Rank-one bases of the surviving stalks -/

section Bases

variable {E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)

/-- **The stalk of `det(E)` at a point where the stalk of `E` is free of rank `r` is free of
rank one.** Only the degree-`r` summand survives, in it the annihilation condition is vacuous,
and the top exterior power of a free module of rank `r` is free of rank one. -/
noncomputable def stalkDeterminantTopBasis (x : ↥X) (r : ℕ)
    (b : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hsum : Function.Bijective
      (PresheafOfModules.stalkMapL x (A.determinantSummand r).val))
    (hι : Function.Bijective
      (PresheafOfModules.stalkMapL x (A.exteriorAnnihilator r).ι.val)) :
    Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk A.determinant.val.presheaf x) :=
  (Stacks.ExteriorPower.topBasis b).map
    (((LinearEquiv.ofBijective _ hι).trans (A.exteriorPowerStalkEquiv r x)).symm.trans
      (LinearEquiv.ofBijective _ hsum))

/-- **The inclusion of the degree-`d` determinant summand into `⋀ᵈ E` is bijective on the stalk
at a point having a neighbourhood on which `⋀ᵈ⁺¹` of every stalk of `E` vanishes.** -/
theorem bijective_stalkMapL_exteriorAnnihilator_ι (d : ℕ) (x : ↥X) {W : Opens ↥X}
    (hxW : x ∈ W)
    (hW : ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y))) :
    Function.Bijective (PresheafOfModules.stalkMapL x (A.exteriorAnnihilator d).ι.val) :=
  ⟨_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.injective_submoduleStalkι x,
    surjective_stalkMapL_exteriorAnnihilator_ι A d x hxW hW⟩

/-- **The stalk of `det(E)` is free of rank one** at a point whose stalk is free of rank `r` and
which has a neighbourhood on which `⋀ʳ⁺¹` of every stalk vanishes. -/
noncomputable def stalkDeterminantTopBasisOfNbhd (x : ↥X) (r : ℕ)
    (b : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) {W : Opens ↥X} (hxW : x ∈ W)
    (hW : ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(r + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y))) :
    Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk A.determinant.val.presheaf x) :=
  stalkDeterminantTopBasis A x r b (bijective_stalkMapL_determinantSummand A x r b)
    (bijective_stalkMapL_exteriorAnnihilator_ι A r x hxW hW)


variable {E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')

/-- **The stalk of `det(E) ⊗ det(E'')` is free of rank one** as soon as both factors' stalks
are. The stalk of a tensor product is the tensor product of the stalks ([Stacks, Tag 01CB]), and
a tensor product of two free modules of rank one is free of rank one. -/
noncomputable def stalkTensorDeterminantTopBasis (x : ↥X)
    (b : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk A.determinant.val.presheaf x))
    (b'' : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk A''.determinant.val.presheaf x)) :
    Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk
          (PresheafOfModules.tensorSheafVal Osharp A.determinant A''.determinant).presheaf x) :=
  ((Module.Basis.tensorProduct b b'').reindex Stacks.ExteriorPower.finOneProdEquiv).map
    (PresheafOfModules.tensorSheafStalkEquiv Osharp A.determinant A''.determinant x).symm

end Bases

/-! ### Surjectivity through a monomorphism -/

section Through

variable {M N P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk map of a composite is the composite of the stalk maps, pointwise. -/
private theorem stalkMapL_comp_apply (x : ↥X) (φ : M ⟶ N) (ψ : N ⟶ P)
    (s : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x ψ.val (PresheafOfModules.stalkMapL x φ.val s) =
      PresheafOfModules.stalkMapL x (φ ≫ ψ).val s :=
  congrFun (congrArg DFunLike.coe
    (_root_.SheafOfModules.stalkMapL_comp_of_comp_eq_comp x φ ψ (φ ≫ ψ) rfl)) s

/-- A morphism is surjective on the stalk at `x` as soon as its composite with a morphism that
is injective there is. -/
theorem surjective_stalkMapL_of_injective_comp (x : ↥X) (φ : M ⟶ N) (ψ : N ⟶ P)
    (hinj : Function.Injective (PresheafOfModules.stalkMapL x ψ.val))
    (hsurj : Function.Surjective (PresheafOfModules.stalkMapL x (φ ≫ ψ).val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x φ.val) := by
  intro t
  obtain ⟨s, hs⟩ := hsurj (PresheafOfModules.stalkMapL x ψ.val t)
  exact ⟨s, hinj ((stalkMapL_comp_apply x φ ψ s).trans hs)⟩

/-- A morphism is surjective on the stalk at `x` as soon as its precomposite with another
morphism is. -/
theorem surjective_stalkMapL_of_surjective_comp (x : ↥X) (φ : M ⟶ N) (ψ : N ⟶ P)
    (hsurj : Function.Surjective (PresheafOfModules.stalkMapL x (φ ≫ ψ).val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x ψ.val) := by
  intro t
  obtain ⟨s, hs⟩ := hsurj t
  exact ⟨PresheafOfModules.stalkMapL x φ.val s, (stalkMapL_comp_apply x φ ψ s).trans hs⟩

/-- A composite of two morphisms surjective on the stalk at `x` is surjective there. -/
theorem surjective_stalkMapL_comp (x : ↥X) (φ : M ⟶ N) (ψ : N ⟶ P)
    (hφ : Function.Surjective (PresheafOfModules.stalkMapL x φ.val))
    (hψ : Function.Surjective (PresheafOfModules.stalkMapL x ψ.val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x (φ ≫ ψ).val) := by
  intro t
  obtain ⟨b, hb⟩ := hψ t
  obtain ⟨a, ha⟩ := hφ b
  exact ⟨a, (stalkMapL_comp_apply x φ ψ a).symm.trans
    ((congrArg (PresheafOfModules.stalkMapL x ψ.val) ha).trans hb)⟩

/-- Surjectivity on a stalk transported along an equality of morphisms. -/
theorem surjective_stalkMapL_of_eq (x : ↥X) {φ ψ : M ⟶ N} (h : φ = ψ)
    (hs : Function.Surjective (PresheafOfModules.stalkMapL x φ.val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x ψ.val) := h ▸ hs

end Through

/-! ### Hitting a wedge of germs -/

section Hit

variable {E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  {S : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- A section whose image under `ψ` is a wedge of sections puts the wedge of their germs in the
image of the stalk map. -/
theorem exists_apply_eq_ιMulti_of_app_eq_wedgeSec {d : ℕ} (ψ : S ⟶ A.exteriorPower d) (x : ↥X)
    (W : Opens ↥X) (hxW : x ∈ W) (ξ₀ : ToType (S.val.obj (op W)))
    (t : Fin d → E.val.obj (op W))
    (hval : ψ.val.app (op W) ξ₀ = wedgeSec A (op W) d t)
    (e : ↑(TopCat.Presheaf.stalk (A.exteriorPower d).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^d ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (he : ∀ (W' : Opens ↥X) (hxW' : x ∈ W') (t' : Fin d → E.val.obj (op W')),
      e (TopCat.Presheaf.germ (A.exteriorPower d).val.presheaf W' x hxW'
          (wedgeSec A (op W') d t')) =
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) d
          fun i => TopCat.Presheaf.germ E.val.presheaf W' x hxW' (t' i)) :
    ∃ ξ, e (PresheafOfModules.stalkMapL x ψ.val ξ) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) d
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW (t i) := by
  refine ⟨TopCat.Presheaf.germ S.val.presheaf W x hxW ξ₀, ?_⟩
  refine Eq.trans (congrArg (fun y => e y)
    ((PresheafOfModules.stalkMapL_germ x ψ.val W hxW ξ₀).trans
      (congrArg (TopCat.Presheaf.germ (A.exteriorPower d).val.presheaf W x hxW) hval))) ?_
  exact he W hxW t

/-- **A morphism into `⋀ᵈ E` is surjective on the stalk at `x`** as soon as some section over a
neighbourhood of `x` is carried to a wedge of sections whose germs wedge to a generator of
`⋀ᵈ(E_x)`. -/
theorem surjective_stalkMapL_of_app_eq_wedgeSec {d : ℕ} (ψ : S ⟶ A.exteriorPower d) (x : ↥X)
    (W : Opens ↥X) (hxW : x ∈ W) (ξ₀ : ToType (S.val.obj (op W)))
    (t : Fin d → E.val.obj (op W))
    (hval : ψ.val.app (op W) ξ₀ = wedgeSec A (op W) d t)
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) d
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW (t i)} = ⊤) :
    Function.Surjective (PresheafOfModules.stalkMapL x ψ.val) := by
  obtain ⟨e, he⟩ := exists_exteriorPowerStalkEquiv_wedgeSec A d x
  obtain ⟨ξ, hξ⟩ := exists_apply_eq_ιMulti_of_app_eq_wedgeSec A ψ x W hxW ξ₀ t hval e he
  exact Stacks.ExteriorPower.surjective_of_span_singleton_eq_top _ e hspan ξ hξ

end Hit

/-! ### The wedge-and-lift formula at a determinant summand -/

section WedgeLift

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)

/-- Multiplying the image of a section of `⋀ⁿ E'` that is a wedge of sections by a wedge of
sections of `E` gives the wedge of the images with the sections of `E`. -/
private theorem mul_extHom_wedgeSec_append {n : ℕ}
    {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (u : P ⟶ A'.exteriorPower n) (m : ℕ) (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V)
    (s : Fin n → E'.val.obj V) (hw : u.val.app V w = wedgeSec A' V n s)
    (l : Fin m → E.val.obj V) :
    (A.exterior.mul (n : ℤ) (m : ℤ)).app V
        (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w)) (wedgeSec A V m l) =
      wedgeSec A V (n + m) (Fin.append (fun i => f.val.app V (s i)) l) := by
  rw [hw]
  refine Eq.trans (congrArg (fun z => (A.exterior.mul (n : ℤ) (m : ℤ)).app V z
      (wedgeSec A V m l)) (extHom_wedgeSec A' A f V n s)) ?_
  refine Eq.trans (homogeneousProd_append A.exterior.toPresheafGradedAlgebra V n m _ _) ?_
  exact congrArg (wedgeProd A.exterior V (n + m))
    (fin_append_comp (A.exteriorGenerator.val.app V) (fun i => f.val.app V (s i)) l).symm

/-- The tensor product with a fixed first factor, computed on a local pure tensor. -/
private theorem sheafTensor_obj_map_val_app_tensorSheafUnit
    (F G G' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (φ : G ⟶ G') (V : (Opens ↥X)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).obj F).map φ).val.app V
        ((PresheafOfModules.tensorSheafUnit F G).app V (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit F G').app V (x ⊗ₜ φ.val.app V y) := by
  have mapUnit :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp _ _
      (𝟙 F) φ V x y
  have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).map (𝟙 F)).app
      G = 𝟙 _ :=
    NatTrans.congr_app
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} Osharp).map_id _) _
  rw [hid, Category.id_comp] at mapUnit
  exact mapUnit

/-- **The wedge-and-lift formula for `Stacks.SheafOfModules.TopWedge.detComparisonFrom` when the
image of the section of `P` in `⋀ⁿ E'` is itself a wedge of sections.** This is the shape in
which the formula exhibits an element of the image: the value is the wedge of the images of the
sections of `E'` with arbitrary local lifts of the sections of `E''`. -/
theorem detComparisonFrom_wedge_append {n : ℕ}
    {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (u : P ⟶ A'.exteriorPower n)
    (hu : ∀ (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V) (a : E'.val.obj V),
      (A.exterior.mul (n : ℤ) 1).app V
          (((extHom A' A f).app (n : ℤ)).val.app V (u.val.app V w))
        (A.exteriorGenerator.val.app V (f.val.app V a)) = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (k : ℕ) (V : (Opens ↥X)ᵒᵖ)
    (w : P.val.obj V) (s : Fin n → E'.val.obj V)
    (hw : u.val.app V w = wedgeSec A' V n s) (l : Fin (k + 1) → E.val.obj V) :
    (detComparisonFrom A' A A'' f g hfg u hu hS k).val.app V
        ((PresheafOfModules.tensorSheafUnit P (A''.exteriorPower (k + 1))).app V
          (w ⊗ₜ wedgeSec A'' V (k + 1) fun i => g.val.app V (l i))) =
      wedgeSec A V (n + (k + 1)) (Fin.append (fun i => f.val.app V (s i)) l) := by
  exact (detComparisonFrom_wedge A' A A'' f g hfg u hS k hu V w l).trans
    (mul_extHom_wedgeSec_append A' A f u (k + 1) V w s hw l)

/-- **The wedge map out of `P` on a pure tensor of wedges of sections.** If the image of the
section of `P` in `⋀ⁿ E'` is the wedge of `s`, the value on `w ⊗ (l₁ ∧ ⋯ ∧ l_m)` is the wedge of
the images of the `sᵢ` with the `lⱼ`. -/
theorem wedgeHomFrom_unit_wedge_append {n : ℕ}
    {P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (u : P ⟶ A'.exteriorPower n) (m : ℕ) (V : (Opens ↥X)ᵒᵖ) (w : P.val.obj V)
    (s : Fin n → E'.val.obj V) (hw : u.val.app V w = wedgeSec A' V n s)
    (l : Fin m → E.val.obj V) :
    (wedgeHomFrom A' A f u m).val.app V
        ((PresheafOfModules.tensorSheafUnit P (A.exteriorPower m)).app V
          (w ⊗ₜ wedgeSec A V m l)) =
      wedgeSec A V (n + m) (Fin.append (fun i => f.val.app V (s i)) l) := by
  exact (wedgeHomFrom_unit A' A f u m V w _).trans
    (mul_extHom_wedgeSec_append A' A f u m V w s hw l)

/-- The degree-zero identification of the two exterior algebras takes the unit to the unit: both
`exteriorPieceIso_zero` do, by the `exteriorPieceIso_zero_one` field. -/
theorem exteriorPowerZeroIso_hom_one (V : (Opens ↥X)ᵒᵖ) :
    (exteriorPowerZeroIso A A'').hom.val.app V (A''.exterior.one.eval V) =
      A.exterior.one.eval V := by
  have hcomp : (exteriorPowerZeroIso A A'').hom =
      A''.exteriorPieceIso_zero.hom ≫ A.exteriorPieceIso_zero.inv := rfl
  rw [hcomp]
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
  rw [A''.exteriorPieceIso_zero_one V, ← A.exteriorPieceIso_zero_one V]
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app A.exteriorPieceIso_zero V _

/-- **The wedge-and-lift formula for the degree-zero comparison.** In degree zero of the second
factor there is nothing to lift: the unit of the exterior algebra of `E''` goes to the unit of
that of `E`, and multiplying by it changes nothing. -/
theorem annTensorExteriorHomZero_unit_wedge (n : ℕ) (V : (Opens ↥X)ᵒᵖ)
    (w : ToType ((A'.exteriorAnnihilator n).toSheafOfModules.val.obj V))
    (s : Fin n → E'.val.obj V)
    (hw : (A'.exteriorAnnihilator n).ι.val.app V w = wedgeSec A' V n s)
    (z : ToType ((A''.exteriorAnnihilator 0).toSheafOfModules.val.obj V))
    (l : Fin 0 → E.val.obj V)
    (hz : (A''.exteriorAnnihilator 0).ι.val.app V z =
      wedgeSec A'' V 0 fun i => g.val.app V (l i))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] :
    (annTensorExteriorHomZero A' A A'' f n).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorAnnihilator n).toSheafOfModules
          (A''.exteriorAnnihilator 0).toSheafOfModules).app V (w ⊗ₜ z)) =
      wedgeSec A V (n + 0) (Fin.append (fun i => f.val.app V (s i)) l) := by
  have hone : ((A''.exteriorAnnihilator 0).ι ≫ (exteriorPowerZeroIso A A'').hom).val.app V z =
      wedgeSec A V 0 l := by
    refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
    rw [hz]
    exact exteriorPowerZeroIso_hom_one A A'' V
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
  refine Eq.trans (congrArg ((wedgeHomFrom A' A f (A'.exteriorAnnihilator n).ι 0).val.app V)
    (sheafTensor_obj_map_val_app_tensorSheafUnit _ _ _
      ((A''.exteriorAnnihilator 0).ι ≫ (exteriorPowerZeroIso A A'').hom) V w z)) ?_
  rw [hone]
  exact wedgeHomFrom_unit_wedge_append A' A f (A'.exteriorAnnihilator n).ι 0 V w s hw l

/-- **The wedge-and-lift formula for the comparison between determinant summands**, in degree
`k + 1` of the second factor. -/
theorem annTensorExteriorHom_unit_wedge
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n k : ℕ)
    (V : (Opens ↥X)ᵒᵖ)
    (w : ToType ((A'.exteriorAnnihilator n).toSheafOfModules.val.obj V))
    (s : Fin n → E'.val.obj V)
    (hw : (A'.exteriorAnnihilator n).ι.val.app V w = wedgeSec A' V n s)
    (z : ToType ((A''.exteriorAnnihilator (k + 1)).toSheafOfModules.val.obj V))
    (l : Fin (k + 1) → E.val.obj V)
    (hz : (A''.exteriorAnnihilator (k + 1)).ι.val.app V z =
      wedgeSec A'' V (k + 1) fun i => g.val.app V (l i)) :
    (annTensorExteriorHom A' A A'' f g hfg hS n k).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorAnnihilator n).toSheafOfModules
          (A''.exteriorAnnihilator (k + 1)).toSheafOfModules).app V (w ⊗ₜ z)) =
      wedgeSec A V (n + (k + 1)) (Fin.append (fun i => f.val.app V (s i)) l) := by
  refine Eq.trans (_root_.SheafOfModules.comp_val_app_apply _ _ V _) ?_
  refine Eq.trans (congrArg
    ((detAnnihilatorComparison A' A A'' f g hfg hS n k).val.app V)
    (sheafTensor_obj_map_val_app_tensorSheafUnit _ _ _
      (A''.exteriorAnnihilator (k + 1)).ι V w z)) ?_
  rw [hz]
  exact detComparisonFrom_wedge_append A' A A'' f g hfg (A'.exteriorAnnihilator n).ι
    (mul_extHom_exteriorAnnihilator_ι_eq_zero A' A f n) hS k V w s hw l

/-- **The wedge-and-lift formula for the comparison between determinant summands**, in every
pair of degrees, read inside `⋀ⁿ⁺ᵐ E` through the inclusion of the degree-`n+m` summand of
`det(E)`.

This is the wedge-and-lift formula of [Stacks, Tag 0B38] in the general case: a short exact
sequence of finite locally free sheaves with no constant-rank hypothesis. On the summand
`det(E')ₙ ⊗ det(E'')ₘ` of `det(E') ⊗ det(E'')` the canonical map of
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantHom` carries the image of
`(s₁∧⋯∧sₙ) ⊗ (g(l₁)∧⋯∧g(lₘ))` to `f(s₁)∧⋯∧f(sₙ)∧l₁∧⋯∧lₘ`, for **arbitrary** local lifts `lⱼ`.
This is the formula the source gives for its canonical map, and
`Stacks.SheafOfModules.TopWedge.eq_determinantTensorDeterminantHom` and
`Stacks.SheafOfModules.TopWedge.eq_detTensorAnnComparison` say it determines the map. -/
@[stacks 0B38 "the WEDGE-AND-LIFT FORMULA in the GENERAL case, with no constant-rank hypothesis"]
theorem detSummandComparison_ι_unit_wedge
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n m : ℕ)
    (V : (Opens ↥X)ᵒᵖ)
    (w : ToType ((A'.exteriorAnnihilator n).toSheafOfModules.val.obj V))
    (s : Fin n → E'.val.obj V)
    (hw : (A'.exteriorAnnihilator n).ι.val.app V w = wedgeSec A' V n s)
    (z : ToType ((A''.exteriorAnnihilator m).toSheafOfModules.val.obj V))
    (l : Fin m → E.val.obj V)
    (hz : (A''.exteriorAnnihilator m).ι.val.app V z =
      wedgeSec A'' V m fun i => g.val.app V (l i)) :
    (detSummandComparison A' A A'' f g hfg hS n m ≫
          (A.exteriorAnnihilator (n + m)).ι).val.app V
        ((PresheafOfModules.tensorSheafUnit (A'.exteriorAnnihilator n).toSheafOfModules
          (A''.exteriorAnnihilator m).toSheafOfModules).app V (w ⊗ₜ z)) =
      wedgeSec A V (n + m) (Fin.append (fun i => f.val.app V (s i)) l) := by
  cases m with
  | zero =>
      change (annTensorAnnHomZero A' A A'' f g hfg hS n ≫
        (A.exteriorAnnihilator (n + 0)).ι).val.app V _ = _
      rw [annTensorAnnHomZero_ι A' A A'' f g hfg hS n]
      exact annTensorExteriorHomZero_unit_wedge A' A A'' f g n V w s hw z l hz
  | succ k =>
      change (annTensorAnnHom A' A A'' f g hfg hS n k ≫
        (A.exteriorAnnihilator (n + (k + 1))).ι).val.app V _ = _
      rw [annTensorAnnHom_ι A' A A'' f g hfg hS n k]
      exact annTensorExteriorHom_unit_wedge A' A A'' f g hfg hS n k V w s hw z l hz

end WedgeLift

/-! ### The chart at a point -/

section Chart

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- `Stacks.SheafOfModules.TopWedge.exists_common_germ` with the neighbourhood required to lie
inside a prescribed one. -/
theorem exists_common_germ_le
    (M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (x : ↥X) (U : Opens ↥X) (hxU : x ∈ U) {r m : ℕ}
    (v : Fin r → ↑(TopCat.Presheaf.stalk M.val.presheaf x))
    (w : Fin m → ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ (W : Opens ↥X) (hxW : x ∈ W) (_ : W ≤ U) (s : Fin r → M.val.obj (op W))
      (l : Fin m → N.val.obj (op W)),
      (∀ i, TopCat.Presheaf.germ M.val.presheaf W x hxW (s i) = v i) ∧
        ∀ j, TopCat.Presheaf.germ N.val.presheaf W x hxW (l j) = w j := by
  obtain ⟨W₀, hxW₀, s₀, l₀, hs, hl⟩ := exists_common_germ M N x v w
  have hxW : x ∈ W₀ ⊓ U := ⟨hxW₀, hxU⟩
  refine ⟨W₀ ⊓ U, hxW, inf_le_right,
    fun i => M.val.presheaf.map (homOfLE inf_le_left).op (s₀ i),
    fun j => N.val.presheaf.map (homOfLE inf_le_left).op (l₀ j), fun i => ?_, fun j => ?_⟩
  · exact (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE inf_le_left) x hxW
      (s₀ i)).trans (hs i)
  · exact (TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE inf_le_left) x hxW
      (l₀ j)).trans (hl j)

/-- The germ family of the appended sections is the appended family of germs. -/
theorem germ_fin_append_eq (f : E' ⟶ E) (x : ↥X) {W : Opens ↥X} (hxW : x ∈ W) {r' r'' : ℕ}
    (s : Fin r' → E'.val.obj (op W)) (l : Fin r'' → E.val.obj (op W))
    (b' : Fin r' → ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (w : Fin r'' → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hs : ∀ i, TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i) = b' i)
    (hl : ∀ j, TopCat.Presheaf.germ E.val.presheaf W x hxW (l j) = w j) :
    (fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
        (Fin.append (fun j => f.val.app (op W) (s j)) l i)) =
      Fin.append (fun j => PresheafOfModules.stalkMapL x f.val (b' j)) w := by
  refine Eq.trans (fin_append_comp (TopCat.Presheaf.germ E.val.presheaf W x hxW) _ l) ?_
  refine congrArg₂ Fin.append (funext fun j => ?_) (funext fun j => hl j)
  exact (PresheafOfModules.stalkMapL_germ x f.val W hxW (s j)).symm.trans
    (congrArg (PresheafOfModules.stalkMapL x f.val) (hs j))

/-- **A basis of the middle stalk and the single wedge generating its top exterior power**, from
bases of the two outer stalks. This is
`Stacks.ExteriorPower.exists_span_ιMulti_append_eq_top` at the stalk sequence; the exactness of
that sequence is taken as a hypothesis, supplied by
`Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact`. -/
theorem exists_span_append_stalk (f : E' ⟶ E) (g : E ⟶ E'') (x : ↥X)
    (hinjf : Function.Injective (PresheafOfModules.stalkMapL x f.val))
    (hsurjg : Function.Surjective (PresheafOfModules.stalkMapL x g.val))
    (hex : LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val))
    {r' r'' : ℕ}
    (b' : Module.Basis (Fin r') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (b'' : Module.Basis (Fin r'') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x)) :
    ∃ w : Fin r'' → ↑(TopCat.Presheaf.stalk E.val.presheaf x),
      Nonempty (Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)) ∧
      Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
          (Fin.append (fun j => PresheafOfModules.stalkMapL x f.val (b' j)) w)} = ⊤ := by
  obtain ⟨w, bM, _, hspan⟩ := Stacks.ExteriorPower.exists_span_ιMulti_append_eq_top
    (PresheafOfModules.stalkMapL x f.val) (PresheafOfModules.stalkMapL x g.val)
    hinjf hsurjg hex b' b''
  exact ⟨w, ⟨bM⟩, hspan⟩

/-- The single wedge of germs the wedge-and-lift formula produces generates the top exterior
power of the middle stalk. -/
theorem span_germ_fin_append_eq_top (f : E' ⟶ E) (x : ↥X) {W : Opens ↥X} (hxW : x ∈ W)
    {r' r'' : ℕ} (s : Fin r' → E'.val.obj (op W)) (l : Fin r'' → E.val.obj (op W))
    (b' : Fin r' → ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (w : Fin r'' → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hs : ∀ i, TopCat.Presheaf.germ E'.val.presheaf W x hxW (s i) = b' i)
    (hl : ∀ j, TopCat.Presheaf.germ E.val.presheaf W x hxW (l j) = w j)
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
        (Fin.append (fun j => PresheafOfModules.stalkMapL x f.val (b' j)) w)} = ⊤) :
    Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
          (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤ :=
  (congrArg (fun v => Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
    {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'') v})
      (germ_fin_append_eq f x hxW s l b' w hs hl)).trans hspan

/-- **The chart at a point**: sections of `E'` over a neighbourhood inside `U` whose germs are
the given basis of `E'_x`, and sections of `E` whose germs complete their images to a basis of
`E_x`, so that the single wedge of their germs generates `⋀^{r'+r''}(E_x)`. -/
theorem exists_chart_of_span (f : E' ⟶ E) (x : ↥X) {r' r'' : ℕ}
    (b' : Fin r' → ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (w : Fin r'' → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hbM : Nonempty (Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)))
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
        (Fin.append (fun j => PresheafOfModules.stalkMapL x f.val (b' j)) w)} = ⊤)
    (U : Opens ↥X) (hxU : x ∈ U) :
    ∃ (W : Opens ↥X) (hxW : x ∈ W) (_ : W ≤ U) (s : Fin r' → E'.val.obj (op W))
      (l : Fin r'' → E.val.obj (op W)),
      Nonempty (Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)) ∧
      Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
          fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
            (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤ := by
  obtain ⟨W, hxW, hWU, s, l, hs, hl⟩ := exists_common_germ_le E' E x U hxU b' w
  refine ⟨W, hxW, hWU, s, l, hbM, ?_⟩
  exact span_germ_fin_append_eq_top f x hxW s l b' w hs hl hspan

/-- **The chart at a point, with the exactness of the stalk sequence and the bases of the two
outer stalks given.** -/
theorem exists_chart_of_stalkExact (f : E' ⟶ E) (g : E ⟶ E'') (x : ↥X)
    (hinjf : Function.Injective (PresheafOfModules.stalkMapL x f.val))
    (hsurjg : Function.Surjective (PresheafOfModules.stalkMapL x g.val))
    (hex : LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val))
    {r' r'' : ℕ}
    (b' : Module.Basis (Fin r') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (b'' : Module.Basis (Fin r'') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x))
    (U : Opens ↥X) (hxU : x ∈ U) :
    ∃ (W : Opens ↥X) (hxW : x ∈ W) (_ : W ≤ U) (s : Fin r' → E'.val.obj (op W))
      (l : Fin r'' → E.val.obj (op W)),
      Nonempty (Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)) ∧
      Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
          fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
            (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤ :=
  (exists_span_append_stalk f g x hinjf hsurjg hex b' b'').elim
    fun w hw => exists_chart_of_span f x (fun i => b' i) w hw.1 hw.2 U hxU

end Chart

/-! ### Vanishing of the exterior powers above the rank, near a point -/

section Vanishing

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The exterior powers of a stalk above its rank vanish, over the whole of a neighbourhood on
which the rank is constant. -/
@[sga "6 VII 4.1" "special case"]
theorem subsingleton_exteriorPower_stalk_of_free
    {F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    {r : ℕ} {W : Opens ↥X}
    (hfree : ∀ y ∈ W, Nonempty (↑(TopCat.Presheaf.stalk F.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y)))) :
    ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(r + 1)
      ↑(TopCat.Presheaf.stalk F.val.presheaf y)) :=
  fun y hy => Stacks.ExteriorPower.subsingleton_exteriorPower_of_lt
    (Module.Basis.ofRepr (hfree y hy).some) (by omega)

/-- **`⋀^{r'+r''+1}` of every stalk of the middle term vanishes over a neighbourhood on which
the two ends have constant ranks `r'` and `r''`**, because the middle stalk is free of rank
`r' + r''` at every such point. -/
theorem subsingleton_exteriorPower_stalk_middle (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] {r' r'' : ℕ} {W : Opens ↥X}
    (hfree' : ∀ y ∈ W, Nonempty (↑(TopCat.Presheaf.stalk E'.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r' →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))))
    (hfree'' : ∀ y ∈ W, Nonempty (↑(TopCat.Presheaf.stalk E''.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r'' →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y)))) :
    ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(r' + r'' + 1)
      ↑(TopCat.Presheaf.stalk E.val.presheaf y)) := by
  intro y hy
  obtain ⟨hinjf, hsurjg, hex⟩ := stalkMapL_shortExact f g hfg hS y
  obtain ⟨b⟩ := nonempty_stalkBasis_append f g y hinjf hsurjg hex
    (Module.Basis.ofRepr (hfree' y hy).some) (Module.Basis.ofRepr (hfree'' y hy).some)
  exact Stacks.ExteriorPower.subsingleton_exteriorPower_of_lt b (by omega)

end Vanishing

/-! ### Stacks 0B38 for a short exact sequence of finite locally free sheaves -/

section Iso

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)

/-- **The comparison `det(E') ⊗ det(E'')ₘ ⟶ det(E)` is surjective on the stalk at `x`** as soon
as the comparison between the two surviving summands and the inclusion of the surviving summand
of `det(E)` are. This is the defining equation
`Stacks.SheafOfModules.TopWedge.map_determinantSummand_comp_detTensorAnnComparison` read on
stalks. -/
theorem surjective_stalkMapL_detTensorAnnComparison
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) (n m : ℕ)
    (h1 : Function.Surjective (PresheafOfModules.stalkMapL x
      (detSummandComparison A' A A'' f g hfg hS n m).val))
    (h2 : Function.Surjective (PresheafOfModules.stalkMapL x
      (A.determinantSummand (n + m)).val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (detTensorAnnComparison A' A A'' f g hfg hS m).val) := by
  refine surjective_stalkMapL_of_surjective_comp x
    ((Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (Opens.grothendieckTopology ↥X) Osharp
        (A''.exteriorAnnihilator m).toSheafOfModules).map
      (Limits.Sigma.ι (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) n))
    (detTensorAnnComparison A' A A'' f g hfg hS m) ?_
  refine surjective_stalkMapL_of_eq x
    (map_determinantSummand_comp_detTensorAnnComparison A' A A'' f g hfg hS n m).symm ?_
  exact surjective_stalkMapL_comp x _ _ h1 h2

/-- **The canonical map `det(E') ⊗ det(E'') ⟶ det(E)` is surjective on the stalk at `x`** as
soon as the comparison between the two surviving summands and the inclusion of the surviving
summand of `det(E)` are. This is the defining equation
`Stacks.SheafOfModules.TopWedge.map_determinantSummand_comp_determinantTensorDeterminantHom`
read on stalks. -/
theorem surjective_stalkMapL_determinantTensorDeterminantHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) (n m : ℕ)
    (h1 : Function.Surjective (PresheafOfModules.stalkMapL x
      (detSummandComparison A' A A'' f g hfg hS n m).val))
    (h2 : Function.Surjective (PresheafOfModules.stalkMapL x
      (A.determinantSummand (n + m)).val)) :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (determinantTensorDeterminantHom A' A A'' f g hfg hS).val) := by
  refine surjective_stalkMapL_of_surjective_comp x
    ((Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp A'.determinant).map
      (Limits.Sigma.ι (fun j : ℕ => (A''.exteriorAnnihilator j).toSheafOfModules) m))
    (determinantTensorDeterminantHom A' A A'' f g hfg hS) ?_
  refine surjective_stalkMapL_of_eq x
    (map_determinantSummand_comp_determinantTensorDeterminantHom A' A A'' f g hfg hS m).symm ?_
  exact surjective_stalkMapL_detTensorAnnComparison A' A A'' f g hfg hS x n m h1 h2

/-- **The comparison between the two surviving determinant summands is surjective on the stalk
at `x`.** Its composite with the inclusion of the summand of `det(E)` hits the wedge the
wedge-and-lift formula produces, which generates `⋀^{n+m}(E_x)`, and that inclusion is injective
on stalks. -/
theorem surjective_stalkMapL_detSummandComparison
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) (n m : ℕ)
    (W : Opens ↥X) (hxW : x ∈ W)
    (w₀ : ToType ((A'.exteriorAnnihilator n).toSheafOfModules.val.obj (op W)))
    (s : Fin n → E'.val.obj (op W))
    (hw : (A'.exteriorAnnihilator n).ι.val.app (op W) w₀ = wedgeSec A' (op W) n s)
    (z₀ : ToType ((A''.exteriorAnnihilator m).toSheafOfModules.val.obj (op W)))
    (l : Fin m → E.val.obj (op W))
    (hz : (A''.exteriorAnnihilator m).ι.val.app (op W) z₀ =
      wedgeSec A'' (op W) m fun i => g.val.app (op W) (l i))
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (n + m)
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
          (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤) :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (detSummandComparison A' A A'' f g hfg hS n m).val) := by
  refine surjective_stalkMapL_of_injective_comp x _ (A.exteriorAnnihilator (n + m)).ι
    (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.injective_submoduleStalkι x) ?_
  refine surjective_stalkMapL_of_app_eq_wedgeSec A _ x W hxW
    ((PresheafOfModules.tensorSheafUnit (A'.exteriorAnnihilator n).toSheafOfModules
      (A''.exteriorAnnihilator m).toSheafOfModules).app (op W) (w₀ ⊗ₜ z₀))
    (Fin.append (fun j => f.val.app (op W) (s j)) l) ?_ hspan
  exact detSummandComparison_ι_unit_wedge A' A A'' f g hfg hS n m (op W) w₀ s hw z₀ l hz



/-- **The canonical map is surjective on the stalk at `x`, from a chart at `x`.** The
wedge-and-lift formula applied to the chart's sections hits a generator of `⋀^{r'+r''}(E_x)`,
and the two sections involved are exterior annihilated because the ranks are constant on the
chart's neighbourhood. -/
theorem surjective_stalkMapL_determinantTensorDeterminantHom_of_chart
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) {r' r'' : ℕ}
    {W : Opens ↥X} (hxW : x ∈ W)
    (hsub' : ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(r' + 1)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf y)))
    (hsub'' : ∀ y ∈ W, Subsingleton ↥(⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(r'' + 1)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf y)))
    (s : Fin r' → E'.val.obj (op W)) (l : Fin r'' → E.val.obj (op W))
    (bM : Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
          (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤) :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (determinantTensorDeterminantHom A' A A'' f g hfg hS).val) := by
  have hann' : A'.IsExteriorAnnihilated r' (wedgeSec A' (op W) r' s) :=
    isExteriorAnnihilated_of_forall_subsingleton_stalk A' r' hsub' W le_rfl _
  have hann'' : A''.IsExteriorAnnihilated r''
      (wedgeSec A'' (op W) r'' fun i => g.val.app (op W) (l i)) :=
    isExteriorAnnihilated_of_forall_subsingleton_stalk A'' r'' hsub'' W le_rfl _
  refine surjective_stalkMapL_determinantTensorDeterminantHom A' A A'' f g hfg hS x r' r''
    (surjective_stalkMapL_detSummandComparison A' A A'' f g hfg hS x r' r'' W hxW
      (show ToType ((A'.exteriorAnnihilator r').toSheafOfModules.val.obj (op W)) from
        ⟨wedgeSec A' (op W) r' s, hann'⟩) s rfl
      (show ToType ((A''.exteriorAnnihilator r'').toSheafOfModules.val.obj (op W)) from
        ⟨wedgeSec A'' (op W) r'' fun i => g.val.app (op W) (l i), hann''⟩) l rfl hspan)
    (bijective_stalkMapL_determinantSummand A x (r' + r'') bM).2

/-- **The canonical map is bijective on the stalk at `x`, from a chart at `x`.** Surjectivity is
the content; injectivity follows because source and target have free stalks of rank one at `x`. -/
theorem bijective_stalkMapL_determinantTensorDeterminantHom_of_chart
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) {r' r'' : ℕ}
    {W : Opens ↥X} (hxW : x ∈ W)
    (hfree' : ∀ y ∈ W, Nonempty (↑(TopCat.Presheaf.stalk E'.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r' →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))))
    (hfree'' : ∀ y ∈ W, Nonempty (↑(TopCat.Presheaf.stalk E''.val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj y)]
      (Fin r'' →₀ ↑(TopCat.Presheaf.stalk Osharp.obj y))))
    (s : Fin r' → E'.val.obj (op W)) (l : Fin r'' → E.val.obj (op W))
    (bM : Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + r'')
        fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW
          (Fin.append (fun j => f.val.app (op W) (s j)) l i)} = ⊤) :
    Function.Bijective (PresheafOfModules.stalkMapL x
      (determinantTensorDeterminantHom A' A A'' f g hfg hS).val) := by
  have hsurj := surjective_stalkMapL_determinantTensorDeterminantHom_of_chart A' A A'' f g hfg hS
    x hxW (subsingleton_exteriorPower_stalk_of_free hfree')
    (subsingleton_exteriorPower_stalk_of_free hfree'') s l bM hspan
  refine ⟨?_, hsurj⟩
  exact Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one
    (stalkTensorDeterminantTopBasis A' A'' x
      (stalkDeterminantTopBasisOfNbhd A' x r' (Module.Basis.ofRepr (hfree' x hxW).some) hxW
        (subsingleton_exteriorPower_stalk_of_free hfree'))
      (stalkDeterminantTopBasisOfNbhd A'' x r'' (Module.Basis.ofRepr (hfree'' x hxW).some) hxW
        (subsingleton_exteriorPower_stalk_of_free hfree'')))
    (stalkDeterminantTopBasisOfNbhd A x (r' + r'') bM hxW
      (subsingleton_exteriorPower_stalk_middle f g hfg hS hfree' hfree'')) _ hsurj

/-- **The canonical map `det(E') ⊗ det(E'') ⟶ det(E)` is bijective on every stalk.** -/
theorem bijective_stalkMapL_determinantTensorDeterminantHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x
      (determinantTensorDeterminantHom A' A A'' f g hfg hS).val) := by
  obtain ⟨hinjf, hsurjg, hex⟩ := stalkMapL_shortExact f g hfg hS x
  obtain ⟨r', W', hxW', hfree'⟩ := exists_nbhd_forall_nonempty_stalkLinearEquiv_finsupp E' x
  obtain ⟨r'', W'', hxW'', hfree''⟩ := exists_nbhd_forall_nonempty_stalkLinearEquiv_finsupp E'' x
  obtain ⟨W, hxW, hWU, s, l, ⟨bM⟩, hspan⟩ := exists_chart_of_stalkExact f g x hinjf hsurjg hex
    (Module.Basis.ofRepr (hfree' x hxW').some) (Module.Basis.ofRepr (hfree'' x hxW'').some)
    (W' ⊓ W'') ⟨hxW', hxW''⟩
  exact bijective_stalkMapL_determinantTensorDeterminantHom_of_chart A' A A'' f g hfg hS x hxW
    (fun y hy => hfree' y (le_trans hWU inf_le_left hy))
    (fun y hy => hfree'' y (le_trans hWU inf_le_right hy)) s l bM hspan

/-- **Stacks 0B38: the canonical map `det(E') ⊗ det(E'') ⟶ det(E)` is an isomorphism**, for a
short exact sequence `0 → E' → E → E'' → 0` of sheaves of modules on a ringed space whose outer
terms are finite locally free of **no particular rank**. -/
@[stacks 0B38 "the ISOMORPHISM clause in the GENERAL case: the canonical map \
det(E')⊗det(E'')⟶det(E) of `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantHom` is \
an isomorphism, for a short exact sequence of finite locally free sheaves with NO constant-rank \
hypothesis. Here det is the det of 0FJN. The isomorphism itself is \
`determinantTensorDeterminantIsoOfFiniteLocallyFree`"]
theorem isIso_determinantTensorDeterminantHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] :
    IsIso (determinantTensorDeterminantHom A' A A'' f g hfg hS) := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (O := toRingCat (Opens.grothendieckTopology ↥X) Osharp)
    (determinantTensorDeterminantHom A' A A'' f g hfg hS)).2 fun x => ?_
  obtain ⟨hinj, hsurj⟩ :=
    bijective_stalkMapL_determinantTensorDeterminantHom A' A A'' f g hfg hS x
  refine ⟨fun a b hab => ?_, fun ζ => ?_⟩
  · exact hinj ((stalkMap_hom_apply _ x a).symm.trans (hab.trans (stalkMap_hom_apply _ x b)))
  · obtain ⟨ξ, hξ⟩ := hsurj ζ
    exact ⟨ξ, (stalkMap_hom_apply _ x ξ).trans hξ⟩


/-- **The comparison `det(E') ⊗ det(E'')ₘ ⟶ det(E)` is the only morphism restricting to the
comparison between summands on every degree-`n` summand of `det(E')`**, the summand inclusions
being jointly epimorphic. -/
theorem eq_detTensorAnnComparison
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (m : ℕ)
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj
        ((A''.exteriorAnnihilator m).toSheafOfModules) ⟶ A.determinant)
    (hψ : ∀ n : ℕ, (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
            (Opens.grothendieckTopology ↥X) Osharp
            (A''.exteriorAnnihilator m).toSheafOfModules).map
          (Limits.Sigma.ι (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) n) ≫ ψ =
        detSummandComparison A' A A'' f g hfg hS n m ≫ A.determinantSummand (n + m)) :
    ψ = detTensorAnnComparison A' A A'' f g hfg hS m := by
  refine Limits.Cofan.IsColimit.hom_ext (isColimitCofanTensorAnnLeft A' A'' m) _ _ fun n => ?_
  exact (hψ n).trans
    (map_determinantSummand_comp_detTensorAnnComparison A' A A'' f g hfg hS n m).symm

/-- **The canonical map is the only morphism restricting to
`Stacks.SheafOfModules.TopWedge.detTensorAnnComparison` on every degree-`m` summand of
`det(E'')`.** Together with `Stacks.SheafOfModules.TopWedge.eq_detTensorAnnComparison` and the
wedge-and-lift formula `Stacks.SheafOfModules.TopWedge.detSummandComparison_ι_unit_wedge` this
is the precise sense in which the map of [Stacks, Tag 0B38] is *canonical*. -/
@[stacks 0B38 "uniqueness of the canonical map det(E')⊗det(E'')⟶det(E) in the GENERAL case — a \
short exact sequence of finite locally free sheaves of modules with no constant-rank \
hypothesis. Together with `eq_detTensorAnnComparison` and the wedge-and-lift formula \
`detSummandComparison_ι_unit_wedge` this says the map is determined by the formula the source \
gives for it"]
theorem eq_determinantTensorDeterminantHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'']
    (ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj A''.determinant
        ⟶ A.determinant)
    (hψ : ∀ m : ℕ, (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
            (Opens.grothendieckTopology ↥X) Osharp A'.determinant).map
          (Limits.Sigma.ι (fun j : ℕ => (A''.exteriorAnnihilator j).toSheafOfModules) m) ≫ ψ =
        detTensorAnnComparison A' A A'' f g hfg hS m) :
    ψ = determinantTensorDeterminantHom A' A A'' f g hfg hS := by
  refine Limits.Cofan.IsColimit.hom_ext (isColimitCofanTensorAnnRight A' A'') _ _ fun m => ?_
  exact (hψ m).trans
    (map_determinantSummand_comp_determinantTensorDeterminantHom A' A A'' f g hfg hS m).symm

/-- **Stacks 0B38, the general case.** For a short exact sequence `0 → E' → E → E'' → 0` of
sheaves of `O_X`-modules on a ringed space with `E'` and `E''` **finite locally free of no
particular rank**, there is a canonical isomorphism

`det(E') ⊗_{O_X} det(E'') ≅ det(E)`

of the determinants of [Stacks, Tag 0FJN] — the annihilator of the degree-one part of the
exterior algebra.

The underlying map is `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantHom`, which
`Stacks.SheafOfModules.TopWedge.detSummandComparison_ι_unit_wedge` pins to the wedge-and-lift
formula the source gives for it, which the uniqueness statements
`Stacks.SheafOfModules.TopWedge.eq_determinantTensorDeterminantHom` and
`Stacks.SheafOfModules.TopWedge.eq_detTensorAnnComparison` show that formula determines, and
which `Stacks.SheafOfModules.TopWedge.isIso_determinantTensorDeterminantHom` shows is an
isomorphism.

No hypothesis on `E` is needed: the freeness of its stalks is derived from the split stalk
sequence, so the statement is a strengthening of the one in the source, which assumes all three
terms finite locally free. -/
@[stacks 0B38 "the canonical isomorphism det(E')⊗det(E'')≅det(E) in the GENERAL case, with NO \
constant-rank hypothesis", sga "6 X 5.1" "special case"]
noncomputable def determinantTensorDeterminantIsoOfFiniteLocallyFree
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj A''.determinant ≅
        A.determinant :=
  have := isIso_determinantTensorDeterminantHom A' A A'' f g hfg hS
  asIso (determinantTensorDeterminantHom A' A A'' f g hfg hS)

/-- The isomorphism of [Stacks, Tag 0B38] in the general case is the canonical map. -/
theorem determinantTensorDeterminantIsoOfFiniteLocallyFree_hom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] :
    (determinantTensorDeterminantIsoOfFiniteLocallyFree A' A A'' f g hfg hS).hom =
      determinantTensorDeterminantHom A' A A'' f g hfg hS := rfl

end Iso

end Stacks.SheafOfModules.TopWedge

end
