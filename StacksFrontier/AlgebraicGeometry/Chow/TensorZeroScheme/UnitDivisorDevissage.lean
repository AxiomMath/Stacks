module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchChowInjective
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnitBranchGlobalEquation
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateChart

/-!
# Presenting a divisor as a `𝒪_X ⊗ ℒ` datum: the remaining inputs of Tag 0F99

[Stacks, Tag 0F99] takes a scheme `X` locally of finite type over the base situation of chapter
42 together with a triple `(ℒ, s, i : D ⟶ X)` as in [Stacks, Tag 0B8Y] — `ℒ` invertible, `s` a
global section of it, `D` its zero scheme — and produces a commutative square

  `D' --i'--> X'`
  `|p         |g`
  `D --i-->   X`

with four properties: `p` and `g` are of finite type and flat of relative dimension one; `p^*` is
injective on `A_k(D)` for every `k`; `D' ⊆ X'` is the zero scheme of a **global** section of
`𝒪_{X'}`; and `p^*i^* = (i')^*g^*`. It closes by asserting that all of this remains true after
arbitrary base change.

Its proof is [Stacks, Tag 0F97] applied with `ℒ₁ = 𝒪_X` and `ℒ₂ = ℒ`, taking `D' = D₁`, together
with [Stacks, Tag 0F98] for the fourth clause and [Stacks, Tag 0B74] for the injectivity. This
file supplies the two inputs of that argument which had no declaration.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.unitTensorUnitor` — the unitor `𝒪_X ⊗ ℒ ≅ ℒ` at the spelling the
  zero scheme is formed at.
* `Stacks.Chow.TensorZeroScheme.unitTensorSection` — **the given section `s` of `ℒ`, read as a
  section of `𝒪_X ⊗ ℒ`**, which is the shape [Stacks, Tag 0F97] takes as input.

## Main results

* `Stacks.Chow.TensorZeroScheme.zeroScheme_unitTensorSection` — **the divisor is unchanged by
  that re-reading**: the zero scheme of `s` read in `𝒪_X ⊗ ℒ` is the zero scheme of `s`. This is
  what makes `ℒ₁ = 𝒪_X` an instantiation of [Stacks, Tag 0F97] *at the given divisor* rather
  than at some other one.
* `Stacks.Chow.TensorZeroScheme.quasiCompact_of_iso_totalSpace` and
  `Stacks.Chow.TensorZeroScheme.quasiCompact_proj₁` — **the branch projection `p₁ : D₁ ⟶ D` is
  quasi-compact**, the half of "finite type" that
  `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchProjection` does not prove. The
  structure morphism of the total space of a line bundle is affine
  (`Stacks.LineBundle.Situation.isAffineHom_totalSpaceToBase`) and hence quasi-compact, and an
  isomorphism is quasi-compact, so condition (4) of [Stacks, Tag 0F97] carries it to `p₁`.

## The five clauses of Tag 0F99, and where each one now stands

Writing `g` for `Stacks.Chow.TensorZeroScheme.proj` and `p` for
`Stacks.Chow.TensorZeroScheme.proj₁` of the diagram instantiated at `L₁ = 𝒪_X`:

1. *`g` and `p` of finite type and flat of relative dimension one.* For `g`:
   `Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj`, `quasiCompact_proj`, `flat_proj`,
   `relativeDimension_proj`. For `p`: `locallyOfFiniteType_proj₁`, `flat_proj₁`,
   `relativeDimension_proj₁`, and `quasiCompact_proj₁` below.
2. *`p^*` injective on `A_k(D)` for every `k`.*
   `Stacks.Chow.TensorZeroScheme.flatPullbackChowProj₁_injective`.
3. *`D' ⊆ X'` the zero scheme of a global section of `𝒪_{X'}`.*
   `Stacks.Chow.TensorZeroScheme.exists_globalSection_branch₁_unit`, and in the form the
   base-change clause needs, `exists_globalSection_branch₁_of_iso`.
4. *`p^*i^* = (i')^*g^*`.*
   `Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj`, which is
   [Stacks, Tag 0F98].
5. *All of this after arbitrary base change.* The diagram base-changes by
   `Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`, which is the
   base-change clause of [Stacks, Tag 0F97]; and the base-changed datum is again one to which
   clauses (1)–(4) apply, because base change along `g : Y' ⟶ Y` replaces `L₁ = 𝒪_Y` by
   `g^*𝒪_Y`, which is isomorphic to `𝒪_{Y'}` by
   `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` — this is why clause (3) is proved above
   for an `L₁` merely isomorphic to the structure sheaf.

## Where `@[stacks 0F99]` sits

The tag is carried by
`Stacks.Chow.TensorZeroScheme.exists_principalReduction_isStableUnderBaseChange` of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.PrincipalReductionExistence`: one square
with all four properties (`Stacks.Chow.TensorZeroScheme.PrincipalReduction`), together with the
closing base-change assertion. The square is built from an *arbitrary* diagram of
[Stacks, Tag 0F97] by `Stacks.Chow.TensorZeroScheme.principalReductionOfDecomposition`, and its
clause (4) is [Stacks, Tag 0F98] for that diagram, which is proved for every diagram; that is what
makes the base-changed square, built from the base-changed diagram, satisfy all four clauses.

## References

* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

@[expose] public noncomputable section

namespace Stacks.Chow.TensorZeroScheme

/-! ### Quasi-compactness of the branch projections -/

section Transport

variable {D : Stacks.LineBundle.Situation.{u}} {Z : Scheme.{u}} (e : Z ≅ D.totalSpace)
  {g : Z ⟶ D.X} (hg : e.hom ≫ D.totalSpaceToBase = g)

include hg in
/-- **A morphism identifying its source with the total space of a line bundle over the target is
quasi-compact.** The structure morphism of the total space is affine, hence quasi-compact, and an
isomorphism is quasi-compact. This is the missing fourth member of the family
`Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_of_iso_totalSpace`, `flat_of_iso_totalSpace`,
`relativeDimension_of_iso_totalSpace`. -/
theorem quasiCompact_of_iso_totalSpace : QuasiCompact g := by
  subst hg
  have : QuasiCompact D.totalSpaceToBase := inferInstance
  infer_instance

end Transport

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

include h₁ h₂ in
/-- **The first branch projection `p₁ : D₁ ⟶ D` of [Stacks, Tag 0F97] is quasi-compact**, which
with `Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj₁` is the "finite type" half of clause
(1) of [Stacks, Tag 0F99] for `p`. -/
theorem quasiCompact_proj₁ (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) :
    QuasiCompact (proj₁ Y L₁ L₂ s) :=
  quasiCompact_of_iso_totalSpace (branchIso₁ Y L₁ L₂ s)
    (branchIso₁_hom_comp_totalSpaceToBase Y L₁ L₂ s)

include h₁ h₂ in
/-- **The second branch projection `p₂ : D₂ ⟶ D` of [Stacks, Tag 0F97] is quasi-compact.** -/
theorem quasiCompact_proj₂ (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) :
    QuasiCompact (proj₂ Y L₁ L₂ s) :=
  quasiCompact_of_iso_totalSpace (branchIso₂ Y L₁ L₂ s)
    (branchIso₂_hom_comp_totalSpaceToBase Y L₁ L₂ s)

/-! ### Reading a section of `ℒ` as a section of `𝒪_X ⊗ ℒ` -/

section Unitor

variable (X : Scheme.{u}) (L : X.Modules)
  [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

include h in
/-- **The unitor `𝒪_X ⊗ ℒ ≅ ℒ`**, at the spelling
`Stacks.Divisors.tensorModules` that the zero scheme of [Stacks, Tag
02OQ] is formed at and that the first module is `AlgebraicGeometry.Scheme.unitModule X`. -/
def unitTensorUnitor :
    Stacks.Divisors.tensorModules (Scheme.unitModule X) L ≅ L :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property L

include h in
/-- **A global section of `ℒ`, read as a global section of `𝒪_X ⊗ ℒ`.** This is the shape
[Stacks, Tag 0F97] takes as input, and so the shape in which the divisor of [Stacks, Tag 0F99]
is handed to it. -/
def unitTensorSection (s : Γ(L, ⊤)) :
    Γ(Stacks.Divisors.tensorModules (Scheme.unitModule X) L, ⊤) :=
  Scheme.Modules.Hom.app (unitTensorUnitor X L).inv ⊤ s

include h in
/-- **The divisor is unchanged by that re-reading.** The zero scheme of `s` read in `𝒪_X ⊗ ℒ` is
the zero scheme of `s`, by [Stacks, Tag 02OQ] — `AlgebraicGeometry.zeroScheme_eq_of_iso`, the
zero scheme depends only on the isomorphism class of the pair.

This is what makes instantiating [Stacks, Tag 0F97] at `ℒ₁ = 𝒪_X`, `ℒ₂ = ℒ` an instantiation at
*the divisor of [Stacks, Tag 0F99]* and not at some other closed subscheme: the `D` of the
instantiated diagram, `Stacks.Chow.TensorZeroScheme.zeroIdeal`, is the given `D = Z(s)`. -/
theorem zeroScheme_unitTensorSection (s : Γ(L, ⊤)) :
    AlgebraicGeometry.zeroScheme X
        (Stacks.Divisors.tensorModules (Scheme.unitModule X) L)
        (unitTensorSection X L s) =
      AlgebraicGeometry.zeroScheme X L s :=
  AlgebraicGeometry.zeroScheme_eq_of_iso (unitTensorUnitor X L)
    (Scheme.Modules.app_inv_app (unitTensorUnitor X L).symm ⊤ s)

end Unitor

/-! ### Trivializability of the first module is stable under base change -/

/-- **The pullback of a trivialized invertible module is trivialized.** If `L₁ ≅ 𝒪_Y` then
`g^*L₁ ≅ 𝒪_{Y'}`, so the hypothesis under which clause (3) of [Stacks, Tag 0F99] is proved in
`Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme_unitModule_of_iso` survives arbitrary base
change. This is the observation the tag's closing assertion rests on. -/
def pullbackIsoUnitModule {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {L₁ : Y.Modules}
    (ε : L₁ ≅ Scheme.unitModule Y) :
    (Scheme.Modules.pullback g).obj L₁ ≅ Scheme.unitModule Y' :=
  ((Scheme.Modules.pullback g).mapIso ε).trans (Scheme.Modules.pullbackUnitIso g)

end Stacks.Chow.TensorZeroScheme

end
