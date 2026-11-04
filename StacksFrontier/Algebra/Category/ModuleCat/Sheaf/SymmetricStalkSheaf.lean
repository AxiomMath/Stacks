module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01CH, symmetric clause: the stalk of a symmetric power of a sheaf of modules

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `M` a sheaf of
`O♯`-modules and `A` a symmetric algebra of `M` in the sense of Stacks Section 17.21. Stacks Tag
01CH asserts canonical isomorphisms of `O_x`-modules between the stalk of each of `T(M)`,
`Sym(M)`, `⋀(M)` and the corresponding construction applied to the stalk `M_x`. This file proves
the symmetric assertion in each graded degree:

`(Symⁿ M)_x ≅ Symⁿ_{O_x}(M_x)`,

together with the formula that pins the isomorphism down: it carries the germ at `x` of the local
section `s₀ ⋯ sₙ₋₁` of `Symⁿ M` to the product of the germs of the `sᵢ`.

The proof is the composition Stacks gives. Tag 01CG
(`SheafOfModules.symmetricPower_isSheafification`, with
`SheafOfModules.symPowCmp_eq_sheafifyUnit_comp` the factorization it rests on) says that `Symⁿ M`
is the sheafification of the presheaf `U ↦ Symⁿ_{O♯(U)}(M(U))`, with the comparison morphism
`SheafOfModules.GradedAlgebra.symPowCmp` as the sheafification map. Sheafification does not change
stalks. And the stalk of that presheaf is `Symⁿ` of the stalk, which is
`PresheafOfModules.symPowStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk`.

## Main definitions

* `SheafOfModules.sheafifyStalkLinearEquiv` : the sheafification unit of a presheaf of modules is
  a linear isomorphism on stalks. This is `PresheafOfModules.isIso_stalkFunctor_map_toSheafify`
  read through Mathlib's `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`.
* `SheafOfModules.valPresheafMapIso` and `SheafOfModules.valStalkLinearEquivOfIso` : an
  isomorphism of sheaves of modules, read as an isomorphism of the underlying presheaves of
  `O♯`-modules, and the linear isomorphism it induces on stalks.
* `SheafOfModules.symPowStalkEquivOfIso` : the stalk of any sheaf of modules isomorphic to the
  sheafification of `U ↦ Symⁿ_{O♯(U)}(M(U))` is `Symⁿ_{O_x}(M_x)`.
* `SheafOfModules.symmetricPowerStalkEquiv` : **the comparison isomorphism of Tag 01CH in degree
  `n`**, obtained by instantiating the previous definition at
  `SheafOfModules.symmetricPieceIso`, the degreewise identification of Tag 01CG. Its hypotheses are
  those of `SheafOfModules.symmetricPower_isSheafification`: a sheaf of graded algebras `A`, a
  degree-one generator `gen : M ⟶ A.piece 1`, and the universal property making `A` a symmetric
  algebra of `M`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricPowerStalkEquiv` and
  `SheafOfModules.ringedSpaceSymmetricPowerStalkEquiv` : the same comparison for the symmetric
  algebra supplied by a package of the three algebras of Section 17.21, and for the chosen package
  on a ringed space, which is the form Section 17.21 states its lemmas in.

## Main results

* `SheafOfModules.symPowStalkEquivOfIso_germ` : the comparison carries the germ of the image of a
  local section of `U ↦ Symⁿ_{O♯(U)}(M(U))` to the base change of that section along the germ
  maps. With `SymPow.symmetricPower` spanned by products of degree-one generators
  (`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`) this determines the comparison.
* `SheafOfModules.symmetricPowerStalkEquiv_germ_prod_ι` : **the comparison on a product of local
  sections.** The germ of the image under `symPowCmp` of a product of `n` degree-one generators
  goes to the product of the germs of those generators.
* `SheafOfModules.symmetricPowerStalkEquiv_germ_homogeneousProd` : the same formula with the local
  section of `Symⁿ M` written using the data of `A` alone, as the ordered product in `A` of the
  images of the `sᵢ` under its degree-one generator. This is the form the tagged statement uses,
  so that statement mentions no sheafification and no comparison morphism.
* `SheafOfModules.symmetricPower_stalk` : **Tag 01CH, symmetric clause, in degree `n`** — the
  isomorphism and that formula assembled into the single assertion that a comparison isomorphism
  with that behaviour on germs of products exists. This is the declaration carrying the tag.

## Implementation notes

**Which clause of Tag 01CH is proved, and which are open.** Tag 01CH makes three assertions. Only
the symmetric one is treated here, and only in each fixed graded degree: the statement proved is
`(Symⁿ M)_x ≅ Symⁿ(M_x)` for every `n`.

The ungraded symmetric assertion `Sym(M)_x ≅ Sym(M_x)` is proved from this one in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded`, as
`SheafOfModules.symmetricAlgebra_stalk`. The sheaf of modules underlying `Sym(M)` is the
coproduct `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricAlgebraSheaf`, whose stalk is
the direct sum of the stalks of the pieces because the module stalk functor preserves colimits
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits` in
`StacksFrontier.Topology.Sheaves.Modules.Colimits`, which carries `@[stacks 01AH]`), and
`SymmetricAlgebra.directSumSymmetricPowerEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading` reassembles
`⨁ n, Symⁿ(M_x)` into `Sym(M_x)`.

The tensor assertion is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk`: degreewise as
`SheafOfModules.tensorPower_stalk` and ungraded as `SheafOfModules.tensorAlgebra_stalk`, both
pinned on germs of ordered tensors of local sections. The exterior assertion is proved in each
graded degree, as `PresheafOfModules.extPowStalkEquivOfStalkIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`, and ungraded as
`SheafOfModules.exteriorAlgebra_stalk` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`, which obtains the passage
from graded to ungraded from `SheafOfModules.stalkCoprodEquiv`. Note that it is the three
*ungraded* isomorphisms that the source asserts; the degreewise statement proved here is this
library's clause convention, a strictly stronger input rather than one of the source's three.

**The symmetric algebra is a hypothesis, not a chosen term**, exactly as in
`SheafOfModules.symmetricPower_isSheafification`: Section 17.21 pins it only up to canonical
isomorphism. `SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val` shows the
hypothesis is satisfiable for every `M`, and
`SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricPowerStalkEquiv` discharges it from a
package of the three algebras.

**Every degree is a variable.** No statement below instantiates a numeral degree.
`SymmetricAlgebra R N` is a reducible abbreviation for a `RingCon` quotient of `TensorAlgebra R N`,
so with a numeral degree `whnf` unfolds `SymPow.symmetricPower (1 + 1)` through `Submodule.mul`
and `Submodule.span` into that quotient; this is fatal while elaborating a *statement*, not only
in a proof. The one numeral that appears, in `gen : M ⟶ A.piece 1`, is the degree of a piece of an
*abstract* sheaf of graded algebras, where there is nothing to unfold — the same device
`SheafOfModules.GradedAlgebra.mul_congr` uses.

**Two spellings of the stalk of a sheaf of modules.** `PresheafOfModules.stalkLinearEquiv` is
stated for presheaves of modules over `O♯.obj ⋙ forget₂ CommRingCat RingCat`, so the morphisms fed
to it are first moved along `PresheafOfModules.restrictScalars` by `valPresheafMapIso`; the
statements, however, are phrased with `N.val.presheaf` rather than
`(SheafOfModules.valPresheaf _ N).presheaf`, the two being the same presheaf of abelian groups.
Similarly `symPowStalkEquivOfIso` takes its hypothesis as an isomorphism onto
`(PresheafOfModules.moduleSheafification _ (𝟙 O♯.obj)).obj (PresheafOfModules.symPow n F)`, which
is the degree-`n` piece of `SheafOfModules.sectionwiseSymmetricAlgebra` by `rfl`, and that is how
`SheafOfModules.symmetricPieceIso` is accepted for it. Each such bridge is isolated in its own
declaration and used through its ascribed type: both the sheafification unit written as
`CategoryTheory.toSheafify` and the symmetric powers written with an unpinned universe exhaust the
heartbeat limit when the elaborator is left to reconcile them inside a larger term.

**Universes.** The space, the ring and the module universe are all `u`. That is forced, not
chosen: Mathlib's instance `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` in
`Mathlib/Algebra/Category/ModuleCat/Stalk.lean` exists at no other combination, which is the
constraint already recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerStalk`. Independently,
`SheafOfModules.symmetricPieceIso` is stated at `GradedAlgebra.{w, w}`, so the ring and module
universes of the symmetric algebra agree there too. Tag 01CH is stated in the equal-universe case
and nothing the source says is narrowed.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### The sheafification unit is a stalk isomorphism -/

/-- **The sheafification unit of a presheaf of modules is a stalk isomorphism.** The underlying
morphism of presheaves of abelian groups of the unit of
`PresheafOfModules.sheafificationAdjunction` is `CategoryTheory.toSheafify` — Mathlib's
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, which holds by `rfl` — and
that morphism induces an isomorphism on stalks. -/
theorem isIso_stalkFunctor_map_sheafifyUnit
    (M : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (x : ↥X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (PresheafOfModules.sheafifyUnit
          (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) M))) :=
  PresheafOfModules.isIso_stalkFunctor_map_toSheafify x M.presheaf

/-- **Sheafification does not change stalks**, as a linear isomorphism over the stalk of the
sheaf of rings: the sheafification unit of a presheaf of `O♯`-modules induces an isomorphism from
the stalk of the presheaf to the stalk of the sheafification. -/
noncomputable def sheafifyStalkLinearEquiv
    (M : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (x : ↥X) :
    ↑(TopCat.Presheaf.stalk M.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk ((PresheafOfModules.moduleSheafification
        (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)).obj M).val.presheaf x) :=
  PresheafOfModules.stalkLinearEquiv x
    (PresheafOfModules.sheafifyUnit
      (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) M)
    (isIso_stalkFunctor_map_sheafifyUnit M x)

/-- `sheafifyStalkLinearEquiv` sends the germ of a local section `y` of `M` to the germ of its
image under the sheafification unit. -/
theorem sheafifyStalkLinearEquiv_germ
    (M : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (y : M.obj (op U)) :
    sheafifyStalkLinearEquiv M x (TopCat.Presheaf.germ M.presheaf U x hx y) =
      TopCat.Presheaf.germ ((PresheafOfModules.moduleSheafification
          (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)).obj M).val.presheaf U x hx
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj)) M) (op U) y) :=
  PresheafOfModules.stalkMapL_germ x _ U hx y

/-! ### Transport along an isomorphism of sheaves of modules -/

variable {N₁ N₂ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- An isomorphism of sheaves of modules, read as an isomorphism of the underlying presheaves of
modules over the presheaf of rings `O♯.obj`. -/
noncomputable def valPresheafMapIso (e : N₁ ≅ N₂) :
    valPresheaf (Opens.grothendieckTopology ↥X) N₁ ≅
      valPresheaf (Opens.grothendieckTopology ↥X) N₂ :=
  (PresheafOfModules.restrictScalars
      (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))).mapIso
    ((SheafOfModules.forget (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).mapIso e)

/-- The morphism of presheaves of abelian groups underlying `valPresheafMapIso e` induces an
isomorphism on the stalk at every point. -/
theorem isIso_stalkFunctor_map_valPresheafMapIso (e : N₁ ≅ N₂) (x : ↥X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf
        (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map
          (valPresheafMapIso e).hom)) := inferInstance

/-- An isomorphism of sheaves of modules induces a linear isomorphism of stalks over the stalk of
the sheaf of rings. -/
noncomputable def valStalkLinearEquivOfIso (e : N₁ ≅ N₂) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk N₁.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk N₂.val.presheaf x) :=
  PresheafOfModules.stalkLinearEquiv x (valPresheafMapIso e).hom
    (isIso_stalkFunctor_map_valPresheafMapIso e x)

/-- `valStalkLinearEquivOfIso e` sends the germ of a local section `y` of `N₁` to the germ of its
image under `e.hom`. -/
theorem valStalkLinearEquivOfIso_germ (e : N₁ ≅ N₂) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (y : N₁.val.obj (op U)) :
    valStalkLinearEquivOfIso e x (TopCat.Presheaf.germ N₁.val.presheaf U x hx y) =
      TopCat.Presheaf.germ N₂.val.presheaf U x hx
        (PresheafOfModules.Hom.app e.hom.val (op U) y) :=
  PresheafOfModules.stalkMapL_germ x _ U hx y

/-! ### The stalk of a sheafification of the sectionwise symmetric powers -/

/-- **The stalk of any sheaf of modules exhibited as the sheafification of the presheaf of
sectionwise symmetric powers.** If `e` identifies `N` with the sheafification of
`U ↦ Symⁿ_{O♯(U)}(F(U))` then the stalk of `N` at `x` is the `n`-th symmetric power of the stalk
of `F`.

This is the point-local half of Tag 01CH in the form Tag 01CG delivers it: sheafification does not
change stalks (`sheafifyStalkLinearEquiv`), and the stalk of the presheaf of sectionwise symmetric
powers is the symmetric power of the stalk (`PresheafOfModules.symPowStalkEquiv`). -/
noncomputable def symPowStalkEquivOfIso
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.symPow n F))
    (x : ↥X) :
    ↑(TopCat.Presheaf.stalk N.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk F.presheaf x) :=
  ((valStalkLinearEquivOfIso e x).trans (sheafifyStalkLinearEquiv
    (PresheafOfModules.symPow n F) x).symm).trans (PresheafOfModules.symPowStalkEquiv F x n)

/-- `symPowStalkEquivOfIso n e x` is the composite of `valStalkLinearEquivOfIso e x`, the inverse
of `sheafifyStalkLinearEquiv`, and `PresheafOfModules.symPowStalkEquiv`. -/
theorem symPowStalkEquivOfIso_apply
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.symPow n F))
    (x : ↥X) (t : ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    symPowStalkEquivOfIso n e x t =
      PresheafOfModules.symPowStalkEquiv F x n
        ((sheafifyStalkLinearEquiv (PresheafOfModules.symPow n F) x).symm
          (valStalkLinearEquivOfIso e x t)) := rfl

/-- **The comparison of `symPowStalkEquivOfIso` on a local section.** The germ of the image in `N`
of a local section `y` of `U ↦ Symⁿ_{O♯(U)}(F(U))` — the image under the sheafification unit
followed by `e.inv` — goes to the base change of `y` along the germ maps. Since the sections of
the sheafified presheaf are locally of this form, this determines the comparison. -/
theorem symPowStalkEquivOfIso_germ
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.symPow n F))
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (y : (PresheafOfModules.symPow n F).obj (op U)) :
    symPowStalkEquivOfIso n e x (TopCat.Presheaf.germ N.val.presheaf U x hx
        (PresheafOfModules.Hom.app e.inv.val (op U)
          (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
            (PresheafOfModules.symPow n F)) (op U) y))) =
      PresheafOfModules.symPowStalkEquiv F x n
        (TopCat.Presheaf.germ (PresheafOfModules.symPow n F).presheaf U x hx y) := by
  refine Eq.trans (symPowStalkEquivOfIso_apply n e x _) (congrArg _ ?_)
  rw [LinearEquiv.symm_apply_eq, valStalkLinearEquivOfIso_germ, sheafifyStalkLinearEquiv_germ]
  exact congrArg _ (SheafOfModules.hom_congr_app_apply e.inv_hom_id (op U) _)

/-- **The comparison of `symPowStalkEquivOfIso` on a product of degree-one generators.** The germ
of the image of `s₀ ⋯ sₙ₋₁` goes to the product of the germs of the `sᵢ`. -/
theorem symPowStalkEquivOfIso_germ_prod_ι
    {F : PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (n : ℕ)
    {N : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : N ≅ (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
      (𝟙 Osharp.obj)).obj (PresheafOfModules.symPow n F))
    (x : ↥X) (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → F.obj (op U)) :
    (symPowStalkEquivOfIso n e x (TopCat.Presheaf.germ N.val.presheaf U x hx
          (PresheafOfModules.Hom.app e.inv.val (op U)
            (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
                (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
                (PresheafOfModules.symPow n F)) (op U)
              ⟨∏ i : Fin n, SymmetricAlgebra.ι
                  ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
                  (F.obj (op U)) (s i),
                SymmetricAlgebra.prod_ι_mem _ s⟩))) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk F.presheaf x)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk F.presheaf x)
        (TopCat.Presheaf.germ F.presheaf U x hx (s i)) :=
  (congrArg Subtype.val (symPowStalkEquivOfIso_germ n e x U hx _)).trans
    (PresheafOfModules.symPowStalkL_germ_prod_ι F x n U hx s)

/-! ### Tag 01CH for the symmetric powers of a sheaf of modules -/

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hgen : GradedAlgebra.PairwiseCommutes gen)
  (hA : GradedAlgebra.IsSymmetricAlgebra A gen)

/-- **The comparison isomorphism of Tag 01CH in degree `n`**: for a symmetric algebra `A` of a
sheaf of modules `M`, the stalk at `x` of the degree-`n` symmetric power `A.piece n` is the `n`-th
symmetric power of the stalk `M_x` over the stalk ring `O_x`.

This is `symPowStalkEquivOfIso` at `SheafOfModules.symmetricPieceIso`, the degreewise
identification of Tag 01CG: the degree-`n` piece of
`SheafOfModules.sectionwiseSymmetricAlgebra` is the sheafification of
`U ↦ Symⁿ_{O♯(U)}(M(U))` by `rfl`. -/
@[ega "II 1.7.4" "partial"]
noncomputable def symmetricPowerStalkEquiv (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  symPowStalkEquivOfIso n (symmetricPieceIso M A gen hA (n : ℤ)).symm x

/-- **The comparison isomorphism of Tag 01CH on a product of local sections.** The germ at `x` of
the local section `s₀ ⋯ sₙ₋₁` of `Symⁿ M` — the image of the product of the degree-one generators
of the `sᵢ` under the comparison morphism `SheafOfModules.GradedAlgebra.symPowCmp` of Tag 01CG —
goes to the product of the germs of the `sᵢ`.

Such products span the `n`-th symmetric power of the stalk
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), so this formula determines
`symmetricPowerStalkEquiv` and is what makes it the *canonical* isomorphism of Tag 01CH rather
than merely one. -/
theorem symmetricPowerStalkEquiv_germ_prod_ι (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M.val.obj (op U)) :
    (symmetricPowerStalkEquiv A gen hA n x
          (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
            (PresheafOfModules.Hom.app
              (A.symPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
                gen hgen n) (op U)
              ⟨∏ i : Fin n, SymmetricAlgebra.ι
                  ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U))
                  (M.val.obj (op U)) (s i),
                SymmetricAlgebra.prod_ι_mem _ s⟩)) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x)
        (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) := by
  refine Eq.trans (congrArg (fun z => (symmetricPowerStalkEquiv A gen hA n x
      (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx z) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x)))
    (PresheafOfModules.hom_congr_apply'
      (symPowCmp_eq_sheafifyUnit_comp M A gen hgen hA n) (op U) _)) ?_
  exact symPowStalkEquivOfIso_germ_prod_ι n (symmetricPieceIso M A gen hA (n : ℤ)).symm x U hx s

/-- **The comparison isomorphism of Tag 01CH on an ordered product of degree-one sections.** This
is `symmetricPowerStalkEquiv_germ_prod_ι` with the local section of `Symⁿ M` written in terms of
the data of `A` alone: `Stacks.GradedAlgebra.cmpSections_prod_ι` identifies the image under
`symPowCmp` of a product of `n` degree-one generators with the ordered product, in `A`, of the
images of those sections under the degree-one generator `gen`. -/
theorem symmetricPowerStalkEquiv_germ_homogeneousProd (n : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin n → M.val.obj (op U)) :
    (symmetricPowerStalkEquiv A gen hA n x
          (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
              fun i => gen.val.app (op U) (s i))) :
        SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x)) =
      ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x)
        (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) := by
  rw [← Stacks.GradedAlgebra.cmpSections_prod_ι A.toPresheafGradedAlgebra gen.val
    (fun _ u v => hA.1 _ u v) n (op U) s]
  exact symmetricPowerStalkEquiv_germ_prod_ι A gen hA.1 hA n x U hx s

include hA in
/-- **Tag 01CH, symmetric clause, in graded degree `n`.** For a sheaf of modules `M` on a
topological space with a sheaf of commutative rings `O♯`, a symmetric algebra `A` of `M` in the
sense of Section 17.21, and a point `x`, there is a canonical isomorphism of `O_x`-modules

`(Symⁿ M)_x ≅ Symⁿ_{O_x}(M_x)`.

It is canonical in the sense Tag 01CH means: its value is prescribed on the germ of every local
section of the form `s₀ ⋯ sₙ₋₁`, namely the product of the germs of the `sᵢ`, and such products
span the target (`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`), so no other linear map has
that behaviour.

The symmetric algebra is a hypothesis rather than a chosen term because Section 17.21 pins it only
up to canonical isomorphism; `SheafOfModules.isSymmetricAlgebra_sectionwiseSymmetricAlgebra_val`
shows the hypothesis is satisfiable for every `M`, and
`SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricPowerStalkEquiv` discharges it from a
package of the three algebras of Section 17.21.

The tag carries a clause comment: this declaration carries the symmetric degreewise assertion
alone. The ungraded symmetric assertion `Sym(M)_x ≅ Sym(M_x)` is proved from this one in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded`, and the two tensor
assertions are `SheafOfModules.tensorPower_stalk` and `SheafOfModules.tensorAlgebra_stalk` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerStalk`.

The exterior assertion in each graded degree is
`PresheafOfModules.extPowStalkEquivOfStalkIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`, pinned on germs of wedges of
local sections by `PresheafOfModules.extPowStalkEquivOfStalkIso_germ_ιMulti`. It is stated there
for a presheaf of modules together with a morphism out of the sectionwise exterior powers which
is a stalk isomorphism — the form a sheafification presentation supplies — rather than in the
bundled framing used here; `SheafOfModules.exteriorPowerStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded` is the bundled form, and
`SheafOfModules.exteriorAlgebra_stalk` there is the ungraded exterior assertion. See the
implementation notes of this file. -/
@[stacks 01CH "the symmetric assertion in each graded degree `n`: `(Symⁿ M)ₓ ≅ Symⁿ(Mₓ)`, with \
the isomorphism pinned down by its values on germs of products of local sections. The ungraded \
`Sym(M)ₓ ≅ Sym(Mₓ)` is `SheafOfModules.symmetricAlgebra_stalk`; the exterior assertion in each \
degree is `PresheafOfModules.extPowStalkEquivOfStalkIso` and the ungraded \
`⋀(M)ₓ ≅ ⋀(Mₓ)` is `SheafOfModules.exteriorAlgebra_stalk`; the tensor assertions are \
`SheafOfModules.tensorPower_stalk` and `SheafOfModules.tensorAlgebra_stalk`. The three \
assertions the source makes are the ungraded ones; the degreewise statements, this one \
included, are this library's clause convention", ega "II 1.7.4" "partial"]
theorem symmetricPower_stalk (n : ℕ) (x : ↥X) :
    ∃ cmp : ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      ∀ (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
        (cmp (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
              (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
                fun i => gen.val.app (op U) (s i))) :
            SymmetricAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk M.val.presheaf x)) =
          ∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)
            (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)) :=
  ⟨symmetricPowerStalkEquiv A gen hA n x,
    fun U hx s => symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA n x U hx s⟩

end SheafOfModules

/-! ### The comparison for a package of the three algebras, and on a ringed space -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **Tag 01CH, symmetric clause, for a package of the three algebras of Section 17.21.** The
stalk of the degree-`n` symmetric power `Symⁿ G` supplied by the package is `Symⁿ` of the stalk
of `G`. -/
noncomputable def symmetricPowerStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.symmetricPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.symmetricPowerStalkEquiv A.symmetric A.symmetricGenerator
    A.symmetric_isSymmetricAlgebra n x

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

-- `structureSheafRing` reduces to `Y.presheaf ⋙ forget₂ _ _`, while the stalk instances
-- below are stated at `Y.sheaf.obj`; unfolding `SheafedSpace.sheaf` for instance search is what
-- identifies the two.
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- **Tag 01CH, symmetric clause, on a ringed space**, for the chosen package
`SheafOfModules.ringedSpaceAlgebras` of the three algebras of Section 17.21: the stalk of the
degree-`n` symmetric power of a sheaf of modules on a ringed space is `Symⁿ` of the stalk. This is
the form Section 17.21 states its lemmas in. -/
noncomputable def ringedSpaceSymmetricPowerStalkEquiv (Y : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf))
    (n : ℕ) (x : ↥Y.carrier) :
    ↑(TopCat.Presheaf.stalk ((ringedSpaceAlgebras Y G).symmetricPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)]
      ↥(SymPow.symmetricPower n ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
  TensorExteriorSymmetricAlgebras.symmetricPowerStalkEquiv (ringedSpaceAlgebras Y G) n x

end SheafOfModules

end
