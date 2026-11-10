module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGESuccTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimitsUnconditional
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorAmplitude
import StacksCore.Tactic.StacksAttribute

/-!
# A functor on the modules of an algebraic space on a complex unbounded below

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `F : Mod(𝒪_X) ⥤ Ab` be an
additive functor commuting with countable direct products and let `(RF, α)` be a right derived
functor of `F` on the unbounded derived category `D(𝒪_X)`.  Let `N ≥ 0` be an integer with
`R^pF(ℱ) = 0` for every quasi-coherent `ℱ` and every `p ≥ N`.  This file proves, for **every**
`E` in `D_QCoh(𝒪_X)` and with no boundedness hypothesis whatsoever, the two assertions of
[Stacks, Tag 08F7] whose bound involves the integer `N`:

* assertion (2), that `H ^ i (RF E) ⟶ H ^ i (RF (τ_{≥ b - N + 1} E))` is an isomorphism for
  `i ≥ b`;
* the upper bound `b + N - 1` of assertion (3), i.e. that `H ^ i (RF E) = 0` for
  `i > b + N - 1` once `H ^ j (E) = 0` for `j > b`, with no hypothesis on the lower endpoint `a`
  of the source's range `-∞ ≤ a ≤ b ≤ ∞`.

These two statements are where Tag 08F7 is registered for those two clauses — one carrier each,
with no boundedness hypothesis on `E`, and they are the only registrations of those two clauses
in the library.  The bounded-`E` forms of the same two clauses are not stated: such a form binds
a lower endpoint `a` that the source's range `-∞ ≤ a ≤ b ≤ ∞` does not, so it would not state
the assertion it is about.  The bounded case enters only as the `private` ingredient
`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_bounded` of the proofs below.

Together with `AlgebraicGeometry.Space.isIso_homologyFunctor_map_rightDerived_truncLE`
(assertion (1)) and `AlgebraicGeometry.Space.isZero_homology_rightDerived_of_isZero_lt` (the
`i < a` half of assertion (3)), which carry the tag for their clauses, need no hypothesis beyond
additivity of `F` and hold at a free module universe, this completes the three assertions of
Tag 08F7 with four registrations, one per clause.

## Main results

* `AlgebraicGeometry.Space.isLE_rightDerived_obj_of_isLE`: a right derived functor of `F` carries
  an object of `D_QCoh(𝒪_X)` living in degrees `≤ c` to an object living in degrees
  `≤ c + N - 1`, with no lower bound on `E`.  This is the engine of both assertions, and carries
  no tag of its own.
* `AlgebraicGeometry.Space.isZero_homology_rightDerived_of_isZero_gt_unbounded`:
  **[Stacks, Tag 08F7], assertion (3), the upper bound, for every `E` of `D_QCoh(𝒪_X)`.**  The
  registered carrier of that half of assertion (3).
* `AlgebraicGeometry.Space.isIso_homologyFunctor_map_rightDerived_truncGE_unbounded`:
  **[Stacks, Tag 08F7], assertion (2), for every `E` of `D_QCoh(𝒪_X)`.**  The registered carrier
  of assertion (2).

Two auxiliary statements about the truncation tower are also exported, since they are of
independent use:

* `AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules`: [Stacks, Tag 08F6] in the form
  the limit argument consumes — `E` *is* a derived limit of the tower `n ↦ τ_{≥ -n} E` of its
  canonical truncations from below, the structural map being the canonical cone.  This is a
  restatement of the tagged
  `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_unconditional` and carries no
  tag of its own.
* `AlgebraicGeometry.Space.hasProduct_truncGETower_modules`: that tower has a product in
  `D(𝒪_X)`.

## Implementation notes

*The argument.*  It is the source's.  An object `E` of `D_QCoh(𝒪_X)` is the derived limit of the
tower `n ↦ τ_{≥ -n} E` ([Stacks, Tag 08F6], here
`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_unconditional` turned into a
derived-limit statement by `Stacks.InverseSystem.exists_distTriang_milnor_of_isIso`); `RF`
carries that derived limit to a derived limit because `F` commutes with countable products
([Stacks, Tag 08U1], `Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor` — this is the one
place the source's hypothesis (2) on `F` is consumed); every term `τ_{≥ -n} E` of the tower is
bounded, so `RF` of it lies in degrees `≤ c + N - 1` whenever `E` lies in degrees `≤ c`
(`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_bounded`); and the cohomology systems
`n ↦ H ^ i (RF (τ_{≥ -n} E))` are Mittag-Leffler, so the derived limit keeps that upper bound
(`Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler`, which is the Milnor sequence of
[Stacks, Tag 07KY] with its `R¹ lim` term killed by the Mittag-Leffler condition).  The two
assertions are then read off the canonical truncation triangle through the long exact homology
sequence, exactly as in the bounded case.

*The Mittag-Leffler condition.*  It is the source's argument too.  For each `n` the two
successive truncations sit in the distinguished triangle
`H^{-n-1}(E)[n+1] ⟶ τ_{≥ -n-1} E ⟶ τ_{≥ -n} E ⟶ H^{-n-1}(E)[n+2]` of [Stacks, Tag 08J5]
(`DerivedCategory.exists_truncGESucc_triangle`, whose middle map is pinned to the canonical
comparison of truncations and hence to the transition map of the tower).  Its first vertex is a
*quasi-coherent* module placed in degree `-n-1`, so `RF` of it lies in degrees
`≤ -n-1+N-1` by the vanishing hypothesis
(`Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj`); for `n ≥ N - i` that is below `i+1`,
so the connecting map of the long exact sequence vanishes and the transition map
`H ^ i (RF (τ_{≥ -n-1} E)) ⟶ H ^ i (RF (τ_{≥ -n} E))` is surjective.  A tower whose transition
maps are surjective from some stage on is Mittag-Leffler
(`Stacks.DerivedLimit.isMittagLeffler_of_eventually_surjective`).

*The module universe.*  It is `u`, the universe of the structure rings.  That is where
[Stacks, Tag 08F6] is unconditional: its two inputs are discharged in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedLimitsUnconditional.lean` only there,
for the reason recorded in that file.  The statements of
`QuasicoherentDerivedFunctorAmplitude.lean`, which need neither the derived limit nor the
countable-product hypothesis on `F`, are at a free module universe `m`; the two clauses proved
here are confined to `m = u`, which is in any case the universe at which `Mod(𝒪_X)` is the
category Tag 08F7 speaks of.  The ingredient `isLE_rightDerived_obj_of_bounded` below is the
`m = u` instance of a statement that holds for a free `m`.

*Instances at the module universe of the structure rings.*  `Modules.{u, u}` is
`SheafOfModules.{u}` on a site whose objects live in `Type (u + 1)`, so the library's
Grothendieck-abelianness and limit instances for sheaves of modules — which produce a module
universe at least that of the site's objects — do not match it by unification, and instance
search for `HasProductsOfShape ℕ` or `EnoughInjectives` there stalls on a universe constraint
rather than failing.  The four theorems
`AlgebraicGeometry.Space.hasProductsOfShape_nat_modules_ringUniverse`,
`AlgebraicGeometry.Space.enoughInjectives_modules_ringUniverse`,
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules_ringUniverse` and
`AlgebraicGeometry.Space.hasProduct_truncGETower_modules` name those instances once, with their
universes pinned, and are registered as local instances so that nothing below searches for them.
`attribute [local instance 5000] SheafOfModules.instAbelian` is needed for the same reason, as in
`QuasicoherentDerivedLimitsUnconditional.lean`.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.DerivedLimit Stacks.SmallDerivedCategory

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

/-- The triangle of [Stacks, Tag 08J5] relating two successive truncations from below, with the
upper cut supplied as a separate integer together with the equation naming it.

This is `DerivedCategory.exists_truncGESucc_triangle` with `a + 1` replaced by a variable `b`,
so that the canonical comparison of truncations occurring in it can be matched with the
transition map of `Stacks.DerivedLimit.truncGETower`, whose upper cut is written `-(n : ℤ)` and
not `-((n + 1 : ℕ) : ℤ) + 1`. -/
private theorem DerivedCategory.exists_truncGESucc_triangle' {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (E : DerivedCategory C) (a b : ℤ) (hb : a + 1 = b) :
    ∃ (f : (DerivedCategory.singleFunctor C a).obj
        ((DerivedCategory.homologyFunctor C a).obj E) ⟶
        (DerivedCategory.TStructure.t.truncGE a).obj E)
      (δ : (DerivedCategory.TStructure.t.truncGE b).obj E ⟶
        ((DerivedCategory.singleFunctor C a).obj
          ((DerivedCategory.homologyFunctor C a).obj E))⟦(1 : ℤ)⟧),
      Triangle.mk f ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b (by omega)).app E) δ ∈
        distTriang (DerivedCategory C) := by
  subst hb
  exact DerivedCategory.exists_truncGESucc_triangle E a

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-! ### Instances for the `𝒪_X`-modules at the universe of the structure rings -/

/-- The `𝒪_X`-modules on the small étale ringed site of an algebraic space have countable
products at the universe of the structure rings.

The universes of `SheafOfModules.hasLimitsOfShape` are pinned because the module universe `u` is
below the universe `u + 1` of the objects of the site, which is where instance search would put
it. -/
theorem hasProductsOfShape_nat_modules_ringUniverse :
    HasProductsOfShape ℕ (Modules.{u, u} B S hS X hX) :=
  SheafOfModules.hasLimitsOfShape.{u, u, 0, u + 1, 0, u} (Discrete ℕ)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

/-- The `𝒪_X`-modules on the small étale ringed site of an algebraic space have enough
injectives at the universe of the structure rings.

This is `AlgebraicGeometry.Space.enoughInjectives_modules`, named here so that the instance is
available to the statements below without an instance search that stalls on a universe
constraint. -/
theorem enoughInjectives_modules_ringUniverse :
    EnoughInjectives (Modules.{u, u} B S hS X hX) :=
  enoughInjectives_modules B S hS X hX

/-- The `𝒪_X`-modules on the small étale ringed site of an algebraic space are Grothendieck
abelian at the universe of the structure rings: the site is essentially small there. -/
theorem isGrothendieckAbelian_modules_ringUniverse :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  exact SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse

/-- Quasi-coherence of `𝒪_X`-modules at the module universe of the structure rings, read as a
`CategoryTheory.ObjectProperty` so that the truncation lemmas of
`Stacks.SmallDerivedCategory` apply to it. -/
private abbrev qcohU : ObjectProperty (Modules.{u, u} B S hS X hX) :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

/-! ### The truncation tower of an object of `D_QCoh(𝒪_X)` -/

/-- The `n`-th term `τ_{≥ -n} E` of the truncation tower lives in degrees `≥ -n`. -/
private theorem isGE_truncGETower_obj (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (n : ℕ) : ((truncGETower (Modules.{u, u} B S hS X hX) E).obj ⟨n⟩).IsGE (-(n : ℤ)) := by
  rw [truncGETower_obj]
  infer_instance

/-- The tower `n ↦ τ_{≥ -n} E` of canonical truncations from below of an object of `D(𝒪_X)` has a
product in `D(𝒪_X)`: each of its terms is bounded below, so [Stacks, Tag 0BK7] applies. -/
theorem hasProduct_truncGETower_modules
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) :
    HasProduct fun n : ℕ ↦ (truncGETower (Modules.{u, u} B S hS X hX) E).obj ⟨n⟩ := by
  obtain ⟨hp, -⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE
    (truncGETower (Modules.{u, u} B S hS X hX) E)
    (fun n ↦ ⟨-(n : ℤ), isGE_truncGETower_obj B S hS X hX E n⟩)
  exact hp

attribute [local instance] hasProduct_truncGETower_modules

/-- **[Stacks, Tag 08F6] as a derived limit.** An object of `D(𝒪_X)` all of whose cohomology
sheaves are quasi-coherent *is* a derived limit of the tower `n ↦ τ_{≥ -n} E` of its canonical
truncations from below.

This repackages `AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_unconditional`,
which says that the canonical map from `E` into any derived limit of the tower is invertible: a
derived limit `L` exists because every `τ_{≥ -n} E` is bounded below ([Stacks, Tag 0BK7]), the
canonical cone `Stacks.DerivedLimit.truncGETowerCone` lifts through the triangle presenting `L`
by `Stacks.DerivedLimit.truncGETowerCone_comp_diff`, and that lift is invertible, so `E` is a
derived limit too.

No `stacks` attribute: this is a restatement of the already tagged
`AlgebraicGeometry.Space.isIso_of_isDerivedLimit_truncGETower_unconditional` in the shape the
limit argument below consumes, not a second proof of Tag 08F6.  The scheme analogue
`AlgebraicGeometry.isDerivedLimit_truncGETower` is untagged for the same reason. -/
theorem isDerivedLimit_truncGETower_modules
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite) :
    IsDerivedLimit (truncGETower (Modules.{u, u} B S hS X hX) E) E := by
  obtain ⟨hprod, L, hL⟩ :=
    DerivedCategory.exists_isDerivedLimit_of_forall_isGE
      (truncGETower (Modules.{u, u} B S hS X hX) E)
      (fun n ↦ ⟨-(n : ℤ), isGE_truncGETower_obj B S hS X hX E n⟩)
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨c, hc⟩ := (Triangle.mk p _ δ).coyoneda_exact₂ hT
    (truncGETowerCone E) (truncGETowerCone_comp_diff E)
  change truncGETowerCone E = c ≫ p at hc
  have hciso : IsIso c := isIso_of_isDerivedLimit_truncGETower_unconditional B S hS X hX E hE
    L c p δ hT (fun n ↦ by rw [← Category.assoc, ← hc]; exact truncGETowerCone_comp_π E n)
  exact isDerivedLimit_of_iso _ ⟨p, δ, hT⟩ (asIso c).symm

/-! ### The upper bound with no lower bound on the complex -/

variable (F : Modules.{u, u} B S hS X hX ⥤ AddCommGrpCat.{u}) [F.Additive]
  [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory (Modules.{u, u} B S hS X hX) ⥤ DerivedCategory AddCommGrpCat.{u})
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))]

omit [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α in
/-- The structure map of a right derived functor out of `K(Mod(𝒪_X))` is invertible at every
K-injective complex of `𝒪_X`-modules, the modules of an algebraic space being Grothendieck
abelian so that K-injective resolutions exist. -/
private theorem isIso_app_isKInjective (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ)
    (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X hX)
      (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F RF α
    Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso I hI

omit [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α in
/-- **The upper bound of Tag 08F7 for a bounded complex.** Let `(RF, α)` be a right derived
functor of `F` and suppose the higher right derived functors `R^pF` vanish on quasi-coherent
modules in every degree `p ≥ N`.  Then `RF` carries an object of `D_QCoh(𝒪_X)` living in degrees
`[a, b]` to an object living in degrees `≤ b + N - 1`.

This is the dévissage `Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE`: a bounded object is
built out of finitely many shifted quasi-coherent modules by the canonical truncation triangles,
and on a single such module the vanishing hypothesis *is* the bound, by
`Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj`.  No countable-product hypothesis on `F`
is used, and no derived limit is taken; that is what confines the statement to a bounded `E`.

This is the input of the unbounded-below halves of assertions (2) and (3) below, which remove the
lower bound `a` by writing `E` as the derived limit of its truncations `τ_{≥ -n} E` and applying
this bound to each of them. -/
private theorem isLE_rightDerived_obj_of_bounded (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    (RF.obj E).IsLE (b + (N : ℤ) - 1) := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α
  have := hGE
  have := hLE
  have hSingle : ∀ M : Modules.{u, u} B S hS X hX, qcohU B S hS X hX M → ∀ n : ℤ,
      (RF.obj ((DerivedCategory.singleFunctor
        (Modules.{u, u} B S hS X hX) n).obj M)).IsLE (n + ((N : ℤ) - 1)) :=
    fun M hM n ↦ Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj F RF α
      (isIso_app_isKInjective B S hS X hX F RF α) M ((N : ℤ) - 1)
      (fun p hp ↦ hRF M hM p (by omega)) n
  have := Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE
    (qcohU B S hS X hX) RF ((N : ℤ) - 1) hSingle E hqc a b
  exact DerivedCategory.TStructure.t.isLE_of_le _ (b + ((N : ℤ) - 1))
    (b + (N : ℤ) - 1) (by omega)

omit [PreservesLimitsOfShape (Discrete ℕ) F] in
include F α in
/-- **The Mittag-Leffler condition on the cohomology of the tower.** Let `(RF, α)` be a right
derived functor of `F` and suppose the higher right derived functors `R^pF` vanish on
quasi-coherent modules in every degree `p ≥ N`.  Then for every object `E` of `D_QCoh(𝒪_X)` and
every `i` the inverse system of abelian groups `n ↦ H ^ i (RF (τ_{≥ -n} E))` is Mittag-Leffler.

The transition maps are in fact surjective from the stage `N - i` on.  Two successive
truncations differ by `H^{-n-1}(E)` placed in degree `-n-1` ([Stacks, Tag 08J5]), a
quasi-coherent module, so `RF` of that difference lies in degrees `≤ -n-1+N-1`; for `n ≥ N - i`
that is below `i + 1`, and the connecting map of the long exact homology sequence, whose target
is `H ^ (i+1)` of the difference, vanishes. -/
private theorem isMittagLeffler_homology_rightDerived_truncGETower (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (i : ℤ) :
    (((truncGETower (Modules.{u, u} B S hS X hX) E ⋙ RF) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) ⋙
        forget AddCommGrpCat.{u}).IsMittagLeffler := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α
  refine Stacks.DerivedLimit.isMittagLeffler_of_eventually_surjective (N - i).toNat ?_
  intro n hn
  have hnn : (N : ℤ) - i ≤ (n : ℤ) := by
    have := Int.toNat_le.1 hn
    omega
  obtain ⟨f, δ, hT⟩ := DerivedCategory.exists_truncGESucc_triangle' E
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by push_cast; ring)
  have hMqc : ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX)
      (-((n + 1 : ℕ) : ℤ))).obj E).IsQuasicoherentOnSite := hqc _
  have hsingle := isLE_obj_singleFunctor_obj F RF α (isIso_app_isKInjective B S hS X hX F RF α) _
    ((N : ℤ) - 1) (fun p hp ↦ hRF _ hMqc p (by omega)) (-((n + 1 : ℕ) : ℤ))
  have hz : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i + 1)).obj
      (RF.obj ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX)
        (-((n + 1 : ℕ) : ℤ))).obj ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS X hX) (-((n + 1 : ℕ) : ℤ))).obj E)))) := by
    have := hsingle
    exact DerivedCategory.isZero_of_isLE _ (-((n + 1 : ℕ) : ℤ) + ((N : ℤ) - 1)) (i + 1)
      (by push_cast at hnn ⊢; omega)
  have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (RF.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E))) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u}
      0).homologySequence_epi_shift_map_mor₂_iff _ (RF.map_distinguished _ hT) i (i + 1)
        rfl).2 (hz.eq_of_tgt _ _)
  have key : Function.Surjective ⇑((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (RF.map ((truncGETower (Modules.{u, u} B S hS X hX) E).map
        (homOfLE (Nat.le_succ n)).op))) := by
    rw [truncGETower_map_homOfLE_succ]
    exact (AddCommGrpCat.epi_iff_surjective _).1 hepi
  exact key

include F α in
/-- **The upper bound of [Stacks, Tag 08F7] for an arbitrary object of `D_QCoh(𝒪_X)`.** Let
`(RF, α)` be a right derived functor of an additive functor `F` commuting with countable
products, and suppose the higher right derived functors `R^pF` vanish on quasi-coherent modules
in every degree `p ≥ N`.  Then `RF` carries an object of `D_QCoh(𝒪_X)` living in degrees `≤ c` to
an object living in degrees `≤ c + N - 1`, with **no** lower bound on `E`.

`E` is the derived limit of the tower of its truncations from below
(`AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules`, [Stacks, Tag 08F6]); `RF` carries
that derived limit to a derived limit, `F` commuting with countable products
(`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`, [Stacks, Tag 08U1]); each term of
the tower is bounded, so `RF` of it lies in degrees `≤ c + N - 1`
(`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_bounded`); and the cohomology systems of the
tower are Mittag-Leffler, so the derived limit keeps that bound
(`Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler`).  No degree is lost: the
`R¹ lim` term of the Milnor sequence, which is what the hypothesis-free bound
`Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit` has to pay a degree for, vanishes. -/
theorem isLE_rightDerived_obj_of_isLE (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (c : ℤ) (hLE : E.IsLE c) : (RF.obj E).IsLE (c + (N : ℤ) - 1) := by
  have := hLE
  obtain ⟨p, δ₀, hT₀⟩ := isDerivedLimit_truncGETower_modules B S hS X hX E hqc
  obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor F RF α
    (truncGETower (Modules.{u, u} B S hS X hX) E) E p ⟨δ₀, hT₀⟩
  let := hp'
  have hlim : IsDerivedLimit
      (truncGETower (Modules.{u, u} B S hS X hX) E ⋙ RF) (RF.obj E) := ⟨_, δ, hδ⟩
  have hbound : ∀ n : ℕ, ((truncGETower (Modules.{u, u} B S hS X hX) E ⋙ RF).obj ⟨n⟩).IsLE
      (c + (N : ℤ) - 1) := by
    intro n
    have hGE := isGE_truncGETower_obj B S hS X hX E n
    have hLE' : ((truncGETower (Modules.{u, u} B S hS X hX) E).obj ⟨n⟩).IsLE c := by
      rw [truncGETower_obj]
      infer_instance
    exact isLE_rightDerived_obj_of_bounded B S hS X hX F RF α N hRF _
      (fun q ↦ prop_homologyFunctor_truncGE_obj (qcohU B S hS X hX) E hqc (-(n : ℤ)) q)
      (-(n : ℤ)) c hGE hLE'
  exact Stacks.DerivedLimit.isLE_of_isDerivedLimit_of_isMittagLeffler _ (RF.obj E) hlim
    (c + (N : ℤ) - 1) hbound
    (isMittagLeffler_homology_rightDerived_truncGETower B S hS X hX F RF α N hRF E hqc)

/-! ### Tag 08F7, assertions (2) and (3) with no boundedness hypothesis -/

include F α in
/-- **Stacks 08F7, assertion (3), the upper bound, for every `E` of `D_QCoh(𝒪_X)`.** Let `S` be a
scheme, let `X` be an algebraic space over `S`, let `F : Mod(𝒪_X) ⥤ Ab` be an additive functor
commuting with countable direct products and let `(RF, α)` be a right derived functor of `F` on
`D(𝒪_X)`.  Let `N ≥ 0` be an integer such that `R^pF(ℱ) = 0` for every quasi-coherent `ℱ` and
every `p ≥ N`, which is the source's hypothesis (3).  Let `E` be an object of `D_QCoh(𝒪_X)` with
`H ^ j (E) = 0` for `j > b`.  Then `H ^ i (RF E) = 0` for `i > b + N - 1`.

Nothing is assumed about the lower endpoint `a` of the source's range `-∞ ≤ a ≤ b ≤ ∞`, so this
is the case `a = -∞` as well; the vanishing for `i < a` when `a` is finite is the other half of
assertion (3) and is
`AlgebraicGeometry.Space.isZero_homology_rightDerived_of_isZero_lt`.  The source's hypothesis (2)
on `F` is the binder `[PreservesLimitsOfShape (Discrete ℕ) F]`; it is used, unlike in the bounded
statements, because the proof passes through the derived limit `E = R lim τ_{≥ -n} E`.

This is the sole registration of the upper bound of assertion (3); no form of that clause
assuming in addition that `E` is bounded below is stated in the library, the bounded case being
confined to the `private` ingredient
`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_bounded`. -/
@[stacks 08F7 "assertion (3), the upper bound b + N - 1, and the sole registration of that \
half: H^i(RF E) = 0 for i > b + N - 1 once H^j(E) = 0 for j > b, for every E of D_QCoh with no \
boundedness hypothesis, so for a = -infinity too.  Hypothesis (2) on F is the binder \
PreservesLimitsOfShape (Discrete N) F, hypothesis (3) is hRF, hypothesis (1) is unused"]
theorem isZero_homology_rightDerived_of_isZero_gt_unbounded (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (b : ℤ)
    (hEb : ∀ j : ℤ, b < j → IsZero ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) j).obj E))
    (i : ℤ) (hi : b + (N : ℤ) - 1 < i) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj (RF.obj E)) := by
  have hLE : E.IsLE b := (DerivedCategory.isLE_iff E b).2 hEb
  have := isLE_rightDerived_obj_of_isLE B S hS X hX F RF α N hRF E hqc b hLE
  exact (RF.obj E).isZero_of_isLE (b + (N : ℤ) - 1) i hi

include F α in
/-- **Stacks 08F7, assertion (2), for every `E` of `D_QCoh(𝒪_X)`.** Let `S` be a scheme, let `X`
be an algebraic space over `S`, let `F : Mod(𝒪_X) ⥤ Ab` be an additive functor commuting with
countable direct products and let `(RF, α)` be a right derived functor of `F` on `D(𝒪_X)`.  Let
`N ≥ 0` be an integer such that `R^pF(ℱ) = 0` for every quasi-coherent `ℱ` and every `p ≥ N`, the
source's hypothesis (3).  Then for every object `E` of `D_QCoh(𝒪_X)` and every `i ≥ b` the
canonical truncation map `E ⟶ τ_{≥ b - N + 1} E` induces an isomorphism
`H ^ i (RF E) ⟶ H ^ i (RF (τ_{≥ b - N + 1} E))`.

No boundedness hypothesis on `E` is made.  The canonical truncation triangle
`τ_{≤ b - N} E ⟶ E ⟶ τ_{≥ b - N + 1} E` is carried by `RF` to a distinguished triangle, `RF`
being triangulated; its first vertex lies in degrees `≤ b - 1` by
`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_isLE`, which needs no lower bound, so `H ^ i`
and `H ^ (i + 1)` vanish on it for `i ≥ b`, and the long exact homology sequence makes the second
map invertible on `H ^ i`.

This is the sole registration of assertion (2); no form of it assuming in addition that `E` is
bounded below is stated in the library, the bounded case being confined to the `private`
ingredient `AlgebraicGeometry.Space.isLE_rightDerived_obj_of_bounded`. -/
@[stacks 08F7 "assertion (2), and the sole registration of it: H^i(RF E) -> \
H^i(RF(tau_{>= b - N + 1} E)) is an isomorphism for i >= b, for every E of D_QCoh with no \
boundedness hypothesis.  Hypothesis (2) on F is the binder \
PreservesLimitsOfShape (Discrete N) F, hypothesis (3) is hRF, hypothesis (1) is unused"]
theorem isIso_homologyFunctor_map_rightDerived_truncGE_unbounded (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) q).obj E).IsQuasicoherentOnSite)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ (b - (N : ℤ) + 1)).app E))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF α
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE
    (b - (N : ℤ) + 1 - 1) (b - (N : ℤ) + 1) (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) :=
    RF.map_distinguished _ (DerivedCategory.TStructure.t.triangleLEGE_distinguished
      (b - (N : ℤ) + 1 - 1) (b - (N : ℤ) + 1) (by omega) E)
  have hl : T.obj₁.IsLE (b - (N : ℤ) + 1 - 1 + (N : ℤ) - 1) :=
    isLE_rightDerived_obj_of_isLE B S hS X hX F RF α N hRF
      ((DerivedCategory.TStructure.t.truncLE (b - (N : ℤ) + 1 - 1)).obj E)
      (fun q ↦ prop_homologyFunctor_truncLE_obj (qcohU B S hS X hX) E hqc
        (b - (N : ℤ) + 1 - 1) q)
      (b - (N : ℤ) + 1 - 1) inferInstance
  have hz := T.obj₁.isZero_of_isLE (b - (N : ℤ) + 1 - 1 + (N : ℤ) - 1) i (by omega)
  have hz' := T.obj₁.isZero_of_isLE (b - (N : ℤ) + 1 - 1 + (N : ℤ) - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u}
      0).homologySequence_mono_shift_map_mor₂_iff T hT i).2 (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u}
      0).homologySequence_epi_shift_map_mor₂_iff T hT i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂)

end AlgebraicGeometry.Space

end
