module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RegularDimensionTwo
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The determinant line bundle of a coherent module on an integral regular surface

Let `X` be an integral regular scheme of dimension at most two and `F` a coherent
`𝒪_X`-module which is finite locally free of rank `r` over some nonempty open `U` — its
*generic rank* is `r`.  Then the reflexive hull `(⋀^r F)^∨∨` of the top exterior power of `F`
is a line bundle.

The argument is the one of the source.  The hull is coherent and reflexive, so on a regular
scheme of dimension at most two it is finite locally free by Tag 0B3N; on an irreducible space
its fibre rank is therefore constant, and one point suffices to compute it.  Over `U` the
exterior power `⋀^r F` is finite locally free of rank `binom(r, r) = 1`, and taking the hull
does not change the fibre rank at a point where the stalk is free, because the double dual of
a finite free module over a local ring is that module.

Regularity and the bound on the dimension are both essential and both enter only through
Tag 0B3N: `StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneNotInvertible.lean`
exhibits a rank-one coherent reflexive module which is not invertible, on the spectrum of the
nonnormal two-dimensional domain `k[y, x², xy, x³]`.

## Main results

* `AlgebraicGeometry.isInvertible_reflexiveHull_exteriorPower_of_genericRank`: **the reflexive
  hull of the top exterior power of a coherent module of generic rank `r` on an integral
  regular scheme of dimension at most two is invertible.**
* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank_over`,
  `nonempty_stalkLinearEquiv_fin_of_isFiniteLocallyFreeOfRank_over` and
  `free_stalk_of_isFiniteLocallyFreeOfRank_over`: a module which is finite locally free of
  rank `s` on the slice site over an open `U` has fibre rank `s`, and a stalk free on `s`
  generators, at every point of `U`.
* `AlgebraicGeometry.Scheme.Modules.fiberRank_reflexiveHull_eq_of_free_stalk`: the reflexive
  hull has the same fibre rank as the module itself at a point where the stalk of the module
  is free.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_over`: on the
  slice site over an open, the degree-`n` exterior power of a module which is finite locally
  free of rank `r` there is finite locally free of rank `binom(r, n)`.
* `AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft`: a trivialization of a module on an
  iterated slice site `(Opens X / U) / W` is a trivialization on the slice site over `W.left`.

## Implementation notes

**From the slice site to a point.**  Finite local freeness of rank `s` of `M.over U` is a
statement on the slice site `Opens X / U`: it provides a covering family `q.X : q.I → Over U`
of the terminal object together with isomorphisms `free I ≅ (M.over U).over (q.X i)` on the
*iterated* slice sites.  Neither a stalk nor a fibre rank of `M.over U` exists, so the route
to a point of `U` is to descend each such isomorphism to the slice site over the open
`(q.X i).left` of `X`, where `Stacks.StalkFreeBridge.trivializationOfGeneratingSections`
produces a trivialization of `M` in the sense of Tag 01C9.  The descent is
`freeIsoOverLeft`: by `Stacks.SheafOfModules.overFunctor_comp_sliceBackward` restricting to
the iterated slice and then transporting along `CategoryTheory.Over.iteratedSliceBackward` is
restriction along `W.hom`, so `SheafOfModules.overFunctorMap` identifies the image of
`(M.over U).over W` with `M.over W.left`; a free module is carried along because
`Stacks.SheafOfModules.sliceBackward` is additive and the index type is finite, which gives
the coproduct preservation that `SheafOfModules.mapFreeIso` consumes.  That a point of `U`
lies in some `(q.X i).left` is read off the covering condition at the terminal object
`Over.mk (𝟙 U)` through `CategoryTheory.GrothendieckTopology.mem_over_iff`.

**The hull on stalks.**  The stalk of the dual of a module of finite presentation is the dual
of the stalk (`Stacks.AlgebraicGeometry.ReflexiveModules.dualStalkEquiv`), so two
applications identify the stalk of `F^∨∨` with the double dual of the stalk of `F`, and
`Module.evalEquiv` closes the comparison when that stalk is finite free.  The finite
presentation hypotheses are available for an exterior power of a coherent module because
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_exteriorPower` makes it an instance.
The alternative route, restricting the dual to an open, is unavailable: only the slice form
`dualSheafOverIso` of that comparison exists.

**Only the first assertion of the tag.**  Tag 0B3T also asserts that in a right-exact
sequence whose quotient is supported on an integral effective Cartier divisor `D` the two
determinant line bundles differ by at most `min s r` copies of `D`.  That assertion is not
proved here.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B3N](https://stacks.math.columbia.edu/tag/0B3N)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### From the slice site over an open to a point of that open -/

/-- A family of objects of `Opens X / U` which covers the terminal object of the slice site has
a member whose underlying open contains a given point of `U`.

The covering condition is evaluated at the terminal object `Over.mk (𝟙 U)`, whose underlying
open is `U`; the resulting sieve on `U` is covering for the topology of open subsets, which is
membership of the point in the source of one of its arrows. -/
theorem exists_mem_left_of_coversTop (U : X.Opens) {ι : Type*} (Y : ι → Over U)
    (hY : ((Opens.grothendieckTopology X).over U).CoversTop Y) {x : X} (hx : x ∈ U) :
    ∃ i, x ∈ (Y i).left := by
  have h := hY (Over.mk (𝟙 U))
  rw [GrothendieckTopology.mem_over_iff] at h
  obtain ⟨V, f, hf, hxV⟩ := h x hx
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff _ _).mp hf
  exact ⟨i, leOfHom g.left hxV⟩

/-- The generating sections of a sheaf of modules attached to an isomorphism with a free sheaf
of modules: the images of the standard basis. -/
private def generatingSectionsOfFreeIso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (N : _root_.SheafOfModules.{u} R) (I : Type u)
    (e : _root_.SheafOfModules.free.{u} (R := R) I ≅ N) : N.GeneratingSections where
  I := I
  s := N.freeHomEquiv e.hom
  epi := by rw [Equiv.symm_apply_apply]; infer_instance

/-- The structure map of the generating sections attached to an isomorphism with a free sheaf
of modules is that isomorphism, hence invertible. -/
private theorem isIso_generatingSectionsOfFreeIso_π {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (N : _root_.SheafOfModules.{u} R) (I : Type u)
    (e : _root_.SheafOfModules.free.{u} (R := R) I ≅ N) :
    IsIso (generatingSectionsOfFreeIso N I e).π := by
  dsimp only [_root_.SheafOfModules.GeneratingSections.π, generatingSectionsOfFreeIso]
  rw [Equiv.symm_apply_apply]
  infer_instance

/-- **A trivialization on an iterated slice site descends to the slice site below it.**  An
isomorphism of `(M.over U).over W` with the free module on a finite index type `I`, on the
iterated slice site `(Opens X / U) / W`, gives an isomorphism of `M.over W.left` with the free
module on `I` on the slice site over `W.left`.

Restriction to the iterated slice followed by transport along
`CategoryTheory.Over.iteratedSliceBackward` is restriction along `W.hom`
(`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`), which
`SheafOfModules.overFunctorMap` compares with restriction to the slice over `W.left`; the free
module is carried along by `SheafOfModules.mapFreeIso`, whose preservation hypothesis holds
because the transport is additive and `I` is finite. -/
def freeIsoOverLeft (M : X.Modules) (U : X.Opens) (W : Over U) (I : Type u) [Finite I]
    (e : _root_.SheafOfModules.free.{u} I ≅ (M.over U).over W) :
    _root_.SheafOfModules.free.{u} I ≅ M.over W.left :=
  letI Φ := Stacks.SheafOfModules.sliceBackward X.ringCatSheaf W.hom
  letI : PreservesColimitsOfShape (Discrete I) Φ := preservesColimitsOfShape_of_discrete _
  _root_.SheafOfModules.mapFreeIso Φ I (Iso.refl _) ≪≫ Φ.mapIso e ≪≫
    (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf W.hom).app M

/-- A module which is finite locally free of rank `s` on the slice site over `U` has, over a
member of its trivializing covering family whose underlying open contains a given point of
`U`, an isomorphism with the free module on an index type equivalent to `Fin s`. -/
private theorem exists_freeIso_over_of_isFiniteLocallyFreeOfRank_over (M : X.Modules)
    (U : X.Opens) (s : ℕ)
    [h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) s]
    {x : X} (hx : x ∈ U) :
    ∃ (W : Over U) (_ : x ∈ W.left) (I : Type u) (_ : Nonempty (I ≃ Fin s)),
      Nonempty (_root_.SheafOfModules.free.{u} I ≅ (M.over U).over W) := by
  obtain ⟨q, hq, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hxi⟩ := exists_mem_left_of_coversTop U q.X q.coversTop hx
  have hiso : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, hxi, (q.generators i).I, hrank i, ⟨asIso (q.generators i).π⟩⟩

/-- A module which is finite locally free of rank `s` on the slice site over `U` has, near every
point of `U`, a trivialization in the sense of Tag 01C9 by a finite index type equivalent to
`Fin s`. -/
private theorem exists_trivialization_of_isFiniteLocallyFreeOfRank_over (M : X.Modules)
    (U : X.Opens) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) s]
    {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (_ : x ∈ V)
      (t : LocallyFreeRank.Trivialization X.toTopCat X.ringCatSheaf M V),
      Finite t.ι ∧ Nonempty (t.ι ≃ Fin s) := by
  obtain ⟨W, hxW, I, ⟨eI⟩, ⟨e⟩⟩ :=
    exists_freeIso_over_of_isFiniteLocallyFreeOfRank_over M U s hx
  have hfin : Finite I := Finite.of_equiv _ eI.symm
  let σ := generatingSectionsOfFreeIso (M.over W.left) I (freeIsoOverLeft M U W I e)
  have : IsIso σ.π := isIso_generatingSectionsOfFreeIso_π _ _ _
  exact ⟨W.left, hxW, Stacks.StalkFreeBridge.trivializationOfGeneratingSections W.left M σ,
    hfin, ⟨eI⟩⟩

/-- **A module which is finite locally free of rank `s` on the slice site over an open `U` has
fibre rank `s` at every point of `U`.**  On a trivializing open the fibre rank is the
cardinality of the trivializing index type, which is `s`. -/
theorem fiberRank_eq_of_isFiniteLocallyFreeOfRank_over (M : X.Modules) (U : X.Opens) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) s] {x : X} (hx : x ∈ U) :
    fiberRank M x = s := by
  obtain ⟨V, hxV, t, _, ⟨eI⟩⟩ :=
    exists_trivialization_of_isFiniteLocallyFreeOfRank_over M U s hx
  exact (fiberRank_eq_card_of_trivialization M x hxV t).trans (Nat.card_eq_of_equiv_fin eI)

/-- **The stalk of a module which is finite locally free of rank `s` on the slice site over an
open `U` is free on `s` generators at every point of `U`.**  The trivialization near the point
identifies the stalk with the finitely supported functions on the trivializing index type,
which is equivalent to `Fin s`. -/
theorem nonempty_stalkLinearEquiv_fin_of_isFiniteLocallyFreeOfRank_over (M : X.Modules)
    (U : X.Opens) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) s] {x : X} (hx : x ∈ U) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
    Nonempty (M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (Fin s →₀ X.presheaf.stalk x)) := by
  classical
  obtain ⟨V, hxV, t, _, ⟨eI⟩⟩ :=
    exists_trivialization_of_isFiniteLocallyFreeOfRank_over M U s hx
  obtain ⟨ε⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf M x hxV t
  let : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val x
  let eF : (t.ι →₀ (X.presheaf.stalk x : Type u)) ≃ₗ[(X.presheaf.stalk x : Type u)]
      (Fin s →₀ (X.presheaf.stalk x : Type u)) := Finsupp.domLCongr eI
  exact ⟨ε ≪≫ₗ eF⟩

/-- **The stalk of a module which is finite locally free of rank `s` on the slice site over an
open `U` is free at every point of `U`.** -/
theorem free_stalk_of_isFiniteLocallyFreeOfRank_over (M : X.Modules) (U : X.Opens) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.over U) s] {x : X} (hx : x ∈ U) :
    letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
    Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  letI : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val x
  Module.Free.of_equiv
    (nonempty_stalkLinearEquiv_fin_of_isFiniteLocallyFreeOfRank_over M U s hx).some.symm

/-! ### The exterior power on the slice site over an open -/

/-- **On the slice site over an open `U`, the degree-`n` exterior power of a module which is
finite locally free of rank `r` there is finite locally free of rank `binom(r, n)`.**

The exterior power computed on `X` and restricted to `U` is the exterior power computed on the
slice site, by `Stacks.SheafOfModules.exteriorPowerOverIso`, and the rank of the latter is
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower` applied on that site. -/
@[ega "0 5.5.4" "special case", sga "6 X 6.1" "special case"]
theorem isFiniteLocallyFreeOfRank_exteriorPower_over (F : X.Modules) (U : X.Opens) (r n : ℕ)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.exteriorPower F n).over U) (r.choose n) := by
  let J := Opens.grothendieckTopology (X : TopCat.{u})
  let A := _root_.SheafOfModules.algebras J
    (show _root_.SheafOfModules.{u} (Sheaf.toRingCat J X.sheaf) from F)
  let B := _root_.SheafOfModules.algebras (Osharp := X.sheaf.over U) (J.over U)
    (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (X.sheaf.over U)) from F.over U)
  have hF' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (J.over U) (X.sheaf.over U))
      (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (X.sheaf.over U)) from
        F.over U) r := hF
  have hpow : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (B.exteriorPower n) (r.choose n) :=
    Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower B r n
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.SheafOfModules.exteriorPowerOverIso
      (show _root_.SheafOfModules.{u} (Sheaf.toRingCat J X.sheaf) from F) U n
      A.exterior A.exteriorGenerator A.exterior_isExteriorAlgebra
      B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra).symm hpow

/-! ### The fibre rank of a reflexive hull -/

/-- **The reflexive hull of a module of finite presentation has the same fibre rank as the
module at a point where the stalk of the module is free.**

The stalk of a dual is the dual of the stalk
(`Stacks.AlgebraicGeometry.ReflexiveModules.dualStalkEquiv`), so the stalk of `F^∨∨` at the
point is the double dual of the stalk of `F`; a finite free module over the local ring is
reflexive, so `Module.evalEquiv` identifies the two, and the fibre rank of a module of finite
type with free stalk is the rank of that stalk. -/
theorem fiberRank_reflexiveHull_eq_of_free_stalk (E : X.Modules) [E.IsFiniteType]
    [E.IsFinitePresentation] [(dualSheaf E).IsFinitePresentation]
    [(reflexiveHull E).IsFiniteType] (x : X)
    (hfree :
      letI : Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) E.val x
      Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x)) :
    fiberRank (reflexiveHull E) x = fiberRank E x := by
  let A := ToType (X.presheaf.stalk x)
  let Ex := ToType (E.presheaf.stalk x)
  let : Module A Ex :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) E.val x
  let : Module.Free A Ex := hfree
  let : Module.Finite A Ex := _root_.SheafOfModules.finite_stalk X.sheaf E x
  let d₁ := dualStalkEquiv E x
  let d₂ := dualStalkEquiv (dualSheaf E) x
  let eqv : Ex ≃ₗ[A] ToType ((reflexiveHull E).presheaf.stalk x) :=
    ((Module.evalEquiv A Ex).trans d₁.dualMap).trans d₂.symm
  have hfreeH : Module.Free A (ToType ((reflexiveHull E).presheaf.stalk x)) :=
    Module.Free.of_equiv eqv
  rw [fiberRank_eq_finrank_stalk (reflexiveHull E) x hfreeH,
    fiberRank_eq_finrank_stalk E x hfree]
  exact eqv.finrank_eq.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B3T.**  The reflexive hull `(⋀^r F)^∨∨` of the top exterior power
of a coherent module of generic rank `r` on an integral regular scheme of dimension at most
two is a line bundle.

Generic rank `r` is finite local freeness of rank `r` of `F` on the slice site over a nonempty
open `U`.  The hull is coherent and reflexive, hence finite locally free by Tag 0B3N, and on
the irreducible space of an integral scheme its fibre rank is constant; over `U` the exterior
power `⋀^r F` is finite locally free of rank `binom(r, r) = 1` with free stalks, and the hull
preserves the fibre rank there, so that constant is one. -/
@[stacks 0B3T "invertibility of the determinant line bundles"]
theorem isInvertible_reflexiveHull_exteriorPower_of_genericRank
    (X : Scheme.{u}) [IsIntegral X] (hX : AlgebraicGeometry.IsRegular X)
    (hXdim : topologicalKrullDim X ≤ 2)
    (F : X.Modules) [F.IsCoherent] (r : ℕ) (U : X.Opens) (hU : ∃ x : X, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      (Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveHull
        (Scheme.Modules.exteriorPower F r)) := by
  obtain ⟨x, hx⟩ := hU
  have hnoeth : IsLocallyNoetherian X := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).1
  have hErank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.exteriorPower F r).over U) 1 := by
    simpa only [Nat.choose_self] using
      Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_over F U r r
  have hEcoh : _root_.SheafOfModules.IsCoherent (Scheme.Modules.exteriorPower F r) :=
    inferInstance
  have hEft : (Scheme.Modules.exteriorPower F r).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have hEfp : (Scheme.Modules.exteriorPower F r).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have hDcoh : _root_.SheafOfModules.IsCoherent (dualSheaf (Scheme.Modules.exteriorPower F r)) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf _
  have hDfp : (dualSheaf (Scheme.Modules.exteriorPower F r)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have hHcoh : _root_.SheafOfModules.IsCoherent
      (reflexiveHull (Scheme.Modules.exteriorPower F r)) :=
    Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_dualSheaf _
  have hHft : (reflexiveHull (Scheme.Modules.exteriorPower F r)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType
  have hHflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (reflexiveHull (Scheme.Modules.exteriorPower F r)) :=
    (isReflexive_iff_isFiniteLocallyFree_of_isRegular_of_dim_le_two X hX hXdim _).mp
      (isReflexive_reflexiveHull X _)
  have hfr : Scheme.Modules.fiberRank (reflexiveHull (Scheme.Modules.exteriorPower F r)) x = 1 :=
    (Scheme.Modules.fiberRank_reflexiveHull_eq_of_free_stalk
        (Scheme.Modules.exteriorPower F r) x
        (Scheme.Modules.free_stalk_of_isFiniteLocallyFreeOfRank_over _ U 1 hx)).trans
      (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank_over _ U 1 hx)
  exact Scheme.Modules.isInvertible_of_fiberRank_eq_one _ x hfr

end AlgebraicGeometry

end
