module

public import StacksFrontier.Algebra.Homology.SingleTopCohomologyComparison
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDualCoefficientComplex
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulHomologyProZeroScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology sheaves of the tower of the Koszul formula are pro-zero away from degree zero

`KoszulDualCoefficientComplex.lean` identifies the tower of the Koszul formula of
[Stacks, Tag 0A0E] at a sheaf of modules `ℱ` with the `r`-fold shift of the **dual** Koszul tower
with coefficients, `AlgebraicGeometry.RingedSite.koszulDualSystemOn`. That tower is an inverse
system of the very complexes `koszulPowerComplexOn X f ℱ n`, and its transition from level `n+1`
to level `n` multiplies the factor indexed by `T` by `∏_{i ∉ T} f_i`.

This file records that those transitions are exactly the downward Koszul transitions
`AlgebraicGeometry.RingedSite.koszulPowerComplexOnDown` of `KoszulHomologyProZero.lean` — at a
single step by `koszulDualComplexOnMap_eq`, and along an arbitrary `n ≤ m` by
`koszulDualSystemOn_map_down` — and therefore that the pro-vanishing proved in
`KoszulHomologyProZeroScheme.lean` is a statement about 0A0E's own tower.

## The indexing, and the shift

`koszulPowerComplexOn X f ℱ n` is concentrated in the degrees `0, …, r`, with top cohomology
sheaf `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`. The identification of
`AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso` carries a shift by `r`:
`ℱ ⊗^𝐋_𝒪 (K^n)^∨ ≅ Q((koszulPowerComplexOn X f ℱ n)⟦r⟧)`, whose cohomology sheaves therefore sit
in the degrees `-r, …, 0`, the degree `i` of the shift being the degree `i + r` of the Koszul
complex. So the pro-vanishing below the top degree proved here — degrees `p < r` of the Koszul
complex — is the pro-vanishing of `H^i` for `i < 0` of 0A0E's tower, with `H^0` the quotient. The
statements below are in the unshifted indexing, `p < r`, which is the one the Koszul complex
itself carries.

## Main results

* `AlgebraicGeometry.RingedSite.koszulDualComplexOnMap_eq` — the one-step transition of the dual
  Koszul tower is the downward Koszul transition.
* `AlgebraicGeometry.RingedSite.koszulDualSystemOn_map_down` — the same along an arbitrary
  `n ≤ m`, so that the dual Koszul tower is the inverse system of the downward transitions.
* `Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent` — **the
  cohomology sheaves of the tower of [Stacks, Tag 0A0E] are pro-zero away from the degree
  carrying the quotient**, for a coherent module on a quasi-compact locally Noetherian scheme.
  This is the hypothesis `hH` of [Stacks, Tag 0G3D] in the degrees other than the top one.
* `AlgebraicGeometry.RingedSite.koszulTopSingleSystem` and
  `AlgebraicGeometry.RingedSite.koszulToTopSingle` — **the target tower of [Stacks, Tag 0G3D]
  and the comparison into it**: the tower of top cohomology sheaves, each placed in degree `r`,
  and the morphism of towers into it. The tower is a composite of functors, so its transitions
  are the maps induced on cohomology by the downward Koszul transitions; the comparison is
  `HomologicalComplex.toSingleTopCohomology` levelwise, natural by
  `HomologicalComplex.toSingleTopCohomology_naturality`.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_koszulToTopSingle` — the comparison is an
  isomorphism on cohomology in the top degree at every level, so 0G3D's hypothesis there holds
  with no refinement of the index. At level `n` the target is `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` by
  `AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AlternatingCech

universe u

namespace AlgebraicGeometry.RingedSite

section Bridge

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The one-step transition of the dual Koszul tower is the downward Koszul transition.** At
the factor indexed by `S` both are multiplication by `∏_{i ∉ S} f_i`. -/
theorem koszulDualComplexOnMap_eq (m : ℕ) :
    koszulDualComplexOnMap X f ℱ m = koszulPowerComplexOnDown X f ℱ (Nat.le_succ m) := by
  refine congrArg AlternatingCech.map (NatTrans.ext (funext fun S => ?_))
  show koszulScalarOn X f (fun i => if i ∈ Sᶜ then 1 else 0) ℱ =
    koszulScalarOn X f (downExp (m + 1) m S) ℱ
  exact koszulScalarOn_congr X f (fun i => by simp [downExp, Finset.mem_compl]) ℱ

/-- The transition of the dual Koszul tower along `n ≤ n + k`. -/
theorem koszulDualSystemOn_map_add (n k : ℕ) :
    (koszulDualSystemOn X f ℱ).map (homOfLE (Nat.le_add_right n k)).op =
      koszulPowerComplexOnDown X f ℱ (Nat.le_add_right n k) := by
  induction k with
  | zero =>
      rw [show (homOfLE (Nat.le_add_right n 0)).op =
        (𝟙 (op (n + 0)) : op (n + 0) ⟶ op n) from rfl, CategoryTheory.Functor.map_id]
      exact (koszulPowerComplexOnDown_self X f ℱ n).symm
  | succ j ih =>
      rw [show (homOfLE (Nat.le_add_right n (j + 1))).op =
          (homOfLE (Nat.le_add_right (n + j) 1)).op ≫
            (homOfLE (Nat.le_add_right n j)).op from rfl,
        CategoryTheory.Functor.map_comp, koszulDualSystemOn_map_succ,
        koszulDualComplexOnMap_eq, ih]
      exact koszulPowerComplexOnDown_comp X f ℱ _ _

/-- **The dual Koszul tower is the inverse system of the downward Koszul transitions.** -/
theorem koszulDualSystemOn_map_down {m n : ℕ} (hnm : n ≤ m) :
    (koszulDualSystemOn X f ℱ).map (homOfLE hnm).op =
      koszulPowerComplexOnDown X f ℱ hnm := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact koszulDualSystemOn_map_add X f ℱ n k

end Bridge

/-! ## The tower of top cohomology sheaves, and the comparison into it -/

section TopSingle

open scoped IsMulCommutative

attribute [local instance]
  hasFiniteBiproducts_sheafOfModules

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The terms of the Koszul complex with coefficients above the top degree are zero: there is no
subset of `Fin r` of cardinality larger than `r`, so the indexing product is empty. -/
theorem isZero_X_koszulPowerComplexOn_gt (n : ℕ) {p : ℤ} (hp : (r : ℤ) < p) :
    IsZero ((koszulPowerComplexOn X f ℱ n).X p) := by
  rw [IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun S => (AlternatingCech.isEmpty_idx_of_lt (r := r) hp).elim S

/-- The degree above the top degree is the successor, in the cochain shape. -/
theorem next_top_eq : (ComplexShape.up ℤ).next (r : ℤ) = (r : ℤ) + 1 :=
  ComplexShape.next_eq' _ (show (r : ℤ) + 1 = (r : ℤ) + 1 from rfl)

/-- The differential out of the top degree vanishes. -/
theorem koszulPowerComplexOn_d_at_top_eq_zero (n : ℕ) :
    (koszulPowerComplexOn X f ℱ n).d (r : ℤ) ((r : ℤ) + 1) = 0 :=
  (isZero_X_koszulPowerComplexOn_gt X f ℱ n (by omega)).eq_of_tgt _ _

/-- **The tower of the top cohomology sheaves of the dual Koszul tower**, each placed in degree
`r`. Its transitions are the maps induced on cohomology by the downward Koszul transitions, so
no construction is needed: it is a composite of functors. At level `n` the object is
`ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ` in degree `r`, by
`AlgebraicGeometry.RingedSite.homologyIsoCokernelKoszulGeneratorsMap`. -/
def koszulTopSingleSystem :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  koszulDualSystemOn X f ℱ ⋙ HomologicalComplex.homologyFunctor _ _ (r : ℤ) ⋙
    HomologicalComplex.single _ _ (r : ℤ)

/-- The transition of `koszulTopSingleSystem` from level `m + 1` to level `m` is the map induced
on cohomology in degree `r` by `koszulDualComplexOnMap`, placed in degree `r`. -/
theorem koszulTopSingleSystem_map_succ (m : ℕ) :
    (koszulTopSingleSystem X f ℱ).map (homOfLE (Nat.le_add_right m 1)).op =
      (HomologicalComplex.single _ _ (r : ℤ)).map
        (HomologicalComplex.homologyMap (koszulDualComplexOnMap X f ℱ m) (r : ℤ)) := by
  show (HomologicalComplex.single _ _ (r : ℤ)).map
      (HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f ℱ).map (homOfLE (Nat.le_add_right m 1)).op) (r : ℤ)) = _
  rw [koszulDualSystemOn_map_succ]
  rfl

/-- **The comparison of the dual Koszul tower with the tower of its top cohomology sheaves**, as
a morphism of towers. Its naturality is
`HomologicalComplex.toSingleTopCohomology_naturality`, which holds for an arbitrary map of
complexes; no computation of the downward transition at the top degree is needed. -/
def koszulToTopSingle : koszulDualSystemOn X f ℱ ⟶ koszulTopSingleSystem X f ℱ :=
  NatTrans.ofOpSequence
    (fun m => HomologicalComplex.toSingleTopCohomology (koszulPowerComplexOn X f ℱ m)
      (next_top_eq (r := r)) (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ m))
    (fun m => by
      rw [koszulDualSystemOn_map_succ, koszulTopSingleSystem_map_succ]
      exact HomologicalComplex.toSingleTopCohomology_naturality
        (koszulDualComplexOnMap X f ℱ m) (next_top_eq (r := r))
        (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ (m + 1))
        (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ m))

/-- At level `m`, `koszulToTopSingle` is the comparison
`HomologicalComplex.toSingleTopCohomology` of the Koszul complex with its top cohomology. -/
theorem koszulToTopSingle_app (m : ℕ) :
    (koszulToTopSingle X f ℱ).app (op m) =
      HomologicalComplex.toSingleTopCohomology (koszulPowerComplexOn X f ℱ m)
        (next_top_eq (r := r)) (koszulPowerComplexOn_d_at_top_eq_zero X f ℱ m) :=
  rfl

/-- **The comparison is an isomorphism on cohomology in the top degree**, at every level. This is
the hypothesis of [Stacks, Tag 0G3D] at that degree, and it needs no refinement of the index. -/
theorem isIso_homologyMap_koszulToTopSingle (m : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((koszulToTopSingle X f ℱ).app (op m)) (r : ℤ)) := by
  rw [koszulToTopSingle_app]
  exact HomologicalComplex.isIso_homologyMap_toSingleTopCohomology _ _ _

end TopSingle

end AlgebraicGeometry.RingedSite

namespace Stacks.KoszulProZero

open _root_.AlgebraicGeometry

section Model

open scoped IsMulCommutative

open Stacks.KoszulCoefficientProIso (rTensorFunctor)


variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The cohomology sheaves of the tower of the Koszul formula of [Stacks, Tag 0A0E] are
pro-zero away from the degree carrying the quotient, on a ringed site with a flat Noetherian
model uniform over a basis.**

This is `Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero` read on
0A0E's own tower: the transitions of `AlgebraicGeometry.RingedSite.koszulDualSystemOn` *are* the
downward Koszul transitions, by
`AlgebraicGeometry.RingedSite.koszulDualSystemOn_map_down`. The hypothesis `hmodel` is a
Noetherian ring `A`, elements `a_1, …, a_r ∈ A` and a finite `A`-module `M` such that every
object of the site is covered by objects `V` over which `𝒪(V)` is an `A`-algebra carrying
`a_i` to `f_i|_V` and `ℱ(V)` is the base change of `M` along a flat `A`-module; the Artin–Rees
level is computed once over the model and inherited by every member of the covering family.

`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent` is the same
conclusion for a coherent module on a quasi-compact locally Noetherian **scheme**, where the
model exists only on each member of a finite affine cover and the levels are maximised over it;
that is the single place quasi-compactness enters the chain of
`Completion/KoszulAdicCompletionLimit.lean`. The statement here carries no compactness and lives
on an arbitrary ringed site, so it applies to the slice over an affine open, where one model —
the ring of functions on that open and the module of sections of `ℱ` over it — serves the whole
basis of basic opens.

The degrees `p < r` are those of the Koszul complex itself, which is concentrated in
`0, …, r`; in the shifted indexing of [Stacks, Tags 0A0E and 0A0K] they are the degrees
`p - r < 0`, the degree `0` carrying the quotient `ℱ/(f_1^{n+1}, …, f_r^{n+1})ℱ`. -/
@[sga "2 II Lemma11" "special case"]
theorem exists_koszulDualSystemOn_homologyMap_eq_zero_of_model
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Fin r → A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hmodel : ∀ U : X.Cᵒᵖ, ∃ P : Presieve U.unop, Sieve.generate P ∈ X.J U.unop ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U.unop), P g →
        ∃ (ρ : A →+* (X.O.obj.obj (op V))) (S : ModuleCat.{u} A),
          (∀ i, ρ (a i) = RingedSite.globalSectionVal (f i) (op V)) ∧ Module.Flat A S ∧
            Nonempty ((modelSectionsFunctor X (op V) ρ).obj ℱ ≅ (rTensorFunctor S).obj M))
    (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      ((RingedSite.koszulDualSystemOn X f ℱ).map (homOfLE hnm).op) p = 0 := by
  obtain ⟨m, hnm, hzero⟩ :=
    exists_koszulPowerComplexOnDown_homologyMap_eq_zero X f ℱ A a M hmodel n p hp
  exact ⟨m, hnm, by rwa [RingedSite.koszulDualSystemOn_map_down]⟩

end Model

section Coherent

variable (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y] {r : ℕ}
  (f : Fin r → Presheaf.globalSections
    ((_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf).O.obj ⋙ forget CommRingCat.{u}))
  (ℱ : Y.Modules) [ℱ.IsCoherent]

/-- **The cohomology sheaves of the tower of the Koszul formula of [Stacks, Tag 0A0E] are
pro-zero away from the degree carrying the quotient**, for a coherent module on a quasi-compact
locally Noetherian scheme.

The tower is `AlgebraicGeometry.RingedSite.koszulDualSystemOn`, which
`AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso` identifies with
`n ↦ ℱ ⊗^𝐋_𝒪 (K^n)^∨` up to the shift by `r`; its transitions are the downward Koszul
transitions by `AlgebraicGeometry.RingedSite.koszulDualSystemOn_map_down`. The degrees `p < r`
here are the degrees `p - r < 0` of the shifted tower.

Quasi-compactness is used only to take the maximum of the finitely many Artin–Rees levels
contributed by the members of a finite affine cover; see
`Stacks.KoszulProZero.exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent`. -/
@[sga "2 II Lemma11" "partial"]
theorem exists_koszulDualSystemOn_homologyMap_eq_zero_of_coherent (n : ℕ) (p : ℤ) (hp : p < r) :
    ∃ (m : ℕ) (hnm : n ≤ m), HomologicalComplex.homologyMap
      ((_root_.AlgebraicGeometry.RingedSite.koszulDualSystemOn
        (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf) f ℱ).map
          (homOfLE hnm).op) p = 0 := by
  obtain ⟨m, hnm, hzero⟩ :=
    exists_koszulPowerComplexOnDown_homologyMap_eq_zero_of_coherent Y f ℱ n p hp
  exact ⟨m, hnm, by
    rwa [_root_.AlgebraicGeometry.RingedSite.koszulDualSystemOn_map_down
      (_root_.Stacks.SheafOfModules.opensRingedSite Y.sheaf) f ℱ hnm]⟩

end Coherent

end Stacks.KoszulProZero

end
