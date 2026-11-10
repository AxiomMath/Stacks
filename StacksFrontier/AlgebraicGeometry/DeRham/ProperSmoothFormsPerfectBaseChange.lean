module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import StacksCore.Tactic.StacksAttribute

/-!
# The relative differential forms of a smooth morphism

Let `f : X ⟶ S` be a smooth morphism of schemes. The sheaf `Ω^p_{X/S}` of relative differential
`p`-forms is the degree-`p` exterior power of `Ω_{X/S}`, which is finite locally free by
[Stacks, Tag 02G1]. This file proves that every exterior power of a finite locally free sheaf of
modules is again finite locally free, and reads off the properties of `Ω^p_{X/S}` that the
proofs of [Stacks, Tag 0FM0] use: finite local freeness, finite presentation, flatness over
`S`, perfectness of `Ω^p_{X/S}` placed in degree zero as an object of `D(𝒪_X)`, and the vanishing
of the forms of high degree over a quasi-compact open.

## Main results

* `AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower`: on any site, every
  exterior power of a finite locally free sheaf of modules is finite locally free. This is
  clause (6) of [Stacks, Tag 01CK] for the exterior power in the finite locally free case;
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower` is the version
  that tracks the rank and therefore needs the rank to be constant, which it need not be for an
  unranked finite locally free sheaf.
* `AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms`,
  `isFinitePresentation_relativeDifferentialForms`, `isFlatOver_relativeDifferentialForms` and
  `isPerfect_single_relativeDifferentialForms`: the four properties of `Ω^p_{X/S}` for a smooth
  `f` — finite local freeness, finite presentation, flatness over `S` (for which smoothness is
  used a second time, through `Smooth f → Flat f`) and perfectness in degree zero.
* `AlgebraicGeometry.ProperSmoothDeRham.exists_forall_subsingleton_relativeDifferentialForms`:
  over a quasi-compact open the forms of degree above some bound vanish.

The four assertions of [Stacks, Tag 0FM0] are
`AlgebraicGeometry.ProperSmoothDeRham.isPerfect_derivedPushforward_forms` and
`AlgebraicGeometry.ProperSmoothDeRham.isIso_derivedBaseChangeMap_forms` for `Rf_*Ω^p_{X/S}`,
and `AlgebraicGeometry.ProperSmoothDeRham.isPerfect_derivedPushforward_deRhamComplex` and
`AlgebraicGeometry.ProperSmoothDeRham.isIso_derivedBaseChangeMap_deRhamComplex` for
`Rf_*Ω^•_{X/S}`.

## Implementation notes

**The exterior power of a finite locally free sheaf.** The proof is the proof of
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower` with the rank bookkeeping
deleted. Finite local freeness of `F` gives local generators data `q` whose projections
`free (γ i) ⟶ F|_{X i}` are invertible with `γ i` finite; the composite of
`Stacks.SheafOfModules.exteriorPowerOverIso` — which passes from the exterior power computed on
the site to the one computed on the slice site over `X i` — with
`Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex` — which computes the exterior power of
a free sheaf on an arbitrary index type, well-ordered here to supply the linear order Mathlib's
exterior basis needs — trivialises `⋀ⁿ F` over `X i` on the `n`-element subsets of `γ i`, of
which there are finitely many. That trivialisation is turned back into generators by
`SheafOfModules.GeneratingSections.ofEpi` of the canonical basis of the free sheaf, exactly as
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff` does for a single open.

**The two copies of finite local freeness.** The statement is at
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, the class carrying [Stacks, Tag 01C6]
(2), which is the one [Stacks, Tag 02G1] concludes. The finite-presentation and perfectness
results consume the other copy, `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`; the two are
crossed by `Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree`.

**Flatness over the base.** `Ω^p_{X/S}` is finite locally free over `𝒪_X` and `𝒪_X` is flat
over `𝒪_S` because `f` is flat ([Stacks, Tag 02N3], and a smooth morphism is flat), so the
stalks of `Ω^p_{X/S}` are flat over the stalks of `𝒪_S`. That composition is
`AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

universe v u₁ u

namespace AlgebraicGeometry.ProperSmoothDeRham

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StrictlyPerfect.structureSheafOfRings
  StrictlyPerfect.structureModule

/-- The category of `𝒪_X`-modules at the spelling
`Stacks.DerivedTensor.RingedSite.Modules` the derived tensor product is written at is abelian:
it is `AlgebraicGeometry.Scheme.Modules` with the structure sheaf of rings spelled through
`CategoryTheory.Sheaf.toRingCat`, so this is the instance for the latter, restated. It is local
and is needed only because in the import closure of this file — which contains the sheaf-algebra
development that `Ω^p_{X/S}` is built from — instance search no longer crosses the two spellings
on its own. -/
local instance abelianDerivedTensorModules (X : Scheme.{u}) :
    Abelian (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
  inferInstanceAs (Abelian X.Modules)

/-! ### Exterior powers of a finite locally free sheaf of modules -/

section Site

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- **A trivialising covering of a finite locally free sheaf of modules trivialises its exterior
powers.** If `F` is finite locally free, there is a trivialising covering of `F` by objects
`X i` with finite index types `γ i` over which every exterior power `⋀ⁿ F` is free on the
`n`-element subsets of `γ i`.

The isomorphism is the composite of `Stacks.SheafOfModules.exteriorPowerOverIso` — which passes
from the exterior power computed on the site to the one computed on the slice site over `X i` —
with `Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex`, which computes the exterior power
of a free sheaf on an arbitrary index type, well-ordered here to supply the linear order
Mathlib's exterior basis needs. -/
@[sga "6 X 6.1" "special case"]
public theorem exists_exteriorPower_over_iso_free
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F)
    [hF : SheafOfModules.IsFiniteLocallyFree.{u, v, u₁} F] :
    ∃ q : F.LocalGeneratorsData.{u₁}, (∀ i, Finite (q.generators i).I) ∧
      ∀ (i : q.I) (n : ℕ), Nonempty ((A.exteriorPower n).over (q.X i) ≅
        _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over (q.X i))
          ↥(Set.powersetCard ((q.generators i).I) n)) := by
  classical
  obtain ⟨q, hfree, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  refine ⟨q, fun i => (hfin.isFiniteType i).finite, fun i n => ?_⟩
  let _ : LinearOrder ((q.generators i).I) := IsWellOrder.linearOrder WellOrderingRel
  have : IsIso (q.generators i).π := hfree.isIso i
  let B := _root_.SheafOfModules.algebras (Osharp := Osharp.over (q.X i)) (J.over (q.X i))
    (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over (q.X i)) (Osharp.over (q.X i)))
      from F.over (q.X i))
  exact ⟨(Stacks.SheafOfModules.exteriorPowerOverIso F (q.X i) n A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra B.exterior B.exteriorGenerator
      B.exterior_isExteriorAlgebra).trans
    (Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex (J.over (q.X i))
      ((q.generators i).I) n B (asIso (q.generators i).π).symm)⟩

/-- **Every exterior power of a finite locally free sheaf of modules is finite locally free.**
This is clause (6) of [Stacks, Tag 01CK] for the exterior power, in the case of a *finite*
locally free sheaf, and with no claim about ranks — which is what makes it applicable to a
sheaf whose local rank is not constant.

A trivialising covering for `F` with index types `γ i` is a trivialising covering for `⋀ⁿ F`
with index types the `n`-element subsets of `γ i`, which are finite in number because the `γ i`
are finite (`exists_exteriorPower_over_iso_free`). -/
@[ega "0 5.5.4" "partial", sga "6 X 6.1" "special case"]
public theorem isFiniteLocallyFree_exteriorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFree.{u, v, u₁} F] :
    SheafOfModules.IsFiniteLocallyFree.{u, v, u₁} (A.exteriorPower n) := by
  classical
  obtain ⟨q, hfin, hE⟩ := exists_exteriorPower_over_iso_free A
  have E : ∀ i : q.I, (A.exteriorPower n).over (q.X i) ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        ↥(Set.powersetCard ((q.generators i).I) n) := fun i => (hE i n).some
  have hfinite : ∀ i : q.I, Finite ↥(Set.powersetCard ((q.generators i).I) n) := fun i =>
    have : Finite ((q.generators i).I) := hfin i
    inferInstance
  refine ⟨⟨⟨q.I, q.X, q.coversTop, fun i =>
      (_root_.SheafOfModules.free.generatingSections
        ↥(Set.powersetCard ((q.generators i).I) n)).ofEpi (E i).inv⟩, ?_, ?_⟩⟩
  · constructor
    intro i
    change IsIso ((_root_.SheafOfModules.free.generatingSections
      ↥(Set.powersetCard ((q.generators i).I) n)).ofEpi (E i).inv).π
    have h0 : IsIso (_root_.SheafOfModules.free.generatingSections
        (R := (Sheaf.toRingCat J Osharp).over (q.X i))
        ↥(Set.powersetCard ((q.generators i).I) n)).π := by
      rw [_root_.SheafOfModules.free.generatingSections_π]
      exact IsIso.id _
    rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h0 inferInstance
  · constructor
    intro i
    exact ⟨hfinite i⟩

end Site

/-- **Every exterior power of a finite locally free sheaf of modules on a scheme is finite
locally free.** This is `AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower`
at the chosen exterior algebra `SheafOfModules.algebras`, the one
`AlgebraicGeometry.Scheme.Modules.exteriorPower` is defined from. The one `haveI` restates the
hypothesis at `CategoryTheory.Sheaf.toRingCat`, the spelling of the structure sheaf of rings
the site-level development uses; it is definitionally the same sheaf of rings as
`AlgebraicGeometry.Scheme.ringCatSheaf` but does not match it at reducible transparency. -/
@[sga "6 X 6.1" "special case"]
public theorem isFiniteLocallyFree_exteriorPower_scheme {X : Scheme.{u}} (F : X.Modules)
    [hF : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] (n : ℕ) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf) F := hF
  isFiniteLocallyFree_exteriorPower
    (J := _root_.Opens.grothendieckTopology X) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ F) n

/-! ### The relative differential forms of a smooth morphism -/

section Forms

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **For a smooth morphism of schemes the sheaf `Ω^p_{X/S}` of relative differential `p`-forms
is finite locally free.** The sheaf of relative differentials is finite locally free by
[Stacks, Tag 02G1] and `Ω^p_{X/S}` is its degree-`p` exterior power. -/
public theorem isFiniteLocallyFree_relativeDifferentialForms [Smooth f] (p : ℕ) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  isFiniteLocallyFree_exteriorPower_scheme (Scheme.Hom.relativeDifferentials f) p

/-- **For a smooth morphism of schemes the sheaf `Ω^p_{X/S}` is of finite presentation.** A
finite locally free sheaf of modules is of finite presentation, which is the
finite-presentation half of the implications (4) ⟹ (1) and (4) ⟹ (2) of
[Stacks, Tag 05P2]; that implication is carried for the second of the two copies of finite
local freeness, so it is reached through
`Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree`. -/
@[ega "IV 16.4.22" "special case"]
public theorem isFinitePresentation_relativeDifferentialForms [Smooth f] (p : ℕ) :
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).IsFinitePresentation :=
  have := isFiniteLocallyFree_relativeDifferentialForms f p
  have := Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ))
  Stacks.FiniteLocallyFree.isFinitePresentation.{u, u, u} _

/-- **For a smooth morphism of schemes the sheaf `Ω^p_{X/S}` is flat over `S`.** It is finite
locally free over `𝒪_X`, and `𝒪_X` is flat over `𝒪_S` because a smooth morphism is flat
([Stacks, Tag 02N3]); the composition of the two is
`AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree`. -/
public theorem isFlatOver_relativeDifferentialForms [Smooth f] (p : ℕ) :
    IsFlatOver f.toLRSHom.toShHom (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  have := isFiniteLocallyFree_relativeDifferentialForms f p
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p
  VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f _

/-- **For a smooth morphism of schemes the sheaf `Ω^p_{X/S}` placed in degree zero is a perfect
object of `D(𝒪_X)`.** It is finite locally free, and a finite locally free module in degree zero
is perfect by `AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`. -/
public theorem isPerfect_single_relativeDifferentialForms [Smooth f] (p : ℕ) :
    RingedSpace.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) :=
  have := isFiniteLocallyFree_relativeDifferentialForms f p
  isPerfect_singleFunctor_of_isFiniteLocallyFree X _
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))

/-- The sections over `W ⟶ U` of a sheaf of modules whose restriction over `U` is zero are
trivial. -/
public theorem subsingleton_val_obj_of_isZero_over {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (M : _root_.SheafOfModules.{u} R)
    {U W : C} (g : W ⟶ U) (h : IsZero (M.over U)) :
    Subsingleton (M.val.obj (Opposite.op W)) := by
  have h0 := h.eq_of_src (𝟙 (M.over U)) 0
  exact ⟨fun a b => congr(($h0).val.app (Opposite.op (Over.mk g)) a).trans
    congr(($h0).val.app (Opposite.op (Over.mk g)) b).symm⟩

/-- A sheaf of modules on a scheme whose sections are trivial over opens covering `W` has trivial
sections over `W`. -/
public theorem subsingleton_val_obj_of_locally {Y : Scheme.{u}} (M : Y.Modules) (W : Y.Opens)
    (h : ∀ y ∈ W, ∃ V : Y.Opens, V ≤ W ∧ y ∈ V ∧ Subsingleton (M.val.obj (Opposite.op V))) :
    Subsingleton (M.val.obj (Opposite.op W)) := by
  choose! V hle hy hV using h
  exact ⟨fun a b => TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf _ _)
    (fun y : {y : Y // y ∈ W} => V y.1) W (fun y => homOfLE (hle y.1 y.2))
    (fun y hy' => Opens.mem_iSup.2 ⟨⟨y, hy'⟩, hy y hy'⟩) a b fun y => (hV y.1 y.2).elim _ _⟩

/-- **The relative differential forms of a smooth morphism vanish in high degree over a
quasi-compact open.** For `f` smooth and `U ⊆ X` quasi-compact there is `N` such that the
sections of `Ω^p_{X/S}` over every open `W ⊆ U` are trivial for `p > N`: `U` is covered by
finitely many opens over which `Ω_{X/S}` is free of finite rank, and over such an open `Ω^p_{X/S}`
is free on the `p`-element subsets of a basis, of which there are none once `p` exceeds the
rank. -/
public theorem exists_forall_subsingleton_relativeDifferentialForms [Smooth f] (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ N : ℕ, ∀ p : ℕ, N < p → ∀ W : X.Opens, W ≤ U →
      Subsingleton ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj (Opposite.op W)) := by
  classical
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf)
      (Scheme.Hom.relativeDifferentials f) := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  obtain ⟨q, hfin, hE⟩ := exists_exteriorPower_over_iso_free
    (J := _root_.Opens.grothendieckTopology X) (Osharp := X.sheaf)
    (_root_.SheafOfModules.algebras _ (Scheme.Hom.relativeDifferentials f))
  -- over a member of the covering the forms of large degree vanish
  have hz : ∀ (i : q.I) (p : ℕ), Nat.card (q.generators i).I < p → ∀ W : X.Opens,
      W ≤ q.X i →
        Subsingleton ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj
          (Opposite.op W)) := by
    intro i p hp W hW
    have : Finite (q.generators i).I := hfin i
    have hempty : IsEmpty ↥(Set.powersetCard ((q.generators i).I) p) :=
      Set.isEmpty_coe_sort.mpr (Set.powersetCard.eq_empty_iff.mpr hp)
    have hZ : IsZero (((_root_.SheafOfModules.algebras _
        (Scheme.Hom.relativeDifferentials f)).exteriorPower p).over (q.X i)) :=
      IsZero.of_iso (Stacks.SheafOfModules.isZero_free_of_isEmpty
        (R := (Sheaf.toRingCat (_root_.Opens.grothendieckTopology X) X.sheaf).over (q.X i))
        ↥(Set.powersetCard ((q.generators i).I) p)) (hE i p).some
    exact subsingleton_val_obj_of_isZero_over _ (homOfLE hW) hZ
  -- a finite subcover of `U`
  have hcov : (U : Set X) ⊆ ⋃ i : q.I, (q.X i : Set X) := by
    rw [← Opens.coe_iSup, (Opens.coversTop_iff X q.X).1 q.coversTop]
    exact fun _ _ => trivial
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => (q.X i : Set X)) (fun i => (q.X i).isOpen)
    hcov
  refine ⟨t.sup fun i => Nat.card (q.generators i).I, fun p hp W hW => ?_⟩
  refine subsingleton_val_obj_of_locally _ W fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (hW hx))
  exact ⟨W ⊓ q.X i, inf_le_left, ⟨hx, hxi⟩,
    hz i p ((Finset.le_sup (f := fun i => Nat.card (q.generators i).I) hi).trans_lt hp)
      (W ⊓ q.X i) inf_le_right⟩

end Forms

end AlgebraicGeometry.ProperSmoothDeRham

end
