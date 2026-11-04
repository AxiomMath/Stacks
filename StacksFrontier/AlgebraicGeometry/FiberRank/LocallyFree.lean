module

public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local freeness from a locally constant fibre rank

A module of finite type on a scheme whose stalks are all free and whose fibre rank is locally
constant is finite locally free. Together with the implications proved in
`StacksFrontier.AlgebraicGeometry.FiberRank.Basic` this completes the five-way equivalence of
Stacks Tag 05P2.

The argument is local and does not pass through affine charts. Near a point `x` a basis of the
stalk at `x` is realised by finitely many sections; by finiteness of type their germs still
generate every stalk on a neighbourhood, and because the fibre rank is locally constant a
generating family of the right cardinality in a finite module is automatically a basis. Taking
combinations of those sections is then injective on sections and locally surjective, which is
exactly the criterion `Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj` for a
trivialisation.

## Main results

* `AlgebraicGeometry.Scheme.Modules.nonempty_over_iso_free_of_span_germs` trivialises a module
  over an open on which finitely many sections have germs generating every stalk, their number
  being the rank of each of those stalks.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant` is
  the implication (5) ⟹ (4) of Stacks Tag 05P2.
* `AlgebraicGeometry.Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae` is
  Stacks Tag 05P2: all five of its conditions on a sheaf of modules on a scheme are equivalent.

## Implementation notes

`nonempty_over_iso_free_of_span_germs` assumes neither freeness of the stalks nor finiteness of
type: the hypothesis that the number of sections equals the rank of each stalk, together with
generation, already forces linear independence, because a commutative ring has the Orzech
property (`linearIndependent_of_top_le_span_of_card_eq_finrank`). Freeness and finiteness of
type enter only when producing the sections.

Finite local freeness has two spellings in this library, the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of Tag 01C6 and the pointwise predicate
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`; they are bridged by
`Stacks.Modules.isFiniteLocallyFree_iff_localGenerators`, and the equivalence below is stated
with the class, which is the one carrying the attribute for Tag 01C6. The further copy
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, off which the already proved consequences of
Tag 05P2 hang, is reached by `Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree`.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Trivialisation

variable {X : Scheme.{u}} (F : X.Modules) {I : Type u} [Fintype I] {U : X.Opens}
  (s : I → F.val.presheaf.obj (op U))

/-- The germs of finitely many sections generate every stalk over `U`, and there are as many of
them as the rank of each of those stalks, so they are a basis of every stalk: a generating
family whose cardinality is the rank of a module over a commutative ring is linearly
independent. -/
private theorem linearIndependent_germs
    (hspan : ∀ (y : X) (hy : y ∈ U),
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y hy (s i)))
    (hcard : ∀ (y : X), y ∈ U →
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Fintype.card I = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y))
    (y : X) (hy : y ∈ U) (c : I → X.presheaf.stalk y)
    (hc :
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ∑ i, c i • TopCat.Presheaf.germ F.val.presheaf U y hy (s i) = 0) :
    ∀ i, c i = 0 := by
  let : Module (X.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  exact Fintype.linearIndependent_iff.mp
    (linearIndependent_of_top_le_span_of_card_eq_finrank (hspan y hy) (hcard y hy)) c hc

/-- A combination of the sections `s` that vanishes on an open inside `U` has vanishing
coefficients, when their germs generate every stalk and their number is its rank. -/
private theorem eq_zero_of_sum_smul_res_eq_zero
    (hspan : ∀ (y : X) (hy : y ∈ U),
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y hy (s i)))
    (hcard : ∀ (y : X), y ∈ U →
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Fintype.card I = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y))
    {V : X.Opens} (f : V ⟶ U) (a : I → X.ringCatSheaf.obj.obj (op V))
    (ha : ∑ i, a i • Stacks.SheafOfModules.res F f (s i) = 0) : a = 0 := by
  funext i
  have hz : ∀ (y : X) (hy : y ∈ V), X.presheaf.germ V y hy (a i) = 0 := by
    intro y hy
    let : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    have hgerm : ∀ j, TopCat.Presheaf.germ F.val.presheaf V y hy
          (a j • Stacks.SheafOfModules.res F f (s j))
        = X.presheaf.germ V y hy (a j) •
            TopCat.Presheaf.germ F.val.presheaf U y (f.le hy) (s j) := fun j =>
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val y V hy (a j)
        (F.val.presheaf.map f.op (s j) : F.val.obj (op V))).trans
        (congrArg (fun w : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) =>
            X.presheaf.germ V y hy (a j) • w)
          (germ_map_section F f y hy (s j)))
    have hsum : ∑ j, X.presheaf.germ V y hy (a j) •
        TopCat.Presheaf.germ F.val.presheaf U y (f.le hy) (s j) = 0 :=
      (Finset.sum_congr rfl fun j _ => (hgerm j).symm).trans
        ((map_sum (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf V y hy)) _ _).symm.trans
          ((congrArg (ConcreteCategory.hom
            (TopCat.Presheaf.germ F.val.presheaf V y hy)) ha).trans (map_zero _)))
    exact linearIndependent_germs F s hspan hcard y (f.le hy)
      (fun j => X.presheaf.germ V y hy (a j)) hsum i
  exact TopCat.Presheaf.section_ext X.sheaf V (a i) 0 fun y hy =>
    (hz y hy).trans (map_zero _).symm

omit [Fintype I] in
/-- Restricting the sections `s` to a smaller open does not change their germs, so the restricted
germs still generate a stalk that the original germs generate. -/
private theorem top_le_span_germ_map_of_le {Z : X.Opens} (hZU : Z ≤ U) {y : X} (hy : y ∈ Z)
    (h :
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y (hZU hy) (s i))) :
    letI : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    ⊤ ≤ Submodule.span (X.presheaf.stalk y) (Set.range fun i =>
      TopCat.Presheaf.germ F.val.presheaf Z y hy (F.val.presheaf.map (homOfLE hZU).op (s i))) := by
  simpa only [germ_map_section F (homOfLE hZU) y hy] using h

/-- **Finitely many sections whose germs are a basis of every stalk trivialise the module.** If
the germs of `s` generate the stalk at every point of `U` and the number of sections is the rank
of each of those stalks, then the module is isomorphic to the free module on `I` over `U`.

Neither freeness of the stalks nor finiteness of type is needed: generation together with the
cardinality condition forces the germs to be linearly independent at every point, which gives
injectivity of taking combinations on sections, while generation gives local surjectivity. -/
theorem nonempty_over_iso_free_of_span_germs
    (hspan : ∀ (y : X) (hy : y ∈ U),
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      ⊤ ≤ Submodule.span (X.presheaf.stalk y)
        (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U y hy (s i)))
    (hcard : ∀ (y : X), y ∈ U →
      letI : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Fintype.card I = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)) :
    Nonempty (F.over U ≅ _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  classical
  refine Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj F s
    (fun V f a a' haa => ?_) (fun V f t y hy => ?_)
  · refine sub_eq_zero.mp (eq_zero_of_sum_smul_res_eq_zero F s hspan hcard f (a - a') ?_)
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [show (∑ i, a i • Stacks.SheafOfModules.res F f (s i))
      = ∑ i, a' i • Stacks.SheafOfModules.res F f (s i) from haa, sub_self]
  · let : Module (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    obtain ⟨W, hWV, hWU, hyW, c, hc⟩ := exists_combination_of_germ_mem_span F s t y (f.le hy) hy
      (hspan y (f.le hy) Submodule.mem_top)
    refine ⟨W, homOfLE hWV, hyW, c, ?_⟩
    rwa [show homOfLE hWV ≫ f = homOfLE hWU from Subsingleton.elim _ _]

end Trivialisation

section Implication

/-- **A module of finite type with free stalks and locally constant fibre rank is finite locally
free.** This is the implication (5) ⟹ (4) of Stacks Tag 05P2, in the pointwise spelling of
finite local freeness.

A basis of the stalk at `x` is realised by sections on a neighbourhood; their germs then
generate every stalk on a smaller neighbourhood because the module is of finite type, and the
locally constant fibre rank makes their number the rank of each of those stalks, so
`nonempty_over_iso_free_of_span_germs` trivialises the module there. -/
theorem pointwise_isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant {X : Scheme.{u}}
    (F : X.Modules) [F.IsFiniteType]
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hconst : IsLocallyConstant (fiberRank F)) :
    Scheme.Modules.IsFiniteLocallyFree F := by
  classical
  intro x
  let A := ToType (X.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module.Free A M := hfree x
  let : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf F x
  let I := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis I A M := Module.Free.chooseBasis A M
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite _
  have hcardx : Fintype.card I = Module.finrank A M := (Module.finrank_eq_card_basis b).symm
  obtain ⟨U, -, hxU, s, hs⟩ :=
    finite_germ_lifts F.val.presheaf x (fun i => (b i : M))
      (V := (⊤ : X.Opens)) (Set.mem_univ x)
  have hspanx : ⊤ ≤ Submodule.span A
      (Set.range fun i => TopCat.Presheaf.germ F.val.presheaf U x hxU (s i)) := by
    simp only [hs]
    exact b.span_eq.ge
  obtain ⟨W, hWU, hxW, hspanW⟩ := span_germs_near F s x hxU hspanx
  rw [IsLocallyConstant.iff_exists_open] at hconst
  obtain ⟨V, hVopen, hxV, hVeq⟩ := hconst x
  let Z : X.Opens := W ⊓ ⟨V, hVopen⟩
  have hZW : Z ≤ W := inf_le_left
  have hZU : Z ≤ U := hZW.trans hWU
  have hZV : (Z : Set X) ⊆ V := fun _ hz => hz.2
  let t : I → F.val.presheaf.obj (op Z) := fun i => F.val.presheaf.map (homOfLE hZU).op (s i)
  have hcardZ : ∀ (y : X) (hy : y ∈ Z),
      let : Module (X.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val y
      Fintype.card I = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) := by
    intro y hy
    have hy' : fiberRank F y = Module.finrank (X.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y) :=
      fiberRank_eq_finrank_stalk F y (hfree y)
    have hx' : fiberRank F x = Module.finrank A M := fiberRank_eq_finrank_stalk F x (hfree x)
    exact hcardx.trans (hx'.symm.trans ((hVeq y (hZV hy)).symm.trans hy'))
  obtain ⟨e⟩ := nonempty_over_iso_free_of_span_germs F t
    (fun y hy => top_le_span_germ_map_of_le F s hZU hy (hspanW y (hZW hy))) hcardZ
  exact ⟨Z, ⟨hxW, hxV⟩, I, inferInstance, ⟨Stacks.Modules.restrictIsoFree Z F I e.symm⟩⟩

/-- **A module of finite type with free stalks and locally constant fibre rank is finite locally
free.** This is the implication (5) ⟹ (4) of Stacks Tag 05P2, with finite local freeness in the
spelling of Stacks Tag 01C6. -/
theorem isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant {X : Scheme.{u}}
    (F : X.Modules) (hft : _root_.SheafOfModules.IsFiniteType.{u, u, u} F)
    (hfree : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x))
    (hconst : IsLocallyConstant (fiberRank F)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F :=
  have := hft
  (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators F).mp
    (pointwise_isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant F hfree hconst)

/-- For a sheaf of modules `F` on a scheme `X` the following are equivalent: `F` is flat and of
finite presentation; `F` is of finite presentation and all its stalks are free; `F` is locally
free and of finite type; `F` is finite locally free; `F` is of finite type, all its stalks are
free, and its fibre rank is locally constant.

Quasi-coherence is not assumed: it is implied by each of the five conditions. -/
@[stacks 05P2,
  ega "III 7.3.4",
  ega "0 5.4.1" "partial, special case",
  ega "IV 19.7.4" "more general",
  ega "IV 2.1.12" "special case"]
theorem flat_finitePresentation_locallyFree_fiberRank_tfae {X : Scheme.{u}} (F : X.Modules) :
    List.TFAE [
      AlgebraicGeometry.SheafOfModules.IsFlat
          (C := TopologicalSpace.Opens X.toTopCat)
          (J := Opens.grothendieckTopology X.toTopCat) (O := X.sheaf) F ∧
        F.IsFinitePresentation,
      F.IsFinitePresentation ∧
        (∀ x : X,
          letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) F.val x
          Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)),
      _root_.SheafOfModules.IsLocallyFree.{u, u, u} F ∧
        _root_.SheafOfModules.IsFiniteType.{u, u, u} F,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F,
      _root_.SheafOfModules.IsFiniteType.{u, u, u} F ∧
        (∀ x : X,
          letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) F.val x
          Module.Free (X.presheaf.stalk x) (F.presheaf.stalk x)) ∧
        IsLocallyConstant (fiberRank F)] := by
  tfae_have 1 → 2 := fun ⟨hflat, hfp⟩ => ⟨hfp, free_stalk_of_isFlat F hfp hflat⟩
  tfae_have 2 → 3 := by
    rintro ⟨hfp, hstalk⟩
    exact ⟨(isLocallyFree_iff_pointwise F).mpr
        (pointwise_isLocallyFree_of_free_stalks F hfp hstalk),
      isFiniteType_of_isFinitePresentation F hfp⟩
  tfae_have 3 → 4 := by
    rintro ⟨hfree, htype⟩
    let := htype
    exact Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree F
      (hM := isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType F
        ((isLocallyFree_iff_pointwise F).mp hfree))
  tfae_have 4 → 1 := by
    intro h
    let := Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F (hM := h)
    exact ⟨isFlat_of_isFiniteLocallyFree F, Stacks.FiniteLocallyFree.isFinitePresentation F⟩
  tfae_have 4 → 5 := by
    intro h
    let := Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F (hM := h)
    exact isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank F
  tfae_have 5 → 4 := fun ⟨hft, hfree, hconst⟩ =>
    isFiniteLocallyFree_of_free_stalk_of_isLocallyConstant F hft hfree hconst
  tfae_finish

end Implication

end AlgebraicGeometry.Scheme.Modules

end
