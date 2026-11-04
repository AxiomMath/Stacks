module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.IdealSheafQuotient
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of `𝒪_X / I` is the vanishing locus of `I`

Let `X` be a scheme and `I : X.IdealSheafData` a quasi-coherent sheaf of ideals. This file
identifies the support of the quotient module `𝒪_X / I`
(`Stacks.AlgebraicGeometry.IdealSheafQuotient.structureQuotient`) with the closed subset
`AlgebraicGeometry.Scheme.IdealSheafData.support` cut out by `I`. **No Noetherian, coherence or
finite-type hypothesis is used.**

## Main results

* `Stacks.AlgebraicGeometry.IdealSheafQuotient.supp_structureQuotient`: **the support of
  `𝒪_X / I` is the vanishing locus of `I`.**
* `Stacks.AlgebraicGeometry.IdealSheafQuotient.notMem_supp_iff_forall_eq_zero`,
  `Stacks.AlgebraicGeometry.IdealSheafQuotient.forall_stalk_cokernel_eq_zero_iff` and
  `Stacks.AlgebraicGeometry.IdealSheafQuotient.surjective_stalkMap_ι_iff`: the three sheaf-level
  steps, for an arbitrary sheaf of rings on a topological space.
* `Stacks.AlgebraicGeometry.IdealSheafQuotient.one_mem_unitSubmodule_iff_notMem_support`: the
  scheme-level step, comparing the sections of `I` with the vanishing locus of `I`.

## Implementation notes

The proof is a chain of three equivalences, each of which holds in more generality than the
statement needs and is recorded separately.

1. A point lies outside the support of a sheaf of modules exactly when every element of its
   stalk vanishes. The carrier of `AlgebraicGeometry.SheafOfModules.stalkObj` is by construction
   the abelian-group stalk that `SheafOfModules.supp` is defined by, so this is a restatement.
2. For the cokernel of a *monomorphism* of sheaves of modules, that happens exactly when the
   induced map of stalk modules is surjective: the stalk functor is exact
   (`AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact`), so it
   carries the short exact sequence of the quotient to a short exact sequence of stalk modules.
3. For the inclusion of an ideal subsheaf `J ⊆ 𝒪_X` that map is surjective exactly when `J`
   contains the unit section on some open neighbourhood of the point. One direction shrinks the
   open on which a section with germ `1` agrees with `1`; the other multiplies the unit section,
   which then lies in `J`, by an arbitrary section.

The last step is then compared with the vanishing locus. Off the vanishing locus some ideal
`I.ideal U` has a section `a` with `x ∈ X.basicOpen a`; the restriction of `a` to `X.basicOpen a`
is a unit (`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`), and an ideal containing a unit
is the unit ideal. Conversely, if `I.unitSubmodule` contains the unit section over an open `U`
containing `x`, shrink `U` to an affine open `W` — this is where
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` is needed, since `Scheme.IdealSheafData`
records no data over a non-affine open — and then `1 ∈ I.ideal W` by
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`, so `x ∈ X.basicOpen 1 = W`
shows `x` is off the vanishing locus.

The stalk ideal `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal` is deliberately *not* used:
the sections of `I.unitSubmodule` are compared with the vanishing locus directly, which avoids
having to identify the range of the stalk map of `I.unitSubmodule.ι` — an additive-group stalk —
with an ideal of the ring-valued stalk `𝒪_{X,x}`.

The germs of sections of the structure sheaf are written through the abbreviations `unitGerm`
and `subGerm`, whose arguments are sections of `O` and of `J` respectively: the sections of the
unit sheaf of modules are the sections of `O` only up to unfolding, so a numeral such as `1`
cannot be elaborated directly at the module spelling.

No `@[stacks]` attribute is attached. [Stacks, Tag 01PH] asserts both that the quotient of the
structure sheaf by a quasi-coherent ideal sheaf of finite type is of finite presentation and
that its support is the closed set cut out by the ideal; the finite presentation half is
`Stacks.AlgebraicGeometry.IdealSheafQuotient.isFinitePresentation_structureQuotient`, which is
untagged as well. What is proved here is substrate for that lemma rather than the lemma itself,
and placing a tag on one half only would make the covering set ambiguous.

## References

* [Stacks Project, Lemma 28.25.1 (Tag 01PH)](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.IdealSheafQuotient

/-! ### The support of a quotient of sheaves of modules -/

section Sheaf

variable {Y : TopCat.{u}} {O : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- The germ at `x` of a section of the structure sheaf, in the stalk of the unit module. -/
private abbrev unitGerm (x : Y) (U : Opens Y) (hx : x ∈ U) (s : O.obj.obj (op U)) :
    AlgebraicGeometry.SheafOfModules.stalkObj O x (_root_.SheafOfModules.unit O) :=
  (TopCat.Presheaf.germ (_root_.SheafOfModules.unit O).val.presheaf U x hx).hom s

/-- The germ at `x` of a section of an ideal subsheaf, in the stalk of that subsheaf. -/
private abbrev subGerm (J : (_root_.SheafOfModules.unit O).Submodule) (x : Y) (U : Opens Y)
    (hx : x ∈ U) (s : (J.toSheafOfModules).val.obj (op U)) :
    AlgebraicGeometry.SheafOfModules.stalkObj O x (J.toSheafOfModules) :=
  (TopCat.Presheaf.germ (J.toSheafOfModules).val.presheaf U x hx).hom s

/-- A point lies outside the support of a sheaf of modules exactly when every element of its
stalk at that point vanishes. -/
theorem notMem_supp_iff_forall_eq_zero (F : _root_.SheafOfModules.{u} O) (x : Y) :
    x ∉ _root_.SheafOfModules.supp F ↔
      ∀ a : AlgebraicGeometry.SheafOfModules.stalkObj O x F, a = 0 :=
  ⟨fun h a => by_contra fun ha => h ⟨a, ha⟩, fun h ⟨a, ha⟩ => ha (h a)⟩

/-- **The stalk of the cokernel of a monomorphism of sheaves of modules vanishes exactly where
the monomorphism is surjective on stalks.** The stalk functor on sheaves of modules is exact, so
it carries the short exact sequence of the quotient to a short exact sequence of stalk
modules. -/
theorem forall_stalk_cokernel_eq_zero_iff {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N)
    (hf : Mono f) (x : Y) :
    (∀ a : (AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj (cokernel f), a = 0) ↔
      Function.Surjective (AlgebraicGeometry.SheafOfModules.stalkMap O x f).hom := by
  have hse : ((ShortComplex.mk f (cokernel.π f) (cokernel.condition _)).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O x)).ShortExact := by
    refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact _).mp ?_ x
    exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
            mono_f := hf
            epi_g := inferInstance }
  set S := (ShortComplex.mk f (cokernel.π f) (cokernel.condition _)).map
    (AlgebraicGeometry.SheafOfModules.stalkFunctor O x)
  have hz : ∀ c : S.X₁, (ConcreteCategory.hom S.g) ((ConcreteCategory.hom S.f) c) = 0 := by
    simp
  refine ⟨fun h b => (ShortComplex.moduleCat_exact_iff _).mp hse.exact b (h _), fun hsurj a => ?_⟩
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective _).mp hse.epi_g a
  obtain ⟨c, rfl⟩ := hsurj b
  exact hz c

/-- If an ideal subsheaf contains `1` over `U`, it contains `1` over every smaller open. -/
private theorem one_mem_of_le (J : (_root_.SheafOfModules.unit O).Submodule) {U W : Opens Y}
    (h : W ≤ U) (h1 : (1 : O.obj.obj (op U)) ∈ J.obj (op U)) :
    (1 : O.obj.obj (op W)) ∈ J.obj (op W) :=
  map_one (O.obj.map (homOfLE h).op).hom ▸ J.toSubmodule.map_mem (homOfLE h).op h1

/-- **The stalk of an ideal subsheaf of the structure sheaf exhausts the stalk of the structure
sheaf exactly when the ideal contains the unit section near the point.** One direction shrinks
the open on which a section with germ `1` agrees with `1`; the other multiplies the germ of the
unit section, which lies in the image, by an arbitrary germ. -/
theorem surjective_stalkMap_ι_iff (J : (_root_.SheafOfModules.unit O).Submodule) (x : Y) :
    Function.Surjective (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom ↔
      ∃ U : Opens Y, ∃ _ : x ∈ U, (1 : O.obj.obj (op U)) ∈ J.obj (op U) := by
  constructor
  · intro hsurj
    obtain ⟨a, ha⟩ := hsurj (unitGerm x ⊤ trivial 1)
    obtain ⟨U, hxU, t, ht⟩ := TopCat.Presheaf.exists_germ_eq
      (J.toSheafOfModules).val.presheaf a
    subst ht
    have ha' : unitGerm x U hxU (J.ι.val.app (op U) t) = unitGerm x ⊤ trivial 1 :=
      (AlgebraicGeometry.SheafOfModules.stalkMap_germ O x J.ι U hxU t).symm.trans ha
    obtain ⟨W, hxW, iU, iTop, hW⟩ := TopCat.Presheaf.germ_eq
      (_root_.SheafOfModules.unit O).val.presheaf x hxU (show x ∈ (⊤ : Opens Y) from trivial)
      (J.ι.val.app (op U) t) (1 : O.obj.obj (op (⊤ : Opens Y))) ha'
    refine ⟨W, hxW, ?_⟩
    have h2 : ((_root_.SheafOfModules.unit O).val.presheaf.map iU.op).hom
        (J.ι.val.app (op U) t) ∈ J.obj (op W) := J.toSubmodule.map_mem iU.op t.2
    have hone : ((_root_.SheafOfModules.unit O).val.presheaf.map iTop.op).hom
        (1 : O.obj.obj (op (⊤ : Opens Y))) = (1 : O.obj.obj (op W)) :=
      map_one (O.obj.map iTop.op).hom
    exact (hW.trans hone) ▸ h2
  · rintro ⟨U, hxU, h1⟩ b
    obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq
      (_root_.SheafOfModules.unit O).val.presheaf b
    have hxW : x ∈ V ⊓ U := ⟨hxV, hxU⟩
    have h1W := one_mem_of_le J (inf_le_right (a := V)) h1
    set r : O.obj.obj (op (V ⊓ U)) :=
      (O.obj.map (homOfLE (inf_le_left (a := V) (b := U))).op).hom s
    refine ⟨(TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r •
      subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩, ?_⟩
    calc (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom
          ((TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r •
            subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩)
        = (TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r •
            (AlgebraicGeometry.SheafOfModules.stalkMap O x J.ι).hom
              (subGerm J x (V ⊓ U) hxW ⟨(1 : O.obj.obj (op (V ⊓ U))), h1W⟩) := map_smul _ _ _
      _ = (TopCat.Presheaf.germ (C := RingCat.{u}) O.obj (V ⊓ U) x hxW).hom r •
            unitGerm x (V ⊓ U) hxW (1 : O.obj.obj (op (V ⊓ U))) :=
            congrArg _ (AlgebraicGeometry.SheafOfModules.stalkMap_germ O x J.ι (V ⊓ U) hxW _)
      _ = unitGerm x (V ⊓ U) hxW (r * (1 : O.obj.obj (op (V ⊓ U)))) :=
            (AlgebraicGeometry.SheafOfModules.germ_hom_smul O x (_root_.SheafOfModules.unit O).val
              (V ⊓ U) hxW r (1 : O.obj.obj (op (V ⊓ U)))).symm
      _ = unitGerm x (V ⊓ U) hxW r := by rw [mul_one]
      _ = unitGerm x V hxV s := TopCat.Presheaf.germ_res_apply
            (_root_.SheafOfModules.unit O).val.presheaf
            (homOfLE (inf_le_left (a := V) (b := U))) x hxW s
      _ = b := hs

end Sheaf

/-! ### The support of `𝒪_X / I` -/

section Scheme

variable {X : Scheme.{u}}

/-- **An ideal sheaf contains the unit section near a point exactly when the point is off its
vanishing locus.**

Off the vanishing locus some ideal `I.ideal U` has a section `a` not vanishing at the point, and
the restriction of `a` to `X.basicOpen a` is a unit, so the sections of `I` there form the unit
ideal. Conversely a neighbourhood on which `I` contains `1` may be shrunk to an affine open `W`,
where `1` then lies in `I.ideal W`, so the point lies in `X.basicOpen 1 = W`. -/
theorem one_mem_unitSubmodule_iff_notMem_support (I : X.IdealSheafData) (x : X) :
    (∃ U : Opens X, ∃ _ : x ∈ U, (1 : Γ(X, U)) ∈ I.unitSubmodule.obj (op U)) ↔
      x ∉ I.support := by
  constructor
  · rintro ⟨U, hxU, h1⟩ hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
    have h1W : (1 : Γ(X, W)) ∈ I.ideal ⟨W, hW⟩ := by
      rw [← I.unitSubmodule_obj_affine ⟨W, hW⟩]
      exact one_mem_of_le I.unitSubmodule hWU h1
    rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW,
      X.mem_zeroLocus_iff] at hx
    exact hx 1 h1W (by simpa using hxW)
  · intro hx
    rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff] at hx
    obtain ⟨U, hU⟩ := not_forall.mp hx
    rw [X.mem_zeroLocus_iff] at hU
    obtain ⟨a, ha, hxa⟩ := by simpa using not_forall.mp hU
    refine ⟨X.basicOpen a, hxa, ?_⟩
    have hmem : (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom a ∈
        I.unitSubmodule.obj (op (X.basicOpen a)) :=
      I.unitSubmodule.toSubmodule.map_mem (homOfLE (X.basicOpen_le a)).op
        (show a ∈ I.unitSubmodule.obj (op U.1) from (I.unitSubmodule_obj_affine U).ge ha)
    exact (Ideal.eq_top_iff_one _).mp
      (Ideal.eq_top_of_isUnit_mem _ hmem (X.toRingedSpace.isUnit_res_basicOpen a))

/-- **The support of `𝒪_X / I` is the closed subset cut out by `I`.** No Noetherian, coherence
or finite-type hypothesis on `X` or on `I`.

This is the vanishing-locus half of step 2 of the proof of [Stacks, Tag 0GPJ]; the finite
presentation half is
`Stacks.AlgebraicGeometry.IdealSheafQuotient.isFinitePresentation_structureQuotient`. -/
@[ega "I 4.1.2", ega "IV 8.9.1" "partial"]
theorem supp_structureQuotient (I : X.IdealSheafData) :
    _root_.SheafOfModules.supp (structureQuotient I) = (I.support : Set X) := by
  ext x
  rw [← not_iff_not]
  exact (notMem_supp_iff_forall_eq_zero (structureQuotient I) x).trans
    ((forall_stalk_cokernel_eq_zero_iff I.unitSubmodule.ι inferInstance x).trans
      ((surjective_stalkMap_ι_iff I.unitSubmodule x).trans
        (one_mem_unitSubmodule_iff_notMem_support I x)))

end Scheme

end Stacks.AlgebraicGeometry.IdealSheafQuotient

end
