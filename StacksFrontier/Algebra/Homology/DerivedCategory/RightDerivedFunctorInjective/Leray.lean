module

import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness

/-!
# Right acyclicity in short exact sequences and Leray's acyclicity lemma

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives. This file proves that two right acyclic objects in a short exact sequence force the
third ([Stacks, Tag 015D]), builds the distinguished triangle of a stupid truncation of a bounded
below complex, and proves Leray's acyclicity lemma ([Stacks, Tag 015E]): a bounded below complex
of right `F`-acyclic objects computes `RF`.

## Main results

* `CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact`
* `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`

## References

* [Stacks, Tag 015D]
* [Stacks, Tag 015E]
* [Stacks, Tag 0118]
* [Stacks, Tag 0152]
-/

@[expose] public section

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory.Functor

open _root_.DerivedCategory

-- As in `RightDerivedFunctorInjective.Exactness`, the instance deriving the conclusion of
-- `hasPointwiseRightDerivedFunctorAt_of_injective` from `EnoughInjectives 𝒜` takes precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section EpiMap

variable {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}

/-- A natural isomorphism of functors does not change which morphisms are sent to epimorphisms. -/
private lemma epi_map_iff_of_natIso (e : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    Epi (F.map f) ↔ Epi (G.map f) := by
  constructor <;> intro _
  · rw [← NatIso.naturality_1 e f]
    infer_instance
  · rw [← NatIso.naturality_2 e f]
    infer_instance

end EpiMap

section SingleTriangle

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex C}

/-- The distinguished triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0]⟦1⟧` of `D⁺(𝒜)` attached to a short
exact sequence `S` of `𝒜`: the bounded below form of
`CategoryTheory.ShortComplex.ShortExact.singleTriangle`. -/
private noncomputable def singleTrianglePlus (hS : S.ShortExact) :
    Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((Plus.singleFunctor C 0).map S.f) ((Plus.singleFunctor C 0).map S.g)
    (Plus.ι.preimage (hS.singleδ ≫
      (Plus.ι.commShiftIso (1 : ℤ)).inv.app ((Plus.singleFunctor C 0).obj S.X₁)))

set_option backward.isDefEq.respectTransparency false in
private lemma ι_mapTriangle_obj_singleTrianglePlus (hS : S.ShortExact) :
    Plus.ι.mapTriangle.obj (singleTrianglePlus hS) = hS.singleTriangle := by
  rw [Functor.mapTriangle_obj]
  dsimp only [singleTrianglePlus, Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
    Triangle.mk_obj₁]
  rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g))
    (Category.comp_id hS.singleδ)

set_option backward.isDefEq.respectTransparency false in
private lemma singleTrianglePlus_distinguished (hS : S.ShortExact) :
    singleTrianglePlus hS ∈ distTriang (DerivedCategory.Plus C) := by
  show Plus.ι.mapTriangle.obj (singleTrianglePlus hS) ∈ distTriang (DerivedCategory C)
  rw [ι_mapTriangle_obj_singleTrianglePlus hS]
  exact hS.singleTriangle_distinguished

end SingleTriangle

section Main

open Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The commutation of `RF` with the shift induced by the universal property of the right
derived functor. It is a local instance: [Stacks, Tag 0159] needs it to state the exactness
of `RF`. -/
@[instance_reducible]
public noncomputable def commShiftRightDerivedFunctorPlus :
    F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _ F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] commShiftRightDerivedFunctorPlus

/-- The unit of `RF` is compatible with the shift. -/
public lemma natTransCommShiftRightDerivedFunctorPlusUnit :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ :=
  Functor.IsRightDerivedFunctor.natTrans_commShift F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) ℤ

attribute [local instance] natTransCommShiftRightDerivedFunctorPlusUnit

/-- `RF` is an exact functor of triangulated categories, [Stacks, Tag 0159]. -/
public lemma isTriangulated_rightDerivedFunctorPlus :
    F.rightDerivedFunctorPlus.IsTriangulated :=
  isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
    F.rightDerivedFunctorPlusUnith

attribute [local instance] isTriangulated_rightDerivedFunctorPlus

/-- The unit of `RF` at the complexes `A[i]`, taken in homological degree `i`: the canonical
map `F ⟶ H ⁱ(RF((-)[i]))` of which [Stacks, Tag 05TD] part (3) is the case `i = 0`, before its
two ends are identified with `F` and with `H ⁱ(RF((-)[i]))`.

Nothing but the whiskering is involved, so the degree is only carried along; what the degree-`i`
form costs is the invertibility, `isIso_homologyUnitAppSingleAt`. -/
public noncomputable def homologyUnitAppSingleAt (i : ℤ) :
    HomotopyCategory.Plus.singleFunctor C i ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⋙
        Plus.homologyFunctor D i ⟶
      HomotopyCategory.Plus.singleFunctor C i ⋙ Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙
        Plus.homologyFunctor D i :=
  Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor C i)
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnith (Plus.homologyFunctor D i))

/-- **The unit of `RF` at `A[i]`, read by `H ⁱ`, is invertible for a left exact `F`**: the
degree-`i` form of the `⇐` direction of [Stacks, Tag 05TD] part (3), whose case `i = 0` is
`isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`.

The degree is moved by the shift, and only invertibility has to be transported, so no
identification of the three shift isomorphisms involved is needed — each contributes a square
with isomorphisms on three sides:

* `A[i]` is `A[0]⟦-i⟧`, by the shift isomorphism of `HomotopyCategory.Plus.singleFunctors`, and
  the unit is natural;
* the unit commutes with the shift, which is
  `CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit`;
* `H ⁱ` of a `⟦-i⟧`-shift is `H ⁰`, by the shift sequence of `DerivedCategory.Plus.homologyFunctor`,
  which is natural. -/
public lemma isIso_homologyFunctor_map_rightDerivedFunctorPlusUnit_app_single
    [PreservesFiniteLimits F] (i : ℤ) (X : C) :
    IsIso ((Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C i).obj X))) := by
  -- The degree-zero statement, which is where left exactness of `F` is used.
  have h₀ : IsIso ((Plus.homologyFunctor D 0).map (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj X))) :=
    (isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
      F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith).2.2.2 ‹_› X
  -- Step 3: `H ⁱ` of a `⟦-i⟧`-shift is `H ⁰`, naturally.
  have hs : shiftFunctor (DerivedCategory.Plus D) (-i) ⋙ Plus.homologyFunctor D i ≅
      Plus.homologyFunctor D 0 :=
    (Plus.homologyFunctor D 0).shiftIso (-i) i 0 (by omega)
  have h₃ : IsIso ((Plus.homologyFunctor D i).map ((shiftFunctor
      (DerivedCategory.Plus D) (-i)).map (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X)))) :=
    (NatIso.isIso_map_iff hs (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj X))).mpr h₀
  -- Step 2: the unit commutes with the shift.
  have h₂ : IsIso ((Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnith.app
      ((shiftFunctor (HomotopyCategory.Plus C) (-i)).obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj X)))) := by
    rw [NatTrans.shift_app F.rightDerivedFunctorPlusUnith (-i)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj X), Functor.map_comp,
      Functor.map_comp] at h₃
    have := IsIso.of_isIso_comp_left ((Plus.homologyFunctor D i).map
        ((Functor.commShiftIso (F.mapHomotopyCategoryPlus ⋙ Plus.Qh)
          (-i)).inv.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X)))
      ((Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnith.app
          ((shiftFunctor (HomotopyCategory.Plus C) (-i)).obj
            ((HomotopyCategory.Plus.singleFunctor C 0).obj X))) ≫
        (Plus.homologyFunctor D i).map
          ((Functor.commShiftIso (Plus.Qh ⋙ F.rightDerivedFunctorPlus)
            (-i)).hom.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X)))
    exact IsIso.of_isIso_comp_right _ ((Plus.homologyFunctor D i).map
      ((Functor.commShiftIso (Plus.Qh ⋙ F.rightDerivedFunctorPlus)
        (-i)).hom.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X)))
  -- Step 1: `A[i]` is `A[0]⟦-i⟧`, and the unit is natural.
  have e : HomotopyCategory.Plus.singleFunctor C 0 ⋙
      shiftFunctor (HomotopyCategory.Plus C) (-i) ≅ HomotopyCategory.Plus.singleFunctor C i :=
    (HomotopyCategory.Plus.singleFunctors C).shiftIso (-i) i 0 (by omega)
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight F.rightDerivedFunctorPlusUnith
    (Plus.homologyFunctor D i)) (e.app X)).1 h₂

/-- For a left exact `F` the canonical map `F ⟶ H ⁱ(RF((-)[i]))` is an isomorphism, in the
spelling of `homologyUnitAppSingleAt`. The case `i = 0` is the `⇐` direction of
[Stacks, Tag 05TD] part (3). -/
public lemma isIso_homologyUnitAppSingleAt [PreservesFiniteLimits F] (i : ℤ) :
    IsIso (homologyUnitAppSingleAt F i) :=
  have : ∀ X : C, IsIso ((homologyUnitAppSingleAt F i).app X) := fun X ↦
    isIso_homologyFunctor_map_rightDerivedFunctorPlusUnit_app_single F i X
  NatIso.isIso_of_isIso_app _

/-- The unit of `RF` at the complexes `A[0]`, taken in homological degree `0`: the canonical
map `F ⟶ R ⁰ F` of [Stacks, Tag 05TD] part (3), before its two ends are identified with `F`
and with `R ⁰ F`. -/
private noncomputable def homologyUnitAppSingle :
    HomotopyCategory.Plus.singleFunctor C 0 ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⋙
        Plus.homologyFunctor D 0 ⟶
      HomotopyCategory.Plus.singleFunctor C 0 ⋙ Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙
        Plus.homologyFunctor D 0 :=
  homologyUnitAppSingleAt F 0

private lemma isIso_homologyUnitAppSingle [PreservesFiniteLimits F] :
    IsIso (homologyUnitAppSingle F) :=
  isIso_homologyUnitAppSingleAt F 0

/-- **The canonical isomorphism `F ≅ H ⁱ(RF((-)[i]))` for a left exact `F`**, the degree-`i` form
of [Stacks, Tag 05TD] part (3): the unit of `RF` at `A[i]` is an isomorphism on `H ⁱ`, its source
is `F(A)` and its target is `H ⁱ(RF(A[i]))`.

The case `i = 0` is `CategoryTheory.Functor.isoRightDerivedPlusZero`, which is defined as this
isomorphism there. Nothing in the construction refers to the degree-zero case: the three
identifications it conjugates the unit by — `mapSingleFunctorCompQhIsoOfDegree`,
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso` and `singleFunctorPlusIsoCompQh` —
are all indexed by the degree already, so no shift isomorphism is commuted past the unit here.
-/
public noncomputable def isoRightDerivedPlusSingle [PreservesFiniteLimits F] (i : ℤ) :
    F ≅ Plus.singleFunctor C i ⋙ F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D i :=
  haveI := isIso_homologyUnitAppSingleAt F i
  (Functor.isoWhiskerRight (mapSingleFunctorCompQhIsoOfDegree F i) (Plus.homologyFunctor D i) ≪≫
      Functor.isoWhiskerLeft F (Plus.singleFunctorCompHomologyFunctorIso i) ≪≫
      F.rightUnitor).symm ≪≫
    asIso (homologyUnitAppSingleAt F i) ≪≫
    (Functor.isoWhiskerRight (singleFunctorPlusIsoCompQh i)
      (F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D i)).symm

/-- **The closed form of `isoRightDerivedPlusSingle`: it is the unit of `RF` at `A[i]` read by
`H ⁱ`**, conjugated by the three identifications of its two ends. This is the statement that makes
the degree-`i` isomorphism `F ≅ H ⁱ(RF((-)[i]))` usable: a comparison built from the unit at the
level of complexes can be matched against it. -/
public lemma isoRightDerivedPlusSingle_hom_app [PreservesFiniteLimits F] (i : ℤ) (X : C) :
    (F.isoRightDerivedPlusSingle i).hom.app X =
      (Plus.singleFunctorCompHomologyFunctorIso i).inv.app (F.obj X) ≫
        (Plus.homologyFunctor D i).map ((mapSingleFunctorCompQhIsoOfDegree F i).inv.app X) ≫
          (Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.singleFunctor C i).obj X)) ≫
            (Plus.homologyFunctor D i).map (F.rightDerivedFunctorPlus.map
              ((singleFunctorPlusIsoCompQh i).inv.app X)) := by
  have := isIso_homologyUnitAppSingleAt F i
  simp [isoRightDerivedPlusSingle, homologyUnitAppSingleAt]

/-- The canonical isomorphism `F ≅ R ⁰ F` for a left exact `F`, [Stacks, Tag 05TD] part (3):
the unit of `RF` at `A[0]` is an isomorphism on `H ⁰`, its source is `F(A)`, and its target is
`R ⁰ F(A)`. This is the degree-zero case of `isoRightDerivedPlusSingle`. -/
private noncomputable def isoRightDerivedPlusZero [PreservesFiniteLimits F] :
    F ≅ F.rightDerivedPlus 0 :=
  F.isoRightDerivedPlusSingle 0

variable {S : ShortComplex C} (hS : S.ShortExact)

include hS

/-- The distinguished triangle `RF(A[0]) ⟶ RF(B[0]) ⟶ RF(C[0]) ⟶ RF(A[0])⟦1⟧` of `D⁺(ℬ)`. -/
private noncomputable def derivedTriangle : Triangle (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.mapTriangle.obj (singleTrianglePlus hS)

private lemma derivedTriangle_distinguished :
    derivedTriangle F hS ∈ distTriang (DerivedCategory.Plus D) :=
  F.rightDerivedFunctorPlus.map_distinguished _ (singleTrianglePlus_distinguished hS)

/-- `R ⁿ F(B) ⟶ R ⁿ F(C)` is epi exactly when the connecting morphism `R ⁿ F(C) ⟶ R ⁿ⁺¹ F(A)`
of the long exact sequence vanishes. -/
private lemma epi_rightDerivedPlus_map_g_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Epi ((F.rightDerivedPlus n₀).map S.g) ↔
      (Plus.homologyFunctor D 0).homologySequenceδ (derivedTriangle F hS) n₀ n₁ h = 0 :=
  (Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff _
    (derivedTriangle_distinguished F hS) n₀ n₁ h

/-- Exactness at `R ⁱ F(B)`: if `R ⁱ F(A) = 0` and `R ⁱ F(C) = 0` then `R ⁱ F(B) = 0`. -/
public lemma isZero_rightDerivedPlus_X₂ (i : ℤ)
    (h₁ : IsZero ((F.rightDerivedPlus i).obj S.X₁))
    (h₃ : IsZero ((F.rightDerivedPlus i).obj S.X₃)) :
    IsZero ((F.rightDerivedPlus i).obj S.X₂) :=
  ((Plus.homologyFunctor D 0).homologySequence_exact₂ _
      (derivedTriangle_distinguished F hS) i).isZero_X₂_iff.2
    ⟨h₁.eq_of_src _ _, h₃.eq_of_tgt _ _⟩

/-- Exactness at `R ⁱ F(C)`: if `R ⁱ F(B) = 0` and `R ⁱ⁺¹ F(A) = 0` then `R ⁱ F(C) = 0`. -/
private lemma isZero_rightDerivedPlus_X₃ (i : ℤ)
    (h₂ : IsZero ((F.rightDerivedPlus i).obj S.X₂))
    (h₁ : IsZero ((F.rightDerivedPlus (i + 1)).obj S.X₁)) :
    IsZero ((F.rightDerivedPlus i).obj S.X₃) :=
  ((Plus.homologyFunctor D 0).homologySequence_exact₃ _
      (derivedTriangle_distinguished F hS) i (i + 1) rfl).isZero_X₂_iff.2
    ⟨h₂.eq_of_src _ _, h₁.eq_of_tgt _ _⟩

/-- Exactness at `R ⁿ⁺¹ F(A)`: if `R ⁿ F(B) ⟶ R ⁿ F(C)` is epi and `R ⁿ⁺¹ F(B) = 0` then
`R ⁿ⁺¹ F(A) = 0`. -/
private lemma isZero_rightDerivedPlus_X₁ (n : ℤ)
    (hg : Epi ((F.rightDerivedPlus n).map S.g))
    (h₂ : IsZero ((F.rightDerivedPlus (n + 1)).obj S.X₂)) :
    IsZero ((F.rightDerivedPlus (n + 1)).obj S.X₁) :=
  ((Plus.homologyFunctor D 0).homologySequence_exact₁ _
      (derivedTriangle_distinguished F hS) n (n + 1) rfl).isZero_X₂_iff.2
    ⟨(epi_rightDerivedPlus_map_g_iff F hS n (n + 1) rfl).1 hg, h₂.eq_of_tgt _ _⟩

/-- If `R ¹ F(A) = 0` then `F(B) ⟶ F(C)` is epi. -/
public lemma epi_map_g [PreservesFiniteLimits F]
    (h₁ : IsZero ((F.rightDerivedPlus 1).obj S.X₁)) : Epi (F.map S.g) :=
  (epi_map_iff_of_natIso (isoRightDerivedPlusZero F) S.g).2
    ((epi_rightDerivedPlus_map_g_iff F hS 0 1 rfl).2 (h₁.eq_of_tgt _ _))

/-- If `F(B) ⟶ F(C)` is epi and `R ⁱ F(C) = 0` for `i > 0`, then `R ⁿ F(B) ⟶ R ⁿ F(C)` is epi in
every degree `n ≥ 0`. -/
private lemma epi_rightDerivedPlus_map_g [PreservesFiniteLimits F] (hg : Epi (F.map S.g))
    (h₃ : ∀ i > 0, IsZero ((F.rightDerivedPlus i).obj S.X₃)) (n : ℤ) (hn : 0 ≤ n) :
    Epi ((F.rightDerivedPlus n).map S.g) := by
  rcases hn.eq_or_lt with rfl | h
  · exact (epi_map_iff_of_natIso (isoRightDerivedPlusZero F) S.g).1 hg
  · exact (epi_rightDerivedPlus_map_g_iff F hS n (n + 1) rfl).2 ((h₃ n h).eq_of_src _ _)

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- A left exact `F` takes `S` to a short exact sequence as soon as `F(B) ⟶ F(C)` is epi: the
common conclusion of the three parts of [Stacks, Tag 015D]. -/
private lemma shortExact_map [PreservesFiniteLimits F] (hg : Epi (F.map S.g)) :
    (S.map F).ShortExact :=
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).1 ‹_› S hS
  { exact := h.1, mono_f := h.2, epi_g := hg }

end Main

/-- **Right acyclicity in a short exact sequence**, [StacksProject 015D].
Let `F : 𝒜 ⥤ ℬ` be a left exact functor between abelian categories, where `𝒜` has enough
injectives, so that `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined, and let
`S : 0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence of `𝒜`. Then
1. if `A` and `C` are right acyclic for `F`, so is `B`,
2. if `A` and `B` are right acyclic for `F`, so is `C`, and
3. if `B` and `C` are right acyclic for `F` and `F(B) ⟶ F(C)` is epi, then so is `A`,
and in each of the three cases `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is a short exact sequence of `ℬ`. -/
@[stacks 015D]
public theorem rightAcyclic_and_shortExact_map_of_shortExact
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (F.rightAcyclic S.X₁ → F.rightAcyclic S.X₃ →
        F.rightAcyclic S.X₂ ∧ (S.map F).ShortExact) ∧
      (F.rightAcyclic S.X₁ → F.rightAcyclic S.X₂ →
        F.rightAcyclic S.X₃ ∧ (S.map F).ShortExact) ∧
      (F.rightAcyclic S.X₂ → F.rightAcyclic S.X₃ → Epi (F.map S.g) →
        F.rightAcyclic S.X₁ ∧ (S.map F).ShortExact) := by
  -- [Stacks, Tag 015C] part (2): for a left exact `F`, right acyclicity of `A` is the
  -- vanishing of `R ⁱ F(A)` in positive degrees.
  have hac := fun A : C ↦ (rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F A).2 ‹_›
  refine ⟨fun h₁ h₃ ↦ ⟨(hac _).2 fun i hi ↦
      isZero_rightDerivedPlus_X₂ F hS i ((hac _).1 h₁ i hi) ((hac _).1 h₃ i hi),
      shortExact_map F hS (epi_map_g F hS ((hac _).1 h₁ 1 one_pos))⟩,
    fun h₁ h₂ ↦ ⟨(hac _).2 fun i hi ↦
      isZero_rightDerivedPlus_X₃ F hS i ((hac _).1 h₂ i hi)
        ((hac _).1 h₁ (i + 1) (hi.trans (lt_add_one i))),
      shortExact_map F hS (epi_map_g F hS ((hac _).1 h₁ 1 one_pos))⟩,
    fun h₂ h₃ hg ↦ ⟨(hac _).2 fun i hi ↦ ?_, shortExact_map F hS hg⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, (Int.sub_add_cancel i 1).symm⟩
  exact isZero_rightDerivedPlus_X₁ F hS n
    (epi_rightDerivedPlus_map_g F hS hg ((hac _).1 h₃) n (Int.lt_add_one_iff.mp hi))
    ((hac _).1 h₂ _ hi)

section StupidTrunc

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c') (e : c.Embedding c')

public lemma isZero_stupidTrunc_X_of_isZero [e.IsRelIff] (i' : ι') (h : IsZero (K.X i')) :
    IsZero ((K.stupidTrunc e).X i') := by
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    exact h.of_iso (K.stupidTruncXIso e hi)
  · exact K.isZero_stupidTrunc_X e i' (by simpa using hi')

end StupidTrunc

section StupidTruncCochain

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  (K : CochainComplex A ℤ) (n : ℤ)

public lemma embeddingUpIntGE_f' (p : ℤ) (k : ℕ) : (embeddingUpIntGE p).f k = p + (k : ℤ) := rfl

public lemma embeddingUpIntLE_f' (p : ℤ) (k : ℕ) : (embeddingUpIntLE p).f k = p - (k : ℤ) := rfl

/-- The stupid truncations of a cochain complex form a short exact sequence
`0 → σ_{≥ n + 1}K ⟶ K ⟶ σ_{≤ n}K → 0`, [Stacks, Tag 0118]. It is termwise split, see
`stupidTruncSplitting`, hence gives a distinguished triangle of `K(A)` through
`CochainComplex.trianglehOfDegreewiseSplit`. -/
@[ega "III 7.9.6" "partial"]
public noncomputable def stupidTruncShortComplex : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (ιStupidTrunc K (embeddingUpIntGE (n + 1)))
    (πStupidTrunc K (embeddingUpIntLE n)) (by
      ext i'
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
      by_cases hi' : ∃ i : ℕ, (embeddingUpIntGE (n + 1)).f i = i'
      · obtain ⟨i, hi⟩ := hi'
        refine (K.isZero_stupidTrunc_X (embeddingUpIntLE n) i' ?_).eq_of_tgt _ _
        rw [notMem_range_embeddingUpIntLE_iff, ← hi, embeddingUpIntGE_f']
        omega
      · exact (K.isZero_stupidTrunc_X (embeddingUpIntGE (n + 1)) i'
          (by simpa using hi')).eq_of_src _ _)

/-- The short exact sequence of stupid truncations is termwise split: in a degree `> n` its
first map is an isomorphism and its last term is zero, and in a degree `≤ n` its first term is
zero and its last map is an isomorphism. -/
public noncomputable def stupidTruncSplitting (i' : ℤ) :
    (((stupidTruncShortComplex K n).map (HomologicalComplex.eval A _ i')).Splitting) := by
  by_cases h : n < i'
  · exact ShortComplex.Splitting.ofIsIsoOfIsZero _
      (isIso_ιStupidTrunc_f K (embeddingUpIntGE (n + 1)) (i := (i' - (n + 1)).toNat)
        (by rw [embeddingUpIntGE_f']; omega))
      (K.isZero_stupidTrunc_X (embeddingUpIntLE n) i'
        (by rw [notMem_range_embeddingUpIntLE_iff]; omega))
  · exact ShortComplex.Splitting.ofIsZeroOfIsIso _
      (K.isZero_stupidTrunc_X (embeddingUpIntGE (n + 1)) i'
        (by rw [notMem_range_embeddingUpIntGE_iff]; omega))
      (isIso_πStupidTrunc_f K (embeddingUpIntLE n) (i := (n - i').toNat)
        (by rw [embeddingUpIntLE_f']; omega))

public lemma isStrictlyGE_stupidTruncGE :
    CochainComplex.IsStrictlyGE (K.stupidTrunc (embeddingUpIntGE n)) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine K.isZero_stupidTrunc_X (embeddingUpIntGE n) i ?_
  rw [notMem_range_embeddingUpIntGE_iff]
  omega

private lemma isStrictlyLE_stupidTruncLE :
    CochainComplex.IsStrictlyLE (K.stupidTrunc (embeddingUpIntLE n)) n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine K.isZero_stupidTrunc_X (embeddingUpIntLE n) i ?_
  rw [notMem_range_embeddingUpIntLE_iff]
  omega

end StupidTruncCochain

section StupidTruncTriangle

open HomologicalComplex ComplexShape Pretriangulated

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A] [HasBinaryBiproducts A]
  (K : CochainComplex A ℤ) (n : ℤ)

/-- The triangle `(σ_{≥ n + 1}K, K, σ_{≤ n}K)` of `K(A)` attached to the termwise split short
exact sequence of stupid truncations `stupidTruncShortComplex`. -/
public noncomputable def stupidTruncTriangleh :
    Triangle (HomotopyCategory A (ComplexShape.up ℤ)) :=
  CochainComplex.trianglehOfDegreewiseSplit
    (stupidTruncShortComplex K n) (stupidTruncSplitting K n)

/-- The triangle of stupid truncations is distinguished in `K(A)`: a termwise split short exact
sequence of cochain complexes gives a distinguished triangle of the homotopy category,
[Stacks, Tag 0118] and `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`. -/
@[sga "4½ Etat_0 1.2.4" "special case"]
public lemma stupidTruncTriangleh_distinguished :
    stupidTruncTriangleh K n ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
    ⟨_, _, ⟨Iso.refl _⟩⟩

end StupidTruncTriangle

section StupidTruncPlus

open HomologicalComplex ComplexShape Pretriangulated

variable {A : Type*} [Category* A] [Abelian A] (K : CochainComplex A ℤ) (n : ℤ)

public lemma plus_stupidTruncGE (m : ℤ) :
    CochainComplex.plus A (K.stupidTrunc (embeddingUpIntGE m)) :=
  ⟨m, isStrictlyGE_stupidTruncGE K m⟩

public lemma plus_stupidTruncLE (hK : CochainComplex.plus A K) (m : ℤ) :
    CochainComplex.plus A (K.stupidTrunc (embeddingUpIntLE m)) := by
  obtain ⟨b, hb⟩ := hK
  refine ⟨b, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦ ?_⟩
  exact isZero_stupidTrunc_X_of_isZero K _ i ((CochainComplex.isStrictlyGE_iff K b).1 hb i hi)

/-- The object `σ_{≥ n + 1}K` of `K⁺(A)`. -/
public noncomputable abbrev plusTruncGE : HomotopyCategory.Plus A :=
  plusObj (K.stupidTrunc (embeddingUpIntGE (n + 1))) (plus_stupidTruncGE K (n + 1))

/-- The object `σ_{≤ n}K` of `K⁺(A)`, for `K` bounded below. -/
public noncomputable abbrev plusTruncLE (hK : CochainComplex.plus A K) : HomotopyCategory.Plus A :=
  plusObj (K.stupidTrunc (embeddingUpIntLE n)) (plus_stupidTruncLE K hK n)

/-- The triangle `(σ_{≥ n + 1}K, K, σ_{≤ n}K)` of `K⁺(A)` attached to the termwise split short
exact sequence of stupid truncations of a bounded below complex. Its image under the inclusion
`K⁺(A) ⥤ K(A)` is `stupidTruncTriangleh`, up to the commutation of that inclusion with the
shift. -/
public noncomputable def stupidTruncTrianglehPlus (hK : CochainComplex.plus A K) :
    Triangle (HomotopyCategory.Plus A) :=
  Triangle.mk
    (ObjectProperty.homMk (X := plusTruncGE K n) (Y := plusObj K hK)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (ιStupidTrunc K (embeddingUpIntGE (n + 1)))))
    (ObjectProperty.homMk (X := plusObj K hK) (Y := plusTruncLE K n hK)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (πStupidTrunc K (embeddingUpIntLE n))))
    (ObjectProperty.homMk (X := plusTruncLE K n hK) (Y := (plusTruncGE K n)⟦(1 : ℤ)⟧)
      ((stupidTruncTriangleh K n).mor₃ ≫
        ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app (plusTruncGE K n)))

/-- The triangle of stupid truncations of a bounded below complex is distinguished in `K⁺(A)`:
it is distinguished in `K(A)` and the inclusion `K⁺(A) ⥤ K(A)` is fully faithful and
triangulated, so `CategoryTheory.Functor.map_distinguished_iff` applies. -/
public lemma stupidTruncTrianglehPlus_distinguished (hK : CochainComplex.plus A K) :
    stupidTruncTrianglehPlus K n hK ∈ distTriang (HomotopyCategory.Plus A) := by
  rw [← Functor.map_distinguished_iff (HomotopyCategory.Plus.ι A)]
  refine isomorphic_distinguished _ (stupidTruncTriangleh_distinguished K n) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h : (shiftFunctor (HomotopyCategory A (up ℤ)) (1 : ℤ)).map
        (Iso.refl (((HomotopyCategory.Plus.ι A).mapTriangle.obj
          (stupidTruncTrianglehPlus K n hK)).obj₁)).hom = 𝟙 _ := by simp
    have h₂ : ((stupidTruncTriangleh K n).mor₃ ≫
        ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).inv.app (plusTruncGE K n)) ≫
        ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ)).hom.app (plusTruncGE K n) =
        (stupidTruncTriangleh K n).mor₃ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun g ↦ (stupidTruncTriangleh K n).mor₃ ≫ g)
          (Iso.inv_hom_id_app ((HomotopyCategory.Plus.ι A).commShiftIso (1 : ℤ))
            (plusTruncGE K n))).trans (Category.comp_id _))
    exact (congrArg (fun g ↦ ((HomotopyCategory.Plus.ι A).mapTriangle.obj
        (stupidTruncTrianglehPlus K n hK)).mor₃ ≫ g) h).trans
      ((Category.comp_id _).trans (h₂.trans (Category.id_comp _).symm))

public lemma isZero_stupidTruncGE_X_of_lt (m i : ℤ) (hi : i < m) :
    IsZero ((K.stupidTrunc (embeddingUpIntGE m)).X i) := by
  have := isStrictlyGE_stupidTruncGE K m
  exact CochainComplex.isZero_of_isStrictlyGE _ m i hi

public lemma isZero_stupidTruncLE_X_of_lt (m i : ℤ) (hi : m < i) :
    IsZero ((K.stupidTrunc (embeddingUpIntLE m)).X i) := by
  have := isStrictlyLE_stupidTruncLE K m
  exact CochainComplex.isZero_of_isStrictlyLE _ m i hi

end StupidTruncPlus

section SingleComplex

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [Abelian A]

/-- A cochain complex whose terms vanish outside one degree `a` is isomorphic to the one-term
complex on its degree-`a` term. -/
public noncomputable def isoSingleFunctorObj (L : CochainComplex A ℤ) (a : ℤ)
    (hL : ∀ i, i ≠ a → IsZero (L.X i)) :
    L ≅ (CochainComplex.singleFunctor A a).obj (L.X a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ if hi : i = a then
        eqToIso (by rw [hi]) ≪≫
          (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) a (L.X a) i hi).symm
      else
        (hL i hi).isoZero ≪≫
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a
            (L.X a) i hi).isoZero.symm)
    (fun i j hij ↦ by
      by_cases hi : i = a
      · refine (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (L.X a) j
          ?_).eq_of_tgt _ _
        simp only [ComplexShape.up_Rel] at hij
        omega
      · exact (hL i hi).eq_of_src _ _)

/-- A bounded below cochain complex whose terms vanish outside one degree `a` gives, in `K⁺(A)`,
the object `(singleFunctor A a).obj (L.X a)`. -/
public noncomputable def isoSingleFunctorObjPlus (L : CochainComplex A ℤ)
    (hL' : CochainComplex.plus A L) (a : ℤ) (hL : ∀ i, i ≠ a → IsZero (L.X i)) :
    plusObj L hL' ≅ (HomotopyCategory.Plus.singleFunctor A a).obj (L.X a) :=
  (HomotopyCategory.Plus.ι A).preimageIso
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapIso (isoSingleFunctorObj L a hL) ≪≫
      eqToIso (HomotopyCategory.quotient_obj_singleFunctors_obj A a (L.X a)) ≪≫
      ((HomotopyCategory.Plus.singleFunctorCompιIso A a).app (L.X a)).symm)

end SingleComplex

section Triangulated

open Pretriangulated

variable {C H : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* H] [HasShift H ℤ] [Preadditive H] [HasZeroObject H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]
  (Φ : HomotopyCategory.Plus C ⥤ H) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (RF : DerivedCategory.Plus C ⥤ H) (α : Φ ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [RF.CommShift ℤ] [NatTrans.CommShift α ℤ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit `α` of a right derived functor, read at a triangle `T` of `K⁺(𝒜)` as a morphism of
triangles from `Φ(T)` to `RF(Qh(T))`. Its three components are the components of `α`, and the
third square commutes because `α` commutes with the shift. -/
private noncomputable def mapTriangleHom (T : Triangle (HomotopyCategory.Plus C)) :
    Φ.mapTriangle.obj T ⟶ (DerivedCategory.Plus.Qh ⋙ RF).mapTriangle.obj T where
  hom₁ := α.app T.obj₁
  hom₂ := α.app T.obj₂
  hom₃ := α.app T.obj₃
  comm₁ := by simp
  comm₂ := by simp
  comm₃ := by
    simp [NatTrans.shift_app_comm, ← dsimp% α.naturality_assoc,
      -NatTrans.naturality_assoc]

/-- Two out of three: if the unit `α` of a right derived functor is invertible at the two outer
objects of a distinguished triangle of `K⁺(𝒜)`, it is invertible at the middle one. This is
[Stacks, Tag 05SZ] for the unit of the Kan extension; `α` is a morphism between the images of
the triangle under `Φ` and under `Qh ⋙ RF`, both distinguished. -/
private lemma isIso_app₂_of_distTriang [RF.IsTriangulated]
    (T : Triangle (HomotopyCategory.Plus C)) (hT : T ∈ distTriang (HomotopyCategory.Plus C))
    (h₁ : IsIso (α.app T.obj₁)) (h₃ : IsIso (α.app T.obj₃)) :
    IsIso (α.app T.obj₂) :=
  isIso₂_of_isIso₁₃ (mapTriangleHom Φ RF α T) (Φ.map_distinguished T hT)
    ((DerivedCategory.Plus.Qh ⋙ RF).map_distinguished T hT) h₁ h₃

omit [Preadditive H] [HasZeroObject H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H] [Φ.IsTriangulated] in
/-- **The comparison of the two long exact sequences.** Let `G` be any functor out of `ℋ` and let
`T` be a triangle of `K⁺(𝒜)`. If `G` sends the second maps of `Φ(T)` and of `RF(Qh(T))` to
isomorphisms and `α` to an isomorphism at `T.obj₃`, then it sends `α` to an isomorphism at
`T.obj₂`: the middle square of `mapTriangleHom` expresses `G(α_{T.obj₂})` composed with an
isomorphism as a composition of isomorphisms. -/
private lemma isIso_map_app₂ {E : Type*} [Category* E] (G : H ⥤ E)
    (T : Triangle (HomotopyCategory.Plus C))
    (h₁ : IsIso (G.map (Φ.mapTriangle.obj T).mor₂))
    (h₂ : IsIso (G.map ((DerivedCategory.Plus.Qh ⋙ RF).mapTriangle.obj T).mor₂))
    (h₃ : IsIso (G.map (α.app T.obj₃))) :
    IsIso (G.map (α.app T.obj₂)) := by
  have key : G.map (Φ.mapTriangle.obj T).mor₂ ≫ G.map ((mapTriangleHom Φ RF α T).hom₃) =
      G.map ((mapTriangleHom Φ RF α T).hom₂) ≫
        G.map ((DerivedCategory.Plus.Qh ⋙ RF).mapTriangle.obj T).mor₂ := by
    rw [← G.map_comp, ← G.map_comp, (mapTriangleHom Φ RF α T).comm₂]
  have h₃' : IsIso (G.map ((mapTriangleHom Φ RF α T).hom₃)) := h₃
  have : IsIso (G.map ((mapTriangleHom Φ RF α T).hom₂) ≫
      G.map ((DerivedCategory.Plus.Qh ⋙ RF).mapTriangle.obj T).mor₂) := by
    rw [← key]; infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    (G.map ((DerivedCategory.Plus.Qh ⋙ RF).mapTriangle.obj T).mor₂) h₂ this

omit [Preadditive H] [HasZeroObject H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [Pretriangulated H] [Φ.IsTriangulated] in
/-- Right acyclicity is invariant under shifts: the unit `α` of a right derived functor is
invertible at `X⟦n⟧` as soon as it is invertible at `X`, because it commutes with the shift
(`CategoryTheory.NatTrans.app_shift`). -/
private lemma isIso_app_shift (X : HomotopyCategory.Plus C) (n : ℤ) (hX : IsIso (α.app X)) :
    IsIso (α.app (X⟦n⟧)) := by
  rw [NatTrans.app_shift α n X]
  infer_instance

end Triangulated

section ZeroObject

/-- A natural transformation between functors preserving zero morphisms is invertible at a zero
object: both values are zero objects, and the zero morphism is inverse to any morphism between
zero objects. -/
public lemma isIso_app_of_isZero {J K : Type*} [Category* J] [Category* K]
    [HasZeroMorphisms J] [HasZeroMorphisms K] {G H : J ⥤ K} [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] (β : G ⟶ H) {X : J} (hX : IsZero X) : IsIso (β.app X) :=
  ⟨0, (G.map_isZero hX).eq_of_src _ _, (H.map_isZero hX).eq_of_src _ _⟩

end ZeroObject

section Leray

open Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)]
  [((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated]

omit [((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated] in
/-- **A complex with at most one nonzero right `F`-acyclic object computes `RF`.** By definition
([Stacks, Tag 0157]) a right `F`-acyclic object `A` is one at which `α` is invertible on `A[0]`;
the complex with `A` placed in degree `n` is the shift `A[0]⟦-n⟧`, where `α` is again invertible
by `isIso_app_shift`. -/
private lemma isIso_app_singleFunctor_obj (A : C) (hA : F.rightAcyclic A) (n : ℤ) :
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
      ((HomotopyCategory.Plus.singleFunctor C n).obj A)) := by
  rw [← NatTrans.isIso_app_iff_of_iso _
    (((HomotopyCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by simp)).app A)]
  exact isIso_app_shift _ _ _ _ (-n) hA

/-- A zero object is right acyclic for `F`: the one-term complex on it is a zero object of
`K⁺(𝒜)`, where the unit of a right derived functor is invertible. -/
private lemma rightAcyclic_of_isZero {A : C} (hA : IsZero A) : F.rightAcyclic A :=
  isIso_app_of_isZero _ ((HomotopyCategory.Plus.singleFunctor C 0).map_isZero hA)

omit [((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated] in
/-- Right acyclicity is invariant under isomorphism. -/
private lemma rightAcyclic_of_iso {A B : C} (e : A ≅ B) (hA : F.rightAcyclic A) :
    F.rightAcyclic B :=
  (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.Plus.singleFunctor C 0).mapIso e)).1 hA

/-- The terms of a stupid truncation of a complex of right acyclic objects are right acyclic:
each is either a term of the complex or a zero object. -/
private lemma rightAcyclic_stupidTrunc {ι : Type*} {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] (K : CochainComplex C ℤ)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) (n : ℤ) :
    F.rightAcyclic ((K.stupidTrunc e).X n) := by
  by_cases hn : ∃ i, e.f i = n
  · obtain ⟨i, hi⟩ := hn
    exact rightAcyclic_of_iso F (K.stupidTruncXIso e hi).symm (hacyclic n)
  · exact rightAcyclic_of_isZero F (K.isZero_stupidTrunc_X e n (by simpa using hn))

omit [((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated] in
/-- **A single degree, for a complex rather than a single object.** A bounded below complex whose
terms vanish outside one degree `a` and whose degree-`a` term is right acyclic computes `RF`: it
is isomorphic in `K⁺(𝒜)` to the one-term complex on that term. -/
private lemma isIso_app_of_isZero_ne (L : CochainComplex C ℤ) (hL' : CochainComplex.plus C L)
    (a : ℤ) (hL : ∀ i, i ≠ a → IsZero (L.X i)) (hacyclic : F.rightAcyclic (L.X a)) :
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app (plusObj L hL')) :=
  (NatTrans.isIso_app_iff_of_iso _ (isoSingleFunctorObjPlus L hL' a hL)).2
    (isIso_app_singleFunctor_obj F (L.X a) hacyclic a)

/-- The induction for the bounded case, on the number `m` of degrees the complex occupies: a
complex of right acyclic objects vanishing outside `[a, a + m]` computes `RF`. The step splits
`K` by the distinguished triangle `(σ_{≥ a + 1}K, K, σ_{≤ a}K)` of `stupidTruncTrianglehPlus`,
whose first object occupies `[a + 1, a + 1 + m]` and whose third occupies the single degree
`a`. -/
private lemma isIso_app_of_isZero_outside_aux (m : ℕ) : ∀ (a : ℤ) (K : CochainComplex C ℤ)
    (hK : CochainComplex.plus C K), (∀ i, (i < a ∨ a + m < i) → IsZero (K.X i)) →
    (∀ i, F.rightAcyclic (K.X i)) →
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app (plusObj K hK)) := by
  induction m with
  | zero =>
    intro a K hK hab hacyclic
    refine isIso_app_of_isZero_ne F K hK a (fun i hi ↦ hab i ?_) (hacyclic a)
    rcases lt_or_gt_of_ne hi with h | h
    · exact Or.inl h
    · exact Or.inr (by push_cast; omega)
  | succ m ih =>
    intro a K hK hab hacyclic
    have h₁ : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app (plusTruncGE K a)) := by
      refine ih (a + 1) _ (plus_stupidTruncGE K (a + 1)) (fun i hi ↦ ?_)
        (fun i ↦ rightAcyclic_stupidTrunc F _ K hacyclic i)
      rcases hi with hi | hi
      · exact isZero_stupidTruncGE_X_of_lt K (a + 1) i hi
      · exact isZero_stupidTrunc_X_of_isZero K _ i
          (hab i (Or.inr (by push_cast at hi ⊢; omega)))
    have h₃ : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
        (plusTruncLE K a hK)) := by
      refine isIso_app_of_isZero_ne F _ (plus_stupidTruncLE K hK a) a (fun i hi ↦ ?_)
        (rightAcyclic_stupidTrunc F _ K hacyclic a)
      rcases lt_or_gt_of_ne hi with h | h
      · exact isZero_stupidTrunc_X_of_isZero K _ i (hab i (Or.inl h))
      · exact isZero_stupidTruncLE_X_of_lt K a i h
    exact isIso_app₂_of_distTriang _ _ _ (stupidTruncTrianglehPlus K a hK)
      (stupidTruncTrianglehPlus_distinguished K a hK) h₁ h₃

/-- **The bounded case of Leray's acyclicity lemma.** A complex of right `F`-acyclic objects
which vanishes outside the degrees `[a, b]` computes `RF`. The proof is the induction on `b - a`
along the distinguished triangle `(σ_{≥ a + 1}K, K, σ_{≤ a}K)` of a stupid truncation, whose
outer objects are handled by `isIso_app_singleFunctor_obj` and the induction hypothesis and whose
middle object then follows by `isIso_app₂_of_distTriang`; that induction is
`isIso_app_of_isZero_outside_aux`. The base case is a complex with one nonzero term `A` in a
degree `n`, where `α` is invertible because it is at `A[0]` by hypothesis and it commutes with
the shift (`Functor.IsRightDerivedFunctor.natTrans_commShift`, `SingleFunctors.shiftIso`). -/
private lemma isIso_app_of_isZero_outside (K : CochainComplex C ℤ)
    (hK : CochainComplex.plus C K) (a b : ℤ) (hab : ∀ n, (n < a ∨ b < n) → IsZero (K.X n))
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
      ((HomotopyCategory.Plus.quotient C).obj ⟨K, hK⟩)) := by
  refine isIso_app_of_isZero_outside_aux F (b - a).toNat a K hK (fun i hi ↦ hab i ?_) hacyclic
  rcases hi with hi | hi
  · exact Or.inl hi
  · exact Or.inr (by omega)

omit [HasDerivedCategory C]
  [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)]
  [((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated] in
/-- `Φ = Qh ∘ F` carries a bounded below complex lying in degrees `≥ m` to an object of `D⁺(ℬ)`
which is `≥ m`, because `F` is additive and therefore kills the vanishing terms. -/
lemma isGE_Phi_obj (L : CochainComplex C ℤ) (hL : CochainComplex.plus C L) (m : ℤ)
    (hm : CochainComplex.IsStrictlyGE L m) :
    (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).obj (plusObj L hL)).IsGE m := by
  have := hm
  have hFm : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) m := inferInstance
  exact isGE_Qh_obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ⟨m, hFm⟩ m hFm

/-- If the first object of a distinguished triangle of `D⁺(ℬ)` lies in degrees `≥ i + 2`, then the
second map of the triangle is an isomorphism on `H ⁱ`: in the long exact sequence of the
homological functor `H ⁱ` the two neighbours of `H ⁱ(T.obj₂) ⟶ H ⁱ(T.obj₃)` are `H ⁱ(T.obj₁)` and
`H ⁱ⁺¹(T.obj₁)`, and both vanish, so the map is a mono and an epi. -/
private lemma isIso_homologyFunctor_map_mor₂ (T : Triangle (DerivedCategory.Plus D))
    (hT : T ∈ distTriang (DerivedCategory.Plus D)) (i : ℤ) (h : T.obj₁.IsGE (i + 1 + 1)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor D i).map T.mor₂) := by
  have := h
  have hz₀ : IsZero ((DerivedCategory.Plus.homologyFunctor D i).obj T.obj₁) :=
    DerivedCategory.Plus.isZero_homology_of_isGE T.obj₁ (i + 1 + 1) i (by omega)
  have hz₁ : IsZero ((DerivedCategory.Plus.homologyFunctor D (i + 1)).obj T.obj₁) :=
    DerivedCategory.Plus.isZero_homology_of_isGE T.obj₁ (i + 1 + 1) (i + 1) (by omega)
  have hmono : Mono ((DerivedCategory.Plus.homologyFunctor D i).map T.mor₂) :=
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_mono_shift_map_mor₂_iff
      T hT i).2 (hz₀.eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.Plus.homologyFunctor D i).map T.mor₂) :=
    ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 (hz₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **The bounded below case of Leray's acyclicity lemma.** A bounded below complex of right
`F`-acyclic objects computes `RF`. The proof compares, for each `i`, the triangle `(σ_{≥ i + 2}K,
K, σ_{≤ i + 1}K)` with its image under `RF`: the middle comparison is an isomorphism on `H ⁱ`
because the comparison at `σ_{≤ i + 1}K` is an isomorphism (`isIso_app_of_isZero_outside`) while
`H ⁱ` and `H ⁱ⁺¹` vanish on `σ_{≥ i + 2}F(K)` by inspection and on `RF(σ_{≥ i + 2}K)` by the
hypothesis `hGE` that `RF` moves cohomology to the right. A morphism of `D⁺(ℬ)` which is an
isomorphism on every `H ⁱ` is an isomorphism (`DerivedCategory.Plus.isIso_iff`), which is how the
comparison in each degree is assembled. -/
lemma isIso_app_of_plus
    (hGE : ∀ (L : CochainComplex C ℤ) (hL : CochainComplex.plus C L) (a : ℤ),
      CochainComplex.IsStrictlyGE L a →
        (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).obj
          (DerivedCategory.Plus.Qh.obj (plusObj L hL))).IsGE a)
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
      ((HomotopyCategory.Plus.quotient C).obj ⟨K, hK⟩)) := by
  have hb : ∃ b, CochainComplex.IsStrictlyGE K b := hK
  obtain ⟨b, hb⟩ := hb
  refine (DerivedCategory.Plus.isIso_iff _).2 fun i ↦ ?_
  have hT := stupidTruncTrianglehPlus_distinguished K (i + 1) hK
  have hgeGE : CochainComplex.IsStrictlyGE
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (i + 1 + 1))) (i + 1 + 1) :=
    isStrictlyGE_stupidTruncGE K (i + 1 + 1)
  -- `H ⁱ` of the second map of `Φ(T)` is an isomorphism, since `Φ(σ_{≥ i + 2}K)` is `≥ i + 2`
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).mapTriangle.obj
        (stupidTruncTrianglehPlus K (i + 1) hK)).mor₂) :=
    isIso_homologyFunctor_map_mor₂ _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map_distinguished _ hT) i
      (isGE_Phi_obj F _ (plus_stupidTruncGE K (i + 1 + 1)) (i + 1 + 1) hgeGE)
  -- and likewise for `RF(Qh(T))`, since `RF` moves cohomology to the right
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      ((DerivedCategory.Plus.Qh ⋙ (F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso C)).mapTriangle.obj
        (stupidTruncTrianglehPlus K (i + 1) hK)).mor₂) :=
    isIso_homologyFunctor_map_mor₂ _
      ((DerivedCategory.Plus.Qh ⋙ (F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso C)).map_distinguished _ hT) i
      (hGE _ (plus_stupidTruncGE K (i + 1 + 1)) (i + 1 + 1) hgeGE)
  -- the comparison at `σ_{≤ i + 1}K` is an isomorphism, by the bounded case
  have h₃ : IsIso ((DerivedCategory.Plus.homologyFunctor D i).map
      (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
        (plusTruncLE K (i + 1) hK))) := by
    have hLE : IsIso (((F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso C)).app (plusTruncLE K (i + 1) hK)) := by
      refine isIso_app_of_isZero_outside F _ (plus_stupidTruncLE K hK (i + 1)) b (i + 1)
        (fun n hn ↦ ?_) (fun n ↦ rightAcyclic_stupidTrunc F _ K hacyclic n)
      rcases hn with hn | hn
      · exact isZero_stupidTrunc_X_of_isZero K _ n
          ((CochainComplex.isStrictlyGE_iff K b).1 hb n hn)
      · exact isZero_stupidTruncLE_X_of_lt K (i + 1) n hn
    exact inferInstance
  exact isIso_map_app₂ _ _ _ (DerivedCategory.Plus.homologyFunctor D i) _ h₁ h₂ h₃

end Leray

section LerayEnoughInjectives

open Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is triangulated, [Stacks, Tag 0159]. -/
private lemma isTriangulated_totalRightDerived :
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).IsTriangulated :=
  isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F _
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))

/-- **[Stacks, Tag 05TC](1) for the unit of the Kan extension.** `RF` moves cohomology to the
right: if `X` is `≥ a`, so is `RF(X)`.

Indeed `X` is isomorphic to the image of a cochain complex `L` of injective objects lying in
degrees `≥ a` (`DerivedCategory.Plus.exists_injective_nonempty_iso`), the unit of the right
derived functor is an isomorphism on the image of such a complex, so `RF(X)` is the image of the
complex obtained by applying `F` termwise to `L`, and that complex again lies in degrees `≥ a`. -/
lemma isGE_rightDerivedFunctorPlus_obj (Y : DerivedCategory.Plus C) (a : ℤ) [Y.IsGE a] :
    (F.rightDerivedFunctorPlus.obj Y).IsGE a := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  have hN : (F.mapCochainComplexPlus.obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)).obj.IsStrictlyGE a := by
    show CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
      (((InjectiveObject.ι C).mapHomologicalComplex _).obj L.obj)) a
    infer_instance
  have hiso : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj L))) := by
    have : ∀ (i : ℤ), Injective (((HomotopyCategory.Plus.quotient C).obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)).obj.as.X i) := fun _ ↦ inferInstance
    infer_instance
  have h₁ := isGE_Q_obj (F.mapCochainComplexPlus.obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj L)) a
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    ((qhQuotientIso (F.mapCochainComplexPlus.obj
        ((InjectiveObject.ι C).mapCochainComplexPlus.obj L))).symm ≪≫
      @asIso _ _ _ _ _ hiso ≪≫
      F.rightDerivedFunctorPlus.mapIso
        (qhQuotientIso ((InjectiveObject.ι C).mapCochainComplexPlus.obj L) ≪≫ e)) a

/-- `RF` moves cohomology to the right, for the unit of the Kan extension as it is spelled in the
statement of Leray's acyclicity lemma. -/
private lemma isGE_totalRightDerived_obj (X : DerivedCategory.Plus C) (a : ℤ) [X.IsGE a] :
    (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).obj X).IsGE a := by
  have h := isGE_rightDerivedFunctorPlus_obj F X a
  unfold rightDerivedFunctorPlus at h
  exact h

end LerayEnoughInjectives

/-- **Leray's acyclicity lemma**, [StacksProject 015E].
Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives, so that the right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, with unit `α`, is everywhere
defined. Let `K` be a bounded below cochain complex of `𝒜` all of whose terms are right acyclic
for `F`. Then `K` computes `RF`: the canonical map `F(K) ⟶ RF(K)`, the component of `α` at the
image of `K` in `K⁺(𝒜)`, is an isomorphism in `D⁺(ℬ)`. -/
@[stacks 015E, sga "4 XVII 1.2.7" "enough injectives (RF)"]
public theorem isIso_totalRightDerivedUnit_app_of_rightAcyclic
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]
    (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K)
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
      ((HomotopyCategory.Plus.quotient C).obj ⟨K, hK⟩)) :=
  have := isTriangulated_totalRightDerived F
  isIso_app_of_plus F (fun L hL a ha ↦
    have := isGE_Qh_obj L hL a ha
    isGE_totalRightDerived_obj F _ a) K hK hacyclic

end CategoryTheory.Functor

end
