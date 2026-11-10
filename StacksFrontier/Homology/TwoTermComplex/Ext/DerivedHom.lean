module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.SuccPred.Int
public import Mathlib.Tactic.LinearCombination
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import StacksFrontier.Homology.TwoTermComplex.ProjRes
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

This is Stacks project Lemma 15.86.4, tag 0ALN ("Two term complexes", section
15.86 of *More on Algebra*).

Throughout, `R` is a (commutative, unital) ring and we work with cochain
complexes of `R`-modules indexed by `ℤ`, with differentials of degree `+1`.
For a complex `C` we write `d_C^i : C^i → C^{i+1}` for the differential.

The categorical setting:

1. Homotopy category `K(R)`: objects are cochain complexes of `R`-modules and
   morphisms are chain-homotopy classes of morphisms of complexes. In Mathlib
   this is `HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)`, with the
   quotient functor `HomotopyCategory.quotient`.
   `Hom_{K(R)}(A, B)` is the group of morphisms between the images of `A`, `B`
   under that quotient.

2. Derived category `D(R)`: the localization of `K(R)` at quasi-isomorphisms.
   In Mathlib this is `DerivedCategory (ModuleCat.{v} R)`. The localization functor
   `K(R) → D(R)` is `DerivedCategory.Qh`, and `DerivedCategory.Q` is the
   composite `CochainComplex → D(R)`. The canonical homomorphism
   `Hom_{K(R)}(A, B) → Hom_{D(R)}(A, B)` is `DerivedCategory.Qh.map`.

3. Shift functor: `(C[n])^i = C^{n+i}`, with `d_{C[n]}^i = (-1)^n d_C^{n+i}`.
   In Mathlib this is `C⟦n⟧`. An `R`-module `N` is regarded as the complex
   concentrated in degree `0`, so `N[n]` is `N` placed in degree `-n`. We model
   `N[n]` as `((single 0).obj N)⟦n⟧`; it is isomorphic, in `D(R)`, to the module
   `N` placed directly in degree `-n`, i.e. `(single (-n)).obj N`.

4. Ext groups: for a complex `C`, a module `N`, and `j ∈ ℤ`,
   `Ext^j_R(C, N) := Hom_{D(R)}(C, N[j])`. A morphism of complexes
   `a : M → K` induces, by pre-composition in `D(R)`, the map
   `Ext^1_R(a, N) : Ext^1_R(K, N) → Ext^1_R(M, N)`, `ξ ↦ ξ ∘ a`.

5. Canonical map `K → K^{-2}[2]` (used in (3)): when `K^i = 0` for `i ≤ -3`,
   the module `K^{-2}` sits in degree `-2`; `K^{-2}[2]` is `K^{-2}` placed in
   degree `-2`, modelled here as `(single (-2)).obj (K^{-2})`. The canonical
   truncation map onto the lowest nonzero term is the morphism of complexes
   which is the identity in degree `-2` and zero in all other degrees.

The hypotheses of the lemma: `R` a ring, `M` a complex with `M^i = 0` for
`i > 0` and `M^0` projective; `K` a second complex.

Note on part (2)(b): the Stacks source has a typographical error; the intended
relation is `a^{-1} + h^0 ∘ d_M^{-1} = 0` with `h^0 : M^0 → K^{-1}` and
`d_M^{-1} : M^{-1} → M^0`. We adopt this corrected formula.

In Mathlib, composition `≫` is in diagrammatic (left-to-right) order, so the
mathematical composite `g ∘ f` is written `f ≫ g`.
-/

/-
## Contents of this file

This file holds the vocabulary that all four parts of the lemma share.

* `shiftSingle N j` is the complex `N[j]` of item 3, with `isZero_shiftSingle_X`,
  `shiftSingle_d_eq_zero` and `shiftSingleXSelf` describing its single nonzero term.
* `HomK` and `HomD` are the morphism groups of items 1 and 2, and `ExtMod` is the Ext
  group `Ext^j_R(C, N) = Hom_{D(R)}(C, N[j])` of item 4.
* `toHomD` is the canonical homomorphism `Hom_{K(C)}(M, K) → Hom_{D(C)}(M, K)`, together
  with its elementary properties (`toHomD_zero`, `toHomD_quotient_map`,
  `Q_map_comp_toHomD`) and the criterion `toHomD_bijective_of_Qh` for it to be bijective.
* `canonicalToSingleNegTwo` is the canonical truncation `K → K^{-2}[2]` of item 5, and
  `mkHomToSingleNegTwo` is the chain map `M → (single (-2)).obj A` determined by a module
  map out of `M^{-2}`.
* `exists_comp_eq_of_apply_eq_zero`, `exists_toCycles_eq_of_homologyπ_eq_zero` and
  `exists_d_apply_eq_of_isIso_homologyMap` are the module-theoretic descent lemmas — factor
  through a surjection, a cycle with vanishing class is a boundary, boundaries lift along a
  quasi-isomorphism — on which the degreewise descent arguments of every part rest.
-/

open CategoryTheory Limits

namespace TwoTermComplexExt

universe u v

variable {R : Type u} [Ring R] [Small.{v} R]
  [HasDerivedCategory (ModuleCat.{v} R)]

section Generic

variable {C : Type*} [Category C] [Abelian C]

/-- An object `N` regarded as `N[j]`: the complex `(single 0).obj N` shifted by `j`,
which places `N` in degree `-j`. -/
@[sga "4½ Fonctions_L 1.11", sga "4½ Fonctions_L 1.7.2" "special case"]
noncomputable def shiftSingle (N : C) (j : ℤ) : CochainComplex C ℤ :=
  ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj N)⟦j⟧

/-- `N[j]` is concentrated in degree `-j`: every other term vanishes. -/
theorem isZero_shiftSingle_X {N : C} {j i : ℤ} (h : i ≠ -j) :
    IsZero ((shiftSingle N j).X i) := by
  rw [shiftSingle, CochainComplex.shiftFunctor_obj_X']
  apply HomologicalComplex.isZero_single_obj_X
  omega

/-- All differentials of `N[j]` vanish, `N[j]` having a single nonzero term. -/
theorem shiftSingle_d_eq_zero (N : C) (j i i' : ℤ) :
    (shiftSingle N j).d i i' = 0 := by
  by_cases hi : i = -j
  · by_cases hi' : i' = -j
    · exact (shiftSingle N j).shape i i' (by simp only [ComplexShape.up_Rel]; omega)
    · exact (isZero_shiftSingle_X hi').eq_zero_of_tgt _
  · exact (isZero_shiftSingle_X hi).eq_zero_of_src _

/-- The degree `-j` term of `N[j]` is `N` itself. -/
noncomputable def shiftSingleXSelf (N : C) (j : ℤ) : (shiftSingle N j).X (-j) ≅ N :=
  eqToIso (by rw [shiftSingle, CochainComplex.shiftFunctor_obj_X']; norm_num) ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N

/-- `Hom_{K(C)}(M, K)`: morphisms in the homotopy category. -/
@[ega "0 20.6.26" "Morphism sets"]
abbrev HomK (M K : CochainComplex C ℤ) : Type _ :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M ⟶
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K

/-- The canonical truncation map `K → K^{-2}[2]` of Definition 5, modelled as the
morphism of complexes `K → (single (-2)).obj (K^{-2})` which is the identity in
degree `-2` and zero elsewhere. Requires `K^i = 0` for `i ≤ -3` so that the
relevant differential vanishes. -/
noncomputable def canonicalToSingleNegTwo (K : CochainComplex C ℤ)
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i)) :
    K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) (-2)).obj (K.X (-2)) :=
  HomologicalComplex.mkHomToSingle (𝟙 (K.X (-2))) (by
    intro i hi
    simp only [ComplexShape.up_Rel] at hi
    have hi3 : i = -3 := by omega
    subst hi3
    have hz : IsZero (K.X (-3)) := hK (-3) (by norm_num)
    have hd : K.d (-3) (-2) = 0 := hz.eq_zero_of_src _
    rw [hd]; simp)

/-- `canonicalToSingleNegTwo K hK` is the identity in degree `-2`. -/
@[simp] theorem canonicalToSingleNegTwo_f_neg_two (K : CochainComplex C ℤ)
    (hK : ∀ i ≤ (-3 : ℤ), IsZero (K.X i)) :
    (canonicalToSingleNegTwo K hK).f (-2)
      = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-2) (K.X (-2))).inv := by
  rw [canonicalToSingleNegTwo, HomologicalComplex.mkHomToSingle_f]
  simp

/-- The morphism of complexes `M ⟶ (single (-2)).obj A` determined by a map
`a : M^{-2} ⟶ A` which kills the incoming differential `d_M^{-3}`. -/
noncomputable def mkHomToSingleNegTwo {A : C}
    (M : CochainComplex C ℤ) (a : M.X (-2) ⟶ A)
    (ha : M.d (-3) (-2) ≫ a = 0) :
    M ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) (-2)).obj A :=
  HomologicalComplex.mkHomToSingle a (by
    intro i hi
    simp only [ComplexShape.up_Rel] at hi
    have hi3 : i = -3 := by omega
    subst hi3
    exact ha)

/-- `mkHomToSingleNegTwo M a ha` is `a` in degree `-2`. -/
@[simp] theorem mkHomToSingleNegTwo_f_neg_two {A : C}
    (M : CochainComplex C ℤ) (a : M.X (-2) ⟶ A)
    (ha : M.d (-3) (-2) ≫ a = 0) :
    (mkHomToSingleNegTwo M a ha).f (-2)
      = a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-2) A).inv := by
  rw [mkHomToSingleNegTwo, HomologicalComplex.mkHomToSingle_f]

variable [HasDerivedCategory C]

/-- `Hom_{D(C)}(M, K)`: morphisms in the derived category. -/
@[sga "4½ Etat_0 3.2.1" "Ext^0 of complexes"]
abbrev HomD (M K : CochainComplex C ℤ) : Type _ :=
  DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj K

/-- Mathlib's comparison isomorphism `Qh (M) ≅ Q M`, evaluated at the complex `M`: the
image of `M` in `D(C)` computed through `K(C)` agrees with `DerivedCategory.Q.obj M`. -/
noncomputable def qhQIso (M : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M) ≅
      DerivedCategory.Q.obj M :=
  (DerivedCategory.quotientCompQhIso C).app M

/-- The canonical homomorphism `Hom_{K(C)}(M, K) → Hom_{D(C)}(M, K)` induced by the
localization functor `Qh`: apply `Qh.map` and transport along `qhQIso`. -/
noncomputable def toHomD {M K : CochainComplex C ℤ} (f : HomK M K) : HomD M K :=
  Iso.homCongr (qhQIso M) (qhQIso K) (DerivedCategory.Qh.map f)

/-- `toHomD f` is the composite `(qhQIso M).inv ≫ Qh.map f ≫ (qhQIso K).hom`. -/
theorem toHomD_eq {M K : CochainComplex C ℤ} (f : HomK M K) :
    toHomD f = (qhQIso M).inv ≫ DerivedCategory.Qh.map f ≫ (qhQIso K).hom := rfl

/-- `toHomD` is `Qh.map` composed with a bijection, so it is bijective whenever
`Qh.map` is. -/
theorem toHomD_bijective_of_Qh {M K : CochainComplex C ℤ}
    (h : Function.Bijective (DerivedCategory.Qh.map : HomK M K → _)) :
    Function.Bijective (fun f : HomK M K => (toHomD f : HomD M K)) :=
  (Iso.homCongr (qhQIso M) (qhQIso K)).bijective.comp h

/-- `toHomD` sends the zero morphism of `K(C)` to the zero morphism of `D(C)`. -/
@[simp] theorem toHomD_zero {M K : CochainComplex C ℤ} :
    toHomD (0 : HomK M K) = 0 := by
  rw [toHomD_eq, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- On the homotopy class of an honest chain map, `toHomD` is just `Q.map`. -/
theorem toHomD_quotient_map {M K : CochainComplex C ℤ} (f : M ⟶ K) :
    toHomD ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)
      = DerivedCategory.Q.map f := by
  simp only [toHomD_eq, qhQIso, Iso.app_hom, Iso.app_inv]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality f]
  simp

/-- Naturality of `toHomD`: precomposing in `D(C)` with `Q.map a` is precomposing in
`K(C)` with the homotopy class `[a]`. -/
theorem Q_map_comp_toHomD {M K L : CochainComplex C ℤ} (a : M ⟶ K)
    (f : HomK K L) :
    DerivedCategory.Q.map a ≫ toHomD f
      = toHomD ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map a ≫ f) := by
  simp only [toHomD_eq, qhQIso, Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc a]

end Generic

/-- `Ext^j_R(C, N) = Hom_{D(R)}(C, N[j])`. -/
@[sga "4½ Etat_0 3.2.1" "Ext^j(C, special case", sga "7 VII 3.2" "special case"]
abbrev ExtMod (C : CochainComplex (ModuleCat.{v} R) ℤ) (N : ModuleCat.{v} R) (j : ℤ) : Type _ :=
  DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj (shiftSingle N j)

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- A module map `f : A ⟶ C` that kills the kernel of a surjection `p : A ⟶ B`
factors through `p`. -/
lemma exists_comp_eq_of_apply_eq_zero {A B C : ModuleCat.{v} R} (p : A ⟶ B) (f : A ⟶ C)
    (hp : Function.Surjective p) (hker : ∀ a : A, p a = 0 → f a = 0) :
    ∃ g : B ⟶ C, p ≫ g = f := by
  classical
  let e := LinearMap.quotKerEquivOfSurjective p.hom hp
  refine ⟨ModuleCat.ofHom ((Submodule.liftQ _ f.hom fun a ha => hker a ha).comp
    e.symm.toLinearMap), ?_⟩
  ext a
  change Submodule.liftQ _ f.hom (fun a ha => hker a ha) (e.symm (p.hom a)) = f.hom a
  rw [show e.symm (p.hom a) = Submodule.Quotient.mk a from e.symm_apply_eq.mpr rfl]
  rfl

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- A cycle whose homology class vanishes is a boundary. -/
lemma exists_toCycles_eq_of_homologyπ_eq_zero {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c)
    {i j : ι} (hij : c.prev j = i) (lc : C.cycles j)
    (h : C.homologyπ j lc = 0) : ∃ b : C.X i, C.toCycles i j b = lc :=
  (ShortComplex.moduleCat_exact_iff _).mp
    (ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk _ _ (C.toCycles_comp_homologyπ i j))
      (C.homologyIsCokernel i j hij)) lc h

/-- `iCycles` is injective on cycles of a complex of modules. -/
private lemma iCycles_injective {S : Type*} [Ring S] {ι : Type*}
    {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    Function.Injective (C.iCycles i) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The image of `toCycles b` in `C.X j` is `d b`. -/
private lemma iCycles_toCycles_apply {S : Type*} [Ring S] {ι : Type*}
    {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} S) c) (i j : ι) (b : C.X i) :
    C.iCycles j (C.toCycles i j b) = C.d i j b := by
  rw [← ModuleCat.comp_apply, C.toCycles_i]

omit [HasDerivedCategory (ModuleCat.{v} R)] [Small.{v, u} R] in
/-- If `φ` induces an iso on homology at degree `i`, then any cycle `x` at `i` whose
image `φ.f i x` is a boundary in the target is itself a boundary in the source. -/
lemma exists_d_apply_eq_of_isIso_homologyMap
    {C D : CochainComplex (ModuleCat.{v} R) ℤ} (φ : C ⟶ D) (i : ℤ)
    [IsIso (HomologicalComplex.homologyMap φ i)]
    (x : C.X i) (hxcyc : C.d i (i + 1) x = 0)
    (w : D.X (i - 1)) (hw : (HomologicalComplex.Hom.f φ i) x = D.d (i - 1) i w) :
    ∃ b : C.X (i-1), C.d (i-1) i b = x := by
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by simp
  -- `x` as a cycle of `C`.
  have hxcyc' : (ConcreteCategory.hom ((forget₂ (ModuleCat.{v} R) Ab).map (C.d i (i+1)))) x = 0 :=
    hxcyc
  let cx : C.cycles i := C.cyclesMk x (i+1) hnext hxcyc'
  have hcx : C.iCycles i cx = x := C.i_cyclesMk x (i+1) hnext hxcyc'
  -- The image cycle `cyclesMap φ i cx` has `iCycles = φ.f i x`, which is a boundary.
  have hcm : D.iCycles i (HomologicalComplex.cyclesMap φ i cx)
      = HomologicalComplex.Hom.f φ i (C.iCycles i cx) := by
    rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i]; rfl
  -- The homology class of `cx` maps to the class of a boundary, hence to `0`;
  -- since `homologyMap φ i` is mono, the class of `cx` is `0`.
  have hbdryD : ∀ (lc : D.cycles i) (b : D.X (i-1)),
      D.iCycles i lc = D.d (i-1) i b → D.homologyπ i lc = 0 := by
    intro lc b hlc
    have heq : lc = D.toCycles (i-1) i b :=
      iCycles_injective D i (by rw [hlc, iCycles_toCycles_apply])
    rw [heq, ← ModuleCat.comp_apply, D.toCycles_comp_homologyπ (i-1) i]
    rfl
  have himg0 : D.homologyπ i (HomologicalComplex.cyclesMap φ i cx) = 0 := by
    apply hbdryD _ w
    rw [hcm, hcx, hw]
  -- transport across the naturality square: `homologyMap φ i (homologyπ cx) = 0`.
  have hmap0 : HomologicalComplex.homologyMap φ i (C.homologyπ i cx) = 0 := by
    rw [← ModuleCat.comp_apply, HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply,
      himg0]
  -- `homologyMap φ i` is mono (it's an iso), so `homologyπ cx = 0`.
  have hmono : Function.Injective (HomologicalComplex.homologyMap φ i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcl0 : C.homologyπ i cx = 0 := hmono (by rw [hmap0, map_zero])
  obtain ⟨b, hb⟩ := exists_toCycles_eq_of_homologyπ_eq_zero C hprev cx hcl0
  -- `C.toCycles (i-1) i b = cx` ⟹ `C.d (i-1) i b = x`.
  exact ⟨b, by rw [← iCycles_toCycles_apply, hb, hcx]⟩

end TwoTermComplexExt
