module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDegreeZero.Augmentation

/-!
# Degree zero Čech cohomology of a sheaf

Let `U : ι → C` be a family of objects of a category `C` with finite products and let
`P : Cᵒᵖ ⥤ A` be a presheaf with values in a preadditive category with products of the
relevant size. `StacksFrontier/CategoryTheory/Sites/CechComplex.lean` builds the augmentation
`Stacks.Cohomology.CechZero.aug U P hT : P(T) ⟶ Č⁰(U, P)` of the Čech complex at a terminal
object `T` and identifies the degree `0` homology of the Čech complex with `P(T)` *under the
hypothesis* that the augmentation is a kernel of the first Čech differential. This file
discharges that hypothesis for `T = ⊤_ C`: it holds as soon as `P` is a sheaf for a
Grothendieck topology for which the family of morphisms `U i ⟶ ⊤_ C` generates a covering
sieve of the terminal object. So `Stacks.Cohomology.CechZero.homologyZeroIso` becomes
unconditional for a sheaf and a covering family. This is the degree `0` part of
[Stacks, Tag 01EP], in the generality of a presheaf category rather than for sheaves of modules
on a ringed space.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.interUnaryIso U i` identifies the unary product
  `inter U (fun _ ↦ i)` with `U i`.
* `Stacks.CategoryTheory.CechComplex.zeroComponent U P s i` is the `i`-th component of a
  degree `0` Čech cochain, a morphism into the sections of `P` over `U i`.

## Main results

* `Stacks.CategoryTheory.CechComplex.zeroComponent_compatible`: the components of a degree
  `0` Čech cocycle agree on every object mapping into two members of the family.
* `Stacks.CategoryTheory.CechComplex.isLimitAugmentationFork`: for a sheaf and a covering
  family of the terminal object, the augmentation is a kernel of the first Čech differential.
* `Stacks.CategoryTheory.CechComplex.homologyZeroIsoOfIsSheaf`: consequently the degree `0`
  homology of the Čech complex of a sheaf is the object of sections over the terminal object.
  This is the unconditional form of `Stacks.Cohomology.CechZero.homologyZeroIso`.
* `Stacks.CategoryTheory.CechComplex.existsUnique_isIso_homologyZero_of_isSheaf`: the same
  statement in the form that pins the isomorphism by the property characterising it, namely
  compatibility with the augmentation.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.CechZero (aug aug_comp_π_assoc aug_comp_d augFork homologyZeroIso)

universe w v v' u u'

namespace Stacks.CategoryTheory

namespace CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasFiniteProducts C] {ι : Type w} (U : ι → C)

/-! ### The unary intersections -/

/-- The unary product `inter U (fun _ ↦ i)` occurring in degree `0` of the Čech complex is
the member `U i` of the family. -/
noncomputable def interUnaryIso (i : ι) : inter U (fun _ : Fin 1 ↦ i) ≅ U i where
  hom := interπ U _ 0
  inv := interLift U fun _ ↦ 𝟙 (U i)
  hom_inv_id := inter_hom_ext U fun a ↦ by
    rw [Category.assoc, interLift_comp_interπ, Category.comp_id, Category.id_comp,
      Fin.fin_one_eq_zero a]
  inv_hom_id := interLift_comp_interπ U _ 0

/-- The inverse of `interUnaryIso U i` followed by any projection of the unary product is the
identity of `U i`. -/
@[simp]
theorem interUnaryIso_inv_comp_interπ (i : ι) (a : Fin 1) :
    (interUnaryIso U i).inv ≫ interπ U (fun _ ↦ i) a = 𝟙 (U i) := by
  rw [Fin.fin_one_eq_zero a]
  exact (interUnaryIso U i).inv_hom_id

/-! ### The components of a degree zero Čech cochain -/

section Components

variable [Preadditive A] (P : Cᵒᵖ ⥤ A)

/-- The `i`-th component of a degree `0` Čech cochain: project onto the factor of the
degree `0` term indexed by the constant tuple at `i`, then restrict along
`interUnaryIso U i`. -/
noncomputable def zeroComponent {E : A} (s : E ⟶ ((cechComplexFunctor U).obj P).X 0) (i : ι) :
    E ⟶ P.obj (op (U i)) :=
  s ≫ π U P 0 (fun _ ↦ i) ≫ P.map (interUnaryIso U i).inv.op

/-- Restricting the `i`-th component of a degree `0` Čech cochain along a morphism
`f : W ⟶ U i` is restricting the corresponding projection along
`f ≫ (interUnaryIso U i).inv`. -/
theorem zeroComponent_comp_map {E : A} (s : E ⟶ ((cechComplexFunctor U).obj P).X 0) (i : ι)
    {W : C} (f : W ⟶ U i) :
    zeroComponent U P s i ≫ P.map f.op =
      s ≫ π U P 0 (fun _ ↦ i) ≫ P.map (f ≫ (interUnaryIso U i).inv).op := by
  rw [zeroComponent, Category.assoc, Category.assoc, ← P.map_comp, ← op_comp]

/-- Two degree `0` Čech cochains with the same components agree: every tuple of length one
is the constant tuple at its only value. -/
theorem zeroComponent_ext {E : A} {f g : E ⟶ ((cechComplexFunctor U).obj P).X 0}
    (h : ∀ i, zeroComponent U P f i = zeroComponent U P g i) : f = g := by
  refine hom_ext U P fun x ↦ ?_
  rw [show x = fun _ ↦ x 0 from funext fun a ↦ congrArg x (Fin.fin_one_eq_zero a)]
  have hc := h (x 0)
  rw [zeroComponent, zeroComponent, ← Category.assoc, ← Category.assoc] at hc
  exact (cancel_mono (P.map (interUnaryIso U (x 0)).inv.op)).1 hc

/-- The components of the image of a section over the terminal object under the augmentation
are its restrictions to the members of the family. -/
@[simp]
theorem zeroComponent_augmentation {E : A} (f : E ⟶ P.obj (op (⊤_ C))) (i : ι) :
    zeroComponent U P (f ≫ aug U P terminalIsTerminal) i =
      f ≫ P.map (terminal.from (U i)).op := by
  rw [zeroComponent, Category.assoc, aug_comp_π_assoc, ← P.map_comp, ← op_comp,
    Subsingleton.elim ((interUnaryIso U i).inv ≫ terminalIsTerminal.from (inter U fun _ ↦ i))
      (terminal.from (U i))]

/-- **The components of a degree `0` Čech cocycle are compatible**, in the formulation with
the two indices and the two morphisms packaged as a function `y : Fin 2 → ι` and a dependent
family over it. -/
theorem zeroComponent_compatible_pair {E : A} (s : E ⟶ ((cechComplexFunctor U).obj P).X 0)
    (hs : s ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0) {W : C} (y : Fin 2 → ι)
    (c : ∀ k, W ⟶ U (y k)) :
    zeroComponent U P s (y 0) ≫ P.map (c 0).op =
      zeroComponent U P s (y 1) ≫ P.map (c 1).op := by
  have h0 : s ≫ (((cechComplexFunctor U).obj P).d 0 1 ≫ π U P 1 y) = 0 := by
    rw [← Category.assoc, hs, zero_comp]
  rw [d_zero_comp_π, Preadditive.comp_sub, sub_eq_zero] at h0
  have h1 := congrArg (fun g ↦ g ≫ P.map (interLift U c).op) h0
  simp only [Category.assoc, ← P.map_comp, ← op_comp] at h1
  have hk (k : Fin 2) :
      interLift U c ≫ interMap U y (fun _ ↦ k) = c k ≫ (interUnaryIso U (y k)).inv :=
    inter_hom_ext U fun a ↦ by
      rw [Category.assoc, interMap_comp_interπ, interLift_comp_interπ, Category.assoc]
      change c k = c k ≫ (interUnaryIso U (y k)).inv ≫ interπ U (fun _ ↦ y k) a
      rw [interUnaryIso_inv_comp_interπ, Category.comp_id]
  rw [zeroComponent_comp_map, zeroComponent_comp_map, ← hk 0, ← hk 1]
  exact h1.symm

/-- **The components of a degree `0` Čech cocycle are compatible.** Any two of them agree
after restriction along a pair of morphisms from a common object. -/
theorem zeroComponent_compatible {E : A} (s : E ⟶ ((cechComplexFunctor U).obj P).X 0)
    (hs : s ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0) {W : C} {i j : ι} (a : W ⟶ U i)
    (b : W ⟶ U j) :
    zeroComponent U P s i ≫ P.map a.op = zeroComponent U P s j ≫ P.map b.op :=
  zeroComponent_compatible_pair U P s hs (Fin.cons i fun _ ↦ j)
    (Fin.cons a (Fin.cons b fun k ↦ k.elim0))

/-! ### Degree zero Čech cohomology of a sheaf -/

/-- **The augmentation of the Čech complex of a sheaf is a kernel of the first Čech
differential.** A degree `0` cocycle is a compatible family of sections over the members of
the family, hence the restriction of a unique section over the terminal object. -/
noncomputable def isLimitAugmentationFork (J : GrothendieckTopology C)
    (hP : Presheaf.IsSheaf J P)
    (hU : Sieve.ofArrows U (fun i ↦ terminal.from (U i)) ∈ J (⊤_ C)) :
    IsLimit (augFork U P terminalIsTerminal) :=
  KernelFork.IsLimit.ofι (aug U P terminalIsTerminal) (aug_comp_d U P terminalIsTerminal)
    (fun s hs ↦ hP.amalgamateOfArrows (fun i ↦ terminal.from (U i)) hU (zeroComponent U P s)
      fun _ _ _ a b _ ↦ zeroComponent_compatible U P s hs a b)
    (fun s hs ↦ zeroComponent_ext U P fun i ↦ by
      rw [zeroComponent_augmentation, hP.amalgamateOfArrows_map])
    fun s hs m hm ↦ hP.hom_ext_ofArrows (fun i ↦ terminal.from (U i)) hU fun i ↦ by
      rw [hP.amalgamateOfArrows_map, ← zeroComponent_augmentation U P m i, hm]

/-- **`H⁰` of the Čech complex of a sheaf.** For a sheaf `P` and a family whose morphisms to
the terminal object generate a covering sieve, the degree `0` homology of the Čech complex is
the object of sections of `P` over the terminal object. This is `homologyZeroIso` with its
hypothesis discharged. -/
noncomputable def homologyZeroIsoOfIsSheaf [((cechComplexFunctor U).obj P).HasHomology 0]
    (J : GrothendieckTopology C) (hP : Presheaf.IsSheaf J P)
    (hU : Sieve.ofArrows U (fun i ↦ terminal.from (U i)) ∈ J (⊤_ C)) :
    ((cechComplexFunctor U).obj P).homology 0 ≅ P.obj (op (⊤_ C)) :=
  homologyZeroIso U P terminalIsTerminal (isLimitAugmentationFork U P J hP hU)

end Components

/-- **`H⁰` of the Čech complex of a sheaf, with the isomorphism pinned by the augmentation.**
There is a unique morphism from the sections over the terminal object to the degree `0` Čech
cohomology whose composite with the inclusion of the homology into the opcycles is induced by
the augmentation, and it is an isomorphism. This is the degree `0` half of
[Stacks, Tag 01EP], for an arbitrary sheaf on an arbitrary site and with no injectivity
hypothesis, in the generality of a presheaf category rather than for sheaves of modules on a
ringed space. -/
theorem existsUnique_isIso_homologyZero_of_isSheaf [Abelian A] (P : Cᵒᵖ ⥤ A)
    (J : GrothendieckTopology C) (hP : Presheaf.IsSheaf J P)
    (hU : Sieve.ofArrows U (fun i ↦ terminal.from (U i)) ∈ J (⊤_ C)) :
    ∃! f : P.obj (op (⊤_ C)) ⟶ ((cechComplexFunctor U).obj P).homology 0,
      IsIso f ∧ f ≫ ((cechComplexFunctor U).obj P).homologyι 0 =
        aug U P terminalIsTerminal ≫ ((cechComplexFunctor U).obj P).pOpcycles 0 :=
  Stacks.Cohomology.CechZero.existsUnique_homologyMap_of_isKernel _ (aug U P terminalIsTerminal)
    (aug_comp_d U P terminalIsTerminal) (isLimitAugmentationFork U P J hP hU)

end CechComplex

end Stacks.CategoryTheory

end
