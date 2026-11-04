module

public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing

/-!
# Degree-zero Čech homology and gluing

`StacksFrontier.CategoryTheory.Sites.CechComplex` builds the augmentation `aug U P hT` of the Čech
complex of a family `U : ι → C` out of the sections over a terminal object presented by an
`IsTerminal` witness `hT`, together with its fork `augFork U P hT` and the identification
`homologyZeroIso` of degree-zero homology with the sections over that terminal object.

This file adds the homological bookkeeping behind that identification: a kernel of the first
differential of a cochain complex in an abelian category *is* its degree-zero homology, by a unique
isomorphism compatible with the canonical monomorphism out of homology
(`existsUnique_homologyMap_of_isKernel`), and the Čech instance of this
(`existsUnique_augHomologyMap`).

It also contains the element-level gluing lemma for a sheaf of abelian groups on a topological
space, `existsUnique_glue`, with **no constraint between the universe of the space and the universe
of the coefficients**.

## Main results

* `homologyZeroKernel`: the degree-zero homology of a cochain complex is a kernel of the first
  differential.
* `existsUnique_homologyMap_of_isKernel`: conversely, any kernel of the first differential is
  degree-zero homology, by a unique isomorphism compatible with the inclusion of cycles into
  opcycles.
* `existsUnique_augHomologyMap`: the Čech case, with the kernel given by the augmentation.
* `existsUnique_glue`: a compatible family of sections of a sheaf of abelian groups over a family
  of opens covering `W` has a unique gluing over `W`.

## Implementation notes

**`existsUnique_glue` deliberately avoids `TopCat.Sheaf.existsUnique_gluing'`.** That lemma is
stated for a sheaf valued in a concrete category and needs
`HasLimitsOfSize.{uX, uX} AddCommGrpCat.{uM}` together with the corresponding
`PreservesLimitsOfSize` for the forgetful functor, i.e. `UnivLE.{uX, uM}`: a constraint between the
universe of the space and the universe of the coefficients that nothing else in this material
carries. `CategoryTheory.Presheaf.IsSheaf.existsUnique_amalgamation_ofArrows` has no such
constraint — its index type and its target category are both arbitrary — and the passage from
morphisms out of the free abelian group on one generator to elements is exactly
`Stacks.Cohomology.Basis.ofElt`. So the gluing is proved through the site-theoretic amalgamation
and is universe-polymorphic in the index type of the covering family.

The compatibility hypothesis of `existsUnique_glue` is phrased over an arbitrary open contained in
two members of the family, rather than over their intersection, because that is the shape
`existsUnique_amalgamation_ofArrows` consumes and because the lattice of opens makes the two
equivalent.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_eq_apply ofElt ofElt_apply ofElt_comp
  eq_of_ofElt hom_ext_of_ulift_int)

universe w v v' u u' uX uM

namespace Stacks.Cohomology.CechZero

noncomputable section

/-! ### Degree-zero homology of a cochain complex as a kernel -/

section Homology

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℕ)

/-- The degree-`0` cycles compose to zero with the first differential. -/
theorem isoHomologyπ₀_inv_iCycles_comp_d :
    (K.isoHomologyπ₀.inv ≫ K.iCycles 0) ≫ K.d 0 1 = 0 := by
  simp

/-- The degree-`0` homology inclusion factors the cycles through the opcycles. -/
theorem homologyZeroKernel_arrow :
    (K.isoHomologyπ₀.inv ≫ K.iCycles 0) ≫ K.pOpcycles 0 = K.homologyι 0 := by
  rw [← cancel_epi (K.homologyπ 0)]
  simp only [Category.assoc, K.homology_π_ι]
  simp

/-- The degree-`0` homology of a cochain complex is a kernel of the first differential. -/
def homologyZeroKernel :
    IsLimit (KernelFork.ofι (K.isoHomologyπ₀.inv ≫ K.iCycles 0)
      (isoHomologyπ₀_inv_iCycles_comp_d K)) :=
  IsKernel.isoKernel (K.d 0 1) (K.isoHomologyπ₀.inv ≫ K.iCycles 0)
    (K.cyclesIsKernel (i := 0) (j := 1) (by simp))
    K.isoHomologyπ₀.symm (by simp)

/-- **A kernel of the first differential is degree-zero homology.** If `r : E ⟶ K.X 0` is a kernel
of `K.d 0 1`, then there is a unique isomorphism `E ≅ K.homology 0` whose composite with the
canonical monomorphism out of homology is `r` followed by the projection to opcycles. -/
theorem existsUnique_homologyMap_of_isKernel {E : A} (r : E ⟶ K.X 0) (w : r ≫ K.d 0 1 = 0)
    (hr : IsLimit (KernelFork.ofι r w)) :
    ∃! f : E ⟶ K.homology 0, IsIso f ∧ f ≫ K.homologyι 0 = r ≫ K.pOpcycles 0 := by
  let e := hr.conePointUniqueUpToIso (homologyZeroKernel K)
  have he : e.hom ≫ (K.isoHomologyπ₀.inv ≫ K.iCycles 0) = r := by
    simpa only [Fork.app_zero_eq_ι, KernelFork.ι_ofι] using
      hr.conePointUniqueUpToIso_hom_comp (homologyZeroKernel K) WalkingParallelPair.zero
  have hcomp : e.hom ≫ K.homologyι 0 = r ≫ K.pOpcycles 0 := by
    rw [← homologyZeroKernel_arrow, ← Category.assoc, he]
  exact ⟨e.hom, ⟨inferInstance, hcomp⟩, fun g hg ↦
    (cancel_mono (K.homologyι 0)).mp (hg.2.trans hcomp.symm)⟩

end Homology

/-! ### Degree-zero homology of the Čech complex -/

section AugHomology

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [Abelian A]
  [HasProducts.{w} A] [HasFiniteProducts C]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A) {T : C} (hT : IsTerminal T)

/-- **`H⁰` of the Čech complex, with its characterization.** The unique isomorphism from the
sections over the terminal object to degree-`0` Čech homology compatible with the canonical
monomorphism out of homology. -/
theorem existsUnique_augHomologyMap (h : IsLimit (augFork U P hT)) :
    ∃! f : P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).homology 0,
      IsIso f ∧ f ≫ ((cechComplexFunctor U).obj P).homologyι 0 =
        aug U P hT ≫ ((cechComplexFunctor U).obj P).pOpcycles 0 :=
  existsUnique_homologyMap_of_isKernel _ (aug U P hT) (aug_comp_d U P hT) h

end AugHomology

/-! ### Gluing sections of a sheaf of abelian groups -/

section Glue

variable {X : Type uX} [TopologicalSpace X]

/-- The sieve generated by a family of opens covering `W` is a covering sieve of `W`. -/
theorem ofArrows_mem_grothendieckTopology {κ : Type*} (B : κ → Opens X) (W : Opens X)
    (hBW : ∀ k, B k ≤ W) (hcov : W ≤ ⨆ k, B k) :
    Sieve.ofArrows B (fun k ↦ homOfLE (hBW k)) ∈ Opens.grothendieckTopology X W :=
  (Opens.mem_grothendieckTopology X).2 fun x hx ↦ by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hcov hx)
    exact ⟨B k, homOfLE (hBW k), Sieve.ofArrows_mk B _ k, hk⟩

variable (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{uM})
  (hF : Presheaf.IsSheaf (Opens.grothendieckTopology X) F)
  {κ : Type*} (B : κ → Opens X) (W : Opens X) (hBW : ∀ k, B k ≤ W) (hcov : W ≤ ⨆ k, B k)

include hF hcov in
/-- **Unique gluing for a sheaf of abelian groups**, with the index type of the covering family in
an arbitrary universe. A family of sections over the members of a family of opens covering `W`,
any two of which agree on every open contained in both, has a unique gluing over `W`. -/
theorem existsUnique_glue (t : ∀ k, ToType (F.obj (op (B k))))
    (hcompat : ∀ (O : Opens X) (k l : κ) (h₁ : O ≤ B k) (h₂ : O ≤ B l),
      res F h₁ (t k) = res F h₂ (t l)) :
    ∃! s : ToType (F.obj (op W)), ∀ k, res F (hBW k) s = t k := by
  obtain ⟨g, hg, hguniq⟩ := hF.existsUnique_amalgamation_ofArrows
    (fun k ↦ homOfLE (hBW k))
    (ofArrows_mem_grothendieckTopology B W hBW hcov)
    (fun k ↦ ofElt (t k))
    (fun {O} {k l} a b _ ↦ by
      rw [ofElt_comp, ofElt_comp, res_eq_apply, res_eq_apply,
        hcompat O k l (leOfHom a) (leOfHom b)])
  refine ⟨ConcreteCategory.hom g (ULift.up 1), fun k ↦ ?_, fun s hs ↦ ?_⟩
  · have hk : ConcreteCategory.hom (g ≫ F.map (homOfLE (hBW k)).op) (ULift.up 1) = t k := by
      rw [hg k, ofElt_apply]
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans hk
  · have hgs : ofElt s = g := hguniq (ofElt s) fun k ↦ by
      rw [ofElt_comp]
      exact congrArg ofElt (hs k)
    rw [← hgs, ofElt_apply]

include hF hcov in
/-- **A section of a sheaf of abelian groups is determined by its restrictions to a covering
family**, with the index type of the family in an arbitrary universe. -/
theorem eq_of_res_eq (s s' : ToType (F.obj (op W)))
    (h : ∀ k, res F (hBW k) s = res F (hBW k) s') : s = s' := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_glue F hF B W hBW hcov (fun k ↦ res F (hBW k) s)
    (fun O k l h₁ h₂ ↦ by rw [res_res, res_res])
  exact (huniq s fun _ ↦ rfl).trans (huniq s' fun k ↦ (h k).symm).symm

end Glue

end

end Stacks.Cohomology.CechZero

end
