module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional

/-!
# The defining ideals of the scheme-theoretic union and intersection

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`Y, Z ⊆ X` be closed subspaces with defining ideal sheaves `𝓘_Y, 𝓘_Z ⊆ 𝒪_X` of Stacks 03MB.
Stacks 0CYZ describes the scheme-theoretic intersection and union of `Y` and `Z` as the closed
subspaces cut out by `𝓘_Y + 𝓘_Z` and by `𝓘_Y ∩ 𝓘_Z`; in this library they are defined instead by
their universal properties in the lattice of closed subspaces, as the intersection of the two
subfunctors and as the smallest closed subspace containing both.  This file proves that the two
descriptions agree:

`𝓘_{Y ∩ Z} = 𝓘_Y ⊔ 𝓘_Z` and `𝓘_{Y ∪ Z} = 𝓘_Y ⊓ 𝓘_Z`.

Both are deduced from the bijection of Stacks 03MB between the closed subspaces of `X` and the
quasi-coherent sheaves of ideals of `𝒪_X`, which is
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite` together with
`AlgebraicGeometry.Space.le_of_definingIdealSheaf_le`.  One containment of each is free from
inclusion-reversal; the other needs the sheaf of ideals on the right-hand side to cut out a
closed subspace at all, that is, to be quasi-coherent.  For the meet that is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`, which identifies the meet with a fibre
product; for the join it is proved here, by identifying the join with a kernel.

## Main results

* `AlgebraicGeometry.Space.le_ker_iff_ι_comp_eq_zero`: a submodule is contained in the kernel of
  a morphism exactly when the composite of its inclusion with that morphism vanishes.
* `AlgebraicGeometry.Space.ker_cokernel_π_ι`: a submodule is the kernel of the projection onto
  the quotient by it.
* `AlgebraicGeometry.Space.ι_comp_eq_zero_of_ker_eq` and
  `AlgebraicGeometry.Space.isLimitKernelFork_of_ker_eq`: a submodule which is the kernel
  submodule of a morphism is annihilated by it, and its inclusion is a kernel of it.
* `AlgebraicGeometry.Space.sumProjection` and
  `AlgebraicGeometry.Space.sup_eq_ker_sumProjection`: **the join of two submodules is their
  sum**, exhibited as the kernel of the two-step projection onto the quotient by that sum.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealSup`: **the sum of two quasi-coherent
  sheaves of ideals of `𝒪_X` is quasi-coherent.**
* `AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticUnion` and
  `AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticIntersection`: **the defining ideal
  sheaf of the scheme-theoretic union is the meet of the two defining ideal sheaves, and that of
  the scheme-theoretic intersection is their join.**

## Implementation notes

`AlgebraicGeometry.Space.le_ker_iff_ι_comp_eq_zero` is the only statement here proved on
sections; everything after it is deduced from it, from the cokernel universal property and from
`CategoryTheory.Abelian.monoLift`, so no local description of the join of two submodules is ever
used.  That matters because the join of `SheafOfModules.Submodule`s is not computed
sectionwise: `⊓` is the sectionwise intersection, by
`SheafOfModules.Submodule.toSubmodule_inf`, but `⊔` is only characterized as the least sheaf
submodule containing both, the sectionwise sum of two sheaf submodules not being a sheaf
submodule.

The lemmas about the submodule lattice are stated for the modules on the small étale ringed site of
an algebraic space rather than for sheaves of modules over an arbitrary sheaf of rings on an
arbitrary site, which is where they would belong.  The reason is the diamond recorded in the
implementation notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiImageSubsheaf.lean`:
`SheafOfModules` carries a global `Preadditive` instance, so an `Abelian (SheafOfModules.{v} R)`
taken as a hypothesis has a preadditive part that is equal but not syntactically equal to it, and
then neither `HasCokernel` nor `HasBinaryBiproduct` is found by instance search — the generic
statements do not even elaborate.  On the small étale ringed site the abelian structure is
`SheafOfModules.instAbelian` at the module universe `u`, and in
`AlgebraicGeometry.Space.ker_cokernel_π_ι` it is introduced as a local instance by that term rather
than left to instance search: at a goal phrased through `AlgebraicGeometry.Space.Modules` the
search produces it at an unsolved module universe and `CategoryTheory.Abelian.monoLift` then does
not elaborate, whereas the term with the pinned expected type does.

The module universe is the universe `u` of the schemes, as everywhere in this part of the tree:
`SheafOfModules.unit` of a `RingCat.{u}`-valued sheaf of rings has its sections in `Type u`, and
the abelian structure of `AlgebraicGeometry.Space.Modules` is only available at a module universe
comparable with `u`.  The two closure results fed to the join are the unconditional
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, both of which are
`theorem`s rather than instances and are therefore introduced with `haveI`.

## References

* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Kernels, cokernels and the submodule lattice -/

section Lattice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {M N : Modules.{u, u} B S hS F hF}

/-- **A submodule is contained in the kernel of a morphism exactly when the composite of its
inclusion with that morphism vanishes.**  Both directions are read off on sections: the inclusion
of a submodule carries a section to itself, and membership in the kernel is the vanishing of the
image. -/
theorem le_ker_iff_ι_comp_eq_zero (P : M.Submodule) (f : M ⟶ N) :
    P ≤ SheafOfModules.Submodule.ker f ↔ P.ι ≫ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h A x hx ↦ ?_⟩
  · ext A x
    exact h A x.2
  · refine (SheafOfModules.Submodule.mem_ker f A x).2 ?_
    rw [show PresheafOfModules.Hom.app f.val A x =
        PresheafOfModules.Hom.app (P.ι ≫ f).val A
          (⟨x, hx⟩ : P.toSheafOfModules.val.obj A) from rfl, h]
    rfl

/-- A submodule is contained in the kernel of the projection onto the quotient by it. -/
theorem le_ker_cokernel_π_ι (P : M.Submodule) :
    P ≤ SheafOfModules.Submodule.ker (cokernel.π P.ι) :=
  (le_ker_iff_ι_comp_eq_zero B S hS F hF P _).2 (cokernel.condition P.ι)

/-- **A submodule is the kernel of the projection onto the quotient by it.**

One containment is `AlgebraicGeometry.Space.le_ker_cokernel_π_ι`.  For the other, the inclusion
of that kernel is annihilated by the projection onto the quotient, so it factors through the
monomorphism `P.ι` by `CategoryTheory.Abelian.monoLift`, and on sections the factorization
exhibits every section of the kernel as a section of `P`. -/
theorem ker_cokernel_π_ι (P : M.Submodule) :
    SheafOfModules.Submodule.ker (cokernel.π P.ι) = P := by
  let : Abelian (Modules.{u, u} B S hS F hF) := SheafOfModules.instAbelian _
  refine le_antisymm (fun A x hx ↦ ?_) (le_ker_cokernel_π_ι B S hS F hF P)
  have hzero : (SheafOfModules.Submodule.ker (cokernel.π P.ι)).ι ≫ cokernel.π P.ι = 0 :=
    SheafOfModules.Submodule.ker_ι_comp _
  have hfac := Abelian.monoLift_comp P.ι
    ((SheafOfModules.Submodule.ker (cokernel.π P.ι)).ι) hzero
  have hval : PresheafOfModules.Hom.app
      (Abelian.monoLift P.ι ((SheafOfModules.Submodule.ker (cokernel.π P.ι)).ι) hzero ≫ P.ι).val
      A (⟨x, hx⟩ : (SheafOfModules.Submodule.ker (cokernel.π P.ι)).toSheafOfModules.val.obj A)
      = x := by
    rw [hfac]
    rfl
  exact hval ▸ (PresheafOfModules.Hom.app
    (Abelian.monoLift P.ι ((SheafOfModules.Submodule.ker (cokernel.π P.ι)).ι) hzero).val
    A ⟨x, hx⟩).2

/-- **A submodule equal to the kernel submodule of a morphism is annihilated by it.** -/
theorem ι_comp_eq_zero_of_ker_eq {P : M.Submodule} {f : M ⟶ N}
    (h : SheafOfModules.Submodule.ker f = P) : P.ι ≫ f = 0 := by
  subst h
  exact SheafOfModules.Submodule.ker_ι_comp f

/-- **A submodule equal to the kernel submodule of a morphism has its inclusion as a kernel of
that morphism.**  This is `SheafOfModules.Submodule.isLimitKernelFork` transported along the
equality, which is done by substitution rather than by rewriting inside the kernel fork. -/
def isLimitKernelFork_of_ker_eq {P : M.Submodule} {f : M ⟶ N}
    (h : SheafOfModules.Submodule.ker f = P) (hz : P.ι ≫ f = 0) :
    IsLimit (KernelFork.ofι P.ι hz) := by
  subst h
  exact SheafOfModules.Submodule.isLimitKernelFork f

/-- **The projection of a module onto the quotient by the sum of two submodules**, formed in two
steps: first the quotient by `N₁`, then the quotient of that by the image of `N₂`.

Forming it in two steps rather than as the cokernel of the map out of `N₁ ⊞ N₂` keeps binary
biproducts out of the statement; the two have the same target, since
`(M/N₁)/((N₁ + N₂)/N₁) = M/(N₁ + N₂)`. -/
def sumProjection (N₁ N₂ : M.Submodule) :
    M ⟶ cokernel (N₂.ι ≫ cokernel.π N₁.ι) :=
  cokernel.π N₁.ι ≫ cokernel.π (N₂.ι ≫ cokernel.π N₁.ι)

/-- **The join of two submodules is their sum**, exhibited as the kernel of the projection onto
the quotient by that sum.

Each of `N₁` and `N₂` is killed by the projection, so the join is contained in its kernel.  For
the reverse containment, the projection onto the quotient by the join kills `N₁` and then kills
the image of `N₂`, so it factors through the two-step projection; the kernel of the latter is
therefore contained in the kernel of the former, which by
`AlgebraicGeometry.Space.ker_cokernel_π_ι` is the join itself. -/
theorem sup_eq_ker_sumProjection (N₁ N₂ : M.Submodule) :
    N₁ ⊔ N₂ = SheafOfModules.Submodule.ker (sumProjection B S hS F hF N₁ N₂) := by
  have h₁ : N₁ ≤ SheafOfModules.Submodule.ker (sumProjection B S hS F hF N₁ N₂) := by
    refine (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).2 ?_
    rw [sumProjection, ← Category.assoc, cokernel.condition, zero_comp]
  have h₂ : N₂ ≤ SheafOfModules.Submodule.ker (sumProjection B S hS F hF N₁ N₂) := by
    refine (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).2 ?_
    rw [sumProjection, ← Category.assoc, cokernel.condition]
  refine le_antisymm (sup_le h₁ h₂) ?_
  have hd : ∀ P ≤ N₁ ⊔ N₂, P.ι ≫ cokernel.π (N₁ ⊔ N₂).ι = 0 := fun P hP ↦
    (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).1 (hP.trans (le_ker_cokernel_π_ι B S hS F hF _))
  have hd₁ := hd N₁ le_sup_left
  have hd₂ : (N₂.ι ≫ cokernel.π N₁.ι) ≫
      cokernel.desc N₁.ι (cokernel.π (N₁ ⊔ N₂).ι) hd₁ = 0 := by
    rw [Category.assoc, cokernel.π_desc]
    exact hd N₂ le_sup_right
  have hfac : sumProjection B S hS F hF N₁ N₂ ≫
      cokernel.desc (N₂.ι ≫ cokernel.π N₁.ι)
        (cokernel.desc N₁.ι (cokernel.π (N₁ ⊔ N₂).ι) hd₁) hd₂ =
      cokernel.π (N₁ ⊔ N₂).ι := by
    rw [sumProjection, Category.assoc, cokernel.π_desc, cokernel.π_desc]
  rw [← ker_cokernel_π_ι B S hS F hF (N₁ ⊔ N₂), ← hfac]
  refine (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).2 ?_
  rw [← Category.assoc, SheafOfModules.Submodule.ker_ι_comp, zero_comp]

/-- **The sum of two quasi-coherent submodules of a quasi-coherent module is quasi-coherent.**

By `AlgebraicGeometry.Space.sup_eq_ker_sumProjection` the sum is the kernel of the two-step
projection of `M` onto `(M/N₁)/N₂`.  That target is a cokernel of a morphism of quasi-coherent
modules, hence quasi-coherent, and the kernel of a morphism of quasi-coherent modules is
quasi-coherent.

This is the join counterpart of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_inf`, which identifies the meet with a fibre
product instead. -/
theorem isQuasicoherentOnSite_sup (hM : M.IsQuasicoherentOnSite) (N₁ N₂ : M.Submodule)
    (h₁ : N₁.toSheafOfModules.IsQuasicoherentOnSite)
    (h₂ : N₂.toSheafOfModules.IsQuasicoherentOnSite) :
    (N₁ ⊔ N₂).toSheafOfModules.IsQuasicoherentOnSite := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  let Q := SheafOfModules.isQuasicoherentOnSite
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  have hc₁ : (cokernel N₁.ι).IsQuasicoherentOnSite := ObjectProperty.prop_cokernel Q N₁.ι h₁ hM
  have hQ : (cokernel (N₂.ι ≫ cokernel.π N₁.ι)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_cokernel Q (N₂.ι ≫ cokernel.π N₁.ι) h₂ hc₁
  rw [sup_eq_ker_sumProjection B S hS F hF]
  exact ObjectProperty.prop_of_isLimit_kernelFork Q
    (SheafOfModules.Submodule.isLimitKernelFork (sumProjection B S hS F hF N₁ N₂)) hM hQ

end Lattice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-coherence of the sum of two ideal sheaves -/

section Quasicoherent

variable (X : AlgebraicSpaces B S hS)

/-- **The sum of two quasi-coherent sheaves of ideals of `𝒪_X` is quasi-coherent.**

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_sup` with the structure sheaf as the
ambient module, whose quasi-coherence is `SheafOfModules.isQuasicoherentOnSite_unit`.  Nothing is
assumed beyond quasi-coherence of the two sheaves of ideals.  It is the join counterpart of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_idealInf`. -/
theorem isQuasicoherentOnSite_idealSup
    (I₁ I₂ : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (h₁ : I₁.toSheafOfModules.IsQuasicoherentOnSite)
    (h₂ : I₂.toSheafOfModules.IsQuasicoherentOnSite) :
    (I₁ ⊔ I₂).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_sup B S hS X.1 X.2
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS X)) I₁ I₂ h₁ h₂

end Quasicoherent

/-! ### The defining ideals of the union and the intersection -/

section UnionIntersection

variable (X : AlgebraicSpaces B S hS) (Y Z : ClosedSubspaces B S hS X.1)

/-- **Stacks 0CYZ.** The defining ideal sheaf of the scheme-theoretic union of two closed
subspaces is the meet of their defining ideal sheaves.

One containment is inclusion-reversal.  For the other, the meet of the two ideal sheaves is
quasi-coherent, hence by Stacks 03MB cuts out a closed subspace `W`; that `W` contains both `Y`
and `Z` because its ideal is contained in each of theirs, so the scheme-theoretic union, being
the smallest closed subspace containing both, is contained in `W`, and inclusion-reversal gives
the containment of ideals back. -/
@[stacks 0CYZ "the defining ideal of the scheme-theoretic union is the meet of the two defining \
ideals"]
theorem definingIdealSheaf_schemeTheoreticUnion :
    definingIdealSheaf B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z) =
      definingIdealSheaf B S hS X Y ⊓ definingIdealSheaf B S hS X Z := by
  refine le_antisymm (le_inf
    (definingIdealSheaf_antitone B S hS X Y _ (le_schemeTheoreticUnion_left B S hS X.2 Y Z))
    (definingIdealSheaf_antitone B S hS X Z _ (le_schemeTheoreticUnion_right B S hS X.2 Y Z))) ?_
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (definingIdealSheaf B S hS X Y ⊓ definingIdealSheaf B S hS X Z)
    (isQuasicoherentOnSite_idealInf B S hS X _ _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y)
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z))
  have hYW : Y.1 ≤ W.1 :=
    le_of_definingIdealSheaf_le B S hS X Y W (hW.le.trans inf_le_left)
  have hZW : Z.1 ≤ W.1 :=
    le_of_definingIdealSheaf_le B S hS X Z W (hW.le.trans inf_le_right)
  have hle : (schemeTheoreticUnion B S hS X.1 X.2 Y Z).1 ≤ W.1 :=
    sInf_le ⟨W.2, hYW, hZW⟩
  exact hW ▸ definingIdealSheaf_antitone B S hS X _ W hle

/-- **Stacks 0CYZ.** The defining ideal sheaf of the scheme-theoretic intersection of two closed
subspaces is the sum of their defining ideal sheaves.

One containment is inclusion-reversal.  For the other, the sum of the two ideal sheaves is
quasi-coherent, hence by Stacks 03MB cuts out a closed subspace `W`; that `W` is contained in
both `Y` and `Z` because its ideal contains each of theirs, hence in their intersection, and
inclusion-reversal gives the containment of ideals back. -/
@[stacks 0CYZ "the defining ideal of the scheme-theoretic intersection is the sum of the two \
defining ideals"]
theorem definingIdealSheaf_schemeTheoreticIntersection :
    definingIdealSheaf B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) =
      definingIdealSheaf B S hS X Y ⊔ definingIdealSheaf B S hS X Z := by
  refine le_antisymm ?_ (sup_le
    (definingIdealSheaf_antitone B S hS X _ Y (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1))
    (definingIdealSheaf_antitone B S hS X _ Z (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1)))
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (definingIdealSheaf B S hS X Y ⊔ definingIdealSheaf B S hS X Z)
    (isQuasicoherentOnSite_idealSup B S hS X _ _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y)
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z))
  have hWY : W.1 ≤ Y.1 :=
    le_of_definingIdealSheaf_le B S hS X W Y (le_sup_left.trans hW.ge)
  have hWZ : W.1 ≤ Z.1 :=
    le_of_definingIdealSheaf_le B S hS X W Z (le_sup_right.trans hW.ge)
  exact hW ▸ definingIdealSheaf_antitone B S hS X W
    (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) (le_inf hWY hWZ)

end UnionIntersection

end AlgebraicGeometry.Space

end
