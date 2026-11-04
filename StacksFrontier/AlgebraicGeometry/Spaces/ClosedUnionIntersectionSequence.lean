module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional

/-!
# The exact sequence of a scheme-theoretic union of two closed subspaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`Y, Z ⊆ X` be closed subspaces.  Let `Y ∪ Z` and `Y ∩ Z` be their scheme-theoretic union and
intersection, the closed subspaces of Stacks 0CYZ cut out by `𝓘_Y ∩ 𝓘_Z` and by `𝓘_Y + 𝓘_Z`.
The second assertion of Stacks 0CZ1 is that

`0 ⟶ 𝒪_{Y ∪ Z} ⟶ 𝒪_Y × 𝒪_Z ⟶ 𝒪_{Y ∩ Z} ⟶ 0`

is a short exact sequence, where the first map is built from the two canonical maps
`𝒪_{Y ∪ Z} ⟶ 𝒪_Y` and `𝒪_{Y ∪ Z} ⟶ 𝒪_Z` and the second from the canonical map
`𝒪_Y ⟶ 𝒪_{Y ∩ Z}` together with the *negative* of the canonical map `𝒪_Z ⟶ 𝒪_{Y ∩ Z}`.
This file proves it.

Following the proof of the tag, the four structure sheaves are regarded as modules on `X`
itself, by the equivalence of Stacks 04CJ between quasi-coherent modules on a closed subspace
and quasi-coherent modules on the ambient space annihilated by the defining ideal; concretely
`𝒪_W` means `AlgebraicGeometry.Space.pushforwardStructureSheaf`, the direct image `i_*𝒪_W`
along the inclusion `i : W ⟶ X`, and the sequence is a sequence of `𝒪_X`-modules.  (The tag
writes "of `𝒪_Z`-modules", which its own proof corrects: the modules it constructs by invoking
Stacks 04CJ live on `X`.)

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceRestriction`: for closed subspaces `W ⊆ W' ⊆ X`, the
  canonical map `i_*𝒪_{W'} ⟶ i_*𝒪_W` of `𝒪_X`-modules, characterized by compatibility with the
  structure projections of `W` and `W'` from `𝒪_X`.
* `AlgebraicGeometry.Space.unionToBiprodStructureSheaves` and
  `AlgebraicGeometry.Space.biprodStructureSheavesToIntersection`: the two maps of the sequence.
* `AlgebraicGeometry.Space.unionIntersectionShortComplex`: the sequence
  `𝒪_{Y ∪ Z} ⟶ 𝒪_Y ⊞ 𝒪_Z ⟶ 𝒪_{Y ∩ Z}` itself.

## Main results

* `AlgebraicGeometry.Space.structureProjection_comp_closedSubspaceRestriction` and
  `AlgebraicGeometry.Space.eq_closedSubspaceRestriction`: the canonical restriction map is the
  unique map compatible with the structure projections from `𝒪_X`.
* `AlgebraicGeometry.Space.ker_biprod_lift`: the kernel of a morphism into a biproduct is the
  meet of the kernels of its two components.
* `AlgebraicGeometry.Space.shortExact_biprod_of_ker_eq_inf_sup`: **the abstract form of the
  sequence.**  If `M ↠ QU`, `M ↠ QI`, `M ↠ QJ` and `M ↠ QV` are epimorphisms of `𝒪_X`-modules
  whose kernel submodules are `I ⊓ J`, `I`, `J` and `I ⊔ J`, then
  `0 ⟶ QU ⟶ QI ⊞ QJ ⟶ QV ⟶ 0` is short exact, the first map being the lift of the two
  comparison maps out of `QU` and the second the difference of the two comparison maps into
  `QV`.
* `AlgebraicGeometry.Space.unionIntersectionShortComplex_shortExact`: **Stacks 0CZ1, second
  assertion**, the short exact sequence of the union and the intersection.

## Implementation notes

The abstract form is where all the content sits, and it is proved with no local description of
either the meet or the join of two sheaves of submodules.  Write `πU, πI, πJ, πV` for the four
projections and `aI, aJ, bI, bJ` for the four comparison maps, so that `πU ≫ aI = πI` and
`πI ≫ bI = πV`, and write `f = biprod.lift aI aJ`, `g = biprod.desc bI (-bJ)`.

* `g` **is a cokernel of** `f`.  Given `t : QI ⊞ QJ ⟶ W` killed by `f`, the two composites
  `u = πI ≫ biprod.inl ≫ t` and `πJ ≫ biprod.inr ≫ t` add up to zero, so `u` is killed by
  `I.ι` because `I.ι ≫ πI = 0` and by `J.ι` because `J.ι ≫ πJ = 0`.  The universal property of
  the join then gives `(I ⊔ J).ι ≫ u = 0`, and `πV`, being an epimorphism whose kernel is
  `I ⊔ J`, is a cokernel of `(I ⊔ J).ι`, so `u` factors through it.  That factorization is the
  required map out of `QV`, and it is unique because `g` is an epimorphism.  This is the step
  the tag's proof performs étale locally; here the join is used only through
  `AlgebraicGeometry.Space.le_ker_iff_ι_comp_eq_zero` and `sup_le`, so no étale localization is
  needed.
* `f` **is a monomorphism.**  A morphism `z` killed by `f` is killed by `aI` and by `aJ`.
  Pulling `z` back along the epimorphism `πU` produces `q` with `q ≫ πI = 0` and
  `q ≫ πJ = 0`, hence `q ≫ biprod.lift πI πJ = 0`; the kernel submodule of that lift is
  `I ⊓ J` by `AlgebraicGeometry.Space.ker_biprod_lift`, so `q` factors through `(I ⊓ J).ι`,
  which `πU` kills.  Therefore `z` vanishes after composition with an epimorphism, so it
  vanishes.
* `g` **is an epimorphism** for free, being a cokernel projection.

The four hypotheses `Epi πU, …` are taken as plain arguments rather than as instances.  The
reason is the one recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealLattice.lean`: the module category of
the small étale ringed site has two spellings here, `AlgebraicGeometry.Space.Modules`, whose
category and topology are projections of the `RingedSite` structure, and
`SheafOfModules (structureRingSheaf …)`, whose category and topology are those of
`AlgebraicGeometry.Space.SmallEtale`.  The two are definitionally equal, and a *term* of one
type is accepted where the other is expected; but instance search does not unfold the
projections, so an `Epi` hypothesis obtained from
`AlgebraicGeometry.Space.epi_structureProjection`, which is stated in the second spelling, is
not found by instance search at a goal phrased in the first.  Passing it explicitly moves the
comparison to the definitional check of an application, which succeeds.  For the same reason
the identifications of the kernels are each proved in a standalone statement, phrased in the
spelling that `AlgebraicGeometry.Space.structureProjection` fixes, and then handed to the
abstract lemma: a `rewrite` inside a goal that mixes the two spellings fails, since rewriting
checks types at a reduced transparency.

## References

* [Stacks Project, Tag 0CZ1](https://stacks.math.columbia.edu/tag/0CZ1)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Quotients by a meet and by a join -/

section Lattice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The kernel of a morphism into a biproduct is the meet of the kernels of its two
components.**  Both containments are read off from
`AlgebraicGeometry.Space.le_ker_iff_ι_comp_eq_zero`: composing the inclusion of the kernel of
the lift with a projection of the biproduct gives one, and a submodule killed by both
components is killed by the lift by `CategoryTheory.Limits.biprod.hom_ext`. -/
theorem ker_biprod_lift {M N P : Modules.{u, u} B S hS F hF} (f : M ⟶ N) (g : M ⟶ P) :
    SheafOfModules.Submodule.ker (biprod.lift f g) =
      SheafOfModules.Submodule.ker f ⊓ SheafOfModules.Submodule.ker g := by
  have h0 := SheafOfModules.Submodule.ker_ι_comp (biprod.lift f g)
  refine le_antisymm (le_inf ?_ ?_) ?_
  · exact (le_ker_iff_ι_comp_eq_zero B S hS F hF _ f).2 (by simpa using h0 =≫ biprod.fst)
  · exact (le_ker_iff_ι_comp_eq_zero B S hS F hF _ g).2 (by simpa using h0 =≫ biprod.snd)
  · refine (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).2 ?_
    refine biprod.hom_ext _ _ ?_ ?_
    · simpa using (le_ker_iff_ι_comp_eq_zero B S hS F hF _ f).1 inf_le_left
    · simpa using (le_ker_iff_ι_comp_eq_zero B S hS F hF _ g).1 inf_le_right

/-- **The lift of the two comparison maps out of a quotient by a meet is a monomorphism.**

Let `πU : M ↠ QU` have kernel submodule `I ⊓ J` and let `πI : M ↠ QI` and `πJ : M ↠ QJ` have
kernel submodules `I` and `J`, with comparison maps `aI, aJ` out of `QU`.  A morphism `z` into
`QU` killed by `biprod.lift aI aJ` is killed by `aI` and by `aJ`; pulling it back along the
epimorphism `πU` gives a morphism into `M` killed by `πI` and by `πJ`, hence by
`biprod.lift πI πJ`, whose kernel submodule is `I ⊓ J` by
`AlgebraicGeometry.Space.ker_biprod_lift`.  So the pullback factors through `(I ⊓ J).ι`, which
`πU` kills, and `z` vanishes after composition with an epimorphism. -/
theorem mono_biprod_lift_of_ker_eq_inf {M QU QI QJ : Modules.{u, u} B S hS F hF}
    {I J : M.Submodule} (πU : M ⟶ QU) (πI : M ⟶ QI) (πJ : M ⟶ QJ) (hπU : Epi πU)
    (hU : SheafOfModules.Submodule.ker πU = I ⊓ J)
    (hI : SheafOfModules.Submodule.ker πI = I)
    (hJ : SheafOfModules.Submodule.ker πJ = J)
    (aI : QU ⟶ QI) (aJ : QU ⟶ QJ)
    (haI : πU ≫ aI = πI) (haJ : πU ≫ aJ = πJ) :
    Mono (biprod.lift aI aJ) := by
  have := hπU
  rw [Preadditive.mono_iff_cancel_zero]
  intro W z hz
  have hker : SheafOfModules.Submodule.ker (biprod.lift πI πJ) = I ⊓ J := by
    rw [ker_biprod_lift, hI, hJ]
  have hz0 : (I ⊓ J).ι ≫ biprod.lift πI πJ = 0 := ι_comp_eq_zero_of_ker_eq B S hS F hF hker
  have hfork := isLimitKernelFork_of_ker_eq B S hS F hF hker hz0
  have hpb : ∀ {Q : Modules.{u, u} B S hS F hF} (π' : M ⟶ Q) (a : QU ⟶ Q), πU ≫ a = π' →
      z ≫ a = 0 → pullback.fst πU z ≫ π' = 0 := by
    rintro Q π' a rfl h
    rw [← Category.assoc, pullback.condition, Category.assoc, h, comp_zero]
  have hq : pullback.fst πU z ≫ biprod.lift πI πJ = 0 :=
    biprod.hom_ext _ _ (by simpa using hpb _ _ haI (by simpa using hz =≫ biprod.fst))
      (by simpa using hpb _ _ haJ (by simpa using hz =≫ biprod.snd))
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hfork (pullback.fst πU z) hq
  have hlq : l ≫ (I ⊓ J).ι = pullback.fst πU z := hl
  have hιU : (I ⊓ J).ι ≫ πU = 0 := ι_comp_eq_zero_of_ker_eq B S hS F hF hU
  have hfin : pullback.snd πU z ≫ z = pullback.snd πU z ≫ 0 := by
    rw [comp_zero, ← pullback.condition, ← hlq, Category.assoc, hιU, comp_zero]
  exact (cancel_epi (pullback.snd πU z)).1 hfin

/-- **The two maps of the sequence compose to zero.**  Both composites of the quotient map by
the meet with a comparison map into the quotient by the join are the quotient map by the join,
so their difference vanishes; the projection out of the quotient by the meet is an epimorphism,
so the difference of the two comparison maps vanishes already before it. -/
theorem biprod_lift_comp_biprod_desc_eq_zero {M QU QI QJ QV : Modules.{u, u} B S hS F hF}
    (πU : M ⟶ QU) (πI : M ⟶ QI) (πJ : M ⟶ QJ) (πV : M ⟶ QV) (hπU : Epi πU)
    (aI : QU ⟶ QI) (aJ : QU ⟶ QJ) (bI : QI ⟶ QV) (bJ : QJ ⟶ QV)
    (haI : πU ≫ aI = πI) (haJ : πU ≫ aJ = πJ)
    (hbI : πI ≫ bI = πV) (hbJ : πJ ≫ bJ = πV) :
    biprod.lift aI aJ ≫ biprod.desc bI (-bJ) = 0 := by
  have := hπU
  rw [← cancel_epi πU, comp_zero, biprod.lift_desc, Preadditive.comp_add,
    ← Category.assoc, ← Category.assoc, haI, haJ, Preadditive.comp_neg, hbI, hbJ,
    add_neg_cancel]

/-- **The abstract form of the sequence of Stacks 0CZ1.**

Let `M` be an `𝒪_X`-module with submodules `I` and `J`, and let `πU, πI, πJ, πV` be
epimorphisms out of `M` whose kernel submodules are `I ⊓ J`, `I`, `J` and `I ⊔ J`.  Let
`aI, aJ` and `bI, bJ` be the comparison maps, so `πU ≫ aI = πI` and `πI ≫ bI = πV`.  Then

`0 ⟶ QU ⟶ QI ⊞ QJ ⟶ QV ⟶ 0`

is short exact, with the lift of `aI, aJ` as its first map and the difference of `bI, bJ` as
its second.

Exactness and the epimorphism come from the second map being a cokernel of the first, which is
the universal property of the join applied to the sum of the two composites coming out of
`QI ⊞ QJ`; the monomorphism is
`AlgebraicGeometry.Space.mono_biprod_lift_of_ker_eq_inf`.  The module documentation sets out
both steps. -/
theorem shortExact_biprod_of_ker_eq_inf_sup
    {M QU QI QJ QV : Modules.{u, u} B S hS F hF} {I J : M.Submodule}
    (πU : M ⟶ QU) (πI : M ⟶ QI) (πJ : M ⟶ QJ) (πV : M ⟶ QV)
    (hπU : Epi πU) (hπI : Epi πI) (hπJ : Epi πJ) (hπV : Epi πV)
    (hU : SheafOfModules.Submodule.ker πU = I ⊓ J)
    (hI : SheafOfModules.Submodule.ker πI = I)
    (hJ : SheafOfModules.Submodule.ker πJ = J)
    (hV : SheafOfModules.Submodule.ker πV = I ⊔ J)
    (aI : QU ⟶ QI) (aJ : QU ⟶ QJ) (bI : QI ⟶ QV) (bJ : QJ ⟶ QV)
    (haI : πU ≫ aI = πI) (haJ : πU ≫ aJ = πJ)
    (hbI : πI ≫ bI = πV) (hbJ : πJ ≫ bJ = πV) :
    (ShortComplex.mk (biprod.lift aI aJ) (biprod.desc bI (-bJ))
      (biprod_lift_comp_biprod_desc_eq_zero B S hS F hF πU πI πJ πV hπU aI aJ bI bJ
        haI haJ hbI hbJ)).ShortExact := by
  have := hπU
  have := hπI
  have := hπJ
  have := hπV
  have hzV : (I ⊔ J).ι ≫ πV = 0 := ι_comp_eq_zero_of_ker_eq B S hS F hF hV
  have hcokV : IsColimit (CokernelCofork.ofπ πV hzV) :=
    (ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk ((I ⊔ J).ι) πV hzV)
        (isLimitKernelFork_of_ker_eq B S hS F hF hV hzV))
      (mono_of_isLimit_fork (isLimitKernelFork_of_ker_eq B S hS F hF hV hzV))
      inferInstance).gIsCokernel
  have hepiI : Epi bI := by
    have h : Epi (πI ≫ bI) := by rw [hbI]; infer_instance
    exact epi_of_epi πI bI
  have hepig : Epi (biprod.desc bI (-bJ)) := by
    have h : Epi (biprod.inl ≫ biprod.desc bI (-bJ)) := by rw [biprod.inl_desc]; exact hepiI
    exact epi_of_epi biprod.inl _
  have hdesc : ∀ {W : Modules.{u, u} B S hS F hF} (t : QI ⊞ QJ ⟶ W),
      biprod.lift aI aJ ≫ t = 0 → {s : QV ⟶ W // biprod.desc bI (-bJ) ≫ s = t} := by
    intro W t ht
    have h : aI ≫ (biprod.inl ≫ t) + aJ ≫ (biprod.inr ≫ t) = 0 := by
      rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ← biprod.lift_eq, ht]
    have hsum : πI ≫ (biprod.inl ≫ t) + πJ ≫ (biprod.inr ≫ t) = 0 := by
      rw [← haI, ← haJ, Category.assoc, Category.assoc, ← Preadditive.comp_add, h, comp_zero]
    have hIu : I.ι ≫ (πI ≫ (biprod.inl ≫ t)) = 0 := by
      rw [← Category.assoc, ι_comp_eq_zero_of_ker_eq B S hS F hF hI, zero_comp]
    have hIu' : πI ≫ (biprod.inl ≫ t) = -(πJ ≫ (biprod.inr ≫ t)) :=
      eq_neg_of_add_eq_zero_left hsum
    have hJu : J.ι ≫ (πI ≫ (biprod.inl ≫ t)) = 0 := by
      rw [hIu', Preadditive.comp_neg, ← Category.assoc,
        ι_comp_eq_zero_of_ker_eq B S hS F hF hJ, zero_comp, neg_zero]
    have hVu : (I ⊔ J).ι ≫ (πI ≫ (biprod.inl ≫ t)) = 0 :=
      (le_ker_iff_ι_comp_eq_zero B S hS F hF _ _).1
        (sup_le ((le_ker_iff_ι_comp_eq_zero B S hS F hF I _).2 hIu)
          ((le_ker_iff_ι_comp_eq_zero B S hS F hF J _).2 hJu))
    obtain ⟨s, hs⟩ := CokernelCofork.IsColimit.desc' hcokV _ hVu
    have hsV : πV ≫ s = πI ≫ (biprod.inl ≫ t) := hs
    refine ⟨s, biprod.hom_ext' _ _ ?_ ?_⟩
    · rw [← Category.assoc, biprod.inl_desc, ← cancel_epi πI, ← Category.assoc, hbI, hsV]
    · rw [← Category.assoc, biprod.inr_desc, ← cancel_epi πJ, Preadditive.neg_comp,
        Preadditive.comp_neg, ← Category.assoc, hbJ, hsV, hIu', neg_neg]
  have hcoker : IsColimit (CokernelCofork.ofπ (biprod.desc bI (-bJ))
      (biprod_lift_comp_biprod_desc_eq_zero B S hS F hF πU πI πJ πV hπU aI aJ bI bJ
        haI haJ hbI hbJ)) :=
    CokernelCofork.IsColimit.ofπ _ _ (fun t ht => (hdesc t ht).1) (fun t ht => (hdesc t ht).2)
      (fun t ht m hm => by rw [← (hdesc t ht).2] at hm; exact (cancel_epi _).1 hm)
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ hcoker)
    (mono_biprod_lift_of_ker_eq_inf B S hS F hF πU πI πJ hπU hU hI hJ aI aJ haI haJ)
    (epi_of_isColimit_cofork hcoker)

end Lattice

/-! ### The canonical map between the structure sheaves of nested closed subspaces -/

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- A smaller closed subspace has a larger kernel of the structure projection.  This is
`AlgebraicGeometry.Space.definingIdealSheaf_antitone` read through
`AlgebraicGeometry.Space.ker_structureProjection`. -/
theorem ker_structureProjection_le (W W' : ClosedSubspaces B S hS X.1) (h : W.1 ≤ W'.1) :
    SheafOfModules.Submodule.ker (structureProjection B S hS X W') ≤
      SheafOfModules.Submodule.ker (structureProjection B S hS X W) := by
  rw [ker_structureProjection, ker_structureProjection]
  exact definingIdealSheaf_antitone B S hS X W W' h

/-- **The canonical map `i_*𝒪_{W'} ⟶ i_*𝒪_W` of `𝒪_X`-modules** attached to an inclusion
`W ⊆ W'` of closed subspaces of `X`.

The structure projection of `W'` exhibits `i_*𝒪_{W'}` as the quotient of `𝒪_X` by the defining
ideal of `W'`, by `AlgebraicGeometry.Space.isColimitCokernelCofork`, and that ideal is
contained in the defining ideal of `W`, which is the kernel of the structure projection of `W`;
so the structure projection of `W` factors through that quotient, uniquely because the
projection of `W'` is an epimorphism.  That factorization is the canonical map:
`AlgebraicGeometry.Space.eq_closedSubspaceRestriction` records that nothing else is compatible
with the two projections from `𝒪_X`. -/
noncomputable def closedSubspaceRestriction
    (W W' : ClosedSubspaces B S hS X.1) (h : W.1 ≤ W'.1) :
    pushforwardStructureSheaf B S hS X W' ⟶ pushforwardStructureSheaf B S hS X W :=
  (CokernelCofork.IsColimit.desc' (isColimitCokernelCofork B S hS X W')
    (structureProjection B S hS X W)
    ((le_ker_iff_ι_comp_eq_zero B S hS X.1 X.2 _ (structureProjection B S hS X W)).1
      (ker_structureProjection_le B S hS X W W' h))).1

/-- **The canonical map is compatible with the structure projections from `𝒪_X`.** -/
@[simp]
theorem structureProjection_comp_closedSubspaceRestriction
    (W W' : ClosedSubspaces B S hS X.1) (h : W.1 ≤ W'.1) :
    structureProjection B S hS X W' ≫ closedSubspaceRestriction B S hS X W W' h =
      structureProjection B S hS X W :=
  (CokernelCofork.IsColimit.desc' (isColimitCokernelCofork B S hS X W')
    (structureProjection B S hS X W)
    ((le_ker_iff_ι_comp_eq_zero B S hS X.1 X.2 _ (structureProjection B S hS X W)).1
      (ker_structureProjection_le B S hS X W W' h))).2

/-- **The canonical map is the only map compatible with the structure projections from `𝒪_X`**,
because the structure projection of the larger subspace is an epimorphism. -/
theorem eq_closedSubspaceRestriction (W W' : ClosedSubspaces B S hS X.1) (h : W.1 ≤ W'.1)
    (r : pushforwardStructureSheaf B S hS X W' ⟶ pushforwardStructureSheaf B S hS X W)
    (hr : structureProjection B S hS X W' ≫ r = structureProjection B S hS X W) :
    r = closedSubspaceRestriction B S hS X W W' h := by
  have := epi_structureProjection B S hS X W'
  exact (cancel_epi (structureProjection B S hS X W')).1
    (hr.trans (structureProjection_comp_closedSubspaceRestriction B S hS X W W' h).symm)

end Restriction

/-! ### The short exact sequence of Stacks 0CZ1 -/

section Sequence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (Y Z : ClosedSubspaces B S hS X.1)

/-- **The first map of the sequence of Stacks 0CZ1**, `𝒪_{Y ∪ Z} ⟶ 𝒪_Y × 𝒪_Z`: the lift of the
two canonical maps `𝒪_{Y ∪ Z} ⟶ 𝒪_Y` and `𝒪_{Y ∪ Z} ⟶ 𝒪_Z`. -/
noncomputable def unionToBiprodStructureSheaves :
    pushforwardStructureSheaf B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z) ⟶
      pushforwardStructureSheaf B S hS X Y ⊞ pushforwardStructureSheaf B S hS X Z :=
  biprod.lift
    (closedSubspaceRestriction B S hS X Y _
      (le_schemeTheoreticUnion_left B S hS X.2 Y Z))
    (closedSubspaceRestriction B S hS X Z _
      (le_schemeTheoreticUnion_right B S hS X.2 Y Z))

/-- **The second map of the sequence of Stacks 0CZ1**, `𝒪_Y × 𝒪_Z ⟶ 𝒪_{Y ∩ Z}`: the canonical
map `𝒪_Y ⟶ 𝒪_{Y ∩ Z}` on the first summand and the *negative* of the canonical map
`𝒪_Z ⟶ 𝒪_{Y ∩ Z}` on the second, as the tag prescribes. -/
noncomputable def biprodStructureSheavesToIntersection :
    pushforwardStructureSheaf B S hS X Y ⊞ pushforwardStructureSheaf B S hS X Z ⟶
      pushforwardStructureSheaf B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) :=
  biprod.desc
    (closedSubspaceRestriction B S hS X
      (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) Y inf_le_left)
    (-(closedSubspaceRestriction B S hS X
      (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) Z inf_le_right))

/-- The kernel of the structure projection of the scheme-theoretic union is the meet of the
kernels of the structure projections of the two subspaces.  This is
`AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticUnion`, the union half of
Stacks 0CYZ, read through `AlgebraicGeometry.Space.ker_structureProjection`. -/
theorem ker_structureProjection_schemeTheoreticUnion :
    SheafOfModules.Submodule.ker
        (structureProjection B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z)) =
      SheafOfModules.Submodule.ker (structureProjection B S hS X Y) ⊓
        SheafOfModules.Submodule.ker (structureProjection B S hS X Z) := by
  rw [ker_structureProjection, ker_structureProjection, ker_structureProjection]
  exact definingIdealSheaf_schemeTheoreticUnion B S hS X Y Z

/-- The kernel of the structure projection of the scheme-theoretic intersection is the join of
the kernels of the structure projections of the two subspaces.  This is
`AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticIntersection`, the intersection half
of Stacks 0CYZ, read through `AlgebraicGeometry.Space.ker_structureProjection`. -/
theorem ker_structureProjection_schemeTheoreticIntersection :
    SheafOfModules.Submodule.ker
        (structureProjection B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z)) =
      SheafOfModules.Submodule.ker (structureProjection B S hS X Y) ⊔
        SheafOfModules.Submodule.ker (structureProjection B S hS X Z) := by
  rw [ker_structureProjection, ker_structureProjection, ker_structureProjection]
  exact definingIdealSheaf_schemeTheoreticIntersection B S hS X Y Z

/-- The two maps of the sequence of Stacks 0CZ1 compose to zero. -/
theorem unionToBiprodStructureSheaves_comp_biprodStructureSheavesToIntersection :
    unionToBiprodStructureSheaves B S hS X Y Z ≫
      biprodStructureSheavesToIntersection B S hS X Y Z = 0 :=
  biprod_lift_comp_biprod_desc_eq_zero B S hS X.1 X.2
    (structureProjection B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z))
    (structureProjection B S hS X Y) (structureProjection B S hS X Z)
    (structureProjection B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z))
    (epi_structureProjection B S hS X _) _ _ _ _
    (structureProjection_comp_closedSubspaceRestriction B S hS X Y _ _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X Z _ _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X _ Y _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X _ Z _)

/-- **The sequence of Stacks 0CZ1**,
`𝒪_{Y ∪ Z} ⟶ 𝒪_Y × 𝒪_Z ⟶ 𝒪_{Y ∩ Z}`, as a short complex of `𝒪_X`-modules. -/
noncomputable def unionIntersectionShortComplex : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (unionToBiprodStructureSheaves B S hS X Y Z)
    (biprodStructureSheavesToIntersection B S hS X Y Z)
    (unionToBiprodStructureSheaves_comp_biprodStructureSheavesToIntersection B S hS X Y Z)

/-- **Stacks 0CZ1, second assertion.**  For two closed subspaces `Y, Z` of an algebraic space
`X` over `S`, with `Y ∪ Z` and `Y ∩ Z` their scheme-theoretic union and intersection,

`0 ⟶ 𝒪_{Y ∪ Z} ⟶ 𝒪_Y × 𝒪_Z ⟶ 𝒪_{Y ∩ Z} ⟶ 0`

is a short exact sequence of `𝒪_X`-modules, the four structure sheaves being taken as modules
on `X` under Stacks 04CJ, the first map built from the two canonical maps `𝒪_{Y ∪ Z} ⟶ 𝒪_Y` and
`𝒪_{Y ∪ Z} ⟶ 𝒪_Z` and the second from the canonical map `𝒪_Y ⟶ 𝒪_{Y ∩ Z}` and the negative of
the canonical map `𝒪_Z ⟶ 𝒪_{Y ∩ Z}`.

This is `AlgebraicGeometry.Space.shortExact_biprod_of_ker_eq_inf_sup` applied to the four
structure projections of `𝒪_X`, which are epimorphisms by
`AlgebraicGeometry.Space.epi_structureProjection` and whose kernels are the four defining
ideals; the two identifications of Stacks 0CYZ say that the kernels for the union and the
intersection are the meet and the join of the kernels for `Y` and `Z`. -/
@[stacks 0CZ1 "the short exact sequence of the structure sheaves of the union, the two \
subspaces and the intersection"]
theorem unionIntersectionShortComplex_shortExact :
    (unionIntersectionShortComplex B S hS X Y Z).ShortExact :=
  shortExact_biprod_of_ker_eq_inf_sup B S hS X.1 X.2
    (structureProjection B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z))
    (structureProjection B S hS X Y) (structureProjection B S hS X Z)
    (structureProjection B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z))
    (epi_structureProjection B S hS X _) (epi_structureProjection B S hS X _)
    (epi_structureProjection B S hS X _) (epi_structureProjection B S hS X _)
    (ker_structureProjection_schemeTheoreticUnion B S hS X Y Z) rfl rfl
    (ker_structureProjection_schemeTheoreticIntersection B S hS X Y Z) _ _ _ _
    (structureProjection_comp_closedSubspaceRestriction B S hS X Y _ _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X Z _ _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X _ Y _)
    (structureProjection_comp_closedSubspaceRestriction B S hS X _ Z _)

end Sequence

end AlgebraicGeometry.Space

end
