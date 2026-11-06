module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceKernelIdealFirstMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactnessAt
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal

/-!
# Exactness at the middle term of the conormal sequence, for an arbitrary closed immersion

`AlgebraicGeometry.Space.conormalSequenceAt_exact` proves exactness at the middle term of the
conormal sequence of [Stacks Project, Tag 05ZA] for a *closed subspace* `Z ⊆ X`, with the
inclusion left as a parameter but with the first arrow written out of the defining ideal sheaf
of that subspace.  A consumer holding only a closed immersion `j : Zs ⟶ X` — with no closed
subspace of `X` in hand, and with the sequence written out of the kernel ideal sheaf
`𝓘_j = ker(j♯)` of [Stacks Project, Tag 03G8] — cannot instantiate it directly.

This file removes that restriction: exactness at the middle term holds for **every** closed
immersion of algebraic spaces, at the first arrow
`AlgebraicGeometry.Space.kernelConormalFirstMap` built from the kernel ideal sheaf.

## How the closed subspace is supplied

The closed subspace is not chosen by hand: it is the *scheme-theoretic image* of `j`.  A closed
immersion is quasi-compact (`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion`), and
for a quasi-compact morphism part (2) of [Stacks Project, Tag 082Z]
(`AlgebraicGeometry.Space.definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf`) says the
defining ideal sheaf of the scheme-theoretic image **is** the kernel ideal sheaf.  That single
equality discharges both stand-in hypotheses of
`AlgebraicGeometry.Space.conormalSequenceAt_exact` at once, since the two of them together say
exactly that the kernel of `j♯` is the defining ideal.

## Main results

* `AlgebraicGeometry.Space.structureSharpKillsDefiningIdeal_schemeTheoreticImage` and
  `AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_schemeTheoreticImage`: the two
  hypotheses, at the scheme-theoretic image of a closed immersion.
* `AlgebraicGeometry.Space.conormalSequenceFirstMapAt_eq_kernelConormalFirstMap`: the first
  arrow of the conormal sequence of a closed subspace is the one built from the kernel ideal
  sheaf, transported along the equality of the two ideals.
* `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion`: **exactness at
  the middle term for an arbitrary closed immersion.**

## Implementation notes

The two sheaves of ideals are *equal*, not merely isomorphic, so the comparison of the two first
arrows is a transport along an `eqToHom`.  It is proved by `subst` on the equality **at plain
variables**, in `AlgebraicGeometry.Space.submoduleTranspose_congr`, before any geometric term is
in sight; at the geometric instantiation the `subst` is unavailable and the unfolding of
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt` into
`AlgebraicGeometry.Space.submoduleTranspose` of
`AlgebraicGeometry.Space.submoduleDerivationHom` is a `whnf` timeout.  That unfolding is
therefore supplied as two `rfl` lemmas at plain variables
(`AlgebraicGeometry.Space.conormalSequenceFirstMapAt_eq_submoduleTranspose` and
`AlgebraicGeometry.Space.kernelConormalFirstMap_eq_submoduleTranspose`), each of which is cheap
on its own.

The annihilation hypotheses of the two `AlgebraicGeometry.Space.submoduleDerivationHom`s are
propositions, so once the two ideals are identified the two morphisms are equal by proof
irrelevance and nothing has to be said about their values.

Three further elaboration points:

* the proofs are in term mode wherever a composition has to be rewritten.  The sections of a
  direct image are typed `AlgebraicGeometry.Space.Modules` on one side of these equations and
  `CategoryTheory.SheafOfModules` on the other; the two are definitionally equal but not equal
  at the transparency `rw` uses, so `rw [Category.id_comp]` reports the target as not
  type-correct while the same step in term mode is immediate;
* in the final transport the exactness being transported has to be named in a `have` **before**
  `CategoryTheory.ShortComplex.exact_iff_of_iso` is applied, so that the target short complex is
  known when the comparison isomorphism is elaborated; with the isomorphism written inside the
  `refine` the elaborator postpones and exhausts the heartbeat budget;
* the comparison isomorphism is taken as `Functor.mapIso` of the transport rather than as the
  transport of the image, which keeps the cancellation inside the inverse-image functor where it
  is `CategoryTheory.Iso.inv_hom_id_assoc`.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 05ZA] is stated for an immersion, and
its middle exactness is registered at that generality on
`AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, which
consumes what is proved here; the subspace reading is registered on
`AlgebraicGeometry.Space.conormalSequence_exact`.  What is proved here is the same clause at
closed-immersion generality, which is one step of the reduction the tag's own proof performs and
not a new assertion of the tag.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Zs : AlgebraicSpaces B S hS}

/-! ### The two ideal hypotheses at the scheme-theoretic image -/

section Hypotheses

variable (j : Zs ⟶ X) (hj : IsClosedImmersion B S hS j.hom)

include hj in
/-- **The defining ideal sheaf of the scheme-theoretic image of a closed immersion is its kernel
ideal sheaf.**  This is part (2) of [Stacks Project, Tag 082Z] together with the fact that a
closed immersion is quasi-compact. -/
theorem definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf_of_isClosedImmersion :
    definingIdealSheaf B S hS X (schemeTheoreticImage B S hS j.hom X.2) =
      kernelIdealSheaf B S hS j :=
  definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS j
    (isQuasiCompact_of_isClosedImmersion B S hS j.hom Zs.2 X.2 hj)

/-- The defining ideal of the scheme-theoretic image of a closed immersion, at `U`, is the kernel
of `j♯` at `U`. -/
private theorem definingIdealAt_schemeTheoreticImage_eq_ker (hj : IsClosedImmersion B S hS j.hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    definingIdealAt B S hS X (schemeTheoreticImage B S hS j.hom X.2) U =
      RingHom.ker ((structureSharp B S hS j).hom.app U).hom :=
  congrArg (fun m : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule => m.obj U)
    (definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf_of_isClosedImmersion B S hS j hj)

include hj in
/-- **The structure map of a closed immersion kills the defining ideal of its scheme-theoretic
image.**  Half of the identification of that ideal with the kernel of `j♯`. -/
theorem structureSharpKillsDefiningIdeal_schemeTheoreticImage :
    StructureSharpKillsDefiningIdeal B S hS (schemeTheoreticImage B S hS j.hom X.2) j := by
  intro U a ha
  rw [definingIdealAt_schemeTheoreticImage_eq_ker B S hS j hj U] at ha
  exact RingHom.mem_ker.1 ha

include hj in
/-- **The kernel of the structure map of a closed immersion is contained in the defining ideal of
its scheme-theoretic image.**  The other half of that identification. -/
theorem structureSharpKernelLeDefiningIdeal_schemeTheoreticImage :
    StructureSharpKernelLeDefiningIdeal B S hS (schemeTheoreticImage B S hS j.hom X.2) j := by
  intro U a ha
  rw [definingIdealAt_schemeTheoreticImage_eq_ker B S hS j hj U]
  exact RingHom.mem_ker.2 ((structureSharpCommRing_app_apply B S hS j U a).symm.trans ha)

end Hypotheses

/-! ### The two first arrows agree -/

section FirstMap

variable {X' : AlgebraicSpaces B S hS}

/-- **The transpose across `f^* ⊣ f_*` of a morphism out of a sheaf of ideals depends on the
sheaf of ideals only.**  Two equal sheaves of ideals carrying morphisms that agree under the
transport have equal transposes, up to that transport.

Stated at plain variables so that the equality of ideals can be `subst`ed: at a geometric
instantiation it cannot be, both sides being applied terms. -/
theorem submoduleTranspose_congr (f : X' ⟶ X)
    {I J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule} (h : I = J)
    (M : Modules.{u, u} B S hS X'.1 X'.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M)
    (v : J.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M)
    (huv : eqToHom (congrArg
        (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
          K.toSheafOfModules) h) ≫ v = u) :
    submoduleTranspose B S hS f I M u =
      (modulePullback B S hS f).map (eqToHom (congrArg
          (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
            K.toSheafOfModules) h)) ≫
        submoduleTranspose B S hS f J M v := by
  subst h
  rw [eqToHom_refl] at huv
  exact (congrArg (fun w => submoduleTranspose B S hS f I M w)
        ((Category.id_comp v).symm.trans huv)).symm.trans
      ((Category.id_comp _).symm.trans
        (congrArg (fun m => m ≫ submoduleTranspose B S hS f I M v)
          (((congrArg (modulePullback B S hS f).map (eqToHom_refl _ _)).trans
            ((modulePullback B S hS f).map_id _)).symm)))

/-- **The transpose of a derivation restricted to a sheaf of ideals depends on the sheaf of
ideals only.**  The annihilation hypothesis is a proposition, so once the two ideals are
identified the two restricted derivations are the same morphism. -/
theorem submoduleTranspose_submoduleDerivationHom_congr (f : X' ⟶ X)
    {I J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule} (h : I = J)
    (M : Modules.{u, u} B S hS X'.1 X'.2)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (D : PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS f).obj M).val φ.hom)
    (hann₁ : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U)
            (((modulePushforward B S hS f).obj M).val.obj U) :=
          (((modulePushforward B S hS f).obj M).val.obj U).isModule
        ∀ m : ((modulePushforward B S hS f).obj M).val.obj U, a • m = 0)
    (hann₂ : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ J.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U)
            (((modulePushforward B S hS f).obj M).val.obj U) :=
          (((modulePushforward B S hS f).obj M).val.obj U).isModule
        ∀ m : ((modulePushforward B S hS f).obj M).val.obj U, a • m = 0) :
    submoduleTranspose B S hS f I M (submoduleDerivationHom B S hS I _ D hann₁) =
      (modulePullback B S hS f).map (eqToHom (congrArg
          (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
            K.toSheafOfModules) h)) ≫
        submoduleTranspose B S hS f J M (submoduleDerivationHom B S hS J _ D hann₂) := by
  subst h
  exact submoduleTranspose_congr B S hS f rfl M _ _
    ((congrArg (fun m => m ≫ submoduleDerivationHom B S hS I _ D hann₂)
        (eqToHom_refl _ _)).trans
      (Category.id_comp (submoduleDerivationHom B S hS I _ D hann₂)))

/-- The first arrow of the conormal sequence of a closed subspace, unfolded one step into the
transpose of the universal derivation restricted to the defining ideal sheaf.  Supplied as its
own `rfl` lemma because the same unfolding inside a larger elaboration is over budget. -/
theorem conormalSequenceFirstMapAt_eq_submoduleTranspose (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) (i : X' ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i) :
    conormalSequenceFirstMapAt B S hS Z b i hi =
      submoduleTranspose B S hS i (definingIdealSheaf B S hS X Z)
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
        (submoduleDerivationHom B S hS (definingIdealSheaf B S hS X Z) _
          (pullbackUnitDerivation B S hS i b)
          (fun U a ha m => smul_modulePushforward_eq_zero_of_structureSharp B S hS Z i hi _
            U a ha m)) :=
  rfl

/-- The first arrow of the conormal sequence at the kernel ideal sheaf, unfolded one step.  The
companion of `AlgebraicGeometry.Space.conormalSequenceFirstMapAt_eq_submoduleTranspose`. -/
theorem kernelConormalFirstMap_eq_submoduleTranspose (i : X' ⟶ X) (b : X ⟶ Bb) :
    kernelConormalFirstMap B S hS i b =
      submoduleTranspose B S hS i (kernelIdealSheaf B S hS i)
        ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
        (submoduleDerivationHom B S hS (kernelIdealSheaf B S hS i) _
          (pullbackUnitDerivation B S hS i b)
          (fun U a ha m => kernelIdealAt_smul_modulePushforward_eq_zero B S hS i _ U a ha m)) :=
  rfl

/-- **The first arrow of the conormal sequence of a closed subspace is the one built from the
kernel ideal sheaf**, transported along the equality of the two sheaves of ideals. -/
theorem conormalSequenceFirstMapAt_eq_kernelConormalFirstMap (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) (i : X' ⟶ X) (hi : StructureSharpKillsDefiningIdeal B S hS Z i)
    (hI : definingIdealSheaf B S hS X Z = kernelIdealSheaf B S hS i) :
    conormalSequenceFirstMapAt B S hS Z b i hi =
      (modulePullback B S hS i).map (eqToHom (congrArg
        (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
          K.toSheafOfModules) hI)) ≫ kernelConormalFirstMap B S hS i b := by
  rw [conormalSequenceFirstMapAt_eq_submoduleTranspose,
    kernelConormalFirstMap_eq_submoduleTranspose]
  exact submoduleTranspose_submoduleDerivationHom_congr B S hS i hI _ _ _ _

end FirstMap

/-! ### Exactness at the middle term -/

/-- **Exactness at the middle term of the conormal sequence of [Stacks Project, Tag 05ZA], for
an arbitrary closed immersion.**  For a closed immersion `j : Zs ⟶ X` of algebraic spaces over
`B` with structure morphism `b : X ⟶ Bb`, the short complex
```
  j^*𝓘_j ⟶ j^*Ω_{X/B} ⟶ Ω_{Zs/B}
```
built from the kernel ideal sheaf of `j` is exact at `j^*Ω_{X/B}`.

No closed subspace of `X` is assumed: the one that
`AlgebraicGeometry.Space.conormalSequenceAt_exact` needs is the scheme-theoretic image of `j`,
whose defining ideal sheaf is the kernel ideal sheaf by part (2) of
[Stacks Project, Tag 082Z]. -/
theorem conormalSequenceKernel_exact_of_isClosedImmersion (j : Zs ⟶ X)
    (hj : IsClosedImmersion B S hS j.hom) (b : X ⟶ Bb) :
    (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS j b)).Exact := by
  have hI := definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf_of_isClosedImmersion
    B S hS j hj
  have hIt : (definingIdealSheaf B S hS X
        (schemeTheoreticImage B S hS j.hom X.2)).toSheafOfModules =
      (kernelIdealSheaf B S hS j).toSheafOfModules :=
    congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
      K.toSheafOfModules) hI
  have hex := conormalSequenceAt_exact B S hS (schemeTheoreticImage B S hS j.hom X.2) b j
    (structureSharpKillsDefiningIdeal_schemeTheoreticImage B S hS j hj)
    (structureSharpKernelLeDefiningIdeal_schemeTheoreticImage B S hS j hj) hj
  refine (ShortComplex.exact_iff_of_iso ?_).mpr hex
  refine ShortComplex.isoMk
    ((modulePullback B S hS j).mapIso (eqToIso hIt)).symm (Iso.refl _) (Iso.refl _)
    ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      conormalSequenceFirstMapAt_eq_kernelConormalFirstMap B S hS
        (schemeTheoreticImage B S hS j.hom X.2) b j
        (structureSharpKillsDefiningIdeal_schemeTheoreticImage B S hS j hj) hI]
    exact Iso.inv_hom_id_assoc _ _
  · simp

end AlgebraicGeometry.Space

end
