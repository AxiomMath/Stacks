module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.EmptyModification
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SingletonSheafReductions

/-!
# A presheaf satisfying the almost blowup conditions does not see a thickening

Let `F` be a presheaf on the big h category over `S` satisfying condition (1) of Stacks 0EU5 and
condition (3) of Stacks 0EVF.  Then `F` turns every thickening of finite presentation of the site
into a bijection of sets.  This is the first step and "Interlude A" of the proof of the
sufficiency direction of Stacks 0EVF.

The source's argument for the affine case is that "the blow up of `Y` in `X` is the empty scheme
and this produces an almost blow up square consisting with `∅, ∅, X, Y` at the vertices", so that
condition (3) exhibits `F(X) → F(Y)` as the base change of a bijection between two singletons;
the empty square is `AlgebraicGeometry.exists_isEmpty_isAlmostBlowUpSquare`.  Interlude A then
drops affineness of the target by an affine open covering, which is
`AlgebraicGeometry.BigHOver.isSheafFor_singleton_of_affine_target`.

## Main results

* `AlgebraicGeometry.closedImmersionIsoKer`: a closed immersion is isomorphic, over its target,
  to the closed subscheme cut out by its kernel.
* `AlgebraicGeometry.BigHOver.isIso_map_of_affine_thickening`: the affine case.
* `AlgebraicGeometry.BigHOver.isIso_map_of_thickening`: **Interlude A**.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVA](https://stacks.math.columbia.edu/tag/0EVA)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

/-- A closed immersion is isomorphic, as a scheme over its target, to the closed subscheme cut
out by its kernel. -/
public theorem closedImmersionIsoKer {X Z : Scheme.{u}} (z : Z ⟶ X) [IsClosedImmersion z] :
    Nonempty (Over.mk z ≅ Over.mk z.ker.subschemeι) := by
  let k : Z ⟶ z.ker.subscheme :=
    IsClosedImmersion.lift z.ker.subschemeι z (by simp [Scheme.IdealSheafData.ker_subschemeι])
  have hk : IsIso k :=
    IsClosedImmersion.isIso_of_ker_eq z z.ker.subschemeι k
      (IsClosedImmersion.lift_fac z.ker.subschemeι z _)
      (by simp [Scheme.IdealSheafData.ker_subschemeι])
  exact ⟨Over.isoMk (asIso k) (IsClosedImmersion.lift_fac z.ker.subschemeι z _)⟩

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}

/-- **The affine case of the first step of the sufficiency direction of Stacks 0EVF.** A
presheaf on the big h category over `S` satisfying condition (1) of Stacks 0EU5 and condition (3)
of Stacks 0EVF turns a thickening of finite presentation with affine target into a bijection.

The centre of the almost blowup square used is the kernel of the thickening, whose support is all
of the target, so the modification may be taken to have empty source by
`AlgebraicGeometry.exists_isEmpty_isAlmostBlowUpSquare`; the sections over the modification and
over the exceptional corner are then both terminal, and a cartesian square with an isomorphism on
one side has an isomorphism on the opposite one. -/
public theorem isIso_map_of_affine_thickening
    (hZar : BigHOver.IsZariskiSheaf B S hS F)
    (hAlmost : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {X Z : BigHOver B S hS} (z : Z ⟶ X)
    (hX : IsAffine ((BigHOver.toScheme B S hS).obj X))
    (hz : IsClosedImmersion ((BigHOver.toScheme B S hS).map z))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map z))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map z)) :
    IsIso (F.map z.op) := by
  let T := BigHOver.toScheme B S hS
  let z' := T.map z
  have : IsAffine (T.obj X) := hX
  have : IsClosedImmersion z' := hz
  have : QuasiCompact z' := hfp.2.1
  let I : (T.obj X).IdealSheafData := z'.ker
  have hsupp : (I.support : Set (T.obj X)) = Set.univ := by
    rw [Scheme.Hom.support_ker z']
    rw [hsurj.surj.range_eq, closure_univ]
  obtain ⟨W, b', hWempty, hb'⟩ :=
    exists_isEmpty_isAlmostBlowUpSquare I (isFiniteType_ker_of_finitePresentation z' hfp) hsupp
  have : IsEmpty W := hWempty
  have : IsProper b' := hb'.proper
  have : LocallyOfFinitePresentation b' := hb'.finitePresentation.1
  have : QuasiCompact b' := hb'.finitePresentation.2.1
  have : LocallyOfFiniteType b' := inferInstance
  have hWcontains : B.Contains W :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact b' X.left.property
  let X' : BigHOver B S hS :=
    Over.mk (Y := B.obj W hWcontains) (ObjectProperty.homMk (b' ≫ X.hom.hom))
  let b : X' ⟶ X := Over.homMk (ObjectProperty.homMk b')
  let E := Limits.pullback b z
  let d : E ⟶ X' := Limits.pullback.fst b z
  let e : E ⟶ Z := Limits.pullback.snd b z
  have : IsEmpty (T.obj X') := hWempty
  have : IsEmpty (T.obj E) := Function.isEmpty (T.map d)
  have hpb : IsPullback (T.map e) (T.map d) (T.map z) (T.map b) :=
    (IsPullback.of_hasPullback b z).flip.map T
  have hsq := hAlmost X X' Z E b z d e I hX hb' (closedImmersionIsoKer z') hpb
  have : IsIso (F.map d.op) :=
    Limits.isIso_of_isTerminal (isTerminal_of_isEmpty hZar X')
      (isTerminal_of_isEmpty hZar E) _
  exact hsq.isIso_fst_of_isIso

/-- **Interlude A of the proof of the sufficiency direction of Stacks 0EVF.** A presheaf on the
big h category over `S` satisfying condition (1) of Stacks 0EU5 and condition (3) of Stacks 0EVF
turns every thickening of finite presentation of the site into a bijection.

The affine case is `AlgebraicGeometry.BigHOver.isIso_map_of_affine_thickening`, and affineness is
dropped by the generic affine reduction
`AlgebraicGeometry.BigHOver.isSheafFor_singleton_of_affine_target`: a thickening of finite
presentation is a monomorphism, so the sheaf condition for the one-element family it generates is
the same as bijectivity. -/
public theorem isIso_map_of_thickening
    (hZar : BigHOver.IsZariskiSheaf B S hS F)
    (hAlmost : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {X Z : BigHOver B S hS} (z : Z ⟶ X)
    (hz : IsClosedImmersion ((BigHOver.toScheme B S hS).map z))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map z))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map z)) :
    IsIso (F.map z.op) := by
  let Q : MorphismProperty Scheme.{u} := @IsClosedImmersion ⊓ (@Surjective ⊓
    (@LocallyOfFinitePresentation ⊓ (@QuasiCompact ⊓ @QuasiSeparated)))
  have : Q.IsStableUnderBaseChange := by
    refine ⟨fun sq hg ↦ ?_⟩
    exact ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq hg.1,
      MorphismProperty.of_isPullback (P := @Surjective) sq hg.2.1,
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq hg.2.2.1,
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq hg.2.2.2.1,
      MorphismProperty.of_isPullback (P := @QuasiSeparated) sq hg.2.2.2.2⟩
  have : Mono z := (BigHOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigHOver.toScheme B S hS).map z)))
  refine Presieve.isIso_map_of_mono_of_isSheafFor_singleton F z ?_
  refine isSheafFor_singleton_of_affine_target hZar Q ?_ z
    ⟨hz, hsurj, hfp.1, hfp.2.1, hfp.2.2⟩
  intro X₀ Z₀ w hX₀ hw
  have := isIso_map_of_affine_thickening hZar hAlmost w hX₀ hw.1 hw.2.1
    ⟨hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩
  exact Presieve.isSheafFor_singleton_of_isIso_map F w

end BigHOver

end AlgebraicGeometry

end
