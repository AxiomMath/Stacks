module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# The defining ideal of a closed subspace, computed on an étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8, which
`AlgebraicGeometry.Space.structureSharp` constructs, takes a regular function on an étale
scheme chart `V` of `Y` to the family of its pullbacks to the étale scheme charts of `X` above
`X ×_Y V`.  This file computes its *kernel*, which is what
`AlgebraicGeometry.Space.definingIdealAt` — the defining ideal of a closed subspace — is made
of.

Two steps.  First, with no hypothesis on `f`, a function lies in the kernel exactly when each
of its chartwise pullbacks vanishes: the sections of the direct image over `V` are a limit over
those charts, so a section of it is zero as soon as every chart projection of it is.  Second,
when `f` is *representable* the family has a distinguished member, namely the base-changed
chart `X ×_Y V` of Stacks 03G2, part (4), and that member is initial among the charts because
the comparison functor of Stacks 03G1 is fully faithful.  The whole kernel is therefore the
kernel of one honest ring map of global sections,

`Γ(V) ⟶ Γ(X ×_Y V)`,

pullback of regular functions along the cartesian projection.

A closed immersion is representable, so this applies to the inclusion of a closed subspace and
gives `AlgebraicGeometry.Space.definingIdealAt_eq_ker`: the defining ideal of a closed subspace
`Z` of `X` on an étale chart `U` is the kernel of `Γ(U) ⟶ Γ(Z ×_X U)`.  The inclusion-reversal
of Stacks 03MB follows at once, as
`AlgebraicGeometry.Space.definingIdealAt_antitone`: a smaller closed subspace has a larger
defining ideal, because `Z ×_X U ⟶ U` factors through `W ×_X U ⟶ U` when `Z ≤ W`.

## Main results

* `AlgebraicGeometry.Space.mem_ker_structureSharp_iff`: a regular function on an étale chart of
  `Y` is killed by the structure map exactly when all of its chartwise pullbacks vanish.  No
  hypothesis on `f`.
* `AlgebraicGeometry.Space.ker_structureSharp_eq`: for a representable `f`, the kernel of the
  structure map on sections over `V` is the kernel of pullback along the cartesian projection
  `X ×_Y V ⟶ V`.
* `AlgebraicGeometry.Space.definingIdealAt_eq_ker`: the defining ideal of a closed subspace on
  an étale chart is the kernel of pullback along the cartesian projection, a kernel of a map of
  rings of global sections of schemes.
* `AlgebraicGeometry.Space.definingIdealAt_antitone`: the defining ideals of closed subspaces
  reverse inclusions.

## Implementation notes

The distinguished chart `AlgebraicGeometry.Space.chartBaseChangeArrow` and the computation
`AlgebraicGeometry.Space.chartBaseChangeMap_chartBaseChangeArrow` of the morphism of schemes it
induces are imported from
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureMap.lean`, where they are the
subject rather than a tool.

Initiality of that chart is used only through the one morphism
`AlgebraicGeometry.Space.chartBaseChangeArrowHom`, which is all the kernel comparison needs, so
no `CategoryTheory.Limits.IsInitial` datum is built.

The kernel of `AlgebraicGeometry.Space.structureSharp` is computed by first discarding the
comparison factor between the direct image and its right Kan extension form: that factor is
an isomorphism of sheaves of sets, hence injective on sections, so it does not change kernels,
and the Kan extension form is where the pointwise limit over the charts lives.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The kernel of the structure map on an étale chart -/

section ChartKernel

variable {X Y : AlgebraicSpaces B S hS}

/-- A chart projection of the zero section of the direct image of the structure sheaf is
zero. -/
theorem chartProjection_ringZeroObj (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        (ringZeroObj (structureRingSheaf B S hS X) (directImageSections B S hS f V)) = 0 :=
  (ringZeroObj_naturality (structureRingSheaf B S hS X)
    (chartProjection B S hS f V j)).trans
      (sectionsFunctor_map_ringZeroHom (structureRingSheaf B S hS X) j.right default)

/-- The comparison of the direct image with its right Kan extension form is injective on
sections: it is an isomorphism of sheaves of sets. -/
theorem injective_smallEtaleDirectImageRanIso_app (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    Function.Injective
      (((pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X)
        (smallEtaleDirectImageRanIso B S hS f).inv).hom.app (op V)).hom) :=
  ((isIso_iff_bijective ((sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map
    ((smallEtaleDirectImageRanIso B S hS f).inv.app
      (structureSetSheaf B S hS X)))).1 inferInstance).1

/-- The structure map on sections over an étale chart `V` of `Y` kills a regular function
exactly when every chartwise pullback of that function vanishes: the sections of the direct
image over `V` are the limit of the sections over the charts of `X` above `X ×_Y V`. -/
theorem structureMapApp_eq_zero_iff (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    structureMapApp B S hS f V a =
        ringZeroObj (structureRingSheaf B S hS X) (directImageSections B S hS f V) ↔
      ∀ j, chartPullbackRingHom B S hS f V j a = 0 :=
  ⟨fun h j ↦ (chartProjection_structureMapApp B S hS f V j a).symm.trans
      (h ▸ chartProjection_ringZeroObj B S hS f V j),
    fun h ↦ chartProjection_ext B S hS f V fun j ↦
      (chartProjection_structureMapApp B S hS f V j a).trans
        ((h j).trans (chartProjection_ringZeroObj B S hS f V j).symm)⟩

/-- **The kernel of the structure map of Stacks 03G8, chartwise.** A regular function on an
étale scheme chart `V` of `Y` lies in the kernel of `f♯ : 𝒪_Y ⟶ f_*𝒪_X` over `V` exactly when
its pullback to every étale scheme chart of `X` above `X ×_Y V` vanishes. -/
theorem mem_ker_structureSharp_iff (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (a : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) :
    a ∈ RingHom.ker ((structureSharp B S hS f).hom.app (op V)).hom ↔
      ∀ j, a ∈ RingHom.ker (chartPullbackRingHom B S hS f V j) := by
  refine Iff.trans ?_ (structureMapApp_eq_zero_iff B S hS f V a)
  exact map_eq_zero_iff _ (injective_smallEtaleDirectImageRanIso_app B S hS f V)

/-! ### The distinguished chart of a representable morphism -/

/-- A function vanishing on the distinguished chart vanishes on every chart of `X` above
`X ×_Y V`, since its pullback there factors through the distinguished chart. -/
theorem ker_chartBaseChangeArrow_le (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    RingHom.ker (chartPullbackRingHom B S hS f V (chartBaseChangeArrow B S hS f hf V)) ≤
      RingHom.ker (chartPullbackRingHom B S hS f V j) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  refine (congrArg (fun g ↦ g a) (chartPullback_comp B S hS f V
    (chartBaseChangeArrowHom B S hS f hf V j))).trans ?_
  show ((structureRingSheaf B S hS X).obj.map
      (chartBaseChangeArrowHom B S hS f hf V j).right).hom
      (chartPullbackRingHom B S hS f V (chartBaseChangeArrow B S hS f hf V) a) = 0
  rw [ha, map_zero]

/-- **The kernel of the structure map of a representable morphism.** For a representable
`f : X ⟶ Y` the kernel of `f♯ : 𝒪_Y ⟶ f_*𝒪_X` on sections over an étale scheme chart `V` of `Y`
is the kernel of pullback of regular functions along the cartesian projection
`X ×_Y V ⟶ V`. -/
theorem ker_structureSharp_eq (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    RingHom.ker ((structureSharp B S hS f).hom.app (op V)).hom =
      RingHom.ker (chartPullbackRingHom B S hS f V (chartBaseChangeArrow B S hS f hf V)) :=
  le_antisymm (fun a ha ↦ (mem_ker_structureSharp_iff B S hS f V a).1 ha _)
    fun a ha ↦ (mem_ker_structureSharp_iff B S hS f V a).2
      fun j ↦ ker_chartBaseChangeArrow_le B S hS f hf V j ha

/-- Pullback of regular functions to the distinguished chart is pullback along the cartesian
projection, as a homomorphism of the rings of global sections of schemes. -/
theorem chartPullbackRingHom_chartBaseChangeArrow (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartPullbackRingHom B S hS f V (chartBaseChangeArrow B S hS f hf V) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op).hom :=
  congrArg (fun m ↦ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom)
    (chartBaseChangeMap_chartBaseChangeArrow B S hS f hf V)

end ChartKernel

/-! ### The defining ideal of a closed subspace -/

section DefiningIdeal

/-- **The defining ideal of a closed subspace, computed.** On an étale scheme chart `U` of `X`
the defining ideal of a closed subspace `Z` is the kernel of pullback of regular functions
along the closed immersion of schemes `Z ×_X U ⟶ U`. -/
theorem definingIdealAt_eq_ker (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X Z (op U) =
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd U.1.hom)).op).hom := by
  rw [show definingIdealAt B S hS X Z (op U) =
      RingHom.ker ((structureSharp B S hS (ObjectProperty.homMk Z.1.ι :
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).hom.app (op U)).hom from rfl,
    ker_structureSharp_eq B S hS _ Z.2.2.rep U,
    chartPullbackRingHom_chartBaseChangeArrow]
  rfl

/-- For morphisms `m : T₁ ⟶ T₂` and `n : T₂ ⟶ T₃`, the kernel of pullback of global regular
functions along `n` is contained in the kernel of pullback along `m ≫ n`. -/
theorem ker_le_ker_comp {T₁ T₂ T₃ : BigFppfOver B S hS} (m : T₁ ⟶ T₂) (n : T₂ ⟶ T₃) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map n).op).hom ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (m ≫ n)).op).hom := by
  intro a ha
  refine RingHom.mem_ker.mpr ?_
  rw [Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply, RingHom.mem_ker.mp ha, map_zero]

/-- **Stacks 03MB, the inclusion-reversal.** A smaller closed subspace has a larger defining
ideal on every étale scheme chart: the closed immersion `Z ×_X U ⟶ U` factors through
`W ×_X U ⟶ U`, so pullback of regular functions along the latter kills no more than pullback
along the former. -/
theorem definingIdealAt_antitone (X : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS X.1) (hZW : Z.1 ≤ W.1) (U : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X W (op U) ≤ definingIdealAt B S hS X Z (op U) := by
  rw [definingIdealAt_eq_ker, definingIdealAt_eq_ker]
  have hcond : (Z.2.2.rep.fst U.1.hom ≫ Subfunctor.homOfLe hZW) ≫ W.1.ι =
      yoneda.map (Z.2.2.rep.snd U.1.hom) ≫ U.1.hom := by
    rw [Category.assoc, Subfunctor.homOfLe_ι]
    exact Z.2.2.rep.w U.1.hom
  refine le_of_le_of_eq (ker_le_ker_comp B S hS (W.2.2.rep.lift
      (Z.2.2.rep.fst U.1.hom ≫ Subfunctor.homOfLe hZW) (Z.2.2.rep.snd U.1.hom) hcond)
      (W.2.2.rep.snd U.1.hom))
    (congrArg (fun t ↦ RingHom.ker
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom)
      (W.2.2.rep.lift_snd _ _ hcond))

end DefiningIdeal

end AlgebraicGeometry.Space

end
