module

public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulaySlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# Slicing a flat chart of an algebraic stack by a regular sequence

Let `𝒳` be an algebraic stack, let `U` be an algebraic space with a 1-morphism `U ⟶ 𝒳` which is
flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a field-valued point and let
`F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. Let global functions `f₁, …, f_r ∈ Γ(U, 𝒪_U)`
map to a regular sequence in the étale local ring `𝒪_{F, z̄}` at a geometric point `z` of the
fibre. If for every smooth surjective 1-morphism `c : 𝒲 ⟶ 𝒳` some open subspace of `U`
containing `p(z)` makes the base change along `c` of the zero locus `V(f₁, …, f_r) ⟶ 𝒳` flat and
locally of finite presentation, then after replacing `U` by an open subspace containing `p(z)`
the zero locus is flat and locally of finite presentation over `𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.chartZeroLocus`, `AlgebraicGeometry.Stack.zeroLocusOnOpen`: the closed
  subspace `V(f₁, …, f_r) ⊆ U`, and its restriction to an open subspace `V ⊆ U`, taken as the
  inverse image of the zero locus in `V`.
* `AlgebraicGeometry.Stack.zeroLocusOnOpenToStack`: the 1-morphism `V(f₁, …, f_r) ∩ V ⟶ 𝒳`.
* `AlgebraicGeometry.Stack.fibreSpaceProjection`: the projection `p : F ⟶ U` read as a morphism
  of algebraic spaces through a representability equivalence for the 2-fibre product.
* `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`: the condition that the `f_i` map to a
  regular sequence in `𝒪_{F, z̄}`.
* `AlgebraicGeometry.Stack.ZeroLocusIsFlatOverSmoothChart`: the condition that for every smooth
  surjective 1-morphism `c : 𝒲 ⟶ 𝒳` some open subspace `V ⊆ U` containing `p(z)` makes the base
  change of `V(f₁, …, f_r) ∩ V ⟶ 𝒳` along `c` flat and locally of finite presentation.

## Main results

* `AlgebraicGeometry.Stack.exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus`:
  under `ZeroLocusIsFlatOverSmoothChart`, there is an open subspace `V ⊆ U` containing `p(z)`
  with `V(f₁, …, f_r) ∩ V ⟶ 𝒳` flat and locally of finite presentation.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_twoFibreProduct_fst_descent`: local
  finite presentation descends along a surjective, flat, locally finitely presented base change.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06M2](https://stacks.math.columbia.edu/tag/06M2)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descent of local finite presentation along a base change -/

/-- Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` with `g`
surjective, flat and locally of finite presentation, and let `P` be a 2-fibre product of the
cospan `(g, f)`. If the base change `P.fst` of `f` along `g` is locally of finite presentation,
then so is `f`. -/
theorem isLocallyOfFinitePresentation_twoFibreProduct_fst_descent
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hgsurj : IsSurjective B S hS g)
    (hgflat : AlgebraicStacks.IsFlat B S hS g)
    (hglfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    (hfst : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.fst) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f := by
  have hsndsurj : IsSurjective B S hS P.snd :=
    isSurjective_of_isTwoFibreProduct B S hS P hP hgsurj
  have hsndflat : AlgebraicStacks.IsFlat B S hS P.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS g f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hgflat
  have hsndlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.snd :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS g f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hglfp
  have hiff := hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    P.pt.property 𝒴.property
  have htotal : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (P.snd ≫ f) :=
    (hiff (P.snd ≫ f).hom).2
      (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
        (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
        (Bicategory.InducedBicategory.isoHom P.iso)
        ((hiff (P.fst ≫ g).hom).1
          (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS P.fst g hfst hglfp)))
  exact AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf B S hS P.snd f
    htotal hsndsurj hsndflat hsndlfp

/-! ### The zero locus of a family of global functions on a chart -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (k : Type u) [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)

variable (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (g : schemeStack.{u, w} B S hS (fieldPointObject B S hS k hk toBase) ⟶ 𝒳)

variable {r : ℕ}
  (a : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)

/-- The closed subspace `V(f₁, …, f_r) ⊆ U` cut out by finitely many global regular functions on
the algebraic space `U`. -/
abbrev chartZeroLocus : Subfunctor U :=
  Space.vanishingSubfunctor B S hS ⟨U, hU⟩ a

/-- The zero locus of the restrictions of `f₁, …, f_r` to an open subspace `V ⊆ U`, namely
`V(f₁, …, f_r) ∩ V`, read as the inverse image of `V(f₁, …, f_r)` in `V`. -/
abbrev zeroLocusOnOpen (V : Subfunctor U) : Subfunctor V.toFunctor :=
  (chartZeroLocus B S hS U hU a).preimage V.ι

/-- `V(f₁, …, f_r) ∩ V` is a closed subspace of the open subspace `V`. -/
theorem isClosedSubspace_zeroLocusOnOpen (V : Subfunctor U)
    (hV : Space.IsOpenSubspace B S hS V) :
    Space.IsClosedSubspace B S hS (zeroLocusOnOpen B S hS U hU a V) :=
  Space.isClosedSubspace_preimage B S hS V.ι (chartZeroLocus B S hS U hU a) hU hV.1
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ a)

/-- The 1-morphism `V(f₁, …, f_r) ∩ V ⟶ 𝒳`: the inclusion of the zero locus into `V` followed by
the inclusion of `V` into `U`, read between algebraic stacks, followed by `U ⟶ 𝒳`. -/
abbrev zeroLocusOnOpenToStack (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V) :
    algebraicSpaceStack.{u, w} B S hS (zeroLocusOnOpen B S hS U hU a V).toFunctor
      (isClosedSubspace_zeroLocusOnOpen B S hS U hU a V hV).1 ⟶ 𝒳 :=
  algebraicSpaceStackMap.{u, w} B S hS
      (isClosedSubspace_zeroLocusOnOpen B S hS U hU a V hV).1 hU
      ((zeroLocusOnOpen B S hS U hU a V).ι ≫ V.ι) ≫ f

/-! ### The fibre and its étale local ring at a geometric point -/

variable (Fsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hFsp : IsAlgebraicSpace B S hS Fsp)
  (eF : StacksRepresentableCFG.EquivalenceOver
    (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val.val.p
    (presheafOfCategories (Fsp ⋙ typeToCat)).p)

/-- The projection `p : F ⟶ U`, as a morphism of algebraic spaces through an algebraic space
`Fsp` representing the 2-fibre product `F = U ×_𝒳 Spec k`. -/
abbrev fibreSpaceProjection : Fsp ⟶ U :=
  representingMap B S hS (fibreOverFieldPoint B S hS 𝒳 U hU k hk toBase f g).val
    (algebraicSpaceStack.{u, w} B S hS U hU).val Fsp U eF
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (fibreProjection B S hS 𝒳 U hU k hk toBase f g).hom

/-- The global functions `f₁, …, f_r` on `U` map to a regular sequence in the étale local ring
`𝒪_{F, z̄}` at a geometric point `z` of the fibre: for every small étale neighbourhood of `p(z)`,
the images in `𝒪_{F, z̄}` of the germs of the `f_i` along it form a regular sequence. -/
abbrev FibreIsRegularSequenceAt (z : Space.GeometricPoint B S hS Fsp) : Prop :=
  ∀ N : Space.SmallEtaleNeighborhood
      (Space.geometricPointMap
        (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z),
    RingTheory.Sequence.IsRegular (Space.etaleLocalRing B S hS Fsp z)
      (List.ofFn fun i : Fin r =>
        Space.etaleLocalRingMap hFsp
            (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z
          (Space.etaleLocalRingGerm B S hS U
            (Space.geometricPointMap
              (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z)
            (Opposite.op N) ((a i).eval (Opposite.op N.chart))))

/-! ### Stacks 06MD -/

/-- Given flatness and local finite presentation of `U ⟶ 𝒳` and the regular sequence in
`𝒪_{F, z̄}`, for every smooth surjective 1-morphism `c : 𝒲 ⟶ 𝒳` there is an open subspace
`V ⊆ U` containing `p(z)` such that the base change of `V(f₁, …, f_r) ∩ V ⟶ 𝒳` along `c` is flat
and locally of finite presentation. -/
abbrev ZeroLocusIsFlatOverSmoothChart (z : Space.GeometricPoint B S hS Fsp) : Prop :=
  ∀ (𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒳),
      AlgebraicStacks.IsSmooth B S hS c → IsSurjective B S hS c →
      AlgebraicStacks.IsFlat B S hS f →
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z →
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∈
        Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
      ∀ P : Bicategory.TwoCommSq c
          (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV),
        Bicategory.IsTwoFibreProduct P →
          AlgebraicStacks.IsFlat B S hS P.fst ∧
            AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.fst

/-- Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space with a 1-morphism
`f : U ⟶ 𝒳` which is flat and locally of finite presentation, let `Spec k ⟶ 𝒳` be a
field-valued point, and let `F = U ×_𝒳 Spec k` with projection `p : F ⟶ U`. Let
`f₁, …, f_r ∈ Γ(U, 𝒪_U)` and let `z` be a geometric point of `F` at which the `f_i` map to a
regular sequence in the étale local ring `𝒪_{F, z̄}`. If the zero locus is flat and locally of
finite presentation after base change along every smooth surjective chart of `𝒳`, the same holds
over `𝒳` itself, after replacing `U` by an open subspace containing `p(z)`. -/
theorem exists_openSubspace_isFlat_isLocallyOfFinitePresentation_zeroLocus
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (z : Space.GeometricPoint B S hS Fsp)
    (hreg : FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z)
    (hSlice :
      ZeroLocusIsFlatOverSmoothChart.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z) :
    ∃ (V : Subfunctor U) (hV : Space.IsOpenSubspace B S hS V),
      Space.pointsMap B S hS Fsp
          (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z.image ∈
        Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ∧
      AlgebraicStacks.IsFlat B S hS
          (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) ∧
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
          (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV) := by
  obtain ⟨T, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨V, hV, hmem, hfst⟩ := hSlice _ c hcsm hcsurj hflat hfp hreg
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS c
    (zeroLocusOnOpenToStack.{u, w} B S hS 𝒳 U hU f a V hV)
  obtain ⟨hPflat, hPlfp⟩ := hfst _ hQ
  refine ⟨V, hV, hmem, ?_, ?_⟩
  · exact AlgebraicStacks.isFlat_twoFibreProduct_fst_descent B S hS _ c _ hQ hcsurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPflat
  · exact isLocallyOfFinitePresentation_twoFibreProduct_fst_descent B S hS _ c _ hQ hcsurj
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hPlfp

/-- `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt` agrees with
`AlgebraicGeometry.Space.FibreIsRegularSequenceAt` for the functions `f₁, …, f_r` on `U` at the
fibre projection `p : F ⟶ U`. -/
theorem fibreIsRegularSequenceAt_iff_space (z : Space.GeometricPoint B S hS Fsp) :
    FibreIsRegularSequenceAt.{u, w} B S hS 𝒳 U hU k hk toBase f g a Fsp hFsp eF z ↔
      Space.FibreIsRegularSequenceAt B S hS ⟨U, hU⟩ a hFsp
        (fibreSpaceProjection B S hS 𝒳 U hU k hk toBase f g Fsp eF) z :=
  Iff.rfl

end AlgebraicGeometry.Stack

end
