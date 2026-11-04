module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyIrreducible
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme

/-!
# The constant family `X × ℓ` inside `ℓ × 𝐏(V)`

Clause (3) of Tag 0B1T compares the family `C'` with the *constant* family `X × 𝐏^1` of a closed
subvariety `X` of `𝐏(V)`. Inside the ambient product `ℓ ×_k 𝐏(V)` that constant family is the
preimage of `X` under the projection to `𝐏(V)`. This file identifies that preimage with the
product `ℓ ×_k X` of the line with the reduced closed subscheme on `X`, which gives its dimension
— `dim X + 1`, by the product formula of Tag 0B2M — and its irreducibility.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.constantFamily`: the constant family, the preimage
  of `X` under the projection `ℓ × 𝐏(V) ⟶ 𝐏(V)`.

## Main results

* `AlgebraicGeometry.range_pullback_fst_base` and
  `AlgebraicGeometry.range_pullback_snd_base`: in a fibre product of schemes the image of a
  projection is the preimage of the image of the opposite leg. This holds for arbitrary schemes,
  the points of a fibre product surjecting onto the set-theoretic fibre product.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_constantFamily`: the constant family is
  closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_constantFamily` and
  `…topologicalKrullDim_constantFamily'`: its dimension is `dim X + 1`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_constantFamily`: it is irreducible
  when `X` is.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre_constantFamily` and
  `…movingFibre_inter_constantFamily`: its fibre over every closed point of the line is `X`, so
  the fibre of an intersection with it is the intersection of the fibre with `X`.

## Implementation notes

The comparison is the pullback-pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`: the product `ℓ ×_k X` of the line with the
closed subscheme on `X` is the fibre product of the ambient product with that closed subscheme
over `𝐏(V)`, whose projection to the ambient product has image the preimage of `X` by
`AlgebraicGeometry.range_pullback_fst_base`. Dimension and irreducibility are then transported
along the homeomorphism onto that image.

The reduced closed subscheme on a closed subset is
`AlgebraicGeometry.ProjectiveSpaceOfModule.closedSubschemeOf`, as in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **In a fibre product of schemes the image of the second projection is the preimage of the
image of the first leg.** The points of a fibre product surject onto the set-theoretic fibre
product, which is `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`. -/
public theorem range_pullback_snd_base {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(pullback.fst f g).base z,
      congrArg (fun m : pullback f g ⟶ S => m.base z) (pullback.condition (f := f) (g := g))⟩
  · rintro ⟨x, hx⟩
    exact (Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hx).imp fun _ h => h.2

/-- **In a fibre product of schemes the image of the first projection is the preimage of the
image of the second leg.** -/
public theorem range_pullback_fst_base {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(pullback.snd f g).base z, (congrArg (fun m : pullback f g ⟶ S => m.base z)
      (pullback.condition (f := f) (g := g))).symm⟩
  · rintro ⟨y, hy⟩
    exact (Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hy.symm).imp
      fun _ h => h.1

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

section AbstractLine

variable (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k V]
  [FiniteDimensional k W] [Nontrivial W] [Nontrivial V]
  (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X)

/-- **The constant family `X × 𝐏(W)`**: the preimage of `X` under the projection of the ambient
product `𝐏(W) ×_k 𝐏(V)` to `𝐏(V)`. -/
public def lineProductConstant : Set (lineProduct k V W) :=
  (lineProductPoint k V W).base ⁻¹' X

omit [FiniteDimensional k V] [FiniteDimensional k W] [Nontrivial W] [Nontrivial V] in
/-- The constant family is closed. -/
public theorem isClosed_lineProductConstant (hXc : IsClosed X) :
    IsClosed (lineProductConstant k V W X) :=
  hXc.preimage (lineProductPoint k V W).continuous

omit [FiniteDimensional k V] [FiniteDimensional k W] [Nontrivial W] [Nontrivial V] in
/-- The constant family of the whole of `𝐏(V)` is the whole ambient product. -/
public theorem lineProductConstant_univ :
    lineProductConstant k V W (Set.univ : Set (projectiveSpaceOfModule k V)) = Set.univ :=
  Set.preimage_univ

/-- **The fibre of the constant family over any closed point of `𝐏(W)` is `X` itself.** -/
public theorem lineProductFibre_lineProductConstant [IsAlgClosed k]
    (lam : projectiveSpaceOfModule k W) (hlam : IsClosed ({lam} : Set _)) :
    lineProductFibre k V W lam hlam (lineProductConstant k V W X) = X := by
  ext y
  rw [mem_lineProductFibre_iff, lineProductConstant, Set.mem_preimage,
    lineProductPoint_lineProductSection]

/-- The fibre of an intersection with the constant family is the intersection of the fibre with
`X`. -/
public theorem lineProductFibre_inter_lineProductConstant [IsAlgClosed k]
    (lam : projectiveSpaceOfModule k W) (hlam : IsClosed ({lam} : Set _))
    (S : Set (lineProduct k V W)) :
    lineProductFibre k V W lam hlam (S ∩ lineProductConstant k V W X) =
      lineProductFibre k V W lam hlam S ∩ X := by
  rw [lineProductFibre, Set.preimage_inter, ← lineProductFibre, ← lineProductFibre,
    lineProductFibre_lineProductConstant]

/-- The product of `𝐏(W)` with the reduced closed subscheme on `X`, which is the constant
family `X × 𝐏(W)` presented as a product of schemes over `Spec k`. -/
public abbrev lineProductConstantProd : Scheme.{u} :=
  pullback (projectiveSpaceOfModuleToSpec k W) (closedSubschemeOfToSpec k V X hX)

/-- The fibre product of the ambient product with the closed subscheme on `X` over `𝐏(V)`, which
presents the constant family as a closed subset of the ambient product. -/
public abbrev lineProductConstantOver : Scheme.{u} :=
  pullback (lineProductPoint k V W) (closedSubschemeOfι k V X hX)

omit [FiniteDimensional k V] [FiniteDimensional k W] [Nontrivial W] [Nontrivial V] in
/-- **The constant family is the image of the projection of `(𝐏(W) × 𝐏(V)) ×_{𝐏(V)} X`.** -/
public theorem range_lineProductConstantOver :
    Set.range (pullback.fst (lineProductPoint k V W) (closedSubschemeOfι k V X hX)).base =
      lineProductConstant k V W X := by
  rw [range_pullback_fst_base, range_closedSubschemeOfι]
  rfl

/-- The two presentations of the constant family agree: `𝐏(W) ×_k X` is the fibre product of the
ambient product with `X` over `𝐏(V)`. -/
public def lineProductConstantIso :
    lineProductConstantOver k V W X hX ≅ lineProductConstantProd k V W X hX :=
  pullbackLeftPullbackSndIso (projectiveSpaceOfModuleToSpec k W)
    (projectiveSpaceOfModuleToSpec k V) (closedSubschemeOfι k V X hX)

/-- The constant family is homeomorphic to the product `𝐏(W) ×_k X`. -/
private theorem nonempty_homeomorph_lineProductConstant {k V W : Type u} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X) :
    Nonempty (lineProductConstant k V W X ≃ₜ lineProductConstantProd k V W X hX) :=
  ⟨(Homeomorph.setCongr (range_lineProductConstantOver k V W X hX).symm).trans <|
    ((pullback.fst (lineProductPoint k V W) (closedSubschemeOfι k V X hX)
      ).isClosedEmbedding.isEmbedding.toHomeomorph.symm.trans
      (lineProductConstantIso k V W X hX).hom.homeomorph)⟩

/-- **The dimension of the constant family is `dim X + dim 𝐏(W)`.** It is homeomorphic to the
product `𝐏(W) ×_k X`, whose dimension is the sum of the two by the product formula. -/
public theorem topologicalKrullDim_lineProductConstant :
    topologicalKrullDim (lineProductConstant k V W X) =
      topologicalKrullDim (projectiveSpaceOfModule k W) +
        topologicalKrullDim (closedSubschemeOf k V X hX) := by
  obtain ⟨e⟩ := nonempty_homeomorph_lineProductConstant (W := W) X hX
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph, topologicalKrullDim_pullback k _ _]

omit [FiniteDimensional k V] [FiniteDimensional k W] [Nontrivial W] [Nontrivial V] in
/-- **The constant family is irreducible** when `X` is, over an algebraically closed field: it is
homeomorphic to the product of `𝐏(W)` with the irreducible closed subscheme on `X`. -/
public theorem isIrreducible_lineProductConstant [IsAlgClosed k]
    [IrreducibleSpace (projectiveSpaceOfModule k W)] (hXc : IsClosed X)
    (hXirr : IsIrreducible X) : IsIrreducible (lineProductConstant k V W X) := by
  have hZ : IrreducibleSpace (closedSubschemeOf k V X hXc) := by
    refine ((closedSubschemeOfι k V X hXc).isClosedEmbedding.isEmbedding.toHomeomorph
      ).irreducibleSpace_iff.mpr ?_
    rw [range_closedSubschemeOfι]
    exact Subtype.irreducibleSpace hXirr
  have hprod : IrreducibleSpace (lineProductConstantProd k V W X hXc) := by
    have h1 : GeometricallyIrreducible (projectiveSpaceOfModuleToSpec k W) :=
      geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
    have h2 : GeometricallyIrreducible (closedSubschemeOfToSpec k V X hXc) :=
      geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
    have h3 : UniversallyOpen (projectiveSpaceOfModuleToSpec k W) := by infer_instance
    have h4 : UniversallyOpen (closedSubschemeOfToSpec k V X hXc) := by infer_instance
    infer_instance
  obtain ⟨e⟩ := nonempty_homeomorph_lineProductConstant (W := W) X hXc
  exact isIrreducible_iff_irreducibleSpace.mpr (e.irreducibleSpace_iff.mpr hprod)

end AbstractLine

variable (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]
  (X : Set (projectiveSpaceOfModule k V)) (hX : IsClosed X)

/-- **The constant family `X × ℓ`**: the constant family of
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineProductConstant` at the corank-two quotient. -/
public def constantFamily : Set (movingAmbient k V L) :=
  lineProductConstant k V (lineSpace k V L) X

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- The constant family is closed. -/
public theorem isClosed_constantFamily (hXc : IsClosed X) :
    IsClosed (constantFamily k V L X) :=
  isClosed_lineProductConstant k V (lineSpace k V L) X hXc

/-- **The fibre of the constant family over any closed point of the line is `X` itself.** -/
public theorem movingFibre_constantFamily [IsAlgClosed k] (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) :
    movingFibre k V L lam hlam (constantFamily k V L X) = X :=
  lineProductFibre_lineProductConstant k V (lineSpace k V L) X lam hlam

/-- The fibre of an intersection with the constant family is the intersection of the fibre with
`X`. -/
public theorem movingFibre_inter_constantFamily [IsAlgClosed k] (lam : movingLine k V L)
    (hlam : IsClosed ({lam} : Set _)) (S : Set (movingAmbient k V L)) :
    movingFibre k V L lam hlam (S ∩ constantFamily k V L X) =
      movingFibre k V L lam hlam S ∩ X :=
  lineProductFibre_inter_lineProductConstant k V (lineSpace k V L) X lam hlam S

/-- The product of the line with the reduced closed subscheme on `X`, which is the constant
family `X × ℓ` presented as a product of schemes over `Spec k`. -/
public abbrev constantFamilyProd : Scheme.{u} :=
  lineProductConstantProd k V (lineSpace k V L) X hX

/-- The fibre product of the ambient product with the closed subscheme on `X` over `𝐏(V)`, which
presents the constant family as a closed subset of the ambient product. -/
public abbrev constantFamilyOver : Scheme.{u} :=
  lineProductConstantOver k V (lineSpace k V L) X hX

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The constant family is the image of the projection of `(ℓ × 𝐏(V)) ×_{𝐏(V)} X`.** -/
public theorem range_constantFamilyOver :
    Set.range (pullback.fst (ambPoint k V L) (closedSubschemeOfι k V X hX)).base =
      constantFamily k V L X :=
  range_lineProductConstantOver k V (lineSpace k V L) X hX

/-- The two presentations of the constant family agree: `ℓ ×_k X` is the fibre product of the
ambient product with `X` over `𝐏(V)`. -/
public def constantFamilyIso :
    constantFamilyOver k V L X hX ≅ constantFamilyProd k V L X hX :=
  lineProductConstantIso k V (lineSpace k V L) X hX

/-- **The dimension of the constant family is `dim X + 1`.** It is homeomorphic to the product
`ℓ ×_k X` of the line with the closed subscheme on `X`, whose dimension is the sum of the two by
the product formula, and the line has dimension one. -/
public theorem topologicalKrullDim_constantFamily
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim (constantFamily k V L X) =
      topologicalKrullDim (closedSubschemeOf k V X hX) + 1 := by
  have h := topologicalKrullDim_lineProductConstant k V (lineSpace k V L) X hX
  rwa [show topologicalKrullDim (projectiveSpaceOfModule k (lineSpace k V L)) = 1 from
    topologicalKrullDim_movingLine k V L hL, add_comm] at h

omit [Nontrivial V] in
/-- **The constant family is irreducible** when `X` is, over an algebraically closed field: it is
homeomorphic to the product of the line with the irreducible closed subscheme on `X`. -/
public theorem isIrreducible_constantFamily [IsAlgClosed k] (hXc : IsClosed X)
    (hXirr : IsIrreducible X) : IsIrreducible (constantFamily k V L X) := by
  have hline : IrreducibleSpace (movingLine k V L) := inferInstance
  exact isIrreducible_lineProductConstant k V (lineSpace k V L) X hXc hXirr

/-- **The dimension of the constant family is `dim X + 1`**, read on the subset `X` itself. -/
public theorem topologicalKrullDim_constantFamily' (hXc : IsClosed X)
    (hL : Module.finrank k (lineSpace k V L) = 2) :
    topologicalKrullDim ↥(constantFamily k V L X) = topologicalKrullDim ↥X + 1 := by
  rw [topologicalKrullDim_constantFamily k V L X hXc hL]
  exact congrArg (· + 1) (topologicalKrullDim_vanishingIdeal_subscheme X hXc)

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
