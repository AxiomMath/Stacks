module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct

/-!
# The invertible module `𝒪(1,1,1)` on the triple product of the Moving Lemma

The graph of the family of projective transformations over a line `ℓ ⊆ 𝐏 = 𝐏((End V)ᵛ)` is cut
out of `𝐏(V) ×_k (ℓ ×_k 𝐏(V))` by the `2 × 2` determinants
`f_y(u) · f_x(g v) - f_y(v) · f_x(g u)`, which say that the functional cutting out the target
point `y` is proportional to the functional `f_x ∘ g` cutting out `r_g(x)`. Each such determinant
is a global section of

`𝒪(1,1,1) = prSource^* 𝒪(1) ⊗ prLine^* 𝒪_ℓ(1) ⊗ prTarget^* 𝒪(1)`,

because `f_x(g v)` is linear in the functional at the source point and linear in `g`, hence —
`g` being the tautological endomorphism of the line — linear in the coordinate of the line. This
file builds that invertible module and the tensors of three tautological sections generating it,
and identifies their nonvanishing loci.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTaut`: the pullback of the section `ι v` of
  `𝒪(1)` along a morphism to a projective space.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.boxModule`: the invertible module `𝒪(1,1,1)` on the
  triple product.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.boxSection`: the tensor
  `prSource^*(ι a) ⊗ prLine^*(ι b) ⊗ prTarget^*(ι c)` of three tautological sections.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isInvertible_boxModule`: `𝒪(1,1,1)` is invertible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.nonvanishingLocus_pullbackTaut`: the nonvanishing
  locus of a pulled-back tautological section is the preimage of the standard open.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_boxSection_iff`: the tensor of
  three tautological sections is nonvanishing at a point of the triple product exactly when each
  of the three degree-one forms avoids the homogeneous prime of the corresponding projection.

## Implementation notes

`AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTaut` is the analogue of
`AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalPullbackSection` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus`, stated for an
arbitrary scheme and an arbitrary module rather than for the triple product of one projective
space with itself: here the middle factor is the projective space of the corank-two quotient
`(End V)ᵛ ⧸ L`, a different module from `V`, so the three pullbacks cannot share a single
instantiation.

The module is assembled as `(𝒪(1) ⊠ 𝒪_ℓ(1)) ⊠ 𝒪(1)`, the left-nested tensor, as in that file, so
that the invertibility instances and the nonvanishing-locus computation are the same two-step
induction.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k : Type u) [Field k]

/-- **The pullback of the tautological section `ι v` of `𝒪(1)`** along a morphism from a scheme
to the projective space of a module. -/
public def pullbackTaut (M : Type u) [AddCommGroup M] [Module k M] {T : Scheme.{u}}
    (f : T ⟶ projectiveSpaceOfModule k M) (v : M) :
    ((Scheme.Modules.pullback f).obj (tautologicalModule k M)).sections :=
  Stacks.SheafOfModules.modulePullbackSection f.toLRSHom (tautologicalModule k M)
    (tautologicalSection k M v)

/-- `𝒪(1)` on the projective space of a module is invertible, as an instance. -/
public instance isInvertible_tautModule (M : Type u) [AddCommGroup M] [Module k M] :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceOfModule k M).presheaf
      (structureSheafRing (projectiveSpaceOfModule k M).toRingedSpace).property
      (tautologicalModule k M) :=
  isInvertible_tautologicalModule k M

/-- A pullback of `𝒪(1)` along a morphism to a projective space is invertible. -/
public instance isInvertible_pullbackTautModule (M : Type u) [AddCommGroup M] [Module k M]
    {T : Scheme.{u}} (f : T ⟶ projectiveSpaceOfModule k M) :
    Stacks.SheafOfModules.IsInvertible T.presheaf
      (structureSheafRing T.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (tautologicalModule k M)) :=
  Stacks.Modules.isInvertible_pullback f (tautologicalModule k M)

/-- **The nonvanishing locus of a pulled-back tautological section** is the preimage of the
standard open `D₊(ι v)`. -/
public theorem nonvanishingLocus_pullbackTaut (M : Type u) [AddCommGroup M] [Module k M]
    {T : Scheme.{u}} (f : T ⟶ projectiveSpaceOfModule k M) (v : M) :
    Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        ((Scheme.Modules.pullback f).obj (tautologicalModule k M)) (pullbackTaut k M f v) =
      f.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k M).toRingedSpace)
        (tautologicalModule k M) (tautologicalSection k M v) := by
  have hinv := isInvertible_tautologicalModule k M
  exact (congrArg (fun U : T.Opens => (U : Set T))
    (Stacks.SheafOfModules.preimage_nonvanishingOpen f (tautologicalModule k M)
      (tautologicalSection k M v))).symm

/-- A point of a scheme over a projective space lies in the nonvanishing locus of a pulled-back
tautological section exactly when the degree-one form avoids the homogeneous prime of its
image. -/
public theorem mem_nonvanishingLocus_pullbackTaut_iff (M : Type u) [AddCommGroup M] [Module k M]
    {T : Scheme.{u}} (f : T ⟶ projectiveSpaceOfModule k M) (v : M) (t : T) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        ((Scheme.Modules.pullback f).obj (tautologicalModule k M)) (pullbackTaut k M f v) ↔
      SymmetricAlgebra.ι k M v ∉ (f.base t).asHomogeneousIdeal := by
  rw [Set.ext_iff.mp (nonvanishingLocus_pullbackTaut k M f v) t, Set.mem_preimage,
    mem_nonvanishingLocus_tautologicalSection_iff]

variable (V : Type u) [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- The pullback `prSource^* 𝒪(1)` of the tautological module of `𝐏(V)` to the triple product. -/
public abbrev boxSource : (movingProd k V L).Modules :=
  (Scheme.Modules.pullback (prSource k V L)).obj (tautologicalModule k V)

/-- The pullback `prLine^* 𝒪_ℓ(1)` of the tautological module of the line to the triple
product. -/
public abbrev boxLine : (movingProd k V L).Modules :=
  (Scheme.Modules.pullback (prLine k V L)).obj (tautologicalModule k (lineSpace k V L))

/-- The pullback `prTarget^* 𝒪(1)` of the tautological module of `𝐏(V)` to the triple product. -/
public abbrev boxTarget : (movingProd k V L).Modules :=
  (Scheme.Modules.pullback (prTarget k V L)).obj (tautologicalModule k V)

/-- **The invertible module `𝒪(1,1,1)`** on the triple product `𝐏(V) ×_k (ℓ ×_k 𝐏(V))`: the
tensor of the pullbacks of the tautological modules of the three factors. -/
public def boxModule : (movingProd k V L).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(movingProd k V L).toRingedSpace.presheaf,
          (movingProd k V L).toRingedSpace.IsSheaf⟩).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(movingProd k V L).toRingedSpace.presheaf,
            (movingProd k V L).toRingedSpace.IsSheaf⟩).obj
        (boxSource k V L)).obj (boxLine k V L))).obj (boxTarget k V L)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **`𝒪(1,1,1)` is invertible**: a pullback of an invertible module is invertible, and so is a
tensor product of invertible modules. -/
public theorem isInvertible_boxModule :
    Stacks.SheafOfModules.IsInvertible (movingProd k V L).presheaf
      (structureSheafRing (movingProd k V L).toRingedSpace).property (boxModule k V L) :=
  have h12 := @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _
    (movingProd k V L).presheaf
    (structureSheafRing (movingProd k V L).toRingedSpace).property _ _
    (boxSource k V L) (boxLine k V L)
    (Stacks.Modules.isInvertible_pullback _ _) (Stacks.Modules.isInvertible_pullback _ _)
  @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ (movingProd k V L).presheaf
    (structureSheafRing (movingProd k V L).toRingedSpace).property _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(movingProd k V L).toRingedSpace.presheaf,
          (movingProd k V L).toRingedSpace.IsSheaf⟩).obj
      (boxSource k V L)).obj (boxLine k V L)) (boxTarget k V L) h12
    (Stacks.Modules.isInvertible_pullback _ _)

/-- **The tensor `prSource^*(ι a) ⊗ prLine^*(ι b) ⊗ prTarget^*(ι c)` of three tautological
sections**, a global section of `𝒪(1,1,1)`. -/
public def boxSection (a : V) (b : lineSpace k V L) (c : V) : (boxModule k V L).sections :=
  Stacks.SheafOfModules.tensorSections _ _
    (Stacks.SheafOfModules.tensorSections _ _
      (pullbackTaut k V (prSource k V L) a)
      (pullbackTaut k (lineSpace k V L) (prLine k V L) b))
    (pullbackTaut k V (prTarget k V L) c)

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The nonvanishing locus of a tensor of three tautological sections** is the intersection of
the three preimages of the nonvanishing loci of its factors. -/
public theorem nonvanishingLocus_boxSection (a : V) (b : lineSpace k V L) (c : V) :
    Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
        (boxModule k V L) (boxSection k V L a b c) =
      (Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
          (boxSource k V L) (pullbackTaut k V (prSource k V L) a) ∩
        Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
          (boxLine k V L) (pullbackTaut k (lineSpace k V L) (prLine k V L) b)) ∩
      Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
        (boxTarget k V L) (pullbackTaut k V (prTarget k V L) c) :=
  (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans
    (congrArg (· ∩ _) (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _))

omit [FiniteDimensional k V] [Nontrivial (lineSpace k V L)] [Nontrivial V] in
/-- **The tensor of three tautological sections is nonvanishing at a point of the triple product
exactly when each of the three degree-one forms avoids the homogeneous prime of the corresponding
projection** of that point. -/
public theorem mem_nonvanishingLocus_boxSection_iff (a : V) (b : lineSpace k V L) (c : V)
    (t : movingProd k V L) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (movingProd k V L).toRingedSpace)
        (boxModule k V L) (boxSection k V L a b c) ↔
      SymmetricAlgebra.ι k V a ∉ ((prSource k V L).base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k (lineSpace k V L) b ∉
          ((prLine k V L).base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k V c ∉ ((prTarget k V L).base t).asHomogeneousIdeal := by
  have h := Set.ext_iff.mp (nonvanishingLocus_boxSection k V L a b c) t
  rw [Set.mem_inter_iff, Set.mem_inter_iff, mem_nonvanishingLocus_pullbackTaut_iff,
    mem_nonvanishingLocus_pullbackTaut_iff, mem_nonvanishingLocus_pullbackTaut_iff] at h
  exact h.trans and_assoc

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
