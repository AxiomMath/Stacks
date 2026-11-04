module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 01CI: pullback of the tensor and symmetric algebras of a module sheaf

Let `f : X ⟶ Y` be a morphism of ringed spaces and `F` a sheaf of `𝒪_Y`-modules. Stacks 01CI
asserts `f^*T(F) = T(f^*F)` and `f^*Sym(F) = Sym(f^*F)`. Here each is a graded family of
isomorphisms of the homogeneous pieces, together with the induced isomorphism of the underlying
direct sums, compatible with multiplication, the unit and the degree-one generators.

Both come from one construction: by
`Stacks.RingedSpace.isUniversal_pullbackGradedAlgebra` the pulled-back graded algebra `f^*A`
with the pulled-back generator `f^*ι` is again universal for the property of degree-one
generators that `A` with `ι` is universal for, so the comparison is the canonical isomorphism
between two graded algebras universal for the same property
(`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`) and its three compatibilities are that
isomorphism's.

## Main definitions

* `Stacks.RingedSpace.pullbackPieceIso` and `Stacks.RingedSpace.pullbackSigmaIso`: the
  degreewise comparison and its direct-sum form, for any graded algebra on `Y` universal for a
  property of degree-one generators which the pulled-back generator has on `X`.
* `AlgebraicGeometry.TensorAlgebraPullbackComparison` and
  `AlgebraicGeometry.SymmetricAlgebraPullbackComparison`: the data of the comparison for the
  tensor algebra and for the symmetric algebra.
* `AlgebraicGeometry.tensorAlgebraPullbackIso` and
  `AlgebraicGeometry.symmetricAlgebraPullbackIso`: **Stacks 01CI** for the tensor algebra and
  for the symmetric algebra of a sheaf of modules on a ringed space.

## Main results

* `Stacks.RingedSpace.pullbackPieceIso_mul`, `pullbackPieceIso_one` and
  `pullbackPieceIso_generator`: the comparison is multiplicative, unital and matches the
  degree-one generators, on pullback-unit images of local sections.
* `Stacks.RingedSpace.pullbackSigmaIso_ι`: the direct-sum comparison restricts on each
  homogeneous summand to the degreewise one.

## Implementation notes

The source writes an equality of algebra sheaves; as in the library's other statement of this
tag it is a graded family of isomorphisms here, and the component equations are stated after
applying the unit of the module-pullback adjunction, since the pullback is an abstract left
adjoint and the unit images are the only sections of it that can be named.

The two comparison structures take the two bundles of algebras as parameters rather than
mentioning `SheafOfModules.ringedSpaceAlgebras` directly; the two main definitions are at that
canonical bundle on both sides.

The exterior case is **absent on purpose**: the argument runs through
`Stacks.RingedSpace.bilinear_app_eq_of_pullbackUnit`, and `SquareZero` — unlike
`PairwiseCommutes`, and unlike the empty condition of the tensor algebra — is not a condition on
a bilinear map but on its diagonal, so it does not transfer to all sections of the pullback by
that extensionality. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra`.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
  PresheafOfModules Opposite

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {F : SheafOfModules.{u} (structureRingSheaf Y)}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)} {ι : F ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj F ⟶ B.piece 1}
  {Q : ∀ B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X),
    ((pullbackFunctor f).obj F ⟶ B'.piece 1) → Prop}
  (hpb : IsUniversal Q (pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι))
  (hB : IsUniversal Q B κ)

/-- **The comparison between the pullback of a universal graded algebra and the universal
graded algebra of the pullback**, in each degree. -/
noncomputable def pullbackPieceIso (n : ℤ) :
    (pullbackFunctor f).obj (A.piece n) ≅ B.piece n :=
  hpb.pieceIso hB n

/-- The comparison is multiplicative on pullback-unit images. -/
theorem pullbackPieceIso_mul (i j : ℤ) (V : (Opens Y.carrier)ᵒᵖ)
    (a : (A.piece i).val.obj V) (b : (A.piece j).val.obj V) :
    Hom.app (pullbackPieceIso f hpb hB (i + j)).hom.val ((opensMap f).op.obj V)
        (pullbackUnit f (A.piece (i + j)) V ((A.mul i j).app V a b)) =
      (B.mul i j).app ((opensMap f).op.obj V)
        (Hom.app (pullbackPieceIso f hpb hB i).hom.val ((opensMap f).op.obj V)
          (pullbackUnit f (A.piece i) V a))
        (Hom.app (pullbackPieceIso f hpb hB j).hom.val ((opensMap f).op.obj V)
          (pullbackUnit f (A.piece j) V b)) := by
  rw [← pullbackBilinear_pullbackUnit f (A.mul i j) V a b]
  exact hpb.pieceIso_mul hB i j ((opensMap f).op.obj V) _ _

/-- The comparison carries the pullback-unit image of the unit to the unit. -/
theorem pullbackPieceIso_one (V : (Opens Y.carrier)ᵒᵖ) :
    Hom.app (pullbackPieceIso f hpb hB 0).hom.val ((opensMap f).op.obj V)
        (pullbackUnit f (A.piece 0) V (A.one.eval V)) =
      B.one.eval ((opensMap f).op.obj V) := by
  obtain ⟨V⟩ := V
  rw [← pullbackSectionsUnit_eval f (A.piece 0) A.one V]
  exact hpb.pieceIso_one hB ((opensMap f).op.obj (op V))

/-- The comparison matches the two degree-one generators. -/
theorem pullbackPieceIso_generator (V : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj V) :
    Hom.app (pullbackPieceIso f hpb hB 1).hom.val ((opensMap f).op.obj V)
        (pullbackUnit f (A.piece 1) V (Hom.app ι.val V s)) =
      Hom.app κ.val ((opensMap f).op.obj V) (pullbackUnit f F V s) := by
  rw [← pullbackUnit_naturality f ι V s]
  exact congrArg (fun h : (pullbackFunctor f).obj F ⟶ B.piece 1 =>
      Hom.app h.val ((opensMap f).op.obj V) (pullbackUnit f F V s))
    (hpb.pieceIso_generator hB)

/-- **The comparison of the underlying direct sums of the nonnegative homogeneous pieces.** -/
noncomputable def pullbackSigmaIso :
    (pullbackFunctor f).obj (∐ fun n : ℕ => A.piece (n : ℤ)) ≅ ∐ fun n : ℕ => B.piece (n : ℤ) :=
  PreservesCoproduct.iso (pullbackFunctor f) (fun n : ℕ => A.piece (n : ℤ)) ≪≫
    Sigma.mapIso fun n : ℕ => pullbackPieceIso f hpb hB (n : ℤ)

/-- The direct-sum comparison restricts on each homogeneous summand to the degreewise
comparison. -/
theorem pullbackSigmaIso_ι (n : ℕ) :
    (pullbackFunctor f).map (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n) ≫
        (pullbackSigmaIso f hpb hB).hom =
      (pullbackPieceIso f hpb hB (n : ℤ)).hom ≫ Sigma.ι (fun m : ℕ => B.piece (m : ℤ)) n := by
  have h : (pullbackFunctor f).map (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n) ≫
        (PreservesCoproduct.iso (pullbackFunctor f) fun m : ℕ => A.piece (m : ℤ)).hom =
      Sigma.ι (fun m : ℕ => (pullbackFunctor f).obj (A.piece (m : ℤ))) n :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit (pullbackFunctor f)
        fun m : ℕ => A.piece (m : ℤ))
      (colimit.isColimit _) (Discrete.mk n)
  rw [pullbackSigmaIso, Iso.trans_hom, ← Category.assoc, h, Sigma.ι_mapIso_hom]

end Stacks.RingedSpace

namespace AlgebraicGeometry

open Stacks.RingedSpace RingedSpaceModuleAdjunction SheafOfModules

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (F : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y))
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology Y.carrier) F)
  (B : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier)
    ((pullbackFunctor f).obj F))

/-- **A graded comparison of the pullback of a tensor algebra with the tensor algebra of the
pullback.** It includes the isomorphism of the underlying algebra sheaves and specifies its
behaviour on homogeneous summands, multiplication, the unit and degree-one generators. -/
structure TensorAlgebraPullbackComparison where
  /-- The comparison on each homogeneous piece. -/
  pieceIso (n : ℤ) : (pullbackFunctor f).obj (A.tensor.piece n) ≅ B.tensor.piece n
  /-- The comparison of the underlying direct-sum sheaves. -/
  sheafIso : (pullbackFunctor f).obj A.tensorAlgebraSheaf ≅ B.tensorAlgebraSheaf
  /-- The direct-sum comparison restricts to the comparison of each piece. -/
  sheafIso_ι (n : ℕ) :
    (pullbackFunctor f).map (Limits.Sigma.ι (fun m : ℕ => A.tensor.piece (m : ℤ)) n) ≫
        sheafIso.hom =
      (pieceIso (n : ℤ)).hom ≫ Limits.Sigma.ι (fun m : ℕ => B.tensor.piece (m : ℤ)) n
  /-- The comparison sends products of homogeneous sections to products. -/
  map_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (a : (A.tensor.piece i).val.obj U)
      (b : (A.tensor.piece j).val.obj U) :
    PresheafOfModules.Hom.app (pieceIso (i + j)).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.tensor.piece (i + j)) U ((A.tensor.mul i j).app U a b)) =
      (B.tensor.mul i j).app ((opensMap f).op.obj U)
        (PresheafOfModules.Hom.app (pieceIso i).hom.val ((opensMap f).op.obj U)
          (pullbackUnit f (A.tensor.piece i) U a))
        (PresheafOfModules.Hom.app (pieceIso j).hom.val ((opensMap f).op.obj U)
          (pullbackUnit f (A.tensor.piece j) U b))
  /-- The distinguished degree-zero unit is preserved. -/
  map_one (U : (Opens Y.carrier)ᵒᵖ) :
    PresheafOfModules.Hom.app (pieceIso 0).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.tensor.piece 0) U (A.tensor.one.eval U)) =
      B.tensor.one.eval ((opensMap f).op.obj U)
  /-- The comparison is the canonical one on the degree-one generators. -/
  map_generator (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U) :
    PresheafOfModules.Hom.app (pieceIso 1).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.tensor.piece 1) U
          (PresheafOfModules.Hom.app A.tensorGenerator.val U s)) =
      PresheafOfModules.Hom.app B.tensorGenerator.val ((opensMap f).op.obj U)
        (pullbackUnit f F U s)

/-- **A graded comparison of the pullback of a symmetric algebra with the symmetric algebra of
the pullback.** It includes the isomorphism of the underlying sheaves and its compatibility with
homogeneous inclusions, multiplication, the unit and degree-one generators. -/
structure SymmetricAlgebraPullbackComparison where
  /-- The comparison on each homogeneous piece. -/
  pieceIso (n : ℤ) : (pullbackFunctor f).obj (A.symmetric.piece n) ≅ B.symmetric.piece n
  /-- The comparison of the underlying direct-sum sheaves. -/
  sheafIso : (pullbackFunctor f).obj A.symmetricAlgebraSheaf ≅ B.symmetricAlgebraSheaf
  /-- The direct-sum comparison restricts to the comparison of each piece. -/
  sheafIso_ι (n : ℕ) :
    (pullbackFunctor f).map (Limits.Sigma.ι (fun m : ℕ => A.symmetric.piece (m : ℤ)) n) ≫
        sheafIso.hom =
      (pieceIso (n : ℤ)).hom ≫ Limits.Sigma.ι (fun m : ℕ => B.symmetric.piece (m : ℤ)) n
  /-- The comparison sends products of homogeneous sections to products. -/
  map_mul (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (a : (A.symmetric.piece i).val.obj U)
      (b : (A.symmetric.piece j).val.obj U) :
    PresheafOfModules.Hom.app (pieceIso (i + j)).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.symmetric.piece (i + j)) U ((A.symmetric.mul i j).app U a b)) =
      (B.symmetric.mul i j).app ((opensMap f).op.obj U)
        (PresheafOfModules.Hom.app (pieceIso i).hom.val ((opensMap f).op.obj U)
          (pullbackUnit f (A.symmetric.piece i) U a))
        (PresheafOfModules.Hom.app (pieceIso j).hom.val ((opensMap f).op.obj U)
          (pullbackUnit f (A.symmetric.piece j) U b))
  /-- The distinguished degree-zero unit is preserved. -/
  map_one (U : (Opens Y.carrier)ᵒᵖ) :
    PresheafOfModules.Hom.app (pieceIso 0).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.symmetric.piece 0) U (A.symmetric.one.eval U)) =
      B.symmetric.one.eval ((opensMap f).op.obj U)
  /-- The comparison is the canonical one on degree-one generators. -/
  map_generator (U : (Opens Y.carrier)ᵒᵖ) (s : F.val.obj U) :
    PresheafOfModules.Hom.app (pieceIso 1).hom.val ((opensMap f).op.obj U)
        (pullbackUnit f (A.symmetric.piece 1) U
          (PresheafOfModules.Hom.app A.symmetricGenerator.val U s)) =
      PresheafOfModules.Hom.app B.symmetricGenerator.val ((opensMap f).op.obj U)
        (pullbackUnit f F U s)

/-- **Stacks 01CI for the tensor algebra.** The pullback of the tensor algebra of a sheaf of
modules is canonically isomorphic to the tensor algebra of the pulled-back sheaf, as a graded
algebra and as an underlying sheaf. -/
noncomputable def tensorAlgebraPullbackIso :
    TensorAlgebraPullbackComparison f F
      (ringedSpaceAlgebras Y F)
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)) :=
  { pieceIso := pullbackPieceIso f
      (isTensorAlgebra_pullbackGradedAlgebra f
        (ringedSpaceAlgebras Y F).tensor_isTensorAlgebra).isUniversal
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)).tensor_isTensorAlgebra.isUniversal
    sheafIso := pullbackSigmaIso f
      (isTensorAlgebra_pullbackGradedAlgebra f
        (ringedSpaceAlgebras Y F).tensor_isTensorAlgebra).isUniversal
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)).tensor_isTensorAlgebra.isUniversal
    sheafIso_ι := pullbackSigmaIso_ι f _ _
    map_mul := pullbackPieceIso_mul f _ _
    map_one := pullbackPieceIso_one f _ _
    map_generator := pullbackPieceIso_generator f _ _ }

/-- **Stacks 01CI for the symmetric algebra.** The pullback of the symmetric algebra of a sheaf
of modules is canonically isomorphic to the symmetric algebra of the pulled-back sheaf,
compatibly with its graded structure. -/
@[ega "II 1.7.5"]
noncomputable def symmetricAlgebraPullbackIso :
    SymmetricAlgebraPullbackComparison f F
      (ringedSpaceAlgebras Y F)
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)) :=
  { pieceIso := pullbackPieceIso f
      (isSymmetricAlgebra_pullbackGradedAlgebra f
        (ringedSpaceAlgebras Y F).symmetric_isSymmetricAlgebra).isUniversal
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)).symmetric_isSymmetricAlgebra.isUniversal
    sheafIso := pullbackSigmaIso f
      (isSymmetricAlgebra_pullbackGradedAlgebra f
        (ringedSpaceAlgebras Y F).symmetric_isSymmetricAlgebra).isUniversal
      (ringedSpaceAlgebras X ((pullbackFunctor f).obj F)).symmetric_isSymmetricAlgebra.isUniversal
    sheafIso_ι := pullbackSigmaIso_ι f _ _
    map_mul := pullbackPieceIso_mul f _ _
    map_one := pullbackPieceIso_one f _ _
    map_generator := pullbackPieceIso_generator f _ _ }

end AlgebraicGeometry

end
