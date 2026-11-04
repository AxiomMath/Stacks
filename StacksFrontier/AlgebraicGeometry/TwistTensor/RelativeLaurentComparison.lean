module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeVeroneseTwists

/-!
# The comparison `c` of Lemma 01O1

Let `r : T ⟶ Proj_S(𝒜)` be a morphism of schemes, for a quasi-coherent graded algebra `𝒜` generated
in degree one over every affine open of the base. The pullback `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd))`
of the `d`-divisible glued twists of [Stacks, Tag 01NR] is isomorphic, as a sheaf of graded
algebras, to the Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of an invertible module `ℒ`, given an
isomorphism `α : r^*𝒪(d) ≅ ℒ` in degree one.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.laurentComparison`: the comparison
  `c : r^*(⨁_n 𝒪(nd)) ≅ ⨁_n ℒ^{⊗ n}` of sheaves of graded algebras.

## Main results

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.existsUnique_theta_of_degreeOneIso`: for a
  quadruple and a family `v` whose triangle commutes for `laurentComparison`, there is an
  isomorphism `θ'` of sheaves of graded algebras solving the triangle, and it is the unique
  homomorphism that does.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.isIso_mulSheaf_pullbackTwistVeronese` and
  `isInvertible_pullbackTwistVeronese_piece`: the multiplications of `r^*(⨁_n 𝒪(nd))` are
  isomorphisms and its pieces are invertible, for a graded algebra generated in degree one.
* `Stacks.RingedSpace.mulSheaf_pullbackGradedAlgebra`: the morphism-level multiplication of a
  pulled-back sheaf of graded algebras is the multiplication of the original, pulled back and
  conjugated by the comparison of [Stacks, Tag 01CD].
* `Stacks.RingedSpace.isIso_mulSheaf_pullbackGradedAlgebra`: the multiplications of `f^*A` are
  isomorphisms as soon as those of `A` are.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.GradedVeronese
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.RingedSpace

section PullbackMul

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- **The descent of the multiplication of a sheaf of graded algebras to the tensor product sheaf
is `SheafOfModules.GradedAlgebra.mulSheaf`.** -/
theorem ofBilinearSheaf_mul (i j : ℤ) :
    ofBilinearSheaf (A.mul i j) = SheafOfModules.GradedAlgebra.mulSheaf A i j :=
  tensor_hom_ext fun U x y ↦
    (ofBilinearSheaf_unit_tmul (A.mul i j) U x y).trans
      (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j U x y).symm

/-- The morphism-level multiplication of `f^*A` is the pulled-back bilinear map of `A`, read out of
the tensor product sheaf. -/
theorem mulSheaf_pullbackGradedAlgebra_eq (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackGradedAlgebra f A) i j =
      pullbackBilinearHom f (A.mul i j) :=
  tensor_hom_ext fun U x y ↦
    SheafOfModules.GradedAlgebra.mulSheaf_unit (pullbackGradedAlgebra f A) i j U x y

/-- **The morphism-level multiplication of `f^*A` is the multiplication of `A`, pulled back and
conjugated by the comparison of [Stacks, Tag 01CD].** -/
theorem mulSheaf_pullbackGradedAlgebra (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackGradedAlgebra f A) i j =
      inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
        (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.mulSheaf A i j) :=
  (mulSheaf_pullbackGradedAlgebra_eq f A i j).trans
    (congrArg (fun z ↦ inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
      (pullbackFunctor f).map z) (ofBilinearSheaf_mul A i j))

/-- The multiplications of `f^*A` are isomorphisms as soon as those of `A` are. -/
theorem isIso_mulSheaf_pullbackGradedAlgebra (i j : ℤ)
    (h : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A i j)) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (pullbackGradedAlgebra f A) i j) := by
  have hiso : IsIso (inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
      (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.mulSheaf A i j)) :=
    isIso_comp_of _ _ IsIso.inv_isIso
      (Iso.isIso_hom ((pullbackFunctor f).mapIso
        (@asIso _ _ _ _ (SheafOfModules.GradedAlgebra.mulSheaf A i j) h)))
  exact Eq.mpr (congrArg IsIso (mulSheaf_pullbackGradedAlgebra f A i j)) hiso

/-- The multiplications of `f^*A` are isomorphisms as soon as the pullbacks of those of `A`
are. -/
theorem isIso_mulSheaf_pullbackGradedAlgebra_of_isIso_map (i j : ℤ)
    (h : IsIso ((pullbackFunctor f).map (SheafOfModules.GradedAlgebra.mulSheaf A i j))) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (pullbackGradedAlgebra f A) i j) := by
  have hiso : IsIso (inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
      (pullbackFunctor f).map (SheafOfModules.GradedAlgebra.mulSheaf A i j)) :=
    isIso_comp_of _ _ IsIso.inv_isIso h
  exact Eq.mpr (congrArg IsIso (mulSheaf_pullbackGradedAlgebra f A i j)) hiso

end PullbackMul

end Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.RelativeVeroneseTwists

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A) (d : ℤ)
  {T : Scheme.{u}} (g : T ⟶ (relativeProj A).scheme)

/-- The multiplications of `r^*(⨁_n 𝒪(nd))` are isomorphisms, for a quasi-coherent graded
algebra generated in degree one over every affine open of the base. -/
theorem isIso_mulSheaf_pullbackTwistVeronese
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf (pullbackTwistVeronese D d g) n m) :=
  Stacks.RingedSpace.isIso_mulSheaf_pullbackGradedAlgebra (ringedSpaceHom g) (twistVeronese D d)
    n m (isIso_mulSheaf_twistVeronese D d hgen n m)

/-- Every piece `r^*𝒪(nd)` of `r^*(⨁_n 𝒪(nd))` is invertible, for a quasi-coherent graded
algebra generated in degree one over every affine open of the base. -/
theorem isInvertible_pullbackTwistVeronese_piece
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((pullbackTwistVeronese D d g).piece n) := by
  have := isInvertible_twistVeronese_piece D d hgen n
  exact Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj (ringedSpaceHom g)
    ((twistVeronese D d).piece n)

/-- **The comparison `c` of [Stacks, Tag 01O1]**: an isomorphism

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras, for a quasi-coherent graded algebra generated in degree
one over every affine open of the base and an invertible `𝒪_T`-module `ℒ` identified with `r^*𝒪(d)`
by `α`. -/
def laurentComparison
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    {Lc : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Lc]
    (α : (pullbackTwistVeronese D d g).piece 1 ≅ Lc) :
    pullbackTwistVeronese D d g ≅ laurent Lc :=
  Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso (pullbackTwistVeronese D d g) Lc α
    (isIso_mulSheaf_pullbackTwistVeronese D d g hgen)
    (isInvertible_pullbackTwistVeronese_piece D d g hgen 0)

/-- The degreewise components of the comparison are
`...GradedLaurentRecognition.pieceIso`. -/
theorem laurentComparison_hom_app
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    {Lc : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Lc]
    (α : (pullbackTwistVeronese D d g).piece 1 ≅ Lc) (n : ℤ) :
    (laurentComparison D d g hgen α).hom.app n =
      (Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso
        (pullbackTwistVeronese D d g) Lc α
        (isIso_mulSheaf_pullbackTwistVeronese D d g hgen)
        (isInvertible_pullbackTwistVeronese_piece D d g hgen 0) n).hom :=
  rfl

variable {S' : Scheme.{u}} {f : T ⟶ S'}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)} {e : ℤ}

/-- Let `(f : T → S', e, ℒ, ψ)` be a quadruple, `r : T ⟶ Proj_S(𝒜)` a morphism,
`v_n : f^*ℬ_{ne} ⟶ r^*𝒪(nd)` a family of morphisms and `α : r^*𝒪(d) ≅ ℒ` an isomorphism. If the
triangle commutes for the comparison `laurentComparison` built out of `α`, there is an isomorphism

`θ' : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras solving the triangle, and it is the unique homomorphism of
graded algebras that does. -/
theorem existsUnique_theta_of_degreeOneIso
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤)
    (P : Quadruple f B e)
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e)) ⟶
      (pullbackTwistVeronese D d g).piece n)
    (α : (pullbackTwistVeronese D d g).piece 1 ≅ P.L)
    (hv : ∀ n : ℤ, v n ≫ (laurentComparison D d g hgen α).hom.app n = P.twisting.app n) :
    ∃ θ' : pullbackTwistVeronese D d g ≅ laurent P.L,
      (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
        ∃! Θ : pullbackTwistVeronese D d g ⟶ laurent P.L,
          ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n :=
  ⟨laurentComparison D d g hgen α, hv,
    Quadruple.existsUnique_theta P (pullbackTwistVeronese D d g) v hv⟩

end Stacks.AlgebraicGeometry.RelativeVeroneseTwists

end
