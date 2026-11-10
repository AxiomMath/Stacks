module

public import StacksFrontier.AlgebraicGeometry.RelativeProjMapDomain.AffineGlobalSections
public import StacksFrontier.RingTheory.GradedIsomScheme

/-!
# The graded multiplication datum of global sections of a sheaf of graded algebras

A quasi-coherent graded `𝒪_S`-algebra `A`
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`) has a graded multiplication
datum of global sections over `Γ(S, 𝒪_S)` in the sense of
`Stacks.GradedIsomScheme.GradedMulDatum`: the `Γ(S, 𝒪_S)`-modules `Γ(S, A_n)`, `n ≥ 0`, with the
multiplication and the unit of `A` over `S`. Over an affine base this datum loses nothing: the
homomorphisms of graded algebras `A ⟶ B` are the homomorphisms of the data, and those that are
isomorphisms in every degree are the isomorphisms of the data.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.globalDatum`: the datum.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.globalDatumHomEquiv`:
  over an affine base, homomorphisms of graded algebras are homomorphisms of the data.
* `Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.globalDatumIsoEquiv`:
  over an affine base, homomorphisms that are isomorphisms in every degree are isomorphisms of the
  data.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.AlgebraicGeometry

open RelativeProjBridge RelativeProjMapDomain GradedIsomScheme

namespace RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **The graded multiplication datum of global sections** of a sheaf of graded algebras: the
`Γ(S, 𝒪_S)`-modules `Γ(S, A_n)` with the multiplication and the unit of `A` over `S`. -/
def globalDatum : GradedMulDatum Γ(S, ⊤) where
  piece n := Γ(A.piece (n : ℤ), ⊤)
  mul i j := LinearMap.mk₂ Γ(S, ⊤) (fun a b => (A.mul (i : ℤ) (j : ℤ)).app ⊤ a b)
    (fun a a' b => by simp only [map_add, AddMonoidHom.add_apply])
    (fun r a b => (A.mul (i : ℤ) (j : ℤ)).map_smul_left ⊤ r a b)
    (fun a b b' => map_add _ _ _)
    (fun r a b => (A.mul (i : ℤ) (j : ℤ)).map_smul_right ⊤ r a b)
  one := A.one ⊤

/-- The multiplication of `A.globalDatum` in degrees `i` and `j` is the multiplication of `A` on
global sections. -/
@[simp]
theorem globalDatum_mul (i j : ℕ) (a : Γ(A.piece (i : ℤ), ⊤)) (b : Γ(A.piece (j : ℤ), ⊤)) :
    A.globalDatum.mul i j a b = (A.mul (i : ℤ) (j : ℤ)).app ⊤ a b := rfl

/-- The unit of `A.globalDatum` is the unit of `A` on global sections. -/
@[simp]
theorem globalDatum_one : A.globalDatum.one = A.one ⊤ := rfl

end RelativeProjBridge.SheafGradedAlgebra

namespace RelativeProjMapDomain.SheafGradedAlgebraHom

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S}

/-- **The homomorphism of global sections data** of a homomorphism of graded algebras. -/
def globalDatumHom (γ : SheafGradedAlgebraHom A B) :
    GradedMulDatum.Hom A.globalDatum B.globalDatum where
  app n := γ.globalSectionsMap n
  app_mul i j a b := γ.globalSectionsMap_mul i j a b
  app_one := γ.globalSectionsMap_one

/-- In degree `n`, `γ.globalDatumHom` is the map of global sections of `γ.app n`. -/
@[simp]
theorem globalDatumHom_app (γ : SheafGradedAlgebraHom A B) (n : ℕ) (a : Γ(A.piece (n : ℤ), ⊤)) :
    γ.globalDatumHom.app n a = (γ.app n).app ⊤ a := rfl

variable [IsAffine S]

/-- **Over an affine base, homomorphisms of graded algebras are homomorphisms of their global
sections data.** -/
def globalDatumHomEquiv :
    SheafGradedAlgebraHom A B ≃ GradedMulDatum.Hom A.globalDatum B.globalDatum where
  toFun γ := γ.globalDatumHom
  invFun F := ofGlobalSections F.app F.app_mul F.app_one
  left_inv γ := ext_of_isAffine fun n a =>
    ofGlobalSections_app_app_top (A := A) (B := B) γ.globalSectionsMap _ _ n a
  right_inv F := by
    ext n a
    exact ofGlobalSections_app_app_top (A := A) (B := B) F.app F.app_mul F.app_one n a

/-- `globalDatumHomEquiv` sends a homomorphism `γ` to `γ.globalDatumHom`. -/
@[simp]
theorem globalDatumHomEquiv_apply (γ : SheafGradedAlgebraHom A B) :
    globalDatumHomEquiv γ = γ.globalDatumHom := rfl

/-- **Over an affine base, homomorphisms of graded algebras that are isomorphisms in every degree
are isomorphisms of their global sections data.** -/
def globalDatumIsoEquiv :
    {γ : SheafGradedAlgebraHom A B // ∀ n : ℤ, IsIso (γ.app n)} ≃
      GradedMulDatum.Iso A.globalDatum B.globalDatum where
  toFun γ := GradedMulDatum.Iso.ofBijective γ.1.globalDatumHom
    ((forall_isIso_app_iff γ.1).1 γ.2)
  invFun I := ⟨globalDatumHomEquiv.symm I.hom, (forall_isIso_app_iff _).2 fun n => by
    refine Function.bijective_iff_has_inverse.2 ⟨I.inv.app n, fun x => ?_, fun y => ?_⟩
    · refine Eq.trans ?_ (I.hom_inv n x)
      exact congrArg (I.inv.app n)
        (ofGlobalSections_app_app_top (A := A) (B := B) I.hom.app I.hom.app_mul I.hom.app_one n x)
    · refine Eq.trans ?_ (I.inv_hom n y)
      exact ofGlobalSections_app_app_top (A := A) (B := B) I.hom.app I.hom.app_mul I.hom.app_one n
        (I.inv.app n y)⟩
  left_inv γ := Subtype.ext (globalDatumHomEquiv.symm_apply_apply γ.1)
  right_inv I := GradedMulDatum.Iso.ext (by
    simp only
    exact globalDatumHomEquiv.apply_symm_apply I.hom)

/-- In degree `n`, the isomorphism `globalDatumIsoEquiv γ` is the map of global sections of
`γ.1.app n`. -/
@[simp]
theorem globalDatumIsoEquiv_hom_app
    (γ : {γ : SheafGradedAlgebraHom A B // ∀ n : ℤ, IsIso (γ.app n)}) (n : ℕ)
    (a : Γ(A.piece (n : ℤ), ⊤)) :
    (globalDatumIsoEquiv γ).hom.app n a = (γ.1.app n).app ⊤ a := rfl

end RelativeProjMapDomain.SheafGradedAlgebraHom

end Stacks.AlgebraicGeometry

end
