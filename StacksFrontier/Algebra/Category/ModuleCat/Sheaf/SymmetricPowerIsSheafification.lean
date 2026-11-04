module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The symmetric power of a sheaf of modules is a sheafification

Let `O` be a sheaf of commutative rings on a site, `F` a sheaf of `O`-modules and `A` a bundle of
tensor, exterior and symmetric algebras on `F`
(`SheafOfModules.TensorExteriorSymmetricAlgebras`). The degree-`n` symmetric power
`Symⁿ F = A.symmetricPower n` is the sheafification of the presheaf of sectionwise symmetric
powers

`U ↦ Symⁿ_{O(U)}(F(U))`,

along the canonical comparison morphism
`SheafOfModules.TensorExteriorSymmetricAlgebras.symPowComparison`.

## Main results

* `SheafOfModules.isIso_sheafification_symPowComparison`: the comparison morphism is an
  isomorphism after sheafification.
* `SheafOfModules.sheafificationHomEquiv_pieceIso`: the comparison morphism is the one the
  universal property of the symmetric algebra produces.
* `Stacks.GradedAlgebra.homogeneousProd_map`: a degreewise map of graded algebras of presheaves
  of modules preserving the unit and products commutes with the ordered product of degree-one
  local sections.
* `PresheafOfModules.homogeneousProd_symmetricAlgebraGen`: in the sectionwise symmetric algebra
  the ordered product of degree-one generators is the product of the generators.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe v u w a

namespace Stacks.GradedAlgebra

section Transfer

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc Qc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) (B : Stacks.GradedAlgebra Qc)

/-- A degreewise map between graded algebras of presheaves of modules which carries the unit to
the unit and products of homogeneous local sections to products commutes with the ordered
product of degree-one local sections over a fixed object. -/
theorem homogeneousProd_map (X : Cᵒᵖ) (ψ : ∀ n : ℤ, (Pc n).obj X → (Qc n).obj X)
    (hone : ψ 0 (A.one.eval X) = B.one.eval X)
    (hmul : ∀ (i j : ℤ) (x : (Pc i).obj X) (y : (Pc j).obj X),
      ψ (i + j) ((A.mul i j).app X x y) = (B.mul i j).app X (ψ i x) (ψ j y))
    (n : ℕ) : ∀ z : Fin n → (Pc 1).obj X,
      ψ (n : ℤ) (A.homogeneousProd X n z) = B.homogeneousProd X n fun i => ψ 1 (z i) := by
  induction n with
  | zero => exact fun _ ↦ hone
  | succ n ih =>
      exact fun z ↦ (hmul (n : ℤ) 1 _ _).trans
        (congrArg (fun t ↦ (B.mul (n : ℤ) 1).app X t (ψ 1 (z (Fin.last n))))
          (ih fun i ↦ z i.castSucc))

end Transfer

end Stacks.GradedAlgebra

namespace PresheafOfModules

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- In the sectionwise symmetric algebra the ordered product of degree-one local sections is the
product of their images in the symmetric algebra of the sections. -/
theorem symPowIntVal_homogeneousProd (X : Cᵒᵖ) (n : ℕ) :
    ∀ z : Fin n → (symPowInt (1 : ℤ) F).obj X,
      symPowIntVal ((symPowIntGradedAlgebra F).homogeneousProd X n z) =
        ∏ i : Fin n, symPowIntVal (z i) := by
  induction n with
  | zero => exact fun _ ↦ symPowIntVal_one F X
  | succ n ih =>
      intro z
      show symPowIntVal ((symPowIntMul F (n : ℤ) 1).app X
          ((symPowIntGradedAlgebra F).homogeneousProd X n fun i ↦ z i.castSucc)
          (z (Fin.last n))) = _
      rw [symPowIntVal_mul, ih fun i ↦ z i.castSucc, Fin.prod_univ_castSucc]

/-- The ordered product, in the sectionwise symmetric algebra, of the degree-one generators
attached to local sections `s i` is the element `∏ i, ι (s i)` of the degree-`n` sectionwise
symmetric power. -/
theorem homogeneousProd_symmetricAlgebraGen (X : Cᵒᵖ) (n : ℕ) (s : Fin n → F.obj X) :
    (symPowIntGradedAlgebra F).homogeneousProd X n
          (fun i => Hom.app (symPowIntGen F) X (s i)) =
        (⟨∏ i : Fin n, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i),
          SymmetricAlgebra.prod_ι_mem _ s⟩ :
            SymPow.symmetricPower n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :=
  symPowIntVal_injective (n : ℤ) F
    (Eq.trans (symPowIntVal_homogeneousProd F X n _)
      (Finset.prod_congr rfl fun i _ ↦ symPowIntVal_gen F X (s i)))

end Sectionwise

end PresheafOfModules

namespace SheafOfModules

section Sheafification

open PresheafOfModules Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- The degree-one generator of `Sym(F)` is the sheafification unit applied to the sectionwise
degree-one generator. -/
theorem sheafifiedSymmetricGenerator_unit (X : Cᵒᵖ) (s : F.val.obj X) :
    Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (1 : ℤ) F.val)) X
        (Hom.app (symPowIntGen F.val) X s) =
      (sheafifiedSymmetricGenerator J F).val.app X s :=
  Eq.trans ((symPowIntGradedAlgebra F.val).sheafifyGen_unit
      (𝟙 (toRingCat J Osharp).obj) (symPowIntGen F.val) X s).symm
    (congrArg (fun t ↦ ((symPowIntGradedAlgebra F.val).sheafifyGen
        (𝟙 (toRingCat J Osharp).obj) (symPowIntGen F.val)).val.app X t)
      (sheafifiedValIso_inv_apply J F X s).symm)

/-- The sheafification unit carries the ordered product of degree-one local sections of the
sectionwise symmetric algebra to the ordered product of their images in `Sym(F)`. -/
theorem sheafifyUnit_homogeneousProd (n : ℕ) (X : Cᵒᵖ)
    (z : Fin n → (symPowInt (1 : ℤ) F.val).obj X) :
    Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (n : ℤ) F.val)) X
        ((symPowIntGradedAlgebra F.val).homogeneousProd X n z) =
      (sheafifiedSymmetricAlgebra J F).toPresheafGradedAlgebra.homogeneousProd X n
        (fun i => Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (1 : ℤ) F.val)) X (z i)) :=
  (symPowIntGradedAlgebra F.val).homogeneousProd_map
    (sheafifiedSymmetricAlgebra J F).toPresheafGradedAlgebra X
    (fun m y ↦ Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
      (symPowInt m F.val)) X y)
    ((symPowIntGradedAlgebra F.val).sheafify_one_eval
      (𝟙 (toRingCat J Osharp).obj) X).symm
    (fun i j x y ↦ ((symPowIntGradedAlgebra F.val).sheafify_mul_unit
      (𝟙 (toRingCat J Osharp).obj) i j X x y).symm)
    n z

/-- The sheafification unit carries the element `∏ i, ι (s i)` of the degree-`n` sectionwise
symmetric power to the ordered product of the images of the `s i` under the degree-one generator
of `Sym(F)`. -/
theorem sheafifyUnit_prod_ι (n : ℕ) (X : Cᵒᵖ) (s : Fin n → F.val.obj X) :
    Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
          (symPowInt (n : ℤ) F.val)) X
        (⟨∏ i : Fin n, SymmetricAlgebra.ι
            ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (F.val.obj X) (s i),
          SymmetricAlgebra.prod_ι_mem _ s⟩ :
            SymPow.symmetricPower n
              ((Osharp.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj X) (F.val.obj X)) =
      (sheafifiedSymmetricAlgebra J F).toPresheafGradedAlgebra.homogeneousProd X n
        fun i => (sheafifiedSymmetricGenerator J F).val.app X (s i) :=
  Eq.trans (congrArg (Hom.app (PresheafOfModules.sheafifyUnit (𝟙 (toRingCat J Osharp).obj)
        (symPowInt (n : ℤ) F.val)) X)
      (homogeneousProd_symmetricAlgebraGen F.val X n s).symm)
    (Eq.trans (sheafifyUnit_homogeneousProd J F n X
        fun i => Hom.app (symPowIntGen F.val) X (s i))
      (congrArg ((sheafifiedSymmetricAlgebra J F).toPresheafGradedAlgebra.homogeneousProd X n)
        (funext fun i => sheafifiedSymmetricGenerator_unit J F X (s i))))

/-- The sheafification adjunction carries the canonical comparison `Symⁿ(F) ≅ A.symmetricPower n`,
between the degree-`n` piece of the sheafified sectionwise symmetric algebra and the degree-`n`
symmetric power of any bundle `A` of algebras on `F`, to
`SheafOfModules.TensorExteriorSymmetricAlgebras.symPowComparison`. -/
theorem sheafificationHomEquiv_pieceIso (A : TensorExteriorSymmetricAlgebras J F) (n : ℕ) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj))
        ((GradedAlgebra.IsUniversal.pieceIso
          (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
          A.symmetric_isSymmetricAlgebra.isUniversal (n : ℤ)).hom) =
      A.symPowComparison n := by
  refine PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext (SymPow.ext_of_prod_ι fun s ↦ ?_)
  refine Eq.trans (congrArg (fun t ↦ ((GradedAlgebra.IsUniversal.pieceIso
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
      A.symmetric_isSymmetricAlgebra.isUniversal (n : ℤ)).hom).val.app X t)
    (sheafifyUnit_prod_ι J F n X s)) ?_
  refine Eq.trans ((sheafifiedSymmetricAlgebra J F).toPresheafGradedAlgebra.homogeneousProd_map
    A.symmetric.toPresheafGradedAlgebra X
    (fun m y ↦ ((GradedAlgebra.IsUniversal.pieceIso
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
      A.symmetric_isSymmetricAlgebra.isUniversal m).hom).val.app X y)
    (GradedAlgebra.IsUniversal.pieceIso_one
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
      A.symmetric_isSymmetricAlgebra.isUniversal X)
    (fun i j x y ↦ GradedAlgebra.IsUniversal.pieceIso_mul
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
      A.symmetric_isSymmetricAlgebra.isUniversal i j X x y) n _) ?_
  refine Eq.trans (congrArg (A.symmetric.toPresheafGradedAlgebra.homogeneousProd X n)
    (funext fun i ↦ congrArg (fun φ : F ⟶ A.symmetric.piece 1 ↦ φ.val.app X (s i))
      (GradedAlgebra.IsUniversal.pieceIso_generator
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
        A.symmetric_isSymmetricAlgebra.isUniversal))) ?_
  exact (Stacks.GradedAlgebra.cmpSections_prod_ι A.symmetric.toPresheafGradedAlgebra
    A.symmetricGenerator.val (fun X x y ↦ A.symmetric_isSymmetricAlgebra.1 X x y) n X s).symm

/-- The morphism out of the sheafification that the comparison morphism
`SheafOfModules.TensorExteriorSymmetricAlgebras.symPowComparison` induces is the canonical
comparison isomorphism. -/
theorem sheafificationHomEquiv_symm_symPowComparison
    (A : TensorExteriorSymmetricAlgebras J F) (n : ℕ) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)
          (P := symPowInt (n : ℤ) F.val)
          (F := A.symmetricPower n)).symm (A.symPowComparison n) =
      (GradedAlgebra.IsUniversal.pieceIso
        (isSymmetricAlgebra_sheafifiedSymmetricAlgebra J F).isUniversal
        A.symmetric_isSymmetricAlgebra.isUniversal (n : ℤ)).hom :=
  Eq.trans (congrArg (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (toRingCat J Osharp).obj)).symm (sheafificationHomEquiv_pieceIso J F A n).symm)
    (Equiv.symm_apply_apply _ _)

/-- The morphism `(PresheafOfModules.sheafification α).obj (U ↦ Symⁿ_{O(U)}(F(U))) ⟶ Symⁿ F`
induced by the comparison morphism
`SheafOfModules.TensorExteriorSymmetricAlgebras.symPowComparison` is an isomorphism: the
degree-`n` symmetric power of `F` is the sheafification of the presheaf of sectionwise degree-`n`
symmetric powers. -/
theorem isIso_sheafification_symPowComparison (A : TensorExteriorSymmetricAlgebras J F)
    (n : ℕ) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)
        (P := symPowInt (n : ℤ) F.val)
        (F := A.symmetricPower n)).symm (A.symPowComparison n)) := by
  rw [sheafificationHomEquiv_symm_symPowComparison J F A n]
  exact ⟨_, Iso.hom_inv_id _, Iso.inv_hom_id _⟩

end Sheafification

end SheafOfModules

end
