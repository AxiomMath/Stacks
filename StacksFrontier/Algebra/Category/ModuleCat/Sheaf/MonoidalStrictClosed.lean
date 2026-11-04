module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Homology.InternalHomComplex

/-!
# The strict monoidal structure on sheaves of modules is closed

Let `(C, 𝒪)` be a ringed site. The monoidal structure on `Mod(𝒪)` whose tensor product is the
tensor product sheaf of [Stacks, Tag 01CA] on the nose — `Strict.monoidalCategory` — is
**closed**, and consequently so is the monoidal category of complexes of `𝒪`-modules formed over
it, with internal hom the internal Hom complex. Complexes over it are also symmetric, for the
Koszul braiding.

Nothing is reproved. `Mod(𝒪)` already carries a closed structure for the *re-seated* monoidal
structure `SheafOfModules.monoidalCategorySheafTensor`, obtained from Day's reflection theorem;
the two structures have naturally isomorphic tensor bifunctors
(`Stacks.SheafOfModules.Strict.tensorLeftIsoSheafTensor`), and a right adjoint of one left
adjoint is a right adjoint of any functor isomorphic to it. Closedness, unlike a monoidal
structure, depends on the tensor bifunctor alone and not on the associators and unitors, which is
why this transport is available where an identification of the two monoidal structures is not.
Complexes are then closed by
`CochainComplex.monoidalClosed`, which needs of the base category exactly the instances that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalStrictColimits.lean` supplies.

## Main definitions

* `Stacks.SheafOfModules.Strict.sheafTensorIhom` and
  `Stacks.SheafOfModules.Strict.sheafTensorIhomAdjunction`: the internal hom of the re-seated
  structure and its tensor-hom adjunction, named so that they can be read at the strict spelling.
* `Stacks.SheafOfModules.Strict.strictClosed` and
  `Stacks.SheafOfModules.Strict.strictMonoidalClosed`: `Mod(𝒪)` is closed for the strict tensor
  product.
* `Stacks.SheafOfModules.Strict.monoidalClosedCochainComplex`: the monoidal category of complexes
  of `𝒪`-modules over the strict tensor product is closed, with internal hom
  `CochainComplex.internalHomComplex`.
* `Stacks.SheafOfModules.Strict.symmetricCategoryCochainComplex`: that monoidal category is
  symmetric.

## Implementation notes

The three monoidal structures on `Mod(𝒪)` that meet here have the same tensor product on objects
but are distinct terms, and instance synthesis does not cross between them. Each instance below
is therefore ascribed at the spelling its consumer names — the symmetry of the strict structure at
`monoidalCategory` rather than at `Strict.monoidalCategory`, the adjunction's left
adjoint as `(Tensor.sheafTensor R).obj D` rather than as `tensorLeft D` for the re-seated
structure — with the definitional equality crossing at the `:=`. The `∀`-quantified graded-object
hypotheses of the monoidal structure on complexes are supplied by name rather than synthesized,
as they are where that structure is built.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0A5Y](https://stacks.math.columbia.edu/tag/0A5Y)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

/-- The internal hom of the re-seated monoidal structure on `Mod(𝒪)`, as a functor. Naming it
here lets the adjunction below be stated without the re-seated structure in scope. -/
def sheafTensorIhom (D : Mod R) : Mod R ⥤ Mod R :=
  let := SheafOfModules.monoidalCategorySheafTensor R
  let := SheafOfModules.monoidalClosedSheafTensor R
  ihom D

/-- **The tensor-hom adjunction of [Stacks, Tag 03EO] for the tensor product sheaf.** The left
adjoint is written as the tensor bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` applied to
`D`, which is what both monoidal structures on `Mod(𝒪)` have as their tensor product. -/
def sheafTensorIhomAdjunction (D : Mod R) :
    (Stacks.SheafOfModules.Tensor.sheafTensor R).obj D ⊣ sheafTensorIhom R D :=
  let := SheafOfModules.monoidalCategorySheafTensor R
  let := SheafOfModules.monoidalClosedSheafTensor R
  ihom.adjunction D

/-- **`Mod(𝒪)` is closed for the strict tensor product**, at each object: the internal hom of the
re-seated structure is a right adjoint of strict tensoring by `D`, the two left adjoints being
isomorphic by `Stacks.SheafOfModules.Strict.tensorLeftIsoSheafTensor`. -/
@[instance_reducible]
def strictClosed (D : Mod R) :
    letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
    Closed D :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  { rightAdj := sheafTensorIhom R D
    adj := Adjunction.ofNatIsoLeft (sheafTensorIhomAdjunction R D)
      (tensorLeftIsoSheafTensor R D).symm }

/-- **`Mod(𝒪)` is monoidal closed for the tensor product of [Stacks, Tag 01CA]** in the strict
spelling, in which the tensor product is the tensor product sheaf on the nose. -/
@[instance_reducible]
def strictMonoidalClosed :
    letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
    MonoidalClosed (Mod R) :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  { closed := fun D => strictClosed R D }

/-- **The monoidal category of complexes of `𝒪`-modules over the tensor product of
[Stacks, Tag 01CA] is closed**, with internal hom the internal Hom complex
`CochainComplex.internalHomComplex`: in degree `n` the product over `p` of the internal hom
sheaves `SheafHom(K^p, L^{p + n})`, with the Hom-complex differential. -/
@[instance_reducible]
def monoidalClosedCochainComplex :
    letI := monoidalCategoryCochainComplex R
    MonoidalClosed (CochainComplex (Mod R) ℤ) :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : MonoidalClosed (Mod R) := strictMonoidalClosed R
  let : ∀ X₁ X₂ : GradedObject ℤ (Mod R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  CochainComplex.monoidalClosed (A := Mod R)

/-- **The monoidal category of complexes of `𝒪`-modules over the tensor product of
[Stacks, Tag 01CA] is symmetric**, the commutativity constraint being the Koszul braiding. -/
@[instance_reducible]
def symmetricCategoryCochainComplex :
    letI := monoidalCategoryCochainComplex R
    SymmetricCategory (CochainComplex (Mod R) ℤ) :=
  letI : MonoidalCategory (Mod R) := monoidalCategory R.obj (isSheaf_ringSheaf R)
  letI : MonoidalPreadditive (Mod R) := monoidalPreadditiveRingSheaf R
  letI : SymmetricCategory (Mod R) :=
    symmetricCategory R.obj (isSheaf_ringSheaf R)
  let : ∀ X₁ X₂ : GradedObject ℤ (Mod R), GradedObject.HasTensor X₁ X₂ :=
    fun _ _ => inferInstance
  let : ∀ X₁ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).obj X₁) := fun X₁ => preservesColimit_tensorLeft R _ X₁
  let : ∀ X₂ : Mod R, PreservesColimit (Functor.empty.{0} (Mod R))
      ((curriedTensor (Mod R)).flip.obj X₂) := fun X₂ => preservesColimit_tensorRight R _ X₂
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := hasGoodTensor₁₂Tensor R
  let : ∀ X₁ X₂ X₃ : GradedObject ℤ (Mod R),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := hasGoodTensorTensor₂₃ R
  let : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := hasTensor₄ObjExt R
  CochainComplex.symmetricCategory (Mod R)

end Stacks.SheafOfModules.Strict

end

end
