module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf

/-!
# The values of a right derived functor with values in sheaves of modules

Let `π : 𝒜 ⥤ Mod(R)` be an additive functor from an abelian category with injective resolutions
to the sheaves of modules over a sheaf of rings `R` on a site `C`. Its right derived functors are
the sheafifications of the right derived functors of the composite `𝒜 ⥤ PMod(R)` with the
inclusion of sheaves into presheaves, and the value of the latter at an object `V` of `C` is the
right derived functor of the value of `π` at `V`:

`Rᵠπ = a ∘ Rᵠ(π ⋙ forget)` and `(Rᵠ(π ⋙ forget)(M))(V) = Rᵠ(Γ(V, π(-)))(M)`.

Both are pulled out of the right derived functor because they are exact: sheafification of
presheaves of modules preserves homology, and so does evaluation at an object. The first
statement is the argument of **Stacks 072W**, which this generalizes from the direct image along
a continuous functor to an arbitrary additive functor; the second is that evaluation of presheaves
of modules is exact.

## Main definitions

* `Stacks.SheafOfModules.rightDerivedIsoSheafificationForget`: `Rᵠπ ≅ a ∘ Rᵠ(π ⋙ forget)`.
* `Stacks.SheafOfModules.rightDerivedForgetObjObjIso`: the value at `V` of `Rᵠ(π ⋙ forget)(M)`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t r v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  (π : A ⥤ SheafOfModules.{t} R) [π.Additive]

/-- **A right derived functor with values in sheaves of modules is the sheafification of the
right derived functor of its underlying presheaves.** `π` is its underlying presheaves followed by
sheafification, the counit of the sheafification adjunction being invertible, and sheafification
preserves homology. -/
def rightDerivedIsoSheafificationForget (q : ℕ) :
    π.rightDerived q ≅ (π ⋙ SheafOfModules.forget.{t} R).rightDerived q ⋙
      PresheafOfModules.sheafification.{t} (𝟙 R.obj) :=
  haveI : (PresheafOfModules.sheafification.{t} (𝟙 R.obj)).PreservesHomology :=
    sheafification_preservesHomology R
  haveI : (PresheafOfModules.sheafification.{t} (𝟙 R.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).left_adjoint_additive
  let cI : (SheafOfModules.forget.{t} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.sheafification.{t} (𝟙 R.obj) ≅ 𝟭 (SheafOfModules.{t} R) :=
    asIso (PresheafOfModules.sheafificationAdjunction.{t} (𝟙 R.obj)).counit
  haveI : ((π ⋙ SheafOfModules.forget.{t} R) ⋙
      PresheafOfModules.sheafification.{t} (𝟙 R.obj)).Additive := Functor.additive_of_iso
    ((Functor.rightUnitor π).symm ≪≫ Functor.isoWhiskerLeft π cI.symm ≪≫ Iso.refl _)
  Functor.rightDerivedIsoOfNatIso
      ((Functor.rightUnitor π).symm ≪≫ Functor.isoWhiskerLeft π cI.symm ≪≫ Iso.refl _) q ≪≫
    Functor.rightDerivedCompIso (π ⋙ SheafOfModules.forget.{t} R)
      (PresheafOfModules.sheafification.{t} (𝟙 R.obj)) q

/-- **The value at an object of the right derived functor of the underlying presheaves is the
right derived functor of the value.** Evaluation of presheaves of modules at `V` preserves
homology, so it can be pulled out of the right derived functor. -/
def rightDerivedForgetObjObjIso (q : ℕ) (M : A) (V : C) :
    (((π ⋙ SheafOfModules.forget.{t} R).rightDerived q).obj M).obj (op V) ≅
      ((π ⋙ SheafOfModules.forget.{t} R ⋙
        PresheafOfModules.evaluation.{t} R.obj (op V)).rightDerived q).obj M :=
  ((Functor.rightDerivedCompIso (π ⋙ SheafOfModules.forget.{t} R)
    (PresheafOfModules.evaluation.{t} R.obj (op V)) q).app M).symm

end Stacks.SheafOfModules

end
