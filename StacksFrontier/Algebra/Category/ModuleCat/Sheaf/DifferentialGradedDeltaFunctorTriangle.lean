module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDistinguished
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryTriangulated
public import StacksFrontier.CategoryTheory.Triangulated.Functor

/-!
# The connecting morphism as a translate, and the image of a short exact sequence as a triangle

Let `X` be a ringed site and let `(A, d)` be a sheaf of differential graded algebras on it. For a
short exact sequence `0 → K --a--> L --b--> M → 0` of right differential graded `A`-modules, the
connecting morphism `δ = - p ∘ q⁻¹` of [Stacks, Tag 0FTB] is a morphism `F(M) ⟶ F(K[1])` of
`D(A, d)`, where `F` is the localization functor and `K[1]` is the chosen degree-one shift of
[Stacks, Tag 0FS5]. We identify `F(K[1])` with the translate `F(K)⟦1⟧` and show that `F`, with this
`δ`, is a `δ`-functor in the sense of [Stacks, Tag 0150]
(`CategoryTheory.Functor.DeltaFunctorStructure`).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.shiftTranslateIso`: the isomorphism
  `F(K[1]) ≅ F(K)⟦1⟧` of the image of the chosen shift with the translate of the image.
* `SheafOfModules.DifferentialGradedModule.shortExactδTranslate`: the connecting morphism
  `δ : F(M) ⟶ F(K)⟦1⟧` of a short exact sequence.
* `SheafOfModules.DifferentialGradedModule.homotopyConeTriangle`: the cone triangle
  `(K, L, C(f), f, i, -p)` in the homotopy category `K(Mod(A, d))`.
* `SheafOfModules.DifferentialGradedModule.ShiftQuotientCompatible`: the statement that the
  translation of `K(Mod(A, d))` agrees with the chosen differential graded shift on morphisms.
* `SheafOfModules.DifferentialGradedModule.deltaFunctorStructure`: the `δ`-functor structure on
  the localization functor `Mod(A, d) ⥤ D(A, d)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyConeTriangle_distinguished`: the cone
  triangle is distinguished in `K(Mod(A, d))` ([Stacks, Tag 09QU]).
* `SheafOfModules.DifferentialGradedModule.shortExactδTranslate_distinguished`: the triangle
  `(F K, F L, F M, F a, F b, δ)` of a short exact sequence is distinguished in `D(A, d)`.
* `SheafOfModules.DifferentialGradedModule.shortExactδTranslate_naturality`: the connecting
  morphism `δ` is natural in the short exact sequence.
* `SheafOfModules.DifferentialGradedModule.shiftQuotientCompatible`: the translation of
  `K(Mod(A, d))` agrees with the chosen differential graded shift on morphisms.

## References

* [Stacks Project, Tag 0FTB](https://stacks.math.columbia.edu/tag/0FTB)
* [Stacks Project, Tag 0150](https://stacks.math.columbia.edu/tag/0150)
* [Stacks Project, Tag 09QU](https://stacks.math.columbia.edu/tag/09QU)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ### The image of the chosen shift as a translate -/

/-- The isomorphism `F(M[1]) ≅ F(M)⟦1⟧` in `D(A, d)` between the image of the chosen degree-one
shift of a right differential graded module `M` and the translate of the image of `M`: the
object-level equality of [Stacks, Tag 0FS7] followed by the commutation of the localization functor
with the translation ([Stacks, Tag 0FT4]). -/
def shiftTranslateIso (M : DifferentialGradedModule.{u, v, w} A) :
    (moduleToDerivedCategory.{u, v, w} A).obj (shift M) ≅
      ((moduleToDerivedCategory.{u, v, w} A).obj M)⟦(1 : ℤ)⟧ :=
  eqToIso (congrArg (toDerivedCategory A).obj
      (HomotopyCategory.shiftFunctor_obj A M).symm) ≪≫
    ((toDerivedCategory A).commShiftIso (1 : ℤ)).app ((HomotopyCategory.quotient A).obj M)

/-- The connecting morphism `δ = - p ∘ q⁻¹ : F(S.X₃) ⟶ F(S.X₁)⟦1⟧` of [Stacks, Tag 0FTB] of a
short exact sequence `S`: the morphism `SheafOfModules.DifferentialGradedModule.shortExactδ`
followed by `shiftTranslateIso`. -/
def shortExactδTranslate {S : ShortComplex (DifferentialGradedModule.{u, v, w} A)}
    (hS : S.ShortExact) :
    (moduleToDerivedCategory.{u, v, w} A).obj S.X₃ ⟶
      ((moduleToDerivedCategory.{u, v, w} A).obj S.X₁)⟦(1 : ℤ)⟧ :=
  shortExactδ hS ≫ (shiftTranslateIso S.X₁).hom

/-- The cone triangle `(K, L, C(f), f, i, -p)` of a morphism `f` of right differential graded
modules, in the homotopy category `K(Mod(A, d))`. Its third arrow is the negative of the cone
projection of [Stacks, Tag 0FS5], read into the translate of `K` through the object-level equality
of [Stacks, Tag 0FS7]. -/
def homotopyConeTriangle {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    Triangle (HomotopyCategory.{u, v, w} A) :=
  Triangle.mk ((HomotopyCategory.quotient A).map f)
    ((HomotopyCategory.quotient A).map (conePackage f).inclusion)
    ((HomotopyCategory.quotient A).map (-(conePackage f).projection) ≫
      eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The cone triangle `homotopyConeTriangle f` is distinguished in `K(Mod(A, d))`
([Stacks, Tag 09QU]). -/
theorem homotopyConeTriangle_distinguished {K L : DifferentialGradedModule.{u, v, w} A}
    (f : K ⟶ L) :
    homotopyConeTriangle f ∈ distTriang (HomotopyCategory.{u, v, w} A) := by
  refine (rotate_distinguished_triangle (homotopyConeTriangle f)).2
    (isomorphic_distinguished _ (coneRotatedTriangle_distinguished f) _ ?_)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (-(eqToIso (HomotopyCategory.shiftFunctor_obj A K))) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · simp [homotopyConeTriangle, coneRotatedTriangle, Triangle.rotate]
  · simp [homotopyConeTriangle, coneRotatedTriangle, Triangle.rotate]

/-! ### The image of a short exact sequence is a distinguished triangle -/

/-- In `D(A, d)`, the image of the cone inclusion `S.X₂ ⟶ C(S.f)` followed by the image of the
comparison `q : C(S.f) ⟶ S.X₃` is the image of `S.g`. -/
theorem moduleToDerivedCategory_coneIncl_coneDescHom
    (S : ShortComplex (DifferentialGradedModule.{u, v, w} A)) :
    (moduleToDerivedCategory A).map (conePackage S.f).inclusion ≫
        (moduleToDerivedCategory A).map (coneDescHom S) =
      (moduleToDerivedCategory A).map S.g :=
  ((moduleToDerivedCategory A).map_comp _ _).symm.trans
    (congrArg (moduleToDerivedCategory A).map (coneIncl_coneDescHom S))

/-- In `D(A, d)`, the image of the comparison `q : C(S.f) ⟶ S.X₃` followed by the connecting
morphism `shortExactδTranslate hS` is the third arrow of the localized cone triangle. -/
theorem coneDescHom_comp_shortExactδTranslate
    {S : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (hS : S.ShortExact) :
    (toDerivedCategory A).map ((HomotopyCategory.quotient A).map
          (-(conePackage S.f).projection) ≫
        eqToHom (HomotopyCategory.shiftFunctor_obj A S.X₁).symm) ≫
      ((toDerivedCategory A).commShiftIso (1 : ℤ)).hom.app
        ((HomotopyCategory.quotient A).obj S.X₁) =
      (moduleToDerivedCategory A).map (coneDescHom S) ≫ shortExactδTranslate hS := by
  have := isIso_moduleToDerivedCategory_map_coneDescHom hS
  have h₁ : (moduleToDerivedCategory A).map (coneDescHom S) ≫ shortExactδ hS =
      (moduleToDerivedCategory A).map (-(conePackage S.f).projection) :=
    IsIso.hom_inv_id_assoc _ _
  have h₂ : ∀ (Z : derivedCategory.{u, v, w} A)
      (k : (moduleToDerivedCategory A).obj (shift S.X₁) ⟶ Z),
      (moduleToDerivedCategory A).map (coneDescHom S) ≫ shortExactδ hS ≫ k =
        (moduleToDerivedCategory A).map (-(conePackage S.f).projection) ≫ k := fun Z k => by
    rw [← Category.assoc, h₁]
  rw [Functor.map_comp, eqToHom_map, Category.assoc]
  dsimp only [shortExactδTranslate, shiftTranslateIso, Iso.trans_hom]
  rw [h₂]
  rfl

/-- For a short exact sequence `0 → K --a--> L --b--> M → 0` of right differential graded
modules, the triangle `(F K, F L, F M, F a, F b, δ)` with `δ = shortExactδTranslate hS` is
distinguished in `D(A, d)`. -/
@[stacks 0FTB "the distinguished-triangle axiom of the delta-functor"]
theorem shortExactδTranslate_distinguished
    {S : ShortComplex (DifferentialGradedModule.{u, v, w} A)} (hS : S.ShortExact) :
    Triangle.mk ((moduleToDerivedCategory.{u, v, w} A).map S.f)
        ((moduleToDerivedCategory.{u, v, w} A).map S.g) (shortExactδTranslate hS) ∈
      distTriang (derivedCategory.{u, v, w} A) := by
  refine isomorphic_distinguished _
    ((toDerivedCategory A).map_distinguished _ (homotopyConeTriangle_distinguished S.f)) _
    (Iso.symm (Triangle.isoMk ((toDerivedCategory A).mapTriangle.obj (homotopyConeTriangle S.f))
      (Triangle.mk ((moduleToDerivedCategory.{u, v, w} A).map S.f)
        ((moduleToDerivedCategory.{u, v, w} A).map S.g) (shortExactδTranslate hS))
      (Iso.refl _) (Iso.refl _)
      (@asIso _ _ _ _ ((moduleToDerivedCategory A).map (coneDescHom S))
        (isIso_moduleToDerivedCategory_map_coneDescHom hS)) ?_ ?_ ?_))
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (moduleToDerivedCategory_coneIncl_coneDescHom S).trans (Category.id_comp _).symm
  · exact (congrArg (fun m =>
        ((toDerivedCategory A).mapTriangle.obj (homotopyConeTriangle S.f)).mor₃ ≫ m)
      ((shiftFunctor (derivedCategory.{u, v, w} A) (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans (coneDescHom_comp_shortExactδTranslate hS))

/-! ### Naturality in the translate spelling -/

/-- The statement that the translation of `K(Mod(A, d))` agrees with the chosen differential
graded shift on morphisms, compatibly with the object-level equality of [Stacks, Tag 0FS7]. -/
def ShiftQuotientCompatible
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∀ {K K' : DifferentialGradedModule.{u, v, w} A} (φ : K ⟶ K'),
    (HomotopyCategory.quotient A).map (coneShiftHom φ) ≫
        eqToHom (HomotopyCategory.shiftFunctor_obj A K').symm =
      eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm ≫
        (shiftFunctor (HomotopyCategory.{u, v, w} A) (1 : ℤ)).map
          ((HomotopyCategory.quotient A).map φ)

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The translation of `K(Mod(A, d))` agrees with the chosen differential graded shift on
morphisms. -/
theorem shiftQuotientCompatible : ShiftQuotientCompatible.{u, v, w} A :=
  fun φ => quotient_map_coneShiftHom φ

/-- The identification of the image of the chosen shift with the translate of the image is
natural in the module. -/
theorem shiftTranslateIso_naturality
    {K K' : DifferentialGradedModule.{u, v, w} A} (φ : K ⟶ K') :
    (shiftTranslateIso K).hom ≫ ((moduleToDerivedCategory A).map φ)⟦(1 : ℤ)⟧' =
      (moduleToDerivedCategory A).map (coneShiftHom φ) ≫ (shiftTranslateIso K').hom := by
  have hnat := ((toDerivedCategory A).commShiftIso (1 : ℤ)).hom.naturality
    ((HomotopyCategory.quotient A).map φ)
  have hK := congrArg (toDerivedCategory A).map (shiftQuotientCompatible.{u, v, w} (A := A) φ)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map] at hK
  dsimp only [shiftTranslateIso, Iso.trans_hom, Functor.comp_map, Iso.app_hom,
    eqToIso.hom] at hnat ⊢
  simp only [Category.assoc]
  rw [← hnat, ← Category.assoc, ← Category.assoc, hK]

/-- The connecting morphism `shortExactδTranslate` is natural in the short exact sequence. -/
@[stacks 0FTB "naturality of the connecting morphism in maps of short exact sequences"]
theorem shortExactδTranslate_naturality
    {S₁ S₂ : ShortComplex (DifferentialGradedModule.{u, v, w} A)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    shortExactδTranslate h₁ ≫ ((moduleToDerivedCategory A).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (moduleToDerivedCategory A).map φ.τ₃ ≫ shortExactδTranslate h₂ := by
  dsimp only [shortExactδTranslate]
  rw [Category.assoc, shiftTranslateIso_naturality φ.τ₁, ← Category.assoc,
    shortExactδ_naturality h₁ h₂ φ, Category.assoc]

/-- The `δ`-functor structure on the localization functor `Mod(A, d) ⥤ D(A, d)`, with
`δ = - p ∘ q⁻¹` the connecting morphism `shortExactδTranslate`. -/
@[stacks 0FTB "the canonical delta-functor: the localization Mod(A, d) to D(A, d) carries the \
natural structure of a delta-functor, with delta equal to -p after q inverse, unconditionally"]
def deltaFunctorStructure :
    (moduleToDerivedCategory.{u, v, w} A).DeltaFunctorStructure
      (DifferentialGradedModule.{u, v, w} A) (derivedCategory.{u, v, w} A) where
  δ hS := shortExactδTranslate hS
  distinguished hS := shortExactδTranslate_distinguished hS
  δ_naturality h₁ h₂ φ := shortExactδTranslate_naturality h₁ h₂ φ

end SheafOfModules.DifferentialGradedModule

end
