module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.OpennessOfVersalityTransferCounterexampleTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismCostructured
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack

/-!
# The 1-morphism `(id, 0) : 𝒳′ ⟶ 𝒳′ × 𝒲` is algebraic

Let `𝒴 = 𝒳′ × 𝒲` and `F = (id, 0) : 𝒳′ ⟶ 𝒴`. For an object `(T₀, g)` of `𝒴`, the arrows
`F(x) ⟶ (T₀, g)` are the morphisms `x ⟶ T₀` factoring through the closed subscheme `V(g) ⊂ T₀`,
the fibre product `T₀ ×_{𝔸¹} Spec ℤ` of `g : T₀ ⟶ 𝔸¹` with the zero section. So the base change of
`F` along every scheme-valued point of `𝒴` is equivalent to the scheme `V(g)`, and `F` is
algebraic.

## Main definitions

* `zeroLocus`: the closed subscheme `V(g)` of the base of an object `(T₀, g)` of `𝒴`, as an object
  of the site, with its closed immersion `zeroLocusι`.
* `zeroLocusFunctor`: the equivalence from the big fppf site of `V(g)` to the arrows
  `F(x) ⟶ (T₀, g)`.

## Main results

* `isClosedImmersion_zeroLocusι`: `V(g) ⟶ T₀` is a closed immersion.
* `isAlgebraicMorphism_zeroSection`: `F` is algebraic.
-/

@[expose] public noncomputable section

universe u w wX wY

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin

namespace AlgebraicGeometry.PolarizedVersality.OpennessTransfer

variable {k : Type u} [Field k] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))

/-- The affine line over `ℤ`. -/
abbrev affineLine : Scheme.{u} := Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

/-- The morphism to the affine line given by a global function. -/
abbrev toLine {X : Scheme.{u}} (g : Γ(X, ⊤)) : X ⟶ affineLine.{u} :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).symm fun _ => g

/-- The zero section `Spec ℤ ⟶ 𝔸¹`. -/
abbrev zeroPoint : Spec (CommRingCat.of (ULift.{u} ℤ)) ⟶ affineLine.{u} := toLine 0

/-- The morphism `toLine g` pulls the coordinate of the affine line back to `g`. -/
theorem toSpecMvPolyIntEquiv_toLine {X : Scheme.{u}} (g : Γ(X, ⊤)) :
    AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} (toLine g) = fun _ => g :=
  Equiv.apply_symm_apply _ _

/-- Two morphisms to the affine line agree when they pull back the coordinate to the same
function. -/
theorem toLine_ext {X : Scheme.{u}} {a b : X ⟶ affineLine.{u}}
    (h : AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} a PUnit.unit =
      AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} b PUnit.unit) : a = b :=
  (AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).injective (funext fun _ => h)

/-- A morphism `T ⟶ X` composed with the morphism `X ⟶ 𝔸¹` given by `g` is the morphism given
by the pullback of `g`. -/
theorem comp_toLine {T X : Scheme.{u}} (f : T ⟶ X) (g : Γ(X, ⊤)) :
    f ≫ toLine g = toLine (f.appTop g) := by
  apply toLine_ext
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_toLine,
    toSpecMvPolyIntEquiv_toLine]

/-- Every morphism to `Spec ℤ` composed with the zero section is the morphism to the affine
line given by the zero function. -/
theorem comp_zeroPoint {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    f ≫ zeroPoint = toLine 0 := by
  rw [comp_toLine, map_zero]

/-- The zero section is a monomorphism. -/
instance : Mono (zeroPoint.{u}) := specULiftZIsTerminal.mono_from _

variable {B hS} (Y₀ : (targetBased B hS).obj)

/-- The function of an object `(T₀, g)` of `𝒴`. -/
abbrev objFunction : functions B hS Y₀.base := Y₀.fiber.as.1

/-- The closed subscheme `V(g)` of `T₀`, as a scheme: the fibre product with the zero
section. -/
abbrev zeroLocusScheme : Scheme.{u} :=
  pullback (toLine (objFunction Y₀)) zeroPoint

/-- The zero section is a closed immersion. -/
instance : IsClosedImmersion (zeroPoint.{u}) := by
  have h : zeroPoint.{u} ≫ specULiftZIsTerminal.from affineLine.{u} = 𝟙 _ :=
    specULiftZIsTerminal.hom_ext _ _
  have : IsClosedImmersion (zeroPoint.{u} ≫ specULiftZIsTerminal.from affineLine.{u}) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (specULiftZIsTerminal.from affineLine.{u})

/-- The scheme `V(g)` lies in the big fppf site. -/
theorem contains_zeroLocusScheme : B.Contains (zeroLocusScheme Y₀) :=
  Scheme.size_lt_of_mono_quasiCompact (pullback.fst (toLine (objFunction Y₀)) zeroPoint)
    Y₀.base.left.2

/-- **The closed subscheme `V(g)`** of the base `T₀` of an object `(T₀, g)` of `𝒴`, as an object
of the big fppf site of `Spec k[s,t]`. -/
def zeroLocus : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS :=
  siteObject B _ hS (contains_zeroLocusScheme Y₀)
    (pullback.fst (toLine (objFunction Y₀)) zeroPoint ≫ B.inclusion.map Y₀.base.hom)

/-- The inclusion `V(g) ⟶ T₀`. -/
def zeroLocusι : zeroLocus Y₀ ⟶ Y₀.base :=
  Over.homMk (ObjectProperty.homMk (pullback.fst (toLine (objFunction Y₀)) zeroPoint)) rfl

/-- **`V(g) ⟶ T₀` is a closed immersion.** -/
theorem isClosedImmersion_zeroLocusι :
    IsClosedImmersion (B.inclusion.map (zeroLocusι Y₀).left) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (toLine (objFunction Y₀)) zeroPoint))

/-- The function `g` vanishes on `V(g)`. -/
theorem pullbackFunction_zeroLocusι :
    pullbackFunction B hS (zeroLocusι Y₀) (objFunction Y₀) = 0 := by
  show (pullback.fst (toLine (objFunction Y₀)) zeroPoint).appTop (objFunction Y₀) = 0
  have h := congrArg (fun a => AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1} a PUnit.unit)
    (pullback.condition (f := toLine (objFunction Y₀)) (g := zeroPoint))
  simp only [AffineSpace.toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_toLine] at h
  rw [h, map_zero]

/-- Morphisms to `V(g)` are determined by their composites with `V(g) ⟶ T₀`. -/
theorem zeroLocus_hom_ext {T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    {a b : T ⟶ zeroLocus Y₀} (h : a ≫ zeroLocusι Y₀ = b ≫ zeroLocusι Y₀) : a = b := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  have h' := congrArg (fun m => B.inclusion.map m.left) h
  simp only [Over.comp_left, CategoryTheory.Functor.map_comp] at h'
  exact (cancel_mono (pullback.fst (toLine (objFunction Y₀)) zeroPoint)).mp h'

/-- **The universal property of `V(g)`**: a morphism `f : T ⟶ T₀` with `f^* g = 0` factors
through `V(g)`. -/
def zeroLocusLift {T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    (f : T ⟶ Y₀.base) (hf : pullbackFunction B hS f (objFunction Y₀) = 0) :
    T ⟶ zeroLocus Y₀ :=
  Over.homMk (ObjectProperty.homMk (pullback.lift (B.inclusion.map f.left)
    (specULiftZIsTerminal.from _) (by
      rw [comp_toLine, comp_zeroPoint]
      exact congrArg toLine hf))) (by
    apply ObjectProperty.hom_ext
    change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ B.inclusion.map Y₀.base.hom =
      B.inclusion.map T.hom
    rw [pullback.lift_fst_assoc, ← CategoryTheory.Functor.map_comp, Over.w f])

/-- The lift of `f` through `V(g)` composed with `V(g) ⟶ T₀` is `f`. -/
@[reassoc (attr := simp)]
theorem zeroLocusLift_ι {T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS}
    (f : T ⟶ Y₀.base) (hf : pullbackFunction B hS f (objFunction Y₀) = 0) :
    zeroLocusLift Y₀ f hf ≫ zeroLocusι Y₀ = f :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _))

/-- The arrow `F(T) ⟶ (T₀, g)` of `𝒴` given by a morphism `T ⟶ V(g)`. -/
def zeroLocusArrow (a : Over (zeroLocus Y₀)) :
    CostructuredArrow (zeroSection.{u, wX, wY} B hS).toFunctor Y₀ :=
  CostructuredArrow.mk (Y := (⟨a.left, Y₀.fiber.as.2.2.of_hom B hS (a.hom ≫ zeroLocusι Y₀)⟩ :
      artinAxiomsCategory k B hS))
    (targetHom B hS (a.hom ≫ zeroLocusι Y₀) (Subtype.ext (by
      change (0 : functions B hS a.left) =
        pullbackFunction B hS (a.hom ≫ zeroLocusι Y₀) (objFunction Y₀)
      rw [pullbackFunction_comp, pullbackFunction_zeroLocusι]
      exact (map_zero _).symm)))

/-- The category of arrows to `(T₀, g)`. -/
instance (Y₀ : (targetBased B hS).obj) :
    Category (CostructuredArrow (zeroSection.{u, wX, wY} B hS).toFunctor Y₀) :=
  commaCategory

/-- The functor from the big fppf site of `V(g)` to the category of arrows `F(x) ⟶ (T₀, g)`. -/
def zeroLocusFunctor :
    Over (zeroLocus Y₀) ⥤ CostructuredArrow (zeroSection.{u, wX, wY} B hS).toFunctor Y₀ where
  obj a := zeroLocusArrow Y₀ a
  map {a b} m := CostructuredArrow.homMk (ObjectProperty.homMk m.left) (targetHom_ext B hS (by
    change m.left ≫ b.hom ≫ zeroLocusι Y₀ = a.hom ≫ zeroLocusι Y₀
    rw [← Category.assoc, Over.w m]))
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

/-- The functor `zeroLocusFunctor` is faithful. -/
instance : (zeroLocusFunctor.{u, wX, wY} Y₀).Faithful where
  map_injective {_ _} _ _ h := Over.OverMorphism.ext (congrArg (fun φ => φ.left.hom) h)

/-- The functor `zeroLocusFunctor` is full. -/
instance : (zeroLocusFunctor.{u, wX, wY} Y₀).Full where
  map_surjective {a b} φ := by
    have hw := congrArg (fun χ => χ.base) (CostructuredArrow.w φ)
    change φ.left.hom ≫ b.hom ≫ zeroLocusι Y₀ = a.hom ≫ zeroLocusι Y₀ at hw
    exact ⟨Over.homMk φ.left.hom (zeroLocus_hom_ext Y₀ ((Category.assoc _ _ _).trans hw)),
      CostructuredArrow.hom_ext _ _ rfl⟩

/-- The functor `zeroLocusFunctor` is essentially surjective. -/
instance : (zeroLocusFunctor.{u, wX, wY} Y₀).EssSurj where
  mem_essImage c := by
    have hf : pullbackFunction B hS c.hom.base (objFunction Y₀) = 0 :=
      (congrArg Subtype.val (fiber_eq_of_hom B hS c.hom)).symm
    refine ⟨Over.mk (zeroLocusLift Y₀ c.hom.base hf), ⟨CostructuredArrow.isoMk
      (Iso.refl c.left) (targetHom_ext B hS ?_)⟩⟩
    change 𝟙 _ ≫ c.hom.base = zeroLocusLift Y₀ c.hom.base hf ≫ zeroLocusι Y₀
    rw [Category.id_comp, zeroLocusLift_ι]

/-- The functor `zeroLocusFunctor` is an equivalence of categories. -/
theorem isEquivalence_zeroLocusFunctor : (zeroLocusFunctor.{u, wX, wY} Y₀).IsEquivalence where

/-- The equivalence `zeroLocusFunctor` lies over the site. -/
theorem zeroLocusFunctor_comp_proj :
    zeroLocusFunctor.{u, wX, wY} Y₀ ⋙ CostructuredArrow.proj _ _ ⋙
      (sourceStack.{u, wX} B hS).toBasedCategory.p = Over.forget (zeroLocus Y₀) :=
  rfl

variable (B hS) in
/-- **The 1-morphism `F = (id, 0) : 𝒳′ ⟶ 𝒳′ × 𝒲` is algebraic.** -/
theorem isAlgebraicMorphism_zeroSection :
    Stack.IsAlgebraicMorphism.{u, wX, wY, w} B _ hS (zeroSection.{u, wX, wY} B hS) := by
  intro U y hy
  exact Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow B _ hS
    (isFiberedInGroupoids_artinAxiomsCategory B hS)
    (isFiberedInGroupoids_targetBased B hS)
    (zeroSection B hS) U y hy (Over.forget (zeroLocus (y.obj (Over.mk (𝟙 _)))))
    (zeroLocusFunctor _) (isEquivalence_zeroLocusFunctor _) (zeroLocusFunctor_comp_proj _)
    (Stack.isAlgebraicStack_schemeFibredCategory B _ hS _)

end AlgebraicGeometry.PolarizedVersality.OpennessTransfer
