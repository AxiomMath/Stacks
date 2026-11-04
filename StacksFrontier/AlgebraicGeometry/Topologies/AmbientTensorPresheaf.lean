module

public import Mathlib.Algebra.Category.AlgCat.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringDisjointUnion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coefficient presheaf `Γ(-, 𝒪) ⊗_R M` of a bare module, on all of `Over X`

Let `X` be a scheme, `R = Γ(X, 𝒪)` and `M` an `R`-module, **at an arbitrary universe**.  This
file builds the presheaf

`Over X ∋ V ↦ Γ(V.left, 𝒪) ⊗_R M`

of abelian groups on `Over X`, proves that it takes finite coproducts of schemes over `X` to
products, and deduces that for these coefficients the Čech complex of a finite family of an object
of `Over X` is the Čech complex of the one morphism out of the family's disjoint union.

## Main definitions

* `CategoryTheory.tensorRightModuleFunctor`: the functor `N ↦ N ⊗_R M` on `R`-modules.
* `AlgebraicGeometry.overGammaUnder`: the coordinate rings of the objects of `Over X`, as rings
  under `Γ(X, 𝒪)`.
* `AlgebraicGeometry.overGammaAlg`: the same as algebras over the universe lift of `Γ(X, 𝒪)`.
* `AlgebraicGeometry.overTensorPresheaf`: **the coefficient presheaf** `V ↦ Γ(V.left, 𝒪) ⊗_R M`,
  with `M` at an arbitrary universe and the presheaf at `AddCommGrpCat.{max u m}`.

## Main results

* `CategoryTheory.preservesFiniteProducts_forget_commAlgCat` and
  `CategoryTheory.preservesFiniteProducts_forget₂_commAlgCat_algCat`: the forgetful functors from
  commutative `R`-algebras to types and to `R`-algebras preserve finite products.
* `CategoryTheory.preservesFiniteProducts_tensorModuleFunctor`: the coefficient functor
  `A ↦ A ⊗_R M` of the Amitsur complex preserves finite products.
* `AlgebraicGeometry.gammaUnder_eq_comp_overGammaUnder` and
  `AlgebraicGeometry.gammaAlg_eq_comp_overGammaAlg`: `Stacks.Sites.gammaUnder` and
  `Stacks.Sites.gammaAlg` are the restrictions of `AlgebraicGeometry.overGammaUnder` and
  `AlgebraicGeometry.overGammaAlg` along `CategoryTheory.Over.post`.
* `AlgebraicGeometry.preservesFiniteProducts_overGammaUnder` and
  `AlgebraicGeometry.preservesFiniteProducts_overGammaAlg`: **the coordinate rings, and the
  coordinate algebras, take finite coproducts of schemes over `X` to products.**
* `AlgebraicGeometry.preservesFiniteProducts_overTensorPresheaf`: **the coefficient presheaf
  takes finite coproducts of schemes over `X` to products.**
* `AlgebraicGeometry.isIso_cechComplexMap_coproductRefinement_overTensorPresheaf`: [Stacks, Tag
  03FI] part (3) for these coefficients — the refinement of a finite family of an object of
  `Over X` by the one morphism out of its disjoint union induces an isomorphism of Čech complexes.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe m w u

/-! ### Finite products and the tensor product of modules -/

namespace CategoryTheory

open AlgebraicTopology

/-- The forgetful functor of `CommAlgCat` to types carries finite products to products. -/
public instance preservesFiniteProducts_forget_commAlgCat (R : Type u) [CommRing R] :
    PreservesFiniteProducts (forget (CommAlgCat.{u} R)) :=
  letI e : (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R) ⋙ forget CommRingCat.{u} ≅ forget (CommAlgCat.{u} R) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)
  ⟨fun _ => preservesLimitsOfShape_of_natIso e⟩

/-- **The forgetful functor from commutative `R`-algebras to `R`-algebras carries finite
products to products.** -/
public instance preservesFiniteProducts_forget₂_commAlgCat_algCat (R : Type u) [CommRing R] :
    PreservesFiniteProducts (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R)) := by
  refine ⟨fun n => ⟨fun {K} => ?_⟩⟩
  let : PreservesLimitsOfShape (Discrete (Fin n))
      (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget (AlgCat.{u} R)) := by
    rw [HasForget₂.forget_comp]
    exact (preservesFiniteProducts_forget_commAlgCat R).preserves n
  let := reflectsLimitsOfShape_of_reflectsIsomorphisms
    (G := forget (AlgCat.{u} R)) (J := Discrete (Fin n))
  exact preservesLimit_of_reflects_of_preserves _ (forget (AlgCat.{u} R))

/-- Tensoring an `R`-module on the right with a fixed `R`-module `M`, as a functor.  `M` may be
at any universe; the functor raises the module universe to `max w m`. -/
public def tensorRightModuleFunctor (R : Type u) [CommRing R] (M : Type m) [AddCommGroup M]
    [Module R M] : ModuleCat.{w} R ⥤ ModuleCat.{max w m} R where
  obj N := ModuleCat.of R (TensorProduct R N M)
  map f := ModuleCat.ofHom (LinearMap.rTensor M f.hom)

/-- `CategoryTheory.tensorRightModuleFunctor` is additive. -/
@[ega "III 7.2.6" "special case"]
public instance additive_tensorRightModuleFunctor (R : Type u) [CommRing R] (M : Type m)
    [AddCommGroup M] [Module R M] :
    (tensorRightModuleFunctor R M : ModuleCat.{w} R ⥤ _).Additive where
  map_add := ModuleCat.hom_ext <| map_add (LinearMap.rTensorHom (R := R) M) _ _

/-- **The coefficient functor `A ↦ A ⊗_R M` of the Amitsur complex carries finite products of
algebras to products.** -/
public instance preservesFiniteProducts_tensorModuleFunctor (R : Type u) [CommRing R]
    (M : Type m) [AddCommGroup M] [Module R M] :
    PreservesFiniteProducts
      (tensorModuleFunctor R M : CommAlgCat.{u} R ⥤ ModuleCat.{max u m} R) :=
  letI e : forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
      forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙
        (tensorRightModuleFunctor R M : ModuleCat.{u} R ⥤ ModuleCat.{max u m} R) ≅
      (tensorModuleFunctor R M : CommAlgCat.{u} R ⥤ ModuleCat.{max u m} R) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)
  ⟨fun _ => preservesLimitsOfShape_of_natIso e⟩

end CategoryTheory

namespace AlgebraicGeometry

/-! ### The coordinate rings of the objects of `Over X` -/

/-- The coordinate rings of the objects of `Over X`, as rings under the coordinate ring of `X`. -/
public def overGammaUnder (X : Scheme.{u}) : (Over X)ᵒᵖ ⥤ Under (Scheme.Γ.obj (op X)) :=
  (Under.opEquivOpOver X).inverse ⋙ Under.post Scheme.Γ

/-- **`Stacks.Sites.gammaUnder` is the restriction of `AlgebraicGeometry.overGammaUnder` along
`CategoryTheory.Over.post`**, by definition. -/
public theorem gammaUnder_eq_comp_overGammaUnder (S : Scheme.{u}) {C : Type (u + 1)}
    [Category.{u} C] (toOver : C ⥤ Over S) (T : C) :
    Stacks.Sites.gammaUnder S toOver T =
      (Over.post (toOver ⋙ Over.forget S)).op ⋙
        overGammaUnder ((toOver ⋙ Over.forget S).obj T) :=
  rfl

/-- **The coordinate rings of the objects of `Over X` take finite coproducts to products.** -/
public instance preservesFiniteProducts_overGammaUnder (X : Scheme.{u}) :
    PreservesFiniteProducts (overGammaUnder X) :=
  inferInstanceAs (PreservesFiniteProducts
    ((Under.opEquivOpOver X).inverse ⋙ Under.post Scheme.Γ))

/-- The coordinate rings of the objects of `Over X`, as algebras over the universe lift of the
coordinate ring of `X`. -/
public def overGammaAlg (X : Scheme.{u}) :
    (Over X)ᵒᵖ ⥤ CommAlgCat.{u} (ULift.{u} (Scheme.Γ.obj (op X))) :=
  overGammaUnder X ⋙ Under.map (Stacks.Sites.uliftHom (Scheme.Γ.obj (op X))) ⋙
    (commAlgCatEquivUnder
      (CommRingCat.of (ULift.{u} (Scheme.Γ.obj (op X))))).inverse

/-- **`Stacks.Sites.gammaAlg` is the restriction of `AlgebraicGeometry.overGammaAlg` along
`CategoryTheory.Over.post`**, by definition. -/
public theorem gammaAlg_eq_comp_overGammaAlg (S : Scheme.{u}) {C : Type (u + 1)}
    [Category.{u} C] (toOver : C ⥤ Over S) (T : C) :
    Stacks.Sites.gammaAlg S toOver T =
      (Over.post (toOver ⋙ Over.forget S)).op ⋙
        overGammaAlg ((toOver ⋙ Over.forget S).obj T) :=
  rfl

/-- The carrier of `AlgebraicGeometry.overGammaAlg` at an object of `Over X` is its coordinate
ring: only the base ring is universe-lifted. -/
public theorem overGammaAlg_obj_carrier (X : Scheme.{u}) (V : Over X) :
    ((overGammaAlg X).obj (op V) : Type u) = Γ(V.left, ⊤) :=
  rfl

/-- **The coordinate algebras of the objects of `Over X` take finite coproducts to products.** -/
public instance preservesFiniteProducts_overGammaAlg (X : Scheme.{u}) :
    PreservesFiniteProducts (overGammaAlg X) :=
  inferInstanceAs (PreservesFiniteProducts
    (overGammaUnder X ⋙ Under.map (Stacks.Sites.uliftHom (Scheme.Γ.obj (op X))) ⋙
      (commAlgCatEquivUnder
        (CommRingCat.of (ULift.{u} (Scheme.Γ.obj (op X))))).inverse))

/-! ### The coefficient presheaf -/

/-- **The coefficient presheaf `V ↦ Γ(V.left, 𝒪) ⊗_R M` on `Over X`**, for `R = Γ(X, 𝒪)` and an
`R`-module `M` at an arbitrary universe `m`.

This is `AlgebraicGeometry.overGammaAlg` followed by the coefficient functor
`Stacks.Descent.amitsurCoefficients` of the Amitsur complex and the forgetful functor to abelian
groups. -/
public def overTensorPresheaf (X : Scheme.{u}) (M : Type m) [AddCommGroup M]
    [Module (Scheme.Γ.obj (op X) : Type u) M] :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u m} :=
  overGammaAlg X ⋙
    Stacks.Descent.amitsurCoefficients.{u, u, m} (Scheme.Γ.obj (op X) : Type u) M ⋙
      forget₂ (ModuleCat.{max u m} (Scheme.Γ.obj (op X) : Type u)) AddCommGrpCat.{max u m}

/-- **The coefficient presheaf carries finite coproducts of schemes over `X` to products.** -/
public instance preservesFiniteProducts_overTensorPresheaf (X : Scheme.{u}) (M : Type m)
    [AddCommGroup M] [Module (Scheme.Γ.obj (op X) : Type u) M] :
    PreservesFiniteProducts (overTensorPresheaf X M) := by
  let : PreservesFiniteProducts
      (ModuleCat.restrictScalars.{max u m}
        (algebraMap (Scheme.Γ.obj (op X) : Type u)
          (ULift.{u} (Scheme.Γ.obj (op X) : Type u)))) :=
    Functor.preservesFiniteProductsOfAdditive _
  let : PreservesFiniteProducts
      (forget₂ (ModuleCat.{max u m} (Scheme.Γ.obj (op X) : Type u)) AddCommGrpCat.{max u m}) :=
    Functor.preservesFiniteProductsOfAdditive _
  exact inferInstanceAs (PreservesFiniteProducts
    (overGammaAlg X ⋙
      Stacks.Descent.amitsurCoefficients.{u, u, m} (Scheme.Γ.obj (op X) : Type u) M ⋙
        forget₂ (ModuleCat.{max u m} (Scheme.Γ.obj (op X) : Type u)) AddCommGrpCat.{max u m}))

/-! ### The one-member reduction -/

/-- **[Stacks, Tag 03FI] part (3) for the bare-module coefficient presheaf**: for a finite
covering family of an object of `Over X`, the canonical refinement by the one morphism out of
the disjoint union of the family induces an isomorphism of Čech complexes. -/
public theorem isIso_cechComplexMap_coproductRefinement_overTensorPresheaf (X : Scheme.{u})
    (M : Type m) [AddCommGroup M] [Module (Scheme.Γ.obj (op X) : Type u) M] {T : Over X}
    (E : PreZeroHypercover.{max u m} T) [Finite E.I₀] :
    IsIso (Stacks.CechSite.cechComplexMap E
      (PreZeroHypercover.singleton.{max u m} (Limits.Sigma.desc E.f))
      (Stacks.CechSite.coproductRefinement E) (overTensorPresheaf X M)) :=
  Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts E _

end AlgebraicGeometry

end
