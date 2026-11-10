module

public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic

/-!
# Functoriality of the pullback of a sheaf of graded algebras

Let `f : X ⟶ Y` be a morphism of ringed spaces. `Stacks.RingedSpace.pullbackGradedAlgebra` makes
the inverse image `f^*A` of a sheaf of `ℤ`-graded `𝒪_Y`-algebras a sheaf of `ℤ`-graded
`𝒪_X`-algebras. This file makes it a functor in `A`: a homomorphism `A ⟶ B` of sheaves of graded
algebras pulls back to one `f^*A ⟶ f^*B`, degreewise the inverse image of the components, and an
isomorphism to an isomorphism.

## Main definitions

* `Stacks.RingedSpace.pullbackGradedAlgebraMap`: **`f^*φ : f^*A ⟶ f^*B`** for `φ : A ⟶ B`.
* `Stacks.RingedSpace.pullbackGradedAlgebraMapIso`: the same for an isomorphism.

## Main results

* `Stacks.RingedSpace.pullbackGradedAlgebraMap_pullbackUnit`: `f^*φ` on the image of a section.

## Implementation notes

Multiplicativity is an equation between two bilinear functions of two local sections of the
pullbacks, so by `Stacks.RingedSpace.pullbackBilinear_ext` it is enough to check it on images of
local sections of `A`, where it is the multiplicativity of `φ`.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A B D : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}

/-- **The inverse image of a homomorphism of sheaves of graded algebras**: degreewise the inverse
image of its components. -/
def pullbackGradedAlgebraMap (φ : A ⟶ B) :
    pullbackGradedAlgebra f A ⟶ pullbackGradedAlgebra f B where
  app n := (pullbackFunctor f).map (φ.app n)
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    refine pullbackBilinear_ext f
      (bilinPostcomp ((pullbackGradedAlgebra f A).mul i j)
        ((pullbackFunctor f).map (φ.app (i + j))))
      ((((pullbackGradedAlgebra f B).mul i j).compLeft
          ((pullbackFunctor f).map (φ.app i)).val).compRight
        ((pullbackFunctor f).map (φ.app j)).val) (fun V a b => ?_) U x y
    change Hom.app ((pullbackFunctor f).map (φ.app (i + j))).val (op ((opensMap f).obj V))
        (((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (A.piece j) (op V) b)) =
      ((pullbackGradedAlgebra f B).mul i j).app (op ((opensMap f).obj V))
        (Hom.app ((pullbackFunctor f).map (φ.app i)).val (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a))
        (Hom.app ((pullbackFunctor f).map (φ.app j)).val (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece j) (op V) b))
    rw [pullbackGradedAlgebra_mul_pullbackUnit]
    refine (pullbackUnit_naturality f (φ.app (i + j)) (op V) _).trans ?_
    refine Eq.trans ?_ (congrArg₂ (fun p q => ((pullbackGradedAlgebra f B).mul i j).app
      (op ((opensMap f).obj V)) p q) (pullbackUnit_naturality f (φ.app i) (op V) a).symm
      (pullbackUnit_naturality f (φ.app j) (op V) b).symm)
    refine Eq.trans ?_ (pullbackGradedAlgebra_mul_pullbackUnit f B i j V _ _).symm
    exact congrArg (pullbackUnit f (B.piece (i + j)) (op V)) (φ.map_mul i j (op V) a b)

/-- The degree `n` component of `f^*φ` is the inverse image of the degree `n` component of `φ`. -/
@[simp] theorem pullbackGradedAlgebraMap_app (φ : A ⟶ B) (n : ℤ) :
    (pullbackGradedAlgebraMap f φ).app n = (pullbackFunctor f).map (φ.app n) := rfl

/-- `f^*φ` on the image of a local section: the image of `φ` of it. -/
theorem pullbackGradedAlgebraMap_pullbackUnit (φ : A ⟶ B) (n : ℤ) (V : Opens Y.carrier)
    (a : (A.piece n).val.obj (op V)) :
    Hom.app ((pullbackGradedAlgebraMap f φ).app n).val (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece n) (op V) a) =
      pullbackUnit f (B.piece n) (op V) (Hom.app (φ.app n).val (op V) a) :=
  pullbackUnit_naturality f (φ.app n) (op V) a

/-- The inverse image of the identity of `A` is the identity of `f^*A`. -/
theorem pullbackGradedAlgebraMap_id :
    pullbackGradedAlgebraMap f (𝟙 A) = 𝟙 (pullbackGradedAlgebra f A) := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  exact (pullbackFunctor f).map_id (A.piece n)

/-- The inverse image of a composite `φ ≫ ψ` is the composite `f^*φ ≫ f^*ψ`. -/
theorem pullbackGradedAlgebraMap_comp (φ : A ⟶ B) (ψ : B ⟶ D) :
    pullbackGradedAlgebraMap f (φ ≫ ψ) =
      pullbackGradedAlgebraMap f φ ≫ pullbackGradedAlgebraMap f ψ := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  exact (pullbackFunctor f).map_comp (φ.app n) (ψ.app n)

/-- **The inverse image of an isomorphism of sheaves of graded algebras.** -/
def pullbackGradedAlgebraMapIso (e : A ≅ B) :
    pullbackGradedAlgebra f A ≅ pullbackGradedAlgebra f B where
  hom := pullbackGradedAlgebraMap f e.hom
  inv := pullbackGradedAlgebraMap f e.inv
  hom_inv_id := by rw [← pullbackGradedAlgebraMap_comp, e.hom_inv_id, pullbackGradedAlgebraMap_id]
  inv_hom_id := by rw [← pullbackGradedAlgebraMap_comp, e.inv_hom_id, pullbackGradedAlgebraMap_id]

/-- The degree `n` component of the homomorphism underlying `f^*e` is the inverse image of the
degree `n` component of `e.hom`. -/
@[simp] theorem pullbackGradedAlgebraMapIso_hom_app (e : A ≅ B) (n : ℤ) :
    (pullbackGradedAlgebraMapIso f e).hom.app n = (pullbackFunctor f).map (e.hom.app n) := rfl

end Stacks.RingedSpace

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- **The inverse image along an open immersion is the restriction**, at the ringed-space spelling
of the inverse image. -/
def pullbackIsoRestrict :
    pullbackFunctor f.toLRSHom.toShHom ≅ Scheme.Modules.restrictFunctor f :=
  (pullbackAdjunction f.toLRSHom.toShHom).leftAdjointUniq (Scheme.Modules.restrictAdjunction f)

/-- `pullbackIsoRestrict` on the image of a local section: its restriction to the image of the
inverse image of the open. -/
theorem pullbackIsoRestrict_hom_pullbackUnit (M : Y.Modules) (V : Y.Opens) (a : Γ(M, V)) :
    Hom.app ((pullbackIsoRestrict f).hom.app M).val (op (f ⁻¹ᵁ V))
        (pullbackUnit f.toLRSHom.toShHom M (op V) a) =
      M.presheaf.map (homOfLE (f.image_preimage_le V)).op a := by
  have h := congrArg (fun g => Hom.app g.val (op V) a)
    ((pullbackAdjunction f.toLRSHom.toShHom).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.restrictAdjunction f) M)
  exact h

/-- **`pullbackIsoRestrict` is multiplicative**: for a sheaf of graded algebras `G` on `Y`, it
carries the product of the pulled-back algebra over an open `U` of `X` to the product of `G` over
the image of `U`. -/
theorem pullbackIsoRestrict_hom_mul
    (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y.toRingedSpace)) (i j : ℤ)
    (U : X.Opens) (x : ((pullbackGradedAlgebra f.toLRSHom.toShHom G).piece i).val.obj (op U))
    (y : ((pullbackGradedAlgebra f.toLRSHom.toShHom G).piece j).val.obj (op U)) :
    Hom.app ((pullbackIsoRestrict f).hom.app (G.piece (i + j))).val (op U)
        (((pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j).app (op U) x y) =
      (G.mul i j).app (op (f ''ᵁ U))
        (Hom.app ((pullbackIsoRestrict f).hom.app (G.piece i)).val (op U) x)
        (Hom.app ((pullbackIsoRestrict f).hom.app (G.piece j)).val (op U) y) := by
  let ρ : Stacks.BilinearMap (Scheme.Modules.restrict (G.piece i) f).val
      (Scheme.Modules.restrict (G.piece j) f).val
      (Scheme.Modules.restrict (G.piece (i + j)) f).val :=
    { app := fun W => (G.mul i j).app (op (f ''ᵁ W.unop))
      map_smul_left := fun W r x y =>
        (G.mul i j).map_smul_left (op (f ''ᵁ W.unop)) ((f.appIso W.unop).inv r) x y
      map_smul_right := fun W r x y =>
        (G.mul i j).map_smul_right (op (f ''ᵁ W.unop)) ((f.appIso W.unop).inv r) x y
      naturality := fun {W W'} h x y =>
        (G.mul i j).naturality (f.opensFunctor.map h.unop).op x y }
  refine pullbackBilinear_ext f.toLRSHom.toShHom
    (bilinPostcomp ((pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j)
      ((pullbackIsoRestrict f).hom.app (G.piece (i + j))))
    ((ρ.compLeft ((pullbackIsoRestrict f).hom.app (G.piece i)).val).compRight
      ((pullbackIsoRestrict f).hom.app (G.piece j)).val) (fun V a b => ?_) U x y
  change Hom.app ((pullbackIsoRestrict f).hom.app (G.piece (i + j))).val (op (f ⁻¹ᵁ V))
      (((pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j).app (op (f ⁻¹ᵁ V))
        (pullbackUnit f.toLRSHom.toShHom (G.piece i) (op V) a)
        (pullbackUnit f.toLRSHom.toShHom (G.piece j) (op V) b)) =
    (G.mul i j).app (op (f ''ᵁ (f ⁻¹ᵁ V)))
      (Hom.app ((pullbackIsoRestrict f).hom.app (G.piece i)).val (op (f ⁻¹ᵁ V))
        (pullbackUnit f.toLRSHom.toShHom (G.piece i) (op V) a))
      (Hom.app ((pullbackIsoRestrict f).hom.app (G.piece j)).val (op (f ⁻¹ᵁ V))
        (pullbackUnit f.toLRSHom.toShHom (G.piece j) (op V) b))
  refine (congrArg (Hom.app ((pullbackIsoRestrict f).hom.app (G.piece (i + j))).val
    (op (f ⁻¹ᵁ V)))
    (pullbackGradedAlgebra_mul_pullbackUnit f.toLRSHom.toShHom G i j V a b)).trans ?_
  refine (pullbackIsoRestrict_hom_pullbackUnit f (G.piece (i + j)) V _).trans ?_
  refine ((G.mul i j).naturality (homOfLE (f.image_preimage_le V)).op a b).trans ?_
  exact congrArg₂ (fun p q => (G.mul i j).app (op (f ''ᵁ (f ⁻¹ᵁ V))) p q)
    (pullbackIsoRestrict_hom_pullbackUnit f (G.piece i) V a).symm
    (pullbackIsoRestrict_hom_pullbackUnit f (G.piece j) V b).symm

end Stacks.RingedSpace

end
