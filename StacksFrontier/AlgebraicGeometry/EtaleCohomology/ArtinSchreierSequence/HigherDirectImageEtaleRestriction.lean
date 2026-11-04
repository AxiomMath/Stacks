module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Higher direct images commute with restriction along an étale morphism

For a cartesian square

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

with `g` and `g'` étale, `g⁻¹ (Rᵠ f_* F) ≅ Rᵠ f'_* (g'⁻¹ F)` for every abelian sheaf `F` on the
small étale site of `X`. The inverse image along `g` is exact, so it may be pulled into the right
derived functor; the underived base change map is invertible for such a square
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback_of_etale`); and the inverse
image along `g'` is exact and preserves injective objects, being the restriction functor, whose
left adjoint, extension by zero, is exact.

## Main definitions

* `Stacks.ArtinSchreier.rightDerivedDirectImageEtaleRestrictIso`: the isomorphism
  `g⁻¹ (Rᵠ f_* F) ≅ Rᵠ f'_* (g'⁻¹ F)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

/-- The inverse image of abelian sheaves on small étale sites along a morphism of schemes
preserves homology. -/
instance etaleAbelianInverseImage_preservesHomology {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (etaleAbelianInverseImage.{u, 0} g).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The inverse image of abelian sheaves on small étale sites along an étale morphism of schemes
preserves injective objects. -/
instance etaleAbelianInverseImage_preservesInjectiveObjects {X' X : Scheme.{u}} (g' : X' ⟶ X)
    [Etale g'] : (etaleAbelianInverseImage.{u, 0} g').PreservesInjectiveObjects := by
  have : (etaleRestriction.{u, 0} g').PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (extensionByZeroAdj.{u, 0} g')
  exact ⟨fun h => Injective.of_iso ((etaleAbelianInverseImageRestrictionIso.{u, 0} g').symm.app _)
    ((etaleRestriction.{u, 0} g').injective_obj_of_injective h)⟩

/-- **Higher direct images commute with restriction along an étale morphism**, for a cartesian
square whose two horizontal legs are étale. -/
def rightDerivedDirectImageEtaleRestrictIso {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') [Etale g] [Etale g'] (sq : IsPullback g' f' f g)
    (h : g' ≫ f = f' ≫ g) (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImage.{u, 0} g).obj
        (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F) ≅
      ((etaleAbelianDirectImage.{u, 0} f').rightDerived q).obj
        ((etaleAbelianInverseImage.{u, 0} g').obj F) :=
  have := isIso_etaleAbelianBaseChange_of_isPullback_of_etale.{u, 0} f g g' f' sq h
  ((Functor.rightDerivedCompIso (etaleAbelianDirectImage.{u, 0} f)
      (etaleAbelianInverseImage.{u, 0} g) q).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso (asIso (etaleAbelianBaseChange.{u, 0} f g g' f' h)) q).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects (etaleAbelianInverseImage.{u, 0} g')
      (etaleAbelianDirectImage.{u, 0} f') F q

end Stacks.ArtinSchreier

end
