module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical

/-!
# The two composition isomorphisms of derived pullback on small étale topoi agree

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces the library constructs the
identification `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D twice:

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, the composition isomorphism
  of derived pullbacks along morphisms of ringed topoi followed by the action of
  `AlgebraicGeometry.Space.pullbackModulesCompTransport`, the left-adjoint form of the comparison
  `AlgebraicGeometry.Space.pushforwardModulesCompTransport` of direct images;
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackCompIsoOfTwoIso`, the same composition
  isomorphism followed by the action of the 2-isomorphism
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso` of Stacks 03G8, which is the one
  of the canonical pseudofunctoriality datum
  `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.

This file proves that they are equal.  Both direct-image comparisons are, on underlying sheaves
of sets, the comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2,
part (3), so they agree; the two pullback comparisons are then the left adjoints of the same
data, and the two derived isomorphisms are induced by the same isomorphism of degreewise
pullbacks.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_eq_ofNatIsoRight_symm`:
  transporting the right adjoint across the first or the second adjunction gives the same
  comparison of left adjoints.
* `AlgebraicGeometry.Space.pushforwardModulesCompTransport_eq_compTwoIso`,
  `AlgebraicGeometry.Space.pullbackModulesCompTransport_eq_compTwoIso`: the underived comparisons
  agree.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq`: the derived ones agree.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso` and
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSquareIso_eq_canonical_iso`: the
  composition and square isomorphisms of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModuleAdjunction.lean` are those of the
  canonical pseudofunctoriality datum.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- **Transporting the right adjoint across either adjunction gives the same comparison of left
adjoints.**  For `F ⊣ G`, `F' ⊣ G'` and `e : G ≅ G'`, comparing `F ⊣ G'` (through `e`) with
`F' ⊣ G'` is the same as comparing `F ⊣ G` with `F' ⊣ G` (through `e⁻¹`). -/
theorem leftAdjointUniq_ofNatIsoRight_eq_ofNatIsoRight_symm {F F' : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (e : G ≅ G') :
    leftAdjointUniq (adj1.ofNatIsoRight e) adj2 =
      leftAdjointUniq adj1 (adj2.ofNatIsoRight e.symm) := by
  ext x
  apply (adj1.homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_hom_app]
  have h := homEquiv_leftAdjointUniq_hom_app (adj1.ofNatIsoRight e) adj2 x
  simp only [ofNatIsoRight, Adjunction.homEquiv_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom] at h ⊢
  rw [← h, Category.assoc, Category.assoc, ← e.hom.naturality_assoc, Iso.hom_inv_id_app,
    Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The two comparisons of direct images along a composite agree**:
`AlgebraicGeometry.Space.pushforwardModulesCompTransport` is the comparison of direct images of
the 2-isomorphism `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`.  On underlying
sheaves of sets both are `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`. -/
theorem pushforwardModulesCompTransport_eq_compTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardModulesCompTransport B S hS f g =
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pushforwardModulesIso := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  rfl

/-- **The two comparisons of pullbacks of modules along a composite agree**:
`AlgebraicGeometry.Space.pullbackModulesCompTransport` is the comparison of pullbacks of the
2-isomorphism `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`. -/
theorem pullbackModulesCompTransport_eq_compTwoIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackModulesCompTransport B S hS f g =
      (smallEtaleRingedToposHom_compTwoIso B S hS f g).pullbackModulesIso := by
  unfold pullbackModulesCompTransport RingedToposHom.TwoIso.pullbackModulesIso
  rw [Adjunction.leftAdjointUniq_ofNatIsoRight_eq_ofNatIsoRight_symm,
    pushforwardModulesCompTransport_eq_compTwoIso]

/-- **The two composition isomorphisms of derived pullback agree.** -/
theorem smallEtaleDerivedModulePullbackCompIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedModulePullbackCompIso B S hS f g =
      smallEtaleDerivedPullbackCompIsoOfTwoIso B S hS f g := by
  rw [smallEtaleDerivedModulePullbackCompIso, smallEtaleDerivedPullbackCompIsoOfTwoIso,
    pullbackModulesCompTransport_eq_compTwoIso]
  rfl

/-- **The composition isomorphism of `SmallEtaleDerivedModuleAdjunction` is that of the
canonical pseudofunctoriality datum.** -/
theorem smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedModulePullbackCompIso B S hS f g =
      (DerivedPullbackComposition.canonical B S hS).iso f g (f ≫ g) rfl := by
  rw [smallEtaleDerivedModulePullbackCompIso_eq]
  ext M
  simp [DerivedPullbackComposition.canonical, smallEtaleDerivedPullbackFactorIso]

/-- **The square isomorphism of `SmallEtaleDerivedModuleAdjunction` is the identification of a
factorisation of the canonical pseudofunctoriality datum**: for a commutative square
`g' ≫ f = f' ≫ g`, the iterated pullback `Lf^* ⋙ L(g')^* ≅ L(f' ≫ g)^*` is
`(DerivedPullbackComposition.canonical B S hS).iso g' f (f' ≫ g) w`. -/
theorem smallEtaleDerivedModulePullbackSquareIso_eq_canonical_iso {X' Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g) :
    smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w =
      (DerivedPullbackComposition.canonical B S hS).iso g' f (f' ≫ g) w := by
  rw [smallEtaleDerivedModulePullbackSquareIso, smallEtaleDerivedModulePullbackCompIso_eq]
  rfl

/-- `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso` on
components. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app M =
      ((DerivedPullbackComposition.canonical B S hS).iso f g (f ≫ g) rfl).hom.app M := by
  rw [smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso]

/-- `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSquareIso_eq_canonical_iso` on
components. -/
theorem smallEtaleDerivedModulePullbackSquareIso_inv_app_eq {X' Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w).inv.app M =
      ((DerivedPullbackComposition.canonical B S hS).iso g' f (f' ≫ g) w).inv.app M := by
  rw [smallEtaleDerivedModulePullbackSquareIso_eq_canonical_iso]

end AlgebraicGeometry.Space

end
