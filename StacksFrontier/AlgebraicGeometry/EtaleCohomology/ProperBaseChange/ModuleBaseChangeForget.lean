module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate

/-!
# The module and the abelian base change comparisons agree through the forgetful functor

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and `Λ` a commutative ring. There are two underived base change
comparisons `g^{-1} f_* ⟶ f'_* (g')^{-1}`: one for sheaves of `Λ`-modules,
`Stacks.EtaleCohomology.etaleModuleBaseChange`, and one for abelian sheaves,
`Stacks.EtaleCohomology.etaleAbelianBaseChange`, the one the derived base change map of the
proper base change theorem is built from. The forgetful functor `U` to abelian sheaves carries
the first to the second, up to the comparison `g^{-1} U ≅ U g^{-1}`
(`Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso`).

Both comparisons are mates along the horizontal adjunctions of the comparison of the two
composite direct images, and direct image commutes with `U` on the nose; the cube identity
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` therefore applies once the mate of the
comparison `g^{-1} U ≅ U g^{-1}` is identified with the identity of `U g_* = g_* U`, which is the
compatibility of that comparison with the units
(`Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIso_unit'`).

## Main results

* `mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso`: the mate of the comparison
  `g^{-1} U ≅ U g^{-1}` is the identity.
* `etaleModuleUnderlyingAbelianInverseImageIso_comp_map_etaleModuleBaseChange`: the cube identity
  at a sheaf of modules.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.ModuleBaseChangeForget

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₅] [Category* C₆]

/-- The component of a 2-square whiskered at its top and bottom. -/
theorem whiskerTop_whiskerBottom_natTrans_app {T T' : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B B' : C₃ ⥤ C₄} (w : TwoSquare T' L R B) (φ : T ⟶ T') (ψ : B ⟶ B') (c : C₁) :
    ((w.whiskerTop φ).whiskerBottom ψ).natTrans.app c =
      R.map (φ.app c) ≫ w.natTrans.app c ≫ ψ.app (L.obj c) := by
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

end Stacks.EtaleCohomology.ModuleBaseChangeForget

namespace Stacks.EtaleCohomology

open ModuleBaseChangeForget

variable (Λ : Type) [CommRing Λ]

/-- **The mate of the comparison `g^{-1} U ≅ U g^{-1}` is the identity of `U g_* = g_* U`**: the
comparison matches the units of the two inverse image adjunctions, and the unit followed by the
direct image of the counit is the identity. -/
theorem mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (mateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ g)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
      (TwoSquare.mk _ _ _ _ (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom)).natTrans =
      𝟙 (etaleModuleDirectImage.{u, 0} Λ g ⋙ etaleModuleUnderlyingAbelian X Λ) := by
  ext N : 2
  have hu := etaleModuleUnderlyingAbelianInverseImageIso_unit' Λ g
    ((etaleModuleDirectImage.{u, 0} Λ g).obj N)
  have ht := (etaleModuleInverseImageAdj.{u, 0} Λ g).right_triangle_components N
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, NatTrans.id_app]
  show (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
        ((etaleModuleUnderlyingAbelian X Λ).obj ((etaleModuleDirectImage.{u, 0} Λ g).obj N)) ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        ((etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ g).obj N)) ≫
      (etaleModuleUnderlyingAbelian X Λ).map ((etaleModuleDirectImage.{u, 0} Λ g).map
        ((etaleModuleInverseImageAdj.{u, 0} Λ g).counit.app N)) = 𝟙 _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu.symm).trans
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg (etaleModuleUnderlyingAbelian X Λ).map ht).trans
        (CategoryTheory.Functor.map_id _ _))))

/-- `Stacks.EtaleCohomology.mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso`, as an
equality of 2-squares. -/
theorem mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso' {X Y : Scheme.{u}} (g : Y ⟶ X) :
    mateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ g)
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
      (TwoSquare.mk _ _ _ _ (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom) =
      TwoSquare.mk (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleUnderlyingAbelian Y Λ)
        (etaleModuleUnderlyingAbelian X Λ) (etaleAbelianDirectImage.{u, 0} g) (𝟙 _) :=
  TwoSquare.ext _ _ fun N => by
    have := congrArg (fun t => t.app N) (mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso Λ g)
    exact this

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- **The forgetful functor carries the module base change comparison to the abelian one**: at a
sheaf of `Λ`-modules `M` on `X_étale`, `U` of the module comparison
`g^{-1} f_* M ⟶ f'_* (g')^{-1} M`, preceded by the comparison `g^{-1} U ≅ U g^{-1}`, is the
abelian comparison at `U M` followed by `f'_*` of the comparison `(g')^{-1} U ≅ U (g')^{-1}`. -/
theorem etaleModuleUnderlyingAbelianInverseImageIso_comp_map_etaleModuleBaseChange
    (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom.app
        ((etaleModuleDirectImage.{u, 0} Λ f).obj M) ≫
      (etaleModuleUnderlyingAbelian Y' Λ).map ((etaleModuleBaseChange Λ f f' g g' w).app M) =
    (etaleAbelianBaseChange.{u, 0} f g g' f' w.symm).app
        ((etaleModuleUnderlyingAbelian X Λ).obj M) ≫
      (etaleAbelianDirectImage.{u, 0} f').map
        ((etaleModuleUnderlyingAbelianInverseImageIso Λ g').hom.app M) := by
  have hcube := Stacks.CategoryTheory.mateEquiv_symm_hComp_eq
    (G := etaleModuleDirectImage.{u, 0} Λ f) (H := etaleModuleDirectImage.{u, 0} Λ f')
    (G' := etaleAbelianDirectImage.{u, 0} f) (H' := etaleAbelianDirectImage.{u, 0} f')
    (etaleModuleInverseImageAdj.{u, 0} Λ g') (etaleModuleInverseImageAdj.{u, 0} Λ g)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} g)
    (TwoSquare.mk _ _ _ _ (etaleModuleUnderlyingAbelianInverseImageIso Λ g').hom)
    (TwoSquare.mk _ _ _ _ (etaleModuleUnderlyingAbelianInverseImageIso Λ g).hom)
    (𝟙 (etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleUnderlyingAbelian Y Λ) :
      etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleUnderlyingAbelian Y Λ ⟶
        etaleModuleUnderlyingAbelian X Λ ⋙ etaleAbelianDirectImage.{u, 0} f)
    (𝟙 (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleUnderlyingAbelian Y' Λ) :
      etaleModuleUnderlyingAbelian X' Λ ⋙ etaleAbelianDirectImage.{u, 0} f' ⟶
        etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleUnderlyingAbelian Y' Λ)
    (TwoSquare.mk _ _ _ _ ((etaleModuleDirectImageComp.{u, 0} Λ g' f (f' ≫ g) w).hom ≫
      (etaleModuleDirectImageComp.{u, 0} Λ f' g (f' ≫ g) rfl).inv))
    (TwoSquare.mk _ _ _ _ ((etaleAbelianDirectImageCompIso'.{u, 0} g' f (f' ≫ g) w).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, 0} f' g (f' ≫ g) rfl).inv)) (by
        rw [mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso',
          mateEquiv_etaleModuleUnderlyingAbelianInverseImageIso']
        refine TwoSquare.ext _ _ fun M => ?_
        refine Sheaf.hom_ext ?_
        refine NatTrans.ext (funext fun U => ?_)
        rfl)
  have h0 := congrArg (fun t => t.natTrans.app M) hcube
  simp only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    Functor.whiskerRight_id', Functor.whiskerLeft_id', NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.id_app, Category.id_comp, Category.comp_id] at h0
  rw [etaleModuleBaseChange_eq_mateEquiv_symm,
    etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0} f g g' f' w.symm
      (f' ≫ g) w rfl]
  refine h0.trans ((Category.comp_id _).trans ?_)
  exact (congrArg (· ≫ _) (show (Functor.whiskerRight
      (𝟙 (etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleUnderlyingAbelian Y Λ) :
        etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleUnderlyingAbelian Y Λ ⟶
          etaleModuleUnderlyingAbelian X Λ ⋙ etaleAbelianDirectImage.{u, 0} f)
      (etaleAbelianInverseImage.{u, 0} g)).app M = 𝟙 _ from
        CategoryTheory.Functor.map_id (etaleAbelianInverseImage.{u, 0} g) _)).trans
    (Category.id_comp _)

end Stacks.EtaleCohomology
