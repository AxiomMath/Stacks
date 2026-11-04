module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate

/-!
# A criterion for the étale base change map on global sections

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and let `K` be an abelian sheaf on `X_étale`. The base change
map `β : g^{-1} f_* K ⟶ f'_* (g')^{-1} K` (`Stacks.EtaleCohomology.etaleAbelianBaseChange`) is
the mate, along the two horizontal adjunctions, of the comparison of the two composite direct
images (`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`).
Reading the defining identity of that mate on global sections gives a commutative square

```
Γ(Y, f_* K)  --unit-->  Γ(Y', g^{-1} f_* K)
    |                          | Γ(β)
    v                          v
Γ(X, K)      --unit-->  Γ(X', (g')^{-1} K)
```

whose horizontal arrows are the restriction maps of global sections along `g` and `g'`, i.e. the
maps induced on global sections by the units of the two inverse-image/direct-image adjunctions.
Hence `Γ(β)` is bijective as soon as both restriction maps are.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDirectImageGammaIso` — global sections of a direct image
  are the global sections upstairs.
* `Stacks.EtaleCohomology.unit_comp_directImage_map_etaleAbelianBaseChange` — the mate identity:
  the unit along `g` followed by `g_*` of the base change map is `f_*` of the unit along `g'`
  followed by the comparison of the two composite direct images.
* `Stacks.EtaleCohomology.isIso_Γ_map_etaleAbelianBaseChange_app` — if restriction of global
  sections is bijective along `g` (at `f_* K`) and along `g'` (at `K`), then the base change map
  at `K` is bijective on global sections over `Y'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

/-- **Global sections of a direct image are the global sections upstairs.** The direct image is
restriction along base change, and base change carries the terminal object of `X_étale` to a
terminal object of `Y_étale`. -/
def etaleAbelianDirectImageGammaIso {X Y : Scheme.{u}} (i : Y ⟶ X) :
    etaleAbelianDirectImage.{u, v} i ⋙
        Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≅
      Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v} (terminalIsTerminal (C := X.Etale))) ≪≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
      (isTerminalSmallEtaleBaseChangeObj i (terminalIsTerminal (C := X.Etale)))).symm

/-- A morphism of abelian sheaves on `Y_étale` is bijective on global sections exactly when its
direct image along `i : Y ⟶ X` is bijective on global sections over `X`. -/
theorem isIso_Γ_map_directImage_map_iff {X Y : Scheme.{u}} (i : Y ⟶ X)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ G) :
    IsIso ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
        ((etaleAbelianDirectImage.{u, v} i).map φ)) ↔
      IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map φ) :=
  NatIso.isIso_map_iff (etaleAbelianDirectImageGammaIso.{u, v} i) φ

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (hyp : g' ≫ f = f' ≫ g)

/-- **The mate identity of the base change map along the horizontal adjunctions.** The unit of
`g^{-1} ⊣ g_*` at `f_* K` followed by `g_*` of the base change map at `K` is `f_*` of the unit of
`(g')^{-1} ⊣ g'_*` at `K` followed by the comparison `f_* g'_* ≅ g_* f'_*` of the two composite
direct images. -/
theorem unit_comp_directImage_map_etaleAbelianBaseChange
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
          ((etaleAbelianDirectImage.{u, v} f).obj K) ≫
        (etaleAbelianDirectImage.{u, v} g).map
          ((etaleAbelianBaseChange.{u, v} f g g' f' hyp).app K) =
      (etaleAbelianDirectImage.{u, v} f).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').unit.app K) ≫
        ((etaleAbelianDirectImageCompIso'.{u, v} g' f (g' ≫ f) rfl).hom ≫
          (etaleAbelianDirectImageCompIso'.{u, v} f' g (g' ≫ f) hyp).inv).app
            ((etaleAbelianInverseImage.{u, v} g').obj K) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} f g g' f' hyp
    (g' ≫ f) rfl hyp]
  exact (unit_mateEquiv_symm (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g) _ K).symm

/-- **A criterion for the base change map on global sections.** If restriction of global sections
along `g` is bijective at `f_* K` and restriction of global sections along `g'` is bijective at
`K` — each read as the map the unit of the inverse-image/direct-image adjunction induces on
global sections — then the base change map `g^{-1} f_* K ⟶ f'_* (g')^{-1} K` is bijective on
global sections over `Y'`. -/
theorem isIso_Γ_map_etaleAbelianBaseChange_app
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hg : IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
        ((etaleAbelianDirectImage.{u, v} f).obj K))))
    (hg' : IsIso ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').unit.app K))) :
    IsIso ((Sheaf.Γ Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleAbelianBaseChange.{u, v} f g g' f' hyp).app K)) := by
  rw [← isIso_Γ_map_directImage_map_iff.{u, v} g]
  have h₁ : IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleAbelianDirectImage.{u, v} f).map
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} g').unit.app K))) :=
    (isIso_Γ_map_directImage_map_iff.{u, v} f _).2 hg'
  have h := congrArg (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
    (unit_comp_directImage_map_etaleAbelianBaseChange.{u, v} f g g' f' hyp K)
  rw [Functor.map_comp, Functor.map_comp] at h
  have h₂ : IsIso ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
          ((etaleAbelianDirectImage.{u, v} f).obj K) ≫
        (etaleAbelianDirectImage.{u, v} g).map
          ((etaleAbelianBaseChange.{u, v} f g g' f' hyp).app K))) := by
    rw [Functor.map_comp, h]
    infer_instance
  rw [Functor.map_comp] at h₂
  exact IsIso.of_isIso_comp_left ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
      ((etaleAbelianDirectImage.{u, v} f).obj K))) _

end Stacks.EtaleCohomology

end
