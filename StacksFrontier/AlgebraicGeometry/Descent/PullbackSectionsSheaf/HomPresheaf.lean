module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections

/-!
# The pullback-sections presheaf is the presheaf of morphisms from the structure sheaf

For a quasi-coherent module `F` on a scheme `S`, the presheaf of Stacks 03DS sends a scheme
`T ⟶ S` to the global sections of the pullback of `F` to `T`.  A global section of a module on
`T` is a morphism from the structure sheaf of `T`, and the structure sheaf of `T` is the
pullback of the structure sheaf of `S`; so the presheaf of Stacks 03DS is the presheaf of
morphisms `T^* 𝒪_S ⟶ T^* F` on the schemes over `S`, which is Mathlib's
`CategoryTheory.Pseudofunctor.presheafHom` for the pullback pseudofunctor of sheaves of
modules.

## Main definitions

* `AlgebraicGeometry.pullbackSectionsHomEquiv`: for `T ⟶ S`, global sections of `T^* F` are
  morphisms `T^* 𝒪_S ⟶ T^* F`.

## Main results

* `AlgebraicGeometry.quasiCoherentPresheafIsoPresheafHom`: the presheaf of Stacks 03DS, with
  its abelian group structure forgotten, is `presheafHom 𝒪_S F` for
  `AlgebraicGeometry.modulePullbackPseudofunctor`.
* `AlgebraicGeometry.modulePullbackPseudofunctor_pullHom`: the pullback map on morphisms of the
  pullback pseudofunctor, written out in terms of the comparison isomorphisms
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr`.

## Implementation notes

The identification is an isomorphism of presheaves of *types*: the sheaf condition for an
abelian presheaf is the sheaf condition for the underlying presheaf of types, and
`CategoryTheory.Pseudofunctor.presheafHom` is type-valued.

Naturality is checked through the prescribed value of the presheaf of Stacks 03DS on
morphisms, `AlgebraicGeometry.PullbackSectionsPresheaf.map_objIso`, rather than by unfolding its
functor, and the comparison of the two sides is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_sections_naturality`.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **Global sections of a pullback are morphisms from the pulled-back structure sheaf.**  For a
scheme `T` over `S` and a module `F` on `S`, the global sections of `T^* F` are the morphisms
`T^* 𝒪_S ⟶ T^* F`, which is the value at `T` of the presheaf of morphisms of
`AlgebraicGeometry.modulePullbackPseudofunctor`. -/
noncomputable def pullbackSectionsHomEquiv (F : S.Modules) {T : Over S} :
    Γ((Scheme.Modules.pullback T.hom).obj F, ⊤) ≃
      (modulePullbackPseudofunctor.presheafHom (Scheme.unitModule S) F).obj (op T) :=
  (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback T.hom).obj F)).trans
    ((Scheme.Modules.pullbackUnitIso T.hom).homCongr (Iso.refl _)).symm

/-- `AlgebraicGeometry.pullbackSectionsHomEquiv` is precomposition with the identification of
`T^* 𝒪_S` with `𝒪_T`. -/
lemma pullbackSectionsHomEquiv_apply (F : S.Modules) (T : Over S)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    pullbackSectionsHomEquiv F x = (Scheme.Modules.pullbackUnitIso T.hom).hom ≫
      Scheme.Modules.unitHomEquivTop _ x := by
  show (Scheme.Modules.pullbackUnitIso T.hom).hom ≫
      Scheme.Modules.unitHomEquivTop _ x ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- **The pullback map on morphisms of the pullback pseudofunctor.**  For a factorisation
`f ≫ g = h` of morphisms of schemes, pulling a morphism `g^* M ⟶ g^* N` back along `f` is
conjugation by the comparison isomorphisms of iterated pullback. -/
lemma modulePullbackPseudofunctor_pullHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (M N : Z.Modules)
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := modulePullbackPseudofunctor) φ f h h w w =
      (Scheme.Modules.pullbackCongr w).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map φ ≫
        (Scheme.Modules.pullbackComp f g).hom.app N ≫
        (Scheme.Modules.pullbackCongr w).hom.app N := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  rfl

/-- `AlgebraicGeometry.pullbackSectionsHomEquiv` is natural in the scheme over `S`: it carries
the pullback map on global sections of Stacks 03DS to the restriction map of the presheaf of
morphisms. -/
lemma pullbackSectionsHomEquiv_naturality (F : S.Modules) {T U : Over S} (g : U ⟶ T)
    (sT : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    pullbackSectionsHomEquiv F (T := U) (pullbackSectionsMap F g sT) =
      (modulePullbackPseudofunctor.presheafHom (Scheme.unitModule S) F).map (op g)
        (pullbackSectionsHomEquiv F (T := T) sT) := by
  rw [pullbackSectionsHomEquiv_apply, pullbackSectionsHomEquiv_apply]
  show _ = Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := modulePullbackPseudofunctor) _ g.left U.hom U.hom (Over.w g) (Over.w g)
  rw [modulePullbackPseudofunctor_pullHom,
    ← Scheme.Modules.pullbackUnitIso_comp_eq g.left T.hom U.hom (Over.w g), Functor.map_comp]
  simp only [Category.assoc]
  apply congrArg (_ ≫ ·)
  apply congrArg (_ ≫ ·)
  apply congrArg (_ ≫ ·)
  convert! Scheme.Modules.pullbackUnitIso_sections_naturality g.left
      ((Scheme.Modules.pullback T.hom).obj F) ((Scheme.Modules.pullback U.hom).obj F)
      ((Scheme.Modules.pullbackComp g.left T.hom).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F) sT using 1

/-- **The presheaf of Stacks 03DS is the presheaf of morphisms from the structure sheaf.**  The
presheaf on the schemes over `S` whose sections over `T ⟶ S` are the global sections of `T^* F`
is, as a presheaf of types, the presheaf of morphisms `T^* 𝒪_S ⟶ T^* F` of the pullback
pseudofunctor of sheaves of modules. -/
noncomputable def quasiCoherentPresheafIsoPresheafHom (F : S.Modules) [F.IsQuasicoherent] :
    (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) ≅
      modulePullbackPseudofunctor.presheafHom (Scheme.unitModule S) F := by
  let P := quasiCoherentPresheaf S F
  refine NatIso.ofComponents (fun T => Equiv.toIso
    ((Functor.mapIso (CategoryTheory.forget AddCommGrpCat) (P.objIso T)).toEquiv.trans
      (pullbackSectionsHomEquiv F (T := T.unop)))) ?_
  rintro ⟨T⟩ ⟨U⟩ ⟨g⟩
  ext s
  let sT := (P.objIso (op T)).hom.hom s
  have hmap : (P.objIso (op U)).hom.hom ((P.functor.map (op g)).hom s) =
      pullbackSectionsMap F g sT := by
    simpa [sT] using congrArg (fun k => k sT) (P.map_objIso (op g))
  change pullbackSectionsHomEquiv F (T := U)
      ((P.objIso (op U)).hom.hom ((P.functor.map (op g)).hom s)) =
    (modulePullbackPseudofunctor.presheafHom (Scheme.unitModule S) F).map (op g)
      (pullbackSectionsHomEquiv F (T := T) sT)
  rw [hmap, pullbackSectionsHomEquiv_naturality]

end AlgebraicGeometry

end
