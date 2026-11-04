module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomPrecomp
public import StacksFrontier.CategoryTheory.Sites.ZModInternalHom
public import StacksFrontier.CategoryTheory.Sites.ModuleInternalHomTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology

/-!
# Restriction along an étale morphism commutes with the internal Hom

For an étale morphism `j : U ⟶ X` restriction of sheaves is precomposition with
`smallEtaleCompose j : U_étale ⥤ X_étale`, and for every `V` étale over `U` the functor
`Over V ⥤ Over (j ∘ V)` it induces is an equivalence: a scheme étale over `V` is the same as a
scheme étale over `X` with a map to `V` over `X`. Hence `j⁻¹ ℋom(F, G) ≅ ℋom(j⁻¹ F, j⁻¹ G)`
for abelian sheaves. As a consequence, for sheaves of `ℤ/n`-modules `G, L` with `L` injective,
the restriction of `ℋom(G, L)` to any `U` étale over `X` has no higher cohomology.

## Main results

* `Stacks.EtaleCohomology.etaleRestrictionInternalHomIso`.
* `Stacks.EtaleCohomology.subsingleton_H_etaleRestriction_internalHomSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse_restrictionInternalHom
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The functor `Over V ⥤ Over (j ∘ V)` induced by `smallEtaleCompose j` is faithful. -/
instance faithful_over_post_smallEtaleCompose (V : U.Etale) :
    (Over.post (X := V) (Scheme.Etale.smallEtaleCompose j)).Faithful where
  map_injective h := Over.OverMorphism.ext <|
    MorphismProperty.Comma.Hom.ext (congrArg (fun φ => φ.left.left) h) (Subsingleton.elim _ _)

/-- The functor `Over V ⥤ Over (j ∘ V)` induced by `smallEtaleCompose j` is full. -/
instance full_over_post_smallEtaleCompose (V : U.Etale) :
    (Over.post (X := V) (Scheme.Etale.smallEtaleCompose j)).Full where
  map_surjective {W W'} h := by
    have hw : h.left.left ≫ W'.hom.left = W.hom.left :=
      congrArg (fun φ => φ.left) (Over.w h)
    refine ⟨Over.homMk (MorphismProperty.Over.homMk h.left.left ?_) ?_, ?_⟩
    · have h₁ : W'.hom.left ≫ V.hom = W'.left.hom := by simpa using W'.hom.w
      have h₂ : W.hom.left ≫ V.hom = W.left.hom := by simpa using W.hom.w
      rw [← h₁, ← h₂, ← hw]
      exact (Category.assoc _ _ _).symm
    · exact MorphismProperty.Comma.Hom.ext hw (Subsingleton.elim _ _)
    · exact Over.OverMorphism.ext (MorphismProperty.Comma.Hom.ext rfl (Subsingleton.elim _ _))

/-- The functor `Over V ⥤ Over (j ∘ V)` induced by `smallEtaleCompose j` is essentially
surjective: a scheme étale over `X` with a map to `V` over `X` is étale over `V`. -/
instance essSurj_over_post_smallEtaleCompose (V : U.Etale) :
    (Over.post (X := V) (Scheme.Etale.smallEtaleCompose j)).EssSurj where
  mem_essImage Z := by
    have hZ : Z.hom.left ≫ V.hom ≫ j = Z.left.hom :=
      (by simpa using Z.hom.w : (𝟭 Scheme).map Z.hom.left ≫ V.hom ≫ j = Z.left.hom)
    have hZe : Etale Z.hom.left := inferInstanceAs (Etale (Z.hom.left : Z.left.left ⟶ V.left))
    have hVe : Etale V.hom := V.prop
    let W : U.Etale := MorphismProperty.Over.mk (P := (@Etale : MorphismProperty Scheme.{u})) ⊤
      (Z.hom.left ≫ V.hom)
      (@Etale.etale_comp _ _ Z.hom.left _ V.hom hZe hVe)
    let g : W ⟶ V := MorphismProperty.Over.homMk Z.hom.left rfl
    refine ⟨Over.mk g, ⟨Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) ?_) ?_⟩⟩
    · change 𝟙 _ ≫ Z.left.hom = (Z.hom.left ≫ V.hom) ≫ j
      rw [Category.id_comp]
      exact hZ.symm.trans (Category.assoc _ _ _).symm
    · exact MorphismProperty.Comma.Hom.ext (Category.id_comp Z.hom.left) (Subsingleton.elim _ _)

/-- The functor `Over V ⥤ Over (j ∘ V)` induced by `smallEtaleCompose j` is an equivalence. -/
instance isEquivalence_over_post_smallEtaleCompose (V : U.Etale) :
    (Over.post (X := V) (Scheme.Etale.smallEtaleCompose j)).IsEquivalence where

/-- **Restriction along an étale morphism commutes with the internal Hom** of abelian sheaves:
`j⁻¹ ℋom(F, G) ≅ ℋom(j⁻¹ F, j⁻¹ G)`. -/
def etaleRestrictionInternalHomIso (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleRestriction.{u, 0} j).obj (internalHomSheaf X.smallEtaleTopology F G) ≅
      internalHomSheaf U.smallEtaleTopology ((etaleRestriction.{u, 0} j).obj F)
        ((etaleRestriction.{u, 0} j).obj G) :=
  Stacks.AbelianInternalHom.internalHomSheafPushforwardIso (Scheme.Etale.smallEtaleCompose j)
    U.smallEtaleTopology X.smallEtaleTopology F G

/-- **`ℋom_{ℤ/n}(G, L)` restricted to `U` étale over `X` has no higher cohomology** when `L` is
injective: the restriction is `ℋom(G|_U, L|_U)` with `L|_U` injective. -/
theorem subsingleton_H_etaleRestriction_internalHomSheaf {n : ℕ}
    (G L : EtaleModules.{u, 0} (ZMod n) X) [Injective L] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleRestriction.{u, 0} j).obj
      (internalHomSheaf X.smallEtaleTopology (Stacks.AbelianInternalHom.toAb _ G)
        (Stacks.AbelianInternalHom.toAb _ L))) q) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have := injective_etaleModuleRestriction.{u, 0} (ZMod n) j L
  refine (subsingleton_H_iff_of_iso ((etaleRestrictionInternalHomIso j
    (Stacks.AbelianInternalHom.toAb _ G) (Stacks.AbelianInternalHom.toAb _ L)).trans
    (Stacks.ModuleInternalHom.zmodHomForgetIso U.smallEtaleTopology n
      ((etaleModuleRestriction.{u, 0} (ZMod n) j).obj G)
      ((etaleModuleRestriction.{u, 0} (ZMod n) j).obj L)).symm) (m + 1)).2 ?_
  exact Stacks.ModuleInternalHom.subsingleton_H_homAbFunctor (ZMod n) U.smallEtaleTopology
    ((etaleModuleRestriction.{u, 0} (ZMod n) j).obj G)
    ((etaleModuleRestriction.{u, 0} (ZMod n) j).obj L) m

end Stacks.EtaleCohomology

end
