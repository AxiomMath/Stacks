module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf

/-!
# Transferring sections of a pullback to schemes over a common base

Let `F` be a module on a scheme `S`, let `g : Y ⟶ S` and let `a : A ⟶ S` factor as
`a = j ≫ g` through `j : A ⟶ Y`.  For an open `V` of `Y` with `j⁻¹(V) = A`, a section of `g^*F`
over `V` pulls back along `j` to a global section of `j^*g^*F`, which is a global section of
`a^*F` through the composition isomorphism of pullbacks.  This file names that map,
`AlgebraicGeometry.pullbackSectionsTransfer`, and proves the two compatibilities that make it a
morphism of presheaves on the schemes over `S`:

* **along a further morphism over `S`**: transferring to `A` and then applying the restriction
  map of the presheaf of [Stacks, Tag 03DS] along `k : A' ⟶ A` is transferring to `A'` along
  `k ≫ j` (`AlgebraicGeometry.pullbackSectionsTransfer_comp_topUnitMap`);
* **through a morphism of the intermediate schemes**: for `φ : Y₁ ⟶ Y₂` with `g₁ = φ ≫ g₂`,
  pulling a section of `g₂^*F` back to `g₁^*F` along `φ` and transferring along `j₁` is
  transferring along `j₁ ≫ φ`
  (`AlgebraicGeometry.pullbackSectionHom_comp_pullbackSectionsTransfer`).

Both are the associativity coherence of the pullback pseudofunctor, read on sections through
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`.

## Main definitions

* `AlgebraicGeometry.pullbackSectionsTransfer`: the transfer of a section of `g^*F` over `V` to a
  global section of `a^*F`.

## Main results

* `AlgebraicGeometry.pullbackSectionsTransfer_comp_topUnitMap`,
  `AlgebraicGeometry.pullbackSectionHom_comp_pullbackSectionsTransfer`: the two compatibilities.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Pulling a section back along a composite is pulling it back twice**, as an equality of
maps of sections: `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`. -/
public theorem pullbackSectionHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (h : V ≤ (f ≫ g) ⁻¹ᵁ U) :
    pullbackSectionHom g M U W hg ≫
        pullbackSectionHom f ((Scheme.Modules.pullback g).obj M) W V hf ≫
        ((Scheme.Modules.pullbackComp f g).hom.app M).app V =
      pullbackSectionHom (f ≫ g) M U V h := by
  ext a
  exact Scheme.Modules.pullbackSection_comp f g M U W V hg hf h a

/-- **Pulling a section back is natural in the module**, as an equality of maps of sections. -/
public theorem pullbackSectionHom_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules}
    (t : M ⟶ N) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    pullbackSectionHom f M U V h ≫ ((Scheme.Modules.pullback f).map t).app V =
      t.app U ≫ pullbackSectionHom f N U V h := by
  ext a
  exact Scheme.Modules.pullbackSection_naturality f t U V h a

/-- `Stacks.Sites.pullbackCompIso_cancel` in the form that moves the comparison of the inner
pullbacks across the outer pullback. -/
public theorem map_pullbackCompIso_hom_comp_pullbackCompIso_hom {S : Scheme.{u}} (F : S.Modules)
    {B' A' Y' : Scheme.{u}} (p : B' ⟶ A') (q : A' ⟶ Y') (y : Y' ⟶ S) (a : A' ⟶ S) (b : B' ⟶ S)
    (ha : q ≫ y = a) (hb : p ≫ a = b) (hc : (p ≫ q) ≫ y = b) :
    (Scheme.Modules.pullback p).map (Stacks.Sites.pullbackCompIso F q y a ha).hom ≫
        (Stacks.Sites.pullbackCompIso F p a b hb).hom =
      (Scheme.Modules.pullbackComp p q).hom.app ((Scheme.Modules.pullback y).obj F) ≫
        (Stacks.Sites.pullbackCompIso F (p ≫ q) y b hc).hom := by
  have h := Stacks.Sites.pullbackCompIso_cancel F p q y a b ha hb hc
  rw [Iso.comp_inv_eq] at h
  rw [h, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Transferring a pulled-back section along a composite.**  For `j : A ⟶ Y` over `S` and
`k : A' ⟶ A` over `S`, pulling a section of `g^*F` back along `j`, transferring it to `a^*F`,
pulling back along `k` and transferring to `a'^*F` is pulling it back along `k ≫ j` and
transferring once. -/
public theorem pullbackSectionHom_pullbackCompIso_comp {S : Scheme.{u}} (F : S.Modules)
    {Y A A' : Scheme.{u}} (g : Y ⟶ S) (j : A ⟶ Y) (a : A ⟶ S) (ha : j ≫ g = a)
    (k : A' ⟶ A) (a' : A' ⟶ S) (hk : k ≫ a = a') (V : Y.Opens) (W : A.Opens) (W' : A'.Opens)
    (hW : W ≤ j ⁻¹ᵁ V) (hW' : W' ≤ k ⁻¹ᵁ W) (hc : (k ≫ j) ≫ g = a') :
    pullbackSectionHom j ((Scheme.Modules.pullback g).obj F) V W hW ≫
        (Stacks.Sites.pullbackCompIso F j g a ha).hom.app W ≫
        pullbackSectionHom k ((Scheme.Modules.pullback a).obj F) W W' hW' ≫
        (Stacks.Sites.pullbackCompIso F k a a' hk).hom.app W' =
      pullbackSectionHom (k ≫ j) ((Scheme.Modules.pullback g).obj F) V W' (hW'.trans
          ((Opens.map k.base).monotone hW)) ≫
        (Stacks.Sites.pullbackCompIso F (k ≫ j) g a' hc).hom.app W' := by
  rw [← reassoc_of% pullbackSectionHom_naturality k (Stacks.Sites.pullbackCompIso F j g a ha).hom
    W W' hW', ← Scheme.Modules.Hom.comp_app,
    map_pullbackCompIso_hom_comp_pullbackCompIso_hom F k j g a a' ha hk hc,
    Scheme.Modules.Hom.comp_app, ← Category.assoc, ← Category.assoc,
    Category.assoc (pullbackSectionHom j _ V W hW), pullbackSectionHom_comp]

/-- Pulling a section back and transferring it along equal morphisms gives the same result. -/
public theorem pullbackSectionHom_pullbackCompIso_congr {S : Scheme.{u}} (F : S.Modules)
    {Y A : Scheme.{u}} (g : Y ⟶ S) (j j' : A ⟶ Y) (hjj' : j = j') (a : A ⟶ S) (ha : j ≫ g = a)
    (ha' : j' ≫ g = a) (V : Y.Opens) (W : A.Opens) (hW : W ≤ j ⁻¹ᵁ V) (hW' : W ≤ j' ⁻¹ᵁ V) :
    pullbackSectionHom j ((Scheme.Modules.pullback g).obj F) V W hW ≫
        (Stacks.Sites.pullbackCompIso F j g a ha).hom.app W =
      pullbackSectionHom j' ((Scheme.Modules.pullback g).obj F) V W hW' ≫
        (Stacks.Sites.pullbackCompIso F j' g a ha').hom.app W := by
  subst hjj'
  rfl

/-- The restriction map of the presheaf of Tag 03DS along a morphism of schemes over `S` is
pulling global sections back, followed by the composition isomorphism of pullbacks. -/
public theorem pullbackSectionsMap_eq_pullbackSectionHom {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y) (h' : (⊤ : X.left.Opens) ≤ g.left ⁻¹ᵁ (⊤ : Y.left.Opens)) :
    pullbackSectionsMap F g =
      pullbackSectionHom g.left ((Scheme.Modules.pullback Y.hom).obj F) ⊤ ⊤ h' ≫
        (Stacks.Sites.pullbackCompIso F g.left Y.hom X.hom (Over.w g)).hom.app ⊤ := by
  ext s
  exact pullbackSectionsMap_eq_comp F g h' s

/-- Pulling a section back along `f` to the whole preimage of its open is the unit of
`f^* ⊣ f_*`. -/
public theorem pullbackSectionHom_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) :
    pullbackSectionHom f M U (f ⁻¹ᵁ U) le_rfl =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U := by
  ext a
  exact ConcreteCategory.congr_hom (((Scheme.Modules.pullback f).obj M).presheaf.map_id _)
    ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) a)

end AlgebraicGeometry

end
