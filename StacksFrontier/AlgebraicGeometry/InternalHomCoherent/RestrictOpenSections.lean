module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom

/-!
# Sections of an internal hom over an open of an open subscheme

Let `X` be a scheme, `V ⊆ X` an open and `W ⊆ V` an open of `X` contained in `V`. A section of
the internal hom `SheafHom(G, M)` over `W` is a morphism of modules on the slice site over `W`;
the same datum, read on the open subscheme `V`, is a section of `SheafHom(G|_V, M|_V)` over the
preimage `V.ι ⁻¹ᵁ W`. This file constructs that identification, as an additive equivalence.

## Main definitions

* `Stacks.Algebraization.internalHomRestrictOpenSectionsEquiv` — the identification.

## Main results

* `Stacks.Algebraization.internalHomRestrictOpenSectionsEquiv_app` — its component at an open `T`
  of `V` is the component of the given section at the image of `T` in `X`.
* `Stacks.Algebraization.internalHomRestrictOpenSectionsEquiv_restrict` — it is natural in `W`.

## Implementation notes

The forward map is defined so that its components are literally those of the given section, so
the sectionwise description and the naturality in `W` hold by `rfl`. The inverse reads a section
over `V.ι ⁻¹ᵁ W` at the preimage of each open `T ⊆ W`, transported back along the equality
`V.ι ''ᵁ V.ι ⁻¹ᵁ T = T`. Its linearity is checked through the components of the section read as
linear maps over the structure sheaf of `X` (`restrictedSectionLinear`), because the module
structures of `G|_V` and of `G` on the same sections differ by `V.ι.appIso`, an identification that
definitional unfolding is too slow to cross.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} (G M : X.Modules) (V W : X.Opens) (hW : W ≤ V)

/-- The image in `X` of an open of `V` contained in `V.ι ⁻¹ᵁ W` is contained in `W`. -/
theorem image_le_of_le_preimage {T : V.toScheme.Opens} (hT : T ≤ V.ι ⁻¹ᵁ W) :
    V.ι ''ᵁ T ≤ W :=
  (Scheme.Hom.image_mono _ hT).trans (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_right)

/-- The slice of an open `W ⊆ V` of `X` read on the open subscheme `V`, mapped back. -/
def overImageFunctor : Over (V.ι ⁻¹ᵁ W) ⥤ Over W where
  obj T := Over.mk (homOfLE (image_le_of_le_preimage V W (leOfHom T.hom)))
  map {T T'} g := Over.homMk (homOfLE (Scheme.Hom.image_mono _ (leOfHom g.left)))
    (Subsingleton.elim _ _)

/-- An open contained in `V` is the image of its preimage in `V`. -/
theorem image_preimage_eq_of_le {T : X.Opens} (hT : T ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ T) = T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 hT

/-- The slice over `W ⊆ V` on `X`, pulled back to the slice over `V.ι ⁻¹ᵁ W` on `V`. -/
def overPreimageFunctor : Over W ⥤ Over (V.ι ⁻¹ᵁ W) where
  obj T := Over.mk (homOfLE (Scheme.Hom.preimage_mono _ (leOfHom T.hom)))
  map {T T'} g := Over.homMk (homOfLE (Scheme.Hom.preimage_mono _ (leOfHom g.left)))
    (Subsingleton.elim _ _)

include hW in
/-- Pulling back to `V` and taking the image again is the identity on the slice over `W ⊆ V`. -/
def overPreimageImageIso : overPreimageFunctor V W ⋙ overImageFunctor V W ≅ 𝟭 (Over W) :=
  NatIso.ofComponents (fun T => Over.isoMk (eqToIso (image_preimage_eq_of_le V
    ((leOfHom T.hom).trans hW))) (Subsingleton.elim _ _)) (fun _ => Subsingleton.elim _ _)


/-- The forward map: a section of `SheafHom(G, M)` over `W` read on the open subscheme `V`. -/
def internalHomRestrictOpenSectionsFun (s : ((sheafHomFunctor X G).obj M).val.obj (op W)) :
    ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W)) :=
  PresheafOfModules.homMk
    (Functor.whiskerLeft (overImageFunctor V W).op
      ((PresheafOfModules.toPresheaf _).map s))
    (fun T r m => (s.app (op ((overImageFunctor V W).obj T.unop))).hom.map_smul
      ((V.ι.appIso T.unop.left).inv r) m)

/-- A section `t` of `SheafHom(G|_V, M|_V)` over `V.ι ⁻¹ᵁ W`, as a morphism of presheaves on the
slice over `V.ι ⁻¹ᵁ W` between the restrictions of `G` and `M` to the slice over `W` on `X`. -/
def restrictedSectionNatTrans
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) :
    (overImageFunctor V W).op ⋙ ((restrFun X.sheaf.obj W).obj G.val).presheaf ⟶
      (overImageFunctor V W).op ⋙ ((restrFun X.sheaf.obj W).obj M.val).presheaf :=
  (PresheafOfModules.toPresheaf _).map t

include hW in
/-- The inverse map, at the level of underlying presheaves on the slice over `W`. -/
def internalHomRestrictOpenSectionsInvNatTrans
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) :
    ((restrFun X.sheaf.obj W).obj G.val).presheaf ⟶
      ((restrFun X.sheaf.obj W).obj M.val).presheaf :=
  Functor.whiskerRight (NatTrans.op (overPreimageImageIso V W hW).hom)
      ((restrFun X.sheaf.obj W).obj G.val).presheaf ≫
    Functor.whiskerLeft (overPreimageFunctor V W).op (restrictedSectionNatTrans G M V W t) ≫
    Functor.whiskerRight (NatTrans.op (overPreimageImageIso V W hW).inv)
      ((restrFun X.sheaf.obj W).obj M.val).presheaf

include hW in
/-- The components of `internalHomRestrictOpenSectionsInvNatTrans`. -/
theorem internalHomRestrictOpenSectionsInvNatTrans_app_apply
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) (T : (Over W)ᵒᵖ) (m : G.val.presheaf.obj (op T.unop.left)) :
    (internalHomRestrictOpenSectionsInvNatTrans G M V W hW t).app T m =
      M.val.presheaf.map (homOfLE (image_preimage_eq_of_le V ((leOfHom T.unop.hom).trans hW)).ge).op
        ((t.app (op ((overPreimageFunctor V W).obj T.unop))).hom
          (G.val.presheaf.map
            (homOfLE (image_preimage_eq_of_le V ((leOfHom T.unop.hom).trans hW)).le).op m)) :=
  rfl

/-- The component of a section over `V.ι ⁻¹ᵁ W` on `V` at an open `T'` of `V`, read as a linear
map of the sections over the image of `T'` in `X`. -/
def restrictedSectionLinear
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) (T' : Over (V.ι ⁻¹ᵁ W)) :
    G.val.obj (op (V.ι ''ᵁ T'.left)) ⟶ M.val.obj (op (V.ι ''ᵁ T'.left)) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (V.ι.appIso T'.left).symm.commRingCatIsoToRingEquiv).fullyFaithfulFunctor.preimage
    (t.app (op T'))

/-- `restrictedSectionLinear` agrees pointwise with the component of the section. -/
theorem restrictedSectionLinear_apply
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) (T' : Over (V.ι ⁻¹ᵁ W)) (y : G.val.obj (op (V.ι ''ᵁ T'.left))) :
    (restrictedSectionLinear G M V W t T').hom y =
      ConcreteCategory.hom ((restrictedSectionNatTrans G M V W t).app (op T')) y :=
  congrArg (fun g => g.hom y) ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (V.ι.appIso T'.left).symm.commRingCatIsoToRingEquiv).fullyFaithfulFunctor.map_preimage
    (X := G.val.obj (op (V.ι ''ᵁ T'.left))) (Y := M.val.obj (op (V.ι ''ᵁ T'.left)))
    (t.app (op T')))

include hW in
/-- The components of `internalHomRestrictOpenSectionsInvNatTrans`, through
`restrictedSectionLinear`. -/
theorem internalHomRestrictOpenSectionsInvNatTrans_app_apply'
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) (T : (Over W)ᵒᵖ) (m : G.val.obj (op T.unop.left)) :
    (internalHomRestrictOpenSectionsInvNatTrans G M V W hW t).app T m =
      (M.val.map (homOfLE (image_preimage_eq_of_le V
          ((leOfHom T.unop.hom).trans hW)).ge).op).hom
        ((restrictedSectionLinear G M V W t ((overPreimageFunctor V W).obj T.unop)).hom
          ((G.val.map (homOfLE (image_preimage_eq_of_le V
            ((leOfHom T.unop.hom).trans hW)).le).op).hom m)) :=
  (internalHomRestrictOpenSectionsInvNatTrans_app_apply G M V W hW t T m).trans
    (congrArg (M.val.map (homOfLE (image_preimage_eq_of_le V
          ((leOfHom T.unop.hom).trans hW)).ge).op).hom
      (restrictedSectionLinear_apply G M V W t _ _).symm)

include hW in
/-- The inverse map: a section over `V.ι ⁻¹ᵁ W` on `V` read as a section over `W` on `X`. -/
def internalHomRestrictOpenSectionsInv
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) :
    ((sheafHomFunctor X G).obj M).val.obj (op W) :=
  PresheafOfModules.homMk (internalHomRestrictOpenSectionsInvNatTrans G M V W hW t)
    (fun T r m => by
      refine (internalHomRestrictOpenSectionsInvNatTrans_app_apply' G M V W hW t T (r • m)).trans
        (Eq.trans ?_ (congrArg (r • ·)
          (internalHomRestrictOpenSectionsInvNatTrans_app_apply' G M V W hW t T m)).symm)
      set a := (homOfLE (image_preimage_eq_of_le V ((leOfHom T.unop.hom).trans hW)).le).op
      set b := (homOfLE (image_preimage_eq_of_le V ((leOfHom T.unop.hom).trans hW)).ge).op
      have hab : (ConcreteCategory.hom (X.ringCatSheaf.obj.map b))
          ((ConcreteCategory.hom (X.ringCatSheaf.obj.map a)) r) = r := by
        change (ConcreteCategory.hom (X.ringCatSheaf.obj.map a ≫ X.ringCatSheaf.obj.map b)) r = r
        rw [← Functor.map_comp, Subsingleton.elim (a ≫ b) (𝟙 _), CategoryTheory.Functor.map_id]
        rfl
      set ψ := restrictedSectionLinear G M V W t ((overPreimageFunctor V W).obj T.unop)
      exact ((congrArg (fun z => (ConcreteCategory.hom (M.val.map b)) (ψ.hom z))
        (G.val.map_smul a r m)).trans
        ((congrArg (ConcreteCategory.hom (M.val.map b)) (ψ.hom.map_smul _ _)).trans
          (M.val.map_smul b _ _))).trans (congrArg (· • _) hab))

/-- Restricting along `U' ≤ U` and then along `U ≤ U'` is the identity. -/
private theorem hom_map_homOfLE_hom_map_homOfLE {C : Type*} [Category C] {FC : C → C → Type*}
    {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    (F : X.Opensᵒᵖ ⥤ C) {U U' : X.Opens} (h₁ : U' ≤ U) (h₂ : U ≤ U') (z : ToType (F.obj (op U))) :
    (ConcreteCategory.hom (F.map (homOfLE h₂).op))
      ((ConcreteCategory.hom (F.map (homOfLE h₁).op)) z) = z := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _),
    CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

include hW in
/-- The inverse map undoes the forward map. -/
theorem internalHomRestrictOpenSectionsInv_fun
    (s : ((sheafHomFunctor X G).obj M).val.obj (op W)) :
    internalHomRestrictOpenSectionsInv G M V W hW (internalHomRestrictOpenSectionsFun G M V W s) =
      s := by
  refine (PresheafOfModules.toPresheaf _).map_injective (NatTrans.ext (funext fun T => ?_))
  refine ConcreteCategory.hom_ext _ _ fun m => ?_
  have hle := (image_preimage_eq_of_le V ((leOfHom T.unop.hom).trans hW)).le
  let g : (overImageFunctor V W).obj ((overPreimageFunctor V W).obj T.unop) ⟶ T.unop :=
    Over.homMk (homOfLE hle) (Subsingleton.elim _ _)
  have hnat := PresheafOfModules.naturality_apply s g.op m
  refine (internalHomRestrictOpenSectionsInvNatTrans_app_apply G M V W hW _ T m).trans ?_
  exact (congrArg (ConcreteCategory.hom (M.val.presheaf.map (homOfLE (image_preimage_eq_of_le V
    ((leOfHom T.unop.hom).trans hW)).ge).op)) hnat).trans
    (hom_map_homOfLE_hom_map_homOfLE M.val.presheaf _ _ _)

/-- Restricting a section to an equal open and back is the identity. -/
theorem presheaf_map_homOfLE_apply_apply (F : X.Modules) {U U' : X.Opens} (h₁ : U' ≤ U)
    (h₂ : U ≤ U') (z : F.val.presheaf.obj (op U)) :
    (ConcreteCategory.hom (F.val.presheaf.map (homOfLE h₂).op))
      ((ConcreteCategory.hom (F.val.presheaf.map (homOfLE h₁).op)) z) = z := by
  exact hom_map_homOfLE_hom_map_homOfLE F.val.presheaf h₁ h₂ z

include hW in
/-- The forward map undoes the inverse map. -/
theorem internalHomRestrictOpenSectionsFun_inv
    (t : ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
      (op (V.ι ⁻¹ᵁ W))) :
    internalHomRestrictOpenSectionsFun G M V W (internalHomRestrictOpenSectionsInv G M V W hW t) =
      t := by
  refine (PresheafOfModules.toPresheaf _).map_injective (NatTrans.ext (funext fun T => ?_))
  refine ConcreteCategory.hom_ext _ _ fun m => ?_
  have hpi : V.ι ⁻¹ᵁ (V.ι ''ᵁ T.unop.left) = T.unop.left := Scheme.Hom.preimage_image_eq _ _
  let g : T.unop ⟶ (overPreimageFunctor V W).obj ((overImageFunctor V W).obj T.unop) :=
    Over.homMk (homOfLE hpi.ge) (Subsingleton.elim _ _)
  have hle := (image_preimage_eq_of_le V
    ((leOfHom ((overImageFunctor V W).obj T.unop).hom).trans hW)).le
  have hnat := NatTrans.naturality_apply (restrictedSectionNatTrans G M V W t) g.op
    ((ConcreteCategory.hom (G.val.presheaf.map (homOfLE hle).op)) m)
  refine (internalHomRestrictOpenSectionsInvNatTrans_app_apply G M V W hW t
    (op ((overImageFunctor V W).obj T.unop)) m).trans ?_
  exact hnat.symm.trans
    (congrArg (ConcreteCategory.hom ((restrictedSectionNatTrans G M V W t).app T))
      (presheaf_map_homOfLE_apply_apply G hle _ m))

include hW in
/-- **A section of `SheafHom(G, M)` over an open `W ⊆ V` is a section of
`SheafHom(G|_V, M|_V)` over the preimage of `W` in the open subscheme `V`.** Its component at an
open `T` of `V` contained in `V.ι ⁻¹ᵁ W` is the component of the given section at the image of
`T` in `X` (`internalHomRestrictOpenSectionsEquiv_app`). -/
def internalHomRestrictOpenSectionsEquiv :
    ((sheafHomFunctor X G).obj M).val.obj (op W) ≃+
      ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.obj
        (op (V.ι ⁻¹ᵁ W)) where
  toFun := internalHomRestrictOpenSectionsFun G M V W
  invFun := internalHomRestrictOpenSectionsInv G M V W hW
  left_inv := internalHomRestrictOpenSectionsInv_fun G M V W hW
  right_inv := internalHomRestrictOpenSectionsFun_inv G M V W hW
  map_add' a b := PresheafOfModules.hom_ext fun T => ModuleCat.hom_ext (LinearMap.ext fun x => rfl)

include hW in
/-- **The sectionwise description of `internalHomRestrictOpenSectionsEquiv`.** -/
theorem internalHomRestrictOpenSectionsEquiv_app (s : ((sheafHomFunctor X G).obj M).val.obj (op W))
    (T : V.toScheme.Opens) (hT : T ≤ V.ι ⁻¹ᵁ W) (x : Γ(G.restrict V.ι, T)) :
    (internalHomRestrictOpenSectionsEquiv G M V W hW s).app (op (Over.mk (homOfLE hT))) x =
      s.app (op (Over.mk (homOfLE (image_le_of_le_preimage V W hT)))) x :=
  rfl

/-- **`internalHomRestrictOpenSectionsEquiv` is natural in the open.** For `W₂ ≤ W₁ ≤ V`,
restricting a section of `SheafHom(G, M)` from `W₁` to `W₂` and reading it on `V` is reading it
on `V` and restricting from `V.ι ⁻¹ᵁ W₁` to `V.ι ⁻¹ᵁ W₂`. -/
theorem internalHomRestrictOpenSectionsEquiv_restrict {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V)
    (h₂₁ : W₂ ≤ W₁) (s : ((sheafHomFunctor X G).obj M).val.obj (op W₁)) :
    internalHomRestrictOpenSectionsEquiv G M V W₂ (h₂₁.trans h₁)
        (((sheafHomFunctor X G).obj M).val.map (homOfLE h₂₁).op s) =
      ((sheafHomFunctor V.toScheme (G.restrict V.ι)).obj (M.restrict V.ι)).val.map
        (homOfLE (Scheme.Hom.preimage_mono V.ι h₂₁)).op
          (internalHomRestrictOpenSectionsEquiv G M V W₁ h₁ s) :=
  rfl

end Stacks.Algebraization

end
