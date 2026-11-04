module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightOperator

/-!
# The box product of the identity with a differential operator, on external tensor sections

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `F` be a quasi-coherent
`𝒪_X`-module and let `E : G ⟶ G'` be a differential operator of order at most `l` between
quasi-coherent `𝒪_Y`-modules. The operator `1 ⊠ E` of
`AlgebraicGeometry.boxOpRight` is `E ⊠ 1` on `Y ×_S X`, read through the symmetry of the fibre
product, so its value on the section of `F ⊠ G` attached to a pair of local sections is computed
from `AlgebraicGeometry.boxOpLeft_externalTensorSection` on `Y ×_S X`: it carries the section
attached to `s` and `t` to the section attached to `s` and `E t`. As on the left, the resulting
operator does not depend on the order bound used to build it, so the morphism
`AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHomRight` of the category of
finite-order differential operators is canonical.

## Main results

* `AlgebraicGeometry.externalTensorProductSwapIso_hom_externalTensorSection`: the identification
  of `F ⊠ G` with the inverse image of `G ⊠ F` along the symmetry of the fibre product carries the
  section attached to a pair of local sections to the pullback of the section attached to the same
  pair in the other order.
* `AlgebraicGeometry.boxOpRight_externalTensorSection`: `1 ⊠ E` carries the section of `F ⊠ G`
  attached to a pair of local sections `s` of `F` and `t` of `G` to the section of `F ⊠ G'`
  attached to `s` and `E t`.
* `AlgebraicGeometry.boxOpRight_eq_of_order`: `1 ⊠ E` does not depend on the order bound used to
  construct it.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHomRight_coe` and
  `boxHomRight_externalTensorSection`: the underlying operator of the morphism `1 ⊠ E` of the
  category of finite-order differential operators is `1 ⊠ E` for any order bound of `E`, and its
  characterisation on the sections attached to pairs of local sections.

## Implementation notes

The order bound enters `AlgebraicGeometry.boxOpRight` only through
`AlgebraicGeometry.boxOpLeft`: the three conjugations transporting the operator across the
symmetry are subtype equivalences whose underlying maps are independent of the order, so
independence of the bound is `AlgebraicGeometry.boxOpLeft_eq_of_order` transported, and no second
gluing argument is needed.

The transport across the symmetry `σ : X ×_S Y ⟶ Y ×_S X` is read on sections with
`AlgebraicGeometry.Scheme.Modules.pullbackSection` rather than with the unit of `σ^* ⊣ σ_*` alone:
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection` is stated over an
arbitrary open of the source, so the equality `σ⁻¹(σ(W)) = W` is absorbed into a chain of
inclusions of opens, which `Subsingleton (U ⟶ V)` collapses, and no transport along an equality of
opens appears.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

/-- Restriction of a section of a sheaf of modules along any endomorphism of an open of a scheme
is the identity: the opens of a scheme form a poset, so that endomorphism is the identity. -/
theorem presheaf_map_self {Z : Scheme.{u}} (M : Z.Modules) (U : Z.Opens) (i : op U ⟶ op U)
    (x : Γ(M, U)) : M.presheaf.map i x = x :=
  (ConcreteCategory.congr_hom
    ((congrArg M.presheaf.map (Subsingleton.elim i (𝟙 (op U)))).trans
      (M.presheaf.map_id (op U))) x).trans (ConcreteCategory.id_apply x)

/-- An isomorphism of sheaves of modules followed by its inverse is the identity on sections. -/
theorem modulesHomApp_inv_hom {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (U : Z.Opens)
    (x : Γ(M, U)) :
    Scheme.Modules.Hom.app e.inv U (Scheme.Modules.Hom.app e.hom U x) = x := by
  have h : Scheme.Modules.Hom.app e.hom U ≫ Scheme.Modules.Hom.app e.inv U = 𝟙 _ := by
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  exact ConcreteCategory.congr_hom h x

/-- The inverse of an isomorphism of sheaves of modules followed by the isomorphism is the identity
on sections. -/
theorem modulesHomApp_hom_inv {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (U : Z.Opens)
    (x : Γ(N, U)) :
    Scheme.Modules.Hom.app e.hom U (Scheme.Modules.Hom.app e.inv U x) = x :=
  modulesHomApp_inv_hom e.symm U x

section Swap

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G : Y.Modules)

/-- The image under the symmetry of the fibre product of an open inside `pr₂⁻¹V` lies inside the
preimage of `V` under the first projection of the other fibre product. -/
theorem image_pullbackSwapMor_le_fst {V' : Y.Opens} (W : (pullback a b).Opens)
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    pullbackSwapMor a b ''ᵁ W ≤ pullback.fst b a ⁻¹ᵁ V' := by
  refine Set.image_subset_iff.2 ?_
  show W ≤ (pullbackSwapMor a b ≫ pullback.fst b a) ⁻¹ᵁ V'
  rw [pullback.lift_fst]
  exact hW₂

/-- The image under the symmetry of the fibre product of an open inside `pr₁⁻¹U` lies inside the
preimage of `U` under the second projection of the other fibre product. -/
theorem image_pullbackSwapMor_le_snd {U' : X.Opens} (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') :
    pullbackSwapMor a b ''ᵁ W ≤ pullback.snd b a ⁻¹ᵁ U' := by
  refine Set.image_subset_iff.2 ?_
  show W ≤ (pullbackSwapMor a b ≫ pullback.snd b a) ⁻¹ᵁ U'
  rw [pullback.lift_snd]
  exact hW₁

/-- **The pullback of `G ⊠ F` along the symmetry of the fibre product, on the section attached to a
pair of local sections.** The identification of the inverse image of `G ⊠ F` along the symmetry
with `pr₂^*G ⊗ pr₁^*F` carries the pullback of the section attached to `t` over `V'` and `s` over
`U'` to the section coming from the pure tensor of the two unit images, restricted to `W`. -/
theorem pullbackLift_externalTensorProductIso_hom_pullbackSection_swap {U' : X.Opens}
    {V' : Y.Opens} (s : Γ(F, U')) (t : Γ(G, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    Scheme.Modules.Hom.app
        (pullbackLift_externalTensorProductIso b a (pullback.snd a b) (pullback.fst a b)
          pullback.condition.symm G F).hom W
        (Scheme.Modules.pullbackSection (pullbackSwapMor a b)
          (externalTensorProduct b a G F) (pullbackSwapMor a b ''ᵁ W) W
          (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).ge
          (externalTensorSection b a G F t s (pullbackSwapMor a b ''ᵁ W)
            (image_pullbackSwapMor_le_fst a b W hW₂)
            (image_pullbackSwapMor_le_snd a b W hW₁)))
      = toTensorSheafSection (pullback a b).toRingedSpace
          ((Scheme.Modules.pullback (pullback.snd a b)).obj G)
          ((Scheme.Modules.pullback (pullback.fst a b)).obj F) (op W)
          (((Scheme.Modules.pullback (pullback.snd a b)).obj G).presheaf.map (homOfLE hW₂).op
              (modulesPullbackUnit (pullback.snd a b) G V' t) ⊗ₜ
            ((Scheme.Modules.pullback (pullback.fst a b)).obj F).presheaf.map (homOfLE hW₁).op
              (modulesPullbackUnit (pullback.fst a b) F U' s)) := by
  have hle : W ≤ pullbackSwapMor a b ⁻¹ᵁ (pullbackSwapMor a b ''ᵁ W) :=
    (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).ge
  have hj₁ : pullbackSwapMor a b ⁻¹ᵁ (pullbackSwapMor a b ''ᵁ W) ≤ pullback.snd a b ⁻¹ᵁ V' :=
    le_trans (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).le hW₂
  have hj₂ : pullbackSwapMor a b ⁻¹ᵁ (pullbackSwapMor a b ''ᵁ W) ≤ pullback.fst a b ⁻¹ᵁ U' :=
    le_trans (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).le hW₁
  have step1 := homApp_presheaf_map
    (pullbackLift_externalTensorProductIso b a (pullback.snd a b) (pullback.fst a b)
      pullback.condition.symm G F).hom (homOfLE hle)
    (modulesPullbackUnit (pullbackSwapMor a b) (externalTensorProduct b a G F)
      (pullbackSwapMor a b ''ᵁ W)
      (externalTensorSection b a G F t s (pullbackSwapMor a b ''ᵁ W)
        (image_pullbackSwapMor_le_fst a b W hW₂) (image_pullbackSwapMor_le_snd a b W hW₁)))
  have step2 := pullbackLift_externalTensorProductIso_hom_externalTensorSection b a
    (pullback.snd a b) (pullback.fst a b) pullback.condition.symm G F t s
    (pullbackSwapMor a b ''ᵁ W) (image_pullbackSwapMor_le_fst a b W hW₂)
    (image_pullbackSwapMor_le_snd a b W hW₁) hj₁ hj₂
  have step3 := toTensorSheafSection_presheaf_map
    ((Scheme.Modules.pullback (pullback.snd a b)).obj G)
    ((Scheme.Modules.pullback (pullback.fst a b)).obj F) (homOfLE hle)
    (((Scheme.Modules.pullback (pullback.snd a b)).obj G).presheaf.map (homOfLE hj₁).op
      (modulesPullbackUnit (pullback.snd a b) G V' t))
    (((Scheme.Modules.pullback (pullback.fst a b)).obj F).presheaf.map (homOfLE hj₂).op
      (modulesPullbackUnit (pullback.fst a b) F U' s))
  have step4 := presheaf_map_map ((Scheme.Modules.pullback (pullback.snd a b)).obj G)
    (homOfLE hj₁) (homOfLE hle) (homOfLE hW₂) (modulesPullbackUnit (pullback.snd a b) G V' t)
  have step5 := presheaf_map_map ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
    (homOfLE hj₂) (homOfLE hle) (homOfLE hW₁) (modulesPullbackUnit (pullback.fst a b) F U' s)
  refine step1.trans ((congrArg (fun z => (Scheme.Modules.presheaf
      (X := pullback a b) ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(pullback a b).toRingedSpace.presheaf, (pullback a b).toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback (pullback.snd a b)).obj G)).obj
          ((Scheme.Modules.pullback (pullback.fst a b)).obj F)))).map
      (homOfLE hle).op z) step2).trans (step3.trans ?_))
  exact congrArg₂ (fun (z : Γ((Scheme.Modules.pullback (pullback.snd a b)).obj G, W))
      (wz : Γ((Scheme.Modules.pullback (pullback.fst a b)).obj F, W)) =>
    toTensorSheafSection (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G)
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F) (op W) (z ⊗ₜ wz)) step4 step5

/-- **The box product across the symmetry of a fibre product, on the section attached to a pair of
local sections.** The identification of `F ⊠ G` with the inverse image of `G ⊠ F` along the
symmetry carries the section of `F ⊠ G` attached to `s` over `U'` and `t` over `V'` to the pullback
of the section of `G ⊠ F` attached to `t` and `s`. -/
theorem externalTensorProductSwapIso_hom_externalTensorSection {U' : X.Opens} {V' : Y.Opens}
    (s : Γ(F, U')) (t : Γ(G, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G).hom W
        (externalTensorSection a b F G s t W hW₁ hW₂)
      = Scheme.Modules.pullbackSection (pullbackSwapMor a b)
          (externalTensorProduct b a G F) (pullbackSwapMor a b ''ᵁ W) W
          (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).ge
          (externalTensorSection b a G F t s (pullbackSwapMor a b ''ᵁ W)
            (image_pullbackSwapMor_le_fst a b W hW₂)
            (image_pullbackSwapMor_le_snd a b W hW₁)) := by
  refine modulesHomApp_trans
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap (pullback a b).toRingedSpace
      ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
      ((Scheme.Modules.pullback (pullback.snd a b)).obj G))
    (pullbackLift_externalTensorProductIso b a (pullback.snd a b) (pullback.fst a b)
      pullback.condition.symm G F).symm W
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_app_toTensorSheafSection
      (pullback a b).toRingedSpace _ _ W _ _) ?_
  exact (congrArg (fun z => Scheme.Modules.Hom.app
        (pullbackLift_externalTensorProductIso b a (pullback.snd a b) (pullback.fst a b)
          pullback.condition.symm G F).symm.hom W z)
      (pullbackLift_externalTensorProductIso_hom_pullbackSection_swap a b F G s t W
        hW₁ hW₂).symm).trans
    (modulesHomApp_inv_hom _ W _)

/-- **The transport of the section attached to a pair of local sections across the symmetry of a
fibre product.** Reading `F ⊠ G` as the inverse image of `G ⊠ F` along the symmetry and then
comparing the inverse image with the restriction carries the section of `F ⊠ G` attached to `s`
over `U'` and `t` over `V'` to the section of `G ⊠ F` over the image of `W`, attached to `t`
and `s`. -/
theorem restrictFunctorIsoPullback_inv_externalTensorProductSwapIso_hom {U' : X.Opens}
    {V' : Y.Opens} (s : Γ(F, U')) (t : Γ(G, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
          (externalTensorProduct b a G F)).inv W
        (Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G).hom W
          (externalTensorSection a b F G s t W hW₁ hW₂))
      = externalTensorSection b a G F t s (pullbackSwapMor a b ''ᵁ W)
          (image_pullbackSwapMor_le_fst a b W hW₂)
          (image_pullbackSwapMor_le_snd a b W hW₁) := by
  rw [externalTensorProductSwapIso_hom_externalTensorSection a b F G s t W hW₁ hW₂]
  refine (Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (pullbackSwapMor a b)
    (externalTensorProduct b a G F) (pullbackSwapMor a b ''ᵁ W) W
    (Scheme.Hom.preimage_image_eq (pullbackSwapMor a b) W).ge (le_refl _) _).trans ?_
  exact presheaf_map_self (externalTensorProduct b a G F) (pullbackSwapMor a b ''ᵁ W) _ _

end Swap

section

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G G' : Y.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsQuasicoherent] (l : ℕ)
  (E : DiffOp.GlobalOp G G')
  (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E)

/-- `1 ⊠ E` is the four-fold conjugate of `E ⊠ 1` on `Y ×_S X`: the identification of `F ⊠ G` with
the inverse image of `G ⊠ F` along the symmetry, the comparison of the inverse image with the
restriction, `E ⊠ 1` read over the image of the open, and the two inverses. -/
theorem boxOpRight_apply (W : (pullback a b).Opens)
    (x : Γ(externalTensorProduct a b F G, W)) :
    boxOpRight a b F G G' l E hE (op W) x =
      Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G').inv W
        (Scheme.Modules.Hom.app
          (((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
            (externalTensorProduct b a G' F)).hom) W
          (boxOpLeft b a G G' F l E hE (op (pullbackSwapMor a b ''ᵁ W))
            (Scheme.Modules.Hom.app
              (((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
                (externalTensorProduct b a G F)).inv) W
              (Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G).hom W x)))) := by
  show Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G').inv W
      ((globalDiffOpEquivRestrictPullback (pullbackSwapMor a b) (pullback.fst b a ≫ b)
        (externalTensorProduct b a G F) (externalTensorProduct b a G' F) l
      (globalDiffOpEquivOfIso (pullbackSwapMor a b) (pullback.fst b a ≫ b)
          (externalTensorProduct b a G F) (externalTensorProduct b a G' F) l
        ⟨boxOpLeft b a G G' F l E hE,
          isGlobalDiffOpOfOrder_boxOpLeft_base b a G G' F l E hE⟩)).1 (op W)
        (Scheme.Modules.Hom.app (externalTensorProductSwapIso a b F G).hom W x)) = _
  congr 1
  show Scheme.Modules.Hom.app
          (((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
            (externalTensorProduct b a G' F)).hom) W
          ((globalDiffOpEquivOfIso (pullbackSwapMor a b) (pullback.fst b a ≫ b)
              (externalTensorProduct b a G F) (externalTensorProduct b a G' F) l
            ⟨boxOpLeft b a G G' F l E hE,
              isGlobalDiffOpOfOrder_boxOpLeft_base b a G G' F l E hE⟩).1 (op W) _) = _
  congr 1
  exact congrArg (fun (f : _ →+ _) => f _) (globalDiffOpEquivOfIso_coe_apply _ _ _ _ _ _ W)

/-- **`1 ⊠ E` on the section attached to a pair of local sections.** It carries the section of
`F ⊠ G` attached to a section `s` of `F` over `U'` and a section `t` of `G` over `V'`, over any
open `W` of `X ×_S Y` inside `pr₁⁻¹U' ⊓ pr₂⁻¹V'`, to the section of `F ⊠ G'` attached to `s`
and `E t`. -/
theorem boxOpRight_externalTensorSection {U' : X.Opens} {V' : Y.Opens} (s : Γ(F, U'))
    (t : Γ(G, V')) (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    boxOpRight a b F G G' l E hE (op W) (externalTensorSection a b F G s t W hW₁ hW₂) =
      externalTensorSection a b F G' s (E (op V') t) W hW₁ hW₂ := by
  rw [boxOpRight_apply a b F G G' l E hE W,
    restrictFunctorIsoPullback_inv_externalTensorProductSwapIso_hom a b F G s t W hW₁ hW₂,
    boxOpLeft_externalTensorSection b a G G' F l E hE t s (pullbackSwapMor a b ''ᵁ W)
      (image_pullbackSwapMor_le_fst a b W hW₂) (image_pullbackSwapMor_le_snd a b W hW₁),
    ← restrictFunctorIsoPullback_inv_externalTensorProductSwapIso_hom a b F G' s
      (E (op V') t) W hW₁ hW₂,
    modulesHomApp_hom_inv, modulesHomApp_inv_hom]

end

section Order

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F : X.Modules) (G G' : Y.Modules)
  [F.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsQuasicoherent]
  (E : DiffOp.GlobalOp G G')

/-- Transport of a differential operator across an isomorphism of schemes depends only on the
underlying operator, not on the order bound carried alongside it. -/
theorem globalDiffOpEquivOfIso_coe_congr {Z Z' T : Scheme.{u}} (e : Z ⟶ Z') [IsIso e]
    (p : Z' ⟶ T) (M M' : Z'.Modules) {k l : ℕ}
    (D : {D : DiffOp.GlobalOp M M' //
      DiffOp.IsGlobalDiffOpOfOrder p.relativeStructureSheafMap k D})
    (D' : {D : DiffOp.GlobalOp M M' //
      DiffOp.IsGlobalDiffOpOfOrder p.relativeStructureSheafMap l D})
    (h : D.1 = D'.1) :
    (globalDiffOpEquivOfIso e p M M' k D).1 = (globalDiffOpEquivOfIso e p M M' l D').1 := by
  funext V
  refine (globalDiffOpEquivOfIso_coe_apply e p M M' k D V.unop).trans ?_
  rw [h]
  exact (globalDiffOpEquivOfIso_coe_apply e p M M' l D' V.unop).symm

/-- **`1 ⊠ E` does not depend on the order bound used to build it.** The order bound enters only
through the box product `E ⊠ 1` on `Y ×_S X`, and the three conjugations transporting that
operator across the symmetry of the fibre product do not involve it. -/
theorem boxOpRight_eq_of_order {k l : ℕ}
    (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap k E)
    (hE' : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E) :
    boxOpRight a b F G G' k E hE = boxOpRight a b F G G' l E hE' :=
  congrArg (fun T => globalOpCongr (externalTensorProductSwapIso a b F G).symm
      (externalTensorProductSwapIso a b F G').symm
      (globalOpCongr ((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
          (externalTensorProduct b a G F))
        ((Scheme.Modules.restrictFunctorIsoPullback (pullbackSwapMor a b)).app
          (externalTensorProduct b a G' F)) T))
    (globalDiffOpEquivOfIso_coe_congr (pullbackSwapMor a b) (pullback.fst b a ≫ b)
      (externalTensorProduct b a G F) (externalTensorProduct b a G' F)
      ⟨boxOpLeft b a G G' F k E hE, isGlobalDiffOpOfOrder_boxOpLeft_base b a G G' F k E hE⟩
      ⟨boxOpLeft b a G G' F l E hE', isGlobalDiffOpOfOrder_boxOpLeft_base b a G G' F l E hE'⟩
      (boxOpLeft_eq_of_order b a G G' F E hE hE'))

end Order

namespace FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- The underlying operator of `1 ⊠ E` is the transported box product of the identity with `E`,
for any order bound of `E`. -/
theorem boxHomRight_coe (F : FiniteOrderDifferentialOperatorCategory a)
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G') {l : ℕ}
    (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E.1) :
    (boxHomRight F E).1 = boxOpRight a b F.module G.module G'.module l E.1 hE :=
  boxOpRight_eq_of_order a b F.module G.module G'.module E.1 E.2.choose_spec hE

/-- **`1 ⊠ E` on the section attached to a pair of local sections.** -/
theorem boxHomRight_externalTensorSection (F : FiniteOrderDifferentialOperatorCategory a)
    {G G' : FiniteOrderDifferentialOperatorCategory b} (E : G ⟶ G') {U' : X.Opens} {V' : Y.Opens}
    (s : Γ(F.module, U')) (t : Γ(G.module, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    (boxHomRight F E).1 (op W)
        (externalTensorSection a b F.module G.module s t W hW₁ hW₂) =
      externalTensorSection a b F.module G'.module s (E.1 (op V') t) W hW₁ hW₂ :=
  boxOpRight_externalTensorSection a b F.module G.module G'.module E.2.choose E.1
    E.2.choose_spec s t W hW₁ hW₂

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry

end
