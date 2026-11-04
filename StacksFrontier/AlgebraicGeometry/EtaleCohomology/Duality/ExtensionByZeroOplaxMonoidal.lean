module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.CategoryTheory.Sites.Point.ExactPairingFiberPerfect
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkFlatTensorExact

/-!
# Extension by zero along an open immersion is monoidal off the unit

Let `j : U ⟶ X` be an open immersion. Extension by zero `j_!` of étale sheaves of `Λ`-modules is
left adjoint to the monoidal inverse image `j⁻¹`, so it is oplax monoidal
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroOplaxMonoidal`), with
`δ : j_!(A ⊗ B) ⟶ j_! A ⊗ j_! B` and `η : j_! ℤ_U ⟶ ℤ_X`. The comparison `δ` is an isomorphism
(`Stacks.EtaleCohomology.isIso_etaleModuleExtensionByZero_δ`): both sides vanish on the closed
complement `Z` of `U` (the tensor product of a zero sheaf with anything is zero), and on `U` it is
the identity up to the isomorphisms `j⁻¹ j_! ≅ 𝟭` and `j⁻¹(M ⊗ N) ≅ j⁻¹ M ⊗ j⁻¹ N`; inverse images
to `Z` and `U` jointly reflect isomorphisms. No dualizability is needed. The unit `η` is not an
isomorphism, but it becomes one after inverse image along any morphism factoring through `j`.

So a pairing `p : A ⊗ B ⟶ ℤ_U` on `U` extends to the pairing
`j_! A ⊗ j_! B ≅ j_!(A ⊗ B) ⟶ j_! ℤ_U ⟶ ℤ_X` on `X`
(`Stacks.EtaleCohomology.extensionByZeroPairing`). If `p` is the evaluation of an exact pairing,
the extended pairing, pulled back along `g₂ : Y ⟶ X` and then `g₁ : T ⟶ Y` with `g₁ ≫ g₂` factoring
through `j`, is perfect on the fibres at all points of `T` with separably closed residue field
(`Stacks.EtaleCohomology.bijective_sheafFiber_inverseImageConstantPairing_extensionByZeroPairing`):
`j_! ⋙ g₂⁻¹ ⋙ g₁⁻¹` is then a monoidal functor, which carries exact pairings to exact pairings.
This is the coefficient pairing of Poincaré duality on an open curve `U ⊂ X̄`, in the purity half
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroInverseImageAdj`: `j_! ⊣ j⁻¹`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroOplaxMonoidal`.
* `Stacks.EtaleCohomology.extensionByZeroPairing`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleExtensionByZero_δ`.
* `Stacks.EtaleCohomology.isIso_inverseImage_map_extensionByZero_η`.
* `Stacks.EtaleCohomology.bijective_sheafFiber_inverseImageConstantPairing_extensionByZeroPairing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Functor.LaxMonoidal Functor.OplaxMonoidal

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  moduleCat_hasLimitsOfSize

attribute [local instance] isMonoidal_W_etaleModules

/-- Sheafification of étale sheaves of modules at the coefficient universe `u + 1`, pinned so that
instance search does not get stuck on a universe-polymorphic instance. -/
local instance hasSheafify_smallEtale_extensionByZeroOplax (Λ : Type) [CommRing Λ]
    (S : Scheme.{u}) : HasSheafify S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} S.smallEtaleTopology Λ

section Oplax

variable (Λ : Type) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Extension by zero is left adjoint to the inverse image** along an open immersion `j`
(`j⁻¹` is restriction to `U`). -/
def etaleModuleExtensionByZeroInverseImageAdj :
    etaleModuleExtensionByZero.{u, 0} Λ j ⊣ etaleModuleInverseImage.{u, 0} Λ j :=
  (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).ofNatIsoRight
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm

/-- The unit `𝟭 ⟶ j⁻¹ j_!` is an isomorphism for an open immersion `j`. -/
instance isIso_etaleModuleExtensionByZeroInverseImageAdj_unit_app
    (A : EtaleModules.{u, 0} Λ U) :
    IsIso ((etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app A) := by
  dsimp [etaleModuleExtensionByZeroInverseImageAdj, Adjunction.ofNatIsoRight]
  infer_instance

/-- **Extension by zero along an open immersion is oplax monoidal**, as the left adjoint of the
monoidal inverse image. -/
@[instance_reducible]
def etaleModuleExtensionByZeroOplaxMonoidal :
    (etaleModuleExtensionByZero.{u, 0} Λ j).OplaxMonoidal :=
  (etaleModuleExtensionByZeroInverseImageAdj Λ j).leftAdjointOplaxMonoidal

/-- Composing the unit with `j⁻¹ δ` gives the tensor product of the units followed by the tensor
comparison of `j⁻¹`. -/
theorem unit_comp_inverseImage_map_extensionByZero_δ (A B : EtaleModules.{u, 0} Λ U) :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    (etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app (A ⊗ B) ≫
        (etaleModuleInverseImage.{u, 0} Λ j).map
          (δ (etaleModuleExtensionByZero.{u, 0} Λ j) A B) =
      ((etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app A ⊗ₘ
        (etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app B) ≫
        μ (etaleModuleInverseImage.{u, 0} Λ j) _ _ := by
  let := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  exact ((etaleModuleExtensionByZeroInverseImageAdj Λ j).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply ((etaleModuleExtensionByZeroInverseImageAdj Λ j).homEquiv _ _) _)

/-- Composing the unit with `j⁻¹ η` gives the unit comparison of `j⁻¹`. -/
theorem unit_comp_inverseImage_map_extensionByZero_η :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    (etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app (𝟙_ _) ≫
        (etaleModuleInverseImage.{u, 0} Λ j).map (η (etaleModuleExtensionByZero.{u, 0} Λ j)) =
      ε (etaleModuleInverseImage.{u, 0} Λ j) := by
  let := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  exact ((etaleModuleExtensionByZeroInverseImageAdj Λ j).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply ((etaleModuleExtensionByZeroInverseImageAdj Λ j).homEquiv _ _) _)

/-- A sheaf tensored with a zero sheaf is zero: `- ⊗ N` preserves colimits, hence is additive. -/
theorem isZero_tensorObj_etaleModules_of_isZero_left {S : Scheme.{u}}
    {M : EtaleModules.{u, 0} Λ S} (N : EtaleModules.{u, 0} Λ S) (hM : IsZero M) :
    IsZero (M ⊗ N) := by
  have : PreservesColimitsOfSize.{u, u + 1} (MonoidalCategory.tensorRight N) :=
    Sheaf.preservesColimitsOfSize_tensorRight_moduleCat.{u + 1, u, u + 1, 0} N
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight N) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesColimitsOfShape (Discrete WalkingPair) (MonoidalCategory.tensorRight N) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have : PreservesBinaryBiproducts (MonoidalCategory.tensorRight N) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (MonoidalCategory.tensorRight N).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact (MonoidalCategory.tensorRight N).map_isZero hM

/-- **`j_!(A ⊗ B) ⟶ j_! A ⊗ j_! B` is an isomorphism** for an open immersion `j`. On the closed
complement `Z` both sides vanish; on `U` it is, up to the isomorphisms `j⁻¹ j_! ≅ 𝟭`, the tensor
comparison of `j⁻¹`; inverse images to `Z` and `U` jointly reflect isomorphisms. -/
instance isIso_etaleModuleExtensionByZero_δ (A B : EtaleModules.{u, 0} Λ U) :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    IsIso (δ (etaleModuleExtensionByZero.{u, 0} Λ j) A B) := by
  letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  let L := etaleModuleExtensionByZero.{u, 0} Λ j
  let J := etaleModuleInverseImage.{u, 0} Λ j
  let adj := etaleModuleExtensionByZeroInverseImageAdj Λ j
  let Zc : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  have hij : Set.range j.base = (Set.range i.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact (compl_compl _).symm
  let I := etaleModuleInverseImage.{u, 0} Λ i
  haveI : IsIso (J.map (δ L A B)) := by
    have h : J.map (δ L A B) = inv (adj.unit.app (A ⊗ B)) ≫
        ((adj.unit.app A ⊗ₘ adj.unit.app B) ≫ μ J (L.obj A) (L.obj B)) := by
      rw [← unit_comp_inverseImage_map_extensionByZero_δ Λ j A B, IsIso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  have h₁ : IsZero (I.obj (L.obj (A ⊗ B))) :=
    isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _
  have h₂ : IsZero (I.obj (L.obj A ⊗ L.obj B)) :=
    (isZero_tensorObj_etaleModules_of_isZero_left Λ _
      (isZero_etaleModuleInverseImage_extensionByZero Λ i j hij A)).of_iso
      (Functor.Monoidal.μIso I (L.obj A) (L.obj B)).symm
  haveI : IsIso (I.map (δ L A B)) :=
    ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

/-- `j⁻¹ η` is an isomorphism: it is the unit comparison of `j⁻¹` up to the unit of
`j_! ⊣ j⁻¹`. -/
instance isIso_inverseImage_map_extensionByZero_η_self :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    IsIso ((etaleModuleInverseImage.{u, 0} Λ j).map
      (η (etaleModuleExtensionByZero.{u, 0} Λ j))) := by
  letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  have h : (etaleModuleInverseImage.{u, 0} Λ j).map (η (etaleModuleExtensionByZero.{u, 0} Λ j)) =
      inv ((etaleModuleExtensionByZeroInverseImageAdj Λ j).unit.app (𝟙_ _)) ≫
        ε (etaleModuleInverseImage.{u, 0} Λ j) := by
    rw [← unit_comp_inverseImage_map_extensionByZero_η Λ j, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- **`g⁻¹ η` is an isomorphism for `g` factoring through `j`.** -/
theorem isIso_inverseImage_map_extensionByZero_η {T : Scheme.{u}} (h : T ⟶ U) (g : T ⟶ X)
    (w : h ≫ j = g) :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    IsIso ((etaleModuleInverseImage.{u, 0} Λ g).map
      (η (etaleModuleExtensionByZero.{u, 0} Λ j))) := by
  let := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  subst w
  refine (NatIso.isIso_map_iff (etaleModuleInverseImageCompIso.{u, 0} Λ h j) _).2 ?_
  show IsIso ((etaleModuleInverseImage.{u, 0} Λ h).map ((etaleModuleInverseImage.{u, 0} Λ j).map
    (η (etaleModuleExtensionByZero.{u, 0} Λ j))))
  infer_instance

/-- **`g₁⁻¹ g₂⁻¹ η` is an isomorphism for `g₁ ≫ g₂` factoring through `j`.** -/
theorem isIso_inverseImage_inverseImage_map_extensionByZero_η {Y T : Scheme.{u}} (g₂ : Y ⟶ X)
    (g₁ : T ⟶ Y) (h : T ⟶ U) (w : h ≫ j = g₁ ≫ g₂) :
    letI := etaleModuleExtensionByZeroOplaxMonoidal Λ j
    IsIso ((etaleModuleInverseImage.{u, 0} Λ g₁).map ((etaleModuleInverseImage.{u, 0} Λ g₂).map
      (η (etaleModuleExtensionByZero.{u, 0} Λ j)))) := by
  let := etaleModuleExtensionByZeroOplaxMonoidal Λ j
  have := isIso_inverseImage_map_extensionByZero_η Λ j h (g₁ ≫ g₂) w
  exact (NatIso.isIso_map_iff (etaleModuleInverseImageCompIso.{u, 0} Λ g₁ g₂).symm _).2
    inferInstance

end Oplax

/-! ### Extending a pairing by zero -/

section Pairing

variable (N : ℕ) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **A pairing on `U` extended by zero**: `j_! A ⊗ j_! B ≅ j_!(A ⊗ B) ⟶ j_! ℤ/N_U ⟶ ℤ/N_X` for
`p : A ⊗ B ⟶ ℤ/N_U`, the first map the inverse of the tensor comparison of `j_!`
(`Stacks.EtaleCohomology.isIso_etaleModuleExtensionByZero_δ`), the last its unit comparison. -/
def extensionByZeroPairing {A B : EtaleModules.{u, 0} (ZMod N) U}
    (p : A ⊗ B ⟶ 𝟙_ (EtaleModules.{u, 0} (ZMod N) U)) :
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj A ⊗
        (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj B ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) X.smallEtaleTopology :=
  letI := etaleModuleExtensionByZeroOplaxMonoidal (ZMod N) j
  inv (δ (etaleModuleExtensionByZero.{u, 0} (ZMod N) j) A B) ≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod N) j).map p ≫
      η (etaleModuleExtensionByZero.{u, 0} (ZMod N) j)

attribute [local instance] AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

/-- **The pulled back extension by zero of an exact pairing is perfect over `U`.** Let
`p = ε_ B A : A ⊗ B ⟶ ℤ/N_U` be the evaluation of an exact pairing on `U`, `g₂ : Y ⟶ X`,
`g₁ : T ⟶ Y` with `g₁ ≫ g₂ = h ≫ j`. Then the pullback along `g₂` and then `g₁` of
`Stacks.EtaleCohomology.extensionByZeroPairing j p` is perfect on the fibres at all points of `T`
with separably closed residue field. Indeed `j_! ⋙ g₂⁻¹ ⋙ g₁⁻¹` is oplax monoidal with invertible
comparisons (`δ` of `j_!` is invertible, and so is `g₁⁻¹ g₂⁻¹ η`), hence monoidal; it carries the
exact pairing to an exact pairing whose evaluation is the pulled back pairing up to an
automorphism of the target, and fibre functors carry exact pairings to exact pairings of modules,
whose evaluations are perfect. -/
theorem bijective_sheafFiber_inverseImageConstantPairing_extensionByZeroPairing
    {Y T : Scheme.{u}} (g₂ : Y ⟶ X) (g₁ : T ⟶ Y) (h : T ⟶ U) (w : h ≫ j = g₁ ≫ g₂)
    (A B : EtaleModules.{u, 0} (ZMod N) U) [ExactPairing B A]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod N)))
      ((etaleModuleInverseImage.{u, 0} (ZMod N) g₁).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g₂).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj A)))
      ((etaleModuleInverseImage.{u, 0} (ZMod N) g₁).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) g₂).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod N) j).obj B))) ≫
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod N))).map
        (inverseImageConstantPairing g₁ N
          (inverseImageConstantPairing g₂ N (extensionByZeroPairing N j (ε_ B A))))).hom) := by
  let := etaleModuleExtensionByZeroOplaxMonoidal (ZMod N) j
  let L := etaleModuleExtensionByZero.{u, 0} (ZMod N) j
  let I₂ := etaleModuleInverseImage.{u, 0} (ZMod N) g₂
  let I₁ := etaleModuleInverseImage.{u, 0} (ZMod N) g₁
  let G := L ⋙ I₂ ⋙ I₁
  let Ψ := ((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
    (A := ModuleCat.{u + 1} (ZMod N))
  let c₂ := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod N)
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) g₂
  let c₁ := inverseImageEtaleModuleConstantSheafIso.{u, 0} (ZMod N)
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N))) g₁
  have : IsIso (I₁.map (I₂.map (η L))) :=
    isIso_inverseImage_inverseImage_map_extensionByZero_η (ZMod N) j g₂ g₁ h w
  have hη : IsIso (η G) := by
    show IsIso (I₁.map (I₂.map (η L)) ≫ (I₁.map (η I₂) ≫ η I₁))
    infer_instance
  have hδ : ∀ P Q, IsIso (δ G P Q) := fun P Q => by
    show IsIso ((I₂ ⋙ I₁).map (δ L P Q) ≫ (I₁.map (δ I₂ _ _) ≫ δ I₁ _ _))
    infer_instance
  let : G.Monoidal := (Functor.CoreMonoidal.ofOplaxMonoidal G).toMonoidal
  let : ExactPairing (G.obj B) (G.obj A) := ExactPairing.map G B A
  let : ExactPairing (Ψ.obj (G.obj B)) (Ψ.obj (G.obj A)) :=
    ExactPairing.map Ψ (G.obj B) (G.obj A)
  -- the unit isomorphism of the target
  let iT : 𝟙_ (EtaleModules.{u, 0} (ZMod N) T) ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod N) T.smallEtaleTopology :=
    Functor.Monoidal.εIso I₁ ≪≫ I₁.mapIso (Functor.Monoidal.εIso I₂ ≪≫ c₂) ≪≫ c₁
  have key : inverseImageConstantPairing g₁ N
      (inverseImageConstantPairing g₂ N (extensionByZeroPairing N j (ε_ B A))) =
      ε_ (G.obj B) (G.obj A) ≫ iT.hom := by
    have hμG : μ G A B = μ I₁ _ _ ≫ I₁.map (μ I₂ _ _ ≫ I₂.map (inv (δ L A B))) := by
      show inv (δ G A B) = _
      refine IsIso.inv_eq_of_hom_inv_id ?_
      show (I₁.map (I₂.map (δ L A B)) ≫ I₁.map (δ I₂ _ _) ≫ δ I₁ _ _) ≫ _ = 𝟙 _
      rw [Category.assoc, Category.assoc, Functor.Monoidal.δ_μ_assoc, ← I₁.map_comp,
        ← I₁.map_comp, Functor.Monoidal.δ_μ_assoc, ← I₂.map_comp, IsIso.hom_inv_id, I₂.map_id,
        I₁.map_id]
    have hηG : @Functor.OplaxMonoidal.η _ _ _ _ _ _ G Functor.Monoidal.toOplaxMonoidal =
        I₁.map (I₂.map (η L)) ≫ I₁.map (η I₂) ≫ η I₁ := rfl
    rw [ExactPairing.map_evaluation, hμG, hηG]
    show μ I₁ _ _ ≫ I₁.map (μ I₂ _ _ ≫ I₂.map (inv (δ L A B) ≫ L.map (ε_ B A) ≫ η L) ≫
        c₂.hom) ≫ c₁.hom =
      ((μ I₁ _ _ ≫ I₁.map (μ I₂ _ _ ≫ I₂.map (inv (δ L A B)))) ≫
        I₁.map (I₂.map (L.map (ε_ B A))) ≫ I₁.map (I₂.map (η L)) ≫ I₁.map (η I₂) ≫ η I₁) ≫
        ε I₁ ≫ I₁.map (ε I₂ ≫ c₂.hom) ≫ c₁.hom
    simp only [Functor.map_comp, Category.assoc, Functor.Monoidal.η_ε_assoc]
    have hηε : η I₂ ≫ ε I₂ ≫ c₂.hom = c₂.hom := Functor.Monoidal.η_ε_assoc I₂ _
    rw [← I₁.map_comp_assoc (η I₂) (ε I₂ ≫ c₂.hom), hηε,
      ← I₁.map_comp_assoc (I₂.map (η L)) c₂.hom,
      ← I₁.map_comp_assoc (I₂.map (L.map (ε_ B A))) _,
      ← I₁.map_comp_assoc (I₂.map (inv (δ L A B))) _]
    rfl
  let iT' := Functor.Monoidal.εIso Ψ ≪≫ Ψ.mapIso iT
  have key' : Functor.LaxMonoidal.μ Ψ (G.obj A) (G.obj B) ≫
      Ψ.map (inverseImageConstantPairing g₁ N
        (inverseImageConstantPairing g₂ N (extensionByZeroPairing N j (ε_ B A)))) =
      ε_ (Ψ.obj (G.obj B)) (Ψ.obj (G.obj A)) ≫ iT'.hom := by
    rw [key, ExactPairing.map_evaluation Ψ (G.obj B) (G.obj A)]
    simp only [iT', Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom,
      Category.assoc, Functor.Monoidal.η_ε_assoc, Functor.map_comp]
  show Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ Ψ (G.obj A) (G.obj B) ≫
      Ψ.map (inverseImageConstantPairing g₁ N
        (inverseImageConstantPairing g₂ N (extensionByZeroPairing N j (ε_ B A))))).hom)
  rw [key']
  exact Stacks.SheafDuality.bijective_curry_comp_iso _ iT'
    (Stacks.SheafDuality.bijective_curry_evaluation_of_exactPairing
      (Ψ.obj (G.obj A)) (Ψ.obj (G.obj B)))

end Pairing

end Stacks.EtaleCohomology

end
