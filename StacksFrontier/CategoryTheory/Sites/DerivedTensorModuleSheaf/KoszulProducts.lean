module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Koszul
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts

/-!
# Tensoring with the Koszul complex commutes with countable products

Let `(C, J)` be a site, `Λ` a commutative ring and `f₁, …, f_r ∈ Λ`. The Koszul complex
`Kos(f)` of sheaves of `Λ`-modules is K-flat, and tensoring with it in `D(C, Λ)` commutes with
countable products.

## Main results

* `Stacks.ModuleSheaf.kFlat_koszulTensor`, `Stacks.ModuleSheaf.kFlat_koszulComplex`: the Koszul
  complex is K-flat.
* `Stacks.ModuleSheaf.isIso_lift_Q_map_map₂CochainComplex_koszulTensor`: the comparison maps out
  of the tensor product of a product are isomorphisms after tensoring with iterated cones.
* `Stacks.ModuleSheaf.preservesLimitsOfShape_tensorRight_koszulComplex`: tensoring with
  `Kos(f)` in `D(C, Λ)` preserves countable products.

## References

* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
  CochainComplex.KFlatBifunctor

universe t w v u

namespace Stacks.ModuleSheaf

/-- Countable products of complexes, from countable products of the terms. -/
private theorem hasProduct_cochainComplex {A : Type*} [Category A] [Preadditive A]
    [HasProductsOfShape ℕ A] (K : ℕ → CochainComplex A ℤ) : HasProduct K :=
  inferInstance

private theorem hasProduct_X {A : Type*} [Category A] [Preadditive A] [HasProductsOfShape ℕ A]
    (K : ℕ → CochainComplex A ℤ) (n : ℤ) : HasProduct fun t ↦ (K t).X n :=
  inferInstance

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]

/-- **Iterated mapping cones of multiplication by scalars on a K-flat complex are K-flat.** -/
theorem kFlat_koszulTensor {K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (hK : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) K) :
    ∀ (r : ℕ) (x : Fin r → Λ),
      KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) (Stacks.KoszulCone.koszulTensor r x K)
  | 0, _ => hK
  | r + 1, x => by
    have h := kFlat_koszulTensor hK r (Fin.init x)
    exact kFlat_obj₃_of_distTriang _ _ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished
        (x (Fin.last r) • 𝟙 (Stacks.KoszulCone.koszulTensor r (Fin.init x) K))) h h

variable (J Λ) in
/-- **The Koszul complex of sheaves of `Λ`-modules is K-flat.** -/
theorem kFlat_koszulComplex {r : ℕ} (f : Fin r → Λ) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) (koszulComplex J Λ f) :=
  kFlat_koszulTensor (CochainComplex.KFlatMonoidal.kFlat_tensorUnit _) r f

omit [UnivLE.{max u v, w}] in
variable (J Λ) in
private theorem hasProductsOfShape_nat_sheaf :
    HasProductsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ)) := by
  have : HasLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ ModuleCat.{w} Λ) :=
    functorCategoryHasLimitsOfShape
  exact hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J _)

variable [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- **Tensoring with iterated cones of multiplication by scalars keeps product comparisons
invertible**: if the maps `Q(P ⊗ K) ⟶ Q(xⱼ ⊗ K)` exhibit a product in `D(C, Λ)`, so do the maps
`Q(P ⊗ (K ⊗ Kos(x))) ⟶ Q(xⱼ ⊗ (K ⊗ Kos(x)))`. -/
theorem isIso_lift_Q_map_map₂CochainComplex_koszulTensor {ι : Type}
    [HasProductsOfShape ι (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
    {x : ι → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (π : ∀ j, P ⟶ x j)
    {K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    (h : IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map
      (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map (π j)).app K))) :
    ∀ (r : ℕ) (y : Fin r → Λ), IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map
      (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map (π j)).app
        (Stacks.KoszulCone.koszulTensor r y K)))
  | 0, _ => h
  | r + 1, y => isIso_lift_Q_map_map₂CochainComplex_mappingCone π _
      (isIso_lift_Q_map_map₂CochainComplex_koszulTensor π h r (Fin.init y))

/-- The product comparison for the unit complex: if the maps `Q P ⟶ Q xⱼ` exhibit a product in
`D(C, Λ)`, so do the maps `Q(P ⊗ 𝟙) ⟶ Q(xⱼ ⊗ 𝟙)`. -/
theorem isIso_lift_Q_map_map₂CochainComplex_tensorUnit {ι : Type}
    [HasProductsOfShape ι (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
    {x : ι → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ}
    {P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (π : ∀ j, P ⟶ x j)
    (h : IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map (π j))) :
    IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map
      (((curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex.map (π j)).app
        (𝟙_ (CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)))) := by
  let B := (curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex
  let U := 𝟙_ (CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ)
  let e : ∀ X : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ, (B.obj X).obj U ≅ X :=
    fun X ↦ ρ_ X
  have h₁ : ∀ j, (B.map (π j)).app U = (e P).hom ≫ π j ≫ (e (x j)).inv := fun j ↦
    whiskerRight_id (π j)
  have h₂ : (Pi.lift fun j ↦ DerivedCategory.Q.map ((B.map (π j)).app U)) =
      DerivedCategory.Q.map (e P).hom ≫ (Pi.lift fun j ↦ DerivedCategory.Q.map (π j)) ≫
        Limits.Pi.map fun j ↦ DerivedCategory.Q.map (e (x j)).inv := by
    ext j
    simp only [h₁, Functor.map_comp, Pi.lift_comp_π, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc]
  change IsIso (Pi.lift fun j ↦ DerivedCategory.Q.map ((B.map (π j)).app U))
  rw [h₂]
  infer_instance

/-- Tensoring with the Koszul complex in `D(C, Λ)` preserves the product of a countable family
of K-injective complexes. -/
theorem preservesLimit_tensorRight_koszulComplex_of_isKInjective {r : ℕ} (f : Fin r → Λ)
    (I : ℕ → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (hI : ∀ n, (I n).IsKInjective) :
    PreservesLimit (Discrete.functor fun n ↦ DerivedCategory.Q.obj (I n))
      (tensorRight (DerivedCategory.Q.obj (koszulComplex J Λ f))) := by
  have := isGrothendieckAbelian J Λ
  have := hasProductsOfShape_nat_sheaf J Λ
  let B := (curriedTensor (Sheaf J (ModuleCat.{w} Λ))).map₂CochainComplex
  let kos := koszulComplex J Λ f
  let Y := DerivedCategory.Q.obj kos
  have hkos := kFlat_koszulComplex J Λ f
  let E : ∀ N : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ,
      DerivedCategory.Q.obj N ⊗ Y ≅ DerivedCategory.Q.obj ((B.obj N).obj kos) :=
    fun N ↦ ((curriedTensorIsoDerivedBifunctor J Λ).app _).app _ ≪≫
      comparisonRight _ N kos hkos
  have hE : ∀ {N N' : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ} (g : N ⟶ N'),
      DerivedCategory.Q.map g ▷ Y ≫ (E N').hom =
        (E N).hom ≫ DerivedCategory.Q.map ((B.map g).app kos) := fun {N N'} g ↦ by
    have h₁ := NatTrans.congr_app
      ((curriedTensorIsoDerivedBifunctor J Λ).hom.naturality (DerivedCategory.Q.map g)) Y
    have h₂ := comparisonRight_naturality_left (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) g
      kos hkos
    simp only [NatTrans.comp_app] at h₁
    simp only [E, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc]
    change (((curriedTensor _).map (DerivedCategory.Q.map g)).app Y ≫ _) ≫ _ = _
    rw [h₁, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) h₂
  have hX : ∀ n : ℤ, HasProduct fun t ↦ (I t).X n := @hasProduct_X _ _ _ this I
  have hP : HasProduct I := @hasProduct_cochainComplex _ _ _ this I
  let hlim := AlgebraicGeometry.RingedSite.isLimit_fan_Q_pi I hI
  refine preservesLimit_of_preserves_limit_cone hlim ?_
  refine (Fan.isLimitMapConeEquiv _ _ _).symm ?_
  have hQ : IsIso (Pi.lift fun n ↦ DerivedCategory.Q.map (Pi.π I n)) := by
    have : Pi.lift (fun n ↦ DerivedCategory.Q.map (Pi.π I n)) =
        (hlim.conePointUniqueUpToIso (limit.isLimit _)).hom := by
      ext n
      simp
    rw [this]
    infer_instance
  have hK := isIso_lift_Q_map_map₂CochainComplex_koszulTensor (Pi.π I)
    (isIso_lift_Q_map_map₂CochainComplex_tensorUnit (Pi.π I) hQ) r f
  let t : Fan fun n ↦ DerivedCategory.Q.obj ((B.obj (I n)).obj kos) :=
    Fan.mk (DerivedCategory.Q.obj ((B.obj (∏ᶜ I)).obj kos))
      fun n ↦ DerivedCategory.Q.map ((B.map (Pi.π I n)).app kos)
  have : IsIso (Pi.lift t.proj) := hK
  refine AlgebraicGeometry.RingedSite.isLimit_fan_of_iso (Fan.isLimitOfIsIsoPiLift t) _
    (E (∏ᶜ I)) (fun n ↦ (E (I n)).symm) _ (fun n ↦ ?_)
  change DerivedCategory.Q.map (Pi.π I n) ▷ Y = _
  rw [← Category.comp_id (DerivedCategory.Q.map (Pi.π I n) ▷ Y), ← (E (I n)).hom_inv_id,
    reassoc_of% (hE (Pi.π I n))]
  rfl

/-- **Tensoring with the Koszul complex in `D(C, Λ)` preserves countable products.** -/
theorem preservesLimitsOfShape_tensorRight_koszulComplex {r : ℕ} (f : Fin r → Λ) :
    PreservesLimitsOfShape (Discrete ℕ)
      (tensorRight (DerivedCategory.Q.obj (koszulComplex J Λ f))) := by
  have := isGrothendieckAbelian J Λ
  constructor
  intro F
  let I : ℕ → CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ := fun n ↦
    (Stacks.Injectives.kInjectiveResolutionFunctor.{w} (Sheaf J (ModuleCat.{w} Λ))).obj
      (DerivedCategory.Q.objPreimage (F.obj ⟨n⟩))
  let eI : ∀ n, DerivedCategory.Q.obj (I n) ≅ F.obj ⟨n⟩ := fun n ↦
    (asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion.{w} (Sheaf J (ModuleCat.{w} Λ))).app
        (DerivedCategory.Q.objPreimage (F.obj ⟨n⟩))))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso (F.obj ⟨n⟩)
  let eF : Discrete.functor (fun n ↦ DerivedCategory.Q.obj (I n)) ≅ F :=
    Discrete.natIso fun n ↦ eI n.as
  have := preservesLimit_tensorRight_koszulComplex_of_isKInjective f I fun _ ↦ inferInstance
  exact preservesLimit_of_iso_diagram _ eF

end Stacks.ModuleSheaf
