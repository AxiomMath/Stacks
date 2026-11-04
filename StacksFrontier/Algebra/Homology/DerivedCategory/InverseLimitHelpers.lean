module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# Countable products of complexes, inverse limits and right derived functors

Cancellation of an isomorphism against its inverse in composites of abstract morphisms; countable
products of complexes computed degreewise by the short-complex and homology functors; the product
of injective resolutions of a countable family; preservation of countable products by the
extension of complexes from `ℕ` to `ℤ` and by the localization functor on K-injective complexes;
the short complex `lim F ⟶ ∏ F n ⟶ ∏ F n` of a tower `F`; and the comparison of the right derived
functors `F.rightDerivedPlus p` and `F.rightDerived p`.

## Main definitions

* `CategoryTheory.productResolutionMap`: the map from the product of a countable family, in degree
  zero, to the product of injective resolutions of its terms.
* `CategoryTheory.productInjectiveResolution`: the product of injective resolutions of a countable
  family, as an injective resolution of its product, when the product complex is exact in positive
  degrees.
* `CategoryTheory.inverseLimitSequence`: the short complex `lim F ⟶ ∏ F n ⟶ ∏ F n` of a tower.
* `CategoryTheory.rightDerivedPlusObjIso`: the isomorphism
  `(F.rightDerivedPlus p).obj M ≅ (F.rightDerived p).obj M`.

## Main results

* `CategoryTheory.invHomCancel₁`, `invHomCancel₂`, `invHomCancel₃`, `homInvCancelId`,
  `comp_map_id`: cancellations in composites.
* `CategoryTheory.preservesLimits_shortComplexFunctor`,
  `CategoryTheory.preservesProducts_homologyFunctor`: countable products are computed degreewise
  by the short-complex and homology functors.
* `CategoryTheory.isZero_homology_mapHomologicalComplex_productResolution`: the image of a product
  of injective resolutions under an additive functor preserving countable products has zero
  homology in every degree in which all terms of the family are acyclic.
* `CategoryTheory.preservesProducts_extend`, `CategoryTheory.preservesProduct_Q_of_isKInjective`:
  countable products are preserved by extension from `ℕ` to `ℤ`, and by the localization functor
  on K-injective complexes.
* `CategoryTheory.inverseLimitSequence_exact_and_mono`: the short complex of a tower is exact with
  monic first map.
* `CategoryTheory.rightAcyclic_iff_isZero_rightDerived`,
  `CategoryTheory.isZero_rightDerived_kernel`: acyclicity in terms of the vanishing of
  `F.rightDerived p` for `0 < p`, and the passage of this vanishing to the kernel of a short exact
  sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Cancellation of `r.inv ≫ r.hom` in `(a ≫ f ≫ r.inv) ≫ r.hom ≫ g`. -/
lemma invHomCancel₁ {C : Type*} [Category C] {W X Y Z V : C}
    (a : W ⟶ X) (f : X ⟶ Y) (r : Z ≅ Y) (g : Y ⟶ V) :
    (a ≫ f ≫ r.inv) ≫ r.hom ≫ g = a ≫ f ≫ g := by simp

/-- Cancellation of `t.inv ≫ t.hom` in `(a ≫ t.inv) ≫ t.hom ≫ g`. -/
lemma invHomCancel₂ {C : Type*} [Category C] {W X Y V : C}
    (a : W ⟶ X) (t : Y ≅ X) (g : X ⟶ V) :
    (a ≫ t.inv) ≫ t.hom ≫ g = a ≫ g := by simp

/-- Cancellation of `r.inv ≫ r.hom` in `(a ≫ r.inv) ≫ r.hom`. -/
lemma invHomCancel₃ {C : Type*} [Category C] {W X Z : C} (a : W ⟶ X) (r : Z ≅ X) :
    (a ≫ r.inv) ≫ r.hom = a := by simp

/-- Cancellation of `r.hom ≫ r.inv` in `(a ≫ r.hom) ≫ r.inv`, with result `𝟙 W ≫ a`. -/
lemma homInvCancelId {C : Type*} [Category C] {W X Y : C} (a : W ⟶ X) (r : X ≅ Y) :
    (a ≫ r.hom) ≫ r.inv = 𝟙 W ≫ a := by simp

/-- Composing with the image of an identity morphism under a functor is the identity. -/
lemma comp_map_id {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D) {X : C} {W : D}
    (a : W ⟶ Φ.obj X) : a ≫ Φ.map (𝟙 X) = a := by simp

/-- The short-complex functor at `n` of complexes of shape `c` preserves countable products. -/
lemma preservesLimits_shortComplexFunctor
    {A : Type*} [Category A] [HasZeroMorphisms A] [HasProductsOfShape ℕ A]
    {ι : Type*} (c : ComplexShape ι) (n : ι) :
    PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.shortComplexFunctor A c n) := by
  constructor; intro D; constructor; intro E hE
  exact ⟨ShortComplex.isLimitOfIsLimitπ _
    (isLimitOfPreserves (HomologicalComplex.eval A c (c.prev n)) hE)
    (isLimitOfPreserves (HomologicalComplex.eval A c n) hE)
    (isLimitOfPreserves (HomologicalComplex.eval A c (c.next n)) hE)⟩

/-- When countable products are exact, the homology functor at `n` of complexes of shape `c`
preserves countable products. -/
lemma preservesProducts_homologyFunctor
    {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {ι : Type*} (c : ComplexShape ι) (n : ι) :
    PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.homologyFunctor A c n) := by
  have := preservesLimits_shortComplexFunctor (A := A) c n
  have := Stacks.DerivedProducts.preservesLimitsOfShape_shortComplexHomologyFunctor
    (A := A) (I := ℕ)
  show PreservesLimitsOfShape (Discrete ℕ)
    (HomologicalComplex.shortComplexFunctor A c n ⋙ ShortComplex.homologyFunctor A)
  infer_instance

/-! ### The product of injective resolutions

For a countable family `M : ℕ → A` with injective resolutions `I n`, the product of the
resolutions resolves the product, provided the product complex is exact in positive degrees. -/

/-- The map from `∏ᶜ M`, placed in degree zero, to the product of the injective resolutions
`I n`, whose `n`-th component is the projection to `M n` followed by the augmentation of
`I n`. -/
public noncomputable def productResolutionMap {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] (M : ℕ → A) (I : ∀ n, InjectiveResolution (M n)) :
    (CochainComplex.single₀ A).obj (∏ᶜ M) ⟶ ∏ᶜ (fun n => (I n).cocomplex) :=
  Pi.lift fun n => (CochainComplex.single₀ A).map (Pi.π M n) ≫ (I n).ι

section SingleDegreeZero

attribute [local implicit_reducible] HomologicalComplex.single

/-- The degree-zero component of `productResolutionMap M I` followed by the `n`-th projection is
the projection to `M n` followed by the augmentation of `I n`. -/
public lemma productResolutionMap_f_zero_π {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] (M : ℕ → A) (I : ∀ n, InjectiveResolution (M n)) (n : ℕ) :
    (productResolutionMap M I).f 0 ≫ (Pi.π (fun n => (I n).cocomplex) n).f 0 =
      Pi.π M n ≫ (I n).ι.f 0 := by
  simpa only [productResolutionMap, HomologicalComplex.comp_f,
    CochainComplex.single₀_map_f_zero] using
    HomologicalComplex.congr_hom (Pi.lift_π
      (fun n => (CochainComplex.single₀ A).map (Pi.π M n) ≫ (I n).ι) n) 0

/-- `productResolutionMap M I` is a quasi-isomorphism in degree zero. -/
public lemma productResolutionMap_quasiIsoAt_zero {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] (M : ℕ → A) (I : ∀ n, InjectiveResolution (M n)) :
    QuasiIsoAt (productResolutionMap M I) 0 := by
  let P := ∏ᶜ (fun n => (I n).cocomplex)
  let η := productResolutionMap M I
  have hz : η.f 0 ≫ P.d 0 1 = 0 := by
    rw [η.comm]; simp
  have hker : IsLimit (KernelFork.ofι (η.f 0) hz) := by
    let l {W : A} (a : W ⟶ P.X 0) (ha : a ≫ P.d 0 1 = 0) (n : ℕ) : W ⟶ M n :=
      (KernelFork.IsLimit.lift' (I n).isLimitKernelFork
        (a ≫ (Pi.π (fun n => (I n).cocomplex) n).f 0) (by
          rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, ha, zero_comp])).1
    have hl {W : A} (a : W ⟶ P.X 0) (ha : a ≫ P.d 0 1 = 0) (n : ℕ) :
        l a ha n ≫ (I n).ι.f 0 = a ≫ (Pi.π (fun n => (I n).cocomplex) n).f 0 :=
      (KernelFork.IsLimit.lift' (I n).isLimitKernelFork _ _).2
    refine KernelFork.IsLimit.ofι _ hz (fun a ha => Pi.lift (l a ha)) ?_ ?_
    · intro W a ha
      apply (isLimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℕ) 0)
        (productIsProduct (fun n => (I n).cocomplex))).hom_ext
      rintro ⟨n⟩
      show (Pi.lift (l a ha) ≫ η.f 0) ≫
        (Pi.π (fun n => (I n).cocomplex) n).f 0 =
          a ≫ (Pi.π (fun n => (I n).cocomplex) n).f 0
      rw [Category.assoc, productResolutionMap_f_zero_π, ← Category.assoc,
        Pi.lift_π, hl a ha n]
    · intro W a ha m hm
      refine Pi.hom_ext _ _ fun n => ?_
      rw [Pi.lift_π]
      apply (cancel_mono ((I n).ι.f 0)).mp
      rw [hl a ha n, Category.assoc, ← productResolutionMap_f_zero_π,
        ← Category.assoc, hm]
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · exact (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).mpr ⟨hker⟩
  · rfl
  · rfl
  · exact HomologicalComplex.shape _ _ _ (by simp)

end SingleDegreeZero

/-- If `G` is an additive functor preserving countable products and `(G.rightDerived p).obj (M n)`
is zero for every `n`, then the image under `G` of the product of injective resolutions `I n` of
the `M n` has zero homology in degree `p`. -/
public lemma isZero_homology_mapHomologicalComplex_productResolution {A B : Type*}
    [Category A] [Abelian A] [HasInjectiveResolutions A] [HasProductsOfShape ℕ A]
    [Category B] [Abelian B] [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    (G : A ⥤ B) [G.Additive] [PreservesLimitsOfShape (Discrete ℕ) G]
    (M : ℕ → A) (I : ∀ n, InjectiveResolution (M n)) (p : ℕ)
    (h : ∀ n, IsZero ((G.rightDerived p).obj (M n))) :
    IsZero (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (∏ᶜ fun n => (I n).cocomplex)).homology p) := by
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) p
  have : PreservesLimitsOfShape (Discrete ℕ) H :=
    preservesProducts_homologyFunctor (A := B) (ComplexShape.up ℕ) p
  have hprod : IsZero (Discrete.functor (fun n : ℕ => (I n).cocomplex) ⋙ Gc ⋙ H) := by
    rw [Functor.isZero_iff]
    rintro ⟨n⟩
    exact (h n).of_iso ((I n).isoRightDerivedObj G p).symm
  exact (isLimitOfPreserves H
    (isLimitOfPreserves Gc (productIsProduct (fun n => (I n).cocomplex)))).isZero_pt hprod

/-- The product of injective resolutions of a countable family, as an injective resolution of the
product of the family, when the product complex is exact in positive degrees. -/
public noncomputable def productInjectiveResolution {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] (M : ℕ → A) (I : ∀ n, InjectiveResolution (M n))
    (hexact : ∀ q : ℕ, 0 < q → (∏ᶜ fun n => (I n).cocomplex).ExactAt q) :
    InjectiveResolution (∏ᶜ M) where
  cocomplex := ∏ᶜ fun n => (I n).cocomplex
  injective p := by
    have : ∀ n, Injective ((I n).cocomplex.X p) := fun n => inferInstance
    exact Injective.of_iso
      (PreservesProduct.iso (HomologicalComplex.eval _ _ p) (fun n => (I n).cocomplex)).symm
      (inferInstanceAs (Injective (∏ᶜ fun n => (I n).cocomplex.X p)))
  ι := productResolutionMap M I
  quasiIso := ⟨fun p => by
    cases p with
    | zero => exact productResolutionMap_quasiIsoAt_zero M I
    | succ p =>
      rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
      exact hexact (p + 1) (Nat.succ_pos p)⟩

/-- Extension of cochain complexes along `ℕ ↪ ℤ` preserves countable products. -/
public lemma preservesProducts_extend {A : Type*} [Category A] [Abelian A]
    [HasProductsOfShape ℕ A] :
    PreservesLimitsOfShape (Discrete ℕ) (ComplexShape.embeddingUpNat.extendFunctor A) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro i
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact preservesLimitsOfShape_of_natIso
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso A (i := n) rfl).symm
  · apply Functor.preservesLimitsOfShape_of_isZero
    rw [Functor.isZero_iff]
    intro K
    exact K.isZero_extend_X _ i (fun n hn => hi (hn ▸ Int.natCast_nonneg n))

/-- The localization functor to the derived category preserves the product of a countable family
of K-injective complexes. -/
public lemma preservesProduct_Q_of_isKInjective {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] [HasProductsOfShape ℕ A]
    (K : ℕ → CochainComplex A ℤ) [∀ n, (K n).IsKInjective] :
    PreservesLimit (Discrete.functor K) DerivedCategory.Q := by
  classical
  have hK (n : ℕ) : (K n).IsKInjective := inferInstance
  let c : Fan (fun n => DerivedCategory.Q.obj (K n)) :=
    Fan.mk (DerivedCategory.Q.obj (∏ᶜ K)) (fun n => DerivedCategory.Q.map (Pi.π K n))
  have hc : IsLimit c := by
    let e (s : Fan (fun n => DerivedCategory.Q.obj (K n))) :=
      DerivedCategory.Q.objObjPreimageIso s.pt
    have key (s : Fan (fun n => DerivedCategory.Q.obj (K n))) :
        ∃! l, ∀ n, l ≫ DerivedCategory.Q.map (Pi.π K n) = (e s).hom ≫ s.proj n := by
      have hb := Stacks.Injectives.KInjectiveProduct.product_repr_derived K hK
        (DerivedCategory.Q.objPreimage s.pt)
      obtain ⟨l, hl, hu⟩ := hb.existsUnique (fun n => (e s).hom ≫ s.proj n)
      exact ⟨l, congrFun hl, fun l' h => hu l' (funext h)⟩
    refine Fan.IsLimit.mk c (fun s => (e s).inv ≫ (key s).choose) (fun s n => ?_)
      (fun s m hm => (Iso.eq_inv_comp _).2 ((key s).unique (fun n => ?_) (key s).choose_spec.1))
    · change ((e s).inv ≫ _) ≫ DerivedCategory.Q.map (Pi.π K n) = s.proj n
      rw [Category.assoc, (key s).choose_spec.1, Iso.inv_hom_id_assoc]
    · exact (Category.assoc _ _ _).trans (congrArg _ (hm n))
  exact preservesLimit_of_preserves_limit_cone (productIsProduct K)
    ((Fan.isLimitMapConeEquiv DerivedCategory.Q K (Fan.mk (∏ᶜ K) (Pi.π K))).symm hc)

/-- The short complex `lim F ⟶ ∏ F n ⟶ ∏ F n` of a tower `F`, whose first map has components the
limit projections and whose second map is `1 - shift`. -/
public noncomputable def inverseLimitSequence {A : Type*} [Category A] [Preadditive A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F] : ShortComplex A :=
  ShortComplex.mk (inverseSystemLimitKernelFork F).ι _
    (inverseSystemLimitKernelFork F).condition

/-- In an abelian category the short complex of a tower is exact and its first map is a
monomorphism. -/
public lemma inverseLimitSequence_exact_and_mono {A : Type*} [Category A] [Abelian A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F] :
    (inverseLimitSequence F).Exact ∧ Mono (inverseLimitSequence F).f :=
  (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).mpr
    ⟨inverseSystemLimitKernelForkIsLimit F⟩

/-- The image under an additive functor `G` of the second map of the short complex of a tower `F`,
followed by the product comparison of `G`, is the product comparison followed by `1 - shift` of
the tower `G ∘ F`. -/
public lemma map_inverseLimitSequence_g {A D : Type*} [Category A] [Category D]
    [Preadditive A] [Preadditive D] (F : ℕᵒᵖ ⥤ A) (G : A ⥤ D) [G.Additive]
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F]
    [HasProduct fun n : ℕ => G.obj (F.obj ⟨n⟩)] :
    G.map (inverseLimitSequence F).g ≫ piComparison G (fun n : ℕ => F.obj ⟨n⟩) =
      piComparison G (fun n : ℕ => F.obj ⟨n⟩) ≫
        Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) n -
          Pi.π (fun n : ℕ => G.obj (F.obj ⟨n⟩)) (n + 1) ≫
            G.map (F.map (homOfLE (Nat.le_succ n)).op)) := by
  refine Pi.hom_ext _ _ fun n => ?_
  dsimp only [inverseLimitSequence]
  rw [Category.assoc, piComparison_comp_π, ← G.map_comp, Pi.lift_π,
    G.map_sub, G.map_comp, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    piComparison_comp_π, ← Category.assoc, piComparison_comp_π]

/-! ### The two indexings of the right derived functors -/

section RightDerived

-- Prefer the direct existence theorem to searching for an injective replacement.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The value at `M` of the right derived functor `F.rightDerivedPlus p` on the bounded below
derived category is isomorphic to that of the classical right derived functor
`F.rightDerived p`. -/
noncomputable def rightDerivedPlusObjIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (M : A) (p : ℕ) :
    (F.rightDerivedPlus (p : ℤ)).obj M ≅ (F.rightDerived p).obj M := by
  let I := InjectiveResolution.of M
  let L : HomotopyCategory.Plus A := (HomotopyCategory.Plus.quotient A).obj
    ⟨I.cochainComplex, ⟨0, inferInstance⟩⟩
  have : ∀ n : ℤ, Injective (L.obj.as.X n) := fun n =>
    inferInstanceAs (Injective (I.cochainComplex.X n))
  have : IsIso (F.rightDerivedFunctorPlusUnit.app L) := inferInstance
  let e : (DerivedCategory.Plus.singleFunctor A 0).obj M ≅ DerivedCategory.Plus.Qh.obj L :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app M ≪≫
        asIso (DerivedCategory.Q.map I.ι') ≪≫
          ((DerivedCategory.quotientCompQhIso A).app I.cochainComplex).symm)
  let e' := F.rightDerivedFunctorPlus.mapIso e ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app L)).symm
  refine (DerivedCategory.Plus.homologyFunctor B (p : ℤ)).mapIso e' ≪≫ ?_
  change (DerivedCategory.homologyFunctor B (p : ℤ)).obj
    (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I.cochainComplex))) ≅ _
  exact (DerivedCategory.homologyFunctor B (p : ℤ)).mapIso
    (DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      I.cochainComplex) ≪≫ (DerivedCategory.quotientCompQhIso B).app _) ≪≫
    (DerivedCategory.homologyFunctorFactors B (p : ℤ)).app _ ≪≫
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (p : ℤ)).mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso F I.cocomplex
        ComplexShape.embeddingUpNat).symm ≪≫
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := p) rfl) ≪≫
    (I.isoRightDerivedObj F p).symm

/-- An object is right acyclic for a left exact additive functor `F` if and only if
`(F.rightDerived p).obj M` is zero for every `p > 0`. -/
lemma rightAcyclic_iff_isZero_rightDerived {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (M : A) :
    F.rightAcyclic M ↔ ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj M) := by
  rw [(F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 inferInstance]
  refine ⟨fun h p hp => (h (p : ℤ) (by exact_mod_cast hp)).of_iso
    (rightDerivedPlusObjIso F M p).symm, fun h i hi => ?_⟩
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact (h p (by exact_mod_cast hi)).of_iso (rightDerivedPlusObjIso F M p)

/-- For a short exact sequence `S` whose image under a left exact additive functor `F` has
epimorphic second map, if `F.rightDerived p` vanishes on `S.X₂` and `S.X₃` for every `p > 0`, then
it vanishes on `S.X₁` for every `p > 0`. -/
lemma isZero_rightDerived_kernel {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (S : ShortComplex A) (hS : S.ShortExact) (hg : Epi (F.map S.g))
    (h₂ : ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj S.X₂))
    (h₃ : ∀ p : ℕ, 0 < p → IsZero ((F.rightDerived p).obj S.X₃))
    (p : ℕ) (hp : 0 < p) : IsZero ((F.rightDerived p).obj S.X₁) := by
  have h := (F.rightAcyclic_and_shortExact_map_of_shortExact S hS).2.2
    ((rightAcyclic_iff_isZero_rightDerived F S.X₂).2 h₂)
    ((rightAcyclic_iff_isZero_rightDerived F S.X₃).2 h₃) hg
  exact (rightAcyclic_iff_isZero_rightDerived F S.X₁).1 h.1 p hp

end RightDerived

end CategoryTheory

end
