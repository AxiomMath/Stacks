module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantCohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# K-injective representatives of a tower and the mapping cocone of its Milnor difference

Let `A` be an abelian category and `K : ℕᵒᵖ ⥤ D(A)` an inverse system. A derived limit of `K`
is an object `L` sitting in a distinguished triangle whose second map is the Milnor difference
`(xₙ) ↦ (xₙ - fₙ(xₙ₊₁))` of the product. This file makes that object concrete when the tower is
represented by a tower of K-injective complexes: the derived limit is then the mapping cocone,
*in the category of complexes*, of the Milnor difference of the representing tower.

The point of the concrete model is that an additive functor can be applied to it termwise.
That is what the convergence argument of Stacks 0D6T needs: the cohomology of the derived limit
has to be compared, over each object of a site, with the cohomology computed after evaluating,
and evaluation is applied to complexes, not to objects of the derived category.

## Main results

* `Stacks.InverseSystem.exists_injective_tower_representative`: a countable tower in `D⁺(A)`
  over a category with enough injectives is represented by a tower of bounded-below complexes
  of injectives.
* `Stacks.InverseSystem.isIso_piComparison_Q_of_isKInjective`: a countable product of
  K-injective complexes computes the product in `D(A)`.
* `Stacks.InverseSystem.exists_mappingCocone_iso_of_isKInjective_tower`: the mapping cocone of
  the Milnor difference of a K-injective representing tower is the derived limit, compatibly
  with the projections.
* `Stacks.InverseSystem.isIso_homologyMap_mappingCocone_proj`: for an eventually constant
  tower, the projection of that mapping cocone onto a stabilising stage is an isomorphism on
  cohomology.
* `Stacks.InverseSystem.isIso_homologyMap_of_isIso_rightDerivedFunctorPlus_map`: on complexes
  of injectives the right derived functor of an additive functor is computed termwise.

## Implementation notes

The product of the representing complexes is the *termwise* product; it computes the product in
`D(A)` because the factors are K-injective, and not because products are exact in `A` — in the
intended application, sheaves of modules on a site, they are not.

A derived limit is supplied by a distinguished triangle rather than by a `HasDerivedLimit`
predicate, so that the structural map, and hence the projections, are the ones the caller
already holds.

## References

* [Stacks Project, Tag 0D6T](https://stacks.math.columbia.edu/tag/0D6T)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.InverseSystem

/-- **A derived morphism into a K-injective bounded-below complex is represented by a chain
map.** The bounded-below form of
`StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective`.

Used to lift the transition maps of the tower of Stacks 0D6T. -/
lemma plus_Q_map_surjective_of_isKInjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X Y : CochainComplex.Plus C) [Y.obj.IsKInjective] :
    Function.Surjective (DerivedCategory.Plus.Q.map : (X ⟶ Y) → _) := by
  intro f
  obtain ⟨g, hg⟩ := StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective
    X.obj Y.obj (DerivedCategory.Plus.ι.map f)
  exact ⟨⟨g⟩, DerivedCategory.Plus.ι.map_injective hg⟩

/-- **A countable tower in `D⁺(C)` is represented by a tower of K-injective complexes.** Given
`K : ℕᵒᵖ ⥤ D⁺(C)` over an abelian category with enough injectives, there is a tower
`I : ℕᵒᵖ ⥤ C⁺(C)` of bounded-below complexes of injectives, hence K-injective, together with an
isomorphism `I ⋙ Q ≅ K`. In particular the transition maps of `K` are represented by honest
chain maps, compatibly.

Each object is resolved separately; the transition maps lift because a derived morphism into a
K-injective complex is represented by a chain map, and the lifts are assembled into a functor
out of `ℕᵒᵖ` by `CategoryTheory.Functor.ofOpSequence`.

This is the concrete model of the tower of Stacks 0D6T. -/
theorem exists_injective_tower_representative
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
    (K : ℕᵒᵖ ⥤ DerivedCategory.Plus C) :
    ∃ I : ℕᵒᵖ ⥤ CochainComplex.Plus C,
      (∀ (n : ℕ) (q : ℤ), Injective ((I.obj (.op n)).obj.X q)) ∧
      (∀ n : ℕ, (I.obj (.op n)).obj.IsKInjective) ∧
      Nonempty (I ⋙ DerivedCategory.Plus.Q ≅ K) := by
  have hrep (n : ℕ) : ∃ I : CochainComplex.Plus C,
      (∀ q : ℤ, Injective (I.obj.X q)) ∧ I.obj.IsKInjective ∧
      Nonempty (DerivedCategory.Plus.Q.obj I ≅ K.obj (.op n)) := by
    obtain ⟨a, ha⟩ := (K.obj (.op n)).property
    have : (K.obj (.op n)).IsGE a :=
      (DerivedCategory.Plus.isGE_ι_obj_iff _ a).1 ha
    obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso
      (K.obj (.op n)) a
    let J := (InjectiveObject.ι C).mapCochainComplexPlus.obj I
    have hJ : J.obj.IsStrictlyGE a := by
      show CochainComplex.IsStrictlyGE
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj) a
      infer_instance
    have hinj (q : ℤ) : Injective (J.obj.X q) := inferInstanceAs (Injective (I.obj.X q).obj)
    exact ⟨J, hinj, CochainComplex.isKInjective_of_injective J.obj a, ⟨e⟩⟩
  choose I hI hKI e using hrep
  let e' (n : ℕ) := (e n).some
  have hmap (n : ℕ) : ∃ g : I (n + 1) ⟶ I n,
      DerivedCategory.Plus.Q.map g =
        (e' (n + 1)).hom ≫ K.map (homOfLE (Nat.le_add_right n 1)).op ≫ (e' n).inv := by
    have := hKI n
    exact plus_Q_map_surjective_of_isKInjective _ _ _
  choose f hf using hmap
  let T := Functor.ofOpSequence f
  let α : T ⋙ DerivedCategory.Plus.Q ⟶ K := NatTrans.ofOpSequence
    (fun n => (e' n).hom) (by
      intro n
      have key : DerivedCategory.Plus.Q.map (f n) ≫ (e' n).hom =
          (e' (n + 1)).hom ≫ K.map (homOfLE (Nat.le_add_right n 1)).op := by
        rw [hf n]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact (congrArg (fun g : I (n + 1) ⟶ I n =>
        DerivedCategory.Plus.Q.map g ≫ (e' n).hom)
        (Functor.ofOpSequence_map_homOfLE_succ f n)).trans key)
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).2 fun n =>
    inferInstanceAs (IsIso (e' n.unop).hom)
  exact ⟨T, hI, hKI, ⟨asIso α⟩⟩

/-- **A countable product of K-injective complexes computes the product in `D(C)`.** The
canonical comparison `Q(∏ Xₙ) ⟶ ∏ Q(Xₙ)` is an isomorphism as soon as every `Xₙ` is
K-injective — no exactness of products in `C` is needed.

This is Stacks 0BK6 in the form Stacks 0D6T uses it. -/
theorem isIso_piComparison_Q_of_isKInjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : ℕ → CochainComplex C ℤ) [HasProduct X]
    [∀ q : ℤ, HasProduct (fun n => (X n).X q)]
    [HasProduct (fun n => DerivedCategory.Q.obj (X n))]
    (hX : ∀ n, (X n).IsKInjective) : IsIso (piComparison DerivedCategory.Q X) := by
  refine isIso_of_yoneda_map_bijective _ fun Z => ?_
  let Q := DerivedCategory.Q (C := C)
  let K := Q.objPreimage Z
  let e := Q.objObjPreimageIso Z
  have hb := Stacks.Injectives.KInjectiveProduct.product_repr_derived X hX K
  refine ⟨fun f g hfg => ?_, fun f => ?_⟩
  · apply (cancel_epi e.hom).1
    apply hb.injective
    funext n
    show (e.hom ≫ f) ≫ Q.map (Pi.π X n) = (e.hom ≫ g) ≫ Q.map (Pi.π X n)
    simpa only [Q, Category.assoc, piComparison_comp_π] using
      congrArg (fun h => e.hom ≫ h ≫ Pi.π (fun n => Q.obj (X n)) n) hfg
  · obtain ⟨g, hg⟩ := hb.surjective (fun n => e.hom ≫ f ≫
      Pi.π (fun n => Q.obj (X n)) n)
    refine ⟨e.inv ≫ g, ?_⟩
    refine Pi.hom_ext _ _ fun n => ?_
    have hn := congrFun hg n
    change g ≫ Q.map (Pi.π X n) = _ at hn
    simp only [Q, Category.assoc, piComparison_comp_π, hn, Iso.inv_hom_id_assoc]

/-- **On complexes of injectives the right derived functor is computed termwise.** If
`f : X ⟶ Y` is a map of bounded-below complexes of injectives and `RE` applied to its image in
`D⁺` is an isomorphism on degree-`j` cohomology, then so is `E` applied to `f` termwise.

This is the unit of the right derived functor being invertible on complexes of injectives,
read backwards.

Used to pass between derived sections and termwise evaluation in Stacks 0D6T. -/
theorem isIso_homologyMap_of_isIso_rightDerivedFunctorPlus_map
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (E : A ⥤ B) [E.Additive] {X Y : CochainComplex.Plus A}
    (hX : ∀ q, Injective (X.obj.X q)) (hY : ∀ q, Injective (Y.obj.X q))
    (f : X ⟶ Y) (j : ℤ)
    (hf : IsIso ((DerivedCategory.Plus.homologyFunctor B j).map
      (E.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)))) :
    IsIso ((HomologicalComplex.homologyFunctor B (.up ℤ) j).map
      ((E.mapHomologicalComplex (.up ℤ)).map f.hom)) := by
  let q := HomotopyCategory.Plus.quotient A
  let H := DerivedCategory.Plus.homologyFunctor B j
  let α := Functor.whiskerRight E.rightDerivedFunctorPlusUnith H
  have hα (Z : CochainComplex.Plus A) (hZ : ∀ n, Injective (Z.obj.X n)) :
      IsIso (α.app (q.obj Z)) := by
    have : ∀ n : ℤ, Injective ((q.obj Z).obj.as.X n) := hZ
    dsimp [α]
    infer_instance
  have := hα X hX
  have := hα Y hY
  have hi : IsIso (((DerivedCategory.Plus.Qh ⋙ E.rightDerivedFunctorPlus) ⋙ H).map
      (q.map f)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (DerivedCategory.Plus.quotientCompQhIso A)
      (E.rightDerivedFunctorPlus ⋙ H)) f).2 hf
  have hi' : IsIso (((E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ H).map
      (q.map f)) := by
    have : IsIso (α.app (q.obj X) ≫
      ((DerivedCategory.Plus.Qh ⋙ E.rightDerivedFunctorPlus) ⋙ H).map (q.map f)) :=
      inferInstance
    rw [← α.naturality (q.map f)] at this
    exact IsIso.of_isIso_comp_right _ (α.app (q.obj Y))
  change IsIso ((DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor B j).map
    ((E.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient A (.up ℤ)).map f.hom))) at hi'
  rw [Functor.mapHomotopyCategory_map] at hi'
  exact (NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors B (.up ℤ) j) _).1
    ((NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh B j) _).1 hi')

/-- **An additive functor takes the mapping cocone triangle to a distinguished triangle of the
derived category.**

Used to transport the derived-limit triangle of Stacks 0D6T along evaluation. -/
theorem map_mappingCocone_triangle_distinguished
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] (E : A ⥤ B) [E.Additive]
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).mapTriangle.obj
      (CochainComplex.mappingCocone.triangle f) ∈ distTriang (DerivedCategory B) := by
  let G := E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  rw [rotate_distinguished_triangle]
  apply isomorphic_distinguished _ _ _
    (G.mapTriangleRotateIso.app _ ≪≫
      G.mapTriangle.mapIso (CochainComplex.mappingCocone.rotateTriangleIso f))
  apply isomorphic_distinguished _ _ _
    ((Functor.mapTriangleCompIso (E.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q).app
      (CochainComplex.mappingCone.triangle f))
  exact isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _)
    _ (DerivedCategory.Q.mapTriangle.mapIso
      (CochainComplex.mappingCone.mapTriangleIso f E))

/-- **Replacing the middle and last objects of a distinguished triangle by isomorphic objects
keeps it distinguished**, the second map being any `d` compatible with the isomorphisms. -/
theorem Triangle.mk_comp_hom_distinguished
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {Y Z : C} (a₂ : T.obj₂ ≅ Y) (a₃ : T.obj₃ ≅ Z)
    (d : Y ⟶ Z) (hd : T.mor₂ ≫ a₃.hom = a₂.hom ≫ d) :
    Triangle.mk (T.mor₁ ≫ a₂.hom) d (a₃.inv ≫ T.mor₃) ∈ distTriang C :=
  isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) a₂.symm a₃.symm (by simp)
    (by rw [← cancel_epi a₂.hom]; simp [← reassoc_of% hd]) (by simp))

/-- **The mapping cocone of the Milnor difference of an eventually constant tower computes its
cohomology.** Let `I : ℕᵒᵖ ⥤ C(A)` be a tower, `d` its Milnor difference and `E` an additive
functor preserving countable products into an abelian category with exact countable products.
If the tower `I ⋙ E ⋙ Hʳ` is constant past the stage `N` in the degrees `r = j - 1, j`, then
the projection of the mapping cocone of `d` onto the stage `N` is an isomorphism on degree-`j`
cohomology after applying `E`.

This is the local statement that Stacks 0D6T globalises. -/
theorem isIso_homologyMap_mappingCocone_proj
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ A]
    [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasLimitsOfShape ℕᵒᵖ B]
    (E : A ⥤ B) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]
    (I : ℕᵒᵖ ⥤ CochainComplex A ℤ) (j : ℤ) (N : ℕ)
    (hstable : ∀ (n : ℕ) (hn : N ≤ n) (r : ℤ), r = j - 1 ∨ r = j →
      IsIso (((I ⋙ E.mapHomologicalComplex (.up ℤ)) ⋙
        HomologicalComplex.homologyFunctor B (.up ℤ) r).map (homOfLE hn).op)) :
    let X := fun n : ℕ => I.obj (.op n)
    let d := Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
      I.map (homOfLE (Nat.le_succ n)).op)
    IsIso ((HomologicalComplex.homologyFunctor B (.up ℤ) j).map
      ((E.mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.mappingCocone.triangle d).mor₁ ≫ Pi.π X N))) := by
  intro X d
  let G := E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let F := I ⋙ G
  let L := G.obj (CochainComplex.mappingCocone d)
  let q : L ⟶ G.obj (∏ᶜ X) := G.map (CochainComplex.mappingCocone.triangle d).mor₁
  let δ : G.obj (∏ᶜ X) ⟶ L⟦(1 : ℤ)⟧ :=
    G.map (CochainComplex.mappingCocone.triangle d).mor₃ ≫
      (G.commShiftIso (1 : ℤ)).hom.app (CochainComplex.mappingCocone d)
  let T : Triangle (DerivedCategory B) := Triangle.mk q (G.map d) δ
  have hT : T ∈ distTriang (DerivedCategory B) := map_mappingCocone_triangle_distinguished E d
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := B) (I := ℕ)
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := B) (I := ℕ)
  have : IsIso (piComparison G X) := by
    dsimp [G]
    infer_instance
  let a := asIso (piComparison G X)
  let d' := Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => G.obj (X n)) n -
    Pi.π (fun n : ℕ => G.obj (X n)) (n + 1) ≫
      G.map (I.map (homOfLE (Nat.le_succ n)).op))
  have hT' : Triangle.mk (q ≫ a.hom) d' (a.inv ≫ δ) ∈ distTriang (DerivedCategory B) :=
    Triangle.mk_comp_hom_distinguished T hT a a d' (map_piLift_sub_comp_piComparison G X _)
  have hst (r : ℤ) (hr : r = j - 1 ∨ r = j) :
      (F ⋙ DerivedCategory.homologyFunctor B r).IsEventuallyConstantTo (.op N) :=
    fun n f => (NatIso.isIso_map_iff (Functor.isoWhiskerLeft (I ⋙ E.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.homologyFunctorFactors B r)) f).2 (hstable n.unop (leOfHom f.unop) r hr)
  have h := isIso_homologyMap_proj_of_eventuallyConstant F L
    (q ≫ a.hom) (a.inv ≫ δ) hT' j _
    ⟨N, hst _ (Or.inl rfl), Iso.refl _⟩ _
    ⟨N, hst _ (Or.inr rfl), Iso.refl _⟩
  have key : (q ≫ piComparison G X) ≫ Pi.π (fun n : ℕ => G.obj (X n)) N =
      G.map ((CochainComplex.mappingCocone.triangle d).mor₁ ≫ Pi.π X N) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun u => q ≫ u) (piComparison_comp_π G X N)).trans
        (G.map_comp _ _).symm)
  change IsIso ((DerivedCategory.homologyFunctor B j).map
    ((q ≫ piComparison G X) ≫ Pi.π (fun n : ℕ => G.obj (X n)) N) ≫ 𝟙 _) at h
  rw [Category.comp_id, key] at h
  exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors B j) _).1 h

/-- **The projections of a mapping cocone are compatible with the transition maps of the
tower.** Composing the projection to the stage `n` with a transition map `n ⟶ m` of the tower
gives the projection to the stage `m`, after applying any additive functor to the degree-`j`
cohomology of the termwise image of the cocone.

This is the statement that the projections form a cone, pushed through the functor; it holds
because the first map of a distinguished triangle composed with its second is zero.

Used in the local-to-global step of Stacks 0D6T. -/
lemma map_mappingCocone_proj_comp_map
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Preadditive D] [HasDerivedCategory B]
    [HasProductsOfShape ℕ A] (E : A ⥤ B) [E.Additive]
    (G : B ⥤ D) [G.Additive] (I : ℕᵒᵖ ⥤ CochainComplex A ℤ) (j : ℤ) :
    let X := fun n : ℕ => I.obj (.op n)
    let d := Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
      I.map (homOfLE (Nat.le_succ n)).op)
    let p := (CochainComplex.mappingCocone.triangle d).mor₁
    let H := E.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor B (.up ℤ) j ⋙ G
    ∀ m n (hmn : m ≤ n), H.map (p ≫ Pi.π X n) ≫
      H.map (I.map (homOfLE hmn).op) = H.map (p ≫ Pi.π X m) := by
  intro X d p H
  change CochainComplex.mappingCocone d ⟶ ∏ᶜ X at p
  let F := E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let Hd := DerivedCategory.homologyFunctor B j
  have hp : F.map (p ≫ d) = 0 := by
    rw [CategoryTheory.Functor.map_comp]
    exact comp_distTriang_mor_zero₁₂ _ (map_mappingCocone_triangle_distinguished E d)
  have hp' : H.map (p ≫ d) = 0 := by
    let e := DerivedCategory.homologyFunctorFactors B j
    have he : (HomologicalComplex.homologyFunctor B (.up ℤ) j).map
        ((E.mapHomologicalComplex (.up ℤ)).map (p ≫ d)) = 0 := by
      apply (cancel_epi (e.app _).hom).1
      show e.hom.app _ ≫ _ = _
      rw [← e.hom.naturality]
      show Hd.map (F.map (p ≫ d)) ≫ _ = _
      rw [hp, Hd.map_zero, zero_comp, comp_zero]
    show G.map ((HomologicalComplex.homologyFunctor B (.up ℤ) j).map
      ((E.mapHomologicalComplex (.up ℤ)).map (p ≫ d))) = 0
    rw [he, G.map_zero]
  have hstep (n : ℕ) : H.map (p ≫ Pi.π X (n + 1)) ≫
      H.map (I.map (homOfLE (Nat.le_succ n)).op) = H.map (p ≫ Pi.π X n) := by
    have hh := congrArg (fun f => f ≫ H.map (Pi.π X n)) hp'
    rw [← H.map_comp, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
      H.map_sub, zero_comp] at hh
    simpa only [H.map_comp, Category.assoc] using (sub_eq_zero.mp hh).symm
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base =>
      show H.map (p ≫ Pi.π X m) ≫ H.map (I.map (𝟙 _)) = H.map (p ≫ Pi.π X m)
      rw [I.map_id, H.map_id, Category.comp_id]
  | succ n hmn ih =>
      have hmap : I.map (homOfLE (hmn.trans (Nat.le_succ n))).op =
          I.map (homOfLE (Nat.le_succ n)).op ≫ I.map (homOfLE hmn).op := by
        rw [← I.map_comp]
        rfl
      rw [hmap, H.map_comp (I.map _) (I.map _), ← Category.assoc]
      exact (congrArg (fun t => t ≫ H.map (I.map (homOfLE hmn).op)) (hstep n)).trans ih

/-- **The mapping cocone of the Milnor difference of a K-injective tower is a derived limit.**
Let `I : ℕᵒᵖ ⥤ C(A)` be a tower of K-injective complexes representing a tower `K` in `D(A)`,
and let `L` be presented as a derived limit of `K` by a distinguished triangle with first map
`p`. Then the mapping cocone of the Milnor difference of `I` is isomorphic to `L`, compatibly
with the projections to every stage.

K-injectivity is what makes `Q(∏ Iₙ)` the product of the `Q(Iₙ)`; the mapping cocone triangle
is then a second derived-limit triangle for the same tower, and two such are isomorphic by the
usual triangulated argument.

This is the concrete model of the derived limit of Stacks 0D6T. -/
theorem exists_mappingCocone_iso_of_isKInjective_tower
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasProductsOfShape ℕ A]
    (I : ℕᵒᵖ ⥤ CochainComplex A ℤ) (hI : ∀ n : ℕ, (I.obj (.op n)).IsKInjective)
    (K : ℕᵒᵖ ⥤ DerivedCategory A) (e : I ⋙ DerivedCategory.Q ≅ K)
    [HasProduct (fun n : ℕ => K.obj (.op n))]
    (L : DerivedCategory A) (p : L ⟶ ∏ᶜ fun n : ℕ => K.obj (.op n))
    (δ : (∏ᶜ fun n : ℕ => K.obj (.op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk p (Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => K.obj (.op n)) n -
      Pi.π (fun n : ℕ => K.obj (.op n)) (n + 1) ≫
        K.map (homOfLE (Nat.le_succ n)).op)) δ ∈ distTriang (DerivedCategory A)) :
    let X := fun n : ℕ => I.obj (.op n)
    let d := Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫
      I.map (homOfLE (Nat.le_succ n)).op)
    ∃ a : DerivedCategory.Q.obj (CochainComplex.mappingCocone d) ≅ L,
      ∀ n : ℕ, DerivedCategory.Q.map
        ((CochainComplex.mappingCocone.triangle d).mor₁ ≫ Pi.π X n) ≫ e.hom.app (.op n) =
        a.hom ≫ p ≫ Pi.π (fun n : ℕ => K.obj (.op n)) n := by
  intro X d
  let Q := DerivedCategory.Q (C := A)
  let eX : Discrete.functor (fun n : ℕ => Q.obj (X n)) ≅
      Discrete.functor (fun n : ℕ => K.obj (.op n)) :=
    Discrete.natIso (fun n => e.app (.op n.as))
  have : HasProduct (fun n : ℕ => Q.obj (X n)) := hasLimit_of_iso eX.symm
  have := isIso_piComparison_Q_of_isKInjective X hI
  let a : Q.obj (∏ᶜ X) ≅ ∏ᶜ (fun n : ℕ => K.obj (.op n)) :=
    asIso (piComparison Q X) ≪≫ HasLimit.isoOfNatIso eX
  have ha (n : ℕ) : a.hom ≫ Pi.π (fun n : ℕ => K.obj (.op n)) n =
      Q.map (Pi.π X n) ≫ e.hom.app (.op n) := by
    dsimp only [a, Iso.trans_hom]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    show (piComparison Q X ≫ Pi.π (fun n => Q.obj (X n)) n) ≫ _ = _
    rw [piComparison_comp_π]
    rfl
  let pc : CochainComplex.mappingCocone d ⟶ ∏ᶜ X :=
    (CochainComplex.mappingCocone.triangle d).mor₁
  let T := Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle d)
  let dK := Pi.lift (fun n : ℕ => Pi.π (fun n : ℕ => K.obj (.op n)) n -
    Pi.π (fun n : ℕ => K.obj (.op n)) (n + 1) ≫
      K.map (homOfLE (Nat.le_succ n)).op)
  let U := Triangle.mk p dK δ
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.mappingCocone_triangle_distinguished d
  have hcomm : Q.map d ≫ a.hom = a.hom ≫ dK := by
    refine Pi.hom_ext _ _ fun n => ?_
    rw [Category.assoc, ha, ← Category.assoc, ← Q.map_comp]
    dsimp only [d, dK]
    rw [Pi.lift_comp_π, Q.map_sub, Q.map_comp, Preadditive.sub_comp, Category.assoc,
      Category.assoc a.hom, Pi.lift_comp_π, Preadditive.comp_sub, ha, ← Category.assoc a.hom, ha]
    simp only [Category.assoc]
    exact congrArg (fun t => Q.map (Pi.π X n) ≫ e.hom.app (.op n) -
      Q.map (Pi.π X (n + 1)) ≫ t)
      (e.hom.naturality (homOfLE (Nat.le_succ n)).op)
  let er := isoTriangleOfIso₁₂ T.rotate U.rotate
    (rot_of_distTriang _ hT) (rot_of_distTriang _ hδ) a a hcomm
  let et : T ≅ U := (rotate (DerivedCategory A)).preimageIso er
  have het₂ : et.hom.hom₂ = a.hom :=
    (congrArg (fun f => f.hom₁) ((rotate (DerivedCategory A)).map_preimage er.hom)).trans
      (isoTriangleOfIso₁₂_hom_hom₁ ..)
  let et₁ : Q.obj (CochainComplex.mappingCocone d) ≅ L := Triangle.π₁.mapIso et
  refine ⟨et₁, fun n => ?_⟩
  have hc : Q.map pc ≫ a.hom = et₁.hom ≫ p :=
    (congrArg (fun u => T.mor₁ ≫ u) het₂).symm.trans et.hom.comm₁
  show Q.map (pc ≫ Pi.π X n) ≫ _ = _
  rw [Q.map_comp, Category.assoc, ← ha, ← Category.assoc, hc, Category.assoc]

end Stacks.InverseSystem

end
