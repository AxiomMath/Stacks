module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.CompletePartialOrder

/-!
# Countable coproducts in the derived category of modules

Homology of cochain complexes of `R`-modules commutes with countable coproducts, so
quasi-isomorphisms are stable under countable coproducts. Using that a product of localization
functors with left calculi of fractions is again a localization, this file shows that the
localization functor `DerivedCategory.Q` preserves colimits of shape `Discrete ℕ`.

## Main results

* `homologyFunctor_preservesCoproductsℕ`: the degree-`n` homology functor on cochain complexes
  of `R`-modules preserves coproducts indexed by `ℕ`.
* `quasiIso_stableUnderCoproductsℕ`: quasi-isomorphisms are stable under coproducts indexed
  by `ℕ`.
* `functorPi_isLocalization_of_leftCoF`: a product of localization functors at morphism
  properties with left calculi of fractions is a localization at the product property.
* `functorPi_Q_isLocalizationℕ`: the product of countably many copies of `DerivedCategory.Q` is
  a localization at the componentwise quasi-isomorphisms.
* `derivedCategoryQ_preservesColimitsOfShapeℕ`: `DerivedCategory.Q` preserves colimits of shape
  `Discrete ℕ`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.MappingTelescope

universe w u

variable {R : Type u} [Ring R]

/-- The functor `HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) n`,
sending a complex to its short complex in degrees `prev n`, `n`, `next n`, preserves coproducts
indexed by `ℕ`. -/
theorem shortComplexFunctor_preservesCoproductsℕ (n : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ)
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n) := by
  refine ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) ?_⟩
  apply ShortComplex.isColimitOfIsColimitπ <;>
    exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) (colimit.isColimit F)

/-- The homology functor on short complexes of `R`-modules preserves coproducts indexed
by `ℕ`. -/
theorem shortComplexHomologyFunctor_preservesCoproductsℕ :
    PreservesColimitsOfShape (Discrete ℕ)
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  let CC : (Discrete ℕ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := colim
  have hpfl : PreservesFiniteLimits CC :=
    (inferInstance : HasExactColimitsOfShape (Discrete ℕ) (ModuleCat.{u} R)).preservesFiniteLimits
  have hpcs : PreservesColimitsOfSize.{0,0} CC :=
    (colimConstAdj (J := Discrete ℕ) (C := ModuleCat.{u} R)).leftAdjoint_preservesColimits
  have hpfc : PreservesFiniteColimits CC :=
    PreservesColimitsOfSize.preservesFiniteColimits CC
  have hph : CC.PreservesHomology := Functor.preservesHomologyOfExact _
  refine ⟨fun {K} => ?_⟩
  set Sc := (ShortComplex.functorEquivalence (Discrete ℕ) (ModuleCat.{u} R)).inverse.obj K
  refine preservesColimit_of_preserves_colimit_cocone (ShortComplex.isColimitColimitCocone K) ?_
  refine IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ ShortComplex.homologyFunctor _))
    (Cocone.ext ((HasColimit.isoOfNatIso (Discrete.natIso (fun j =>
        ((ShortComplex.homologyFunctorIso ((evaluation (Discrete ℕ) (ModuleCat.{u} R)).obj j)).app
            Sc).symm)).symm) ≪≫
      ((ShortComplex.homologyFunctorIso CC).app Sc).symm) ?_)
  intro j
  simp only [Functor.mapCocone_ι_app, Iso.trans_hom, Iso.symm_hom, colimit.cocone_ι]
  rw [show (ShortComplex.colimitCocone K).ι.app j = Sc.mapNatTrans (colim.ι j) from rfl,
    ShortComplex.homologyFunctor_map]
  refine Eq.trans ?_ (ShortComplex.homologyMap_mapNatTrans Sc (colim.ι j)).symm
  rw [HasColimit.ι_isoOfNatIso_hom_assoc,
    show ((ShortComplex.homologyFunctorIso CC).app Sc).inv = (Sc.mapHomologyIso CC).inv from rfl,
    colim.ι_app]
  congr 1

/-- For every `n : ℤ`, the degree-`n` homology functor on cochain complexes of `R`-modules
preserves coproducts indexed by `ℕ`. -/
theorem homologyFunctor_preservesCoproductsℕ (n : ℤ) :
    PreservesColimitsOfShape (Discrete ℕ)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n) := by
  have := shortComplexFunctor_preservesCoproductsℕ (R := R) n
  have := shortComplexHomologyFunctor_preservesCoproductsℕ (R := R)
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} R) (ComplexShape.up ℤ) n).symm

/-- Quasi-isomorphisms of cochain complexes of `R`-modules are stable under coproducts indexed
by `ℕ`. -/
theorem quasiIso_stableUnderCoproductsℕ :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R)
      (ComplexShape.up ℤ)).IsStableUnderCoproductsOfShape ℕ := by
  refine ⟨fun X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ => ?_⟩
  rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  set H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have := homologyFunctor_preservesCoproductsℕ (R := R) i
  rw [← HomologicalComplex.homologyFunctor_map (ModuleCat.{u} R) (ComplexShape.up ℤ) i φ]
  have hcF : IsColimit (H.mapCocone c₁) := isColimitOfPreserves H h₁
  have hcG : IsColimit (H.mapCocone c₂) := isColimitOfPreserves H h₂
  set α := Functor.whiskerRight f H with hα
  have : ∀ j, IsIso (α.app j) := by
    intro j
    rw [hα, Functor.whiskerRight_app, HomologicalComplex.homologyFunctor_map,
      ← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff (f.app j)).mp ((HomologicalComplex.mem_quasiIso_iff _).mp (hf j)) i
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have heq : H.map φ = (IsColimit.coconePointsIsoOfNatIso hcF hcG (asIso α)).hom := by
    refine hcF.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp only [Functor.mapCocone_ι_app, ← H.map_comp, hφ j]
    simp [asIso, hα]
  rw [heq]
  infer_instance

/-- The cocone on `F` with point `Lc.obj F` given by the unit of an adjunction
`Lc ⊣ Functor.const K`. -/
noncomputable def coconeOfAdj {K : Type*} [Category K] {C' : Type*} [Category C']
    {Lc : (K ⥤ C') ⥤ C'} (adj : Lc ⊣ Functor.const K) (F : K ⥤ C') : Cocone F :=
  { pt := Lc.obj F, ι := adj.unit.app F }

/-- The cocone `coconeOfAdj adj F` is a colimit cocone. -/
noncomputable def isColimitCoconeOfAdj {K : Type*} [Category K] {C' : Type*} [Category C']
    {Lc : (K ⥤ C') ⥤ C'} (adj : Lc ⊣ Functor.const K) (F : K ⥤ C') :
    IsColimit (coconeOfAdj adj F) where
  desc s := (adj.homEquiv F s.pt).symm s.ι
  fac s j := by
    have key := (adj.homEquiv F s.pt).apply_symm_apply s.ι
    rw [adj.homEquiv_unit] at key
    have hj := congr_app key j
    dsimp [coconeOfAdj] at hj ⊢
    simpa using hj
  uniq s m hm := by
    apply (adj.homEquiv F s.pt).injective
    rw [Equiv.apply_symm_apply, adj.homEquiv_unit]
    ext j
    have := hm j
    dsimp [coconeOfAdj] at this ⊢
    rw [← this]

/-- If each `Wq j` admits a left calculus of fractions, then so does the product morphism
property `MorphismProperty.pi Wq`. -/
theorem pi_hasLeftCalculusOfFractions {J : Type*} {C : J → Type*} [∀ j, Category (C j)]
    (Wq : ∀ j, MorphismProperty (C j)) [∀ j, (Wq j).HasLeftCalculusOfFractions] :
    (MorphismProperty.pi Wq).HasLeftCalculusOfFractions := by
  have hid : (MorphismProperty.pi Wq).ContainsIdentities :=
    ⟨fun X j => (Wq j).id_mem (X j)⟩
  have hcomp : (MorphismProperty.pi Wq).IsStableUnderComposition :=
    ⟨fun f g hf hg j => (Wq j).comp_mem (f j) (g j) (hf j) (hg j)⟩
  have hmult : (MorphismProperty.pi Wq).IsMultiplicative := ⟨⟩
  refine ⟨?_, ?_⟩
  · intro X Y φ
    choose ψ hψ using fun j =>
      MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction (W := Wq j)
        (MorphismProperty.RightFraction.mk (φ.s j) (φ.hs j) (φ.f j))
    exact ⟨MorphismProperty.LeftFraction.mk
      (fun j => (ψ j).f) (fun j => (ψ j).s) (fun j => (ψ j).hs), funext hψ⟩
  · intro X' X Y f₁ f₂ s hs heq
    choose Y' t ht hcancel using fun j =>
      MorphismProperty.HasLeftCalculusOfFractions.ext (W := Wq j)
        (f₁ j) (f₂ j) (s j) (hs j) (funext_iff.mp heq j)
    exact ⟨Y', t, ht, funext hcancel⟩

/-- The lift of a functor `F` inverting `W` through the localization construction agrees with
`F` on the images of morphisms under `W.Q`. -/
theorem lift_map_Q_map {C D : Type*} [Category C] [Category D] {W : MorphismProperty C}
    (F : C ⥤ D) (hF : W.IsInvertedBy F) {A B : C} (h : A ⟶ B) :
    (Localization.Construction.lift F hF).map (W.Q.map h) = F.map h := by
  simpa using Functor.congr_hom (Localization.Construction.fac F hF) h

/-- The lift of a functor `F` inverting `W` through the localization construction sends the
image of a left fraction under `W.Q` to its image under `F`. -/
theorem lift_map_leftFraction_map {C D : Type*} [Category C] [Category D]
    {W : MorphismProperty C} (F : C ⥤ D) (hF : W.IsInvertedBy F) {A B : C}
    (φ : W.LeftFraction A B) (hQ : W.IsInvertedBy W.Q) :
    (Localization.Construction.lift F hF).map (φ.map W.Q hQ) = φ.map F hF := by
  have i1 := hF φ.s φ.hs
  have := hQ φ.s φ.hs
  have i2 : IsIso ((Localization.Construction.lift F hF).map (W.Q.map φ.s)) := inferInstance
  rw [MorphismProperty.LeftFraction.map, MorphismProperty.LeftFraction.map, Functor.map_comp,
    Functor.map_inv, lift_map_Q_map]
  congr 1
  exact (@IsIso.inv_eq_inv _ _ _ _ _ _ i2 i1).mpr (lift_map_Q_map F hF φ.s)

/-- The `j`-th component of the image of a left fraction for `MorphismProperty.pi Wq` under
`Functor.pi Lh` is the image under `Lh j` of its `j`-th component. -/
theorem leftFraction_map_pi_apply {J : Type*} {C D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (Lh : ∀ j, C j ⥤ D j) (Wq : ∀ j, MorphismProperty (C j)) [∀ j, (Lh j).IsLocalization (Wq j)]
    (inverts : (MorphismProperty.pi Wq).IsInvertedBy (Functor.pi Lh)) {A B : ∀ j, C j}
    (φ : (MorphismProperty.pi Wq).LeftFraction A B) (j : J) :
    (φ.map (Functor.pi Lh) inverts) j
      = (MorphismProperty.LeftFraction.mk (φ.f j) (φ.s j) (φ.hs j)).map (Lh j)
          (Localization.inverts (Lh j) (Wq j)) := by
  have ij : IsIso ((Lh j).map (φ.s j)) := Localization.inverts (Lh j) (Wq j) _ (φ.hs j)
  simp only [MorphismProperty.LeftFraction.map]
  exact (@IsIso.eq_comp_inv _ _ _ _ _ _ ij _ _).mpr
    (congr_fun (MorphismProperty.LeftFraction.map_comp_map_s φ (Functor.pi Lh) inverts) j)

/-- Let each `Lh j` be a localization functor at `Wq j`, where `Wq j` admits a left calculus of
fractions. Then the functor `(MorphismProperty.pi Wq).Localization ⥤ ∀ j, D j` induced by
`Functor.pi Lh` is full. -/
theorem functorPi_lift_full {J : Type*} {C D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (Lh : ∀ j, C j ⥤ D j) (Wq : ∀ j, MorphismProperty (C j))
    [∀ j, (Lh j).IsLocalization (Wq j)] [∀ j, (Wq j).HasLeftCalculusOfFractions]
    (inverts : (MorphismProperty.pi Wq).IsInvertedBy (Functor.pi Lh)) :
    (Localization.Construction.lift (Functor.pi Lh) inverts).Full := by
  have := pi_hasLeftCalculusOfFractions Wq
  have hfac := Localization.Construction.fac (Functor.pi Lh) inverts
  refine ⟨fun {X Y} f => ?_⟩
  obtain ⟨A, rfl⟩ := (Localization.Construction.objEquiv (MorphismProperty.pi Wq)).surjective X
  obtain ⟨B, rfl⟩ := (Localization.Construction.objEquiv (MorphismProperty.pi Wq)).surjective Y
  set f' : (Functor.pi Lh).obj A ⟶ (Functor.pi Lh).obj B :=
    eqToHom (Functor.congr_obj hfac A).symm ≫ f ≫ eqToHom (Functor.congr_obj hfac B) with hf'
  choose ψ hψ using fun j => Localization.exists_leftFraction (Lh j) (Wq j) (f' j)
  let φ : (MorphismProperty.pi Wq).LeftFraction A B :=
    MorphismProperty.LeftFraction.mk (fun j => (ψ j).f) (fun j => (ψ j).s) (fun j => (ψ j).hs)
  have hmaps : φ.map (Functor.pi Lh) inverts = f' := by
    funext j
    rw [leftFraction_map_pi_apply Lh Wq inverts φ j, hψ j]
  refine ⟨φ.map _ (Localization.inverts (MorphismProperty.pi Wq).Q (MorphismProperty.pi Wq)), ?_⟩
  rw [lift_map_leftFraction_map, hmaps, hf']
  simp

/-- Let each `Lh j` be a localization functor at `Wq j`, where `Wq j` admits a left calculus of
fractions. Then the functor `(MorphismProperty.pi Wq).Localization ⥤ ∀ j, D j` induced by
`Functor.pi Lh` is faithful. -/
theorem functorPi_lift_faithful {J : Type*} {C D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (Lh : ∀ j, C j ⥤ D j) (Wq : ∀ j, MorphismProperty (C j))
    [∀ j, (Lh j).IsLocalization (Wq j)] [∀ j, (Wq j).HasLeftCalculusOfFractions]
    (inverts : (MorphismProperty.pi Wq).IsInvertedBy (Functor.pi Lh)) :
    (Localization.Construction.lift (Functor.pi Lh) inverts).Faithful := by
  have := pi_hasLeftCalculusOfFractions Wq
  refine ⟨fun {X Y} f g hfg => ?_⟩
  obtain ⟨A, rfl⟩ := (Localization.Construction.objEquiv (MorphismProperty.pi Wq)).surjective X
  obtain ⟨B, rfl⟩ := (Localization.Construction.objEquiv (MorphismProperty.pi Wq)).surjective Y
  obtain ⟨φf, rfl⟩ := Localization.exists_leftFraction (MorphismProperty.pi Wq).Q
      (MorphismProperty.pi Wq) f
  obtain ⟨φg, rfl⟩ := Localization.exists_leftFraction (MorphismProperty.pi Wq).Q
      (MorphismProperty.pi Wq) g
  rw [lift_map_leftFraction_map, lift_map_leftFraction_map] at hfg
  have hrel : ∀ j, MorphismProperty.LeftFractionRel
      (MorphismProperty.LeftFraction.mk (φf.f j) (φf.s j) (φf.hs j))
      (MorphismProperty.LeftFraction.mk (φg.f j) (φg.s j) (φg.hs j)) := fun j => by
    rw [← MorphismProperty.LeftFraction.map_eq_iff (Lh j) (Wq j),
      ← leftFraction_map_pi_apply Lh Wq inverts, ← leftFraction_map_pi_apply Lh Wq inverts, hfg]
  choose Z t₁ t₂ hs hf hw using hrel
  exact (MorphismProperty.LeftFraction.map_eq_iff _ (MorphismProperty.pi Wq) φf φg).mpr
    ⟨Z, t₁, t₂, funext hs, funext hf, hw⟩

/-- For an arbitrary index type `J`, if each `Lh j` is a localization functor at a morphism
property `Wq j` admitting a left calculus of fractions, then `Functor.pi Lh` is a localization
functor at `MorphismProperty.pi Wq`. -/
theorem functorPi_isLocalization_of_leftCoF {J : Type*} {C D : J → Type*}
    [∀ j, Category (C j)] [∀ j, Category (D j)]
    (Lh : ∀ j, C j ⥤ D j) (Wq : ∀ j, MorphismProperty (C j))
    [∀ j, (Lh j).IsLocalization (Wq j)] [∀ j, (Wq j).HasLeftCalculusOfFractions] :
    (Functor.pi Lh).IsLocalization (MorphismProperty.pi Wq) := by
  have inverts : (MorphismProperty.pi Wq).IsInvertedBy (Functor.pi Lh) :=
    MorphismProperty.IsInvertedBy.pi Wq Lh (fun j => Localization.inverts (Lh j) (Wq j))
  apply Functor.IsLocalization.mk inverts
  have hfac := Localization.Construction.fac (Functor.pi Lh) inverts
  have hessSurj : (Localization.Construction.lift (Functor.pi Lh) inverts).EssSurj := by
    refine ⟨fun Y => ?_⟩
    have hes : ∀ j, (Lh j).EssSurj := fun j => Localization.essSurj (Lh j) (Wq j)
    let X : ∀ j, C j := fun j => ((hes j).mem_essImage (Y j)).choose
    have hiso : ∀ j, (Lh j).obj (X j) ≅ Y j :=
      fun j => ((hes j).mem_essImage (Y j)).choose_spec.some
    exact ⟨(MorphismProperty.pi Wq).Q.obj X, ⟨eqToIso (Functor.congr_obj hfac X) ≪≫
      { hom := fun j => (hiso j).hom
        inv := fun j => (hiso j).inv
        hom_inv_id := funext fun j => (hiso j).hom_inv_id
        inv_hom_id := funext fun j => (hiso j).inv_hom_id }⟩⟩
  exact Functor.IsEquivalence.mk (functorPi_lift_faithful Lh Wq inverts)
    (functorPi_lift_full Lh Wq inverts) hessSurj

/-- The product homotopy congruence on `ℕ → CochainComplex (ModuleCat R) ℤ`:
two families of chain maps are related iff they are homotopic in each coordinate. -/
def prodHtpy (R : Type u) [Ring R] : HomRel (ℕ → CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun _ _ f g => ∀ n, homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ) (f n) (g n)

/-- The componentwise homotopy relation `prodHtpy R` is a congruence. -/
instance prodHtpyCongruence (R : Type u) [Ring R] : Congruence (prodHtpy R) where
  equivalence := ⟨fun _ _ => (homotopy_congruence _ _).equivalence.refl _,
    fun h n => (homotopy_congruence _ _).equivalence.symm (h n),
    fun h1 h2 n => (homotopy_congruence _ _).equivalence.trans (h1 n) (h2 n)⟩
  comp_left _ _ _ h n := (homotopy_congruence _ _).comp_left _ (h n)
  comp_right _ h n := (homotopy_congruence _ _).comp_right _ (h n)

/-- The product of the homotopy-category quotient functors, indexed by `ℕ`. -/
abbrev piQuotient (R : Type u) [Ring R] :
    (ℕ → CochainComplex (ModuleCat.{u} R) ℤ) ⥤
      (ℕ → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- Families of maps related by `prodHtpy R`, that is, componentwise homotopic families, have
the same image under `piQuotient R`. -/
theorem piQuotient_map_eq_of_prodHtpy (R : Type u) [Ring R]
    (x y : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f g : x ⟶ y) (h : prodHtpy R f g) :
    (piQuotient R).map f = (piQuotient R).map g := by
  funext n
  change (HomotopyCategory.quotient _ _).map (f n) = (HomotopyCategory.quotient _ _).map (g n)
  exact (Quotient.functor_map_eq_iff _ _ _).mpr (h n)

/-- The comparison functor from `Quotient (prodHtpy R)` to the product of the homotopy
categories, induced by `piQuotient R` via the universal property of the quotient. -/
noncomputable def prodHtpyQuotientToPi (R : Type u) [Ring R] :
    (CategoryTheory.Quotient (prodHtpy R)) ⥤
      (ℕ → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.lift (prodHtpy R) (piQuotient R) (piQuotient_map_eq_of_prodHtpy R)

/-- The composite of the quotient functor for `prodHtpy R` with `prodHtpyQuotientToPi R` is
`piQuotient R`. -/
theorem prodHtpyQuotientToPi_spec (R : Type u) [Ring R] :
    Quotient.functor (prodHtpy R) ⋙ prodHtpyQuotientToPi R = piQuotient R :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The functor `prodHtpyQuotientToPi R` is faithful. -/
theorem prodHtpyQuotientToPi_faithful (R : Type u) [Ring R] :
    (prodHtpyQuotientToPi R).Faithful where
  map_injective {A B} p q hpq := by
    obtain ⟨a⟩ := A
    obtain ⟨b⟩ := B
    obtain ⟨f, rfl⟩ := (Quotient.full_functor (prodHtpy R)).map_surjective p
    obtain ⟨g, rfl⟩ := (Quotient.full_functor (prodHtpy R)).map_surjective q
    replace hpq : (piQuotient R).map f = (piQuotient R).map g := hpq
    rw [Quotient.functor_map_eq_iff]
    intro n
    rw [← Quotient.functor_map_eq_iff (homotopic (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    exact congrFun hpq n

/-- The functor `prodHtpyQuotientToPi R` is full. -/
theorem prodHtpyQuotientToPi_full (R : Type u) [Ring R] :
    (prodHtpyQuotientToPi R).Full where
  map_surjective {A B} φ := by
    obtain ⟨a⟩ := A
    obtain ⟨b⟩ := B
    choose f hf using fun n => (Quotient.full_functor _).map_surjective (φ n)
    refine ⟨(Quotient.functor (prodHtpy R)).map f, ?_⟩
    change (piQuotient R).map f = φ
    exact funext hf

/-- The functor `prodHtpyQuotientToPi R` is essentially surjective. -/
theorem prodHtpyQuotientToPi_essSurj (R : Type u) [Ring R] :
    (prodHtpyQuotientToPi R).EssSurj where
  mem_essImage Z := by
    choose X hX using fun n => HomotopyCategory.quotient_obj_surjective (Z n)
    refine ⟨⟨X⟩, ⟨eqToIso ?_⟩⟩
    change (piQuotient R).obj X = Z
    exact funext hX

/-- The functor `prodHtpyQuotientToPi R` is an equivalence of categories. -/
noncomputable instance prodHtpyQuotientToPiIsEquivalence (R : Type u) [Ring R] :
    (prodHtpyQuotientToPi R).IsEquivalence :=
  Functor.IsEquivalence.mk (prodHtpyQuotientToPi_faithful R) (prodHtpyQuotientToPi_full R)
    (prodHtpyQuotientToPi_essSurj R)

/-- The equivalence between `Quotient (prodHtpy R)` and the product of the homotopy
categories. -/
noncomputable def prodHtpyQuotientEquivPi (R : Type u) [Ring R] :
    (CategoryTheory.Quotient (prodHtpy R)) ≌
      (ℕ → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  (prodHtpyQuotientToPi R).asEquivalence

/-- A morphism is sent to an isomorphism by the quotient functor for `prodHtpy R` if and only if
it is sent to an isomorphism by `piQuotient R`. -/
private theorem isIso_quotient_map_iff {R : Type u} [Ring R]
    {x y : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (f : x ⟶ y) :
    IsIso ((Quotient.functor (prodHtpy R)).map f) ↔ IsIso ((piQuotient R).map f) :=
  (isIso_iff_of_reflects_iso ((Quotient.functor (prodHtpy R)).map f) (prodHtpyQuotientToPi R)).symm

/-- Let `G` be a functor out of `ℕ → CochainComplex (ModuleCat R) ℤ` that inverts every
morphism sent to an isomorphism by the quotient functor for `prodHtpy R`. Then `G` takes equal
values on families of maps related by `prodHtpy R`, that is, on componentwise homotopic
families. -/
theorem map_eq_of_prodHtpy (R : Type u) [Ring R] {E : Type*} [Category E]
    (G : (ℕ → CochainComplex (ModuleCat.{u} R) ℤ) ⥤ E)
    (hG : ((MorphismProperty.isomorphisms (CategoryTheory.Quotient (prodHtpy R))).inverseImage
      (Quotient.functor (prodHtpy R))).IsInvertedBy G)
    (x y : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f g : x ⟶ y) (h : prodHtpy R f g) :
    G.map f = G.map g := by
  classical
  have hc : ∀ (j : ℤ), ∃ i, (ComplexShape.up ℤ).Rel i j :=
    fun j => ⟨j - 1, by simp [ComplexShape.up_Rel]⟩
  let hh : ∀ n, Homotopy (f n) (g n) := fun n => (h n).some
  let i0 : x ⟶ (fun n => (x n).cylinder) := fun n => HomologicalComplex.cylinder.ι₀ (x n)
  let i1 : x ⟶ (fun n => (x n).cylinder) := fun n => HomologicalComplex.cylinder.ι₁ (x n)
  let pp : (fun n => (x n).cylinder) ⟶ x := fun n => HomologicalComplex.cylinder.π (x n)
  let HH : (fun n => (x n).cylinder) ⟶ y := fun n =>
    HomologicalComplex.cylinder.desc (f n) (g n) (hh n)
  have hppmem : ((MorphismProperty.isomorphisms (CategoryTheory.Quotient (prodHtpy R))).inverseImage
      (Quotient.functor (prodHtpy R))) pp := by
    rw [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]
    rw [isIso_quotient_map_iff, isIso_pi_iff]
    intro n
    exact Localization.inverts
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (pp n)
      ⟨HomologicalComplex.cylinder.homotopyEquiv (x n) hc,
        HomologicalComplex.cylinder.homotopyEquiv_hom (x n) _⟩
  have isopp : IsIso (G.map pp) := hG _ hppmem
  have c0 : i0 ≫ pp = 𝟙 x := funext fun n => HomologicalComplex.cylinder.ι₀_π (x n)
  have c1 : i1 ≫ pp = 𝟙 x := funext fun n => HomologicalComplex.cylinder.ι₁_π (x n)
  have key : G.map i0 = G.map i1 := by
    rw [← cancel_mono (G.map pp), ← G.map_comp, ← G.map_comp, c0, c1]
  have d0 : i0 ≫ HH = f := funext fun n => HomologicalComplex.cylinder.ι₀_desc (f n) (g n) (hh n)
  have d1 : i1 ≫ HH = g := funext fun n => HomologicalComplex.cylinder.ι₁_desc (f n) (g n) (hh n)
  rw [← d0, ← d1, G.map_comp, G.map_comp, key]

/-- The strict universal property of the quotient functor for `prodHtpy R` as a localization at
the morphisms it sends to isomorphisms. -/
noncomputable def prodHtpyQuotientStrictUniversalProperty (R : Type u) [Ring R]
    (E : Type*) [Category E] :
    Localization.StrictUniversalPropertyFixedTarget (Quotient.functor (prodHtpy R))
      ((MorphismProperty.isomorphisms (CategoryTheory.Quotient (prodHtpy R))).inverseImage
        (Quotient.functor (prodHtpy R))) E where
  inverts := fun _ _ _ hf => hf
  lift := fun G hG => CategoryTheory.Quotient.lift (prodHtpy R) G (map_eq_of_prodHtpy R G hG)
  fac := fun _ _ => CategoryTheory.Quotient.lift_spec _ _ _
  uniq := fun _ _ h => CategoryTheory.Quotient.lift_unique' _ _ _ h

/-- The quotient functor for the product homotopy congruence is a localization at the
morphisms it inverts. -/
theorem prodHtpyQuotient_isLocalization (R : Type u) [Ring R] :
    (Quotient.functor (prodHtpy R)).IsLocalization
      ((MorphismProperty.isomorphisms (CategoryTheory.Quotient (prodHtpy R))).inverseImage
        (Quotient.functor (prodHtpy R))) :=
  Functor.IsLocalization.mk' _ _ (prodHtpyQuotientStrictUniversalProperty R _)
    (prodHtpyQuotientStrictUniversalProperty R _)

/-- The morphisms sent to isomorphisms by the quotient functor for `prodHtpy R` are exactly the
morphisms sent to isomorphisms by `piQuotient R`. -/
theorem inverseImage_isomorphisms_prodHtpyQuotient_eq (R : Type u) [Ring R] :
    ((MorphismProperty.isomorphisms (CategoryTheory.Quotient (prodHtpy R))).inverseImage
      (Quotient.functor (prodHtpy R)))
    = (MorphismProperty.isomorphisms
        (ℕ → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))).inverseImage
        (piQuotient R) := by
  ext X Y f
  rw [MorphismProperty.inverseImage_iff, MorphismProperty.inverseImage_iff,
    MorphismProperty.isomorphisms.iff, MorphismProperty.isomorphisms.iff, isIso_quotient_map_iff]

/-- The product of the homotopy-category quotient functors indexed by `ℕ` is a localization at
the morphisms it sends to isomorphisms. -/
theorem functorPi_quotient_isLocalization_invIso :
    (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
        (ComplexShape.up ℤ))).IsLocalization
      ((MorphismProperty.isomorphisms
            ((_ : ℕ) → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))).inverseImage
        (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
          (ComplexShape.up ℤ)))) := by
  rw [← inverseImage_isomorphisms_prodHtpyQuotient_eq R]
  have := prodHtpyQuotient_isLocalization R
  exact Functor.IsLocalization.of_equivalence_target (Quotient.functor (prodHtpy R)) _
    (piQuotient R) (prodHtpyQuotientEquivPi R) (eqToIso (prodHtpyQuotientToPi_spec R))

/-- A morphism of `ℕ → CochainComplex (ModuleCat R) ℤ` is sent to an isomorphism by the product
of the homotopy-category quotient functors if and only if it is a componentwise homotopy
equivalence. -/
theorem functorPi_invIso_eq_pi_homotopyEquivalences :
    ((MorphismProperty.isomorphisms
          ((_ : ℕ) → HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))).inverseImage
        (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
          (ComplexShape.up ℤ))))
      = MorphismProperty.pi (fun _ : ℕ =>
          HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]
  ext X Y f
  rw [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    show (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
            (ComplexShape.up ℤ))).map f
          = fun j => (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map (f j)
        from rfl,
    isIso_pi_iff]
  rfl

/-- The product of the homotopy-category quotient functors indexed by `ℕ` is a localization at
the componentwise homotopy equivalences. -/
theorem functorPi_quotient_isLocalizationℕ :
    (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
        (ComplexShape.up ℤ))).IsLocalization
      (MorphismProperty.pi (fun _ : ℕ =>
        HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ))) := by
  rw [← functorPi_invIso_eq_pi_homotopyEquivalences]
  exact functorPi_quotient_isLocalization_invIso

/-- Every componentwise quasi-isomorphism in
`ℕ → HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)` is, up to isomorphism, the image under
the product of the quotient functors of a componentwise quasi-isomorphism of cochain complexes. -/
theorem functorPi_quasiIso_le_map :
    (MorphismProperty.pi (fun _ : ℕ =>
        HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) ≤
      (MorphismProperty.pi (fun _ : ℕ =>
        HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))).map
        (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R)
          (ComplexShape.up ℤ))) := by
  intro X Y f hf
  choose g hg using fun j => Functor.map_surjective
    (F := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)) (f j)
  refine ⟨fun j => (X j).as, fun j => (Y j).as, g, ?_, ?_⟩
  · intro j
    rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff, hg j]
    exact hf j
  · exact ⟨Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      funext j
      simp only [Functor.pi_map, Arrow.mk_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact (hg j).symm)⟩

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Componentwise quasi-isomorphisms are inverted by the product of the homotopy-category quotient
functors followed by the product of the functors `DerivedCategory.Qh`. -/
theorem pi_quasiIso_isInvertedBy_functorPi_quotient_comp_Qh :
    (MorphismProperty.pi (fun _ : ℕ =>
        HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))).IsInvertedBy
      (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)) ⋙
        Functor.pi (fun (_ : ℕ) => DerivedCategory.Qh (C := ModuleCat.{u} R))) := by
  intro X Y f hf
  let eIso : Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      ≅ Functor.pi (fun (_ : ℕ) => DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    NatIso.pi (fun (_ : ℕ) => DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  have hQinv : IsIso ((Functor.pi (fun (_ : ℕ) =>
      DerivedCategory.Q (C := ModuleCat.{u} R))).map f) := by
    rw [isIso_pi_iff]
    intro j
    exact Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (f j) (hf j)
  have hmapeq : (Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Qh)).map f
      = eIso.hom.app X ≫ (Functor.pi (fun (_ : ℕ) =>
          DerivedCategory.Q (C := ModuleCat.{u} R))).map f ≫ eIso.inv.app Y := by
    rw [← Category.assoc, ← eIso.hom.naturality f, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  change IsIso ((Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Qh)).map f)
  rw [hmapeq]
  infer_instance

/-- The functor `Functor.pi (fun _ : ℕ => DerivedCategory.Q)` from
`ℕ → CochainComplex (ModuleCat R) ℤ` to `ℕ → DerivedCategory (ModuleCat R)` is a localization at
the componentwise quasi-isomorphisms. -/
theorem functorPi_Q_isLocalizationℕ :
    (Functor.pi (fun (_ : ℕ) => DerivedCategory.Q (C := ModuleCat.{u} R))).IsLocalization
      (MorphismProperty.pi (fun _ : ℕ =>
        HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) := by
  let Wq : MorphismProperty (ℕ → CochainComplex (ModuleCat.{u} R) ℤ) :=
    MorphismProperty.pi (fun _ : ℕ =>
      HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  have hQh : (Functor.pi (fun (_ : ℕ) => DerivedCategory.Qh (C := ModuleCat.{u} R))).IsLocalization
      (MorphismProperty.pi (fun _ : ℕ =>
        HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))) :=
    functorPi_isLocalization_of_leftCoF _ _
  have hquot := functorPi_quotient_isLocalizationℕ (R := R)
  let eIso : Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      ≅ Functor.pi (fun (_ : ℕ) => DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    NatIso.pi (fun (_ : ℕ) => DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  have hcomp : ((Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))) ⋙
      (Functor.pi (fun (_ : ℕ) =>
        DerivedCategory.Qh (C := ModuleCat.{u} R)))).IsLocalization Wq := by
    apply Functor.IsLocalization.comp
      (Functor.pi (fun (_ : ℕ) => HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (Functor.pi (fun (_ : ℕ) => DerivedCategory.Qh (C := ModuleCat.{u} R)))
      (MorphismProperty.pi (fun _ : ℕ =>
        HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      (MorphismProperty.pi (fun _ : ℕ =>
        HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
      Wq
    · exact pi_quasiIso_isInvertedBy_functorPi_quotient_comp_Qh
    · intro X Y f hf j
      exact (homotopyEquivalences_le_quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ (hf j)
    · exact functorPi_quasiIso_le_map (R := R)
  have heq : (Functor.pi (fun (_ : ℕ) =>
      HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))) ⋙
      (Functor.pi (fun (_ : ℕ) => DerivedCategory.Qh (C := ModuleCat.{u} R)))
      = Functor.pi (fun (_ : ℕ) =>
          HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
            ⋙ DerivedCategory.Qh) := rfl
  rw [heq] at hcomp
  exact Functor.IsLocalization.of_iso Wq eIso

open CategoryTheory.Functor.IsLocalization in
/-- Postcomposition with `DerivedCategory.Q`, as a functor from
`Discrete ℕ ⥤ CochainComplex (ModuleCat R) ℤ` to `Discrete ℕ ⥤ DerivedCategory (ModuleCat R)`,
is a localization at the natural transformations that are objectwise quasi-isomorphisms. -/
theorem whiskeringRight_Q_isLocalizationℕ :
    ((Functor.whiskeringRight (Discrete ℕ) (CochainComplex (ModuleCat.{u} R) ℤ)
        (DerivedCategory (ModuleCat.{u} R))).obj (DerivedCategory.Q)).IsLocalization
      ((HomologicalComplex.quasiIso (ModuleCat.{u} R)
        (ComplexShape.up ℤ)).functorCategory (Discrete ℕ)) := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let L := DerivedCategory.Q (C := ModuleCat.{u} R)
  let E := piEquivalenceFunctorDiscrete ℕ (CochainComplex (ModuleCat.{u} R) ℤ)
  let E' := piEquivalenceFunctorDiscrete ℕ (DerivedCategory (ModuleCat.{u} R))
  let L₂ := (Functor.whiskeringRight (Discrete ℕ) (CochainComplex (ModuleCat.{u} R) ℤ)
    (DerivedCategory (ModuleCat.{u} R))).obj L
  let L₁ := Functor.pi (fun (_ : ℕ) => L)
  have : L₁.IsLocalization (MorphismProperty.pi (fun _ => W)) :=
    functorPi_Q_isLocalizationℕ (R := R)
  have hsq : CatCommSq E.functor L₁ L₂ E'.functor :=
    ⟨(Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E'.counitIso.symm ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Iso.refl _) _) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm L₁) _ ≪≫ Functor.isoWhiskerRight L₁.leftUnitor _⟩
  refine Functor.IsLocalization.of_equivalences L₁
    (MorphismProperty.pi (fun _ => W)) L₂ _ E E' ?_ ?_
  · exact fun X Y f hf => MorphismProperty.le_isoClosure _ _ (fun ⟨j⟩ => hf j)
  · intro X Y f hf
    have : ∀ (j : Discrete ℕ), IsIso ((L₂.map f).app j) :=
      fun j => Localization.inverts L W _ (hf j)
    apply NatIso.isIso_of_isIso_app

open CategoryTheory.Localization CategoryTheory.Functor in
/-- The localization functor `DerivedCategory.Q` for `R`-modules preserves colimits of shape
`Discrete ℕ`. -/
theorem derivedCategoryQ_preservesColimitsOfShapeℕ :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := ModuleCat.{u} R)) := by
  set L : CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (ModuleCat.{u} R) :=
    DerivedCategory.Q
  set W : MorphismProperty (CochainComplex (ModuleCat.{u} R) ℤ) :=
    HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
  have hwl : ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L).IsLocalization
      (W.functorCategory (Discrete ℕ)) := whiskeringRight_Q_isLocalizationℕ (R := R)
  have : W.IsStableUnderCoproductsOfShape ℕ := quasiIso_stableUnderCoproductsℕ (R := R)
  have : W.ContainsIdentities := inferInstance
  have : L.IsLocalization W := inferInstance
  have invertsLem : (W.functorCategory (Discrete ℕ)).IsInvertedBy (colim ⋙ L) :=
    fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.colimMap f hf)
  let colF : (Discrete ℕ ⥤ DerivedCategory (ModuleCat.{u} R)) ⥤ DerivedCategory (ModuleCat.{u} R) :=
    Localization.lift _ invertsLem ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L)
  let compIso : ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) ⋙ colF ≅ colim ⋙ L :=
    Localization.fac _ invertsLem _
  let ccsqC : CatCommSq (Functor.const (Discrete ℕ)) L
      ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) (Functor.const (Discrete ℕ)) :=
    ⟨(Functor.compConstIso _ _).symm⟩
  let ccsq : CatCommSq colim ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) L colF :=
    ⟨compIso.symm⟩
  let adjL : colF ⊣ Functor.const _ :=
    (colimConstAdj (J := Discrete ℕ) (C := CochainComplex (ModuleCat.{u} R) ℤ)).localization
      ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) (W.functorCategory (Discrete ℕ))
      L W colF (Functor.const _)
  have adjL_unit_app : ∀ (F : Discrete ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ),
      adjL.unit.app (F ⋙ L) =
      ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L).map
          ((colimConstAdj (J := Discrete ℕ) (C := CochainComplex (ModuleCat.{u} R) ℤ)).unit.app F) ≫
        (CatCommSq.iso (Functor.const (Discrete ℕ)) L
          ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) (Functor.const (Discrete ℕ))).hom.app
              (colim.obj F) ≫
        (Functor.const (Discrete ℕ)).map ((CatCommSq.iso colim
          ((Functor.whiskeringRight (Discrete ℕ) _ _).obj L) L colF).hom.app F) :=
    fun F => Adjunction.localization_unit_app _ _ _ _ _ _ _ _
  refine ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) ?_⟩
  refine IsColimit.ofIsoColimit (isColimitCoconeOfAdj adjL (F ⋙ L))
    (Cocone.ext (compIso.app F) (fun j => ?_))
  have hcancel : ∀ (X : DerivedCategory (ModuleCat.{u} R)) (g : X ⟶ (colim ⋙ L).obj F),
      g ≫ 𝟙 ((colim ⋙ L).obj F) ≫ compIso.inv.app F ≫ compIso.hom.app F = g := by
    intro X g
    rw [Category.id_comp, compIso.inv_hom_id_app, Category.comp_id]
  dsimp [coconeOfAdj]
  rw [adjL_unit_app]
  dsimp only [ccsq, ccsqC, CatCommSq.iso]
  simp only [Iso.symm_hom, colimConstAdj, Adjunction.mk'_unit, Functor.compConstIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.whiskerRight_app,
    Functor.whiskeringRight_obj_map, Functor.const_map_app, Functor.const_obj_obj,
    Functor.id_obj, NatTrans.comp_app, Category.assoc, Functor.comp_obj]
  exact hcancel _ _

end Stacks.MappingTelescope
