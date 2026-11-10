module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionProperDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionStepInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTowerLevelTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` and its Frobenius do not depend on the compactification

Let `X` be separated of finite type over a finite field `k`, let `k̄` be an extension of `k`, and
let `g : j ⟶ l` be a morphism of compactifications of `X` over `k`, so that the ambient morphism
`ḡ : X̄_j ⟶ X̄_l` is proper with `ḡ ∘ j = l`. For a bounded below complex `K` of sheaves of
`Λ`-modules on `X_étale` each of whose terms is annihilated by a positive integer,

`RΓ_c(X_k̄, K)` through `j` `≅` `RΓ_c(X_k̄, K)` through `l`,

naturally in `K` and compatibly with the canonical geometric Frobenius: `l_! ≅ ḡ_* j_!`
(Tags 0F79 and 0F51, `refinementIso`), the restrictions to `X̄_{j,k̄}` of the sheaves `j_! Kⁿ` are
the extensions by zero `(j_k̄)_!(Kⁿ|_{X_k̄})`, which are acyclic for the proper `ḡ_k̄`
(`isZero_rightDerived_etaleModuleDirectImage_extensionByZero`, the vanishing behind
[Stacks, Tag 0F7G]), and `RΓ(X̄_{j,k̄}, -) = RΓ(X̄_{l,k̄}, ḡ_{k̄,*} -)` on them
Frobenius-equivariantly (`frobeniusRestrictionProperDirectImageIso`).

The levels of an ℓ-adic sheaf are killed by `ℓⁿ⁺¹`, so passing to the inverse limit and
tensoring with `ℚ_ℓ` gives an isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l`
intertwining the geometric Frobenius endomorphisms. Since any two compactifications are dominated
by a third (the compactifications form a cofiltered category, [Stacks, Tag 0ATU]), the
characteristic polynomial of the Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` does not depend on the
compactification: this is [Stacks, Tag 0F7I] read on the Frobenius, and the proposition
`LAdicSheaf.CompactSupportCompactificationIndependenceInput` of the induction step of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). The case of a smooth curve is
`LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isCurve`.

## Main definitions

* `compactSupportFrobeniusCohomologyHomIso`: `RΓ_c(X_k̄, K)` through `j` and through `l`, for a
  morphism `g : j ⟶ l` of compactifications.
* `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso`: the same for
  `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.

## Main results

* `compactSupportFrobeniusCohomologyHomIso_hom_frobenius`,
  `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_frobenius`: the
  isomorphisms intertwine the geometric Frobenius.
* `LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification`: the
  characteristic polynomial of the Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is the same for any two
  compactifications; this proves `LAdicSheaf.CompactSupportCompactificationIndependenceInput`.

## Implementation notes

The objects are those of the standard model of the derived category, in which
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` is defined.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### Torsion -/

section Torsion

variable {Λ : Type} [Ring Λ] {Z : Scheme.{u}}

/-- A sheaf of `Λ`-modules annihilated by a positive integer is torsion. -/
theorem isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero (G : EtaleModules.{u, 0} Λ Z) (m : ℕ)
    (hm : 0 < m) (h : m • 𝟙 G = 0) : IsTorsionEtaleModule.{u, 0} Λ Z G := by
  intro U x
  refine ⟨⊤, Z.smallEtaleTopology.top_mem U, fun V g _ => ⟨m, hm, ?_⟩⟩
  generalize G.obj.map g.op x = y
  have h' : ((m • 𝟙 G).hom.app (op V)).hom y = 0 := by
    rw [h]
    rfl
  have e : ((m • 𝟙 G).hom.app (op V)).hom y = m • y := rfl
  exact e.symm.trans h'

end Torsion

/-! ### `RΓ_c` along a morphism of compactifications -/

section Hom

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) {j l : CompactificationOf (Over.mk f)} (g : j ⟶ l)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The ambient proper morphism `ḡ : X̄_j ⟶ X̄_l` of a morphism of compactifications, as a
morphism over `k`. -/
abbrev compactificationHomOver : Over.mk j.toBase ⟶ Over.mk l.toBase :=
  Over.homMk (CompactificationOf.Hom.map g) (CompactificationOf.map_comp_toBase g)

/-- The ambient morphism `ḡ : X̄_j ⟶ X̄_l` of a morphism of compactifications is proper. -/
instance isProper_compactificationHomOver_left : IsProper (compactificationHomOver f g).left :=
  (inferInstance : IsProper (CompactificationOf.Hom.map g))

omit [Fintype k] in
/-- The base change `ḡ_k̄` of the ambient morphism extends the identity of `X_k̄`. -/
lemma compactificationFieldBaseChangeImmersion_comp_fieldBaseChangeMap :
    compactificationFieldBaseChangeImmersion f j kbar ≫
        fieldBaseChangeMap (compactificationHomOver f g) kbar =
      compactificationFieldBaseChangeImmersion f l kbar := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, fieldBaseChangeMap, pullback.lift_fst, Over.homMk_left]
    change compactificationFieldBaseChangeImmersion f j kbar ≫
        pullback.fst j.toBase (specAlgebraMap k kbar) ≫ CompactificationOf.Hom.map g =
      compactificationFieldBaseChangeImmersion f l kbar ≫
        pullback.fst l.toBase (specAlgebraMap k kbar)
    rw [compactificationFieldBaseChange_immersion_comp_fst_assoc,
      compactificationFieldBaseChange_immersion_comp_fst, CompactificationOf.immersion_comp_map]
  · simp only [Category.assoc, fieldBaseChangeMap, pullback.lift_snd, Category.comp_id]
    change compactificationFieldBaseChangeImmersion f j kbar ≫
        pullback.snd j.toBase (specAlgebraMap k kbar) =
      compactificationFieldBaseChangeImmersion f l kbar ≫
        pullback.snd l.toBase (specAlgebraMap k kbar)
    rw [compactificationFieldBaseChange_immersion_comp_snd,
      compactificationFieldBaseChange_immersion_comp_snd]

omit [Fintype k] in
/-- **The restrictions to `X̄_{j,k̄}` of the terms of `j_! K` are acyclic for `ḡ_k̄`**, when every
term of `K` is annihilated by a positive integer: the restriction of `j_! Kⁿ` is
`(j_k̄)_!(Kⁿ|_{X_k̄})` ([Stacks, Tag 03S6]), a torsion sheaf extended by zero along the open
immersion `j_k̄` with `ḡ_k̄ ∘ j_k̄ = l_k̄`, so its higher direct images along the proper `ḡ_k̄`
vanish. -/
@[sga "4½ Arcata 4.5.2" "special case"]
theorem fieldBaseChangeDirectImageAcyclic_extensionByZero
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K.obj.X n) = 0) :
    FieldBaseChangeDirectImageAcyclic Λ (compactificationHomOver f g) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K) := by
  intro n
  obtain ⟨m, hm, hmK⟩ := hK n
  have := isProper_fieldBaseChangeMap (compactificationHomOver f g) kbar
  let F := (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
    (K.obj.X n)
  have hF : IsTorsionEtaleModule.{u, 0} Λ _ F := by
    refine isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero F m hm ?_
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hmK, Functor.map_zero]
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  exact (isZero_rightDerived_etaleModuleDirectImage_extensionByZero Λ
    (compactificationFieldBaseChangeImmersion_comp_fieldBaseChangeMap f g kbar) F hF p hp).of_iso
      (((etaleModuleDirectImage.{u, 0} Λ
        (fieldBaseChangeMap (compactificationHomOver f g) kbar)).rightDerived p).mapIso
          ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app
            (K.obj.X n)).symm)

/-- `ḡ_* j_! K ≅ l_! K`, degreewise on a bounded below complex (Tags 0F79 and 0F51). -/
def refinementPlusIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDirectImage.{u, 0} Λ (compactificationHomOver f g).left).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ l.immersion).mapCochainComplexPlus.obj K :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex (refinementIso Λ g).symm _).app K.obj)

/-- **`RΓ_c(X_k̄, K)` through `j` is `RΓ_c(X_k̄, K)` through `l`**, for a morphism `g : j ⟶ l` of
compactifications of `X` over `k` and a complex `K` whose terms are annihilated by positive
integers. -/
def compactSupportFrobeniusCohomologyHomIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K.obj.X n) = 0) :
    compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K ≅
      compactSupportFrobeniusCohomology.{u, 0} Λ f l kbar K :=
  frobeniusRestrictionProperDirectImageIso Λ (compactificationHomOver f g) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)
      (fieldBaseChangeDirectImageAcyclic_extensionByZero Λ f g kbar K hK) ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk l.toBase).hom (specAlgebraMap k kbar))).mapIso
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk l.toBase) kbar).mapIso
          (refinementPlusIso Λ f g K)))

omit [Fintype k] in
/-- **The identification is natural in `K`.** -/
theorem compactSupportFrobeniusCohomologyHomIso_hom_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (x : K ⟶ K')
    (hK : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K.obj.X n) = 0)
    (hK' : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K'.obj.X n) = 0) :
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map x ≫
        (compactSupportFrobeniusCohomologyHomIso Λ f g kbar K' hK').hom =
      (compactSupportFrobeniusCohomologyHomIso Λ f g kbar K hK).hom ≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ f l kbar).map x := by
  have h₁ := frobeniusRestrictionProperDirectImageIso_hom_naturality Λ
    (compactificationHomOver f g) kbar
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map x)
    (fieldBaseChangeDirectImageAcyclic_extensionByZero Λ f g kbar K hK)
    (fieldBaseChangeDirectImageAcyclic_extensionByZero Λ f g kbar K' hK')
  have h₂ : (etaleModuleDirectImage.{u, 0} Λ
        (compactificationHomOver f g).left).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map x) ≫
        (refinementPlusIso Λ f g K').hom =
      (refinementPlusIso Λ f g K).hom ≫
        (etaleModuleExtensionByZero.{u, 0} Λ l.immersion).mapCochainComplexPlus.map x := by
    ext n : 2
    exact (refinementIso Λ g).inv.naturality (x.hom.f n)
  have h₃ := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk l.toBase).hom (specAlgebraMap k kbar))).map
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk l.toBase) kbar).map t))) h₂
  simp only [Functor.map_comp] at h₃
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁ h₃

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(X_k̄, K)` through `j` `≅` through `l` commutes with the canonical
geometric Frobenius.** -/
theorem compactSupportFrobeniusCohomologyHomIso_hom_frobenius
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : ∀ n, ∃ m : ℕ, 0 < m ∧ m • 𝟙 (K.obj.X n) = 0) :
    canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K ≫
        (compactSupportFrobeniusCohomologyHomIso Λ f g kbar K hK).hom =
      (compactSupportFrobeniusCohomologyHomIso Λ f g kbar K hK).hom ≫
        canonicalCompactSupportFrobenius.{u, 0} Λ f l kbar p q hcard K := by
  have h₁ := frobeniusRestrictionProperDirectImageIso_hom_frobenius Λ
    (compactificationHomOver f g) kbar p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)
    (fieldBaseChangeDirectImageAcyclic_extensionByZero Λ f g kbar K hK)
  have h₂ := frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk l.toBase) kbar p q
    hcard (refinementPlusIso Λ f g K).hom
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁ h₂.symm

end Hom

/-! ### Sheaves placed in degree zero -/

section Single

variable {Λ : Type} [Ring Λ] {X : Scheme.{u}}

/-- If `m` kills a sheaf, it kills every term of the sheaf placed in degree zero. -/
theorem nsmul_id_sheafSingleComplex_X (G : EtaleModules.{u, 0} Λ X) (m : ℕ) (h : m • 𝟙 G = 0)
    (n : ℤ) : m • 𝟙 (((sheafSingleComplex Λ).obj G).obj.X n) = 0 := by
  by_cases hn : n = 0
  · subst hn
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
    change m • 𝟙 (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).X 0) = 0
    have : m • 𝟙 (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).X 0) =
        e.hom ≫ (m • 𝟙 G) ≫ e.inv := by
      rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, e.hom_inv_id]
    rw [this, h, zero_comp, comp_zero]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_src _ _

end Single

/-! ### ℓ-adic sheaves -/

section LAdic

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  {j l : CompactificationOf (Over.mk f)} (g : j ⟶ l) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (F : LAdicSheaf B X ℓ)

/-- Every term of a level of the tower placed in degree zero is killed by a positive integer. -/
theorem LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower (n : ℕᵒᵖ) (d : ℤ) :
    ∃ m : ℕ, 0 < m ∧ m • 𝟙 (((sheafSingleComplex ℤ_[ℓ]).obj
      ((LAdicSheaf.padicTower B X ℓ F).obj n)).obj.X d) = 0 :=
  ⟨ℓ ^ (n.unop + 1), pow_pos (Fact.out : ℓ.Prime).pos _,
    nsmul_id_sheafSingleComplex_X _ _ (LAdicSheaf.pow_nsmul_id_padicTower_obj B ℓ F n.unop) d⟩

/-- **`Hⁱ_c` of the tower of levels through `j` and through `l`**, for a morphism `g : j ⟶ l` of
compactifications. -/
def LAdicSheaf.padicTowerCompactSupportHomIso (i : ℤ) :
    LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i ≅
      LAdicSheaf.padicTower B X ℓ F ⋙ compactSupportSheafCohomology ℤ_[ℓ] f l kbar i :=
  NatIso.ofComponents
    (fun n => (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
      (compactSupportFrobeniusCohomologyHomIso ℤ_[ℓ] f g kbar
        ((sheafSingleComplex ℤ_[ℓ]).obj ((LAdicSheaf.padicTower B X ℓ F).obj n))
        (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ F n)))
    (fun {n n'} φ =>
      (Functor.map_comp _ _ _).symm.trans
        ((congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
          (compactSupportFrobeniusCohomologyHomIso_hom_naturality ℤ_[ℓ] f g kbar
            ((sheafSingleComplex ℤ_[ℓ]).map ((LAdicSheaf.padicTower B X ℓ F).map φ))
            (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ F n)
            (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ F n'))).trans
          (Functor.map_comp _ _ _)))

/-- **The inverse systems `n ↦ Hⁱ_c(X_k̄, Fₙ)` through `j` and through `l` are isomorphic.** -/
def LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f l kbar F i :=
  (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).symm ≪≫
    LAdicSheaf.padicTowerCompactSupportHomIso B ℓ f g kbar F i ≪≫
    LAdicSheaf.padicTowerCohomologyIso B X ℓ f l kbar F i

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` is `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `l`**, for a morphism
`g : j ⟶ l` of compactifications. -/
def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f l kbar F i :=
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso B ℓ f g kbar F i)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The isomorphism of the towers intertwines the geometric Frobenius through `j` and `l`. -/
theorem LAdicSheaf.padicTowerCompactSupportHomIso_hom_frobenius (i : ℤ) :
    Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) ≫
      (LAdicSheaf.padicTowerCompactSupportHomIso B ℓ f g kbar F i).hom =
    (LAdicSheaf.padicTowerCompactSupportHomIso B ℓ f g kbar F i).hom ≫
      Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] f l kbar p q hcard i) := by
  refine NatTrans.ext (funext fun n => ?_)
  exact (Functor.map_comp _ _ _).symm.trans
    ((congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
      (compactSupportFrobeniusCohomologyHomIso_hom_frobenius ℤ_[ℓ] f g kbar p q hcard
        ((sheafSingleComplex ℤ_[ℓ]).obj ((LAdicSheaf.padicTower B X ℓ F).obj n))
        (LAdicSheaf.exists_nsmul_id_sheafSingleComplex_padicTower B ℓ F n))).trans
      (Functor.map_comp _ _ _))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The isomorphism of inverse systems intertwines the geometric Frobenius through `j` and `l`. -/
theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso_hom_frobenius (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso B ℓ f g kbar F i).hom =
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso B ℓ f g kbar F i).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f l kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f l kbar p q hcard) := by
  have hj := LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f j kbar p q hcard F i
  have hl := LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ f l kbar p q hcard F i
  have hT := LAdicSheaf.padicTowerCompactSupportHomIso_hom_frobenius B ℓ f g kbar F p q hcard i
  have hj' : LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).inv =
      (LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).inv ≫
        Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
          (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) := by
    rw [Iso.comp_inv_eq, Category.assoc, hj, Iso.inv_hom_id_assoc]
  simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hj', reassoc_of% hT, hl]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≅` through `l` intertwines the geometric
Frobenius.** -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_frobenius (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F i).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F i).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f l kbar p q hcard F i := by
  have h := congrArg (rationalLim.{u + 1} (ℓ := ℓ)).map
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemHomIso_hom_frobenius B ℓ f g kbar F p q
      hcard i)
  simp only [Functor.map_comp] at h
  exact h

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include g in
/-- `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `l` is finite dimensional when it is through `j`. -/
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_hom
    [Finite k] (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f l kbar F i) :=
  have := Fintype.ofFinite k
  LinearEquiv.finiteDimensional
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F i).toLinearEquiv

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include g in
/-- `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` is finite dimensional when it is through `l`. -/
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_hom'
    [Finite k] (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f l kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  have := Fintype.ofFinite k
  LinearEquiv.finiteDimensional
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F
      i).symm.toLinearEquiv

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include g in
/-- **Along a morphism of compactifications, the Frobenius on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` keeps its
characteristic polynomial.** -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_hom (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f l kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f l kbar p q hcard F
        i).hom.charpoly := by
  set E := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar F i
  rw [← E.toLinearEquiv.charpoly_conj]
  congr 1
  ext v
  have h := congrArg (fun t => t.hom (E.toLinearEquiv.symm v))
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_frobenius B ℓ f g kbar F
      p q hcard i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact h.trans (congrArg _ (E.toLinearEquiv.apply_symm_apply v))

end LAdic

/-! ### Independence of the compactification -/

section Independence

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` and its Frobenius do not depend on the compactification**
([Stacks, Tag 0F7I], read on the Frobenius): for a separated scheme of finite type over a finite
field and two compactifications `j₁`, `j₂` of it, the geometric Frobenius endomorphisms of
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` computed through `j₁` and through `j₂` have the same characteristic
polynomial. Both are compared with a third compactification mapping to each
([Stacks, Tag 0ATU]), along which `RΓ_c` and its Frobenius are unchanged. -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification
    (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₁ kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₂ kbar p q hcard F
        i).hom.charpoly := by
  let m := IsCofiltered.min j₁ j₂
  have : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f m kbar F i) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_hom' B ℓ f
      (IsCofiltered.minToLeft j₁ j₂) kbar F i
  rw [← LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_hom B ℓ f
      (IsCofiltered.minToLeft j₁ j₂) kbar F p q hcard i,
    LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_hom B ℓ f
      (IsCofiltered.minToRight j₁ j₂) kbar F p q hcard i]

/-- The input of the induction step of Weil II on the independence of the compactification
holds: `LAdicSheaf.CompactSupportCompactificationIndependenceInput`. -/
theorem LAdicSheaf.compactSupportCompactificationIndependenceInput :
    LAdicSheaf.CompactSupportCompactificationIndependenceInput B ℓ := by
  intro k _ _ kbar _ _ _ p q _ _ hcard _ X _ f _ _ _ j₁ j₂ F i _ _
  exact LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactification B
    ℓ f kbar p q hcard j₁ j₂ F i

end Independence

end Stacks.EtaleCohomology

end
