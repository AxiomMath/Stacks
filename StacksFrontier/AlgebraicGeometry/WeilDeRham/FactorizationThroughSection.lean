module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.CupWithDerivedClass
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ClassRepresentatives
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethSectionFactorization
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethSingleIso
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.UnitPullbackSections
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DiagonalGysinAmbient
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsDerivedSectionsAmplitude
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorPureTensors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatModulePullback
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage

/-!
# The cup product with a pulled back class factors through a section

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n = e + 1` over a Noetherian
ring, with `Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` an isomorphism and a section `σ`, and let `p₁`, `p₂` be
the projections of `W = X ×_A X`. For `θ ∈ Hⁿ(X, Ωᵃ_{X/A})` the cup product
`ε ↦ p₁^*θ ∪ ε` on `Hⁿ(W, p₂^*Ωᵇ_{X/A})` depends on `ε` only through its pullback along the section
`(σ ∘ f, id)` of `p₂`, and symmetrically with the two projections exchanged. This is the step of
the proof of [Stacks, Tag 0G8J] stated as `Stacks.WeilDeRham.CupFactorsThroughSection`.

The proof is the source's, through derived sections over the base. Write `θ = Hⁿ(t)(1)` for
`t : 𝒪_X[-n] ⟶ Ωᵃ[0]`, so that `p^*θ = Hⁿ(Lp^*t)(1)` up to the comparisons of the derived with the
ordinary pullback. After exchanging the two factors (graded commutativity of the cup product,
Cohomology, Lemma 0FP5), the cup product with the class of `Lp^*t` is the map on cohomology of
a morphism `q^*G[-n] ⟶ (q^*G ⊗ p^*F)[0]` factoring through `Lq^*G[0] ⊗^𝐋 Lp^*t`
(`Stacks.WeilDeRham.exists_cup_eq_cohomologyMapOfSingleHom`), and on derived sections over the
base the latter only sees the pullback along the section
(`Stacks.WeilDeRham.kunnethSectionFactorization`), which the pullback of classes computes
(`Stacks.WeilDeRham.unitPullbackCompat_single`).

## Main results

* `Stacks.WeilDeRham.canonicalPairingModule_eq_of_swap_eq`: the cup product with a fixed class
  on the left depends on the right factor only through the cup product on the other side.
* `Stacks.WeilDeRham.pullbackSections_hgroupSectionsOverBaseIso_eq_of_unitPullback_eq`: classes
  with equal pullbacks have equal pullbacks on derived sections over the base.
* `Stacks.WeilDeRham.cupFactorsThroughSection_of_isIso`: the factorization, under the two
  Künneth isomorphisms.
* `Stacks.WeilDeRham.cupFactorsThroughSection_fst`,
  `Stacks.WeilDeRham.cupFactorsThroughSection_snd`: the factorizations for the forms on `X ×_A X`.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction AlgebraicGeometry.Scheme.Hom
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCupHodge
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyCast)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace)
open scoped Stacks.StandardDerivedModel TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-! ### Swapping the factors of the cup product -/

section Swap

variable {X : RingedSpace.{u, u}}

/-- Three functors applied to an identity, on an element. -/
private lemma map_map_map_id_apply {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {R : Type u} [Ring R] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ ModuleCat.{u} R) (c : C)
    (z : H.obj (G.obj (F.obj c))) : (H.map (G.map (F.map (𝟙 c)))).hom z = z := by
  simp

/-- **The cup product with a fixed class on the left depends on the right factor only through the
cup product with it on the other side.** -/
theorem canonicalPairingModule_eq_of_swap_eq
    (P Q : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (i j : ℤ) (x : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat P 0)) i)
    (y y' : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat Q 0)) j)
    (h : (canonicalPairingModule (A := X.sheaf) (singleTensorMult (X := X)
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj Q).obj P)) 0 0 0 rfl) j i).hom (y ⊗ₜ x) =
      (canonicalPairingModule (A := X.sheaf) (singleTensorMult (X := X)
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj Q).obj P)) 0 0 0 rfl) j i).hom (y' ⊗ₜ x)) :
    (canonicalPairingModule (A := X.sheaf) (singleTensorMult (X := X)
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj P).obj Q)) 0 0 0 rfl) i j).hom (x ⊗ₜ y) =
      (canonicalPairingModule (A := X.sheaf) (singleTensorMult (X := X)
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj P).obj Q)) 0 0 0 rfl) i j).hom
        (x ⊗ₜ y') := by
  let β := ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.sheaf).app Q).hom.app P
  have hcv := AlgebraicGeometry.SheafOfModules.singleMultiplication_comm_value (A := X.sheaf)
    (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj P).obj Q)) β
    (fun U a b => (Stacks.SheafOfModules.Tensor.sheafTensorBraiding_hom_app_sheafifyUnit_tmul
      X.sheaf Q P U b a).symm)
  have hcx := AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding _ _ hcv
  have he := AlgebraicGeometry.SheafOfModules.canonicalPairingModule_comm _ _ hcx i j x
  have hm : singleTensorMult (X := X) (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj Q).obj P))
        0 0 0 rfl ≫ (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map β =
      ((tensorBifunctorNat (A := X.sheaf)).obj (singleNat Q 0)).map (𝟙 _) ≫
        ((tensorBifunctorNat (A := X.sheaf)).map (𝟙 (singleNat Q 0))).app (singleNat P 0) ≫
        AlgebraicGeometry.SheafOfModules.singleMultiplication (A := X.sheaf) β := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.id_comp, ← singleTensorMult_comp, Category.id_comp,
      singleTensorMult_zero_eq]
  have hid : ∀ (k : ℤ) (Z : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
      (z : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat Z 0)) k),
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace X.sheaf))) k).map
        ((baseSections (baseRingedSpace X.sheaf)).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap (𝟙 (singleNat Z 0))
          ComplexShape.embeddingUpNat)))).hom z = z := by
    intro k Z z
    rw [HomologicalComplex.extendMap_id]
    exact map_map_map_id_apply _ _ _ _ z
  have hn := AlgebraicGeometry.SheafOfModules.canonicalPairingModule_naturality (A := X.sheaf)
    (𝟙 (singleNat Q 0)) (𝟙 (singleNat P 0))
    (singleTensorMult (X := X) (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj Q).obj P)) 0 0 0 rfl)
    (AlgebraicGeometry.SheafOfModules.singleMultiplication (A := X.sheaf) β)
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map β) hm j i
  simp only [hid] at hn
  rw [← singleTensorMult_zero_eq] at he
  refine (he y).trans (Eq.trans ?_ (he y').symm)
  exact congrArg (fun t => (((i * j).negOnePow : ℤ)) • (cohomologyCast _ (add_comm j i)).hom t)
    ((hn y x).symm.trans ((congrArg _ h).trans (hn y' x)))

end Swap

/-! ### Classes with equal pullbacks have equal pullbacks on derived sections over the base -/

section PullbackSections

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase)
open Stacks.Cohomology.KunnethCupWithClass (pullbackSections)

variable {S V V' : Scheme.{u}} (c : V ⟶ S) (g : V' ⟶ V)

/-- **Two classes with the same pullback along `g` have the same pullback on derived sections
over the base**, for a flat module placed in degree `n`: the pullback map on cohomology is the
pullback on derived sections followed by the comparison `Lg^*(Q[-n]) ⟶ (g^*Q)[-n]`
(`Stacks.WeilDeRham.unitPullbackCompat_single`), which is invertible for flat `Q`. -/
theorem pullbackSections_hgroupSectionsOverBaseIso_eq_of_unitPullback_eq (Q : V.Modules)
    (hQ : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := V.toRingedSpace.sheaf) Q)
    (n : ℕ) (m : ℤ) (h : (n : ℤ) + (n : ℤ) = m)
    (ε ε' : Hgroup (structureSheafRing V.toRingedSpace) ⊤ n Q)
    (hε : (unitPullback g Q n).hom ε = (unitPullback g Q n).hom ε') :
    ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          (pullbackSections c.toLRSHom.toShHom g.toLRSHom.toShHom (g ≫ c).toLRSHom.toShHom rfl
            ((DerivedCategory.singleFunctor _ (n : ℤ)).obj Q)))).hom
        ((hgroupSectionsOverBaseIso c.toLRSHom.toShHom Q n n m h).hom ε) =
      ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          (pullbackSections c.toLRSHom.toShHom g.toLRSHom.toShHom (g ≫ c).toLRSHom.toShHom rfl
            ((DerivedCategory.singleFunctor _ (n : ℤ)).obj Q)))).hom
        ((hgroupSectionsOverBaseIso c.toLRSHom.toShHom Q n n m h).hom ε') := by
  have hp : ∀ x, (Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup
      (Stacks.DeRham.GysinCohomologyBaseChange.CohomologyPullbackComparison.canonical
        g.toLRSHom.toShHom) (n : ℤ) m n (by omega)
      ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app Q)).hom x =
      (unitPullback g Q n).hom x := fun x =>
    congrArg (fun t : Hgroup (structureSheafRing V.toRingedSpace) ⊤ n Q ⟶
        Hgroup (structureSheafRing V'.toRingedSpace) ⊤ n ((Scheme.Modules.pullback g).obj Q) =>
      t.hom x)
      (Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup_canonical_eq (G := g.toLRSHom.toShHom)
        (n : ℤ) m n (by omega)
        ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app Q))
  have e := unitPullbackCompat_single c (g ≫ c) g rfl Q n n m h
  have := isIso_singleDegreePullbackComparison g.toLRSHom.toShHom Q hQ (n : ℤ)
  refine (ConcreteCategory.bijective_of_isIso
    ((forget₂ (ModuleCat.{u} (baseRing S.toRingedSpace)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map
          ((sectionsOverBase (g ≫ c).toLRSHom.toShHom).map
            (singleDegreePullbackComparison g.toLRSHom.toShHom Q (n : ℤ)))))).1 ?_
  exact (e ε).symm.trans ((congrArg (hgroupSectionsOverBaseIso (g ≫ c).toLRSHom.toShHom
    ((Scheme.Modules.pullback g).obj Q) n n m h).hom
      ((hp ε).trans (hε.trans (hp ε').symm))).trans (e ε'))

end PullbackSections

/-! ### Reading cohomology maps and pullbacks through the bridges -/

section Bridges

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase)

/-- **Two classes identified by a morphism on derived sections over the base are identified by
the map it induces on cohomology**: `hgroupSectionsOverBaseIso` is injective and carries the map
on cohomology of `φ : A[-k] ⟶ F[0]` to the map `φ` induces on derived sections over the base. -/
theorem cohomologyMapOfSingleHom_eq_of_sectionsOverBase_eq {S V : RingedSpace.{u, u}}
    (c : V ⟶ S) (A F : SheafOfModules.{u} (structureSheafRing V)) (k q : ℕ) (m : ℤ)
    (h : (q : ℤ) + (k : ℤ) = m)
    (φ : (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V)) (k : ℤ)).obj A ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing V))
        ((0 : ℕ) : ℤ)).obj F)
    (x x' : Hgroup (structureSheafRing V) ⊤ q A)
    (hx : ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase c).map φ))).hom
        ((hgroupSectionsOverBaseIso c A k q m h).hom x) =
      ((forget₂ (ModuleCat.{u} (baseRing S)) AddCommGrpCat.{u}).map
        ((DerivedCategory.homologyFunctor _ m).map ((sectionsOverBase c).map φ))).hom
        ((hgroupSectionsOverBaseIso c A k q m h).hom x')) :
    cohomologyMapOfSingleHom V A F k q φ x = cohomologyMapOfSingleHom V A F k q φ x' := by
  have h₀ : ((q + k : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = m := by push_cast; omega
  refine (ConcreteCategory.bijective_of_isIso
    (hgroupSectionsOverBaseIso c F 0 (q + k) m h₀).hom).1 ?_
  rw [hgroupSectionsOverBaseIso_cohomologyMapOfSingleHom c A F k q m h h₀ φ x,
    hgroupSectionsOverBaseIso_cohomologyMapOfSingleHom c A F k q m h h₀ φ x', hx]

/-- The pullback of classes read through `hgroupModuleShiftIso` does not depend on the spelling
of the degree. -/
theorem hgroupModuleShiftIso_unitPullback_eq {V V' : Scheme.{u}} (g : V' ⟶ V) (F : V.Modules)
    (k k' : ℕ) (m : ℤ) (hk : k = k') (h : (k : ℤ) + ((0 : ℕ) : ℤ) = m)
    (h' : (k' : ℤ) + ((0 : ℕ) : ℤ) = m)
    (a : Hgroup (structureSheafRing V.toRingedSpace) ⊤ k F)
    (b : Hgroup (structureSheafRing V.toRingedSpace) ⊤ k' F)
    (hab : (hgroupModuleShiftIso (X := V.toRingedSpace) F 0 k m h).hom a =
      (hgroupModuleShiftIso (X := V.toRingedSpace) F 0 k' m h').hom b) :
    (hgroupModuleShiftIso (X := V'.toRingedSpace) ((Scheme.Modules.pullback g).obj F) 0 k m h).hom
        ((unitPullback g F k).hom a) =
      (hgroupModuleShiftIso (X := V'.toRingedSpace) ((Scheme.Modules.pullback g).obj F) 0 k' m
        h').hom ((unitPullback g F k').hom b) := by
  subst hk
  obtain rfl : a = b := (ConcreteCategory.bijective_of_isIso
    (hgroupModuleShiftIso (X := V.toRingedSpace) F 0 k m h).hom).1 hab
  rfl

end Bridges

/-! ### The factorization through the section -/

section Factorization

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase kunnethGlobalMapCanonical)
open Stacks.Cohomology.KunnethCupWithClass (pullbackSections)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

/-- Conjugating the second variable of a bifunctor by an isomorphism of the first, at
variables. -/
private lemma bifunctor_map_eq_conj {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C ⥤ D ⥤ E) {A B : C} (ι : A ≅ B) {Y Z : D} (w : Y ⟶ Z) :
    (T.obj B).map w = (T.map ι.inv).app Y ≫ (T.obj A).map w ≫ (T.map ι.hom).app Z := by
  rw [(T.map ι.hom).naturality w, ← NatTrans.comp_app_assoc, ← T.map_comp, Iso.inv_hom_id,
    T.map_id, NatTrans.id_app, Category.id_comp]

/-- Inserting an isomorphism of the first variable of a bifunctor into a composite through its
second variable, at variables. -/
lemma comp_bifunctor_map_eq {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C ⥤ D ⥤ E) {A B : C} (ι : A ≅ B) {Y₀ Y₁ Y₂ Y₃ : D} {P Z : E}
    (a : P ⟶ (T.obj B).obj Y₀) (u : Y₀ ⟶ Y₁) (w : Y₁ ⟶ Y₂) (v : Y₂ ⟶ Y₃)
    (b : (T.obj B).obj Y₃ ⟶ Z) :
    a ≫ (T.obj B).map (u ≫ w ≫ v) ≫ b =
      (a ≫ (T.obj B).map u ≫ (T.map ι.inv).app Y₁) ≫ (T.obj A).map w ≫
        ((T.map ι.hom).app Y₂ ≫ (T.obj B).map v ≫ b) := by
  rw [Functor.map_comp, Functor.map_comp, bifunctor_map_eq_conj T ι w]
  simp only [Category.assoc]

/-- Two elements identified by the middle factor of a threefold factorization are identified by
the composite, after a functor, at variables. -/
private lemma map_apply_eq_of_eq_comp {D : Type*} [Category* D] (Φ : D ⥤ AddCommGrpCat.{u})
    {a b c d : D} {φ : a ⟶ d} (x : a ⟶ b) (w : b ⟶ c) (y : c ⟶ d) (hφ : φ = x ≫ w ≫ y)
    {z z' : Φ.obj a} (h : (Φ.map w).hom ((Φ.map x).hom z) = (Φ.map w).hom ((Φ.map x).hom z')) :
    (Φ.map φ).hom z = (Φ.map φ).hom z' := by
  subst hφ
  simp only [Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, h]

/-- Moving the equality of two elements under `H(pK)` across a naturality square
`Sa(α) ≫ pK' = pK ≫ u`, at variables. -/
private lemma naturality_apply_eq {C D : Type*} [Category* C] [Category* D] {R : Type u} [Ring R]
    (Sa : D ⥤ C) (H : C ⥤ ModuleCat.{u} R) {K K' : D} {Z Z' : C} (α : K ⟶ K')
    (pK : Sa.obj K ⟶ Z) (pK' : Sa.obj K' ⟶ Z') (u : Z ⟶ Z') (hnat : Sa.map α ≫ pK' = pK ≫ u)
    (z z' : H.obj (Sa.obj K))
    (hz : ((H ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map pK).hom z =
      ((H ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map pK).hom z') :
    (H.map pK').hom (((Sa ⋙ H ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map α).hom z) =
      (H.map pK').hom (((Sa ⋙ H ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map α).hom z') := by
  have e : ∀ w, (H.map pK').hom
      (((Sa ⋙ H ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map α).hom w) =
      (H.map u).hom ((H.map pK).hom w) := fun w => by
    have := congrArg (fun g => (H.map g).hom w) hnat
    simpa using this
  rw [e, e]
  exact congrArg (H.map u).hom hz

variable {A : Type u} [CommRing A] {X W : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The cup product with a pulled back class factors through the section**, under the two
Künneth isomorphisms of `Stacks.WeilDeRham.kunnethSectionFactorization`: for `q, p : W ⟶ X` over
`Spec A` and `j : X ⟶ W` with `j ≫ q = 𝟙` and `j ≫ p = f ≫ σ`, a flat `G` and `F` with
`RΓ(X, F)` in degrees `≤ n`, the cup product `p^*θ ∪ ε` depends on `ε ∈ Hⁿ(W, q^*G)` only through
`j^*ε`. -/
theorem cupFactorsThroughSection_of_isIso [IsProper f] [Smooth f] [IsIso f.appTop]
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (p q : W ⟶ X) (hqp : q ≫ f = p ≫ f)
    (j : X ⟶ W) (hjq : j ≫ q = 𝟙 X) (hjp : j ≫ p = f ≫ σ) (F G : X.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.toRingedSpace.sheaf) G)
    (n : ℕ)
    [((sectionsOverBase f.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj F)).IsLE (n : ℤ)]
    (hκW : IsIso (kunnethGlobalMapCanonical f.toLRSHom.toShHom f.toLRSHom.toShHom
      q.toLRSHom.toShHom p.toLRSHom.toShHom (q ≫ f).toLRSHom.toShHom rfl
      (by rw [hqp]; rfl) ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj G)
      (unitInDegree X n)))
    (hκX : IsIso (kunnethGlobalMapCanonical f.toLRSHom.toShHom
      (𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)).toLRSHom.toShHom
      (𝟙 X : X ⟶ X).toLRSHom.toShHom f.toLRSHom.toShHom
      (𝟙 X ≫ f).toLRSHom.toShHom rfl (by rw [Category.id_comp]; exact Category.comp_id _)
      ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj G)
      (unitInDegree (Spec (.of A)) n))) :
    CupFactorsThroughSection p q j F G n := by
  intro θ ε ε' hjε
  have hK := kunnethSectionFactorization f σ hσ q p hqp j hjq hjp _ n hκW hκX
  obtain ⟨t, ht⟩ := classRepresented F n θ
  have hx := hgroupModuleShiftIso_unitPullback_eq p F n (0 + n) n (Nat.zero_add n).symm
    (by simp) (by simp) θ _ ht
  rw [pullbackRepresented p F n t] at hx
  unfold pullbackCup
  refine canonicalPairingModule_eq_of_swap_eq (X := W.toRingedSpace)
    ((Scheme.Modules.pullback p).obj F) ((Scheme.Modules.pullback q).obj G) n n _ _ _ ?_
  rw [hx]
  obtain ⟨s, α, β, hcup⟩ := exists_cup_eq_cohomologyMapOfSingleHom (X := W.toRingedSpace)
    ((Scheme.Modules.pullback q).obj G) ((Scheme.Modules.pullback p).obj F) n
  rw [hcup, hcup]
  have := isIso_singleDegreePullbackComparison q.toLRSHom.toShHom G hG ((0 : ℕ) : ℤ)
  have hQ := isFlat_modulePullback q.toLRSHom.toShHom G hG
  have hC := pullbackSections_hgroupSectionsOverBaseIso_eq_of_unitPullback_eq (q ≫ f) j
    ((Scheme.Modules.pullback q).obj G) hQ n ((n : ℤ) + (n : ℤ)) rfl ε ε' hjε
  congr 2
  let ι := asIso (singleDegreePullbackComparison q.toLRSHom.toShHom G ((0 : ℕ) : ℤ)) ≪≫
    (moduleDerivedSingleIso (X := W.toRingedSpace) ((Scheme.Modules.pullback q).obj G) 0).symm
  apply cohomologyMapOfSingleHom_eq_of_sectionsOverBase_eq (q ≫ f).toLRSHom.toShHom _ _ n n
    ((n : ℤ) + (n : ℤ)) rfl
  refine map_apply_eq_of_eq_comp (sectionsOverBase (q ≫ f).toLRSHom.toShHom ⋙
      DerivedCategory.homologyFunctor _ ((n : ℤ) + (n : ℤ)) ⋙
      forget₂ (ModuleCat.{u} (baseRing (Spec (.of A)).toRingedSpace)) AddCommGrpCat.{u}) _ _ _
    (comp_bifunctor_map_eq (derivedTensorProductFunctor
      (SheafedSpace.sheaf (baseRingedSpace (SheafedSpace.sheaf W.toRingedSpace)))) ι α _ _ _ β) ?_
  refine hK _ t _ _ _ ?_
  exact naturality_apply_eq (sectionsOverBase (q ≫ f).toLRSHom.toShHom)
    (DerivedCategory.homologyFunctor _ ((n : ℤ) + (n : ℤ))) _ _ _ _
    (pullbackSections_naturality (q ≫ f).toLRSHom.toShHom j.toLRSHom.toShHom
      (j ≫ q ≫ f).toLRSHom.toShHom rfl _) _ _ hC

end Factorization

/-! ### The two factorizations of the proof of [Stacks, Tag 0G8J] -/

section Forms

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `RΓ(X, Ωᵃ_{X/A})` lies in degrees `≤ n` for `f` smooth of relative dimension `n`, at the
spelling of `DerivedCategory.singleFunctor`. -/
theorem isLE_sectionsOverBase_singleFunctor_forms [IsNoetherianRing A] [IsProper f] (n : ℕ)
    [SmoothOfRelativeDimension n f] (a : ℕ) :
    ((sectionsOverBase f.toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj
        (relativeDifferentialForms f (a : ℤ)))).IsLE (n : ℤ) := by
  have h := AlgebraicGeometry.TopDegreeDifferential.isLE_sectionsOverBase_forms f n a
  exact ⟨(DerivedCategory.TStructure.t.le (n : ℤ)).prop_of_iso
    ((sectionsOverBase f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm) h.le⟩

/-- The Künneth isomorphism through `X = X ×_S S` at the forms and the structure sheaf. -/
theorem isIso_kunnethGlobalMapCanonical_id_forms [IsProper f] [Smooth f] (b n : ℕ) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical f.toLRSHom.toShHom
      (𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)).toLRSHom.toShHom
      (𝟙 X : X ⟶ X).toLRSHom.toShHom f.toLRSHom.toShHom
      (𝟙 X ≫ f).toLRSHom.toShHom rfl (by rw [Category.id_comp]; exact Category.comp_id _)
      ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj (relativeDifferentialForms f (b : ℤ)))
      (unitInDegree (Spec (.of A)) n)) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f b
  exact kunnethSingleIso f (𝟙 _) (relativeDifferentialForms f (b : ℤ))
    (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (isFlatOver_unit_of_flat (𝟙 (Spec (.of A)))) ((0 : ℕ) : ℤ) (n : ℤ) (𝟙 X) f
    (asIso (pullback.fst f (𝟙 _))).symm (by simp) (by simp)
    (by rw [Category.id_comp, Category.comp_id])

/-- The Künneth isomorphism through `X ×_S X` at the forms and the structure sheaf, for
projections exhibiting the fibre product up to an automorphism. -/
theorem isIso_kunnethGlobalMapCanonical_forms [IsProper f] [Smooth f] (b n : ℕ)
    (q p : pullback f f ⟶ X) (hqp : q ≫ f = p ≫ f) (e : pullback f f ≅ pullback f f)
    (he₁ : e.hom ≫ pullback.fst f f = q) (he₂ : e.hom ≫ pullback.snd f f = p) :
    IsIso (Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical f.toLRSHom.toShHom
      f.toLRSHom.toShHom q.toLRSHom.toShHom p.toLRSHom.toShHom (q ≫ f).toLRSHom.toShHom rfl
      (by rw [hqp]; rfl)
      ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).obj (relativeDifferentialForms f (b : ℤ)))
      (unitInDegree X n)) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f b
  exact kunnethSingleIso f f (relativeDifferentialForms f (b : ℤ))
    (SheafOfModules.unit X.ringCatSheaf) (isFlatOver_unit_of_flat f) ((0 : ℕ) : ℤ) (n : ℤ) q p
    e he₁ he₂ hqp

variable [IsNoetherianRing A] [IsProper f] (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]
  [IsIso f.appTop] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- **The cup product with `p₁^*θ` factors through the section `(σ ∘ f, id)` of `p₂`**: for
`θ ∈ Hⁿ(X, Ωᵃ_{X/A})` and `ε, ε' ∈ Hⁿ(X ×_A X, p₂^*Ωᵇ_{X/A})`, `n = e + 1`, with
`(σ ∘ f, id)^*ε = (σ ∘ f, id)^*ε'`, `p₁^*θ ∪ ε = p₁^*θ ∪ ε'`. -/
theorem cupFactorsThroughSection_fst (a b : ℕ) :
    CupFactorsThroughSection (pullback.fst f f) (pullback.snd f f) (sectionFst f σ hσ)
      (relativeDifferentialForms f (a : ℤ)) (relativeDifferentialForms f (b : ℤ)) (e + 1) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have := isLE_sectionsOverBase_singleFunctor_forms f (e + 1) a
  exact cupFactorsThroughSection_of_isIso f σ hσ (pullback.fst f f) (pullback.snd f f)
    pullback.condition.symm (sectionFst f σ hσ) (pullback.lift_snd _ _ _)
    (pullback.lift_fst _ _ _) _ _
    (AlgebraicGeometry.ProperSmoothDeRham.isFlat_relativeDifferentialForms f b) (e + 1)
    (isIso_kunnethGlobalMapCanonical_forms f b (e + 1) _ _ pullback.condition.symm
      (pullbackSymmetry f f) (pullbackSymmetry_hom_comp_fst f f)
      (pullbackSymmetry_hom_comp_snd f f))
    (isIso_kunnethGlobalMapCanonical_id_forms f b (e + 1))

/-- **The cup product with `p₂^*θ` factors through the section `(id, σ ∘ f)` of `p₁`**: for
`θ ∈ Hⁿ(X, Ωᵃ_{X/A})` and `ε, ε' ∈ Hⁿ(X ×_A X, p₁^*Ωᵇ_{X/A})`, `n = e + 1`, with
`(id, σ ∘ f)^*ε = (id, σ ∘ f)^*ε'`, `p₂^*θ ∪ ε = p₂^*θ ∪ ε'`. -/
theorem cupFactorsThroughSection_snd (a b : ℕ) :
    CupFactorsThroughSection (pullback.snd f f) (pullback.fst f f) (sectionSnd f σ hσ)
      (relativeDifferentialForms f (a : ℤ)) (relativeDifferentialForms f (b : ℤ)) (e + 1) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (e + 1) f
  have := isLE_sectionsOverBase_singleFunctor_forms f (e + 1) a
  exact cupFactorsThroughSection_of_isIso f σ hσ (pullback.snd f f) (pullback.fst f f)
    pullback.condition (sectionSnd f σ hσ) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) _ _
    (AlgebraicGeometry.ProperSmoothDeRham.isFlat_relativeDifferentialForms f b) (e + 1)
    (isIso_kunnethGlobalMapCanonical_forms f b (e + 1) _ _ pullback.condition
      (Iso.refl _) (Category.id_comp _) (Category.id_comp _))
    (isIso_kunnethGlobalMapCanonical_id_forms f b (e + 1))

end Forms

end Stacks.WeilDeRham

end
