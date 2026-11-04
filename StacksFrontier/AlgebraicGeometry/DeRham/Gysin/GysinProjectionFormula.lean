module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupGysinEdge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRhamKoszul
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeTensorMatching
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map and the cup product: [Stacks, Tag 0G8C]

Let `π : X ⟶ S` be smooth and `i : Z ⟶ X` a Koszul regular closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c`. For `α ∈ H^q(X, Ω^p_{X/S})`,
`γ^{p,q}(α|_Z) = (-1)^{qc} α ∪ γ^{0,0}(1)` in `H^{q+c}(X, Ω^{p+c}_{X/S})`
(`gysinHodgeFormsMapOfConormalRank_hodgeRestriction`), where `γ^{a,b}` is the Gysin map of
Tag 0G8A and `∪` is the cup product of Cohomology, Section 0FKU, along the wedge product of forms.

The proof is the source's: `γ^{p,q}(α|_Z)` is the class of `α` multiplied by `γ^0(1)` along the
pairing of Tag 0G88, pushed through the Gysin edge morphism
(`gysinHodgeFormsMap_hodgeRestriction`), `γ^{0,0}(1)` is the class of `γ^0(1)` pushed through
the same edge (`gysinHodgeFormsMap_one`), and Cohomology, Tags 0G77 and 0G76 identify the first
with the cup product of `α` with the second (`cup_of_edgeTensorMatching`, along the edge
matching `edgeTensorMatching_conormalWedge`).

The sign `(-1)^{qc}` comes from the identification `H^q(X, A) ≅ H^{q+c}(RΓ(X, A[-c]))` used by
the bridge `hgroupModuleShiftIso`, which is sign-free, where the source uses the Koszul-signed
one. It appears at `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`; under the
Koszul-signed identification the formula is the source's `γ^{p,q}(α|_Z) = α ∪ γ^{0,0}(1)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open DerivedCategory
open scoped CategoryTheory.Prod

/-- A functor applied to a factorisation, at variables. -/
private lemma e2_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {a b b' d : C}
    {e : D} (r : a ⟶ b') (f : a ⟶ b) (g : b ⟶ b') (t : b' ⟶ d) (edge : F.obj d ⟶ e)
    (h : r = f ≫ g) : F.map r ≫ (F.map t ≫ edge) = F.map f ≫ (F.map (g ≫ t) ≫ edge) := by
  rw [h, F.map_comp, F.map_comp]
  simp only [Category.assoc]

/-- The algebra of `gysinHodgeFormsMap_hodgeRestriction`, at variables. -/
private lemma A1_chase {C : Type*} [Category* C] {a b b' e : C} (hf : a ⟶ b) (ci : b ⟶ b')
    (ch : b' ⟶ b) (g : b ⟶ e) (k : a ⟶ e) (hci : ci ≫ ch = 𝟙 b) (hk : k = hf ≫ g) :
    k = (hf ≫ ci) ≫ ch ≫ g := by
  rw [hk, Category.assoc, ← Category.assoc ci, hci, Category.id_comp]

/-- The algebra of `cohomologyMapOfSingleHom_comp_single`, at variables. -/
private lemma single_comp_chase {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {a b b' : D} {P Q Q' : C} (ia : a ⟶ H.obj P) (φ : P ⟶ Q) (sg : Q ⟶ Q') (jq : H.obj Q ⟶ b)
    (jq' : H.obj Q' ⟶ b') (hg : b ⟶ b') (h : H.map sg ≫ jq' = jq ≫ hg) :
    ia ≫ H.map (φ ≫ sg) ≫ jq' = (ia ≫ H.map φ ≫ jq) ≫ hg := by
  rw [H.map_comp, Category.assoc, h]
  simp only [Category.assoc]

/-- The algebra of `gysinHodgeFormsMap_one`, at variables. -/
private lemma hφ_chase {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {x y z : C}
    {w w' : D} (a : x ⟶ y) (b : y ⟶ z) (E₀ : F.obj y ⟶ w) (Ec : F.obj z ⟶ w') (s : w ⟶ w')
    (h : E₀ ≫ s = F.map b ≫ Ec) : F.map (a ≫ b) ≫ Ec = (F.map a ≫ E₀) ≫ s := by
  rw [F.map_comp, Category.assoc, Category.assoc, h]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

section Geometric

open AlgebraicGeometry.Scheme.Hom Stacks.Gysin
open Stacks.AlgebraicGeometry.ConormalEquations (ConormalRank)
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsKoszulRegularImmersion)

variable {Z X S : Scheme.{u}}

/-- The bilinear map underlying the morphism out of the tensor product sheaf induced by a
bilinear map is that bilinear map. -/
theorem tensorBilinear_ofBilinearSheaf {Y : RingedSpace.{u, u}}
    {A B C : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)}
    (β : SheafOfModules.BilinearMap A B C) :
    tensorBilinear (X := Y) (Stacks.RingedSpace.ofBilinearSheaf β) = β := by
  ext U x y
  exact Stacks.RingedSpace.ofBilinearSheaf_unit_tmul β U x y

/-- Right multiplication along the morphism induced by a bilinear map is right multiplication
along the bilinear map. -/
theorem rightMulTensor_ofBilinearSheaf {Y : RingedSpace.{u, u}}
    {A B C : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)}
    (β : SheafOfModules.BilinearMap A B C) (s : B.val.sections) :
    rightMulTensor (X := Y) (Stacks.RingedSpace.ofBilinearSheaf β) s =
      Stacks.Cohomology.rightMulHom β s := by
  unfold rightMulTensor
  rw [tensorBilinear_ofBilinearSheaf]

/-- **The cup product on Hodge cohomology of Cohomology, Section 0FKU over `𝒪_X`**: the base
`canonicalPairingModule` at the ring sheaf `𝒪_X`, along the wedge product of forms
`Ω^p_{X/S} ⊗ Ω^{p'}_{X/S} ⟶ Ω^{p+p'}_{X/S}`.

The cup product of Tag 0FM5, `AlgebraicGeometry.SheafOfModules.hodgeComponentCup`, is the same
pairing `canonicalPairingModule` over `π⁻¹𝒪_S` in place of `𝒪_X`. Tag 0G8C is stated for the
cup product of the ringed space `(X, 𝒪_X)`, which is this one, so no change-of-rings comparison
between the two is needed. -/
abbrev hodgeCupStructureSheaf (π : X ⟶ S) (p p' : ℕ) (i j : ℤ) :=
  canonicalPairingModule (A := X.sheaf)
    (singleTensorMult (X := X.toRingedSpace)
      (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ)
        (p' : ℤ)) 0 0 0 rfl) i j

/-- The restriction `α ↦ α|_Z` of a Hodge class to the closed subscheme. -/
def hodgeRestriction (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (p q : ℕ) :
    Hgroup X.ringCatSheaf ⊤ q (relativeDifferentialForms π (p : ℤ)) ⟶
      Hgroup Z.ringCatSheaf ⊤ q (relativeDifferentialForms (i ≫ π) (p : ℤ)) :=
  (Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)) ≫
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
      ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).inv

/-- **The Gysin map of Tag 0G8A on the restriction of a class, as a single map on cohomology**:
`γ^{p,q}(α|_Z)` is the map induced by right multiplication by `γ^0(1)` along the pairing of
Tag 0G88, followed by the Gysin edge morphism. -/
theorem gysinHodgeFormsMap_hodgeRestriction (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (hE : ConormalRank i c) (p q : ℕ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))))
    (α : Hgroup X.ringCatSheaf ⊤ q (relativeDifferentialForms π (p : ℤ))) :
    (Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank i π p hE hvan q).hom
        ((hodgeRestriction i π p q).hom α) =
      (cohomologyMapOfSingleHom X.toRingedSpace (relativeDifferentialForms π (p : ℤ))
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) c q
        ((DerivedCategory.singleFunctor _ (c : ℤ)).map (rightMulTensor (X := X.toRingedSpace)
          (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p))
          (conormalUnitClass i π
            (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
            (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE))) ≫
          formsGysinEdge i π c ((p : ℤ) + (c : ℤ)) hvan)).hom α := by
  have hR := formRestriction_comp_gysinHom i π p hE
    (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
    (fun _ f _ hV => eqToHom_app_gysinWedgeOn_one π f hV) _
    (fun a V hV x => Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app i π p hE a V hV x) _
    (fun a V hV x => Stacks.DeRham.CohomologicalGysin.conormalGysinHom_app i π 0 hE a V hV x)
  have e₁ : rightMulTensor (X := X.toRingedSpace)
      (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p))
      (conormalUnitClass i π
        (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
        (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE)) =
      formRestriction i π (p : ℤ) ≫ Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE :=
    (rightMulTensor_ofBilinearSheaf _ _).trans hR.symm
  have e₂ : (DerivedCategory.singleFunctor _ (c : ℤ)).map (rightMulTensor (X := X.toRingedSpace)
      (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p))
      (conormalUnitClass i π
        (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
        (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE))) ≫
        formsGysinEdge i π c ((p : ℤ) + (c : ℤ)) hvan =
      (DerivedCategory.singleFunctor _ (c : ℤ)).map (formRestriction i π (p : ℤ)) ≫
        ((DerivedCategory.singleFunctor _ (c : ℤ)).map
          ((Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE) ≫
            (Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso i π c p).hom) ≫
        supportedGysinEdge (Set.range i.base) i.isClosedEmbedding.isClosed_range (c : ℤ)
          ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
            (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hvan) :=
    e2_chase (DerivedCategory.singleFunctor X.Modules (c : ℤ)) _ _ _ _ _ e₁
  have hsplit := Stacks.DeRham.GysinProjection.cohomologyMapOfSingleHom_single_comp X.toRingedSpace
    (relativeDifferentialForms π (p : ℤ)) (pushforwardRelativeForms i π (p : ℤ))
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) c q (formRestriction i π (p : ℤ))
    ((DerivedCategory.singleFunctor _ (c : ℤ)).map
        ((Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE) ≫
          (Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso i π c p).hom) ≫
      supportedGysinEdge (Set.range i.base) i.isClosedEmbedding.isClosed_range (c : ℤ)
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hvan)
  have hnat := Stacks.DeRham.GysinProjection.comparisonIsNatural X.toRingedSpace c q
    (relativeDifferentialForms π (p : ℤ)) (pushforwardRelativeForms i π (p : ℤ))
    (formRestriction i π (p : ℤ))
  have hk := ((congrArg (cohomologyMapOfSingleHom X.toRingedSpace _ _ c q) e₂).trans hsplit).trans
    (congrArg (· ≫ _) hnat)
  unfold Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank
    Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMap
    Stacks.DeRham.CohomologicalGysin.gysinHodgeMap
    Stacks.DeRham.CohomologicalGysin.gysinHodgeMapOfClosed hodgeRestriction
  have hk' := A1_chase
    ((Hfunctor X.ringCatSheaf ⊤ q).map (formRestriction i π (p : ℤ)))
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
      ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).inv
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i q).app
      ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) p⟩).hom
    (gysinCohomologyMap (Set.range i.base) i.isClosedEmbedding.isClosed_range c
      (pushforwardRelativeForms i π (p : ℤ)) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) hvan
      ((Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π p hE) ≫
        (Stacks.DeRham.CohomologicalGysin.conormalGysinTargetIso i π c p).hom) q)
    _ (Iso.inv_hom_id _) hk
  exact (congrArg (fun φ => φ.hom α) hk').symm


/-- **A morphism of sheaves after a morphism `𝒜[-c] ⟶ ℱ[0]` acts on cohomology by the canonical
map.** -/
theorem cohomologyMapOfSingleHom_comp_single {Y : RingedSpace.{u, u}}
    (A F F' : _root_.SheafOfModules.{u} (structureSheafRing Y)) (c q : ℕ)
    (φ : (DerivedCategory.singleFunctor _ (c : ℤ)).obj A ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj F) (g : F ⟶ F') :
    cohomologyMapOfSingleHom Y A F' c q (φ ≫ (DerivedCategory.singleFunctor _ (0 : ℤ)).map g) =
      cohomologyMapOfSingleHom Y A F c q φ ≫
        (Hfunctor (structureSheafRing Y) ⊤ (q + c)).map g := by
  unfold cohomologyMapOfSingleHom
  rw [(derivedGlobalSections Y).map_comp]
  exact single_comp_chase _ _ _ _ _ _ _
    (Stacks.DeRham.CohomologicalGysin.cohomologyDerivedSingleIso_hom_naturality Y g 0
      ((q : ℤ) + (c : ℤ)) (q + c) (by omega))

/-- **The degree-zero class of a global section is natural.** -/
theorem Hfunctor_map_sectionClass {Y : RingedSpace.{u, u}}
    {G G' : _root_.SheafOfModules.{u} (structureSheafRing Y)} (ψ : G ⟶ G') (s : G.val.sections) :
    ((Hfunctor (structureSheafRing Y) ⊤ 0).map ψ).hom (sectionClass s) =
      sectionClass (SheafOfModules.sectionsMap ψ s) :=
  (congrArg (fun φ => φ.hom (s.eval (Opposite.op ⊤)))
    ((secF (structureSheafRing Y)
      (⊤ : TopologicalSpace.Opens Y.carrier)).toRightDerivedZero.naturality ψ)).symm

/-- A morphism of sheaves before a map `𝒜[-c] ⟶ ℱ[0]`, on the class of a global section. -/
theorem cohomologyMapOfSingleHom_single_comp_sectionClass {Y : RingedSpace.{u, u}}
    (A A' F : _root_.SheafOfModules.{u} (structureSheafRing Y)) (c : ℕ) (ψ : A ⟶ A')
    (φ : (DerivedCategory.singleFunctor _ (c : ℤ)).obj A' ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj F) (s : A.val.sections) :
    (cohomologyMapOfSingleHom Y A F c 0 ((DerivedCategory.singleFunctor _ (c : ℤ)).map ψ ≫ φ)).hom
        (sectionClass s) =
      (cohomologyMapOfSingleHom Y A' F c 0 φ).hom
        (sectionClass (SheafOfModules.sectionsMap ψ s)) := by
  rw [Stacks.DeRham.GysinProjection.cohomologyMapOfSingleHom_single_comp,
    Stacks.DeRham.GysinProjection.comparisonIsNatural]
  exact congrArg (cohomologyMapOfSingleHom Y A' F c 0 φ).hom (Hfunctor_map_sectionClass ψ s)

/-- **The Gysin edge morphisms of `Ω^d` and `Ω^{d'}` for `d = d'` agree through the canonical
identification.** -/
theorem formsGysinEdge_eqToHom (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c : ℕ)
    {d d' : ℤ} (h : d = d')
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π d))))
    (hvan' : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π d')))) :
    formsGysinEdge i π c d hvan ≫ (DerivedCategory.singleFunctor X.Modules ((0 : ℕ) : ℤ)).map
        (eqToHom (congrArg (relativeDifferentialForms π) h)) =
      (DerivedCategory.singleFunctor X.Modules (c : ℤ)).map
        ((Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor (isClosed_range_base i)
          (c : ℤ)).map (eqToHom (congrArg (relativeDifferentialForms π) h))) ≫
        formsGysinEdge i π c d' hvan' := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The unit class of `Z`, read on `X` through the affine-pushforward comparison of Tag 089W, is
the class of the restriction of `1` to `Z`. -/
theorem cohomologyPushforwardIso_oneFormCohomologyClass (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) :
    (((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i 0).app
        ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) 0⟩).hom).hom
        (Stacks.DeRham.GysinProjection.oneFormCohomologyClass (i ≫ π)) =
      sectionClass (X := X.toRingedSpace) (subschemeFormUnit i π) := by
  have h := congrArg (fun φ => (φ.app ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) 0⟩).hom
      ((relativeDifferentialFormsAlgebra (i ≫ π)).one.eval (Opposite.op ⊤)))
    (Stacks.AffineCohomologyResolution.cohomologyPushforwardIso_zero_hom i)
  refine h.trans ?_
  unfold sectionClass
  exact congrArg _ (subschemeFormUnit_eq_one i π ⊤).symm

/-- **`γ^{0,0}(1)` is the class of `γ^0(1)` pushed through the Gysin edge morphism.** -/
theorem gysinHodgeFormsMap_one (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) {c : ℕ} (hE : ConormalRank i c)
    (hvan₀ : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ))))))
    (hvanL : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π (c : ℤ))))) :
    ((Hfunctor X.ringCatSheaf ⊤ (0 + c)).map
        (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))).hom
      ((Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank i π 0 hE hvan₀ 0).hom
        (Stacks.DeRham.GysinProjection.oneFormCohomologyClass (i ≫ π))) =
    (cohomologyMapOfSingleHom X.toRingedSpace (conormalSource i π c)
        (relativeDifferentialForms π (c : ℤ)) c 0 (formsGysinEdge i π c (c : ℤ) hvanL)).hom
      (sectionClass (X := X.toRingedSpace) (conormalUnitClass i π
        (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
        (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE))) := by
  have hedge := formsGysinEdge_eqToHom i π c (natCast_zero_add c) hvan₀ hvanL
  have hcomp := cohomologyMapOfSingleHom_comp_single (Y := X.toRingedSpace)
    (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))
    (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ))) (relativeDifferentialForms π (c : ℤ))
    c 0 ((DerivedCategory.singleFunctor _ (c : ℤ)).map
        (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE) ≫
      formsGysinEdge i π c (((0 : ℕ) : ℤ) + (c : ℤ)) hvan₀)
    (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
  have hsc := cohomologyMapOfSingleHom_single_comp_sectionClass (Y := X.toRingedSpace)
    (pushforwardRelativeForms i π ((0 : ℕ) : ℤ)) (conormalSource i π c)
    (relativeDifferentialForms π (c : ℤ)) c
    (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE ≫
      gysinDegreeShift i π (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c))))
    (formsGysinEdge i π c (c : ℤ) hvanL) (subschemeFormUnit i π)
  have hone := cohomologyPushforwardIso_oneFormCohomologyClass i π
  have hφ : (DerivedCategory.singleFunctor _ (c : ℤ)).map
        (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE ≫
          gysinDegreeShift i π (eqToHom (congrArg (relativeDifferentialForms π)
            (natCast_zero_add c)))) ≫ formsGysinEdge i π c (c : ℤ) hvanL =
      ((DerivedCategory.singleFunctor _ (c : ℤ)).map
          (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE) ≫
        formsGysinEdge i π c (((0 : ℕ) : ℤ) + (c : ℤ)) hvan₀) ≫
        (DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).map
          (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c))) :=
    hφ_chase (DerivedCategory.singleFunctor X.Modules (c : ℤ)) _ _ _ _ _ hedge
  have key := (congrArg (cohomologyMapOfSingleHom X.toRingedSpace _ _ c 0) hφ).trans hcomp
  have hγ : Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank i π 0 hE hvan₀ 0 =
      ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i 0).app
        ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) 0⟩).hom ≫
        cohomologyMapOfSingleHom X.toRingedSpace (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))
          (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ))) c 0
          ((DerivedCategory.singleFunctor _ (c : ℤ)).map
              (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE) ≫
            formsGysinEdge i π c (((0 : ℕ) : ℤ) + (c : ℤ)) hvan₀) := by
    unfold Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank
      Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMap
      Stacks.DeRham.CohomologicalGysin.gysinHodgeMap
      Stacks.DeRham.CohomologicalGysin.gysinHodgeMapOfClosed gysinCohomologyMap formsGysinEdge
    exact congrArg (_ ≫ cohomologyMapOfSingleHom X.toRingedSpace _ _ c 0 ·)
      (Functor.map_comp_assoc (DerivedCategory.singleFunctor X.Modules (c : ℤ)) _ _ _)
  rw [hγ]
  exact (congrArg (fun x => ((Hfunctor X.ringCatSheaf ⊤ (0 + c)).map
      (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))).hom
      ((cohomologyMapOfSingleHom X.toRingedSpace (pushforwardRelativeForms i π ((0 : ℕ) : ℤ))
        (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (c : ℤ))) c 0
        ((DerivedCategory.singleFunctor _ (c : ℤ)).map
            (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE) ≫
          formsGysinEdge i π c (((0 : ℕ) : ℤ) + (c : ℤ)) hvan₀)).hom x)) hone).trans
    ((congrArg (fun φ => φ.hom (sectionClass (X := X.toRingedSpace) (subschemeFormUnit i π)))
      key.symm).trans hsc)

/-- **The Gysin map and the cup product** [Stacks, Tag 0G8C]. Let `π : X ⟶ S` be smooth and
`i : Z ⟶ X` a Koszul regular closed immersion of finite presentation whose conormal sheaf is
locally free of rank `c` (`hE`). For `α ∈ H^q(X, Ω^p_{X/S})`,
`γ^{p,q}(α|_Z) = (-1)^{qc} α ∪ γ^{0,0}(1)` in `H^{q+c}(X, Ω^{p+c}_{X/S})`.

Here `α|_Z` is `hodgeRestriction i π p q α`, `γ^{a,b}` is the Gysin map
`gysinHodgeFormsMapOfConormalRank` of Tag 0G8A, whose vanishing hypothesis is proved from the
smoothness of `π` and the Koszul regularity of `i` (`supportVanishing_relativeDifferentialForms`,
Tag 0G7P), `1 ∈ H^0(Z, Ω^0_{Z/S})` is `oneFormCohomologyClass`, and `∪` is the cup product
`hodgeCupStructureSheaf` of Cohomology, Section 0FKU. The cup product is stated on the modules
`H^m(RΓ(X, -))`, so both sides are read through the bridge `hgroupModuleShiftIso`, an
isomorphism.

The sign `(-1)^{qc}` comes from the identification `H^q(X, A) ≅ H^{q+c}(RΓ(X, A[-c]))` of the
bridge, which is sign-free, where the source uses the Koszul-signed identification; it appears
at `Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_shift₂`. Under the Koszul-signed
identification this is the source's formula `γ^{p,q}(α|_Z) = α ∪ γ^{0,0}(1)`. -/
@[stacks 0G8C "the full statement, at the source's hypotheses (pi smooth, i a Koszul regular \
closed immersion of finite presentation with conormal sheaf locally free of rank c), with the \
cup product of Cohomology Section 0FKU constructed and nothing assumed; stated with the sign: \
gamma^{p,q}(alpha|_Z) = (-1)^{qc} alpha cup gamma^{0,0}(1). The sign comes from this library's \
sign-free identification H^q(X, A) = H^{q+c}(R Gamma(X, A[-c])) of the bridge \
hgroupModuleShiftIso, where the source uses the Koszul-signed identification; it appears at \
totalCupPairing_shift₂. Under the Koszul-signed identification the formula is the source's \
gamma^{p,q}(alpha|_Z) = alpha cup gamma^{0,0}(1)"]
theorem gysinHodgeFormsMapOfConormalRank_hodgeRestriction (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) [Smooth π] {c : ℕ} (hE : ConormalRank i c)
    (hK : IsKoszulRegularImmersion i) (p q : ℕ)
    (α : Hgroup X.ringCatSheaf ⊤ q (relativeDifferentialForms π (p : ℤ))) :
    (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
        0 (q + c) ((q : ℤ) + (c : ℤ)) (by push_cast; ring)).hom
      ((Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank i π p hE
        (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
          i π hK c hE p) q).hom
        ((hodgeRestriction i π p q).hom α)) =
    ((q : ℤ) * (c : ℤ)).negOnePow •
      (hodgeCupStructureSheaf π p c q c).hom
        ((hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (p : ℤ)) 0 q q
          (by simp)).hom α ⊗ₜ
        (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (c : ℤ)) 0 (0 + c)
          c (by push_cast; ring)).hom
          ((Hfunctor X.ringCatSheaf ⊤ (0 + c)).map
            (eqToHom (congrArg (relativeDifferentialForms π) (by push_cast; ring)))
            ((Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank i π 0 hE
              (Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
                i π hK c hE 0) 0).hom
              (Stacks.DeRham.GysinProjection.oneFormCohomologyClass (i ≫ π))))) := by
  have hvanP := Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
    i π hK c hE p
  have hvan₀ := Stacks.DeRham.GysinCohomologyDeRhamKoszul.supportVanishing_relativeDifferentialForms
    i π hK c hE 0
  have hvanL : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π (c : ℤ)))) := by
    rwa [natCast_zero_add] at hvan₀
  have hA1 := gysinHodgeFormsMap_hodgeRestriction i π hE p q hvanP α
  have hA2 := gysinHodgeFormsMap_one i π hE hvan₀ hvanL
  have hC := cup_of_edgeTensorMatching (X := X.toRingedSpace) c q
    (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ) (c : ℤ))
    (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p))
    (formsGysinEdge i π c (c : ℤ) hvanL) (formsGysinEdge i π c ((p : ℤ) + (c : ℤ)) hvanP)
    (edgeTensorMatching_conormalWedge i π hE p hvanL hvanP)
    (conormalUnitClass i π
      (eqToHom (congrArg (relativeDifferentialForms π) (natCast_zero_add c)))
      (Stacks.DeRham.CohomologicalGysin.conormalGysinHom i π 0 hE)) α
  refine (congrArg _ hA1).trans (hC.trans ?_)
  exact congrArg (fun y => ((q : ℤ) * (c : ℤ)).negOnePow • (hodgeCupStructureSheaf π p c q c).hom
    ((hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (p : ℤ)) 0 q q
      (by simp)).hom α ⊗ₜ
      (hgroupModuleShiftIso (X := X.toRingedSpace) (relativeDifferentialForms π (c : ℤ)) 0 (0 + c)
        c (by push_cast; ring)).hom y)) hA2.symm

end Geometric

end StandardModel

end Stacks.DeRham.GysinCupHodge
