module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.Construction

/-!
# The cup product on the graded pieces through the shifts

The shift identifications of cohomology modules compose (`shiftCohomologyIsoR_add`), and the
canonical pairing of the graded pieces of the de Rham complex is the pairing of the sheaves of
forms in degree zero read through the shifts (`canonicalPairingModule_gradedPieceWedge`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The shift identifications of cohomology modules compose -/

section ShiftCompose

open CategoryTheory.MonoidalCategory
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (ringSheaf)

variable {S : RingedSpace.{u, u}}

/-- The algebra of `shiftCohomologyIsoR_add`, with every object and morphism a variable. -/
lemma shiftR_paste {V : Type*} [Category* V] {P Q R T U Q' Q'' P' : V} (x : P ⟶ Q) (S₁ : Q ⟶ R)
    (y : R ⟶ T) (S₂ : T ⟶ U) (y' : Q ⟶ Q') (S₁' : Q' ⟶ T) (z : Q' ⟶ Q'') (St : Q'' ⟶ U)
    (w : P ⟶ P') (v : P' ⟶ Q'') (n₁ : y' ≫ S₁' = S₁ ≫ y) (n₂ : S₁' ≫ S₂ = z ≫ St)
    (c : x ≫ y' ≫ z = w ≫ v) : (x ≫ S₁) ≫ (y ≫ S₂) = w ≫ (v ≫ St) := by
  rw [Category.assoc, ← Category.assoc S₁, ← n₁, Category.assoc, n₂, ← Category.assoc w,
    ← c]
  simp only [Category.assoc]

/-- `shiftCohomologyIso` is the identification `shiftHomologyIsoU` of the functor
`RΓ(S, -) ∘ Q` commuting with the shift. -/
theorem shiftCohomologyIso_eq_shiftHomologyIsoU
    (N : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) (n a a' : ℤ)
    (h : n + a = a') :
    (shiftCohomologyIso N n a a' h).hom =
      (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU
        (DerivedCategory.Q ⋙ baseSections S) N n a a' h).hom := by
  refine congrArg (· ≫ _) ?_
  change (DerivedCategory.homologyFunctor _ a).map ((baseSections S).map
      ((DerivedCategory.Q.commShiftIso n).hom.app N) ≫
        ((baseSections S).commShiftIso n).hom.app (DerivedCategory.Q.obj N)) = _
  exact congrArg (DerivedCategory.homologyFunctor _ a).map
    (Functor.commShiftIso_comp_hom_app DerivedCategory.Q (baseSections S) n N).symm

/-- **The identifications `Hᵃ(S, 𝒦^•[t]) ≅ Hᵃ⁺ᵗ(S, 𝒦^•)` compose**: shifting by `t₁` and then by
`t₂` is shifting by `t₂ + t₁`, through the composition of the shifts of `𝒦^•`. -/
theorem shiftCohomologyIsoR_add
    (M : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (t₁ t₂ t : ℤ) (ht : t₂ + t₁ = t) (a a' a'' : ℤ) (h₁ : t₁ + a = a') (h₂ : t₂ + a' = a'') :
    (shiftCohomologyIsoR (shiftR M t₂) t₁ a a' h₁).hom ≫ (shiftCohomologyIsoR M t₂ a' a'' h₂).hom =
      (DerivedCategory.homologyFunctor _ a).map ((baseSections S).map (DerivedCategory.Q.map
        ((shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u}
          (ringSheaf.{u, u, u} S.sheaf)) ℤ) t₂ t₁ t ht).inv.app M))) ≫
        (shiftCohomologyIsoR M t a a'' (by omega)).hom := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) a
  let Hq : ∀ {K L : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ},
      (K ⟶ L) → (H.obj ((baseSections S).obj (DerivedCategory.Q.obj K)) ⟶
        H.obj ((baseSections S).obj (DerivedCategory.Q.obj L))) :=
    fun f => H.map ((baseSections S).map (DerivedCategory.Q.map f))
  have n₁ := shiftCohomologyIso_naturality (S := S) (shiftBridge M t₂).hom t₁ a a' h₁
  have n₂ : (shiftCohomologyIso ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) t₂).obj M) t₁ a a' h₁).hom ≫
      (shiftCohomologyIso M t₂ a' a'' h₂).hom =
      Hq ((shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ)
        t₂ t₁ t ht).inv.app M) ≫ (shiftCohomologyIso M t a a'' (by omega)).hom :=
    (congrArg₂ (· ≫ ·) (shiftCohomologyIso_eq_shiftHomologyIsoU _ _ _ _ _)
      (shiftCohomologyIso_eq_shiftHomologyIsoU _ _ _ _ _)).trans
      ((Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_add _ _ t₁ t₂ t ht a a' a'' h₁
        h₂).trans (congrArg (_ ≫ ·) (shiftCohomologyIso_eq_shiftHomologyIsoU _ _ _ _ _).symm))
  have c : (shiftBridge (shiftR M t₂) t₁).hom ≫ (CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) t₁).map (shiftBridge M t₂).hom ≫
      (shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ)
        t₂ t₁ t ht).inv.app M =
      (shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u}
        (ringSheaf.{u, u, u} S.sheaf)) ℤ) t₂ t₁ t ht).inv.app M ≫ (shiftBridge M t).hom := by
    refine HomologicalComplex.Hom.ext (funext fun k => ?_)
    refine (Category.id_comp _).trans ((Category.id_comp _).trans ?_)
    refine Eq.trans ?_ (Category.comp_id _).symm
    exact (CochainComplex.shiftFunctorAdd'_inv_app_f' _ t₂ t₁ t ht k).trans
      (CochainComplex.shiftFunctorAdd'_inv_app_f' _ t₂ t₁ t ht k).symm
  have c' : Hq (shiftBridge (shiftR M t₂) t₁).hom ≫ Hq ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) t₁).map (shiftBridge M t₂).hom) ≫
      Hq ((shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ)
        t₂ t₁ t ht).inv.app M) =
      Hq ((shiftFunctorAdd' (CochainComplex (_root_.SheafOfModules.{u}
        (ringSheaf.{u, u, u} S.sheaf)) ℤ) t₂ t₁ t ht).inv.app M) ≫ Hq (shiftBridge M t).hom := by
    have hq : ∀ {K L L' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ}
        (f : K ⟶ L) (g : L ⟶ L'), Hq (f ≫ g) = Hq f ≫ Hq g := fun f g => by
      simp only [Hq, Functor.map_comp]
    exact (congrArg (_ ≫ ·) (hq _ _).symm).trans ((hq _ _).symm.trans
      ((congrArg (fun f => Hq f) c).trans (hq _ _)))
  exact shiftR_paste _ _ _ _ _ _ _ _ _ _ n₁ n₂ c'

/-- **The cup product and the shift of the second factor**, `totalCupPairing_shift₂` with the
degree of the shifted class a parameter. -/
theorem totalCupPairing_shift₂_of_eq
    (K M : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n) (t i j j' : ℤ)
    (hj : t + j = j')
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj K) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶
      cohomologyModule (DerivedCategory.Q.obj (shiftR M t)) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫
        totalCupPairing K (shiftR M t) i j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map
          ((baseSections S).map (DerivedCategory.Q.map
            (CochainComplex.mapBifunctorShift₂Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
          (ComplexShape.up ℤ)) t (i + j) (i + j') (by omega)).hom =
      (i * t).negOnePow • ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        (ξ ⊗ₘ (η ≫ (shiftCohomologyIsoR M t j j' hj).hom)) ≫ totalCupPairing K M i j') := by
  obtain rfl : j' = j + t := by omega
  exact totalCupPairing_shift₂ K M hK hM t i j ξ η

/-- **The cup product and the shift of the first factor**, `totalCupPairing_shift₁` with the
degree of the shifted class a parameter. -/
theorem totalCupPairing_shift₁_of_eq
    (K M : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n) (t i i' j : ℤ)
    (hi : t + i = i')
    (ξ : ModuleCat.of (baseRing S) (baseRing S) ⟶
      cohomologyModule (DerivedCategory.Q.obj (shiftR K t)) i)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (DerivedCategory.Q.obj M) j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (ξ ⊗ₘ η) ≫
        totalCupPairing (shiftR K t) M i j ≫ (DerivedCategory.homologyFunctor _ (i + j)).map
          ((baseSections S).map (DerivedCategory.Q.map
            (CochainComplex.mapBifunctorShift₁Iso K M (sheafTensor S.sheaf) t).hom)) ≫
        (shiftCohomologyIsoR (HomologicalComplex.mapBifunctor K M (sheafTensor S.sheaf)
          (ComplexShape.up ℤ)) t (i + j) (i' + j) (by omega)).hom =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((ξ ≫ (shiftCohomologyIsoR K t i i' hi).hom) ⊗ₘ η) ≫ totalCupPairing K M i' j := by
  obtain rfl : i' = i + t := by omega
  exact totalCupPairing_shift₁ K M hK hM t i j ξ η

end ShiftCompose

/-! ### The cup product on the graded pieces through the shifts -/

section GradedPieceShift

open CategoryTheory.MonoidalCategory
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite

/-- The algebra of `canonicalPairingModule_gradedPieceWedge`, with every object and morphism a
variable. -/
lemma gradedPiece_paste {V : Type*} [Category* V] [Preadditive V] {U U₂ P₁ P₂ P₃ Q₁ Q₂ Q₃ Q₄ Q₅
      R₁ R₂ R₃ R₄ W₁ W₂ W₃ Z₁ : V}
    (L : U ⟶ U₂) (X : U₂ ⟶ P₁) (T₁ : P₁ ⟶ P₂) (A₁ : P₂ ⟶ P₃) (A₂ : P₃ ⟶ Q₅) (Gt : Q₅ ⟶ Z₁)
    (N₁ : P₂ ⟶ Q₁) (N₂ : Q₁ ⟶ Q₂) (N₃ : Q₂ ⟶ Q₃) (N₄ : Q₃ ⟶ Q₄) (N₅ : Q₄ ⟶ Q₅)
    (Ga' : Q₄ ⟶ R₁) (Gb' : R₁ ⟶ Z₁) (Ga : Q₂ ⟶ R₂) (M₃ : R₂ ⟶ R₃) (M₄ : R₃ ⟶ R₁)
    (Gb : R₃ ⟶ R₄) (P₄ : R₄ ⟶ Z₁) (X' : U₂ ⟶ W₁) (T₂ : W₁ ⟶ Q₁) (X'' : U₂ ⟶ W₂) (T₃ : W₂ ⟶ R₂)
    (Y : U₂ ⟶ W₃) (T₄ : W₃ ⟶ R₄) (s : ℤˣ)
    (F₁ : A₁ ≫ A₂ = N₁ ≫ N₂ ≫ N₃ ≫ N₄ ≫ N₅) (F₂ : Ga' ≫ Gb' = N₅ ≫ Gt)
    (F₃ : N₃ ≫ N₄ ≫ Ga' = Ga ≫ M₃ ≫ M₄) (F₄ : M₄ ≫ Gb' = Gb ≫ P₄)
    (F₅ : L ≫ X ≫ T₁ ≫ N₁ = L ≫ X' ≫ T₂) (F₆ : L ≫ X' ≫ T₂ ≫ N₂ ≫ Ga = L ≫ X'' ≫ T₃)
    (F₇ : L ≫ X'' ≫ T₃ ≫ M₃ ≫ Gb = s • (L ≫ Y ≫ T₄)) (Pa : P₁ ⟶ P₃) (Pb : W₃ ⟶ Z₁)
    (Ia : P₃ ⟶ Z₁) (ca : Pa = T₁ ≫ A₁) (cb : Pb = T₄ ≫ P₄) (cI : Ia = A₂ ≫ Gt) :
    L ≫ X ≫ Pa ≫ Ia = s • (L ≫ Y ≫ Pb) := by
  subst ca cb cI
  simp only [Category.assoc]
  have F₂' : N₄ ≫ N₅ ≫ Gt = N₄ ≫ Ga' ≫ Gb' := by rw [F₂]
  rw [reassoc_of% F₁, F₂', reassoc_of% F₃, F₄]
  have e : L ≫ X ≫ T₁ ≫ N₁ ≫ N₂ ≫ Ga ≫ M₃ ≫ Gb ≫ P₄ =
      (L ≫ X'' ≫ T₃ ≫ M₃ ≫ Gb) ≫ P₄ := by
    have F₆' : L ≫ X'' ≫ T₃ ≫ M₃ ≫ Gb = L ≫ X' ≫ T₂ ≫ N₂ ≫ Ga ≫ M₃ ≫ Gb := by
      rw [← Category.assoc X'', ← Category.assoc L, ← F₆]
      simp only [Category.assoc]
    have F₅' : L ≫ X ≫ T₁ ≫ N₁ ≫ N₂ ≫ Ga ≫ M₃ ≫ Gb ≫ P₄ =
        L ≫ X' ≫ T₂ ≫ N₂ ≫ Ga ≫ M₃ ≫ Gb ≫ P₄ := by
      simp only [← Category.assoc] at F₅ ⊢
      rw [F₅]
    rw [F₅', F₆']
    simp only [Category.assoc]
  rw [e, F₇, Linear.units_smul_comp]
  simp only [Category.assoc]

/-- `Hⁿ(RΓ(X, -))` of a morphism of complexes of sheaves of `A`-modules. -/
abbrev cohomologyModuleMap (n : ℤ) {K L : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ}
    (f : K ⟶ L) :
    cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj K) n ⟶
      cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj L) n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
    ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map f))

/-- `cohomologyModuleMap n` sends a composite to the composite of the induced maps. -/
lemma cohomologyModuleMap_comp (n : ℤ) {K L M : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    cohomologyModuleMap n (f ≫ g) = cohomologyModuleMap n f ≫ cohomologyModuleMap n g :=
  (congrArg (fun x => (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A)))
      n).map ((baseSections (baseRingedSpace A)).map x)) (DerivedCategory.Q.map_comp f g)).trans
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A)))
      n).map ((baseSections (baseRingedSpace A)).map_comp _ _)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map_comp
        _ _))

/-- The cup product along a multiplication is the cup product followed by `RΓ` of the canonical
map to the total tensor complex and of the extended multiplication. -/
lemma canonicalPairingModule_eq {K L M : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (i j : ℤ) :
    canonicalPairingModule m i j =
      totalCupPairing (S := baseRingedSpace A) (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        i j ≫ cohomologyModuleMap (i + j) (multiplicationInt m) := by
  unfold canonicalPairingModule totalCupPairing
  rw [Category.assoc]
  exact congrArg (_ ≫ ·)
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A)))
      (i + j)).map ((baseSections (baseRingedSpace A)).map_comp _ _)).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A)))
        (i + j)).map_comp
        _ _))

/-- **`H^n(X, Ω^k[-k]) ≅ H^{n - k}(X, Ω^k[0])`**, on cohomology modules: the identification
`gradedPieceShiftIso` followed by the shift identification `shiftCohomologyIsoR`. -/
def gradedPieceModuleShiftIso (k : ℕ) (n i : ℤ) (h : -(k : ℤ) + n = i) :
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D k)) n ≅
      cohomologyModule (moduleDerived (A := A) (hodgeSingle B D k)) i :=
  (DerivedCategory.homologyFunctor _ n).mapIso ((baseSections (baseRingedSpace A)).mapIso
      (DerivedCategory.Q.mapIso (gradedPieceShiftIso B D k))) ≪≫
    shiftCohomologyIsoR (S := baseRingedSpace A) ((hodgeSingle B D k).extend embeddingUpNat)
      (-(k : ℤ)) n i h

/-- The forward map of `gradedPieceModuleShiftIso` is the map induced by `gradedPieceShiftIso`
followed by `shiftCohomologyIsoR`. -/
lemma gradedPieceModuleShiftIso_hom (k : ℕ) (n i : ℤ) (h : -(k : ℤ) + n = i) :
    (gradedPieceModuleShiftIso B D k n i h).hom =
      cohomologyModuleMap n (gradedPieceShiftIso B D k).hom ≫
        (shiftCohomologyIsoR (S := baseRingedSpace A) ((hodgeSingle B D k).extend embeddingUpNat)
          (-(k : ℤ)) n i h).hom :=
  Iso.trans_hom _ _

/-- The extension to `ℤ` of `hodgeSingle B D k` is strictly bounded below. -/
lemma exists_isStrictlyGE_hodgeSingle (k : ℕ) :
    ∃ n : ℤ, CochainComplex.IsStrictlyGE ((hodgeSingle B D k).extend embeddingUpNat) n :=
  ⟨0, inferInstance⟩

/-- On `H^{n + m}`, the map induced by the multiplication `gradedPieceWedge B D a b` followed by
`gradedPieceShiftIso B D (a + b)` is the composite of the maps induced by the tensor product of
the shift identifications, the shift isomorphisms `mapBifunctorShift₁Iso` and
`mapBifunctorShift₂Iso`, the shifted multiplication `hodgeSingleWedge B D a b`, and the inverse of
`shiftFunctorAdd'`. -/
lemma gradedPieceCup_step₁ (a b : ℕ) (n m : ℤ) :
    cohomologyModuleMap (n + m) (multiplicationInt (gradedPieceWedge B D a b)) ≫
      cohomologyModuleMap (n + m) (gradedPieceShiftIso B D (a + b)).hom =
      cohomologyModuleMap (n + m) (HomologicalComplex.mapBifunctorMap
        (gradedPieceShiftIso B D a).hom (gradedPieceShiftIso B D b).hom
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ)) ≫
        cohomologyModuleMap (n + m) (CochainComplex.mapBifunctorShift₁Iso
          ((hodgeSingle B D a).extend embeddingUpNat)
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat))
          (sheafTensor.{u, u, u, u, u} A) (-(a : ℤ))).hom ≫
          cohomologyModuleMap (n + m) ((CategoryTheory.shiftFunctor
          (CochainComplex (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(a : ℤ))).map
          (CochainComplex.mapBifunctorShift₂Iso ((hodgeSingle B D a).extend embeddingUpNat)
          ((hodgeSingle B D b).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
          (-(b : ℤ))).hom) ≫
        cohomologyModuleMap (n + m) ((CategoryTheory.shiftFunctor
          (CochainComplex (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(a : ℤ))).map
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(b : ℤ))).map (multiplicationInt (hodgeSingleWedge B D a b)))) ≫
          cohomologyModuleMap (n + m) ((shiftFunctorAdd'
          (CochainComplex (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(b : ℤ)) (-(a : ℤ))
          (-((a + b : ℕ) : ℤ)) (by push_cast; ring)).inv.app
          ((hodgeSingle B D (a + b)).extend embeddingUpNat)) := by
  rw [← cohomologyModuleMap_comp, ← cohomologyModuleMap_comp, ← cohomologyModuleMap_comp,
    ← cohomologyModuleMap_comp, ← cohomologyModuleMap_comp,
    multiplicationInt_gradedPieceWedge_shift]

/-- The shift identification `shiftCohomologyIsoR` by `-a` followed by the one by `-b` is the map
induced by the inverse of `shiftFunctorAdd'` followed by the shift identification by `-(a + b)`. -/
lemma gradedPieceCup_step₂ (a b : ℕ) (n m i j : ℤ) (hi : -(a : ℤ) + n = i) (hj : -(b : ℤ) + m = j) :
    (shiftCohomologyIsoR (S := baseRingedSpace A)
      ((CategoryTheory.shiftFunctor (CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
      (-(b : ℤ))).obj ((hodgeSingle B D (a + b)).extend embeddingUpNat)) (-(a : ℤ)) (n + m) (i + m)
      (by omega)).hom ≫
      (shiftCohomologyIsoR (S := baseRingedSpace A)
        ((hodgeSingle B D (a + b)).extend embeddingUpNat) (-(b : ℤ)) (i + m) (i + j)
        (by omega)).hom =
      cohomologyModuleMap (n + m) ((shiftFunctorAdd'
        (CochainComplex (_root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(b : ℤ)) (-(a : ℤ))
        (-((a + b : ℕ) : ℤ)) (by push_cast; ring)).inv.app
        ((hodgeSingle B D (a + b)).extend embeddingUpNat)) ≫
        (shiftCohomologyIsoR (S := baseRingedSpace A)
          ((hodgeSingle B D (a + b)).extend embeddingUpNat) (-((a + b : ℕ) : ℤ)) (n + m) (i + j)
          (by push_cast; omega)).hom :=
  shiftCohomologyIsoR_add (S := baseRingedSpace A) ((hodgeSingle B D (a + b)).extend embeddingUpNat)
      (-(a : ℤ)) (-(b : ℤ))
    (-((a + b : ℕ) : ℤ)) (by push_cast; ring) (n + m) (i + m) (i + j) (by omega) (by omega)

/-- Naturality of the shift identification `shiftCohomologyIsoR` by `-a` with respect to
`mapBifunctorShift₂Iso` followed by the `-b`-shifted multiplication `hodgeSingleWedge B D a b`. -/
lemma gradedPieceCup_step₃ (a b : ℕ) (n m i : ℤ) (hi : -(a : ℤ) + n = i) :
    cohomologyModuleMap (n + m) ((CategoryTheory.shiftFunctor
      (CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(a : ℤ))).map
      (CochainComplex.mapBifunctorShift₂Iso ((hodgeSingle B D a).extend embeddingUpNat)
      ((hodgeSingle B D b).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (-(b : ℤ))).hom) ≫
      cohomologyModuleMap (n + m) ((CategoryTheory.shiftFunctor
      (CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(a : ℤ))).map
      ((CategoryTheory.shiftFunctor (CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
      (-(b : ℤ))).map (multiplicationInt (hodgeSingleWedge B D a b)))) ≫
      (shiftCohomologyIsoR (S := baseRingedSpace A)
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(b : ℤ))).obj ((hodgeSingle B D (a + b)).extend embeddingUpNat)) (-(a : ℤ)) (n + m)
        (i + m) (by omega)).hom =
      (shiftCohomologyIsoR (S := baseRingedSpace A)
        (HomologicalComplex.mapBifunctor ((hodgeSingle B D a).extend embeddingUpNat)
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ)) (-(a : ℤ)) (n + m) (i + m) (by omega)).hom ≫
        cohomologyModuleMap (i + m) (CochainComplex.mapBifunctorShift₂Iso
        ((hodgeSingle B D a).extend embeddingUpNat) ((hodgeSingle B D b).extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (-(b : ℤ))).hom ≫
        cohomologyModuleMap (i + m) ((CategoryTheory.shiftFunctor
          (CochainComplex (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(b : ℤ))).map
          (multiplicationInt (hodgeSingleWedge B D a b))) := by
  have F₃ := shiftCohomologyIsoR_naturality (S := baseRingedSpace A)
    ((CochainComplex.mapBifunctorShift₂Iso ((hodgeSingle B D a).extend embeddingUpNat)
      ((hodgeSingle B D b).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (-(b : ℤ))).hom ≫
      ((CategoryTheory.shiftFunctor (CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
      (-(b : ℤ))).map (multiplicationInt (hodgeSingleWedge B D a b)))) (-(a : ℤ)) (n + m)
      (i + m) (by omega)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    ((cohomologyModuleMap_comp _ _ _).symm.trans (congrArg (cohomologyModuleMap _)
      (Functor.map_comp _ _ _).symm))).trans (F₃.trans (congrArg (_ ≫ ·)
        (cohomologyModuleMap_comp _ _ _))))

/-- Naturality of the shift identification `shiftCohomologyIsoR` by `-b` with respect to the
multiplication `hodgeSingleWedge B D a b`. -/
lemma gradedPieceCup_step₄ (a b : ℕ) (m i j : ℤ) (hj : -(b : ℤ) + m = j) :
    cohomologyModuleMap (i + m) ((CategoryTheory.shiftFunctor
      (CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (-(b : ℤ))).map
      (multiplicationInt (hodgeSingleWedge B D a b))) ≫
      (shiftCohomologyIsoR (S := baseRingedSpace A)
      ((hodgeSingle B D (a + b)).extend embeddingUpNat) (-(b : ℤ)) (i + m) (i + j) (by omega)).hom =
      (shiftCohomologyIsoR (S := baseRingedSpace A)
        (HomologicalComplex.mapBifunctor ((hodgeSingle B D a).extend embeddingUpNat)
        ((hodgeSingle B D b).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ)) (-(b : ℤ)) (i + m) (i + j) (by omega)).hom ≫
        cohomologyModuleMap (i + j) (multiplicationInt (hodgeSingleWedge B D a b)) :=
  shiftCohomologyIsoR_naturality (S := baseRingedSpace A)
      (multiplicationInt (hodgeSingleWedge B D a b)) (-(b : ℤ)) (i + m) (i + j) (by omega)

/-- Naturality of `totalCupPairing` with respect to the identifications `gradedPieceShiftIso B D a`
and `gradedPieceShiftIso B D b`, evaluated on classes `ξ` and `η`. -/
lemma gradedPieceCup_step₅ (a b : ℕ) (n m : ℤ)
    (ξ : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D a)) n)
    (η : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D b)) m) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
      (ξ ⊗ₘ η) ≫ totalCupPairing (S := baseRingedSpace A)
      ((deRhamGradedPiece B D a).extend embeddingUpNat)
      ((deRhamGradedPiece B D b).extend embeddingUpNat) (n) (m) ≫
      cohomologyModuleMap (n + m) (HomologicalComplex.mapBifunctorMap
        (gradedPieceShiftIso B D a).hom (gradedPieceShiftIso B D b).hom
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ)) =
      (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
        ((ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) ⊗ₘ
        (η ≫ cohomologyModuleMap (m) (gradedPieceShiftIso B D b).hom)) ≫
        totalCupPairing (S := baseRingedSpace A)
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(a : ℤ))).obj ((hodgeSingle B D a).extend embeddingUpNat))
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (n) (m) :=
  totalCupPairing_naturality' (S := baseRingedSpace A) (gradedPieceShiftIso B D a).hom
      (gradedPieceShiftIso B D b).hom n m ξ η

/-- The cup product followed by `mapBifunctorShift₁Iso` and the shift identification by `-a` is the
cup product after applying the shift identification by `-a` to the first class. -/
lemma gradedPieceCup_step₆ (a b : ℕ) (n m i : ℤ) (hi : -(a : ℤ) + n = i)
    (ξ : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D a)) n)
    (η : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D b)) m) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
      ((ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) ⊗ₘ
      (η ≫ cohomologyModuleMap (m) (gradedPieceShiftIso B D b).hom)) ≫
      totalCupPairing (S := baseRingedSpace A)
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(a : ℤ))).obj ((hodgeSingle B D a).extend embeddingUpNat))
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (n) (m) ≫
        cohomologyModuleMap (n + m) (CochainComplex.mapBifunctorShift₁Iso
        ((hodgeSingle B D a).extend embeddingUpNat)
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (sheafTensor.{u, u, u, u, u} A)
        (-(a : ℤ))).hom ≫
        (shiftCohomologyIsoR (S := baseRingedSpace A)
          (HomologicalComplex.mapBifunctor ((hodgeSingle B D a).extend embeddingUpNat)
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat))
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ)) (-(a : ℤ)) (n + m) (i + m)
          (by omega)).hom =
      (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
        (((ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) ≫
        (shiftCohomologyIsoR (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
        (-(a : ℤ)) (n) (i) hi).hom) ⊗ₘ (η ≫ cohomologyModuleMap (m)
        (gradedPieceShiftIso B D b).hom)) ≫
        totalCupPairing (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
          ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
          (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (i) (m) :=
  totalCupPairing_shift₁_of_eq (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
      ((CategoryTheory.shiftFunctor (CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
      (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat))
      (exists_isStrictlyGE_hodgeSingle B D a)
    (isStrictlyGE_shift (S := baseRingedSpace A) (exists_isStrictlyGE_hodgeSingle B D b) (-(b : ℤ)))
      (-(a : ℤ)) n i m
    hi (ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) (η ≫
      cohomologyModuleMap (m) (gradedPieceShiftIso B D b).hom)

/-- The cup product followed by `mapBifunctorShift₂Iso` and the shift identification by `-b` is
`(-1)^{i (-b)}` times the cup product after applying the shift identification by `-b` to the
second class. -/
lemma gradedPieceCup_step₇ (a b : ℕ) (n m i j : ℤ) (hi : -(a : ℤ) + n = i) (hj : -(b : ℤ) + m = j)
    (ξ : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D a)) n)
    (η : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D b)) m) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
      (((ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) ≫
      (shiftCohomologyIsoR (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
      (-(a : ℤ)) (n) (i) hi).hom) ⊗ₘ (η ≫ cohomologyModuleMap (m)
      (gradedPieceShiftIso B D b).hom)) ≫
      totalCupPairing (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
        ((CategoryTheory.shiftFunctor (CochainComplex
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
        (-(b : ℤ))).obj ((hodgeSingle B D b).extend embeddingUpNat)) (i) (m) ≫
        cohomologyModuleMap (i + m) (CochainComplex.mapBifunctorShift₂Iso
        ((hodgeSingle B D a).extend embeddingUpNat) ((hodgeSingle B D b).extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (-(b : ℤ))).hom ≫
        (shiftCohomologyIsoR (S := baseRingedSpace A)
          (HomologicalComplex.mapBifunctor ((hodgeSingle B D a).extend embeddingUpNat)
          ((hodgeSingle B D b).extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ)) (-(b : ℤ)) (i + m) (i + j) (by omega)).hom =
      (i * -(b : ℤ)).negOnePow • ((λ_ (ModuleCat.of (baseRing (baseRingedSpace A))
        (baseRing (baseRingedSpace A)))).inv ≫
        ((ξ ≫ (gradedPieceModuleShiftIso B D a n i hi).hom) ⊗ₘ
          (η ≫ (gradedPieceModuleShiftIso B D b m j hj).hom)) ≫
            totalCupPairing (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
            ((hodgeSingle B D b).extend embeddingUpNat) (i) (j)) := by
  have F₇ := totalCupPairing_shift₂_of_eq (S := baseRingedSpace A)
      ((hodgeSingle B D a).extend embeddingUpNat) ((hodgeSingle B D b).extend embeddingUpNat)
    (exists_isStrictlyGE_hodgeSingle B D a) (exists_isStrictlyGE_hodgeSingle B D b)
      (-(b : ℤ)) i m j hj
    ((ξ ≫ cohomologyModuleMap (n) (gradedPieceShiftIso B D a).hom) ≫
      (shiftCohomologyIsoR (S := baseRingedSpace A) ((hodgeSingle B D a).extend embeddingUpNat)
      (-(a : ℤ)) (n) (i) hi).hom) (η ≫ cohomologyModuleMap (m) (gradedPieceShiftIso B D b).hom)
  refine F₇.trans (congrArg (fun y => (i * -(b : ℤ)).negOnePow • ((λ_
      (ModuleCat.of (baseRing (baseRingedSpace A))
      (baseRing (baseRingedSpace A)))).inv ≫ y ≫ _)) ?_)
  exact congrArg₂ (· ⊗ₘ ·) (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- **The cup product on the graded pieces is the cup product on the sheaves of forms in degree
zero, up to the sign `(-1)^{(n - a) b}`**, on cohomology modules: for classes
`ξ ∈ H^n(X, Ω^a[-a])` and `η ∈ H^m(X, Ω^b[-b])`, moving the cup product along the multiplication
of the graded pieces to `H^{n + m - (a + b)}(X, Ω^{a + b}[0])` is `(-1)^{(n - a) b}` times the cup
product along the wedge product of `ξ` and `η` moved to `H^{n - a}(X, Ω^a[0])` and
`H^{m - b}(X, Ω^b[0])`.

The multiplications agree through the shifts (`multiplicationInt_gradedPieceWedge_shift`), and
the cup product commutes with the shift of the first factor and, up to `(-1)^{(n - a) b}`, with
the shift of the second (`totalCupPairing_shift₁_of_eq`, `totalCupPairing_shift₂_of_eq`). -/
theorem canonicalPairingModule_gradedPieceWedge (a b : ℕ) (n m i j : ℤ) (hi : -(a : ℤ) + n = i)
    (hj : -(b : ℤ) + m = j) (ξ : (ModuleCat.of (baseRing (baseRingedSpace A))
    (baseRing (baseRingedSpace A))) ⟶ cohomologyModule
    (moduleDerived (A := A) (deRhamGradedPiece B D a)) n)
    (η : (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A))) ⟶
    cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D b)) m) :
    (λ_ (ModuleCat.of (baseRing (baseRingedSpace A)) (baseRing (baseRingedSpace A)))).inv ≫
      (ξ ⊗ₘ η) ≫ canonicalPairingModule (gradedPieceWedge B D a b) n m ≫
        (gradedPieceModuleShiftIso B D (a + b) (n + m) (i + j) (by push_cast; omega)).hom =
      (i * -(b : ℤ)).negOnePow • ((λ_ (ModuleCat.of (baseRing (baseRingedSpace A))
        (baseRing (baseRingedSpace A)))).inv ≫
        ((ξ ≫ (gradedPieceModuleShiftIso B D a n i hi).hom) ⊗ₘ
          (η ≫ (gradedPieceModuleShiftIso B D b m j hj).hom)) ≫
        canonicalPairingModule (hodgeSingleWedge B D a b) i j) :=
  gradedPiece_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (gradedPieceCup_step₁ B D a b n m) (gradedPieceCup_step₂ B D a b n m i j hi hj)
    (gradedPieceCup_step₃ B D a b n m i hi) (gradedPieceCup_step₄ B D a b m i j hj)
    (gradedPieceCup_step₅ B D a b n m ξ η) (gradedPieceCup_step₆ B D a b n m i hi ξ η)
    (gradedPieceCup_step₇ B D a b n m i j hi hj ξ η) _ _ _
    (canonicalPairingModule_eq _ _ _) (canonicalPairingModule_eq _ _ _)
    (gradedPieceModuleShiftIso_hom B D (a + b) _ _ _)

/-- **`canonicalPairingModule_gradedPieceWedge` on elements.** -/
theorem canonicalPairingModule_gradedPieceWedge_apply (a b : ℕ) (n m i j : ℤ)
    (hi : -(a : ℤ) + n = i) (hj : -(b : ℤ) + m = j)
    (x : cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D a)) n)
    (y : cohomologyModule (moduleDerived (A := A) (deRhamGradedPiece B D b)) m) :
    (gradedPieceModuleShiftIso B D (a + b) (n + m) (i + j) (by push_cast; omega)).hom.hom
        ((canonicalPairingModule (gradedPieceWedge B D a b) n m).hom (x ⊗ₜ y)) =
      (i * -(b : ℤ)).negOnePow • (canonicalPairingModule (hodgeSingleWedge B D a b) i j).hom
        ((gradedPieceModuleShiftIso B D a n i hi).hom.hom x ⊗ₜ
          (gradedPieceModuleShiftIso B D b m j hj).hom.hom y) := by
  have h := congrArg (fun f => f.hom (1 : baseRing (baseRingedSpace A)))
    (canonicalPairingModule_gradedPieceWedge B D a b n m i j hi hj
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x))
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)))
  have e₂ : ∀ {M N M' N' : ModuleCat.{u} (baseRing (baseRingedSpace A))} (x : M) (y : N)
      (f : M ⟶ M') (g : N ⟶ N'),
      ((ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x) ≫ f) ⊗ₘ
        (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y) ≫ g)).hom
        ((λ_ (ModuleCat.of (baseRing (baseRingedSpace A))
          (baseRing (baseRingedSpace A)))).inv.hom 1)
        = f.hom x ⊗ₜ g.hom y := fun x y f g => by
    change f.hom (LinearMap.toSpanSingleton _ _ x 1) ⊗ₜ g.hom
      (LinearMap.toSpanSingleton _ _ y 1) = _
    simp
  have e₁ : ∀ {M N : ModuleCat.{u} (baseRing (baseRingedSpace A))} (x : M) (y : N),
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x) ⊗ₘ
        ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)).hom
        ((λ_ (ModuleCat.of (baseRing (baseRingedSpace A))
          (baseRing (baseRingedSpace A)))).inv.hom 1)
        = x ⊗ₜ y := fun x y => by
    simpa using e₂ x y (𝟙 _) (𝟙 _)
  have hu : ∀ {M N : ModuleCat.{u} (baseRing (baseRingedSpace A))} (e : ℤˣ) (f : M ⟶ N) (z : M),
      (e • f).hom z = e • f.hom z := fun e f z => by
    rw [Units.smul_def, Units.smul_def]
    rfl
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hu] at h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [e₁, e₂] at h
  exact h

end GradedPieceShift

end AlgebraicGeometry.SheafOfModules

end
