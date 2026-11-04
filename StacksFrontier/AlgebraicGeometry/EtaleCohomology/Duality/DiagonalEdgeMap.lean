module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalKummerClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EdgeMapBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower

/-!
# The edge map of the Kummer class of the diagonal

Let `f : X ⟶ S` be separated and smooth of relative dimension one, `pr₂ : X ×_S X ⟶ X` the
second projection and `c_Δ ∈ H²(X ×_S X, μ_n)` the Kummer class of the diagonal
(`Stacks.Kummer.diagonalKummerClass`). Read as a morphism `ℤ[0] ⟶ μ_n[2]` in the derived category
of abelian sheaves of `X ×_S X`, its adjoint along `pr₂⁻¹ ⊣ Rpr₂_*` is a morphism

`ψ : ℤ_X[0] ⟶ Rpr₂_*(μ_n[2])`

(`Stacks.EtaleCohomology.diagonalEdge`), whose `H⁰` is a section of `R²pr₂_* μ_n`. This file shows
that, when `f` is moreover proper with geometrically irreducible fibres, the restriction of `ψ`
to every geometric point `x̄ : Spec Ω ⟶ X`, `Ω` algebraically closed, generates: `H⁰(x̄⁻¹ψ)` is a
generator of order `n` of the group of morphisms `H⁰(x̄⁻¹ℤ[0]) ⟶ H⁰(x̄⁻¹Rpr₂_*(μ_n[2]))`
(`Stacks.EtaleCohomology.isZModGenerator_homologyMap_diagonalEdge`).

The proof: the base change map along `x̄` is the mate of the comparison of composite inverse
images (`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`), so `x̄⁻¹ψ` followed
by it is the adjoint of the restriction of `c_Δ` to the geometric fibre `C` of `pr₂`
(`CategoryTheory.map_homEquiv_comp_mateEquiv_app`); the base change map is invertible by proper
base change (Tag 0DDE); over `Spec Ω` the constant sheaf `ℤ` is projective, so morphisms out of
`ℤ[0]` are morphisms of `H⁰`; and the restriction of `c_Δ` to `C` generates `H²(C, μ_n) ≅ ℤ/n`,
its trace being `1` (`Stacks.Kummer.smoothProperCurveTrace_diagonalKummerClass`). Every
identification used is an additive bijection, so being a generator of order `n` passes along.

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which the
base change map of Tag 0A2A and its mate description are stated.

## Main definitions

* `Stacks.EtaleCohomology.IsZModGenerator`: `m` generates a cyclic group of order `n`.
* `Stacks.EtaleCohomology.diagonalKummerShiftedHom`, `Stacks.EtaleCohomology.diagonalEdge`.

## Main results

* `Stacks.EtaleCohomology.diagonalEdge_comp_baseChange`: the edge map under base change.
* `Stacks.EtaleCohomology.isZModGenerator_homologyMap_diagonalEdge`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- An element `m` of an abelian group `M` **generates a cyclic group of order `n`** when there is
an additive isomorphism `M ≃+ ℤ/n` sending `m` to `1`. -/
def IsZModGenerator (n : ℕ) {M : Type*} [AddCommGroup M] (m : M) : Prop :=
  ∃ e : M ≃+ ZMod n, e m = 1

/-- The image of a generator of a cyclic group of order `n` under an additive isomorphism is a
generator of a cyclic group of order `n`. -/
theorem IsZModGenerator.map {n : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] {m : M}
    (h : IsZModGenerator n m) (φ : M ≃+ M') : IsZModGenerator n (φ m) := by
  obtain ⟨e, he⟩ := h
  exact ⟨φ.symm.trans e, by simpa using he⟩

/-- Pre- and postcomposition with isomorphisms, as an additive bijection of morphism groups. -/
def isoHomAddEquiv {C : Type*} [Category* C] [Preadditive C] {P P' Q Q' : C} (I₁ : P' ≅ P)
    (I₂ : Q ≅ Q') : (P ⟶ Q) ≃+ (P' ⟶ Q') where
  toFun g := I₁.hom ≫ g ≫ I₂.hom
  invFun g := I₁.inv ≫ g ≫ I₂.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g g' := by simp

/-- The constant sheaf `ℤ` on the small étale site. -/
abbrev intSheaf (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- The inverse image of the constant sheaf `ℤ[0]` is `ℤ[0]`. -/
def inverseImageSingleIntSheafIso {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (etaleAbelianDerivedInverseImage.{u, 0} g).obj
        ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (intSheaf Y) :=
  ((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategorySingleFunctor 0).app (intSheaf X) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).app (AddCommGrpCat.of (ULift ℤ)))

section Edge

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {n : ℕ} (hn0 : n ≠ 0) (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤)))

/-- **The Kummer class of the diagonal as a morphism of the derived category**,
`pr₂⁻¹(ℤ_X[0]) ≅ ℤ[0] ⟶ μ_n[2]` on `X ×_S X`. -/
def diagonalKummerShiftedHom :
    (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd f f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧ :=
  (inverseImageSingleIntSheafIso (pullback.snd f f)).hom ≫
    (Stacks.Kummer.diagonalKummerClass f hn0 hY).hom

/-- **The edge map of the Kummer class of the diagonal**: the adjoint
`ℤ_X[0] ⟶ Rpr₂_*(μ_n[2])` of `diagonalKummerShiftedHom` along `pr₂⁻¹ ⊣ Rpr₂_*`. -/
def diagonalEdge :
    (DerivedCategory.singleFunctor _ 0).obj (intSheaf X) ⟶
      (etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f f)).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧) :=
  (etaleAbelianDerivedAdjunction.{u, 0} (pullback.snd f f)).homEquiv _ _
    (diagonalKummerShiftedHom f hn0 hY)

variable {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)

omit [IsSeparated f] [SmoothOfRelativeDimension 1 f] in
/-- The geometric fibre `Spec Ω ×_X (X ×_S X)` of `pr₂` over `x̄` is a pullback square. -/
theorem isPullback_fibre :
    IsPullback (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
      (pullback.snd f f) x :=
  (IsPullback.of_hasPullback x (pullback.snd f f)).flip

/-- **The edge map under base change to a geometric point**: `x̄⁻¹ψ` followed by the base change
map is the adjoint of the restriction of the Kummer class of the diagonal to the geometric
fibre. -/
theorem diagonalEdge_comp_baseChange :
    (etaleAbelianDerivedInverseImage.{u, 0} x).map (diagonalEdge f hn0 hY) ≫
      (etaleAbelianDerivedBaseChange.{u, 0} (pullback.snd f f) x
        (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
        (isPullback_fibre f x).w).app _ =
      (etaleAbelianDerivedAdjunction.{u, 0} (pullback.fst x (pullback.snd f f))).homEquiv _ _
        ((etaleAbelianDerivedSquare.{u, 0} (pullback.snd f f) x
            (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
            (pullback.snd x (pullback.snd f f) ≫ pullback.snd f f) rfl
            (isPullback_fibre f x).w).app _ ≫
          (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd x (pullback.snd f f))).map
            (diagonalKummerShiftedHom f hn0 hY)) := by
  rw [etaleAbelianDerivedBaseChange_eq_mateEquiv.{u, 0} (pullback.snd f f) x
    (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
    (pullback.snd x (pullback.snd f f) ≫ pullback.snd f f) rfl (isPullback_fibre f x).w]
  exact map_homEquiv_comp_mateEquiv_app _ _ _ _

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_comp_left_of_isIso {C : Type*} [Category* C] {P P' : C} (i : P' ⟶ P) [IsIso i]
    (Q : C) : Function.Bijective (fun g : P ⟶ Q => i ≫ g) :=
  ⟨fun a b h => by simpa using congrArg (inv i ≫ ·) h, fun w => ⟨inv i ≫ w, by simp⟩⟩

/-- **`H⁰` is bijective on morphisms out of an object isomorphic to a projective object in degree
zero.** -/
theorem bijective_homologyFunctor_map_of_iso_singleFunctor {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {A' : DerivedCategory C} {A : C} [Projective A]
    (e : A' ≅ (DerivedCategory.singleFunctor C 0).obj A) (E : DerivedCategory C) :
    Function.Bijective
      (fun z : A' ⟶ E => (DerivedCategory.homologyFunctor C 0).map z) := by
  have h := DerivedCategory.bijective_homologyFunctor_map_singleFunctor_of_projective A E
  have key : (fun z : A' ⟶ E => (DerivedCategory.homologyFunctor C 0).map z) =
      (fun w => (DerivedCategory.homologyFunctor C 0).map e.hom ≫ w) ∘
        (fun z' : (DerivedCategory.singleFunctor C 0).obj A ⟶ E =>
          (DerivedCategory.homologyFunctor C 0).map z') ∘ (fun z => e.inv ≫ z) := by
    funext z
    simp [← Functor.map_comp]
  rw [key]
  exact (bijective_comp_left_of_isIso _ _).comp (h.comp (bijective_comp_left_of_isIso _ _))

/-- The shifted constant sheaf `μ_n[2]` is bounded below with torsion cohomology. -/
theorem torsionCohomologyProperty_shift_single_rootsOfUnity (Y : Scheme.{u}) {n : ℕ}
    (hn0 : n ≠ 0) :
    Stacks.Torsion.torsionCohomologyProperty.{u + 1} Y.smallEtaleTopology
      (((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y n))⟦(2 : ℤ)⟧) := by
  have h := Stacks.Torsion.torsionCohomologyProperty_singleFunctor
    (hF := torsionSheafProperty_of_nsmul_id_eq_zero
      (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y n) n
      (Nat.pos_of_ne_zero hn0) (Stacks.Kummer.nsmul_id_rootsOfUnitySheaf_univ.{u, u + 1} Y n))
  intro i
  exact (Stacks.Torsion.torsionSheafProperty.{u + 1} Y.smallEtaleTopology).prop_of_iso
    ((((DerivedCategory.homologyFunctor _ 0).shiftIso 2 i (2 + i) rfl).app _).symm) (h (2 + i))

/-- **The restriction of the Kummer class of the diagonal to the geometric fibre, read in the
derived category**: up to isomorphisms at both ends, the class `α ≫ q⁻¹ c` obtained from the
comparison of inverse images around the fibre square is the derived-category morphism of the
pulled back class `q^* c_Δ ∈ H²(C, μ_n)`. -/
theorem exists_square_comp_map_diagonalKummerShiftedHom_eq {S X : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [SmoothOfRelativeDimension 1 f] {n : ℕ} (hn0 : n ≠ 0)
    (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤))) {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃ (I₁ : (etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst x (pullback.snd f f))).obj
          ((etaleAbelianDerivedInverseImage.{u, 0} x).obj
            ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (intSheaf (pullback x (pullback.snd f f))))
      (I₂ : ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1}
          (pullback x (pullback.snd f f)) n))⟦((2 : ℕ) : ℤ)⟧ ≅
        (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd x (pullback.snd f f))).obj
          (((DerivedCategory.singleFunctor _ 0).obj
            (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧)),
      (etaleAbelianDerivedSquare.{u, 0} (pullback.snd f f) x
            (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
            (pullback.snd x (pullback.snd f f) ≫ pullback.snd f f) rfl
            (isPullback_fibre f x).w).app _ ≫
          (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd x (pullback.snd f f))).map
            (diagonalKummerShiftedHom f hn0 hY) =
        I₁.hom ≫ (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1}
          (pullback.snd x (pullback.snd f f)) n 2
            (Stacks.Kummer.diagonalKummerClass f hn0 hY)).hom ≫ I₂.hom := by
  let q := pullback.snd x (pullback.snd f f)
  let F := etaleAbelianInverseImage.{u, 0} q
  let c := Stacks.Kummer.diagonalKummerClass f hn0 hY
  let M := c.mapExactFunctor F
  let κ := (etaleAbelianInverseImageConstantIso.{u, 0} q).app (AddCommGrpCat.of (ULift ℤ))
  let μi := Stacks.Kummer.rootsOfUnityInverseImageIso.{u, u + 1} q n hY
  let sF := F.mapDerivedCategorySingleFunctor 0
  let sq := (etaleAbelianDerivedSquare.{u, 0} (pullback.snd f f) x q
      (pullback.fst x (pullback.snd f f)) (q ≫ pullback.snd f f) rfl
      (isPullback_fibre f x).w).app ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X))
  have : IsIso sq := by
    change IsIso (((etaleAbelianDerivedInverseImageCompIso'.{u, 0}
      (pullback.fst x (pullback.snd f f)) x (q ≫ pullback.snd f f) (isPullback_fibre f x).w).inv ≫
        (etaleAbelianDerivedInverseImageCompIso'.{u, 0} q (pullback.snd f f)
          (q ≫ pullback.snd f f) rfl).hom).app _)
    infer_instance
  refine ⟨asIso sq ≪≫
    (etaleAbelianDerivedInverseImage.{u, 0} q).mapIso
      (inverseImageSingleIntSheafIso (pullback.snd f f)) ≪≫ sF.app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso κ,
    (shiftFunctor _ ((2 : ℕ) : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso μi.symm ≪≫
      (sF.app _).symm) ≪≫
    (((etaleAbelianDerivedInverseImage.{u, 0} q).commShiftIso ((2 : ℕ) : ℤ)).app _).symm, ?_⟩
  have hr : (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} q n 2 c).hom =
      (DerivedCategory.singleFunctor _ 0).map κ.inv ≫ M.hom ≫
        ((DerivedCategory.singleFunctor _ 0).map μi.hom)⟦((2 : ℕ) : ℤ)⟧' := by
    have e : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} q n 2 c =
        ((Abelian.Ext.mk₀ κ.inv).comp M (zero_add 2)).comp (Abelian.Ext.mk₀ μi.hom)
          (add_zero 2) := by
      rw [Stacks.EtaleCohomology.rootsOfUnityPullbackMap_apply,
        Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply]
      rfl
    rw [e, Abelian.Ext.comp_hom, Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom,
      Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  have hM : M.hom = (sF.inv.app _) ≫ ((etaleAbelianDerivedInverseImage.{u, 0} q).map c.hom ≫
      ((etaleAbelianDerivedInverseImage.{u, 0} q).commShiftIso ((2 : ℕ) : ℤ)).hom.app _) ≫
        (sF.hom.app _)⟦((2 : ℕ) : ℤ)⟧' :=
    Abelian.Ext.mapExactFunctor_hom F c
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc, diagonalKummerShiftedHom, Functor.map_comp]
  congr 2
  rw [hr, hM]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id]
  have h1 : ∀ (Z : Sheaf (pullback x (pullback.snd f f)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (DerivedCategory.singleFunctor _ 0).map (𝟙 Z) = 𝟙 _ :=
    fun Z => CategoryTheory.Functor.map_id _ _
  simp only [h1, Category.id_comp, Iso.app_inv, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm.trans (by congr 1; simp [F, q])

end Edge

section Generator

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIrreducible f]
  {n : ℕ} (hn0 : n ≠ 0) (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (hn : IsUnit (n : Ω))

include hn in
/-- **The edge map of the Kummer class of the diagonal generates at every geometric point.** For
`x̄ : Spec Ω ⟶ X`, `Ω` algebraically closed, `H⁰(x̄⁻¹ψ)` generates a cyclic group of order `n`,
the group of morphisms `H⁰(x̄⁻¹ℤ[0]) ⟶ H⁰(x̄⁻¹Rpr₂_*(μ_n[2]))`. -/
theorem isZModGenerator_homologyMap_diagonalEdge :
    IsZModGenerator n ((DerivedCategory.homologyFunctor _ 0).map
      ((etaleAbelianDerivedInverseImage.{u, 0} x).map (diagonalEdge f hn0 hY))) := by
  have : IsSeparated f := inferInstance
  have : SmoothOfRelativeDimension 1 (pullback.snd f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f f) inferInstance
  have : SmoothOfRelativeDimension 1 (pullback.fst x (pullback.snd f f)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (isPullback_fibre f x) inferInstance
  have : IsProper (pullback.fst x (pullback.snd f f)) := inferInstance
  have : GeometricallyIrreducible (pullback.fst x (pullback.snd f f)) := inferInstance
  have : Smooth (pullback.fst x (pullback.snd f f)) :=
    SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve Ω (pullback.fst x (pullback.snd f f)) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
  let c := Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1}
    (pullback.snd x (pullback.snd f f)) n 2 (Stacks.Kummer.diagonalKummerClass f hn0 hY)
  have h0 : IsZModGenerator n c :=
    ⟨Stacks.Kummer.smoothProperCurveTrace _ hn,
      Stacks.Kummer.smoothProperCurveTrace_diagonalKummerClass f x hn hn0 hY⟩
  obtain ⟨I₁, I₂, hI⟩ := exists_square_comp_map_diagonalKummerShiftedHom_eq f hn0 hY x
  let φ₁ := (Abelian.Ext.homAddEquiv (C := Sheaf (pullback x (pullback.snd f f)).smallEtaleTopology
    AddCommGrpCat.{u + 1})).trans (isoHomAddEquiv I₁ I₂)
  have : (etaleAbelianDerivedDirectImage.{u, 0} (pullback.fst x (pullback.snd f f))).Additive :=
    (etaleAbelianDerivedAdjunction.{u, 0}
      (pullback.fst x (pullback.snd f f))).right_adjoint_additive
  have := projective_constantSheaf_uliftInt_of_isSepClosed Ω
  let adjC := etaleAbelianDerivedAdjunction.{u, 0} (pullback.fst x (pullback.snd f f))
  let Θ₀ : ((etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst x (pullback.snd f f))).obj
          ((etaleAbelianDerivedInverseImage.{u, 0} x).obj
            ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X))) ⟶
        (etaleAbelianDerivedInverseImage.{u, 0} (pullback.snd x (pullback.snd f f))).obj
          (((DerivedCategory.singleFunctor _ 0).obj
            (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧)) →+ _ :=
    AddMonoidHom.mk' (fun d => (DerivedCategory.homologyFunctor _ 0).map (adjC.homEquiv _ _ d))
      (fun d d' => by simp [Adjunction.homEquiv_unit, Functor.map_add])
  let Θ := AddEquiv.ofBijective Θ₀ ((bijective_homologyFunctor_map_of_iso_singleFunctor
      (inverseImageSingleIntSheafIso x) _).comp (adjC.homEquiv _ _).bijective)
  let bc := (etaleAbelianDerivedBaseChange.{u, 0} (pullback.snd f f) x
      (pullback.snd x (pullback.snd f f)) (pullback.fst x (pullback.snd f f))
      (isPullback_fibre f x).w).app (((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (pullback f f) n))⟦(2 : ℤ)⟧)
  have : IsIso bc :=
    isIso_etaleAbelianDerivedBaseChange_of_isProper (pullback.snd f f) (isPullback_fibre f x) _
      (-2) (DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by omega))
      (torsionCohomologyProperty_shift_single_rootsOfUnity _ hn0)
  let Ψ := isoHomAddEquiv (Iso.refl ((DerivedCategory.homologyFunctor _ 0).obj
    ((etaleAbelianDerivedInverseImage.{u, 0} x).obj
      ((DerivedCategory.singleFunctor _ 0).obj (intSheaf X)))))
    ((DerivedCategory.homologyFunctor _ 0).mapIso
    (asIso bc)).symm
  have key : Ψ (Θ (φ₁ c)) =
      (DerivedCategory.homologyFunctor _ 0).map
        ((etaleAbelianDerivedInverseImage.{u, 0} x).map (diagonalEdge f hn0 hY)) := by
    have e := diagonalEdge_comp_baseChange f hn0 hY x
    change (𝟙 _ ≫ (DerivedCategory.homologyFunctor _ 0).map
      (adjC.homEquiv _ _ (I₁.hom ≫ c.hom ≫ I₂.hom)) ≫ _) = _
    rw [← hI, ← e]
    simp
  rw [← key]
  exact ((h0.map φ₁).map Θ).map Ψ

end Generator

end Stacks.EtaleCohomology

end
