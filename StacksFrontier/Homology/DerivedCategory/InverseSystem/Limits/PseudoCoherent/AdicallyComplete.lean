module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent.DerivedLimit

/-!
# Pseudo-coherence of a derived inverse limit: the adically complete case

## Main results

* `derivedLimit_isPseudoCoherent_isDerivedComplete_and_baseChange_iso`
  ([stacks 09AV]): the adically complete case, where the derived inverse limit is in addition
  derived complete.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped TensorProduct

namespace StacksDraft.DerivedInverseLimit

universe u v w w'

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] extendScalarsGeneral_additive

/-! ### Tag 09AV: the adically complete case -/

section AdicallyComplete

open CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra


/-- The inverse system `n ↦ A ⧸ I ^ (n + 1)` of quotients by the powers of an ideal, with the
canonical factorisation maps as transitions. -/
public abbrev quotientPowerDiagram {A : Type u} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (A ⧸ I ^ (n.unop + 1))
  map f := CommRingCat.ofHom
    (Ideal.Quotient.factorPow I (Nat.add_le_add_right (leOfHom f.unop) 1))
  map_id n := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The cone on `quotientPowerDiagram I` with vertex `A`, given by the quotient maps. -/
public abbrev quotientPowerCone {A : Type u} [CommRing A] (I : Ideal A) :
    Cone (quotientPowerDiagram I) where
  pt := CommRingCat.of A
  π := {
    app n := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n.unop + 1)))
    naturality := by intros; ext x; rfl }

-- Constructing the universal map through the adic limit requires substantial elaboration.
/-- For an `I`-adically complete ring, `A` is the limit of its quotients by the powers of `I`. -/
public def quotientPowerConeIsLimit {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] : IsLimit (quotientPowerCone I) := by
  let ha : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ h ↦ Nat.add_lt_add_right h 1
  let f (s : Cone (quotientPowerDiagram I)) (n : ℕ) :
      s.pt →+* A ⧸ I ^ (n + 1) := (s.π.app (op n)).hom
  have hf (s : Cone (quotientPowerDiagram I)) {n : ℕ} :
      (Ideal.Quotient.factorPow I (ha.monotone (Nat.le_succ n))).comp (f s (n + 1)) =
        f s n :=
    congrArg CommRingCat.Hom.hom (s.w (homOfLE (Nat.le_succ n)).op)
  refine IsLimit.mk (fun s ↦ CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom I ha (f s) (hf s))) ?_ ?_
  · exact fun s n ↦ CommRingCat.hom_ext
      (IsAdicComplete.StrictMono.mk_comp_liftRingHom I ha (f s) (hf s) (n := n.unop))
  · exact fun s m hm ↦ CommRingCat.hom_ext (IsAdicComplete.StrictMono.eq_liftRingHom I ha (f s)
      (hf s) fun n ↦ congrArg CommRingCat.Hom.hom (hm (op n)))

/-- If `J ^ n ≤ I ≤ J`, the kernel of the factorisation `A ⧸ I →+* A ⧸ J` has vanishing
`n`-th power. -/
public theorem ker_factor_pow_eq_bot {A : Type u} [CommRing A]
    {I J : Ideal A} (hIJ : I ≤ J) {n : ℕ} (hJI : J ^ n ≤ I) :
    RingHom.ker (Ideal.Quotient.factor hIJ) ^ n = ⊥ := by
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  apply le_bot_iff.mp
  simpa only [Ideal.map_quotient_self] using
    (Ideal.map_mono (f := Ideal.Quotient.mk I) hJI)

/-- A nilpotent ideal is locally nilpotent. -/
public theorem isLocallyNilpotent_of_isNilpotent {A : Type u} [CommRing A]
    (I : Ideal A) (hI : IsNilpotent I) : I.IsLocallyNilpotent := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow hx n
  simpa only [hn, Ideal.zero_eq_bot, Submodule.mem_bot] using h

/-- The endomorphism `1 - f · shift` of the countable product `∏ₙ K`, that is,
`(xₙ) ↦ (xₙ - f · xₙ₊₁)`. -/
public def shiftSubMul {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (f : A) :
    (∏ᶜ fun _ : ℕ => K) ⟶ (∏ᶜ fun _ : ℕ => K) :=
  Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1))

/-- For any morphism `g : L ⟶ M`, the endomorphisms `shiftSubMul L f` and `shiftSubMul M f` are
intertwined by `Pi.map (fun _ : ℕ => g)`. -/
public theorem shiftSubMul_naturality {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (L M : DerivedCategory (ModuleCat.{max u v} A)) (f : A) (g : L ⟶ M) :
    shiftSubMul L f ≫ Limits.Pi.map (fun _ : ℕ => g) =
      Limits.Pi.map (fun _ : ℕ => g) ≫ shiftSubMul M f := by
  apply Pi.hom_ext
  intro m
  simp [shiftSubMul, Preadditive.sub_comp, Preadditive.comp_sub,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- If some power of `f` acts as zero on `K`, then `shiftSubMul K f` is an isomorphism: it is
`1` minus a nilpotent endomorphism of `∏ₙ K`. -/
public theorem shiftSubMul_isIso_of_pow_smul_id_eq_zero {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (f : A) (e : ℕ)
    (he : f ^ e • 𝟙 K = (0 : K ⟶ K)) : IsIso (shiftSubMul K f) := by
  let S : (∏ᶜ fun _ : ℕ => K) ⟶ ∏ᶜ fun _ : ℕ => K :=
    Pi.lift (fun n : ℕ ↦ f • Pi.π (fun _ : ℕ => K) (n + 1))
  let S' : End (∏ᶜ fun _ : ℕ => K) := End.of S
  have hSpi (m : ℕ) : S ≫ Pi.π (fun _ : ℕ => K) m =
      f • Pi.π (fun _ : ℕ => K) (m + 1) := by
    simp [S]
  have key : ∀ (k n : ℕ), (S' ^ k).asHom ≫ Pi.π (fun _ : ℕ => K) n =
      f ^ k • Pi.π (fun _ : ℕ => K) (n + k) := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [show (S' ^ (k + 1)).asHom = S ≫ (S' ^ k).asHom by rw [pow_succ]; rfl,
        Category.assoc, ih n, Linear.comp_smul, hSpi, smul_smul, pow_succ]
      rfl
  have hSe : (S' ^ e : End (∏ᶜ fun _ : ℕ => K)) = 0 := by
    apply End.ext
    change (S' ^ e).asHom = (0 : (∏ᶜ fun _ : ℕ => K) ⟶ ∏ᶜ fun _ : ℕ => K)
    apply Limits.limit.hom_ext
    intro j
    rw [key e j.as]
    calc
      f ^ e • Pi.π (fun _ : ℕ => K) (j.as + e) =
          Pi.π (fun _ : ℕ => K) (j.as + e) ≫ (f ^ e • 𝟙 K) := by
            rw [Linear.comp_smul, Category.comp_id]
      _ = 0 := by rw [he, comp_zero]
    simp only [zero_comp]
  have hsplit : shiftSubMul K f = ((1 : End (∏ᶜ fun _ : ℕ => K)) - S').asHom := by
    have h1 : ((1 : End (∏ᶜ fun _ : ℕ => K)) - S').asHom = 𝟙 _ - S := rfl
    rw [h1]
    apply Limits.limit.hom_ext
    intro j
    rw [shiftSubMul, Pi.lift_comp_π, Preadditive.sub_comp, Category.id_comp, hSpi]
  have hunit : IsUnit ((1 : End (∏ᶜ fun _ : ℕ => K)) - S') :=
    (show IsNilpotent S' from ⟨e, hSe⟩).isUnit_one_sub
  rw [hsplit]
  exact (CategoryTheory.isUnit_iff_isIso _).mp hunit

/-- If `shiftSubMul (D n) f` is an isomorphism for every `n`, then so is
`shiftSubMul (∏ᶜ D) f`. -/
public theorem shiftSubMul_isIso_pi {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (D : ℕ → DerivedCategory (ModuleCat.{max u v} A)) (f : A)
    (hD : ∀ n, IsIso (shiftSubMul (D n) f)) : IsIso (shiftSubMul (∏ᶜ D) f) := by
  let X : DerivedCategory (ModuleCat.{max u v} A) := ∏ᶜ (fun _ : ℕ => ∏ᶜ D)
  let Y : DerivedCategory (ModuleCat.{max u v} A) :=
    ∏ᶜ (fun n : ℕ => ∏ᶜ (fun _ : ℕ => D n))
  let ehom : X ⟶ Y := Pi.lift (fun n : ℕ ↦ Pi.lift (fun j : ℕ ↦
    Pi.π (fun _ : ℕ => ∏ᶜ D) j ≫ Pi.π D n))
  let einv : Y ⟶ X := Pi.lift (fun j : ℕ ↦ Pi.lift (fun n : ℕ ↦
    Pi.π (fun n : ℕ => ∏ᶜ (fun _ : ℕ => D n)) n ≫
      Pi.π (fun _ : ℕ => D n) j))
  have hhi : ehom ≫ einv = 𝟙 X := by
    apply Pi.hom_ext; intro j; apply Pi.hom_ext; intro n
    simp [ehom, einv]
  have hih : einv ≫ ehom = 𝟙 Y := by
    apply Pi.hom_ext; intro n; apply Pi.hom_ext; intro j
    simp [ehom, einv]
  let e : X ≅ Y := ⟨ehom, einv, hhi, hih⟩
  let g : Y ⟶ Y := Limits.Pi.map (fun n : ℕ => shiftSubMul (D n) f)
  have hg : IsIso g := by apply Pi.map_isIso
  have hconj : shiftSubMul (∏ᶜ D) f = ehom ≫ g ≫ einv := by
    apply Pi.hom_ext; intro j; apply Pi.hom_ext; intro n
    simp [shiftSubMul, ehom, einv, g, Preadditive.sub_comp, Preadditive.comp_sub,
      Linear.smul_comp, Linear.comp_smul, Category.assoc]
  rw [hconj]
  have : IsIso ehom := e.isIso_hom
  have : IsIso einv := e.isIso_inv
  infer_instance

/-- The Milnor endomorphism `1 - f·shift` of a constant tower, in the form used below. -/
public theorem oneSubSmulShift_eq_shiftSubMul {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (f : A) :
    oneSubSmulShift K f = shiftSubMul K f := by
  apply Pi.hom_ext
  intro n
  rw [oneSubSmulShift_π, shiftSubMul, Pi.lift_comp_π]

private theorem isDerivedComplete_of_milnor {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (I : Ideal A) (D : ℕ → DerivedCategory (ModuleCat.{max u v} A))
    (t : ∀ n, D (n + 1) ⟶ D n) (K : DerivedCategory (ModuleCat.{max u v} A))
    (p : K ⟶ ∏ᶜ D) (δ : ∏ᶜ D ⟶ K⟦(1 : ℤ)⟧)
    (hTriangle : Triangle.mk p
      (Pi.lift fun n : ℕ ↦ Pi.π D n - Pi.π D (n + 1) ≫ t n) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} A)))
    (hzero : ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, f ^ e • 𝟙 (D n) = 0) :
    _root_.IsDerivedComplete I K := by
  intro f hf
  have hterm : ∀ n, IsIso (shiftSubMul (D n) f) := fun n ↦
    let ⟨e, he⟩ := hzero f hf n
    shiftSubMul_isIso_of_pow_smul_id_eq_zero (D n) f e he
  have hprod : IsIso (shiftSubMul (∏ᶜ D) f) := shiftSubMul_isIso_pi D f hterm
  let MT := Triangle.mk p (Pi.lift fun n : ℕ ↦
    Pi.π D n - Pi.π D (n + 1) ≫ t n) δ
  let Tfam : ℕ → Triangle (DerivedCategory (ModuleCat.{max u v} A)) := fun _ => MT
  have hPTdist := productTriangle_distinguished Tfam (fun _ => hTriangle)
  let ψ : productTriangle Tfam ⟶ productTriangle Tfam :=
    Triangle.homMk _ _ (shiftSubMul K f) (shiftSubMul (∏ᶜ D) f)
      (shiftSubMul (∏ᶜ D) f)
      (by rw [productTriangle_mor₁]; exact (shiftSubMul_naturality K _ f p).symm)
      (by rw [productTriangle_mor₂]; exact (shiftSubMul_naturality _ _ f _).symm)
      (by
        rw [productTriangle_mor₃]
        change (Limits.Pi.map (fun _ : ℕ => δ) ≫
            inv (piComparison (shiftFunctor _ (1 : ℤ)) (fun _ : ℕ => K))) ≫
              (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) =
          shiftSubMul (∏ᶜ D) f ≫
            (Limits.Pi.map (fun _ : ℕ => δ) ≫
              inv (piComparison (shiftFunctor _ (1 : ℤ)) (fun _ : ℕ => K)))
        let pc := piComparison (shiftFunctor
          (DerivedCategory (ModuleCat.{max u v} A)) (1 : ℤ)) (fun _ : ℕ => K)
        have hnatδ := shiftSubMul_naturality (∏ᶜ D)
          ((shiftFunctor _ (1 : ℤ)).obj K) f δ
        have hshift : pc ≫ shiftSubMul ((shiftFunctor _ (1 : ℤ)).obj K) f =
            (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) ≫ pc := by
          apply Pi.hom_ext
          intro m
          rw [Category.assoc, shiftSubMul, Pi.lift_comp_π, Preadditive.comp_sub,
            Linear.comp_smul, piComparison_comp_π, piComparison_comp_π,
            Category.assoc, piComparison_comp_π, shiftSubMul, ← Functor.map_comp,
            Pi.lift_comp_π, Functor.map_sub, Functor.Linear.map_smul]
        have hshift' : shiftSubMul ((shiftFunctor _ (1 : ℤ)).obj K) f ≫ inv pc =
            inv pc ≫ (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact hshift
        rw [Category.assoc, ← hshift', ← Category.assoc, ← hnatδ, Category.assoc])
  have hK : IsIso ψ.hom₁ := isIso₁_of_isIso₂₃ ψ hPTdist hPTdist hprod hprod
  have hm : IsIso (shiftSubMul K f) := hK
  rw [isDerivedCompleteAt_iff_isIso, oneSubSmulShift_eq_shiftSubMul]
  exact hm

/-- **Stacks 09AV.** Let `A` be `I`-adically complete and let `Kₙ n` be a derived object over
`A ⧸ I ^ (n + 1)`. Suppose `Kₙ 0` is pseudo-coherent and every transition map becomes an
isomorphism after derived base change. Then a derived inverse limit `K` over `A` is
pseudo-coherent and derived complete, and its canonical derived base-change map to every
`Kₙ n` is an isomorphism. -/
@[stacks 09AV]
public theorem derivedLimit_isPseudoCoherent_isDerivedComplete_and_baseChange_iso
    (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (Kₙ : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (φ : ∀ n : ℕ, Kₙ (n + 1) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))).mapDerivedCategory.obj (Kₙ n))
    (hPseudoCoherent : PseudoCoherence.IsPseudoCoherent (Kₙ 0))
    (hBaseChange : ∀ n : ℕ, IsIso (derivedBaseChangeComparison
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) (φ n))) :
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} A) :=
      moduleCat_hasExactLimitsOfShape_discrete A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let q : ∀ n : ℕ, A ⧸ I ^ (n + 2) →+* A ⧸ I ^ (n + 1) := fun n ↦
      Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
    let a : ∀ n : ℕ, A →+* A ⧸ I ^ (n + 1) := fun n ↦
      Ideal.Quotient.mk (I ^ (n + 1))
    let X : ℕ → DerivedCategory (ModuleCat.{max u v} A) := fun n ↦
      (ModuleCat.restrictScalars (a n)).mapDerivedCategory.obj (Kₙ n)
    let t : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
      (ModuleCat.restrictScalars (a (n + 1))).mapDerivedCategory.map (φ n) ≫
        (derivedRestrictScalarsComp (a (n + 1)) (q n) (a n)
          (by ext x; rfl)).hom.app (Kₙ n)
    ∀ (K : DerivedCategory (ModuleCat.{max u v} A))
      (p : K ⟶ ∏ᶜ X) (δ : ∏ᶜ X ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π X n - Pi.π X (n + 1) ≫ t n) δ ∈
          distTriang (DerivedCategory (ModuleCat.{max u v} A)) →
        PseudoCoherence.IsPseudoCoherent K ∧ _root_.IsDerivedComplete I K ∧
          ∀ n : ℕ, IsIso (derivedBaseChangeComparison
            (a n) (p ≫ Pi.π X n)) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} A) :=
    moduleCat_hasExactLimitsOfShape_discrete A ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  dsimp only
  intro K p δ hTriangle
  have hNilpotent (n : ℕ) :
      IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))) :=
    ⟨2, ker_factor_pow_eq_bot (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (by rw [← pow_mul]; exact Ideal.pow_le_pow_right (by omega))⟩
  have hMain := derivedLimit_isPseudoCoherent_and_baseChange_iso
    (quotientPowerDiagram I) (quotientPowerCone I) (quotientPowerConeIsLimit I) Kₙ φ
    (fun n ↦ Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
    (fun n ↦ isLocallyNilpotent_of_isNilpotent _ (hNilpotent n))
    (Or.inr ⟨0, hPseudoCoherent, fun n _ ↦ hNilpotent n⟩) hBaseChange K p δ hTriangle
  have hzero : ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ,
      f ^ e • 𝟙 ((ModuleCat.restrictScalars
        (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj (Kₙ n)) = 0 := by
    intro f hf n
    refine ⟨n + 1, ?_⟩
    -- Scalar multiplication after restriction is induced by the quotient map.
    let qn : A →+* A ⧸ I ^ (n + 1) := Ideal.Quotient.mk (I ^ (n + 1))
    let : Algebra A (A ⧸ I ^ (n + 1)) := qn.toAlgebra
    have hf' : f ^ (n + 1) ∈ I ^ (n + 1) := Ideal.pow_mem_pow hf (n + 1)
    let F := (ModuleCat.restrictScalars qn).mapDerivedCategory
    have hF : F.Linear A := by
      change (ModuleCat.restrictScalars (Algebra.ofId A (A ⧸ I ^ (n + 1))).toRingHom)
        |>.mapDerivedCategory.Linear A
      infer_instance
    change f ^ (n + 1) • 𝟙 (F.obj (Kₙ n)) = 0
    rw [← F.map_id, ← Functor.Linear.map_smul]
    have hq : algebraMap A (A ⧸ I ^ (n + 1)) (f ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf'
    have hs : f ^ (n + 1) • 𝟙 (Kₙ n) = 0 := by
      change algebraMap A (A ⧸ I ^ (n + 1)) (f ^ (n + 1)) • 𝟙 (Kₙ n) = 0
      rw [hq, zero_smul]
    rw [hs, F.map_zero]
  exact ⟨hMain.1, isDerivedComplete_of_milnor I _ _ K p δ hTriangle hzero, hMain.2⟩

end AdicallyComplete

end StacksDraft.DerivedInverseLimit

end
