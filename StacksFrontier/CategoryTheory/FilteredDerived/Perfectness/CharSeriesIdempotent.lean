module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsSection
public import StacksFrontier.Algebra.Module.Projective.Determinant.IdempotentQuotient
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeries
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresProd

/-!
# The characteristic series over the factors of an idempotent splitting

Let `Λ` be a commutative ring, `e` an idempotent, `Λ₁ = Λ ⧸ (1 - e)` and `Λ₂ = Λ ⧸ (e)`, so that
`Λ = Λ₁ × Λ₂`. A complex of `Λ`-modules which is the direct sum of a complex of `Λ₁`-modules and
a complex of `Λ₂`-modules, both viewed as `Λ`-modules, is perfect as soon as the two summands are,
and the characteristic series `det(1 - f T)` over `Λ` of an endomorphism respecting the splitting
maps, over `Λ₁` and over `Λ₂`, to the characteristic series of the two components. This is the
determinant half of the reduction of Tag 03UZ to local coefficient rings.

## Main results

* `CategoryTheory.FilteredDerived.exists_perfectRep_spec`: an endomorphism of a perfect object
  is represented by a cochain map on a bounded complex of finite projective modules.
* `CategoryTheory.FilteredDerived.alternatingCharSeries_biprod`: the characteristic series of
  `f ⊕ g` on `P ⊕ Q` is the product.
* `CategoryTheory.FilteredDerived.map_alternatingCharSeries_restrictScalars`: for a surjection
  `Λ → Λ'`, the characteristic series over `Λ` of a complex of `Λ'`-modules maps to the one over
  `Λ'`.
* `CategoryTheory.FilteredDerived.exists_isPerfect_map_perfectDerivedCharSeries_of_binaryBicone`:
  the derived statement for a direct sum `K = M₁|_Λ ⊕ M₂|_Λ` in `D(Λ)`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ZeroObject

universe w u v

namespace CategoryTheory.FilteredDerived

/-! ### Representatives -/

section Rep

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **An endomorphism of a perfect object is represented on a bounded complex of finite projective
modules.** -/
public theorem exists_perfectRep_spec (K : DerivedCategory (ModuleCat.{v} R))
    (hK : StacksDraft.Perfect.IsPerfect K) (f : K ⟶ K) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ) (_ : finiteProjectiveComplex R P)
      (e : DerivedCategory.Q.obj P ≅ K) (g : P ⟶ P),
      DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv := by
  let P := perfectRep R K hK
  have hP := perfectRep_spec R K hK
  let e := perfectRepIso R K hK
  let : CochainComplex.IsKProjective P := by
    obtain ⟨⟨_, ⟨d, hd⟩⟩, hproj⟩ := hP
    let : P.IsStrictlyLE d := hd
    let (i : ℤ) : Module.Projective R (P.X i) := (hproj i).1
    let (i : ℤ) : Projective (P.X i) := inferInstance
    exact CochainComplex.isKProjective_of_projective P d
  let Q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let α : DerivedCategory.Qh.obj (Q.obj P) ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P ≪≫ e
  obtain ⟨gH, hgH⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (Q.obj P)).surjective
    (α.hom ≫ f ≫ α.inv)
  obtain ⟨g, rfl⟩ := Q.map_surjective gH
  refine ⟨P, hP, e, g, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.naturality g
  dsimp at hn
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).hom.app P), ← hn]
  show DerivedCategory.Qh.map (Q.map g) ≫ _ = _
  rw [hgH]
  simp [α]

end Rep

/-! ### Direct sums -/

section Biprod

variable (R : Type u) [CommRing R]

/-- The direct sum of two bounded complexes of finite projective modules is one. -/
public theorem finiteProjectiveComplex_biprod {P Q : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : finiteProjectiveComplex R P) (hQ : finiteProjectiveComplex R Q) :
    finiteProjectiveComplex R (P ⊞ Q) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hPi⟩ := hP
  obtain ⟨⟨⟨c, hc⟩, ⟨d, hd⟩⟩, hQi⟩ := hQ
  have hz : ∀ i, IsZero (P.X i) → IsZero (Q.X i) → IsZero ((P ⊞ Q).X i) := fun i h₁ h₂ =>
    (biprod_isZero_iff _ _).2 ⟨h₁, h₂⟩ |>.of_iso (HomologicalComplex.biprodXIso P Q i)
  refine ⟨⟨⟨min a c, ?_⟩, ⟨max b d, ?_⟩⟩, fun i => ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (P.isZero_of_isStrictlyGE a i (by omega))
      (Q.isZero_of_isStrictlyGE c i (by omega))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (P.isZero_of_isStrictlyLE b i (by omega))
      (Q.isZero_of_isStrictlyLE d i (by omega))
  · have := (hPi i).1
    have := (hPi i).2
    have := (hQi i).1
    have := (hQi i).2
    let eq := (HomologicalComplex.biprodXIso P Q i ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
    exact ⟨Module.Projective.of_equiv eq.symm, Module.Finite.equiv eq.symm⟩

/-- **The characteristic series of `f ⊕ g` on `P ⊕ Q` is the product of the two.** -/
public theorem alternatingCharSeries_biprod {P Q : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : finiteProjectiveComplex R P) (hQ : finiteProjectiveComplex R Q) (f : P ⟶ P)
    (g : Q ⟶ Q) :
    alternatingCharSeries R (P ⊞ Q) (finiteProjectiveComplex_biprod R hP hQ) (biprod.map f g) =
      alternatingCharSeries R P hP f * alternatingCharSeries R Q hQ g := by
  have h₁ : ∀ n (x : P.X n), (biprod.fst : P ⊞ Q ⟶ P).f n ((biprod.inl : P ⟶ P ⊞ Q).f n x) = x :=
    fun n x => congrArg (fun h => h.hom x) (HomologicalComplex.biprod_inl_fst_f P Q n)
  have h₂ : ∀ n (x : P.X n), (biprod.snd : P ⊞ Q ⟶ Q).f n ((biprod.inl : P ⟶ P ⊞ Q).f n x) = 0 :=
    fun n x => congrArg (fun h => h.hom x) (HomologicalComplex.biprod_inl_snd_f P Q n)
  have h₃ : ∀ n (x : Q.X n), (biprod.snd : P ⊞ Q ⟶ Q).f n ((biprod.inr : Q ⟶ P ⊞ Q).f n x) = x :=
    fun n x => congrArg (fun h => h.hom x) (HomologicalComplex.biprod_inr_snd_f P Q n)
  have h₄ : ∀ n (x : (P ⊞ Q).X n), (biprod.inl : P ⟶ P ⊞ Q).f n ((biprod.fst : P ⊞ Q ⟶ P).f n x) +
      (biprod.inr : Q ⟶ P ⊞ Q).f n ((biprod.snd : P ⊞ Q ⟶ Q).f n x) = x :=
    fun n x => congrArg (fun h => h.hom x) (HomologicalComplex.biprod_total_f P Q n)
  refine alternatingCharSeries_of_shortExact R P (P ⊞ Q) Q hP _ hQ biprod.inl biprod.snd
    (fun n => Function.LeftInverse.injective (h₁ n))
    (fun n x => ⟨fun hx => ⟨(biprod.fst : P ⊞ Q ⟶ P).f n x, ?_⟩, ?_⟩)
    (fun n => Function.RightInverse.surjective (h₃ n)) f (biprod.map f g) g
    (by simp) (by simp)
  · have := h₄ n x
    rw [hx, map_zero, add_zero] at this
    exact this
  · rintro ⟨y, rfl⟩
    exact h₂ n y

end Biprod

/-! ### Restriction of scalars along a surjection -/

section RestrictScalars

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']

/-- A bounded complex of finite projective `R'`-modules is, over `R`, a bounded complex of finite
projective modules, if `R'` is a finite projective `R`-module. -/
public theorem finiteProjectiveComplex_restrictScalars [Module.Finite R R'] [Module.Projective R R']
    {P : CochainComplex (ModuleCat.{v} R') ℤ} (hP : finiteProjectiveComplex R' P) :
    finiteProjectiveComplex R
      (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex _).obj P) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hPi⟩ := hP
  refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i => ?_⟩
  · exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff P _ a).2 ha
  · exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P _ b).2 hb
  · have : Module.Projective R' ((ModuleCat.restrictScalars (algebraMap R R')).obj (P.X i)) :=
      (hPi i).1
    have : Module.Finite R' ((ModuleCat.restrictScalars (algebraMap R R')).obj (P.X i)) :=
      (hPi i).2
    show Module.Projective R ((ModuleCat.restrictScalars (algebraMap R R')).obj (P.X i)) ∧
      Module.Finite R ((ModuleCat.restrictScalars (algebraMap R R')).obj (P.X i))
    exact ⟨Module.Projective.trans R R' _, Module.Finite.trans R' _⟩

/-- **For a surjection `R → R'`, the characteristic series over `R` of an endomorphism of a complex
of `R'`-modules maps to its characteristic series over `R'`.** -/
public theorem map_alternatingCharSeries_restrictScalars [Module.Finite R R']
    [Module.Projective R R'] (hs : Function.Surjective (algebraMap R R'))
    {P : CochainComplex (ModuleCat.{v} R') ℤ} (hP : finiteProjectiveComplex R' P) (g : P ⟶ P) :
    Units.map (PowerSeries.map (algebraMap R R')).toMonoidHom
        (alternatingCharSeries R _ (finiteProjectiveComplex_restrictScalars hP)
          (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex _).map g)) =
      alternatingCharSeries R' P hP g := by
  refine (alternatingCharSeries_baseChange R _ (finiteProjectiveComplex_restrictScalars hP) P hP
    _ g (fun n => (baseChangeEquivOfSurjective
      ((ModuleCat.restrictScalars (algebraMap R R')).obj (P.X n)) hs).symm) fun n => ?_).symm
  let N := (ModuleCat.restrictScalars (algebraMap R R')).obj (P.X n)
  let φ : N →ₗ[R'] N := (g.f n).hom
  have hr :
      ((((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex _).map g).f n).hom =
        φ.restrictScalars R :=
    LinearMap.ext fun _ => rfl
  rw [hr]
  exact baseChangeEquivOfSurjective_symm_conj N hs φ

/-- **If an element of `R` mapping to `1` in `R'` kills a complex, its characteristic series maps
to `1` over `R'`.** -/
public theorem map_alternatingCharSeries_eq_one {a : R} (ha : algebraMap R R' a = 1)
    {P : CochainComplex (ModuleCat.{v} R) ℤ} (hP : finiteProjectiveComplex R P)
    (hPa : ∀ n (x : P.X n), a • x = 0) (g : P ⟶ P) :
    Units.map (PowerSeries.map (algebraMap R R')).toMonoidHom
      (alternatingCharSeries R P hP g) = 1 := by
  let Z : CochainComplex (ModuleCat.{v} R') ℤ := 0
  have hZ : ∀ n, IsZero (Z.X n) := fun n =>
    (HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)
  have (n : ℤ) : Subsingleton (Z.X n) := ModuleCat.subsingleton_of_isZero (hZ n)
  have h0 : finiteProjectiveComplex R' Z :=
    ⟨⟨⟨0, by rw [CochainComplex.isStrictlyGE_iff]; exact fun i _ => hZ i⟩,
      ⟨0, by rw [CochainComplex.isStrictlyLE_iff]; exact fun i _ => hZ i⟩⟩,
      fun n => ⟨inferInstance, inferInstance⟩⟩
  have (n : ℤ) : Subsingleton (R' ⊗[R] P.X n) :=
    TensorProduct.subsingleton_of_smul_eq_zero ha (hPa n)
  rw [← alternatingCharSeries_baseChange R P hP Z h0 g 0
    (fun n => LinearEquiv.ofSubsingleton _ _)
    (fun n => LinearMap.ext fun _ => Subsingleton.elim _ _)]
  unfold alternatingCharSeries
  refine finprod_eq_one_of_forall_eq_one fun i => ?_
  have : charUnitAt R' Z h0 i ((0 : Z ⟶ Z).f i) = 1 := by
    let : Module.Projective R' (Z.X i) := (h0.2 i).1
    let : Module.Finite R' (Z.X i) := (h0.2 i).2
    apply Units.ext
    rw [coe_charUnitAt, Units.val_one]
    have : ((0 : Z ⟶ Z).f i).hom = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
    rw [this, ProjectiveDeterminant.charSeries_zero]
  rw [this]
  split_ifs <;> simp

end RestrictScalars

/-! ### The derived statement -/

section Derived

/-- An object of the derived category represented by a bounded complex of finite projective
modules is perfect. -/
public theorem isPerfect_of_iso (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max v u} R)]
    {P : CochainComplex (ModuleCat.{max v u} R) ℤ} (hP : finiteProjectiveComplex R P)
    {K : DerivedCategory (ModuleCat.{max v u} R)} (e : DerivedCategory.Q.obj P ≅ K) :
    StacksDraft.Perfect.IsPerfect K := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hPi⟩ := hP
  exact ⟨P, a, b, ha, hb, fun i => (hPi i).2, fun i => (hPi i).1, ⟨e.symm⟩⟩

variable {R : Type u} [CommRing R] {R₁ : Type u} [CommRing R₁] [Algebra R R₁]
  {R₂ : Type u} [CommRing R₂] [Algebra R R₂]
  [Module.Finite R R₁] [Module.Projective R R₁] [Module.Finite R R₂] [Module.Projective R R₂]
  [HasDerivedCategory.{w} (ModuleCat.{max v u} R)] [HasDerivedCategory.{w} (ModuleCat.{max v u} R₁)]
  [HasDerivedCategory.{w} (ModuleCat.{max v u} R₂)]

/-- The isomorphism `Q(P|_R) ≅ (Q P)|_R` transporting a representative of `M` to `M|_R`. -/
private def restrictRepIso {R' : Type u} [CommRing R'] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{max v u} R')]
    {P : CochainComplex (ModuleCat.{max v u} R') ℤ} {M : DerivedCategory (ModuleCat.{max v u} R')}
    (e : DerivedCategory.Q.obj P ≅ M) :
    DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex _).obj P) ≅
      (ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory.obj M :=
  ((ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategoryFactors.app P).symm ≪≫
    (ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory.mapIso e

private theorem restrictRepIso_comm {R' : Type u} [CommRing R'] [Algebra R R']
    [HasDerivedCategory.{w} (ModuleCat.{max v u} R')]
    {P : CochainComplex (ModuleCat.{max v u} R') ℤ} {M : DerivedCategory (ModuleCat.{max v u} R')}
    (e : DerivedCategory.Q.obj P ≅ M) (g : P ⟶ P) (φ : M ⟶ M)
    (hg : DerivedCategory.Q.map g = e.hom ≫ φ ≫ e.inv) :
    DerivedCategory.Q.map
        (((ModuleCat.restrictScalars (algebraMap R R')).mapHomologicalComplex _).map g) ≫
        (restrictRepIso (R := R) e).hom =
      (restrictRepIso (R := R) e).hom ≫
        (ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory.map φ := by
  have hn :=
    (ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategoryFactors_hom_naturality g
  simp only [restrictRepIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [← cancel_epi
      ((ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategoryFactors.hom.app P),
    ← reassoc_of% hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, hg, Iso.inv_hom_id,
    Category.comp_id]

/-- **The characteristic series over the two factors of a biproduct.** Let `a : R` map to `1` in
`R₁` and to `0` in `R₂`, both finite projective `R`-algebras with `R → R₁` and `R → R₂` surjective.
Let `K` be a direct sum, in `D(R)`, of the restrictions `M₁|_R` and `M₂|_R` of perfect objects
`M₁ ∈ D(R₁)` and `M₂ ∈ D(R₂)`, and `φ` an endomorphism of `K` inducing `φ₁` and `φ₂` on the two
summands. Then `K` is perfect and `det(1 - φ T | K)` maps to `det(1 - φ₁ T | M₁)` over `R₁` and to
`det(1 - φ₂ T | M₂)` over `R₂`. -/
public theorem exists_isPerfect_map_perfectDerivedCharSeries_of_binaryBicone
    (hs₁ : Function.Surjective (algebraMap R R₁)) (hs₂ : Function.Surjective (algebraMap R R₂))
    {a : R} (ha₁ : algebraMap R R₁ a = 1) (ha₂ : algebraMap R R₂ a = 0)
    (M₁ : DerivedCategory (ModuleCat.{max v u} R₁)) (hM₁ : StacksDraft.Perfect.IsPerfect M₁)
    (φ₁ : M₁ ⟶ M₁) (M₂ : DerivedCategory (ModuleCat.{max v u} R₂))
    (hM₂ : StacksDraft.Perfect.IsPerfect M₂) (φ₂ : M₂ ⟶ M₂)
    (b : BinaryBicone ((ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.obj M₁)
      ((ModuleCat.restrictScalars (algebraMap R R₂)).mapDerivedCategory.obj M₂))
    (htotal : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) (φ : b.pt ⟶ b.pt)
    (h₁ : φ ≫ b.fst =
      b.fst ≫ (ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.map φ₁)
    (h₂ : φ ≫ b.snd =
      b.snd ≫ (ModuleCat.restrictScalars (algebraMap R R₂)).mapDerivedCategory.map φ₂) :
    ∃ hK : StacksDraft.Perfect.IsPerfect b.pt,
      Units.map (PowerSeries.map (algebraMap R R₁)).toMonoidHom
          (perfectDerivedCharSeries R b.pt hK φ) = perfectDerivedCharSeries R₁ M₁ hM₁ φ₁ ∧
      Units.map (PowerSeries.map (algebraMap R R₂)).toMonoidHom
          (perfectDerivedCharSeries R b.pt hK φ) = perfectDerivedCharSeries R₂ M₂ hM₂ φ₂ := by
  let hb := isBinaryBilimitOfTotal b htotal
  obtain ⟨P₁, hP₁, e₁, g₁, hg₁⟩ := exists_perfectRep_spec R₁ M₁ hM₁ φ₁
  obtain ⟨P₂, hP₂, e₂, g₂, hg₂⟩ := exists_perfectRep_spec R₂ M₂ hM₂ φ₂
  let F₁ := (ModuleCat.restrictScalars (algebraMap R R₁)).mapHomologicalComplex (ComplexShape.up ℤ)
  let F₂ := (ModuleCat.restrictScalars (algebraMap R R₂)).mapHomologicalComplex (ComplexShape.up ℤ)
  have hQ₁ := finiteProjectiveComplex_restrictScalars (R := R) hP₁
  have hQ₂ := finiteProjectiveComplex_restrictScalars (R := R) hP₂
  let P := F₁.obj P₁ ⊞ F₂.obj P₂
  have hP := finiteProjectiveComplex_biprod R hQ₁ hQ₂
  let g : P ⟶ P := biprod.map (F₁.map g₁) (F₂.map g₂)
  let α₁ := restrictRepIso (R := R) e₁
  let α₂ := restrictRepIso (R := R) e₂
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{max v u} R)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let E : DerivedCategory.Q.obj P ≅ b.pt :=
    DerivedCategory.Q.mapBiprod _ _ ≪≫ biprod.mapIso α₁ α₂ ≪≫ (biprod.uniqueUpToIso _ _ hb).symm
  have hd₁ : biprod.desc b.inl b.inr ≫ b.fst = biprod.fst := by ext <;> simp
  have hd₂ : biprod.desc b.inl b.inr ≫ b.snd = biprod.snd := by ext <;> simp
  have hE₁ : E.hom ≫ b.fst = DerivedCategory.Q.map biprod.fst ≫ α₁.hom := by
    show (biprod.lift (DerivedCategory.Q.map biprod.fst) (DerivedCategory.Q.map biprod.snd) ≫
      biprod.map α₁.hom α₂.hom ≫ biprod.desc b.inl b.inr) ≫ b.fst = _
    rw [Category.assoc, Category.assoc, hd₁, biprod.map_fst, biprod.lift_fst_assoc]
  have hE₂ : E.hom ≫ b.snd = DerivedCategory.Q.map biprod.snd ≫ α₂.hom := by
    show (biprod.lift (DerivedCategory.Q.map biprod.fst) (DerivedCategory.Q.map biprod.snd) ≫
      biprod.map α₁.hom α₂.hom ≫ biprod.desc b.inl b.inr) ≫ b.snd = _
    rw [Category.assoc, Category.assoc, hd₂, biprod.map_snd, biprod.lift_snd_assoc]
  have hgE : DerivedCategory.Q.map g = E.hom ≫ φ ≫ E.inv := by
    rw [← cancel_mono E.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine hb.isLimit.hom_ext fun j => ?_
    rcases j with ⟨⟨⟩⟩
    · show (DerivedCategory.Q.map g ≫ E.hom) ≫ b.fst = (E.hom ≫ φ) ≫ b.fst
      rw [Category.assoc, Category.assoc, hE₁, h₁, reassoc_of% hE₁, ← Functor.map_comp_assoc,
        biprod.map_fst, Functor.map_comp_assoc,
        restrictRepIso_comm e₁ g₁ φ₁ hg₁]
    · show (DerivedCategory.Q.map g ≫ E.hom) ≫ b.snd = (E.hom ≫ φ) ≫ b.snd
      rw [Category.assoc, Category.assoc, hE₂, h₂, reassoc_of% hE₂, ← Functor.map_comp_assoc,
        biprod.map_snd, Functor.map_comp_assoc,
        restrictRepIso_comm e₂ g₂ φ₂ hg₂]
  have hK := isPerfect_of_iso R hP E
  refine ⟨hK, ?_, ?_⟩
  · rw [perfectDerivedCharSeries_eq_alternatingCharSeries R b.pt hK φ P hP E g hgE,
      perfectDerivedCharSeries_eq_alternatingCharSeries R₁ M₁ hM₁ φ₁ P₁ hP₁ e₁ g₁ hg₁,
      alternatingCharSeries_biprod R hQ₁ hQ₂, map_mul,
      map_alternatingCharSeries_restrictScalars hs₁,
      map_alternatingCharSeries_eq_one ha₁ hQ₂ (fun n x => ?_), mul_one]
    show algebraMap R R₂ a • (show P₂.X n from x) = 0
    rw [ha₂, zero_smul]
  · rw [perfectDerivedCharSeries_eq_alternatingCharSeries R b.pt hK φ P hP E g hgE,
      perfectDerivedCharSeries_eq_alternatingCharSeries R₂ M₂ hM₂ φ₂ P₂ hP₂ e₂ g₂ hg₂,
      alternatingCharSeries_biprod R hQ₁ hQ₂, map_mul,
      map_alternatingCharSeries_restrictScalars hs₂,
      map_alternatingCharSeries_eq_one (a := 1 - a) (by rw [map_sub, map_one, ha₂, sub_zero]) hQ₁
        (fun n x => ?_), one_mul]
    show algebraMap R R₁ (1 - a) • (show P₁.X n from x) = 0
    rw [map_sub, map_one, ha₁, sub_self, zero_smul]

end Derived

end CategoryTheory.FilteredDerived

end
