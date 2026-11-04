module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.PicardGroup

/-!
# Lifting bounded above acyclic complexes modulo an ideal

Let `R` be a commutative ring, `I ⊆ R` an ideal, and `𝒫` a class of `R`-modules such that every
member of `𝒫` is projective, `𝒫` is closed under complementary direct summands, and an
`R`-linear map between members of `𝒫` is surjective as soon as its reduction modulo `I` is.
Then every bounded above acyclic complex `E^•` of `R/I`-modules whose terms are of the form
`P/IP` with `P ∈ 𝒫` lifts to a bounded above acyclic complex `P^•` of `R`-modules with terms in
`𝒫` and `P^•/IP^• ≅ E^•`.

## Main definitions

* `LiftAcyclic.redFunctor`: The reduction functor `M ↦ M/IM` on `R`-modules.
* `LiftAcyclic.reduceComplex`: Degreewise reduction modulo `I` of a cochain complex of
  `R`-modules.
* `LiftAcyclic.LiftingHypotheses`: The three lifting hypotheses on a predicate on `R`-modules.
* `LiftAcyclic.HasTermsForm`: A complex has terms of the form `M/IM` with `M` satisfying the
  predicate.

## Main results

* `LiftAcyclic.exists_lift_acyclic_complex`: A bounded above acyclic complex of `R/I`-modules
  with terms of the form `P/IP`, `P ∈ 𝒫`, lifts to a bounded above acyclic complex with terms
  in `𝒫`.

## Implementation notes

Complexes are `CochainComplex (ModuleCat R) ℤ`; `IM` is `I • (⊤ : Submodule R M)`. "Bounded
above" is `∃ b, C.IsStrictlyLE b` and "acyclic" is `∀ i, C.ExactAt i`. The class `𝒫` is a
predicate on `ModuleCat R` that is not assumed to be closed under isomorphism, so the lift is
built with terms the given modules `M` with `E^i ≅ M/IM`: one first shows that `E^•` is
contractible, and then lifts the differentials and the contracting homotopy simultaneously by
descending recursion.

## References

* [Stacks Project, Tag 0BC9](https://stacks.math.columbia.edu/tag/0BC9)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace LiftAcyclic

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Reduction mod `I` on objects: `M ↦ M / IM` where `IM = I • (⊤ : Submodule R M)`. -/
noncomputable def redObj (M : ModuleCat.{v} R) : ModuleCat.{v} R :=
  ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))

/-- Reduction mod `I` on morphisms: the map `M/IM → N/IN` induced by `f : M → N`. -/
noncomputable def redMap {M N : ModuleCat.{v} R} (f : M ⟶ N) : redObj I M ⟶ redObj I N :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ f.hom (by
    rw [Submodule.smul_le]
    intro r hr n hn
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr trivial)

/-- The reduction functor `M ↦ M/IM` on `R`-modules. -/
noncomputable def redFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj := redObj I
  map := redMap I
  map_id := by
    intro M; ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x; rfl
  map_comp := by
    intro M N P f g; ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x; rfl

/-- `redFunctor I` sends `M` to `M/IM`. -/
theorem redFunctor_obj (M : ModuleCat.{v} R) :
    (redFunctor I).obj M = ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M))) := rfl

/-- `redFunctor I` acts on morphisms by `redMap I`. -/
theorem redFunctor_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (redFunctor I).map f = redMap I f := rfl

/-- `redMap I f` sends the class of `m` to the class of `f m`. -/
@[simp] theorem redMap_apply_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) :
    (redMap I f).hom (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f.hom m) := rfl

/-- The reduction functor `redFunctor I` is additive. -/
instance redFunctor_additive : (redFunctor I).Additive := by
  constructor
  intro M N f g
  ext x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

/-- Degreewise reduction mod `I` of a cochain complex of `R`-modules:
`P^• ↦ P^•/IP^•`. -/
noncomputable def reduceComplex :
    CochainComplex (ModuleCat.{v} R) ℤ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  (redFunctor I).mapHomologicalComplex _

/-- The reduction `reduceComplex I` of a complex has, in degree `i`, the term
`(PC.X i)/I(PC.X i)`, i.e. it is degreewise reduction mod `I`. -/
@[simp] theorem reduceComplex_obj_X (PC : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    ((reduceComplex I).obj PC).X i = (redFunctor I).obj (PC.X i) := rfl

/-- The differential of the reduction `reduceComplex I` of a complex is the reduction of its
differential. -/
@[simp] theorem reduceComplex_obj_d (PC : CochainComplex (ModuleCat.{v} R) ℤ) (i j : ℤ) :
    ((reduceComplex I).obj PC).d i j = (redFunctor I).map (PC.d i j) := rfl

/-- A predicate `P` on `R`-modules satisfies the *lifting hypotheses* relative to `I` if
every module satisfying `P` is projective, `P` is closed under complementary direct summands,
and an `R`-linear map between modules satisfying `P` is surjective as soon as its reduction
modulo `I` is. -/
structure LiftingHypotheses (P : ModuleCat.{v} R → Prop) : Prop where
  /-- Every module satisfying `P` is projective. -/
  projective : ∀ M, P M → Module.Projective R M
  /-- `P` is closed under complementary direct summands. -/
  complement : ∀ M₁ M₂, P M₁ → P (M₁ ⊞ M₂) → P M₂
  /-- An `R`-linear map between modules satisfying `P` whose reduction modulo `I` is
  surjective is itself surjective. -/
  surjective_of_reduction : ∀ (M₁ M₂ : ModuleCat.{v} R) (f : M₁ ⟶ M₂), P M₁ → P M₂ →
    Function.Surjective ((redFunctor I).map f).hom → Function.Surjective f.hom

/-- A complex `E^•` has *terms of the form `M/IM` with `P M`* if each term `E^i` is
isomorphic to `M/IM` for some `M` satisfying `P`. -/
def HasTermsForm (P : ModuleCat.{v} R → Prop) (E : CochainComplex (ModuleCat.{v} R) ℤ) :
    Prop :=
  ∀ i, ∃ M, P M ∧ Nonempty (E.X i ≅ (redFunctor I).obj M)

namespace HasTermsForm

variable {I} {P : ModuleCat.{v} R → Prop} {E : CochainComplex (ModuleCat.{v} R) ℤ}

/-- A module satisfying `P` whose reduction modulo `I` is identified with `E.X i`. -/
noncomputable def witness (h : HasTermsForm I P E) (i : ℤ) : ModuleCat.{v} R := (h i).choose

/-- The module `h.witness i` satisfies `P`. -/
theorem witness_prop (h : HasTermsForm I P E) (i : ℤ) : P (h.witness i) := (h i).choose_spec.1

/-- The identification of `E.X i` with the reduction modulo `I` of `h.witness i`. -/
noncomputable def witnessIso (h : HasTermsForm I P E) (i : ℤ) :
    E.X i ≅ (redFunctor I).obj (h.witness i) :=
  (h i).choose_spec.2.some

end HasTermsForm

/-- If `M` satisfies `P` and its reduction `M/IM` is a zero object, then `M` is a zero
object. -/
theorem isZero_of_isZero_redFunctor_obj {P : ModuleCat.{v} R → Prop}
    (hP : LiftingHypotheses I P) (M : ModuleCat.{v} R) (hM : P M)
    (h0 : Limits.IsZero ((redFunctor I).obj M)) : Limits.IsZero M := by
  have hsub0 : Subsingleton ((redFunctor I).obj M) := ModuleCat.isZero_iff_subsingleton.mp h0
  have hsurj : Function.Surjective ((0 : M ⟶ M)).hom :=
    hP.surjective_of_reduction M M 0 hM hM fun _ => ⟨0, Subsingleton.elim _ _⟩
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', ha'⟩ := hsurj a
  obtain ⟨b', hb'⟩ := hsurj b
  rw [ModuleCat.hom_zero] at ha' hb'
  simp only [LinearMap.zero_apply] at ha' hb'
  rw [← ha', ← hb']

/-- Every map between the reductions modulo `I` of a projective module and a module lifts. -/
theorem exists_redFunctor_map_eq {X Y : ModuleCat.{v} R} [CategoryTheory.Projective X]
    (gbar : (redFunctor I).obj X ⟶ (redFunctor I).obj Y) :
    ∃ f : X ⟶ Y, (redFunctor I).map f = gbar := by
  let qX : X ⟶ (redFunctor I).obj X := ModuleCat.ofHom (Submodule.mkQ _)
  let qY : Y ⟶ (redFunctor I).obj Y := ModuleCat.ofHom (Submodule.mkQ _)
  have : Epi qY := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  refine ⟨Projective.factorThru (qX ≫ gbar) qY, ?_⟩
  ext x
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R X)) x
  exact congrArg (fun (φ : X ⟶ (redFunctor I).obj Y) => φ.hom m)
    (Projective.factorThru_comp (qX ≫ gbar) qY)

/-- The reduction modulo `I` of a zero module is zero. -/
theorem isZero_redFunctor_obj {X : ModuleCat.{v} R} (hX : Limits.IsZero X) :
    Limits.IsZero ((redFunctor I).obj X) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← (redFunctor I).map_id,
    hX.eq_of_src (𝟙 _) 0, (redFunctor I).map_zero]

/-- A homological complex whose identity is homotopic to zero is exact in every degree. -/
theorem exactAt_of_homotopy_id_zero {C : Type*} [Category C] [Preadditive C]
    [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex C c} (H : Homotopy (𝟙 K) 0) (i : ι) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology, Limits.IsZero.iff_id_eq_zero]
  have hh := H.homologyMap_eq i
  rwa [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] at hh

/-- A cochain complex admitting a contracting homotopy `s` has identity homotopic to zero. -/
theorem nonempty_homotopy_id_zero_of_contracting {C : Type*} [Category C] [Preadditive C]
    (K : CochainComplex C ℤ) (s : ∀ j, K.X (j + 1) ⟶ K.X j)
    (hs : ∀ j, s j ≫ K.d j (j + 1) + K.d (j + 1) (j + 1 + 1) ≫ s (j + 1) = 𝟙 (K.X (j + 1))) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  refine ⟨Homotopy.mk (fun i j => if h : i = j + 1 then by subst h; exact s j else 0) ?_ ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    dsimp only
    rw [dite_eq_right]; omega
  · intro i
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    dsimp only [HomologicalComplex.id_f]
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) from by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel j (j + 1) from by simp),
      HomologicalComplex.zero_f, add_zero, dite_eq_left rfl, dite_eq_left rfl,
      add_comm (K.d (j + 1) (j + 1 + 1) ≫ s (j + 1)) (s j ≫ K.d j (j + 1))]
    exact (hs j).symm

/-- If `E` has terms of the form `M/IM` with `P M`, then every term of `E` is annihilated
by `I`. -/
theorem smul_top_eq_bot_of_hasTermsForm {P : ModuleCat.{v} R → Prop}
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hterms : HasTermsForm I P E) (i : ℤ) :
    (I • (⊤ : Submodule R (E.X i))) = ⊥ := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hterms i
  have hinj : Function.Injective e.hom.hom := by
    rw [← ModuleCat.mono_iff_injective]
    infer_instance
  have hkill : ∀ (r : R), r ∈ I → ∀ (y : (redFunctor I).obj M), r • y = 0 := by
    intro r hr y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr x _
  rw [Submodule.mem_bot]
  apply hinj
  rw [map_smul, map_zero, hkill r hr]

/-- A module `A` with `I • (⊤ : Submodule R A) = ⊥` is torsion by the set `I`. -/
theorem isTorsionBySet_of_smul_top_eq_bot (A : Type v) [AddCommGroup A] [Module R A]
    (h : (I • (⊤ : Submodule R A)) = ⊥) : Module.IsTorsionBySet R A (I : Set R) := fun x r => by
  have hmem : (r : R) • (x : A) ∈ (I • (⊤ : Submodule R A)) :=
    Submodule.smul_mem_smul r.2 Submodule.mem_top
  simpa [h] using hmem

/-- If `E` has terms of the form `M/IM` with `P M`, then every term of `E` has the lifting
property against surjections `Y ⟶ W` between modules annihilated by `I`. -/
theorem exists_comp_eq_of_hasTermsForm {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hterms : HasTermsForm I P E) (i : ℤ)
    (W Y : ModuleCat.{v} R) (hW : (I • (⊤ : Submodule R W)) = ⊥)
    (hY : (I • (⊤ : Submodule R Y)) = ⊥) (p : Y ⟶ W) (u : E.X i ⟶ W)
    (hp : Function.Surjective p.hom) :
    ∃ t : E.X i ⟶ Y, t ≫ p = u := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hterms i
  have hMproj : Module.Projective R M := hP.projective M hM
  have tX : Module.IsTorsionBySet R (E.X i) (I : Set R) :=
    isTorsionBySet_of_smul_top_eq_bot I (E.X i) (smul_top_eq_bot_of_hasTermsForm I hterms i)
  have tW : Module.IsTorsionBySet R W (I : Set R) := isTorsionBySet_of_smul_top_eq_bot I W hW
  have tY : Module.IsTorsionBySet R Y (I : Set R) := isTorsionBySet_of_smul_top_eq_bot I Y hY
  let : Module (R ⧸ I) (E.X i) := tX.module
  let : Module (R ⧸ I) W := tW.module
  let : Module (R ⧸ I) Y := tY.module
  have : Module.Projective (R ⧸ I) (TensorProduct R (R ⧸ I) M) := Module.Projective.tensorProduct
  have hq : Function.Surjective (algebraMap R (R ⧸ I)) := by
    rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
  have : Module.Projective (R ⧸ I) (E.X i) := Module.Projective.of_equiv <|
    LinearEquiv.extendScalarsOfSurjective hq <|
      (TensorProduct.quotTensorEquivQuotSMul M I).trans e.toLinearEquiv.symm
  let pl : (Y : Type v) →ₗ[R ⧸ I] (W : Type v) := LinearMap.extendScalarsOfSurjective hq p.hom
  let ul : (E.X i : Type v) →ₗ[R ⧸ I] (W : Type v) := LinearMap.extendScalarsOfSurjective hq u.hom
  obtain ⟨tl, htl⟩ := Module.projective_lifting_property pl ul hp
  exact ⟨ModuleCat.ofHom (tl.restrictScalars R), ModuleCat.hom_ext <| LinearMap.ext fun x =>
    LinearMap.congr_fun htl x⟩

/-- If every element of the kernel of `f` is hit by `g`, then `g` lifts to a surjection onto
the kernel of `f`. -/
private theorem surjective_kernel_lift_of_forall {X Y Z : ModuleCat.{v} R} (f : X ⟶ Y)
    (g : Z ⟶ X) (hg : g ≫ f = 0) (h : ∀ x, f.hom x = 0 → ∃ a, g.hom a = x) :
    Function.Surjective (Limits.kernel.lift f g hg).hom := fun z => by
  obtain ⟨a, ha⟩ := h ((Limits.kernel.ι f).hom z) (by simp)
  exact ⟨a, (ModuleCat.mono_iff_injective (Limits.kernel.ι f)).1 inferInstance
    (by simpa using ha)⟩

/-- For a cochain complex of modules exact at `i + 1`, the differential `d i (i + 1)` maps onto
the kernel of `d (i + 1) (i + 2)`. -/
theorem surjective_kernel_lift_d_of_exactAt (E : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ)
    (hac : E.ExactAt (i + 1)) (hdd : E.d i (i + 1) ≫ E.d (i + 1) (i + 1 + 1) = 0) :
    Function.Surjective (Limits.kernel.lift (E.d (i+1) (i+1+1)) (E.d i (i+1)) hdd).hom := by
  have hexact := (HomologicalComplex.exactAt_iff' E i (i+1) (i+1+1) (by simp) (by simp)).1 hac
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  exact surjective_kernel_lift_of_forall _ _ hdd hexact

/-- If `f : K ⟶ M` is injective and `I` annihilates `M`, then `I` annihilates `K`. -/
theorem smul_top_eq_bot_of_injective {K M : ModuleCat.{v} R} (f : K ⟶ M)
    (hf : Function.Injective f.hom) (hM : (I • (⊤ : Submodule R M)) = ⊥) :
    (I • (⊤ : Submodule R K)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr x _
  rw [Submodule.mem_bot]
  apply hf
  have : r • (f.hom x) ∈ (I • (⊤ : Submodule R M)) := Submodule.smul_mem_smul hr trivial
  simpa [hM] using this

/-- The inductive step of `nonempty_homotopy_id_zero_of_smul_top_eq_bot`: a contracting
homotopy from degree `i + 1` on extends to one from degree `i` on, changing it only in
degree `i`. -/
theorem exists_contracting_homotopy_step (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hac : ∀ i, E.ExactAt i)
    (hkilled : ∀ i, (I • (⊤ : Submodule R (E.X i))) = ⊥)
    (hlift : ∀ (i : ℤ) (W Y : ModuleCat.{v} R),
      (I • (⊤ : Submodule R W)) = ⊥ →
      (I • (⊤ : Submodule R Y)) = ⊥ →
      ∀ (p : Y ⟶ W) (u : E.X i ⟶ W), Function.Surjective p.hom →
        ∃ t : E.X i ⟶ Y, t ≫ p = u)
    (i : ℤ) (s : ∀ j, E.X (j + 1) ⟶ E.X j)
    (hInv : ∀ j, i + 1 ≤ j →
      s j ≫ E.d j (j + 1) + E.d (j + 1) (j + 1 + 1) ≫ s (j + 1) = 𝟙 (E.X (j + 1))) :
    ∃ s' : ∀ j, E.X (j+1) ⟶ E.X j, (∀ j, i ≤ j →
      s' j ≫ E.d j (j+1) + E.d (j+1) (j+1+1) ≫ s' (j+1) = 𝟙 (E.X (j+1))) ∧
      (∀ j, j ≠ i → s' j = s j) := by
  have hddi : E.d i (i+1) ≫ E.d (i+1) (i+1+1) = 0 := E.d_comp_d i (i+1) (i+1+1)
  let w : E.X (i+1) ⟶ E.X (i+1) := 𝟙 (E.X (i+1)) - E.d (i+1) (i+1+1) ≫ s (i+1)
  have hkey : s (i+1) ≫ E.d (i+1) (i+1+1) = 𝟙 (E.X
      (i+1+1)) - E.d (i+1+1) (i+1+1+1) ≫ s (i+1+1) :=
    eq_sub_iff_add_eq.2 (hInv (i+1) (by omega))
  have hwker : w ≫ E.d (i+1) (i+1+1) = 0 := by
    show (𝟙 (E.X (i+1)) - E.d (i+1) (i+1+1) ≫ s (i+1)) ≫ E.d (i+1) (i+1+1) = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hkey,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, E.d_comp_d, Limits.zero_comp,
      sub_zero, sub_self]
  let K : ModuleCat.{v} R := Limits.kernel (E.d (i+1) (i+1+1))
  let pK : E.X i ⟶ K := Limits.kernel.lift (E.d (i+1) (i+1+1)) (E.d i (i+1)) hddi
  let wK : E.X (i+1) ⟶ K := Limits.kernel.lift (E.d (i+1) (i+1+1)) w hwker
  have hpKsurj : Function.Surjective pK.hom :=
    surjective_kernel_lift_d_of_exactAt E i (hac (i+1)) hddi
  have hKkilled : (I • (⊤ : Submodule R K)) = ⊥ :=
    smul_top_eq_bot_of_injective I (Limits.kernel.ι (E.d (i+1) (i+1+1)))
      ((ModuleCat.mono_iff_injective _).1 inferInstance) (hkilled (i+1))
  obtain ⟨t, ht⟩ := hlift (i+1) K (E.X i) hKkilled (hkilled i) pK wK hpKsurj
  have htw : t ≫ E.d i (i+1) = w := by
    simpa only [Category.assoc, pK, wK, Limits.kernel.lift_ι] using
      congrArg (· ≫ Limits.kernel.ι (E.d (i+1) (i+1+1))) ht
  let s' : ∀ j, E.X (j+1) ⟶ E.X j := Function.update s i t
  have hs'i : s' i = t := Function.update_self i t s
  have hs'ne : ∀ j, j ≠ i → s' j = s j := fun j hj => Function.update_of_ne hj t s
  refine ⟨s', ?_, fun j hj => hs'ne j hj⟩
  intro j hj
  rcases eq_or_lt_of_le hj with hji | hji
  · subst hji
    rw [hs'i, hs'ne (i+1) (by omega), htw]
    show (𝟙 (E.X (i+1)) - E.d (i+1) (i+1+1) ≫ s (i+1)) + E.d (i+1) (i+1+1) ≫ s (i+1) = 𝟙 (E.X
        (i+1))
    abel
  · rw [hs'ne j (by omega), hs'ne (j+1) (by omega)]
    exact hInv j (by omega)

/-- A sequence of dependent functions `F n` that changes at stage `n` only at the index `b - n` is
constant at every index `j` from stage `(b + 1 - j).toNat` on. -/
theorem stage_stable_of_update_at {X : ℤ → Sort*} (b : ℤ) (F : ℕ → ∀ j, X j)
    (hagree : ∀ (n : ℕ) (j : ℤ), j ≠ b - n → F (n + 1) j = F n j) (j : ℤ) {m : ℕ}
    (hm : (b + 1 - j).toNat ≤ m) : F m j = F (b + 1 - j).toNat j := by
  induction m with
  | zero => rw [show (b + 1 - j).toNat = 0 by omega]
  | succ k ih =>
    rcases Nat.lt_or_ge (b + 1 - j).toNat (k + 1) with hlt | hge
    · exact (hagree k j (by omega)).trans (ih (by omega))
    · rw [show (b + 1 - j).toNat = k + 1 by omega]

/-- For a sequence as in `stage_stable_of_update_at`, the value at `j + 1` is already final at the
stage `(b + 1 - j).toNat` where the index `j` stabilizes. -/
theorem stage_succ_eq_of_update_at {X : ℤ → Sort*} (b : ℤ) (F : ℕ → ∀ j, X j)
    (hagree : ∀ (n : ℕ) (j : ℤ), j ≠ b - n → F (n + 1) j = F n j) (j : ℤ) :
    F (b + 1 - j).toNat (j + 1) = F (b + 1 - (j + 1)).toNat (j + 1) := by
  by_cases hjb : j ≤ b
  · exact stage_stable_of_update_at b F hagree (j + 1) (by omega)
  · rw [show (b + 1 - j).toNat = 0 by omega, show (b + 1 - (j + 1)).toNat = 0 by omega]

/-- **Descending recursion on `ℤ`.** Let `Q j` relate the values in degrees `j` and `j + 1` of a
dependent family. If some family satisfies `Q` in all degrees above `b`, and every family
satisfying `Q` from degree `i + 1` on can be modified in degree `i` alone so as to satisfy `Q`
from degree `i` on, then some family satisfies `Q` in every degree. -/
theorem exists_forall_of_descending_recursion {X : ℤ → Sort*} (Q : ∀ j, X j → X (j + 1) → Prop)
    (b : ℤ) (hbase : ∃ F : ∀ j, X j, ∀ j, b + 1 ≤ j → Q j (F j) (F (j + 1)))
    (hstep : ∀ (i : ℤ) (F : ∀ j, X j), (∀ j, i + 1 ≤ j → Q j (F j) (F (j + 1))) →
      ∃ F' : ∀ j, X j, (∀ j, i ≤ j → Q j (F' j) (F' (j + 1))) ∧ ∀ j, j ≠ i → F' j = F j) :
    ∃ F : ∀ j, X j, ∀ j, Q j (F j) (F (j + 1)) := by
  classical
  let Bdl : ℕ → Sort _ :=
    fun n => Σ' F : ∀ j, X j, ∀ j, b + 1 - (n : ℤ) ≤ j → Q j (F j) (F (j + 1))
  let stepFun : ∀ n : ℕ, Bdl n → Bdl (n + 1) := fun n prev =>
    let res := hstep (b - (n : ℤ)) prev.1 fun j hj => prev.2 j (by omega)
    ⟨res.choose, fun j hj => res.choose_spec.1 j (by omega)⟩
  let coreF : ∀ n, Bdl n := fun n =>
    Nat.rec (⟨hbase.choose, fun j hj => hbase.choose_spec j (by omega)⟩ : Bdl 0) stepFun n
  have hagree : ∀ (n : ℕ) (j : ℤ), j ≠ b - (n : ℤ) → (coreF (n + 1)).1 j = (coreF n).1 j := by
    intro n j hj
    exact (hstep (b - (n : ℤ)) (coreF n).1 fun k hk =>
      (coreF n).2 k (by omega)).choose_spec.2 j hj
  have hsucc : ∀ j : ℤ, (coreF (b + 1 - j).toNat).1 (j + 1)
      = (coreF (b + 1 - (j + 1)).toNat).1 (j + 1) :=
    stage_succ_eq_of_update_at b (fun n => (coreF n).1) hagree
  refine ⟨fun j => (coreF (b + 1 - j).toNat).1 j, fun j => ?_⟩
  show Q j ((coreF (b + 1 - j).toNat).1 j) ((coreF (b + 1 - (j + 1)).toNat).1 (j + 1))
  rw [← hsucc j]
  exact (coreF (b + 1 - j).toNat).2 j (by omega)

/-- A bounded above acyclic complex whose terms are annihilated by `I` and have the lifting
property against surjections between modules annihilated by `I` is contractible: its identity is
homotopic to zero. -/
theorem nonempty_homotopy_id_zero_of_smul_top_eq_bot (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbdd : ∃ b, E.IsStrictlyLE b) (hac : ∀ i, E.ExactAt i)
    (hkilled : ∀ i, (I • (⊤ : Submodule R (E.X i))) = ⊥)
    (hlift : ∀ (i : ℤ) (W Y : ModuleCat.{v} R),
      (I • (⊤ : Submodule R W)) = ⊥ →
      (I • (⊤ : Submodule R Y)) = ⊥ →
      ∀ (p : Y ⟶ W) (u : E.X i ⟶ W), Function.Surjective p.hom →
        ∃ t : E.X i ⟶ Y, t ≫ p = u) :
    Nonempty (Homotopy (𝟙 E) 0) := by
  classical
  obtain ⟨b, hbE⟩ := hbdd
  have hzero : ∀ i, b < i → Limits.IsZero (E.X i) := by
    rwa [CochainComplex.isStrictlyLE_iff] at hbE
  obtain ⟨s, hs⟩ := exists_forall_of_descending_recursion (X := fun j => E.X (j + 1) ⟶ E.X j)
    (fun j sj sj' => sj ≫ E.d j (j + 1) + E.d (j + 1) (j + 1 + 1) ≫ sj' = 𝟙 (E.X (j + 1))) b
    ⟨fun _ => 0, fun j hj => by
      simpa only [Limits.zero_comp, Limits.comp_zero, add_zero] using
        ((hzero (j + 1) (by omega)).eq_of_src _ _).symm⟩
    (exists_contracting_homotopy_step I E hac hkilled hlift)
  exact nonempty_homotopy_id_zero_of_contracting E s hs

/-- A bounded above acyclic complex with terms of the form `M/IM` with `P M` is contractible:
its identity is homotopic to zero. -/
theorem nonempty_homotopy_id_zero_of_hasTermsForm {P : ModuleCat.{v} R → Prop}
    (hP : LiftingHypotheses I P) {E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hbdd : ∃ b, E.IsStrictlyLE b) (hac : ∀ i, E.ExactAt i) (hterms : HasTermsForm I P E) :
    Nonempty (Homotopy (𝟙 E) 0) :=
  nonempty_homotopy_id_zero_of_smul_top_eq_bot I E hbdd hac
    (smul_top_eq_bot_of_hasTermsForm I hterms) (exists_comp_eq_of_hasTermsForm I hP hterms)

/-- Let `δ₁ : A ⟶ M` and `δ₂ : M ⟶ B` with `δ₁ ≫ δ₂ = 0` and `M` satisfying `P`, and let
`s : B ⟶ M` and `σ : M ⟶ A` with `δ₂ ≫ s ≫ δ₂ = δ₂`. If the reduction of `σ ≫ δ₁ + δ₂ ≫ s`
modulo `I` is surjective, then every element of the kernel of `δ₂` lies in the image of `δ₁`. -/
theorem exists_preimage_of_apply_eq_zero {P : ModuleCat.{v} R → Prop}
    (hP : LiftingHypotheses I P) {A M B : ModuleCat.{v} R} (hM : P M)
    (δ₁ : A ⟶ M) (δ₂ : M ⟶ B) (s : B ⟶ M) (σ : M ⟶ A) (hdd : δ₁ ≫ δ₂ = 0)
    (hsB : δ₂ ≫ s ≫ δ₂ = δ₂)
    (hΘ : Function.Surjective ((redFunctor I).map (σ ≫ δ₁ + δ₂ ≫ s)).hom) :
    ∀ z : M, δ₂.hom z = 0 → ∃ a : A, δ₁.hom a = z := by
  have hΘsurj : Function.Surjective ((σ ≫ δ₁ + δ₂ ≫ s)).hom :=
    hP.surjective_of_reduction M M (σ ≫ δ₁ + δ₂ ≫ s) hM hM hΘ
  have hdd' : ∀ a : A, δ₂.hom (δ₁.hom a) = 0 := by
    intro a
    have := congrArg (fun g => g.hom a) hdd
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hsB' : ∀ x : M, δ₂.hom (s.hom (δ₂.hom x)) = δ₂.hom x := by
    intro x
    have := congrArg (fun g => g.hom x) hsB
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  intro z hz
  obtain ⟨m, hm⟩ := hΘsurj z
  have hexp : (σ ≫ δ₁ + δ₂ ≫ s).hom m = δ₁.hom (σ.hom m) + s.hom (δ₂.hom m) := by
    simp [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply]
  rw [hexp] at hm
  have hd2 : δ₂.hom z = δ₂.hom (s.hom (δ₂.hom m)) := by
    rw [← hm]
    rw [map_add, hdd' (σ.hom m), zero_add]
  have hδ₂m : δ₂.hom m = 0 := by
    have : δ₂.hom (s.hom (δ₂.hom m)) = 0 := by rw [← hd2]; exact hz
    rw [hsB' m] at this
    exact this
  refine ⟨σ.hom m, ?_⟩
  rw [← hm, hδ₂m, map_zero, add_zero]

/-- Let `δ : A ⟶ Mid`, `δn : Mid ⟶ Nxt`, `sn : Nxt ⟶ Mid` and `s0 : Mid ⟶ A` with `Mid`
satisfying `P`, `δ ≫ δn = 0` and `s0 ≫ δ = 𝟙 - δn ≫ sn`. If `htgt : Mid/I·Mid ⟶ A/IA` satisfies
`htgt ≫ red δ + red δn ≫ red sn = 𝟙`, where `red` is reduction modulo `I`, then there is
`c : Mid ⟶ A` with `c ≫ δ = 0` and `red (s0 + c) = htgt`. -/
theorem exists_homotopy_correction {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {A Mid Nxt : ModuleCat.{v} R} (hMid : P Mid)
    (δ : A ⟶ Mid) (δn : Mid ⟶ Nxt) (sn : Nxt ⟶ Mid) (s0 : Mid ⟶ A)
    (htgt : (redFunctor I).obj Mid ⟶ (redFunctor I).obj A) (hδδn : δ ≫ δn = 0)
    (hC0 : s0 ≫ δ = 𝟙 Mid - δn ≫ sn)
    (hredId : htgt ≫ (redFunctor I).map δ
      + (redFunctor I).map δn ≫ (redFunctor I).map sn
        = 𝟙 ((redFunctor I).obj Mid)) :
    ∃ c : Mid ⟶ A, c ≫ δ = 0 ∧ (redFunctor I).map (s0 + c) = htgt := by
  have : Module.Projective R (Mid : Type v) := hP.projective Mid hMid
  set d : (redFunctor I).obj Mid ⟶ (redFunctor I).obj A := htgt - (redFunctor I).map s0 with hd_def
  have hstep1 : d ≫ (redFunctor I).map δ = 0 := by
    have hredC0 : (redFunctor I).map s0 ≫ (redFunctor I).map δ
        = 𝟙 ((redFunctor I).obj Mid) - (redFunctor I).map δn ≫ (redFunctor I).map sn := by
      rw [← (redFunctor I).map_comp, hC0, Functor.map_sub, (redFunctor I).map_comp,
        (redFunctor I).map_id]
    have hhtgt : htgt ≫ (redFunctor I).map δ
        = 𝟙 ((redFunctor I).obj Mid) - (redFunctor I).map δn ≫ (redFunctor I).map sn :=
      eq_sub_iff_add_eq.2 hredId
    rw [hd_def, Preadditive.sub_comp, hhtgt, hredC0, sub_self]
  obtain ⟨e, hrede⟩ := exists_redFunctor_map_eq I d
  refine ⟨e - e ≫ δ ≫ s0, ?_, ?_⟩
  · have key : δ ≫ s0 ≫ δ = δ := by
      rw [hC0, Preadditive.comp_sub, Category.comp_id, ← Category.assoc δ δn sn, hδδn,
        Limits.zero_comp, sub_zero]
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, key, sub_self]
  · have hredc : (redFunctor I).map (e - e ≫ δ ≫ s0) = d := by
      rw [Functor.map_sub, hrede, (redFunctor I).map_comp, (redFunctor I).map_comp,
        ← Category.assoc, hrede, hstep1, Limits.zero_comp, sub_zero]
    rw [(redFunctor I).map_add, hredc, hd_def, add_sub_cancel]

/-- The invariant of the descending recursion in `exists_lift_families`: from degree `i` on,
`δ` and `s` satisfy the complex and homotopy identities and reduce to `g` and `h`. -/
structure LiftInvariant (M : ℤ → ModuleCat.{v} R)
    (g : ∀ i, (redFunctor I).obj (M i) ⟶ (redFunctor I).obj (M (i + 1)))
    (h : ∀ j, (redFunctor I).obj (M (j + 1)) ⟶ (redFunctor I).obj (M j))
    (δ : ∀ j, M j ⟶ M (j + 1)) (s : ∀ j, M (j + 1) ⟶ M j) (i : ℤ) : Prop where
  /-- From degree `i` on, consecutive `δ`s compose to zero. -/
  d_comp_d : ∀ j, i ≤ j → δ j ≫ δ (j + 1) = 0
  /-- From degree `i` on, `δ` reduces to `g` modulo `I`. -/
  red_d : ∀ j, i ≤ j → (redFunctor I).map (δ j) = g j
  /-- From degree `i` on, `s` is a contracting homotopy for `δ`. -/
  homotopy_id : ∀ j, i ≤ j → s j ≫ δ j + δ (j + 1) ≫ s (j + 1) = 𝟙 (M (j + 1))
  /-- From degree `i` on, `s` reduces to `h` modulo `I`. -/
  red_s : ∀ j, i ≤ j → (redFunctor I).map (s j) = h j

/-- Changing `δ` and `s` in degree `i` to maps `δi`, `si` satisfying the degree-`i` identities
extends the invariant `LiftInvariant` from degree `i + 1` to degree `i`. -/
theorem LiftInvariant.update (M : ℤ → ModuleCat.{v} R)
    (g : ∀ i, (redFunctor I).obj (M i) ⟶ (redFunctor I).obj (M (i + 1)))
    (h : ∀ j, (redFunctor I).obj (M (j + 1)) ⟶ (redFunctor I).obj (M j))
    (i : ℤ) (δ : ∀ j, M j ⟶ M (j + 1)) (s : ∀ j, M (j + 1) ⟶ M j)
    (hinv : LiftInvariant I M g h δ s (i + 1)) (δi : M i ⟶ M (i + 1)) (si : M (i + 1) ⟶ M i)
    (hDi : δi ≫ δ (i + 1) = 0) (hRi : (redFunctor I).map δi = g i)
    (hCi : si ≫ δi + δ (i + 1) ≫ s (i + 1) = 𝟙 (M (i + 1)))
    (hRHi : (redFunctor I).map si = h i) :
    LiftInvariant I M g h (Function.update δ i δi) (Function.update s i si) i := by
  obtain ⟨hD, hR, hC, hRH⟩ := hinv
  have hδne : ∀ j, j ≠ i → Function.update δ i δi j = δ j := fun _ hj =>
    Function.update_of_ne hj _ _
  have hsne : ∀ j, j ≠ i → Function.update s i si j = s j := fun _ hj =>
    Function.update_of_ne hj _ _
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
    rcases eq_or_lt_of_le hj with rfl | hji
  · rwa [Function.update_self, hδne (i + 1) (by omega)]
  · rw [hδne j (by omega), hδne (j + 1) (by omega)]
    exact hD j (by omega)
  · rwa [Function.update_self]
  · rw [hδne j (by omega)]; exact hR j (by omega)
  · rwa [Function.update_self, Function.update_self, hδne (i + 1) (by omega),
      hsne (i + 1) (by omega)]
  · rw [hsne j (by omega), hδne j (by omega), hδne (j + 1) (by omega), hsne (j + 1) (by omega)]
    exact hC j (by omega)
  · rwa [Function.update_self]
  · rw [hsne j (by omega)]; exact hRH j (by omega)

/-- The inductive step of `exists_lift_families`: the invariant in degree `i + 1` extends to
degree `i`, changing `δ` and `s` only in degree `i`. -/
theorem LiftInvariant.step {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    (M : ℤ → ModuleCat.{v} R) (hM : ∀ i, P (M i))
    (g : ∀ i, (redFunctor I).obj (M i) ⟶ (redFunctor I).obj (M (i + 1)))
    (h : ∀ j, (redFunctor I).obj (M (j + 1)) ⟶ (redFunctor I).obj (M j))
    (hgg : ∀ i, g i ≫ g (i + 1) = 0)
    (hredId : ∀ j, h j ≫ g j + g (j + 1) ≫ h (j + 1) = 𝟙 ((redFunctor I).obj (M (j + 1))))
    (i : ℤ) (δ : ∀ j, M j ⟶ M (j + 1)) (s : ∀ j, M (j + 1) ⟶ M j)
    (hinv : LiftInvariant I M g h δ s (i + 1)) :
    ∃ δ' s', LiftInvariant I M g h δ' s' i ∧ (∀ j, j ≠ i → δ' j = δ j) ∧
      (∀ j, j ≠ i → s' j = s j) := by
  obtain ⟨hD, hR, hC, hRH⟩ := hinv
  have hproj : ∀ i, Module.Projective R (M i : Type v) := fun i => hP.projective (M i) (hM i)
  obtain ⟨δtil, hδtil⟩ := exists_redFunctor_map_eq I (X := M i) (Y := M (i + 1)) (g i)
  let δi : M i ⟶ M (i + 1) := δtil ≫ (𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1))
  have hRi : (redFunctor I).map δi = g i := by
    have h1 : (redFunctor I).map (𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1))
        = 𝟙 _ - g (i + 1) ≫ h (i + 1) := by
      rw [Functor.map_sub, (redFunctor I).map_id, (redFunctor I).map_comp, hR (i + 1) (by omega),
        hRH (i + 1) (by omega)]
    show (redFunctor I).map (δtil ≫ (𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1))) = g i
    rw [(redFunctor I).map_comp, hδtil, h1, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hgg i, Limits.zero_comp, sub_zero]
  have hsB : δ (i + 1) ≫ s (i + 1) ≫ δ (i + 1) = δ (i + 1) := by
    have hkey : s (i + 1) ≫ δ (i + 1) = 𝟙 (M (i + 1 + 1)) - δ (i + 1 + 1) ≫ s (i + 1 + 1) :=
      eq_sub_iff_add_eq.2 (hC (i + 1) (by omega))
    rw [hkey, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hD (i + 1) (by omega), Limits.zero_comp, sub_zero]
  have hDi : δi ≫ δ (i + 1) = 0 := by
    show (δtil ≫ (𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1))) ≫ δ (i + 1) = 0
    rw [Category.assoc, Preadditive.sub_comp, Category.id_comp, Category.assoc, hsB, sub_self,
      Limits.comp_zero]
  obtain ⟨σ, hσ⟩ := exists_redFunctor_map_eq I (X := M (i + 1)) (Y := M i) (h i)
  let w : M (i + 1) ⟶ M (i + 1) := 𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1)
  have hΘ : Function.Surjective
      ((redFunctor I).map (σ ≫ δi + δ (i + 1) ≫ s (i + 1))).hom := by
    have hredΘ : (redFunctor I).map (σ ≫ δi + δ (i + 1) ≫ s (i + 1))
        = 𝟙 ((redFunctor I).obj (M (i + 1))) := by
      rw [(redFunctor I).map_add, (redFunctor I).map_comp σ δi,
        (redFunctor I).map_comp (δ (i + 1)) (s (i + 1)), hσ, hRi,
        hR (i + 1) (by omega), hRH (i + 1) (by omega)]
      exact hredId i
    rw [hredΘ]
    exact fun y => ⟨y, rfl⟩
  have hsurjcyc : ∀ z : M (i + 1), (δ (i + 1)).hom z = 0 → ∃ a : M i, δi.hom a = z :=
    exists_preimage_of_apply_eq_zero I hP (hM (i + 1)) δi (δ (i + 1)) (s (i + 1)) σ hDi hsB hΘ
  have hwker : w ≫ δ (i + 1) = 0 := by
    show (𝟙 (M (i + 1)) - δ (i + 1) ≫ s (i + 1)) ≫ δ (i + 1) = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hsB, sub_self]
  let K : ModuleCat.{v} R := Limits.kernel (δ (i + 1))
  let δK : M i ⟶ K := Limits.kernel.lift (δ (i + 1)) δi hDi
  have hδKι : δK ≫ Limits.kernel.ι (δ (i + 1)) = δi := Limits.kernel.lift_ι _ _ _
  let wK : M (i + 1) ⟶ K := Limits.kernel.lift (δ (i + 1)) w hwker
  have hwKι : wK ≫ Limits.kernel.ι (δ (i + 1)) = w := Limits.kernel.lift_ι _ _ _
  have hδKepi : Epi δK := (ModuleCat.epi_iff_surjective _).2
    (surjective_kernel_lift_of_forall _ _ hDi hsurjcyc)
  let si : M (i + 1) ⟶ M i := Projective.factorThru wK δK
  have hsiδK : si ≫ δK = wK := Projective.factorThru_comp wK δK
  have hsiδi : si ≫ δi = w := by
    rw [← hδKι, ← Category.assoc, hsiδK, hwKι]
  have hredId' : h i ≫ (redFunctor I).map δi
      + (redFunctor I).map (δ (i + 1)) ≫ (redFunctor I).map (s (i + 1))
        = 𝟙 ((redFunctor I).obj (M (i + 1))) := by
    rw [hRi, hR (i + 1) (by omega), hRH (i + 1) (by omega)]; exact hredId i
  obtain ⟨c, hcδi, hcRH⟩ :=
    exists_homotopy_correction I hP (hM (i + 1)) δi (δ (i + 1)) (s (i + 1)) si (h i) hDi hsiδi
      hredId'
  have hsicδi : (si + c) ≫ δi = w := by
    rw [Preadditive.add_comp, hcδi, add_zero, hsiδi]
  exact ⟨_, _, LiftInvariant.update I M g h i δ s ⟨hD, hR, hC, hRH⟩ δi (si + c) hDi hRi
    (by rw [hsicδi, sub_add_cancel]) hcRH,
    fun j hj => Function.update_of_ne hj _ _, fun j hj => Function.update_of_ne hj _ _⟩

/-- Given modules `M i` satisfying `P` and vanishing above `b`, together with families `g` of
reduced differentials and `h` of reduced contracting homotopies, there are families `δ` and `s`
of maps satisfying the complex and homotopy identities in every degree and reducing to `g`
and `h`. -/
theorem exists_lift_families {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    (M : ℤ → ModuleCat.{v} R) (hM : ∀ i, P (M i))
    (b : ℤ) (hzero : ∀ i, b < i → Limits.IsZero (M i))
    (g : ∀ i, (redFunctor I).obj (M i) ⟶ (redFunctor I).obj (M (i + 1)))
    (h : ∀ j, (redFunctor I).obj (M (j + 1)) ⟶ (redFunctor I).obj (M j))
    (hgg : ∀ i, g i ≫ g (i + 1) = 0)
    (hredId : ∀ j, h j ≫ g j + g (j + 1) ≫ h (j + 1) = 𝟙 ((redFunctor I).obj (M (j + 1)))) :
    ∃ (δ : ∀ i, M i ⟶ M (i + 1)) (s : ∀ i, M (i + 1) ⟶ M i),
      (∀ i, δ i ≫ δ (i + 1) = 0) ∧
      (∀ j, s j ≫ δ j + δ (j + 1) ≫ s (j + 1) = 𝟙 (M (j + 1))) ∧
      (∀ i, (redFunctor I).map (δ i) = g i) ∧
      (∀ j, (redFunctor I).map (s j) = h j) := by
  classical
  have hredMzero : ∀ j, b < j → Limits.IsZero ((redFunctor I).obj (M j)) :=
    fun j hj => isZero_redFunctor_obj I (hzero j hj)
  obtain ⟨F, hF⟩ := exists_forall_of_descending_recursion
    (X := fun j => (M j ⟶ M (j + 1)) × (M (j + 1) ⟶ M j))
    (fun j p q => p.1 ≫ q.1 = 0 ∧ (redFunctor I).map p.1 = g j ∧
      p.2 ≫ p.1 + q.1 ≫ q.2 = 𝟙 (M (j + 1)) ∧ (redFunctor I).map p.2 = h j) b
    (by
      refine ⟨fun _ => ⟨0, 0⟩, fun j hj => ⟨by simp, ?_, ?_, ?_⟩⟩
      · simpa only [Functor.map_zero] using ((hredMzero j (by omega)).eq_of_src _ _).symm
      · simpa only [Limits.zero_comp, Limits.comp_zero, add_zero] using
          ((hzero (j + 1) (by omega)).eq_of_src _ _).symm
      · simpa only [Functor.map_zero] using (hredMzero j (by omega)).eq_of_tgt _ _)
    (fun i F hInv => by
      obtain ⟨δ', s', hinv', hδ', hs'⟩ := LiftInvariant.step I hP M hM g h hgg hredId i
        (fun j => (F j).1) (fun j => (F j).2)
        ⟨fun j hj => (hInv j hj).1, fun j hj => (hInv j hj).2.1,
          fun j hj => (hInv j hj).2.2.1, fun j hj => (hInv j hj).2.2.2⟩
      exact ⟨fun j => (δ' j, s' j), fun j hj => ⟨hinv'.d_comp_d j hj, hinv'.red_d j hj,
        hinv'.homotopy_id j hj, hinv'.red_s j hj⟩,
        fun j hj => by
          show (δ' j, s' j) = F j
          rw [hδ' j hj, hs' j hj]⟩)
  exact ⟨fun j => (F j).1, fun j => (F j).2, fun j => (hF j).1, fun j => (hF j).2.2.1,
    fun j => (hF j).2.1, fun j => (hF j).2.2.2⟩

/-- Let `E` be strictly bounded above by `b`, with identity homotopic to zero and terms of the
form `M/IM` with `P M`. Then there are modules `M i` satisfying `P` and vanishing above `b`, maps
`δ i : M i ⟶ M (i+1)` with `δ i ≫ δ (i+1) = 0`, maps `s j : M (j+1) ⟶ M j` with
`s j ≫ δ j + δ (j+1) ≫ s (j+1) = 𝟙`, and isomorphisms `ε i : M i/I ≅ E.X i` intertwining the
reductions of the `δ i` with the differentials of `E`. -/
theorem exists_lift_bundle {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (b : ℤ) (hbE : E.IsStrictlyLE b)
    (hHE : Homotopy (𝟙 E) 0) (hterms : HasTermsForm I P E) :
    ∃ (M : ℤ → ModuleCat.{v} R) (δ : ∀ i, M i ⟶ M (i + 1))
      (s : ∀ i, M (i + 1) ⟶ M i)
      (ε : ∀ i, (redFunctor I).obj (M i) ≅ E.X i),
      (∀ i, P (M i)) ∧
      (∀ i, b < i → Limits.IsZero (M i)) ∧
      (∀ i, δ i ≫ δ (i + 1) = 0) ∧
      (∀ j, s j ≫ δ j + δ (j + 1) ≫ s (j + 1) = 𝟙 (M (j + 1))) ∧
      (∀ i, (redFunctor I).map (δ i) ≫ (ε (i + 1)).hom = (ε i).hom ≫ E.d i (i + 1)) := by
  classical
  let M : ℤ → ModuleCat.{v} R := hterms.witness
  have hM : ∀ i, P (M i) := hterms.witness_prop
  let ε : ∀ i, (redFunctor I).obj (M i) ≅ E.X i := fun i => (hterms.witnessIso i).symm
  have hzero : ∀ i, b < i → Limits.IsZero (M i) := by
    intro i hi
    rw [CochainComplex.isStrictlyLE_iff] at hbE
    exact isZero_of_isZero_redFunctor_obj I hP (M i) (hM i) ((hbE i hi).of_iso (ε i))
  let g : ∀ i, (redFunctor I).obj (M i) ⟶ (redFunctor I).obj (M (i + 1)) :=
    fun i => (ε i).hom ≫ E.d i (i + 1) ≫ (ε (i + 1)).inv
  let h : ∀ j, (redFunctor I).obj (M (j + 1)) ⟶ (redFunctor I).obj (M j) :=
    fun j => (ε (j + 1)).hom ≫ hHE.hom (j + 1) j ≫ (ε j).inv
  have hgg : ∀ i, g i ≫ g (i + 1) = 0 := by
    intro i
    simp only [g, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (E.d i (i + 1)), HomologicalComplex.d_comp_d]
    simp
  have hredId : ∀ j, h j ≫ g j + g (j + 1) ≫ h (j + 1) = 𝟙 ((redFunctor I).obj (M (j + 1))) := by
    intro j
    have hcomm := hHE.comm (j + 1)
    rw [HomologicalComplex.id_f,
      dNext_eq hHE.hom (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) from by simp),
      prevD_eq hHE.hom (show (ComplexShape.up ℤ).Rel j (j + 1) from by simp),
      HomologicalComplex.zero_f, add_zero] at hcomm
    simp only [g, h, Category.assoc, Iso.inv_hom_id_assoc]
    have key : hHE.hom (j + 1) j ≫ E.d j (j + 1) ≫ (ε (j + 1)).inv
        + E.d (j + 1) (j + 1 + 1) ≫ hHE.hom (j + 1 + 1) (j + 1) ≫ (ε (j + 1)).inv
        = (ε (j + 1)).inv := by
      rw [← Category.assoc (hHE.hom (j + 1) j), ← Category.assoc (E.d (j + 1) (j + 1 + 1)),
        ← Preadditive.add_comp, add_comm (hHE.hom (j + 1) j ≫ E.d j (j + 1)),
        ← hcomm, Category.id_comp]
    rw [show (ε (j + 1)).hom ≫ hHE.hom (j + 1) j ≫ E.d j (j + 1) ≫ (ε (j + 1)).inv
          + (ε (j + 1)).hom ≫ E.d (j + 1) (j + 1 + 1) ≫ hHE.hom (j + 1 + 1) (j + 1) ≫ (ε (j +
              1)).inv
        = (ε (j + 1)).hom ≫ (hHE.hom (j + 1) j ≫ E.d j (j + 1) ≫ (ε (j + 1)).inv
          + E.d (j + 1) (j + 1 + 1) ≫ hHE.hom (j + 1 + 1) (j + 1) ≫ (ε (j + 1)).inv)
        from by rw [Preadditive.comp_add]]
    rw [key, Iso.hom_inv_id]
  obtain ⟨δ, s, hdd, hC, hRred, _⟩ :=
    exists_lift_families I hP M hM b hzero g h hgg hredId
  refine ⟨M, δ, s, ε, hM, hzero, hdd, hC, ?_⟩
  intro i
  rw [hRred i]
  simp only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let `E` be strictly bounded above by `b`, with identity homotopic to zero and terms of the
form `M/IM` with `P M`. Then there are modules `M i` satisfying `P` and vanishing above `b`, and
maps `δ i : M i ⟶ M (i+1)` with `δ i ≫ δ (i+1) = 0`, such that the complex
`CochainComplex.of M δ` has identity homotopic to zero and reduction modulo `I` isomorphic
to `E`. -/
theorem exists_lift_data {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (b : ℤ) (hbE : E.IsStrictlyLE b)
    (hHE : Homotopy (𝟙 E) 0) (hterms : HasTermsForm I P E) :
    ∃ (M : ℤ → ModuleCat.{v} R) (δ : ∀ i, M i ⟶ M (i + 1))
      (hdd : ∀ i, δ i ≫ δ (i + 1) = 0),
      (∀ i, P (M i)) ∧
      (∀ i, b < i → Limits.IsZero (M i)) ∧
      Nonempty (Homotopy (𝟙 (CochainComplex.of M δ hdd)) 0) ∧
      Nonempty ((reduceComplex I).obj (CochainComplex.of M δ hdd) ≅ E) := by
  obtain ⟨M, δ, s, ε, hPM, hzero, hdd, hC, hR⟩ :=
    exists_lift_bundle I hP b hbE hHE hterms
  refine ⟨M, δ, hdd, hPM, hzero, ?_, ?_⟩
  · have hd : ∀ k, (CochainComplex.of M δ hdd).d k (k + 1) = δ k := by
      intro k; apply CochainComplex.of_d
    refine nonempty_homotopy_id_zero_of_contracting _ s fun j => ?_
    rw [hd j, hd (j + 1)]
    exact hC j
  · refine ⟨HomologicalComplex.Hom.isoOfComponents ε ?_⟩
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    have hd : ((reduceComplex I).obj (CochainComplex.of M δ hdd)).d i (i + 1)
        = (redFunctor I).map (δ i) := by
      rw [reduceComplex_obj_d]
      congr 1
      apply CochainComplex.of_d
    rw [hd]
    exact (hR i).symm

/-- A bounded above complex `E` with identity homotopic to zero and terms of the form `M/IM`
with `P M` lifts to a bounded above complex with terms satisfying `P`, identity homotopic to
zero, and reduction modulo `I` isomorphic to `E`. -/
theorem exists_lift_of_homotopy_id_zero {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hbdd : ∃ b, E.IsStrictlyLE b)
    (hHE : Nonempty (Homotopy (𝟙 E) 0)) (hterms : HasTermsForm I P E) :
    ∃ (PC : CochainComplex (ModuleCat.{v} R) ℤ),
      (∀ i, P (PC.X i)) ∧
      (∃ b, PC.IsStrictlyLE b) ∧
      Nonempty (Homotopy (𝟙 PC) 0) ∧
      Nonempty ((reduceComplex I).obj PC ≅ E) := by
  obtain ⟨b, hbE⟩ := hbdd
  obtain ⟨H⟩ := hHE
  obtain ⟨M, δ, hdd, hPM, hzero, hHpc, hiso⟩ :=
    exists_lift_data I hP b hbE H hterms
  refine ⟨CochainComplex.of M δ hdd, ?_, ⟨b, ?_⟩, hHpc, hiso⟩
  · intro i
    rw [CochainComplex.of_X]
    exact hPM i
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.of_X]
    exact hzero i hi

/-- A bounded above acyclic complex `E` with terms of the form `M/IM` with `P M` lifts to a
bounded above acyclic complex with terms satisfying `P` whose reduction modulo `I` is isomorphic
to `E`. -/
theorem exists_lift_of_exactAt {P : ModuleCat.{v} R → Prop} (hP : LiftingHypotheses I P)
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hbdd : ∃ b, E.IsStrictlyLE b)
    (hac : ∀ i, E.ExactAt i) (hterms : HasTermsForm I P E) :
    ∃ (PC : CochainComplex (ModuleCat.{v} R) ℤ),
      (∀ i, P (PC.X i)) ∧
      (∃ b, PC.IsStrictlyLE b) ∧
      (∀ i, PC.ExactAt i) ∧
      Nonempty ((reduceComplex I).obj PC ≅ E) := by
  have hHE : Nonempty (Homotopy (𝟙 E) 0) :=
    nonempty_homotopy_id_zero_of_hasTermsForm I hP hbdd hac hterms
  obtain ⟨PC, hterm, hb, ⟨H⟩, hiso⟩ :=
    exists_lift_of_homotopy_id_zero I hP hbdd hHE hterms
  exact ⟨PC, hterm, hb, fun i => exactAt_of_homotopy_id_zero H i, hiso⟩

open scoped ChangeOfRings

private noncomputable instance quotientRestrictFull :
    (ModuleCat.restrictScalars.{max v u, u, u} (Ideal.Quotient.mk I)).Full where
  map_surjective {M N} f := by
    let g : M ⟶ N := ModuleCat.ofHom {
      toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro s m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact f.hom.map_smul r m
    }
    refine ⟨g, ?_⟩
    ext x
    rfl

private noncomputable def redCompIso (M : ModuleCat.{max v u} R) :
    (ModuleCat.restrictScalars.{max v u, u, u} (Ideal.Quotient.mk I)).obj
      ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M) ≅
      (redFunctor I).obj M :=
  LinearEquiv.toModuleIso (TensorProduct.quotTensorEquivQuotSMul M I)

private noncomputable def redCompNatIso :
    (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)) ⋙
      (ModuleCat.restrictScalars.{max v u, u, u} (Ideal.Quotient.mk I)) ≅
      redFunctor I :=
  NatIso.ofComponents (redCompIso I) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (TensorProduct.quotTensorEquivQuotSMul N I)
      (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom x) =
      ((redFunctor I).map f).hom ((TensorProduct.quotTensorEquivQuotSMul M I) x)
    induction x using TensorProduct.induction_on with
    | zero =>
      calc
        (TensorProduct.quotTensorEquivQuotSMul N I)
            (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom 0) =
              0 := by
          rw [map_zero, map_zero]
        _ = _ := by rw [map_zero, map_zero]
    | tmul s m =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      let : Module R (R ⧸ I) := Module.compHom (R ⧸ I) (Ideal.Quotient.mk I)
      simp only [ModuleCat.ExtendScalars.map_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
      change (Submodule.Quotient.mk (r • f.hom m) : N ⧸ I • (⊤ : Submodule R N)) =
        Submodule.Quotient.mk (f.hom (r • m))
      exact congrArg (Submodule.Quotient.mk : N → N ⧸ I • (⊤ : Submodule R N))
        (f.hom.map_smul r m).symm
    | add x y hx hy =>
      calc
        (TensorProduct.quotTensorEquivQuotSMul N I)
            (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom (x + y)) =
          (TensorProduct.quotTensorEquivQuotSMul N I)
              (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom x) +
          (TensorProduct.quotTensorEquivQuotSMul N I)
              (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom y) := by
            rw [map_add, map_add]
        _ = _ := by rw [hx, hy, map_add, map_add])

private lemma extension_surjective_of_reduction_surjective
    {M N : ModuleCat.{max v u} R} (f : M ⟶ N)
    (h : Function.Surjective ((redFunctor I).map f).hom) :
    Function.Surjective
      (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom) := by
  let G := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let F := ModuleCat.restrictScalars.{max v u, u, u} (Ideal.Quotient.mk I)
  let α := redCompNatIso I
  have hred : Epi ((redFunctor I).map f) := (ModuleCat.epi_iff_surjective _).mpr h
  have hcomp : Epi ((G ⋙ F).map f ≫ (α.app N).hom) := by
    rw [Iso.app_hom, α.hom.naturality f]
    infer_instance
  show Function.Surjective (((G ⋙ F).map f).hom)
  exact (ModuleCat.epi_iff_surjective _).mp
    ((epi_comp_iff_of_isIso ((G ⋙ F).map f) (α.app N).hom).mp hcomp)

/-- **Stacks 0BC9**.
A bounded above acyclic complex of `R/I`-modules with terms of the form `P/IP` has a bounded
above acyclic lift over `R` with terms satisfying `P`, whose reduction is isomorphic to the given
complex as a complex of `R/I`-modules. -/
@[stacks 0BC9]
theorem exists_lift_acyclic_complex
    (P : ModuleCat.{max v u} R → Prop)
    (hPprojective : ∀ M, P M → Module.Projective R M)
    (hPcomplement : ∀ M₁ M₂, P M₁ → P (M₁ ⊞ M₂) → P M₂)
    (hPsurjective : ∀ (M₁ M₂ : ModuleCat.{max v u} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom) →
      Function.Surjective f.hom)
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hbdd : ∃ b, E.IsStrictlyLE b) (hac : ∀ i, E.ExactAt i)
    (hterms : ∀ i, ∃ M, P M ∧ Nonempty
      (E.X i ≅ (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M)) :
    ∃ PC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (PC.X i)) ∧ (∃ b, PC.IsStrictlyLE b) ∧
      (∀ i, PC.ExactAt i) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj PC ≅ E) := by
  let G := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let F := ModuleCat.restrictScalars.{max v u, u, u} (Ideal.Quotient.mk I)
  let GR := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let FR := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let ER : CochainComplex (ModuleCat.{max v u} R) ℤ := FR.obj E
  have hP : LiftingHypotheses I P := ⟨hPprojective, hPcomplement, fun M N f hM hN hf =>
    hPsurjective M N f hM hN (extension_surjective_of_reduction_surjective I f hf)⟩
  have hbddR : ∃ b, ER.IsStrictlyLE b :=
    hbdd.imp fun b => (E.isStrictlyLE_mapHomologicalComplex_obj_iff F b).2
  have hacR : ∀ i, ER.ExactAt i := by
    intro i
    rw [HomologicalComplex.exactAt_iff]
    show ((E.sc i).map F).Exact
    exact ModuleCat.restrictScalars_map_exact (Ideal.Quotient.mk I) (E.sc i)
      ((HomologicalComplex.exactAt_iff E i).mp (hac i))
  have htermsR : HasTermsForm I P ER := by
    intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := hterms i
    exact ⟨M, hM, ⟨(F.mapIso e) ≪≫ redCompIso I M⟩⟩
  obtain ⟨PC, hPC, hbPC, hacPC, ⟨e⟩⟩ :=
    exists_lift_of_exactAt I hP hbddR hacR htermsR
  let : Limits.PreservesBinaryBiproducts G :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts G
  have : G.Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts G
  let bridge := CategoryTheory.Functor.mapHomologicalComplexCompIso
    (redCompNatIso I) (ComplexShape.up ℤ)
  have : F.Full := quotientRestrictFull I
  exact ⟨PC, hPC, hbPC, hacPC, ⟨FR.preimageIso (bridge.app PC ≪≫ e)⟩⟩

end LiftAcyclic
