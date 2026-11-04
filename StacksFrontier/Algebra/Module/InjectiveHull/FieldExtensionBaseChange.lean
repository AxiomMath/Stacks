module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import StacksFrontier.Algebra.Module.InjectiveHull.CoextendBaseChangeIso
public import StacksFrontier.Algebra.Module.InjectiveHull.CoextendScalarsDimension
public import StacksFrontier.Algebra.Module.InjectiveHull.ExtFlatBaseChangeVanishing
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing

/-!
# Injective dimension of a flat base change of an injective module

Let `k ⊆ K` be an extension of fields and let `A` be a `k`-algebra of finite type.  For every
injective `A`-module `I` the base change `A_K ⊗_A I`, where `A_K = K ⊗_k A`, has finite injective
dimension over `A_K`.

## Main results

* `Module.hasInjectiveDimensionLE_extendScalars_of_injective` — the abstract form: let `R` be a
  Noetherian ring, let `S` be a flat `R`-algebra over which every module has injective dimension
  at most `d`, and let `A` be an `R`-algebra which is finite as an `R`-module.  Then for every
  injective `A`-module `I` the base change `(S ⊗_R A) ⊗_A I` has injective dimension at most `d`
  over `S ⊗_R A`.
* `Module.forall_hasInjectiveDimensionLE_mvPolynomial` — every module over a polynomial algebra in
  `n` variables over a field has injective dimension at most `n`.

## Implementation notes

The proof is in three steps.  First, `I` is a retract of the coextension `Hom_R(A, E)` of an
injective `R`-module `E`: embed `I`, viewed as an `R`-module, into an injective `R`-module, and
split the resulting `A`-linear monomorphism `I → Hom_R(A, E)` using injectivity of `I` over `A`.
Second, flat base change identifies `(S ⊗_R A) ⊗_A Hom_R(A, E)` with
`Hom_S(S ⊗_R A, S ⊗_R E)`, which is `ModuleCat.extendCoextendBaseChangeIso`.  Third, the Rees
change-of-rings bound `ModuleCat.hasInjectiveDimensionLE_coextendScalars` applies to
`Hom_S(S ⊗_R A, S ⊗_R E)`: its two hypotheses are that `S ⊗_R E` has injective dimension at most
`d` over `S`, which is the assumption on `S`, and that all higher
`Ext^{q+1}_S(S ⊗_R A, S ⊗_R E)` vanish, which is
`Module.subsingleton_ext_baseChange_of_injective`.  Injective dimension passes to retracts, so the
bound descends to `(S ⊗_R A) ⊗_A I`.

The polynomial input is Stacks 00OQ: a polynomial algebra in `n` variables over a field is regular
of global dimension `n`, so every module over it has projective dimension at most `n`, hence — by
the `Ext`-form of Baer's criterion — injective dimension at most `n`.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

section MvPoly

open MvPolynomial

/-- Every module over a polynomial algebra in `n` variables over a field has injective dimension
at most `n`: the algebra is regular of global dimension `n` by Stacks 00OQ, so every module has
projective dimension at most `n`, and the `Ext`-characterisation of injective dimension turns that
bound around. -/
public theorem Module.forall_hasInjectiveDimensionLE_mvPolynomial (K : Type u) [Field K] (n : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) K)) :
    HasInjectiveDimensionLE M n := by
  have hsup :=
    (isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization.{u, 0, 0}
      K (Fin n)).2.1
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsup
  refine CategoryTheory.hasInjectiveDimensionLT_of_enoughProjectives M (n + 1) fun Y => ?_
  have hY : HasProjectiveDimensionLE Y n := by
    rw [← CategoryTheory.projectiveDimension_le_iff]
    exact
      (le_iSup
          (fun N : ModuleCat.{u} (MvPolynomial (Fin n) K) ↦
            CategoryTheory.projectiveDimension N) Y).trans
        hsup.le
  exact CategoryTheory.HasProjectiveDimensionLT.subsingleton Y (n + 1) (n + 1) le_rfl M

end MvPoly

/-- The underlying `S`-module of an extension of scalars along `algebraMap R S` is the ordinary
tensor product `S ⊗_R N`: the two differ only in the `R`-action carried by `S`. -/
private noncomputable def extendScalarsObjEquiv {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj N : Type u) ≃ₗ[S]
      TensorProduct R S N := by
  letI : Module S (TensorProduct R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) : Type u)
      (N : Type u)) :=
    inferInstanceAs (Module S
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj N : Type u))
  let eS : ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) : Type u) ≃ₗ[R]
      S :=
    { AddEquiv.refl S with
      map_smul' := fun r x => (Algebra.smul_def (R := R) (A := S) r x).symm }
  let t := TensorProduct.congr eS (LinearEquiv.refl R (N : Type u))
  have key : ∀ (s : S) (w : TensorProduct R
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) : Type u)
      (N : Type u)), t (s • w) = s • t w := by
    intro s w
    induction w using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b n => rfl
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { t.toAddEquiv with map_smul' := key }

/-- Vanishing of an `Ext`-group transports along an isomorphism of the source. -/
private lemma subsingleton_ext_of_iso_left {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X X' Y : C} (i : X ≅ X') (n : ℕ) (h : Subsingleton (Abelian.Ext X' Y n)) :
    Subsingleton (Abelian.Ext X Y n) := by
  refine Function.Surjective.subsingleton
    (f := fun x : Abelian.Ext X' Y n => (Abelian.Ext.mk₀ i.hom).comp x (zero_add n))
    fun x => ⟨(Abelian.Ext.mk₀ i.inv).comp x (zero_add n), ?_⟩
  dsimp only
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, i.hom_inv_id,
    Abelian.Ext.mk₀_id_comp]

/-- Vanishing of an `Ext`-group transports along an isomorphism of the target. -/
public lemma subsingleton_ext_of_iso_right {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Y' : C} (j : Y ≅ Y') (n : ℕ) (h : Subsingleton (Abelian.Ext X Y' n)) :
    Subsingleton (Abelian.Ext X Y n) := by
  refine Function.Surjective.subsingleton
    (f := fun y : Abelian.Ext X Y' n => y.comp (Abelian.Ext.mk₀ j.inv) (add_zero n))
    fun x => ⟨x.comp (Abelian.Ext.mk₀ j.hom) (add_zero n), ?_⟩
  dsimp only
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, j.hom_inv_id,
    Abelian.Ext.comp_mk₀_id]

/-- An injective `A`-module is a retract of the coextension along `f : R →+* A` of an injective
`R`-module, namely of an injective hull of its own underlying `R`-module.  The monomorphism is the
unit of the restriction/coextension adjunction followed by that embedding, and it splits because
the source is injective. -/
private noncomputable def retractCoextendScalars {R A : Type u} [Ring R] [Ring A] (f : R →+* A)
    (I : ModuleCat.{u} A) [Injective I] :
    Retract I ((ModuleCat.coextendScalars.{u, u, u} f).obj
      (Injective.under ((ModuleCat.restrictScalars.{u, u, u} f).obj I))) := by
  let N := (ModuleCat.restrictScalars.{u, u, u} f).obj I
  let m : I ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj (Injective.under N) :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).unit.app I ≫
      (ModuleCat.coextendScalars.{u, u, u} f).map (Injective.ι N)
  have hm : Mono m := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have h1 := congrArg (fun w => ModuleCat.CoextendScalars.equiv f _ w (1 : A)) hxy
    have h2 : (Injective.ι N).hom ((1 : A) • x) = (Injective.ι N).hom ((1 : A) • y) := h1
    rw [one_smul, one_smul] at h2
    exact (ModuleCat.mono_iff_injective (Injective.ι N)).mp inferInstance h2
  exact { i := m, r := Injective.factorThru (𝟙 I) m, retract := Injective.comp_factorThru _ _ }

/-- `S ⊗_R A`, regarded as an `S`-module by restriction of scalars along the structure map of the
tensor-product algebra, is the ordinary tensor product `S ⊗_R A`. -/
private noncomputable def tensorRestrictEquiv {R S A : Type u} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] :
    TensorProduct R S A ≃ₗ[S]
      (((ModuleCat.restrictScalars.{u, u, u} (algebraMap S (TensorProduct R S A))).obj
        (ModuleCat.of (TensorProduct R S A) (TensorProduct R S A))) : Type u) := by
  refine { AddEquiv.refl (TensorProduct R S A) with map_smul' := ?_ }
  intro s b
  change (s • b : TensorProduct R S A) = algebraMap S (TensorProduct R S A) s * b
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul s' a => simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

/-- **Flat base change of an injective module has bounded injective dimension.**  Let `R` be a
Noetherian ring, let `S` be a flat `R`-algebra over which every module has injective dimension at
most `d`, and let `A` be an `R`-algebra which is finite as an `R`-module.  Then for every injective
`A`-module `I` the base change `(S ⊗_R A) ⊗_A I` has injective dimension at most `d` over
`S ⊗_R A`. -/
public theorem Module.hasInjectiveDimensionLE_extendScalars_of_injective
    {R S A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Module.Flat R S] [Module.Finite R A] (d : ℕ)
    (hSdim : ∀ Y : ModuleCat.{u} S, HasInjectiveDimensionLE Y d)
    (I : ModuleCat.{u} A) [CategoryTheory.Injective I] :
    HasInjectiveDimensionLE
      ((ModuleCat.extendScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R S A).toRingHom).obj I) d := by
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  set F := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R S A).toRingHom
  set E := CategoryTheory.Injective.under
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).obj I)
  let _ : CategoryTheory.Injective (ModuleCat.of R (E : Type u)) :=
    inferInstanceAs (CategoryTheory.Injective E)
  have _ : Module.Injective R (E : Type u) := Module.injective_module_of_injective_object R _
  -- the two identifications of the `S`-modules occurring in the `Ext`-vanishing
  let iLeft : ((ModuleCat.restrictScalars.{u, u, u} (algebraMap S (TensorProduct R S A))).obj
        (ModuleCat.of (TensorProduct R S A) (TensorProduct R S A))) ≅
      ModuleCat.of S (TensorProduct R S A) :=
    (tensorRestrictEquiv (R := R) (S := S) (A := A)).toModuleIso.symm
  let iRight : (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj E ≅
      ModuleCat.of S (TensorProduct R S (E : Type u)) :=
    (extendScalarsObjEquiv (S := S) E).toModuleIso
  have hExt : ∀ q : ℕ, Subsingleton (Abelian.Ext
      ((ModuleCat.restrictScalars.{u, u, u} (algebraMap S (TensorProduct R S A))).obj
        (ModuleCat.of (TensorProduct R S A) (TensorProduct R S A)))
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj E) (q + 1)) := fun q =>
    subsingleton_ext_of_iso_left iLeft (q + 1)
      (subsingleton_ext_of_iso_right iRight (q + 1)
        (Module.subsingleton_ext_baseChange_of_injective (R := R) (S := S) (E : Type u) A q))
  have hcoext := ModuleCat.hasInjectiveDimensionLE_coextendScalars
    (algebraMap S (TensorProduct R S A)) d
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj E) (hSdim _) hExt
  have hmid : HasInjectiveDimensionLE
      (F.obj ((ModuleCat.coextendScalars.{u, u, u} (algebraMap R A)).obj E)) d :=
    CategoryTheory.hasInjectiveDimensionLT_of_iso
      (ModuleCat.extendCoextendBaseChangeIso (R := R) (S := S) (A := A) E).symm (d + 1)
  exact ((retractCoextendScalars (algebraMap R A) I).map F).hasInjectiveDimensionLT (d + 1)

end
