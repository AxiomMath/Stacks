module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatLowestTerm

/-!
# Dimension shifting along a complex of acyclic objects

Let `C` be an abelian category, `X` an object of `C`, and `T` a cochain complex in `C`. Write
`Γ = Hom(X, -)` and `Hⁿ(-) = Extⁿ(X, -)`. If `T` is exact in the degrees `a + 1, …, a + n + 1`
and its terms `Tᵃ, …, Tᵃ⁺ⁿ` are acyclic for `H`, then the cohomology of the complex of abelian
groups `Γ(T)` in degree `a + n + 1` embeds into `Hⁿ⁺¹(Zᵃ)`, where `Zᵃ` is the object of cycles of
`T` in degree `a`. This is the standard dimension shifting along the short exact sequences
`0 → Zʲ → Tʲ → Zʲ⁺¹ → 0`.

For sheaves of abelian groups on a site and `X` the constant sheaf `ℤ`, `H` is Mathlib's sheaf
cohomology `CategoryTheory.Sheaf.H` and `Γ` is global sections. It is how the proof of
[Stacks, Tag 03TV] bounds the cohomology of the global sections of a complex of acyclic sheaves
by the cohomological dimension of a curve.

## Main results

* `StacksDraft.DimensionShift.exists_injective_homology_ext_one`: the case `n = 0`.
* `StacksDraft.DimensionShift.exists_injective_homology_ext`: the general case.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian HomologicalComplex

universe w v u

namespace StacksDraft.DimensionShift

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (X : C)

/-- The complex of abelian groups `Hom(X, T)`. -/
abbrev homComplex (T : CochainComplex C ℤ) : CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj T

/-- The short exact sequence `0 → Zᵃ → Tᵃ → Zᵃ⁺¹ → 0` of a complex exact in degree `a + 1`. -/
abbrev cyclesShortComplex (T : CochainComplex C ℤ) (a : ℤ) : ShortComplex C :=
  ShortComplex.mk (T.iCycles a) (T.toCycles a (a + 1))
    (by rw [← cancel_mono (T.iCycles (a + 1))]; simp)

omit [HasExt C] in
/-- If `T` is exact in degree `a + 1`, then `0 → Zᵃ → Tᵃ → Zᵃ⁺¹ → 0` is short exact. -/
lemma cyclesShortComplex_shortExact (T : CochainComplex C ℤ) (a : ℤ) (h : T.ExactAt (a + 1)) :
    (cyclesShortComplex T a).ShortExact :=
  HomologicalComplex.shortExact_iCycles_toCycles T a h

/-- **The connecting map of a short exact sequence `0 → A → B → C → 0` is injective on
`Hⁿ⁺¹(C)` when `Hⁿ⁺¹(B) = 0`.** -/
lemma injective_postcomp_extClass {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (h : Subsingleton (Ext X S.X₂ (n + 1))) :
    Function.Injective (hS.extClass.postcomp X (show n + 1 + 1 = n + 2 from rfl)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ X hS x rfl hx
  have : z = 0 := Subsingleton.elim _ _
  rw [this, Ext.zero_comp] at hz
  exact hz.symm

/-- An injective homomorphism out of `H` yields one out of any `G ≅ H` in `AddCommGrpCat`. -/
private lemma exists_injective_of_iso {G H : AddCommGrpCat.{v}} {A : Type*} [AddCommGroup A]
    (e : G ≅ H) (h : ∃ f : H →+ A, Function.Injective f) : ∃ f : G →+ A, Function.Injective f :=
  let ⟨f, hf⟩ := h
  ⟨f.comp e.hom.hom, hf.comp ((AddCommGrpCat.mono_iff_injective _).1 inferInstance)⟩

/-- **The base case of dimension shifting.** If `T` is exact in degree `a + 1`, the cohomology of
`Hom(X, T)` in degree `a + 1` embeds into `Ext¹(X, Zᵃ)`: a cycle `x : X ⟶ Tᵃ⁺¹` factors through
`Zᵃ⁺¹`, and the class of `x` is sent to the image of that factorization under the connecting map
of `0 → Zᵃ → Tᵃ → Zᵃ⁺¹ → 0`. -/
lemma exists_injective_homology_ext_one (T : CochainComplex C ℤ) (a : ℤ)
    (h : T.ExactAt (a + 1)) :
    ∃ f : (homComplex X T).homology (a + 1) →+ Ext X (T.cycles a) 1, Function.Injective f := by
  have hS := cyclesShortComplex_shortExact T a h
  let S := (homComplex X T).sc' a (a + 1) (a + 2)
  let e : (homComplex X T).homology (a + 1) ≅ AddCommGrpCat.of
      ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) :=
    (homComplex X T).homologyIsoSc' a (a + 1) (a + 2) (by simp) (by simp; omega) ≪≫
      S.abHomologyIso
  have hnext : (ComplexShape.up ℤ).next (a + 1) = a + 2 := by simp; omega
  -- the factorization of a cycle through the cycles object
  let lift : AddMonoidHom.ker S.g.hom → (X ⟶ T.cycles (a + 1)) := fun x =>
    T.liftCycles (x.1 : X ⟶ T.X (a + 1)) (a + 2) hnext (by exact x.2)
  have hlift (x : AddMonoidHom.ker S.g.hom) : lift x ≫ T.iCycles (a + 1) = x.1 :=
    T.liftCycles_i _ _ _ _
  have hlift_add (x y : AddMonoidHom.ker S.g.hom) : lift (x + y) = lift x + lift y := by
    rw [← cancel_mono (T.iCycles (a + 1)), Preadditive.add_comp, hlift, hlift, hlift]
    rfl
  have hlift_zero : lift 0 = 0 := by
    rw [← cancel_mono (T.iCycles (a + 1)), hlift, zero_comp]
    rfl
  let φ : AddMonoidHom.ker S.g.hom →+ Ext X (T.cycles a) 1 :=
    { toFun := fun x => (Ext.mk₀ (lift x)).comp hS.extClass (zero_add 1)
      map_zero' := by rw [hlift_zero, Ext.mk₀_zero, Ext.zero_comp]
      map_add' := fun x y => by rw [hlift_add, Ext.mk₀_add, Ext.add_comp] }
  have hφ : AddMonoidHom.range S.abToCycles ≤ AddMonoidHom.ker φ := by
    rintro _ ⟨y, rfl⟩
    let y' : X ⟶ T.X a := y
    have hy : lift (S.abToCycles y) = y' ≫ (cyclesShortComplex T a).g := by
      rw [← cancel_mono (T.iCycles (a + 1)), hlift, Category.assoc]
      change y' ≫ T.d a (a + 1) = y' ≫ T.toCycles a (a + 1) ≫ T.iCycles (a + 1)
      rw [T.toCycles_i]
    change (Ext.mk₀ (lift (S.abToCycles y))).comp hS.extClass (zero_add 1) = 0
    rw [hy, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]
  let ψ : ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) →+
      Ext X (T.cycles a) 1 := QuotientAddGroup.lift _ φ hφ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ X hS _ (zero_add 1) hz
    obtain ⟨y, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    have hy := (Ext.mk₀_bijective _ _).1 hx₂
    refine (QuotientAddGroup.eq_zero_iff _).2 ⟨y, ?_⟩
    apply Subtype.ext
    have := congrArg (· ≫ T.iCycles (a + 1)) hy
    simp only [Category.assoc, hlift, T.toCycles_i] at this
    change y ≫ T.d a (a + 1) = x.1
    exact this
  exact exists_injective_of_iso e ⟨ψ, hψ⟩

/-- **Dimension shifting.** If `T` is exact in the degrees `a + 1, …, a + n + 1` and
`Extᵠ(X, Tʲ) = 0` for `q ≥ 1` and `a ≤ j ≤ a + n - 1`, the cohomology of `Hom(X, T)` in degree
`a + n + 1` embeds into `Extⁿ⁺¹(X, Zᵃ)`. -/
lemma exists_injective_homology_ext (n : ℕ) :
    ∀ (T : CochainComplex C ℤ) (a : ℤ), (∀ k : ℕ, k ≤ n → T.ExactAt (a + 1 + k)) →
      (∀ k : ℕ, k < n → ∀ q : ℕ, Subsingleton (Ext X (T.X (a + k)) (q + 1))) →
      ∃ f : (homComplex X T).homology (a + 1 + n) →+ Ext X (T.cycles a) (n + 1),
        Function.Injective f := by
  induction n with
  | zero =>
    intro T a hex _
    obtain ⟨f, hf⟩ := exists_injective_homology_ext_one X T a (by simpa using hex 0 le_rfl)
    exact exists_injective_of_iso (eqToIso (by simp)) ⟨f, hf⟩
  | succ n ih =>
    intro T a hex hac
    have hS := cyclesShortComplex_shortExact T a (by simpa using hex 0 (by omega))
    obtain ⟨f, hf⟩ := ih T (a + 1) (fun k hk => by
        have := hex (k + 1) (by omega)
        rwa [show a + 1 + ((k + 1 : ℕ) : ℤ) = a + 1 + 1 + (k : ℤ) by push_cast; ring] at this)
      (fun k hk q => by
        have := hac (k + 1) (by omega) q
        rwa [show a + ((k + 1 : ℕ) : ℤ) = a + 1 + (k : ℤ) by push_cast; ring] at this)
    have h0 : Subsingleton (Ext X (T.X a) (n + 1)) := by
      have := hac 0 (by omega) n
      simpa using this
    have hδ := injective_postcomp_extClass X hS n h0
    exact exists_injective_of_iso (eqToIso (by congr 1; push_cast; ring))
      ⟨(hS.extClass.postcomp X (show n + 1 + 1 = n + 2 from rfl)).comp f, hδ.comp hf⟩

end StacksDraft.DimensionShift

end
