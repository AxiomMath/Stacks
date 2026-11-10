module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism of constant sheaves of modules is locally induced by a module map

Let `(C, J)` be a site and `Λ` a ring, not assumed commutative. For a `Λ`-module `M` the constant
sheaf `M̲` is the sheafification of the constant presheaf with value `M`. A morphism of constant
sheaves `ξ : M̲ ⟶ N̲` is *not* in general of the form `ψ̲` for a homomorphism `ψ : M ⟶ N`. This
file proves that it is so locally, provided `M` is finitely presented: every object of the site
has a covering family on each member of which `ξ` agrees with `ψ̲` for some `ψ : M ⟶ N`.

## Main definitions

* `Stacks.ConstantSheaf.constantUnitApp`: the canonical map `M ⟶ Γ(X, M̲)`, i.e. the component
  at `X` of `toSheafify` for the constant presheaf on `M`.

## Main results

* `Stacks.ConstantSheaf.finset_inf_covering`: a finite infimum of covering sieves is covering.
* `Stacks.ConstantSheaf.injective_constantUnitApp`: on an object not covered by the empty sieve,
  the canonical map `M ⟶ Γ(X, M̲)` is injective.
* `Stacks.ConstantSheaf.homComparison_constantUnitApp`: for a *commutative* ring, the comparison
  of `Stacks.ConstantSheaf.homComparison` takes the canonical image of a homomorphism `ψ : M ⟶ N`
  to the map sending `m` to the canonical image of `ψ m`.
* `Stacks.ConstantSheaf.app_eq_of_eq_on_constantUnit`: two morphisms `M̲ ⟶ G` into a sheaf which
  agree on the canonical image of `M` over every object lying over `V` agree over every object
  lying over `V`.
* `Stacks.ConstantSheaf.exists_cover_app_eq_constantSheaf_map`: for `M` finitely presented,
  every object `U` of the site has a covering family `{V i ⟶ U}` such that on each `V i` the
  morphism `ξ` agrees with `ψ̲` for some `ψ : M ⟶ N`, over every object lying over `V i`.
* `Stacks.ConstantSheaf.exists_cover_overPullback_map_eq`: the same statement read as an equality
  of morphisms of sheaves on the slice site `C/V i`.

## References

* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w x

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ### Finite intersections of covering sieves -/

section FiniteInf

/-- A finite infimum of covering sieves is covering. -/
theorem finset_inf_covering {ι : Type*} {U : C} (s : Finset ι) (T : ι → Sieve U)
    (h : ∀ i ∈ s, T i ∈ J U) : s.inf T ∈ J U := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- An arrow in a sieve is in any larger sieve. -/
theorem sieve_apply_of_le {U W : C} {A B : Sieve U} (h : A ≤ B) {f : W ⟶ U} (hf : A f) : B f :=
  h f hf

end FiniteInf

/-! ### A linear map out of a finite free module and its values on the standard generators -/

section Algebra

variable {Λ : Type w} [Ring Λ]

/-- A linear map out of `Λ^{⊕n}` is the linear combination map attached to its values on the
standard generators. -/
theorem eq_fintype_linearCombination_single {n : ℕ} {P : Type*} [AddCommGroup P] [Module Λ P]
    (F : (Fin n → Λ) →ₗ[Λ] P) :
    Fintype.linearCombination Λ (fun i => F (Pi.single i 1)) = F := by
  classical
  refine LinearMap.ext fun c => ?_
  rw [Fintype.linearCombination_apply]
  have h : ∀ i : Fin n, c i • F (Pi.single i (1 : Λ)) = F (Pi.single i (c i)) := fun i => by
    rw [← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl fun i _ => h i, ← map_sum, Finset.univ_sum_single]

end Algebra

/-! ### The canonical map from a module to the sections of its constant sheaf -/

section Unit

variable {Λ : Type w} [Ring Λ] [HasWeakSheafify J (ModuleCat.{x} Λ)]

/-- The canonical map from a module to the sections over `X` of the constant sheaf it generates,
i.e. the component at `X` of `toSheafify` for the constant presheaf on the module. -/
noncomputable abbrev constantUnitApp (M : ModuleCat.{x} Λ) (X : Cᵒᵖ) :
    M ⟶ ((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.obj X :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app X

/-- The canonical map is compatible with restriction: the image of an element of `M` restricts to
the image of the same element. -/
theorem map_constantUnitApp (M : ModuleCat.{x} Λ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M) :
    (((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map f).hom
        ((constantUnitApp J M X).hom m) = (constantUnitApp J M Y).hom m := by
  have h : ((Functor.const Cᵒᵖ).obj M).map f ≫ constantUnitApp J M Y =
      constantUnitApp J M X ≫ ((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map f :=
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality f
  simpa using (ConcreteCategory.congr_hom h m).symm

/-- The canonical map is natural in the module. -/
theorem app_constantUnitApp_map {M N : ModuleCat.{x} Λ} (ψ : M ⟶ N) (X : Cᵒᵖ) (m : M) :
    (((constantSheaf J (ModuleCat.{x} Λ)).map ψ).hom.app X).hom
        ((constantUnitApp J M X).hom m) = (constantUnitApp J N X).hom (ψ.hom m) :=
  (ConcreteCategory.congr_hom
    (toSheafify_const_naturality_app J (ModuleCat.{x} Λ) ψ X) m).symm

end Unit

/-! ### Injectivity of the canonical map on a non-degenerate object -/

section Injective

variable {Λ : Type w} [Ring Λ] [HasWeakSheafify J (ModuleCat.{x} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{x} Λ)]

/-- On an object not covered by the empty sieve, the canonical map from a module to the sections
of its constant sheaf over that object is injective. -/
theorem injective_constantUnitApp (M : ModuleCat.{x} Λ) {U : C} (hU : (⊥ : Sieve U) ∉ J U) :
    Function.Injective (constantUnitApp J M (op U)).hom := by
  intro p q hpq
  by_contra hne
  have hmem := Presheaf.equalizerSieve_mem J
    (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)) p q hpq
  have hbot : Presheaf.equalizerSieve
      (F := (Functor.const Cᵒᵖ).obj M) (X := op U) p q = ⊥ := by
    refine Sieve.ext fun V g => ?_
    simp only [Presheaf.equalizerSieve_apply, Functor.const_obj_map, Sieve.bot_apply, iff_false]
    exact hne
  exact hU (hbot ▸ hmem)

end Injective

/-! ### The comparison on the canonical image of a homomorphism -/

section Comparison

variable {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{x} Λ)]
variable (M N E : ModuleCat.{x} Λ)
  (e : ((M : Type x) →ₗ[Λ] (N : Type x)) ≃ₗ[Λ] E)

/-- The comparison `Γ(X, Hom_Λ(M, N)̲) → Hom_Λ(M, Γ(X, N̲))` is compatible with restriction. -/
theorem homComparison_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : (constantSections J X.unop).obj E) (m : M) :
    (homComparison J M N E e Y.unop).1
        ((((constantSheaf J (ModuleCat.{x} Λ)).obj E).obj.map f).hom s) m =
      (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map f).hom
        ((homComparison J M N E e X.unop).1 s m) := by
  have hX := (homComparison J M N E e X.unop).2 s m
  have hY := (homComparison J M N E e Y.unop).2
    ((((constantSheaf J (ModuleCat.{x} Λ)).obj E).obj.map f).hom s) m
  have hnat := ConcreteCategory.congr_hom
    (((constantSheaf J (ModuleCat.{x} Λ)).map (ModuleCat.ofHom
      (LinearMap.lcomp Λ (N : Type x) e.symm.toLinearMap
        (evalHom (M : Type x) (N : Type x) m)))).hom.naturality f) s
  exact hY.trans (hnat.trans (congrArg
    (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map f).hom hX.symm))

/-- The comparison takes the canonical image of a homomorphism `ψ : M ⟶ N` to the map sending
`m` to the canonical image of `ψ m`. -/
theorem homComparison_constantUnitApp (X : Cᵒᵖ) (ψ : M ⟶ N) (m : M) :
    (homComparison J M N E e X.unop).1
        ((constantUnitApp J E X).hom (e (ModuleCat.homLinearEquiv (S := Λ) ψ))) m =
      (constantUnitApp J N X).hom (ψ.hom m) := by
  refine ((homComparison J M N E e X.unop).2 _ m).trans
    ((app_constantUnitApp_map J _ X _).trans ?_)
  refine congrArg (constantUnitApp J N X).hom ?_
  change (e.symm (e (ModuleCat.homLinearEquiv (S := Λ) ψ))) m = ψ.hom m
  rw [e.symm_apply_apply]
  rfl

end Comparison

/-! ### The separatedness step -/

section Separated

variable {Λ : Type w} [Ring Λ] [HasWeakSheafify J (ModuleCat.{x} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{x} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{x} Λ))]

/-- Two morphisms out of a constant sheaf into a sheaf which agree on the canonical image of the
module over every object lying over `V` agree over every object lying over `V`. -/
theorem app_eq_of_eq_on_constantUnit {M : ModuleCat.{x} Λ} {G : Sheaf J (ModuleCat.{x} Λ)}
    (ξ ξ' : (constantSheaf J (ModuleCat.{x} Λ)).obj M ⟶ G) {V : C}
    (h : ∀ (W : C) (_ : W ⟶ V) (m : M),
      (ξ.hom.app (op W)).hom ((constantUnitApp J M (op W)).hom m) =
        (ξ'.hom.app (op W)).hom ((constantUnitApp J M (op W)).hom m))
    (W : C) (p : W ⟶ V) : ξ.hom.app (op W) = ξ'.hom.app (op W) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  refine G.property.isSeparated _ _ (Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)) t) _ _ ?_
  rintro Y q ⟨m, hm⟩
  have hξ := NatTrans.naturality_apply ξ.hom q.op t
  have hξ' := NatTrans.naturality_apply ξ'.hom q.op t
  have hm' : (constantUnitApp J M (op Y)).hom m =
      (((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map q.op).hom t := hm
  rw [← hξ, ← hξ', ← hm']
  exact h Y (q ≫ p) m

end Separated

/-! ### The main result -/

section Main

variable {Λ : Type w} [Ring Λ] [HasSheafify J (ModuleCat.{x} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{x} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{x} Λ))]

/-- If `M` is a finitely presented `Λ`-module, then every object `U` of the site has a covering
family `{V i ⟶ U}` such that, for each `i`, there is a homomorphism `ψ : M ⟶ N` with `ξ` and `ψ̲`
agreeing over every object lying over `V i`. -/
@[sga "4 IX 2.1" "(ii), special case"]
theorem exists_cover_app_eq_constantSheaf_map (M N : ModuleCat.{x} Λ)
    [Module.FinitePresentation Λ (M : Type x)]
    (ξ : (constantSheaf J (ModuleCat.{x} Λ)).obj M ⟶
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ J U ∧ ∀ i, ∃ ψ : M ⟶ N, ∀ (W : C) (_ : W ⟶ V i),
        ξ.hom.app (op W) = ((constantSheaf J (ModuleCat.{x} Λ)).map ψ).hom.app (op W) := by
  classical
  obtain ⟨n, k, ψ₀, aa, hψ₀, hexact⟩ :=
    Module.FinitePresentation.exists_fin' Λ (M : Type x)
  set TU : (M : Type x) →ₗ[Λ] (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.obj (op U) :
      Type x) := (ξ.hom.app (op U)).hom ∘ₗ (constantUnitApp J M (op U)).hom with hTU
  set s : Fin n → (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.obj (op U) : Type x) :=
    fun i => TU (ψ₀ (Pi.single i 1)) with hsdef
  have hs0 : ∀ j : Fin k, Fintype.linearCombination Λ s (aa (Pi.single j 1)) = 0 := by
    intro j
    have h1 : Fintype.linearCombination Λ s = TU ∘ₗ ψ₀ :=
      eq_fintype_linearCombination_single (TU ∘ₗ ψ₀)
    rw [h1]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hexact.apply_apply_eq_zero, map_zero]
  obtain ⟨I, V, g, hVg⟩ := Sieve.exists_eq_ofArrows
    (Finset.univ.inf fun i : Fin n => Presheaf.imageSieve
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (s i))
  refine ⟨I, V, g, hVg ▸ finset_inf_covering J Finset.univ _
    (fun i _ => Presheaf.imageSieve_mem J
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (s i)), fun i₀ => ?_⟩
  have hmem : ∀ i : Fin n, (Presheaf.imageSieve
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (s i)).arrows (g i₀) := by
    intro i
    have h0 : (Finset.univ.inf fun i : Fin n => Presheaf.imageSieve
        (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj N)) (s i)).arrows (g i₀) := by
      rw [hVg]; exact Sieve.ofArrows_mk V g i₀
    exact sieve_apply_of_le (Finset.inf_le (Finset.mem_univ i)) h0
  choose nn hnn using hmem
  have hnn' : ∀ i : Fin n, (constantUnitApp J N (op (V i₀))).hom (nn i) =
      (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map (g i₀).op).hom (s i) := hnn
  by_cases hbot : (⊥ : Sieve (V i₀)) ∈ J (V i₀)
  · exact ⟨0, fun W p => (Sheaf.isTerminalOfBotCover ((constantSheaf J (ModuleCat.{x} Λ)).obj N) W
      (by simpa using J.pullback_stable p hbot)).hom_ext _ _⟩
  set bb : (Fin n → Λ) →ₗ[Λ] (N : Type x) := Fintype.linearCombination Λ nn with hbb
  have hrel : ∀ j : Fin k, bb (aa (Pi.single j 1)) = 0 := by
    intro j
    refine injective_constantUnitApp J N hbot ?_
    rw [map_zero, hbb, Fintype.linearCombination_apply, map_sum]
    calc ∑ i, (constantUnitApp J N (op (V i₀))).hom (aa (Pi.single j 1) i • nn i)
        = (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map (g i₀).op).hom
            (∑ i, aa (Pi.single j 1) i • s i) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hnn' i]
      _ = 0 := by
          rw [show (∑ i, aa (Pi.single j 1) i • s i) = 0 from hs0 j, map_zero]
  have hker : LinearMap.ker ψ₀ ≤ LinearMap.ker bb := by
    intro l hl
    obtain ⟨t, ht⟩ := (hexact l).1 hl
    rw [LinearMap.mem_ker, ← ht]
    have h1 : Fintype.linearCombination Λ (fun j => bb (aa (Pi.single j 1))) = bb ∘ₗ aa :=
      eq_fintype_linearCombination_single (bb ∘ₗ aa)
    have h2 : (bb ∘ₗ aa) t = 0 := by
      rw [← h1, Fintype.linearCombination_apply]
      exact Finset.sum_eq_zero fun j _ => by rw [hrel j, smul_zero]
    exact h2
  set ψ' : (M : Type x) →ₗ[Λ] (N : Type x) :=
    (LinearMap.ker ψ₀).liftQ bb hker ∘ₗ
      (ψ₀.quotKerEquivOfSurjective hψ₀).symm.toLinearMap with hψ'
  have hψ'_apply : ∀ l : Fin n → Λ, ψ' (ψ₀ l) = bb l := by
    intro l
    have h2 : (ψ₀.quotKerEquivOfSurjective hψ₀).symm (ψ₀ l) = Submodule.Quotient.mk l := by
      rw [LinearEquiv.symm_apply_eq]
      exact (LinearMap.quotKerEquivOfSurjective_apply_mk ψ₀ hψ₀ l).symm
    rw [hψ']
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2]
    exact Submodule.liftQ_apply _ _ _
  refine ⟨ModuleCat.ofHom ψ', fun W p => ?_⟩
  refine app_eq_of_eq_on_constantUnit J ξ
    ((constantSheaf J (ModuleCat.{x} Λ)).map (ModuleCat.ofHom ψ')) (V := V i₀)
    (fun W' q m => ?_) W p
  rw [app_constantUnitApp_map]
  set L₁ : (Fin n → Λ) →ₗ[Λ]
      (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.obj (op W') : Type x) :=
    (ξ.hom.app (op W')).hom ∘ₗ (constantUnitApp J M (op W')).hom ∘ₗ ψ₀ with hL₁
  set L₂ : (Fin n → Λ) →ₗ[Λ]
      (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.obj (op W') : Type x) :=
    (constantUnitApp J N (op W')).hom ∘ₗ bb with hL₂
  have hgen : ∀ i : Fin n, L₁ (Pi.single i 1) = L₂ (Pi.single i 1) := by
    intro i
    have hres : (constantUnitApp J M (op W')).hom (ψ₀ (Pi.single i 1)) =
        (((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map (q ≫ g i₀).op).hom
          ((constantUnitApp J M (op U)).hom (ψ₀ (Pi.single i 1))) :=
      (map_constantUnitApp J M (q ≫ g i₀).op _).symm
    have hnat : (ξ.hom.app (op W')).hom
          ((((constantSheaf J (ModuleCat.{x} Λ)).obj M).obj.map (q ≫ g i₀).op).hom
            ((constantUnitApp J M (op U)).hom (ψ₀ (Pi.single i 1)))) =
        (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map (q ≫ g i₀).op).hom
          ((ξ.hom.app (op U)).hom ((constantUnitApp J M (op U)).hom (ψ₀ (Pi.single i 1)))) :=
      ConcreteCategory.congr_hom (ξ.hom.naturality (q ≫ g i₀).op) _
    have hsplit : (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map (q ≫ g i₀).op).hom (s i) =
        (((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map q.op).hom
          ((((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map (g i₀).op).hom (s i)) := by
      rw [op_comp, ((constantSheaf J (ModuleCat.{x} Λ)).obj N).obj.map_comp]
      rfl
    rw [hL₁, hL₂]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hres, hnat, show (ξ.hom.app (op U)).hom ((constantUnitApp J M (op U)).hom
      (ψ₀ (Pi.single i 1))) = s i from rfl, hsplit, ← hnn' i, map_constantUnitApp J N q.op (nn i),
      hbb, Fintype.linearCombination_apply_single, one_smul]
  have hL : L₁ = L₂ := by
    rw [← eq_fintype_linearCombination_single L₁, ← eq_fintype_linearCombination_single L₂,
      funext hgen]
  obtain ⟨l, rfl⟩ := hψ₀ m
  have h₁ : L₁ l = (ξ.hom.app (op W')).hom ((constantUnitApp J M (op W')).hom (ψ₀ l)) := rfl
  have h₂ : L₂ l = (constantUnitApp J N (op W')).hom (bb l) := rfl
  rw [← h₁, hL, h₂, ← hψ'_apply l]
  rfl

/-- If `M` is a finitely presented `Λ`-module, then every object `U` of the site has a covering
family `{V i ⟶ U}` such that, for each `i`, the restrictions of `ξ` and of `ψ̲` to `C/V i` agree
for some homomorphism `ψ : M ⟶ N`. -/
theorem exists_cover_overPullback_map_eq
    [∀ Y : C, HasWeakSheafify (J.over Y) (ModuleCat.{x} Λ)] (M N : ModuleCat.{x} Λ)
    [Module.FinitePresentation Λ (M : Type x)]
    (ξ : (constantSheaf J (ModuleCat.{x} Λ)).obj M ⟶
      (constantSheaf J (ModuleCat.{x} Λ)).obj N) (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (g : ∀ i, V i ⟶ U),
      Sieve.ofArrows V g ∈ J U ∧ ∀ i, ∃ ψ : M ⟶ N,
        (J.overPullback (ModuleCat.{x} Λ) (V i)).map ξ =
          (J.overPullback (ModuleCat.{x} Λ) (V i)).map
            ((constantSheaf J (ModuleCat.{x} Λ)).map ψ) := by
  obtain ⟨I, V, g, hcov, hloc⟩ := exists_cover_app_eq_constantSheaf_map J M N ξ U
  refine ⟨I, V, g, hcov, fun i => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc i
  refine ⟨ψ, Sheaf.hom_ext (NatTrans.ext (funext fun Y => ?_))⟩
  exact hψ Y.unop.left Y.unop.hom

end Main

end Stacks.ConstantSheaf

end
