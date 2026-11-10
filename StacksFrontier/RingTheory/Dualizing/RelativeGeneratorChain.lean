module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom
public import StacksFrontier.Homology.ExtendScalars.HomologyBaseChange
public import StacksFrontier.Homology.RelativelyPerfect.Representative
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorUniversal

/-!
# Derived base change of a generator, computed on representatives

Let `φ : S → T` be a ring map, `P` a bounded above complex of projective `S`-modules and `F` a
complex of `S`-modules, and write `E = Hom^•_S(P, F)`, `P' = P ⊗_S T`, `F' = F ⊗_S T`.  Suppose the
termwise base change `E ⊗_S T` is the Hom complex `Hom^•_T(P', F')` by the canonical map, and the
degree-zero cycles of `E` base change, i.e. `T ⊗_S Z^0(E) → Z^0(E ⊗_S T)` is invertible.  Then a
chain map `f₀ : P ⟶ F` whose class generates the morphisms `P ⟶ F` in `D(S)` (every morphism
factoring through it by a scalar) has a base change `f₀ ⊗ T` whose class generates the morphisms
`P' ⟶ F'` in `D(T)`.

This is the chain-level content of the last sentence of the source's proof of [stacks 0E2F]:
"this equality furthermore gives the final assertion of the lemma".  There the identification
`H^0(E^• ⊗_R R') = H^0(E^•) ⊗_R R'` comes from the degreewise flatness chase; here it enters
through the cycles, `Z^0(E^• ⊗ T) = Z^0(E^•) ⊗ T`, which is the form the chase delivers
(`StacksDraft.DegreewiseChase.isIso_cyclesComparison_includeLeft`).

## Main results

* `Dualizing.extendScalars_map_smul` — extension of scalars is semilinear on morphisms.
* `Dualizing.homComplexBaseChange_ofHom` — the canonical base-change isomorphism of Hom complexes
  sends the cochain of a chain map to the cochain of its base change.
* `Dualizing.isPostcompGenerator_Q_map_extend` — **the generator survives base change.**
* `Dualizing.isPostcompGenerator_derivedExtension_map` — the same, read through derived extension
  of scalars.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings TensorProduct
open CochainComplex.HomComplex CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

variable {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)

/-- **Extension of scalars is semilinear on morphisms**: `(s • f) ⊗ T = φ s • (f ⊗ T)`. -/
theorem extendScalars_map_smul {M N : ModuleCat.{u} S} (s : S) (f : M ⟶ N) :
    (ModuleCat.extendScalars.{u, u, u} φ).map (s • f) =
      φ s • (ModuleCat.extendScalars.{u, u, u} φ).map f := by
  have key : ∀ (t : (ModuleCat.restrictScalars.{u, u, u} φ).obj (ModuleCat.of T T)) (x : N),
      (t ⊗ₜ[S] (s • x) : TensorProduct S _ _) = (s • t) ⊗ₜ[S] x :=
    fun t x => (TensorProduct.smul_tmul s t x).symm
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change ((1 : T) ⊗ₜ[S, φ] (s • f m) : (ModuleCat.extendScalars.{u, u, u} φ).obj N) =
    (φ s * (1 : T)) ⊗ₜ[S, φ] f m
  exact key (1 : T) (f m)

/-- **Termwise extension of scalars is semilinear on chain maps.** -/
theorem extendComplex_map_smul {P F : CochainComplex (ModuleCat.{u} S) ℤ} (s : S) (k : P ⟶ F) :
    (StacksDraft.HomologyBaseChange.extendComplex φ).map (s • k) =
      φ s • (StacksDraft.HomologyBaseChange.extendComplex φ).map k := by
  ext i : 1
  exact extendScalars_map_smul φ s (k.f i)

/-- A morphism in the derived category out of a K-projective complex is the class of a chain
map. -/
alias Q_map_surjective_of_isKProjective :=
  AlgebraicGeometry.Q_map_surjective_of_isKProjective

variable {φ}

/-- **The canonical base-change isomorphism of Hom complexes on a chain map.**  If `e` is the
canonical identification `Hom^•_S(P, F) ⊗_S T ≅ Hom^•_T(P ⊗ T, F ⊗ T)`, it sends `a ⊗ g` to `a`
times the base change of `g`, for every chain map `g : P ⟶ F`. -/
theorem homComplexBaseChange_ofHom {P F : CochainComplex (ModuleCat.{u} S) ℤ}
    {e : (StacksDraft.HomologyBaseChange.extendComplex φ).obj (CochainComplex.HomComplexR S P F) ≅
      CochainComplex.HomComplexR T
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)}
    (he : StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso φ P F e)
    (a : T) (g : P ⟶ F) :
    (e.hom.f 0).hom (a ⊗ₜ[S, φ] (Cochain.ofHom g : Cochain P F 0)) =
      a • Cochain.ofHom ((StacksDraft.HomologyBaseChange.extendComplex φ).map g) := by
  let := φ.toModule
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  have hq : p = q := by omega
  subst hq
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  refine (he 0 p p hpq a 1 (Cochain.ofHom g) x).trans ?_
  rw [Cochain.ofHom_v, Cochain.smul_v, Cochain.ofHom_v]
  change _ = a • ((((StacksDraft.HomologyBaseChange.extendComplex φ).map g).f p).hom
    ((1 : T) ⊗ₜ[S, φ] x))
  exact (ModuleCat.ExtendScalars.smul_tmul φ a 1 ((g.f p).hom x)).symm

/-- **Termwise extension of scalars is additive on chain maps.** -/
theorem extendComplex_map_sub {P F : CochainComplex (ModuleCat.{u} S) ℤ} (k k' : P ⟶ F) :
    (StacksDraft.HomologyBaseChange.extendComplex φ).map (k - k') =
      (StacksDraft.HomologyBaseChange.extendComplex φ).map k -
        (StacksDraft.HomologyBaseChange.extendComplex φ).map k' := by
  ext i : 1
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change ((1 : T) ⊗ₜ[S, φ] ((k.f i - k'.f i) m) : (ModuleCat.extendScalars.{u, u, u} φ).obj
      (F.X i)) = (1 : T) ⊗ₜ[S, φ] (k.f i m) - (1 : T) ⊗ₜ[S, φ] (k'.f i m)
  exact TensorProduct.tmul_sub _ _ _

/-- The degree-zero cocycle underlying a degree-zero cycle of the Hom complex. -/
private def cocycleOfCycles {R : Type u} [CommRing R] (P F : CochainComplex (ModuleCat.{u} R) ℤ)
    (z : (CochainComplex.HomComplexR R P F).cycles 0) : Cocycle P F 0 :=
  Cocycle.mk (((CochainComplex.HomComplexR R P F).iCycles 0).hom z) 1 (zero_add 1) (by
    have h := congrArg (fun f => f.hom z) ((CochainComplex.HomComplexR R P F).iCycles_d 0 1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h)

variable (φ) in
/-- **The generator survives base change, on representatives.**  Let `P` be a bounded above
complex of projective `S`-modules and `F` a complex of `S`-modules, let
`e : Hom^•_S(P, F) ⊗_S T ≅ Hom^•_T(P ⊗ T, F ⊗ T)` be the canonical identification and suppose
the degree-zero cycles of `Hom^•_S(P, F)` base change (`hcyc`).  Suppose moreover that the
endomorphisms of `P` in `D(S)` are scalars and that a chain map whose class vanishes in `D(S)` has
a base change whose class vanishes in `D(T)` (`hext`, which holds as soon as derived extension of
scalars is computed termwise at `P`).  If the class of `f₀ : P ⟶ F` is a postcomposition
generator in `D(S)`, the class of `f₀ ⊗ T` is one in `D(T)`.

Every morphism `P ⊗ T ⟶ F ⊗ T` in `D(T)` is the class of a chain map, that is of a degree-zero
cocycle of `Hom^•_T(P ⊗ T, F ⊗ T)`; by `hcyc` and `e` these cocycles are `T`-linear combinations
of the base changes `g ⊗ T` of chain maps `g : P ⟶ F`
(`Dualizing.homComplexBaseChange_ofHom`), and each such class is `φ s` times the class of
`f₀ ⊗ T`, because the class of `g` is `s` times that of `f₀`. -/
theorem isPostcompGenerator_Q_map_extend
    (P F : CochainComplex (ModuleCat.{u} S) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i, Projective (P.X i)]
    (e : (StacksDraft.HomologyBaseChange.extendComplex φ).obj (CochainComplex.HomComplexR S P F) ≅
      CochainComplex.HomComplexR T
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F))
    (he : StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso φ P F e)
    (hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison φ
      (CochainComplex.HomComplexR S P F) 0))
    (hscal : ∀ a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P, ∃ s : S, a = s • 𝟙 _)
    (hext : ∀ k : P ⟶ F, DerivedCategory.Q.map k = 0 →
      DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map k) = 0)
    (f₀ : P ⟶ F) (hf₀ : IsPostcompGenerator (DerivedCategory.Q.map f₀)) :
    IsPostcompGenerator
      (DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map f₀)) := by
  have : ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P).IsStrictlyLE dP := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} φ)
      (P.isZero_of_isStrictlyLE dP i hi)
  have : ∀ i : ℤ, Projective (((StacksDraft.HomologyBaseChange.extendComplex φ).obj P).X i) :=
    fun i => projective_extendScalars φ (P.X i)
  have : ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ dP
  let Θ := StacksDraft.HomologyBaseChange.cyclesComparison φ (CochainComplex.HomComplexR S P F) 0 ≫
    HomologicalComplex.cyclesMap e.hom 0
  have : IsIso Θ := by
    have : IsIso (HomologicalComplex.cyclesMap e.hom 0) :=
      (HomologicalComplex.cyclesMapIso e 0).isIso_hom
    infer_instance
  -- the chain map of a degree-zero cycle of `Hom^•_T(P ⊗ T, F ⊗ T)`, `T`-linearly
  let χ : (CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).cycles 0 →ₗ[T]
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P ⟶
        (StacksDraft.HomologyBaseChange.extendComplex φ).obj F) :=
    { toFun := fun w => Cocycle.homOf (cocycleOfCycles _ _ w)
      map_add' := fun w₁ w₂ => by
        ext i : 1
        exact congrArg (fun c : Cochain ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F) 0 => c.v i i (add_zero i))
          (((CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0).hom.map_add
              w₁ w₂)
      map_smul' := fun t w => by
        ext i : 1
        exact congrArg (fun c : Cochain ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F) 0 => c.v i i (add_zero i))
          (((CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0).hom.map_smul
              t w) }
  have hχ : ∀ (w : (CochainComplex.HomComplexR T
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).cycles 0)
      (k : (StacksDraft.HomologyBaseChange.extendComplex φ).obj P ⟶
        (StacksDraft.HomologyBaseChange.extendComplex φ).obj F),
      ((CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0).hom w =
          Cochain.ofHom k → χ w = k := by
    intro w k hk
    ext i : 1
    change (((CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0).hom w).v i i
        (add_zero i) = k.f i
    rw [hk, Cochain.ofHom_v]
  let L : (ModuleCat.extendScalars.{u, u, u} φ).obj
      ((CochainComplex.HomComplexR S P F).cycles 0) →ₗ[T]
      (DerivedCategory.Q.obj ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P) ⟶
        DerivedCategory.Q.obj ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)) :=
    (DerivedCategory.Q.mapLinearMap T) ∘ₗ χ ∘ₗ Θ.hom
  let N := Submodule.span T
    {DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map f₀)}
  -- on `1 ⊗ z` the value of `L` is the class of a base change, a multiple of that of `f₀ ⊗ T`
  have hone : ∀ (t : T) (z : (CochainComplex.HomComplexR S P F).cycles 0),
      L (t ⊗ₜ[S, φ] z) ∈ N := by
    intro t z
    let g : P ⟶ F := Cocycle.homOf (cocycleOfCycles P F z)
    have hg : ((CochainComplex.HomComplexR S P F).iCycles 0).hom z = Cochain.ofHom g :=
      (Cocycle.cochain_ofHom_homOf_eq_coe (cocycleOfCycles P F z)).symm
    have hi : ((CochainComplex.HomComplexR T
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0).hom
          (Θ.hom (t ⊗ₜ[S, φ] z)) =
        (e.hom.f 0).hom (t ⊗ₜ[S, φ] ((CochainComplex.HomComplexR S P F).iCycles 0).hom z) := by
      have h := congrArg (fun k => k.hom (t ⊗ₜ[S, φ] z))
        (show Θ ≫ (CochainComplex.HomComplexR T
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
            ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).iCycles 0 =
            (ModuleCat.extendScalars.{u, u, u} φ).map
              ((CochainComplex.HomComplexR S P F).iCycles 0) ≫ e.hom.f 0 by
          simp only [Θ, Category.assoc, HomologicalComplex.cyclesMap_i,
            StacksDraft.HomologyBaseChange.cyclesComparison_iCycles_assoc])
      exact h
    have hL : L (t ⊗ₜ[S, φ] z) =
        t • DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map g) := by
      change DerivedCategory.Q.map (χ (Θ.hom (t ⊗ₜ[S, φ] z))) = _
      rw [hχ _ (t • (StacksDraft.HomologyBaseChange.extendComplex φ).map g) (by
        rw [hi, hg, homComplexBaseChange_ofHom he t g]
        refine Cochain.ext _ _ (fun p q hpq => ?_)
        have hq : p = q := by omega
        subst hq
        rw [Cochain.smul_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.smul_f_apply]),
        Functor.map_smul]
    obtain ⟨a, ha⟩ := hf₀ (DerivedCategory.Q.map g)
    obtain ⟨s, rfl⟩ := hscal a
    have hgs : DerivedCategory.Q.map (g - s • f₀) = 0 := by
      rw [Functor.map_sub, Functor.map_smul]
      dsimp only at ha
      rw [← ha, Linear.smul_comp, Category.id_comp, sub_self]
    have hext' := hext _ hgs
    rw [extendComplex_map_sub, extendComplex_map_smul, Functor.map_sub, Functor.map_smul,
      sub_eq_zero] at hext'
    rw [hL, hext']
    exact N.smul_mem _ (N.smul_mem _ (Submodule.subset_span (Set.mem_singleton _)))
  -- hence everywhere, `1 ⊗ z` spanning the base change
  have hall : ∀ y, L y ∈ N := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => convert N.add_mem h₁ h₂ using 1; exact L.map_add _ _
    | tmul b z => exact hone b z
  intro g
  obtain ⟨h, rfl⟩ := Q_map_surjective_of_isKProjective
    ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
    ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F) g
  let w : (CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).cycles 0 :=
    (CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
      ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)).cyclesMk (Cocycle.ofHom h).val 1
        (by simp) (Cocycle.δ_eq_zero (Cocycle.ofHom h) _)
  have hw : χ w = h := by
    apply hχ
    have hwi := HomologicalComplex.i_cyclesMk
      (CochainComplex.HomComplexR T ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F)) (Cocycle.ofHom h).val 1 (by simp)
      (Cocycle.δ_eq_zero (Cocycle.ofHom h) _)
    simpa [w, HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using hwi
  have hy := hall ((inv Θ).hom w)
  have hLw : L ((inv Θ).hom w) = DerivedCategory.Q.map h := by
    change DerivedCategory.Q.map (χ (Θ.hom ((inv Θ).hom w))) = _
    rw [← ModuleCat.comp_apply, IsIso.inv_hom_id, ModuleCat.id_apply, hw]
  rw [hLw] at hy
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨t • 𝟙 _, ?_⟩
  dsimp only
  rw [Linear.smul_comp, Category.id_comp, ht]

variable (φ) in
/-- **The generator survives derived base change, computed on representatives.**  This is
`Dualizing.isPostcompGenerator_Q_map_extend` read through derived extension of scalars: if the
comparison from derived to termwise extension of scalars is invertible at `P` and at `F` — at `P`
because it is K-flat, at `F` by Tor independence in the application — then derived extension of
scalars sends the class of `f₀` to a postcomposition generator.

The hypothesis `hext` of `Dualizing.isPostcompGenerator_Q_map_extend` is supplied by the
naturality of the comparison and its invertibility at `P`. -/
theorem isPostcompGenerator_derivedExtension_map
    (P F : CochainComplex (ModuleCat.{u} S) ℤ) (dP : ℤ) [P.IsStrictlyLE dP]
    [∀ i, Projective (P.X i)]
    (hP : IsIso ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app P))
    (hF : IsIso ((totalDerivedExtensionScalars.{u, u, u} φ).comparison.app F))
    (e : (StacksDraft.HomologyBaseChange.extendComplex φ).obj (CochainComplex.HomComplexR S P F) ≅
      CochainComplex.HomComplexR T
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj P)
        ((StacksDraft.HomologyBaseChange.extendComplex φ).obj F))
    (he : StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso φ P F e)
    (hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison φ
      (CochainComplex.HomComplexR S P F) 0))
    (hscal : ∀ a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P, ∃ s : S, a = s • 𝟙 _)
    (f₀ : P ⟶ F) (hf₀ : IsPostcompGenerator (DerivedCategory.Q.map f₀)) :
    IsPostcompGenerator
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.map (DerivedCategory.Q.map f₀)) := by
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  let := D.additive
  have hnat : ∀ k : P ⟶ F, D.functor.map (DerivedCategory.Q.map k) ≫ D.comparison.app F =
      D.comparison.app P ≫
        DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map k) :=
    fun k => D.comparison.naturality k
  have hext : ∀ k : P ⟶ F, DerivedCategory.Q.map k = 0 →
      DerivedCategory.Q.map ((StacksDraft.HomologyBaseChange.extendComplex φ).map k) = 0 := by
    intro k hk
    have h := hnat k
    rw [hk, Functor.map_zero, Limits.zero_comp] at h
    exact (cancel_epi (D.comparison.app P)).1 (h.symm.trans (Limits.comp_zero).symm)
  have hg := isPostcompGenerator_Q_map_extend φ P F dP e he hcyc hscal hext f₀ hf₀
  refine hg.of_conj (asIso (D.comparison.app P)).symm (asIso (D.comparison.app F)).symm ?_
  simp only [Iso.symm_inv, Iso.symm_hom, asIso_hom, asIso_inv]
  exact (((IsIso.eq_comp_inv (D.comparison.app F)).2 (hnat f₀)).trans
    (Category.assoc _ _ _)).symm

end

end Dualizing

end
