module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

@[expose] public section

/-!
# Uniform annihilation and factorisation bounds for restriction on Ext

Let `I` be an ideal of a Noetherian ring `A`.  Restricting a class in `Ext^p_A(M, N)` along
the inclusion `I ^ n M → M` kills it, or at least pushes it into `I ^ (n - c) Ext^p_A(M, N)`,
once `n` is large — with a bound `c` uniform in `n`.  This file collects those bounds and
their consequence for the inverse system of Ext groups of the adic reductions of a module.

## Main results

* `Stacks.AdicSystem.ExtIdealPowerRestriction.ext_ideal_power_restriction_factors`: in positive
  degree `p`, restriction
  `Ext^p_A(M, N) → Ext^p_A(I ^ n M, N)` factors through `Ext^p_A(M, I ^ ? N)` — precisely,
  through Ext into a shifted ideal power of the second argument.
* `Stacks.AdicSystem.ExtRestrictionVanishing.ext_ideal_power_restriction_eq_zero_of_annihilated`:
  if some positive power of
  `I` annihilates `N`, then in every positive degree the restriction map
  `Ext^p_A(M, N) → Ext^p_A(I ^ n M, N)` is zero for `n` large.  This is 0G3L with the target
  power of `I` annihilating `N`.
* `Stacks.ExtIdealPowerImage.range_ext_map_ideal_pow_le`: for a pseudo-coherent `K` in `D(A)`, the
  image of
  `Ext^p(K, I ^ n M)` in `Ext^p(K, M)` lies in `I ^ (n - c) Ext^p(K, M)` for one `c`
  independent of `n` and of the degree.
* `Stacks.AdicSystem.ExtEssentiallyConstant.ext_quotient_ideal_pow_essentially_constant`: if
  `Ext^j(K, N)` is `I`-power
  torsion for every finite `N` and every `j ≥ a`, then for `p ≥ a` the inverse system
  `n ↦ Ext^p(K, M ⧸ I ^ n M)` is essentially constant with value — and limit —
  `Ext^p(K, M)`.

## Implementation notes

Ext groups are `DerivedCategory.Ext` in `ModuleCat A`, and restriction along a module map is
`Ext.precomp`/`Ext.postcomp` with the degree-zero class of that map.  Essential constancy is
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith`.

Pseudo-coherence of an object of `D(A)` is part (2) of tag 064Q: representability by a
bounded-above complex of finite free modules.  It is taken from the conceptual library as
`StacksDraft.PseudoCoherence.IsPseudoCoherent`, which carries the tag; tag 064Q is not
claimed here.

## References

* [Stacks Project, Tag 0G3L](https://stacks.math.columbia.edu/tag/0G3L)
* [Stacks Project, Tag 0927](https://stacks.math.columbia.edu/tag/0927)
* [Stacks Project, Tag 0DYI](https://stacks.math.columbia.edu/tag/0DYI)
* [Stacks Project, Tag 0DYJ](https://stacks.math.columbia.edu/tag/0DYJ)
-/

/-! ## Tag 0G3L -/

section

open CategoryTheory CategoryTheory.Abelian

namespace Stacks.AdicSystem.ExtIdealPowerRestriction

universe w u v

/-- Artin–Rees gives a uniform power shift for lifting maps through a surjection onto a
submodule. -/
private theorem exists_pow_controlled_lift
    {R A B P : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (I : Ideal R) (f : A →ₗ[R] B) (K : Submodule R B) (hf : f.range = K) :
    ∃ c : ℕ, ∀ n ≥ c, ∀ h : P →ₗ[R] B, h.range ≤ (I ^ n • ⊤) ⊓ K →
      ∃ k : P →ₗ[R] A, f.comp k = h ∧ k.range ≤ I ^ (n - c) • ⊤ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul K
  refine ⟨c, ?_⟩
  intro n hn h hh
  let T : Submodule R A := I ^ (n - c) • ⊤
  have hT : h.range ≤ T.map f := by
    calc
      h.range ≤ (I ^ n • ⊤) ⊓ K := hh
      _ = I ^ (n - c) • (I ^ c • ⊤ ⊓ K) := hc n hn
      _ ≤ I ^ (n - c) • K := Submodule.smul_mono le_rfl inf_le_right
      _ = T.map f := by rw [Submodule.map_smul'', Submodule.map_top, hf]
  let fT : T →ₗ[R] T.map f :=
    LinearMap.codRestrict (T.map f) (f.domRestrict T) fun x => ⟨x, x.property, rfl⟩
  have hfT : Function.Surjective fT := by
    intro y
    obtain ⟨x, hx, hy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hy⟩
  let hT : P →ₗ[R] T.map f := h.codRestrict (T.map f) (fun x => hT ⟨x, rfl⟩)
  obtain ⟨kT, hkT⟩ := Module.projective_lifting_property fT hT hfT
  refine ⟨T.subtype.comp kT, ?_, ?_⟩
  · exact LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun hkT x)
  · rintro _ ⟨y, rfl⟩
    exact (kT y).property

/-- A finite free cover of an ideal power can be chosen compatibly with a fixed surjection
onto the original module. -/
private theorem exists_compatible_finite_presentation_idealPower
    {R : Type u} {F M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Small.{v} R]
    (I : Ideal R) (f : F →ₗ[R] M) (hf : Function.Surjective f) (n : ℕ) :
    let X : Submodule R M := I ^ n • ⊤
    ∃ (F' : Type v) (_ : AddCommGroup F') (_ : Module R F')
      (_ : Module.Free R F') (_ : Module.Finite R F')
      (g : F' →ₗ[R] X), Function.Surjective g ∧
      ∃ φ : F' →ₗ[R] F,
        f.comp φ = X.subtype.comp g ∧ φ.range ≤ I ^ n • ⊤ := by
  dsimp only
  let X : Submodule R M := I ^ n • ⊤
  have : Module.Finite R X := inferInstance
  obtain ⟨F', hG, hMod, hFree, hFin, g, hg⟩ := Module.exists_finite_presentation R X
  let : AddCommGroup F' := hG
  let : Module R F' := hMod
  let : Module.Free R F' := hFree
  let : Module.Finite R F' := hFin
  let T : Submodule R F := I ^ n • ⊤
  have hmap : T.map f = X := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
  let fT : T →ₗ[R] X :=
    LinearMap.codRestrict X (f.domRestrict T) (by
      intro x
      rw [← hmap]
      exact ⟨x, x.property, rfl⟩)
  have hfT : Function.Surjective fT := by
    intro y
    obtain ⟨x, hx, hy⟩ : (y : M) ∈ T.map f := hmap.symm ▸ y.property
    exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [fT] using hy)⟩
  obtain ⟨φT, hφT⟩ := Module.projective_lifting_property fT g hfT
  refine ⟨F', hG, hMod, hFree, hFin, g, hg, T.subtype.comp φT, ?_, ?_⟩
  · exact LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun hφT x)
  · rintro _ ⟨y, rfl⟩
    exact (φT y).property

/-- The map between kernels of compatible presentations carries the kernel of a high ideal
power into a uniformly shifted ideal power of the original kernel. -/
private theorem exists_kernel_map_idealPower_bound
    {R : Type u} {F M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup F] [Module R F] [Module.Finite R F]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) (f : F →ₗ[R] M) :
    ∃ c : ℕ, ∀ n ≥ c,
      ∀ {F' X : Type v} [AddCommGroup F'] [Module R F']
        [AddCommGroup X] [Module R X]
        (g : F' →ₗ[R] X) (φ : F' →ₗ[R] F)
        (hker : ∀ x ∈ g.ker, φ x ∈ f.ker) (_ : φ.range ≤ I ^ n • ⊤),
        let κ : g.ker →ₗ[R] f.ker :=
          LinearMap.codRestrict f.ker (φ.domRestrict g.ker)
            (fun x => hker x x.property)
        κ.range ≤ I ^ (n - c) • ⊤ := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul f.ker
  refine ⟨c, ?_⟩
  intro n hn F' X _ _ _ _ g φ hker hφ
  dsimp only
  let κ : g.ker →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (φ.domRestrict g.ker) (fun x => hker x x.property)
  have hbound : (I ^ n • ⊤ : Submodule R F) ⊓ f.ker ≤
      (I ^ (n - c) • ⊤ : Submodule R f.ker).map f.ker.subtype := by
    calc
      (I ^ n • ⊤ : Submodule R F) ⊓ f.ker =
          I ^ (n - c) • ((I ^ c • ⊤ : Submodule R F) ⊓ f.ker) := hc n hn
      _ ≤ I ^ (n - c) • f.ker := Submodule.smul_mono le_rfl inf_le_right
      _ = (I ^ (n - c) • ⊤ : Submodule R f.ker).map f.ker.subtype := by
        rw [Submodule.map_smul'', Submodule.map_top]
        simp
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, hz, heq⟩ := hbound ⟨hφ ⟨y, rfl⟩, hker y y.property⟩
  rwa [show κ y = z from Subtype.ext heq.symm]

/-- A commutative square of linear maps induces a morphism between their kernel short
complexes. -/
private def shortComplexKerHom
    {R : Type u} [Ring R]
    {F M F' X : Type v}
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    [AddCommGroup F'] [Module R F'] [AddCommGroup X] [Module R X]
    (f : F →ₗ[R] M) (g : F' →ₗ[R] X)
    (φ : F' →ₗ[R] F) (ψ : X →ₗ[R] M)
    (h : f.comp φ = ψ.comp g) : g.shortComplexKer ⟶ f.shortComplexKer where
  τ₁ := ModuleCat.ofHom <| LinearMap.codRestrict f.ker (φ.domRestrict g.ker) (by
    intro x
    change f (φ x) = 0
    have hh := LinearMap.congr_fun h (x : F')
    simpa [x.property] using hh)
  τ₂ := ModuleCat.ofHom φ
  τ₃ := ModuleCat.ofHom ψ
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext x
    exact LinearMap.congr_fun h x

/-- A map whose image lies in an ideal power induces additive restriction of Hom into a
submodule containing the corresponding ideal power of the target. -/
private def homBound
    {R : Type u} [CommRing R]
    {X K N : Type v}
    [AddCommGroup X] [Module R X]
    [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (a : X →ₗ[R] K)
    (ha : a.range ≤ I ^ m • ⊤)
    (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y) :
    (ModuleCat.of R K ⟶ ModuleCat.of R N) →+
      (ModuleCat.of R X ⟶ ModuleCat.of R Y) where
  toFun f := ModuleCat.ofHom <| LinearMap.codRestrict Y (f.hom.comp a) (by
    intro x
    exact hY ((Submodule.smul_top_le_comap_smul_top (I ^ m) f.hom) (ha ⟨x, rfl⟩)))
  map_zero' := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl

private theorem homBound_comp_subtype
    {R : Type u} [CommRing R]
    {X K N : Type v}
    [AddCommGroup X] [Module R X]
    [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (a : X →ₗ[R] K)
    (ha : a.range ≤ I ^ m • ⊤)
    (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y)
    (f : ModuleCat.of R K ⟶ ModuleCat.of R N) :
    homBound I m a ha Y hY f ≫ ModuleCat.ofHom Y.subtype =
      ModuleCat.ofHom a ≫ f := by
  ext x
  rfl

/-- Degree-zero Ext restriction expressed through the additive Hom equivalence. -/
private noncomputable def extZeroBound
    {R : Type u} [CommRing R] [Small.{v} R]
    {X K N : Type v}
    [AddCommGroup X] [Module R X]
    [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (a : X →ₗ[R] K)
    (ha : a.range ≤ I ^ m • ⊤)
    (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y) :
    Ext (ModuleCat.of R K) (ModuleCat.of R N) 0 →+
      Ext (ModuleCat.of R X) (ModuleCat.of R Y) 0 :=
  Ext.addEquiv₀.symm.toAddMonoidHom.comp
    ((homBound I m a ha Y hY).comp Ext.addEquiv₀.toAddMonoidHom)

private theorem extZeroBound_naturality
    {R : Type u} [CommRing R] [Small.{v} R]
    {X K N : Type v}
    [AddCommGroup X] [Module R X]
    [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (a : X →ₗ[R] K)
    (ha : a.range ≤ I ^ m • ⊤)
    (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y)
    (x : Ext (ModuleCat.of R K) (ModuleCat.of R N) 0) :
    (extZeroBound I m a ha Y hY x).comp (Ext.mk₀ (ModuleCat.ofHom Y.subtype))
        (add_zero 0) =
      (Ext.mk₀ (ModuleCat.ofHom a)).comp x (zero_add 0) := by
  let f := Ext.addEquiv₀ x
  have hx : Ext.mk₀ f = x := Ext.mk₀_addEquiv₀_apply x
  rw [← hx]
  have hmap : extZeroBound I m a ha Y hY (Ext.mk₀ f) =
      Ext.mk₀ (homBound I m a ha Y hY f) := by
    simp [extZeroBound, ← Ext.addEquiv₀_symm_apply]
  rw [hmap, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, homBound_comp_subtype I m a ha Y hY f]

private theorem extZeroBound_mk₀
    {R : Type u} [CommRing R] [Small.{v} R]
    {X K N : Type v}
    [AddCommGroup X] [Module R X]
    [AddCommGroup K] [Module R K]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (a : X →ₗ[R] K)
    (ha : a.range ≤ I ^ m • ⊤)
    (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y)
    (f : ModuleCat.of R K ⟶ ModuleCat.of R N) :
    extZeroBound I m a ha Y hY (Ext.mk₀ f) = Ext.mk₀ (homBound I m a ha Y hY f) := by
  simp [extZeroBound, ← Ext.addEquiv₀_symm_apply]

/-- In degree zero, controlled Hom restriction commutes with a square of module maps. -/
private theorem extZeroBound_comm
    {R : Type u} [CommRing R] [Small.{v} R]
    {K F K' F' N : Type v}
    [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [AddCommGroup K'] [Module R K'] [AddCommGroup F'] [Module R F']
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (m : ℕ) (Y : Submodule R N) (hY : I ^ m • ⊤ ≤ Y)
    (κ : K' →ₗ[R] K) (φ : F' →ₗ[R] F)
    (i : K →ₗ[R] F) (i' : K' →ₗ[R] F')
    (hsq : φ.comp i' = i.comp κ)
    (hκ : κ.range ≤ I ^ m • ⊤) (hφ : φ.range ≤ I ^ m • ⊤)
    (x : Ext (ModuleCat.of R F) (ModuleCat.of R N) 0) :
    extZeroBound I m κ hκ Y hY ((Ext.mk₀ (ModuleCat.ofHom i)).comp x (zero_add 0)) =
      (Ext.mk₀ (ModuleCat.ofHom i')).comp (extZeroBound I m φ hφ Y hY x)
        (zero_add 0) := by
  let f := Ext.addEquiv₀ x
  have hx : Ext.mk₀ f = x := Ext.mk₀_addEquiv₀_apply x
  rw [← hx, Ext.mk₀_comp_mk₀, extZeroBound_mk₀, extZeroBound_mk₀, Ext.mk₀_comp_mk₀]
  congr 1
  have : Mono (ModuleCat.ofHom Y.subtype) :=
    (ModuleCat.mono_iff_injective _).mpr Y.injective_subtype
  apply (cancel_mono (ModuleCat.ofHom Y.subtype)).mp
  rw [Category.assoc, homBound_comp_subtype, homBound_comp_subtype, ← Category.assoc]
  have hs : ModuleCat.ofHom i' ≫ ModuleCat.ofHom φ =
      ModuleCat.ofHom κ ≫ ModuleCat.ofHom i := by
    ext z
    exact LinearMap.congr_fun hsq z
  rw [← hs, Category.assoc]

/-- A map on the first two terms of compatible short exact sequences descends through the
Ext connecting map when it respects the kernel of that map. -/
private theorem ext_descend_short
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    [Projective S.X₂] (Y Y' : C) (q : ℕ)
    (r₁ : Ext S.X₁ Y q →+ Ext S'.X₁ Y' q)
    (r₂ : Ext S.X₂ Y q →+ Ext S'.X₂ Y' q)
    (hcomm : ∀ x,
      r₁ ((Ext.mk₀ S.f).comp x (zero_add q)) =
        (Ext.mk₀ S'.f).comp (r₂ x) (zero_add q))
    (τ : S' ⟶ S) (b : Y' ⟶ Y)
    (hfac : ∀ x, (r₁ x).comp (Ext.mk₀ b) (add_zero q) =
      (Ext.mk₀ τ.τ₁).comp x (zero_add q)) :
    ∃ l : Ext S.X₃ Y (q + 1) →+ Ext S'.X₃ Y' (q + 1),
      (∀ x, l (hS.extClass.comp x (add_comm 1 q)) =
        hS'.extClass.comp (r₁ x) (add_comm 1 q)) ∧
      ((Ext.mk₀ b).postcomp S'.X₃ (add_zero (q + 1))).comp l =
        (Ext.mk₀ τ.τ₃).precomp Y (zero_add (q + 1)) := by
  let d : Ext S.X₁ Y q →+ Ext S.X₃ Y (q + 1) :=
    hS.extClass.precomp Y (add_comm 1 q)
  let d' : Ext S'.X₁ Y' q →+ Ext S'.X₃ Y' (q + 1) :=
    hS'.extClass.precomp Y' (add_comm 1 q)
  have hd : Function.Surjective d := fun x =>
    Ext.contravariant_sequence_exact₃ hS Y x (Ext.eq_zero_of_projective _) (add_comm 1 q)
  have hk : d.ker ≤ (d'.comp r₁).ker := by
    intro x hx
    change d' (r₁ x) = 0
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS Y x (add_comm 1 q) hx
    rw [← hy, hcomm]
    exact hS'.extClass_comp_assoc (r₂ y) (h := add_comm 1 q)
  let l : Ext S.X₃ Y (q + 1) →+ Ext S'.X₃ Y' (q + 1) :=
    d.liftOfSurjective hd ⟨d'.comp r₁, hk⟩
  have hl : ∀ x, l (d x) = d' (r₁ x) := fun x => by
    unfold l
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨l, hl, ?_⟩
  · apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := hd z
    change (l (d x)).comp (Ext.mk₀ b) (add_zero (q + 1)) =
      (Ext.mk₀ τ.τ₃).comp (d x) (zero_add (q + 1))
    rw [hl]
    change (hS'.extClass.comp (r₁ x) (add_comm 1 q)).comp
        (Ext.mk₀ b) (add_zero (q + 1)) =
      (Ext.mk₀ τ.τ₃).comp (hS.extClass.comp x (add_comm 1 q))
        (zero_add (q + 1))
    simp only [Ext.comp_assoc_of_third_deg_zero, hfac x]
    rw [← Ext.comp_assoc_of_second_deg_zero, hS'.extClass_naturality hS τ]
    exact Ext.comp_assoc (Ext.mk₀ τ.τ₃) hS.extClass x
      (zero_add 1) (add_comm 1 q) (by omega)

/-- The degree-zero factorization is restriction of linear maps to ideal powers. -/
private theorem ext_ideal_power_restriction_factors_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
    {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M]
    (I : Ideal A) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      let P : Submodule A M := I ^ n • ⊤
      let Q : Submodule A N := I ^ (n - c) • ⊤
      ∃ lift : Ext (ModuleCat.of A M) (ModuleCat.of A N) 0 →+
          Ext (ModuleCat.of A P) (ModuleCat.of A Q) 0,
        ((Ext.mk₀ (ModuleCat.ofHom Q.subtype)).postcomp
            (ModuleCat.of A P) (add_zero 0)).comp lift =
          (Ext.mk₀ (ModuleCat.ofHom P.subtype)).precomp
            (ModuleCat.of A N) (zero_add 0) := by
  refine ⟨0, fun n hn => ?_⟩
  dsimp only [Nat.sub_zero]
  let P : Submodule A M := I ^ n • ⊤
  let Q : Submodule A N := I ^ n • ⊤
  have hP : P.subtype.range ≤ I ^ n • ⊤ := by simp [P]
  exact ⟨extZeroBound I n P.subtype hP Q le_rfl,
    AddMonoidHom.ext (extZeroBound_naturality I n P.subtype hP Q le_rfl)⟩

private theorem ext_ideal_power_restriction_factors_all
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
    {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M]
    (I : Ideal A) (p : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      let P : Submodule A M := I ^ n • ⊤
      let Q : Submodule A N := I ^ (n - c) • ⊤
      ∃ lift : Ext (ModuleCat.of A M) (ModuleCat.of A N) p →+
          Ext (ModuleCat.of A P) (ModuleCat.of A Q) p,
        ((Ext.mk₀ (ModuleCat.ofHom Q.subtype)).postcomp
            (ModuleCat.of A P) (add_zero p)).comp lift =
          (Ext.mk₀ (ModuleCat.ofHom P.subtype)).precomp
            (ModuleCat.of A N) (zero_add p) := by
  induction p generalizing M with
  | zero => exact ext_ideal_power_restriction_factors_zero I
  | succ p ih =>
    obtain ⟨F, hG, hMod, hFree, hFin, f, hf⟩ :=
      Module.exists_finite_presentation A M
    let : AddCommGroup F := hG
    let : Module A F := hMod
    let : Module.Free A F := hFree
    let : Module.Finite A F := hFin
    have : Module.Finite A f.ker := inferInstance
    have : Projective (ModuleCat.of A F) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis A F)
    obtain ⟨c, hc⟩ := exists_kernel_map_idealPower_bound I f
    obtain ⟨d, hd⟩ := ih (M := f.ker)
    refine ⟨c + d, ?_⟩
    intro n hn
    have hpow : n - (c + d) = n - c - d := by omega
    rw [hpow]
    let X : Submodule A M := I ^ n • ⊤
    let Y : Submodule A N := I ^ (n - c - d) • ⊤
    obtain ⟨F', hG', hMod', hFree', hFin', g, hg, φ, hsq, hφ⟩ :=
      exists_compatible_finite_presentation_idealPower I f hf n
    let : AddCommGroup F' := hG'
    let : Module A F' := hMod'
    let : Module.Free A F' := hFree'
    let : Module.Finite A F' := hFin'
    let S := f.shortComplexKer
    let S' := g.shortComplexKer
    let τ : S' ⟶ S := shortComplexKerHom f g φ X.subtype hsq
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hS' : S'.ShortExact := LinearMap.shortExact_shortComplexKer hg
    have hcn : c ≤ n := by omega
    let κ : g.ker →ₗ[A] f.ker :=
      LinearMap.codRestrict f.ker (φ.domRestrict g.ker) (by
        intro x
        change f (φ x) = 0
        have hh := LinearMap.congr_fun hsq (x : F')
        simpa [x.property] using hh)
    have hκ : κ.range ≤ I ^ (n - c) • ⊤ :=
      hc n hcn g φ (by
        intro x hx
        change f (φ x) = 0
        have hh := LinearMap.congr_fun hsq x
        have hx0 : g x = 0 := hx
        simpa [hx0] using hh) hφ
    have hsqker : φ.comp g.ker.subtype = f.ker.subtype.comp κ := by
      ext x
      rfl
    have hshift : n - c - d ≤ n - c := by omega
    have hκY : κ.range ≤ I ^ (n - c - d) • ⊤ :=
      hκ.trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right hshift))
    have hφY : φ.range ≤ I ^ (n - c - d) • ⊤ :=
      hφ.trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
    cases p with
    | zero =>
      let r₁ := extZeroBound I (n - c - d) κ hκY Y le_rfl
      let r₂ := extZeroBound I (n - c - d) φ hφY Y le_rfl
      obtain ⟨l, _, hl⟩ := ext_descend_short hS hS' (ModuleCat.of A N)
        (ModuleCat.of A Y) 0 r₁ r₂ (by
          intro x
          exact extZeroBound_comm I (n - c - d) Y le_rfl κ φ
            f.ker.subtype g.ker.subtype hsqker hκY hφY x)
        τ (ModuleCat.ofHom Y.subtype) (by
          intro x
          exact extZeroBound_naturality I (n - c - d) κ hκY Y le_rfl x)
      exact ⟨l, hl⟩
    | succ p =>
      have hdn : d ≤ n - c := by omega
      obtain ⟨lK, hlK⟩ := hd (n - c) hdn
      let Kpow : Submodule A f.ker := I ^ (n - c) • ⊤
      let κpow : g.ker →ₗ[A] Kpow := κ.codRestrict Kpow (by
        intro x
        exact hκ ⟨x, rfl⟩)
      let r₁ : Ext (ModuleCat.of A f.ker) (ModuleCat.of A N) (p + 1) →+
          Ext (ModuleCat.of A g.ker) (ModuleCat.of A Y) (p + 1) :=
        ((Ext.mk₀ (ModuleCat.ofHom κpow)).precomp (ModuleCat.of A Y)
          (zero_add (p + 1))).comp lK
      let r₂ : Ext S.X₂ (ModuleCat.of A N) (p + 1) →+
          Ext S'.X₂ (ModuleCat.of A Y) (p + 1) := 0
      obtain ⟨l, _, hl⟩ := ext_descend_short hS hS' (ModuleCat.of A N)
        (ModuleCat.of A Y) (p + 1) r₁ r₂ (by
          intro x
          have hx : x = 0 := Ext.eq_zero_of_projective x
          subst x
          simp [r₁, r₂]) τ (ModuleCat.ofHom Y.subtype) (by
          intro x
          have hL := congrArg (fun h => h x) hlK
          have hL' : (lK x).comp (Ext.mk₀ (ModuleCat.ofHom Y.subtype))
                (add_zero (p + 1)) =
              (Ext.mk₀ (ModuleCat.ofHom Kpow.subtype)).comp x
                (zero_add (p + 1)) := hL
          change ((Ext.mk₀ (ModuleCat.ofHom κpow)).comp (lK x) (zero_add (p + 1))).comp
              (Ext.mk₀ (ModuleCat.ofHom Y.subtype)) (add_zero (p + 1)) =
            (Ext.mk₀ τ.τ₁).comp x (zero_add (p + 1))
          rw [Ext.comp_assoc_of_third_deg_zero, hL',
            ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
          change (Ext.mk₀ (ModuleCat.ofHom (Kpow.subtype.comp κpow))).comp x
            (zero_add (p + 1)) =
            (Ext.mk₀ (ModuleCat.ofHom κ)).comp x (zero_add (p + 1))
          congr 1)
      exact ⟨l, hl⟩

/-- **Stacks 0G3L.** Restriction on positive-degree Ext from a finite module to a sufficiently
high ideal power factors through Ext into a shifted ideal power of the second module. -/
@[stacks 0G3L]
public theorem ext_ideal_power_restriction_factors
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
    {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M]
    (I : Ideal A) (p : ℕ) (_hp : 0 < p) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      let P : Submodule A M := I ^ n • ⊤
      let Q : Submodule A N := I ^ (n - c) • ⊤
      ∃ lift : Ext (ModuleCat.of A M) (ModuleCat.of A N) p →+
          Ext (ModuleCat.of A P) (ModuleCat.of A Q) p,
        ((Ext.mk₀ (ModuleCat.ofHom Q.subtype)).postcomp
            (ModuleCat.of A P) (add_zero p)).comp lift =
          (Ext.mk₀ (ModuleCat.ofHom P.subtype)).precomp
            (ModuleCat.of A N) (zero_add p) :=
  ext_ideal_power_restriction_factors_all I p

end Stacks.AdicSystem.ExtIdealPowerRestriction

end

/-! ## Tag 0927 -/

section

open CategoryTheory CategoryTheory.Abelian

namespace Stacks.AdicSystem.ExtRestrictionVanishing

universe u v

/-- **Stacks 0927.** If a power of an ideal annihilates `N`, then in every positive degree,
restriction on Ext from a finite module to some ideal power is zero. -/
@[stacks 0927]
public theorem ext_ideal_power_restriction_eq_zero_of_annihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Small.{v} A]
    {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M]
    (I : Ideal A) (hN : ∃ m : ℕ, 0 < m ∧ I ^ m • (⊤ : Submodule A N) = ⊥)
    (p : ℕ) (hp : 0 < p) :
    ∃ n : ℕ,
      let P : Submodule A M := I ^ n • ⊤
      (Ext.mk₀ (ModuleCat.ofHom P.subtype)).precomp
          (ModuleCat.of A N) (zero_add p) = 0 := by
  obtain ⟨m, _, hm⟩ := hN
  obtain ⟨c, hc⟩ :=
    Stacks.AdicSystem.ExtIdealPowerRestriction.ext_ideal_power_restriction_factors (M := M) (N := N)
      I p hp
  refine ⟨c + m, ?_⟩
  obtain ⟨lift, hlift⟩ := hc (c + m) (Nat.le_add_right c m)
  have hQ : I ^ (c + m - c) • (⊤ : Submodule A N) = ⊥ := by
    simpa only [Nat.add_sub_cancel_left] using hm
  have hsub : (I ^ (c + m - c) • (⊤ : Submodule A N)).subtype = 0 := by
    ext x
    have hx : (x : N) ∈ (⊥ : Submodule A N) := by
      rw [← hQ]
      exact x.property
    simpa using hx
  rw [hsub] at hlift
  simpa using hlift.symm

end Stacks.AdicSystem.ExtRestrictionVanishing

end

/-! ## Tag 0DYI -/

section

open CategoryTheory CochainComplex.HomComplex

namespace Stacks.ExtIdealPowerImage

universe u v

private theorem artinRees_image
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {L X : Type*} [AddCommGroup L] [Module A L] [Module.Finite A L]
    [AddCommGroup X] [Module A X]
    (I : Ideal A) (N : Submodule A L) (f : N →ₗ[A] X) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n → ∀ x : N,
      (x : L) ∈ I ^ n • (⊤ : Submodule A L) →
      f x ∈ I ^ (n - c) • (⊤ : Submodule A X) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨c, ?_⟩
  intro n hn x hx
  have hx' : (x : L) ∈ I ^ (n - c) • N := by
    have h : (x : L) ∈ I ^ n • (⊤ : Submodule A L) ⊓ N := ⟨hx, x.property⟩
    rw [hc n hn] at h
    exact (SetLike.coe_subset_coe.mpr (smul_mono_right (I ^ (n - c)) inf_le_right)) h
  have hy : x ∈ I ^ (n - c) • (⊤ : Submodule A N) := by
    have hmap : Submodule.map N.subtype (I ^ (n - c) • (⊤ : Submodule A N)) =
        I ^ (n - c) • N := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← hmap] at hx'
    obtain ⟨y, hy, heq⟩ := hx'
    simpa [Subtype.ext heq] using hy
  have hfmap : Submodule.map f (I ^ (n - c) • (⊤ : Submodule A N)) =
      I ^ (n - c) • LinearMap.range f := by
    rw [Submodule.map_smul'', Submodule.map_top]
  have hfx : f x ∈ I ^ (n - c) • LinearMap.range f := by
    rw [← hfmap]
    exact Submodule.mem_map_of_mem hy
  exact (SetLike.coe_subset_coe.mpr (smul_mono_right (I ^ (n - c)) le_top)) hfx

private theorem mem_ideal_smul_hom_of_basis
    {A : Type*} [CommRing A] {P M : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M]
    {ι : Type*} [Finite ι] (b : Module.Basis ι A P) (I : Ideal A) (n : ℕ)
    (f : P →ₗ[A] M)
    (hf : ∀ i, f (b i) ∈ I ^ n • (⊤ : Submodule A M)) :
    f ∈ I ^ n • (⊤ : Submodule A (P →ₗ[A] M)) := by
  classical
  let := Fintype.ofFinite ι
  let e := b.constr (M' := M) A
  let g := e.symm f
  have hgi (i : ι) : g i ∈ I ^ n • (⊤ : Submodule A M) := by
    simpa [g, e] using hf i
  have hsingle (i : ι) :
      LinearMap.single A (fun _ : ι => M) i (g i) ∈
        I ^ n • (⊤ : Submodule A (ι → M)) := by
    have hmap : LinearMap.single A (fun _ : ι => M) i (g i) ∈
        Submodule.map (LinearMap.single A (fun _ : ι => M) i)
          (I ^ n • (⊤ : Submodule A M)) :=
      Submodule.mem_map_of_mem (hgi i)
    rw [Submodule.map_smul'', Submodule.map_top] at hmap
    exact (SetLike.coe_subset_coe.mpr (smul_mono_right (I ^ n) le_top)) hmap
  have hg : g ∈ I ^ n • (⊤ : Submodule A (ι → M)) := by
    rw [← Finset.univ_sum_single g]
    exact Submodule.sum_mem _ (fun i _ => hsingle i)
  have hmap := Submodule.smul_top_le_comap_smul_top (I ^ n) e.toLinearMap
  have h := (SetLike.coe_subset_coe.mpr hmap) hg
  simpa [g, e] using h

private lemma cocycle_equivHomShift_symm_smul
    {A : Type*} [CommRing A]
    {E L : CochainComplex (ModuleCat A) ℤ} (p : ℤ)
    (r : A) (z : Cocycle E L p) :
    Cocycle.equivHomShift.symm (r • z) =
      r • (Cocycle.equivHomShift.symm z : E ⟶ L⟦p⟧) := by
  have hz : z.postcomp (r • 𝟙 L) = r • z := by
    ext i j hij
    simp [Cocycle.postcomp]
  rw [← hz, Cocycle.equivHomShift_symm_postcomp]
  simp

attribute [local instance] HasDerivedCategory.standard

private noncomputable def cocycleToDerived
    {A : Type*} [CommRing A]
    (E L : CochainComplex (ModuleCat A) ℤ) (p : ℤ) :
    Cocycle E L p →ₗ[A] ShiftedHom (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj L) p where
  toFun z := ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q
  map_add' x y := by simp
  map_smul' r x := by simp

private theorem cocycleToDerived_surjective
    {A : Type*} [CommRing A]
    (E L : CochainComplex (ModuleCat A) ℤ) (p : ℤ) [E.IsKProjective] :
    Function.Surjective (cocycleToDerived E L p) := by
  intro x
  let Qq := HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)
  let iE := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app E
  let iL := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app (L⟦p⟧)
  let sL := (DerivedCategory.Q.commShiftIso p).app L
  let xh : DerivedCategory.Qh.obj (Qq.obj E) ⟶
      DerivedCategory.Qh.obj (Qq.obj (L⟦p⟧)) :=
    iE.hom ≫ x ≫ sL.inv ≫ iL.inv
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective E (Qq.obj (L⟦p⟧))).surjective xh
  obtain ⟨g, rfl⟩ := Qq.map_surjective h
  refine ⟨Cocycle.equivHomShift g, ?_⟩
  dsimp [cocycleToDerived]
  simp only [AddEquiv.symm_apply_apply]
  change DerivedCategory.Q.map g ≫ sL.hom = x
  dsimp [xh] at hh
  apply (cancel_epi iE.hom).mp
  calc
    iE.hom ≫ (DerivedCategory.Q.map g ≫ sL.hom) =
        DerivedCategory.Qh.map (Qq.map g) ≫ iL.hom ≫ sL.hom := by
          simpa only [iE, iL, Qq, Functor.comp_obj, Iso.app_hom, Category.assoc] using
            congrArg (fun y => y ≫ sL.hom)
              (DerivedCategory.quotientCompQhIso_hom_naturality g).symm
    _ = (iE.hom ≫ x ≫ sL.inv ≫ iL.inv) ≫ iL.hom ≫ sL.hom := by rw [hh]
    _ = iE.hom ≫ x := by simp [Category.assoc]

private def cycleDifferential
    {A : Type*} [CommRing A]
    (E : CochainComplex (ModuleCat A) ℤ) (M : ModuleCat A) (p : ℤ) :
    (E.X (-p) ⟶ M) →ₗ[A] (E.X (-p - 1) ⟶ M) where
  toFun f := E.d (-p - 1) (-p) ≫ f
  map_add' f g := by simp
  map_smul' r f := by simp

private noncomputable def cyclesToCocycle
    {A : Type*} [CommRing A]
    (E : CochainComplex (ModuleCat A) ℤ) (M : ModuleCat A) (p : ℤ) :
    (cycleDifferential E M p).ker →ₗ[A]
      Cocycle E ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p where
  toFun f := Cocycle.toSingleMk f.1 (by omega) (-p - 1) (by omega) f.2
  map_add' f g := by
    apply Cocycle.ext
    apply (Cochain.toSingleEquiv (K := E) (X := M) (by omega : -p + p = 0)).injective
    simp [Cocycle.toSingleMk, Cochain.toSingleEquiv]
  map_smul' r f := by
    apply Cocycle.ext
    apply (Cochain.toSingleEquiv (K := E) (X := M) (by omega : -p + p = 0)).injective
    simp [Cocycle.toSingleMk, Cochain.toSingleEquiv]

private noncomputable def cyclesToExt
    {A : Type*} [CommRing A]
    (E : CochainComplex (ModuleCat A) ℤ) (M : ModuleCat A) (p : ℤ)
    {K : DerivedCategory (ModuleCat A)} (e : DerivedCategory.Q.obj E ≅ K) :
    (cycleDifferential E M p).ker →ₗ[A]
      DerivedCategory.Ext K ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M) p where
  toFun f := e.inv ≫ cocycleToDerived E ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p
      (cyclesToCocycle E M p f)
  map_add' f g := by simp
  map_smul' r f := by simp

private theorem cocycleToDerived_postcomp
    {A : Type*} [CommRing A]
    (E L L' : CochainComplex (ModuleCat A) ℤ) (p : ℤ)
    (z : Cocycle E L p) (g : L ⟶ L') :
    (cocycleToDerived E L' p) (z.postcomp g) =
      (cocycleToDerived E L p) z ≫ (DerivedCategory.Q.map g)⟦p⟧' := by
  simp [cocycleToDerived, Cocycle.equivHomShift_symm_postcomp, ShiftedHom.map,
    Functor.map_comp, Category.assoc]

private theorem mem_ideal_smul_catHom_of_free
    {A : Type*} [CommRing A] (P M : ModuleCat A)
    [Module.Free A P] [Module.Finite A P] (I : Ideal A) (n : ℕ)
    (f : P ⟶ ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M))) :
    f ≫ ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype ∈
      I ^ n • (⊤ : Submodule A (P ⟶ M)) := by
  let b := Module.Free.chooseBasis A P
  have hval : ∀ i, (f ≫ ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype).hom (b i) ∈
      I ^ n • (⊤ : Submodule A M) := fun i => (f (b i)).property
  have hm := mem_ideal_smul_hom_of_basis b I n
    (f ≫ ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype).hom hval
  have hmap := Submodule.smul_top_le_comap_smul_top (I ^ n)
    (ModuleCat.homLinearEquiv (S := A) (M := P) (N := M)).symm.toLinearMap
  have h := (SetLike.coe_subset_coe.mpr hmap) hm
  change (ModuleCat.homLinearEquiv (S := A) (M := P) (N := M)).symm
    ((ModuleCat.homLinearEquiv (S := A) (M := P) (N := M))
      (f ≫ ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype)) ∈
      I ^ n • (⊤ : Submodule A (P ⟶ M)) at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h


private theorem range_of_resolution
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (E : CochainComplex (ModuleCat A) ℤ) (p : ℤ)
    [E.IsKProjective] [Module.Free A (E.X (-p))]
    [Module.Finite A (E.X (-p))]
    (M : ModuleCat A) [Module.Finite A M]
    {K : DerivedCategory (ModuleCat A)} (e : DerivedCategory.Q.obj E ≅ K) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      Set.range (fun x : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
            (ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)))) p ↦
        x ≫ ((DerivedCategory.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype))⟦p⟧') ⊆
        ((I ^ (n - c) • (⊤ : Submodule A
          (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M) p)) :
            Submodule A _) : Set _) := by
  let : Module.Finite A (E.X (-p) ⟶ M) :=
    Module.Finite.equiv (ModuleCat.homLinearEquiv (S := A)
      (M := E.X (-p)) (N := M)).symm
  let N := (cycleDifferential E M p).ker
  obtain ⟨c, hc⟩ := artinRees_image I N (cyclesToExt E M p e)
  refine ⟨c, ?_⟩
  rintro n hn _ ⟨x, rfl⟩
  let B := ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M))
  let j : B ⟶ M := ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype
  obtain ⟨z, hz⟩ := cocycleToDerived_surjective E
    ((CochainComplex.singleFunctor (ModuleCat A) 0).obj B) p (e.hom ≫ x)
  obtain ⟨f, hf, hzf⟩ := Cocycle.toSingleMk_surjective z (-p)
    (by omega : -p + p = 0) (-p - 1) (by omega)
  let q : N := ⟨f ≫ j, by
    change E.d (-p - 1) (-p) ≫ (f ≫ j) = 0
    simp [← Category.assoc, hf]⟩
  have hqPow : (q : E.X (-p) ⟶ M) ∈ I ^ n • (⊤ : Submodule A (E.X (-p) ⟶ M)) :=
    mem_ideal_smul_catHom_of_free (E.X (-p)) M I n f
  have hq := hc n hn q hqPow
  have heq : (cyclesToExt E M p e) q = x ≫
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).map j)⟦p⟧' := by
    have hz' : (cocycleToDerived E ((CochainComplex.singleFunctor (ModuleCat A) 0).obj B) p)
        (Cocycle.toSingleMk f (by omega : -p + p = 0) (-p - 1) (by omega) hf) =
        e.hom ≫ x := by rw [hzf]; exact hz
    have hco : (cyclesToCocycle E M p) q =
        (Cocycle.toSingleMk f (by omega : -p + p = 0) (-p - 1) (by omega) hf).postcomp
          ((CochainComplex.singleFunctor (ModuleCat A) 0).map j) := by
      change Cocycle.toSingleMk (f ≫ j) (by omega : -p + p = 0) (-p - 1)
        (by omega : (-p - 1) + 1 = -p) (by simp [← Category.assoc, hf]) = _
      exact Cocycle.toSingleMk_postcomp f (by omega : -p + p = 0)
        (-p - 1) (by omega : (-p - 1) + 1 = -p) hf j
    calc
      (cyclesToExt E M p e) q =
          e.inv ≫ (cocycleToDerived E ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p)
            ((Cocycle.toSingleMk f (by omega : -p + p = 0) (-p - 1) (by omega) hf).postcomp
              ((CochainComplex.singleFunctor (ModuleCat A) 0).map j)) := by
                change e.inv ≫ (cocycleToDerived E
                  ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p)
                    ((cyclesToCocycle E M p) q) = _
                rw [hco]
      _ = e.inv ≫ ((cocycleToDerived E
            ((CochainComplex.singleFunctor (ModuleCat A) 0).obj B) p)
            (Cocycle.toSingleMk f (by omega : -p + p = 0) (-p - 1) (by omega) hf) ≫
            ((DerivedCategory.singleFunctor (ModuleCat A) 0).map j)⟦p⟧') := by
              rw [cocycleToDerived_postcomp]
              rfl
      _ = x ≫ ((DerivedCategory.singleFunctor (ModuleCat A) 0).map j)⟦p⟧' := by
            rw [hz']
            simp [Category.assoc]
  rwa [heq] at hq

/-- **Stacks 0DYI.** In each degree, the image in `Ext(K, M)` of the Ext group with second
argument `I ^ n M` is eventually contained in `I ^ (n - c) Ext(K, M)`. -/
@[stacks 0DYI]
public theorem range_ext_map_ideal_pow_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (M : ModuleCat.{v} A)
    [Module.Finite A M] (p : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
      Set.range (fun x : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
            (ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)))) p ↦
        x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype))⟦p⟧') ⊆
        ((I ^ (n - c) • (⊤ : Submodule A
          (DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p)) :
            Submodule A _) : Set _) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  let : E.IsStrictlyLE b := hb
  have hfree : ∀ i : ℤ, Module.Free A (E.X i) := fun i => (hE.finiteFree i).2
  have hfinite : ∀ i : ℤ, Module.Finite A (E.X i) := fun i => (hE.finiteFree i).1
  have hprojective : ∀ i : ℤ, CategoryTheory.Projective (E.X i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis A (E.X i))
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E b
  exact range_of_resolution I E p M e


end Stacks.ExtIdealPowerImage

end

/-! ## Tag 0DYJ -/

section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace Stacks.AdicSystem.ExtEssentiallyConstant

universe u v

attribute [local instance] HasDerivedCategory.standard

private alias cocycle_equivHomShift_symm_smul :=
  Stacks.ExtIdealPowerImage.cocycle_equivHomShift_symm_smul

private theorem cyclesToExt_surjective
    {A : Type*} [CommRing A]
    (E : CochainComplex (ModuleCat A) ℤ) (M : ModuleCat A) (p : ℤ)
    [E.IsKProjective]
    {K : DerivedCategory (ModuleCat A)} (e : DerivedCategory.Q.obj E ≅ K) :
    Function.Surjective (Stacks.ExtIdealPowerImage.cyclesToExt E M p e) := by
  intro x
  obtain ⟨z, hz⟩ := Stacks.ExtIdealPowerImage.cocycleToDerived_surjective E
    ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p (e.hom ≫ x)
  obtain ⟨f, hf, hzf⟩ := Cocycle.toSingleMk_surjective z (-p)
    (by omega : -p + p = 0) (-p - 1) (by omega)
  refine ⟨⟨f, hf⟩, ?_⟩
  change e.inv ≫ (Stacks.ExtIdealPowerImage.cocycleToDerived E
    ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M) p)
      (Cocycle.toSingleMk f (by omega) (-p - 1) (by omega) hf) = x
  rw [hzf, hz]
  simp

private theorem finite_ext_of_pseudoCoherent
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (M : ModuleCat.{v} A)
    [Module.Finite A M] (p : ℤ) :
    Module.Finite A
      (DerivedCategory.Ext K ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  let : E.IsStrictlyLE b := hb
  have hfree : ∀ i : ℤ, Module.Free A (E.X i) := fun i => (hE.finiteFree i).2
  have hfinite : ∀ i : ℤ, Module.Finite A (E.X i) := fun i => (hE.finiteFree i).1
  have hprojective : ∀ i : ℤ, CategoryTheory.Projective (E.X i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis A (E.X i))
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E b
  have : Module.Finite A (E.X (-p) ⟶ M) :=
    Module.Finite.equiv (ModuleCat.homLinearEquiv (S := A)
      (M := E.X (-p)) (N := M)).symm
  have : Module.Finite A (Stacks.ExtIdealPowerImage.cycleDifferential E M p).ker :=
    Module.Finite.of_injective (Stacks.ExtIdealPowerImage.cycleDifferential E M p).ker.subtype
      Subtype.val_injective
  exact Module.Finite.of_surjective (Stacks.ExtIdealPowerImage.cyclesToExt E M p e)
    (cyclesToExt_surjective E M p e)

private theorem exists_pow_annihilates
    {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (h : IsIPowerTorsion A N I) :
    ∃ t : ℕ, ∀ a ∈ I ^ t, ∀ x : N, a • x = 0 := by
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := A) (M := N))
  have hS : ∀ x ∈ S, ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
    intro x hx
    obtain ⟨n, _, hn⟩ := h x
    exact ⟨n, hn⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ x ∈ S, ∀ a ∈ I ^ t, a • x = 0 := by
    classical
    choose n hn using hS
    let m : N → ℕ := fun x => if hx : x ∈ S then n x hx else 0
    refine ⟨hSfin.toFinset.sup m, ?_⟩
    intro x hx a ha
    have hnm : n x hx ≤ hSfin.toFinset.sup m := by
      simpa [m, hx] using (Finset.le_sup (f := m) (hSfin.mem_toFinset.mpr hx))
    exact hn x hx a (Ideal.pow_le_pow_right hnm ha)
  refine ⟨t, fun a ha x => ?_⟩
  let T : Submodule A N := {
    carrier := {x | ∀ a ∈ I ^ t, a • x = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy a ha
      simp [smul_add, hx a ha, hy a ha]
    smul_mem' := by
      intro r x hx a ha
      rw [smul_comm]
      simp [hx a ha]
  }
  have htop : T = ⊤ := by
    apply top_unique
    rw [← hSspan]
    exact Submodule.span_le.mpr ht
  have hx : x ∈ T := htop.symm ▸ Submodule.mem_top
  exact hx a ha

private theorem exists_zero_ext_inclusion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (p : ℤ)
    (M : ModuleCat.{v} A) [Module.Finite A M]
    [Module.Finite A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p)]
    (h : IsIPowerTorsion A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p) I) :
    ∃ n : ℕ, ∀ x : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        (ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)))) p,
      x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype))⟦p⟧' = 0 := by
  obtain ⟨t, ht⟩ := exists_pow_annihilates I h
  obtain ⟨c, hc⟩ := Stacks.ExtIdealPowerImage.range_ext_map_ideal_pow_le I K hK M p
  refine ⟨c + t, fun x => ?_⟩
  have hpow : (I ^ t • (⊤ : Submodule A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p))) = ⊥ := by
    apply eq_bot_iff.mpr
    rw [Submodule.smul_le]
    intro a ha y _
    simpa using ht a ha y
  have hx := hc (c + t) (Nat.le_add_right c t) (show _ ∈ Set.range _ from ⟨x, rfl⟩)
  simpa [Nat.add_sub_cancel_left, hpow] using hx

private theorem essentiallyConstantWith_of_eventually_factors
    {C : Type*} [Category C] (E : ℕᵒᵖ ⥤ C) (X : C)
    (π : (Functor.const ℕᵒᵖ).obj X ⟶ E) (n : ℕ)
    [Mono (π.app (op n))]
    (hfac : ∀ j : ℕ, n ≤ j → ∃ k : ℕ, ∃ h : j ≤ k,
      ∃ r : E.obj (op k) ⟶ X,
        E.map (homOfLE h).op = r ≫ π.app (op j)) :
    ∃ (m : ℕᵒᵖ) (s : E.obj m ⟶ X),
      EssentiallyConstantPro.IsEssentiallyConstantWith E (Cone.mk X π) m s := by
  obtain ⟨m, hnm, s, hs⟩ := hfac n le_rfl
  have hret : π.app (op m) ≫ s = 𝟙 X := by
    apply (cancel_mono (π.app (op n))).mp
    calc
      (π.app (op m) ≫ s) ≫ π.app (op n) =
          π.app (op m) ≫ E.map (homOfLE hnm).op := by rw [Category.assoc, hs]
      _ = π.app (op n) := by simpa using (π.naturality (homOfLE hnm).op).symm
      _ = 𝟙 X ≫ π.app (op n) := by simp
  refine ⟨op m, s, ⟨hret, ?_⟩⟩
  intro j
  let q := max m (max n j.unop)
  have hqn : n ≤ q := (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  obtain ⟨k, hqk, r, hr⟩ := hfac q hqn
  have hmk : m ≤ k := (Nat.le_max_left ..).trans hqk
  have hnk : n ≤ k := (Nat.le_max_left ..).trans
    ((Nat.le_max_right ..).trans hqk)
  have hjk : j.unop ≤ k := (Nat.le_max_right ..).trans
    ((Nat.le_max_right ..).trans hqk)
  have hqm : m ≤ q := Nat.le_max_left ..
  have hqj : j.unop ≤ q := (Nat.le_max_right ..).trans (Nat.le_max_right ..)
  have hπn : π.app (op k) ≫ E.map (homOfLE hnk).op = π.app (op n) := by
    simpa using (π.naturality (homOfLE hnk).op).symm
  have hcompare : E.map (homOfLE hmk).op ≫ s = r := by
    apply (cancel_mono (π.app (op n))).mp
    calc
      (E.map (homOfLE hmk).op ≫ s) ≫ π.app (op n) =
          E.map (homOfLE hmk).op ≫ E.map (homOfLE hnm).op := by
            rw [Category.assoc, hs]
      _ = E.map (homOfLE hnk).op := by
        rw [← E.map_comp]
        congr 1
      _ = E.map (homOfLE hqk).op ≫ E.map (homOfLE hqn).op := by
        rw [← E.map_comp]
        congr 1
      _ = r ≫ π.app (op n) := by
        rw [hr, Category.assoc]
        congr 1
        simpa using (π.naturality (homOfLE hqn).op).symm
  refine ⟨op k, (homOfLE hmk).op, (homOfLE hjk).op, ?_⟩
  calc
    E.map (homOfLE hjk).op =
        E.map (homOfLE hqk).op ≫ E.map (homOfLE hqj).op := by
          rw [← E.map_comp]
          congr 1
    _ = r ≫ π.app j := by
      rw [hr, Category.assoc]
      congr 1
      simpa using (π.naturality (homOfLE hqj).op).symm
    _ = E.map (homOfLE hmk).op ≫ s ≫ π.app j := by
      rw [← hcompare, Category.assoc]

private abbrev quotientPowShortComplex
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    ShortComplex (ModuleCat A) :=
  ModuleCat.shortComplexOfCompEqZero
    (I ^ n • (⊤ : Submodule A M)).subtype
    (I ^ n • (⊤ : Submodule A M)).mkQ
    (LinearMap.exact_subtype_mkQ _).linearMap_comp_eq_zero

private theorem quotientPowShortExact
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    (quotientPowShortComplex I M n).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (LinearMap.exact_subtype_mkQ _)
    (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _)

private def quotientPowShortComplexMap
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A)
    {n m : ℕ} (hnm : n ≤ m) :
    quotientPowShortComplex I M m ⟶ quotientPowShortComplex I M n where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion (Submodule.pow_smul_top_le I M hnm))
  τ₂ := 𝟙 _
  τ₃ := ModuleCat.ofHom (Submodule.factorPow I M hnm)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def powToPowSubmodule
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A)
    (n t : ℕ) :
    ↥(I ^ (t + n) • (⊤ : Submodule A M)) →ₗ[A]
      ↥(I ^ t • (⊤ : Submodule A ↥(I ^ n • (⊤ : Submodule A M)))) :=
  (Submodule.inclusion (Submodule.pow_smul_top_le I M
    (show n ≤ t + n by omega))).codRestrict _ (by
    intro x
    apply (Submodule.mem_smul_top_iff (I ^ t)
      (I ^ n • (⊤ : Submodule A M)) _).2
    simpa only [pow_add, Submodule.mul_smul, Submodule.inclusion_apply] using x.property)

private theorem powInclusion_factor
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A)
    (n t : ℕ) :
    ModuleCat.ofHom (Submodule.inclusion (Submodule.pow_smul_top_le I M
      (show n ≤ t + n by omega))) =
      ModuleCat.ofHom (powToPowSubmodule I M n t) ≫
        ModuleCat.ofHom
          (I ^ t • (⊤ : Submodule A ↥(I ^ n • (⊤ : Submodule A M)))).subtype := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

private theorem exists_zero_ext_pow_transition
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (M : ModuleCat.{v} A)
    [Module.Finite A M] (p : ℤ)
    (h : ∀ (N : ModuleCat.{v} A) [Module.Finite A N],
      IsIPowerTorsion A
        (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj N) p) I)
    (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m,
      ∀ x : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A ↥(I ^ m • (⊤ : Submodule A M)))) p,
        x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.inclusion
            (Submodule.pow_smul_top_le I M hnm))))⟦p⟧' = 0 := by
  let P : Submodule A M := I ^ n • ⊤
  have : Module.Finite A P := inferInstance
  have : Module.Finite A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A P)) p) := finite_ext_of_pseudoCoherent K hK _ p
  obtain ⟨t, ht⟩ := exists_zero_ext_inclusion I K hK p
    (ModuleCat.of A P) (h (ModuleCat.of A P))
  refine ⟨t + n, by omega, fun x => ?_⟩
  have hf := powInclusion_factor I M n t
  change ModuleCat.ofHom (Submodule.inclusion
      (Submodule.pow_smul_top_le I M (show n ≤ t + n by omega))) = _ at hf
  rw [hf, Functor.map_comp, Functor.map_comp, ← Category.assoc]
  exact ht _

private theorem linearCoyoneda_isHomological
    {A : Type*} [CommRing A] {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (K : C) :
    ((linearCoyoneda A C).obj (op K)).IsHomological where
  exact T hT := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    ((ShortComplex.ab_exact_iff_function_exact _).1
      ((preadditiveCoyoneda.obj (op K)).map_distinguished_exact T hT))

private theorem mono_ext_quotient_of_zero_inclusion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (M : ModuleCat.{v} A) (p : ℤ) (n : ℕ)
    (hzero : ∀ x : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        (ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M)))) p,
      x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).subtype))⟦p⟧' = 0) :
    Mono (ModuleCat.ofHom (Linear.rightComp A K
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ))⟦p⟧'))) := by
  let F := (linearCoyoneda A (DerivedCategory (ModuleCat.{v} A))).obj (op K)
  let : F.IsHomological := linearCoyoneda_isHomological K
  let : F.ShiftSequence ℤ := Functor.ShiftSequence.tautological F ℤ
  let hS := quotientPowShortExact I M n
  let T := hS.singleTriangle
  have hex := F.homologySequence_exact₂ T hS.singleTriangle_distinguished p
  have hf : ((F.shift p).map T.mor₁) = 0 := ModuleCat.hom_ext (LinearMap.ext hzero)
  exact hex.mono_g hf

private theorem ext_quotient_transition_factors
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (M : ModuleCat.{v} A) (p : ℤ) {n m : ℕ} (hnm : n ≤ m)
    [Mono (ModuleCat.ofHom (Linear.rightComp A K
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ))⟦p⟧')))]
    (hzero : ∀ x : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
        (ModuleCat.of A ↥(I ^ m • (⊤ : Submodule A M)))) (p + 1),
      x ≫ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (Submodule.inclusion
          (Submodule.pow_smul_top_le I M hnm))))⟦p + 1⟧' = 0) :
    ∃ r : ModuleCat.of A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A (M ⧸ (I ^ m • ⊤ : Submodule A M)))) p) ⟶
      ModuleCat.of A
        (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p),
      ModuleCat.ofHom (Linear.rightComp A K
        (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.factorPow I M hnm)))⟦p⟧')) =
        r ≫ ModuleCat.ofHom (Linear.rightComp A K
          (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
            (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ))⟦p⟧')) := by
  let F := (linearCoyoneda A (DerivedCategory (ModuleCat.{v} A))).obj (op K)
  let : F.IsHomological := linearCoyoneda_isHomological K
  let : F.ShiftSequence ℤ := Functor.ShiftSequence.tautological F ℤ
  let hSn := quotientPowShortExact I M n
  let hSm := quotientPowShortExact I M m
  let Tn := hSn.singleTriangle
  let Tm := hSm.singleTriangle
  let φ : Tm ⟶ Tn :=
    ShortComplex.ShortExact.singleTriangle.map hSm hSn
      (quotientPowShortComplexMap I M hnm)
  have : Mono ((F.shift p).map Tn.mor₂) := by
    change Mono (ModuleCat.ofHom (Linear.rightComp A K
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ))⟦p⟧')))
    infer_instance
  have hz : (F.shift (p + 1)).map φ.hom₁ = 0 := ModuleCat.hom_ext (LinearMap.ext hzero)
  have hc : (F.shift p).map φ.hom₃ ≫
      F.homologySequenceδ Tn p (p + 1) rfl = 0 := by
    rw [F.homologySequenceδ_naturality φ p (p + 1) rfl, hz, comp_zero]
  obtain ⟨r, hr⟩ := (F.homologySequence_exact₃ Tn
    hSn.singleTriangle_distinguished p (p + 1) rfl).lift'
      ((F.shift p).map φ.hom₃) hc
  exact ⟨r, hr.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quotientPowDiagram_map
    {A : Type*} [CommRing A] (I : Ideal A) (M : ModuleCat A)
    {n m : ℕ} (hnm : n ≤ m) :
    let D : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
      Functor.ofOpSequence
        (X := fun j ↦ (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (M ⧸ (I ^ j • ⊤ : Submodule A M))))
        (fun j ↦ (DerivedCategory.singleFunctor (ModuleCat A) 0).map
          (ModuleCat.ofHom (Submodule.factorPowSucc I M j)))
    D.map (homOfLE hnm).op =
      (DerivedCategory.singleFunctor (ModuleCat A) 0).map
        (ModuleCat.ofHom (Submodule.factorPow I M hnm)) := by
  intro D
  induction m, hnm using Nat.le_induction with
  | base =>
      simp [D, Submodule.factorPow, Functor.ofOpSequence, Functor.ofSequence,
        Functor.OfSequence.map_id]
  | succ m hnm ih =>
      have hcomp : (homOfLE (show n ≤ m + 1 by omega)).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op :=
        Subsingleton.elim _ _
      rw [hcomp, D.map_comp, ih]
      simp only [D, Functor.ofOpSequence_map_homOfLE_succ]
      rw [← Functor.map_comp]
      congr 1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [Submodule.factorPow, Submodule.factorPowSucc]

private theorem quotientPowExtDiagram_map
    {A : Type u} [CommRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (M : ModuleCat.{v} A) (p : ℤ) {n m : ℕ} (hnm : n ≤ m) :
    let D : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
      Functor.ofOpSequence
        (X := fun j ↦ (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A (M ⧸ (I ^ j • ⊤ : Submodule A M))))
        (fun j ↦ (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.factorPowSucc I M j)))
    let E : ℕᵒᵖ ⥤ ModuleCat.{max u (v + 1)} A :=
      D ⋙ shiftFunctor (DerivedCategory (ModuleCat.{v} A)) p ⋙
        (linearCoyoneda A (DerivedCategory (ModuleCat.{v} A))).obj (op K)
    E.map (homOfLE hnm).op =
      ModuleCat.ofHom (Linear.rightComp A K
        (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.factorPow I M hnm)))⟦p⟧')) := by
  intro D E
  change ModuleCat.ofHom (Linear.rightComp A K
      ((D.map (homOfLE hnm).op)⟦p⟧')) = _
  rw [quotientPowDiagram_map I M hnm]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def quotientPowExtCone
    {A : Type u} [CommRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (M : ModuleCat.{v} A) (p : ℤ) :
    let D : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
      Functor.ofOpSequence
        (X := fun n ↦ (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A (M ⧸ (I ^ n • ⊤ : Submodule A M)))) (fun n ↦
        (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.factorPowSucc I M n)))
    let E : ℕᵒᵖ ⥤ ModuleCat.{max u (v + 1)} A :=
      D ⋙ shiftFunctor (DerivedCategory (ModuleCat.{v} A)) p ⋙
        (linearCoyoneda A (DerivedCategory (ModuleCat.{v} A))).obj (op K)
    let X := ModuleCat.of A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p)
    (Functor.const ℕᵒᵖ).obj X ⟶ E := by
  intro D E X
  refine NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj X) (G := E)
    (fun n => ModuleCat.ofHom (Linear.rightComp A K
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ))⟦p⟧'))) ?_
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x ≫ _ = (x ≫ _) ≫ _
  rw [Category.assoc]
  congr 1
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- **Stacks 0DYJ.** If high-degree Ext from a pseudo-coherent complex into every finite module is
`I`-power torsion, then the inverse system `Ext^p(K, M / I ^ n M)` is essentially constant with
value `Ext^p(K, M)`, which is also its limit. -/
@[stacks 0DYJ]
public theorem ext_quotient_ideal_pow_essentially_constant
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a : ℤ)
    (h : ∀ (N : ModuleCat.{v} A) [Module.Finite A N] (j : ℤ), a ≤ j →
      IsIPowerTorsion A
        (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj N) j) I)
    (p : ℤ) (hp : a ≤ p) (M : ModuleCat.{v} A) [Module.Finite A M] :
    let D : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} A) :=
      Functor.ofOpSequence
        (X := fun n ↦ (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
          (ModuleCat.of A (M ⧸ (I ^ n • ⊤ : Submodule A M)))) (fun n ↦
        (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (Submodule.factorPowSucc I M n)))
    let E : ℕᵒᵖ ⥤ ModuleCat.{max u (v + 1)} A :=
      D ⋙ shiftFunctor (DerivedCategory (ModuleCat.{v} A)) p ⋙
        (linearCoyoneda A (DerivedCategory (ModuleCat.{v} A))).obj (op K)
    let X := ModuleCat.of A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p)
    ∃ π : (Functor.const ℕᵒᵖ).obj X ⟶ E,
      (∀ n : ℕ, π.app (op n) = ModuleCat.ofHom (Linear.rightComp A K
        (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom
            ((I ^ n • ⊤ : Submodule A M).mkQ)))⟦p⟧'))) ∧
      (∃ (n : ℕᵒᵖ) (s : E.obj n ⟶ X),
        EssentiallyConstantPro.IsEssentiallyConstantWith E (Cone.mk X π) n s) ∧
      Nonempty (IsLimit (Cone.mk X π)) := by
  intro D E X
  let π : (Functor.const ℕᵒᵖ).obj X ⟶ E := quotientPowExtCone I K M p
  have : Module.Finite A
      (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) p) :=
    finite_ext_of_pseudoCoherent K hK M p
  obtain ⟨n₀, hz₀⟩ := exists_zero_ext_inclusion I K hK p M (h M p hp)
  have hmono₀ : Mono (π.app (op n₀)) := by
    change Mono (ModuleCat.ofHom (Linear.rightComp A K
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
        (ModuleCat.ofHom (I ^ n₀ • (⊤ : Submodule A M)).mkQ))⟦p⟧')))
    exact mono_ext_quotient_of_zero_inclusion I K M p n₀ hz₀
  have hfac : ∀ j : ℕ, n₀ ≤ j → ∃ k : ℕ, ∃ hjk : j ≤ k,
      ∃ r : E.obj (op k) ⟶ X,
        E.map (homOfLE hjk).op = r ≫ π.app (op j) := by
    intro j h₀j
    have hjmono : Mono (π.app (op j)) := by
      have hcomp : π.app (op j) ≫ E.map (homOfLE h₀j).op = π.app (op n₀) := by
        simpa using (π.naturality (homOfLE h₀j).op).symm
      have : Mono (π.app (op j) ≫ E.map (homOfLE h₀j).op) := by
        rw [hcomp]
        infer_instance
      exact mono_of_mono (π.app (op j)) (E.map (homOfLE h₀j).op)
    obtain ⟨k, hjk, hzk⟩ := exists_zero_ext_pow_transition I K hK M (p + 1)
      (fun N => h N (p + 1) (by omega)) j
    have : Mono (ModuleCat.ofHom (Linear.rightComp A K
        (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (I ^ j • (⊤ : Submodule A M)).mkQ))⟦p⟧'))) := by
      change Mono (π.app (op j))
      exact hjmono
    obtain ⟨r, hr⟩ := ext_quotient_transition_factors I K M p hjk hzk
    refine ⟨k, hjk, r, ?_⟩
    change E.map (homOfLE hjk).op =
      r ≫ ModuleCat.ofHom (Linear.rightComp A K
        (((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
          (ModuleCat.ofHom (I ^ j • (⊤ : Submodule A M)).mkQ))⟦p⟧'))
    rw [quotientPowExtDiagram_map I K M p hjk]
    exact hr
  have hw := essentiallyConstantWith_of_eventually_factors E X π n₀ hfac
  refine ⟨π, ?_, hw, ?_⟩
  · intro n
    rfl
  · obtain ⟨n, s, hs⟩ := hw
    exact ⟨isLimitOfOp (EssentiallyConstantPro.isEssentiallyConstantWith_op hs).isColimit⟩

end Stacks.AdicSystem.ExtEssentiallyConstant

end

end
