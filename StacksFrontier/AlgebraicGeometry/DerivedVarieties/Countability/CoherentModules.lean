module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Logic.Equiv.List
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.BoundedDerivedCategory
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineRestrictSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Countability of the category of coherent modules

Let `X` be a scheme of finite type over a countable Noetherian ring. Then the category
`Coh(𝒪_X)` of coherent `𝒪_X`-modules is essentially countable: it has countably many morphisms
between any two objects and countably many isomorphism classes of objects.

The argument is the one the source leaves to the reader. Choose a finite cover of `X` by affine
opens `U i`, with countable rings of sections `A i = Γ(X, U i)`, and a finite cover of each
overlap `U i ∩ U j` by affine opens. A coherent module `M` is quasi-coherent and its sections over
`U i` form a finite `A i`-module; choose generators, that is, a surjection
`π i : A i ^ n i → Γ(M, U i)`.

* A morphism `M ⟶ N` is determined by the images of these finitely many generators, which lie in
  the countable modules `Γ(N, U i)`.
* The isomorphism class of `M` is determined by the numbers `n i`, the kernels of the `π i`
  (submodules of `A i ^ n i`, countably many because `A i` is Noetherian), and, for every affine
  open `W` of the chosen cover of `U i ∩ U j`, a matrix over `Γ(X, W)` expressing the restrictions
  to `W` of the generators over `U i` in terms of those over `U j`. Two coherent modules sharing
  these data are isomorphic: the generators define isomorphisms over each `U i`, the matrices make
  them agree over each `W`, hence over the overlaps, and they glue.

## Main results

* `AlgebraicGeometry.CoherentCountability.countable_hom`: morphisms between two quasi-coherent
  modules of finite type are countable as soon as the rings of sections of a finite affine cover
  are.
* `AlgebraicGeometry.essentiallyCountable_coherentModules`: on a Noetherian scheme whose rings of
  sections over affine opens are countable, `Coh(𝒪_X)` is essentially countable.
* `AlgebraicGeometry.essentiallyCountable_coherentModules_of_finiteType`: the same for a scheme of
  finite type over a countable Noetherian ring.

## References

* [Stacks Project, Tag 0G0W](https://stacks.math.columbia.edu/tag/0G0W)
* [Stacks Project, Tag 0G0T](https://stacks.math.columbia.edu/tag/0G0T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry.CoherentCountability

/-! ### Linear algebra -/

/-- A finite module over a countable ring is countable. -/
theorem countable_of_moduleFinite (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    [Countable A] [Module.Finite A M] : Countable M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact hf.countable

/-- Over a countable Noetherian ring `A`, the free module `A ^ n` has countably many
submodules, each being spanned by a finite set. -/
theorem countable_submodule (A : Type*) [CommRing A] [Countable A] [IsNoetherianRing A]
    (n : ℕ) : Countable (Submodule A (Fin n → A)) := by
  refine (show Function.Surjective
      (fun s : Finset (Fin n → A) => Submodule.span A (s : Set (Fin n → A))) from ?_).countable
  intro K
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian K
  exact ⟨s, hs⟩

/-- The images of the standard basis vectors under a surjection `A ^ n → M` span `M`. -/
theorem span_range_single_eq_top {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n : ℕ} (π : (Fin n → A) →ₗ[A] M) (hπ : Function.Surjective π) :
    Submodule.span A (Set.range fun t : Fin n => π (Pi.single t 1)) = ⊤ := by
  have h1 :
      Submodule.span A (Set.range fun t : Fin n => (Pi.single t (1 : A) : Fin n → A)) = ⊤ := by
    have e : (fun t : Fin n => (Pi.single t (1 : A) : Fin n → A)) = ⇑(Pi.basisFun A (Fin n)) :=
      funext fun t => (Pi.basisFun_apply A (Fin n) t).symm
    rw [e]
    exact (Pi.basisFun A (Fin n)).span_eq
  rw [show (fun t : Fin n => π (Pi.single t 1)) = π ∘ fun t => Pi.single t 1 from rfl,
    Set.range_comp, ← Submodule.map_span, h1, Submodule.map_top, LinearMap.range_eq_top.mpr hπ]

/-- Two linear maps out of `M` agree as soon as they agree on the images of the standard basis
vectors under a surjection `A ^ n → M`. -/
theorem linearMap_ext_of_surjective {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {n : ℕ} (π : (Fin n → A) →ₗ[A] M)
    (hπ : Function.Surjective π) {f g : M →ₗ[A] N}
    (h : ∀ t, f (π (Pi.single t 1)) = g (π (Pi.single t 1))) : f = g :=
  LinearMap.ext_on_range (span_range_single_eq_top π hπ) h

/-! ### Morphisms of quasi-coherent modules and their sections over affine opens -/

variable {X : Scheme.{u}}

/-- Two morphisms of quasi-coherent modules agreeing on the sections over an affine open `O`
agree on the sections over every open contained in `O`. -/
theorem app_eq_of_isAffineOpen {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    {O : X.Opens} (hO : IsAffineOpen O) {φ ψ : M ⟶ N}
    (h : ∀ m : Γ(M, O), φ.app O m = ψ.app O m) {U : X.Opens} (hU : U ≤ O) :
    φ.app U = ψ.app U := by
  ext m
  exact sectionFamily_ext_of_isAffineOpen hO (fun U _ => φ.app U) (fun U _ => ψ.app U)
    (fun _ _ _ _ => map_add _ _ _) (fun _ _ r m => Scheme.Modules.Hom.app_smul φ r m)
    (fun _ _ hUV _ m => (Hom_app_presheaf_map φ hUV m).symm)
    (fun _ _ _ _ => map_add _ _ _) (fun _ _ r m => Scheme.Modules.Hom.app_smul ψ r m)
    (fun _ _ hUV _ m => (Hom_app_presheaf_map ψ hUV m).symm) h U hU m

/-- Over affine opens `W ≤ O`, the restrictions to `W` of generators of the sections of a
quasi-coherent module over `O` generate its sections over `W`. -/
theorem span_restrict_eq_top (M : X.Modules) [M.IsQuasicoherent] {O W : X.Opens}
    (hO : IsAffineOpen O) (hW : IsAffineOpen W) (hWO : W ≤ O) {n : ℕ}
    (π : (Fin n → Γ(X, O)) →ₗ[Γ(X, O)] Γ(M, O)) (hπ : Function.Surjective π) :
    Submodule.span Γ(X, W)
      (Set.range fun t : Fin n => M.presheaf.map (homOfLE hWO).op (π (Pi.single t 1))) = ⊤ := by
  set S := Submodule.span Γ(X, W)
    (Set.range fun t : Fin n => M.presheaf.map (homOfLE hWO).op (π (Pi.single t 1)))
  have hres : ∀ m : Γ(M, O), M.presheaf.map (homOfLE hWO).op m ∈ S := by
    intro m
    have hm : m ∈ Submodule.span Γ(X, O) (Set.range fun t : Fin n => π (Pi.single t 1)) := by
      rw [span_range_single_eq_top π hπ]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨t, rfl⟩
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [Scheme.Modules.map_smul]; exact S.smul_mem _ hx
  let := algebraOfLE X hWO
  let := moduleOfLE M hWO
  let := isScalarTowerOfLE M hWO
  have hbc := isBaseChange_restrictₗ M hW hO hWO
  suffices h : ∀ x, x ∈ S from eq_top_iff.mpr fun x _ => h x
  intro x
  induction x using hbc.inductionOn with
  | tmul m => exact hres m
  | smul s y hy => exact S.smul_mem s hy
  | add y z hy hz => exact S.add_mem hy hz

section Cover

variable {I : Type u} (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hcov : ∀ x : X, ∃ i, x ∈ U i)

include hU hcov in
/-- A morphism of quasi-coherent modules is determined by the images of generators of the
sections over the members of an affine open cover. -/
theorem hom_ext_of_generators {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    {n : I → ℕ} (π : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i))
    (hπ : ∀ i, Function.Surjective (π i)) {φ ψ : M ⟶ N}
    (h : ∀ i t, φ.app (U i) (π i (Pi.single t 1)) = ψ.app (U i) (π i (Pi.single t 1))) :
    φ = ψ := by
  refine hom_ext_of_app_eq_of_cover U hcov fun i V hV => app_eq_of_isAffineOpen (hU i) ?_ hV
  intro m
  have := linearMap_ext_of_surjective (π i) (hπ i)
    (f := Stacks.AlgebraicGeometry.QcohLimits.appₗ φ (U i))
    (g := Stacks.AlgebraicGeometry.QcohLimits.appₗ ψ (U i)) (h i)
  exact LinearMap.congr_fun this m

include hU hcov in
/-- Morphisms between two quasi-coherent modules of finite type are countable when the rings of
sections of a finite affine open cover are countable. -/
theorem countable_hom [Finite I] (hA : ∀ i, Countable Γ(X, U i)) (M N : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType] :
    Countable (M ⟶ N) := by
  have hfin (P : X.Modules) [P.IsQuasicoherent] [P.IsFiniteType] (i : I) :
      Module.Finite Γ(X, U i) Γ(P, U i) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections P (hU i)
  choose n π hπ using fun i => @Module.Finite.exists_fin' _ _ _ _ _ (hfin M i)
  have : ∀ i, Countable Γ(N, U i) := fun i =>
    @countable_of_moduleFinite _ _ _ _ _ (hA i) (hfin N i)
  refine (show Function.Injective
      (fun φ : M ⟶ N => fun i (t : Fin (n i)) => φ.app (U i) (π i (Pi.single t 1))) from
    fun φ ψ hφψ => hom_ext_of_generators U hU hcov π hπ fun i t =>
      congrFun (congrFun hφψ i) t).countable

variable (V : I → I → Finset X.affineOpens)
  (hVle : ∀ i j, ∀ W ∈ V i j, (W : X.Opens) ≤ U i ⊓ U j)
  (hVcov : ∀ i j, ∀ x ∈ U i ⊓ U j, ∃ W ∈ V i j, x ∈ (W : X.Opens))

/-- The relations satisfied by generators `π` of the sections of `M` over the opens `U i`: over
each affine open `W` of the chosen cover of `U i ∩ U j`, the restriction to `W` of the `s`-th
generator over `U i` is the combination, with coefficients `c i j W s t`, of the restrictions of
the generators over `U j`. -/
def Relations (M : X.Modules) (n : I → ℕ)
    (π : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i))
    (c : ∀ i j, ∀ W : V i j, Fin (n i) → Fin (n j) → Γ(X, W.1.1)) : Prop :=
  ∀ i j (W : V i j) (s : Fin (n i)),
    M.presheaf.map (homOfLE ((hVle i j W.1 W.2).trans inf_le_left)).op (π i (Pi.single s 1)) =
      ∑ t, c i j W s t •
        M.presheaf.map (homOfLE ((hVle i j W.1 W.2).trans inf_le_right)).op
          (π j (Pi.single t 1))

include hU in
/-- Generators over the `U i` of a quasi-coherent module always satisfy some relations. -/
theorem exists_relations (M : X.Modules) [M.IsQuasicoherent] (n : I → ℕ)
    (π : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i))
    (hπ : ∀ i, Function.Surjective (π i)) :
    ∃ c, Relations U V hVle M n π c := by
  have key : ∀ i j (W : V i j) (s : Fin (n i)), ∃ d : Fin (n j) → Γ(X, W.1.1),
      ∑ t, d t • M.presheaf.map (homOfLE ((hVle i j W.1 W.2).trans inf_le_right)).op
          (π j (Pi.single t 1)) =
        M.presheaf.map (homOfLE ((hVle i j W.1 W.2).trans inf_le_left)).op
          (π i (Pi.single s 1)) := by
    intro i j W s
    rw [← Submodule.mem_span_range_iff_exists_fun,
      span_restrict_eq_top M (hU j) W.1.2 _ (π j) (hπ j)]
    trivial
  choose c hc using key
  exact ⟨c, fun i j W s => (hc i j W s).symm⟩

include hU in
/-- A quasi-coherent module of finite type has finitely many generators over each `U i`, and
these satisfy some relations. -/
theorem exists_generators_relations (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (n : I → ℕ) (π : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i)),
      (∀ i, Function.Surjective (π i)) ∧
      (∃ K : ∀ i, Submodule Γ(X, U i) (Fin (n i) → Γ(X, U i)), ∀ i v, π i v = 0 ↔ v ∈ K i) ∧
      ∃ c, Relations U V hVle M n π c := by
  have hfin (i : I) : Module.Finite Γ(X, U i) Γ(M, U i) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections M (hU i)
  choose n π hπ using fun i => @Module.Finite.exists_fin' _ _ _ _ _ (hfin i)
  exact ⟨n, π, hπ, ⟨fun i => LinearMap.ker (π i), fun _ _ => LinearMap.mem_ker.symm⟩,
    exists_relations U hU V hVle M n π hπ⟩

include hU hcov hVcov in
/-- **Gluing.** Let `M` and `N` be quasi-coherent modules with generators `πM` and `πN` over the
`U i` satisfying the same relations `c`. Then linear maps `α i : Γ(M, U i) → Γ(N, U i)` sending
the generators of `M` to those of `N` are the sections over the `U i` of a morphism `M ⟶ N`. -/
theorem exists_hom_of_relations {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    {n : I → ℕ} (πM : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i))
    (πN : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(N, U i))
    (hπM : ∀ i, Function.Surjective (πM i))
    {c : ∀ i j, ∀ W : V i j, Fin (n i) → Fin (n j) → Γ(X, W.1.1)}
    (hM : Relations U V hVle M n πM c) (hN : Relations U V hVle N n πN c)
    (α : ∀ i, Γ(M, U i) →ₗ[Γ(X, U i)] Γ(N, U i))
    (hα : ∀ i s, α i (πM i (Pi.single s 1)) = πN i (Pi.single s 1)) :
    ∃ φ : M ⟶ N, ∀ i s, φ.app (U i) (πM i (Pi.single s 1)) = πN i (Pi.single s 1) := by
  choose t hadd hsmul hres htop using fun i => exists_sectionFamily_of_isAffineOpen (hU i) (α i)
  -- the two families agree on the opens contained in a member `W` of the cover of an overlap
  have hW : ∀ a b (W : V a b) (U' : X.Opens) (hU' : U' ≤ W.1.1) (m : Γ(M, U')),
      t a U' (hU'.trans ((hVle a b W.1 W.2).trans inf_le_left)) m =
        t b U' (hU'.trans ((hVle a b W.1 W.2).trans inf_le_right)) m := by
    intro a b W
    have hWa := (hVle a b W.1 W.2).trans inf_le_left
    have hWb := (hVle a b W.1 W.2).trans inf_le_right
    let fa : Γ(M, W.1.1) →ₗ[Γ(X, W.1.1)] Γ(N, W.1.1) :=
      { toFun := t a W.1.1 hWa
        map_add' := hadd a W.1.1 hWa
        map_smul' := hsmul a W.1.1 hWa }
    let fb : Γ(M, W.1.1) →ₗ[Γ(X, W.1.1)] Γ(N, W.1.1) :=
      { toFun := t b W.1.1 hWb
        map_add' := hadd b W.1.1 hWb
        map_smul' := hsmul b W.1.1 hWb }
    have hab : fa = fb := by
      refine LinearMap.ext_on_range (span_restrict_eq_top M (hU a) W.1.2 hWa (πM a) (hπM a))
        fun s => ?_
      show t a W.1.1 hWa _ = t b W.1.1 hWb _
      have e1 := hres a W.1.1 (U a) hWa le_rfl (πM a (Pi.single s 1))
      rw [htop] at e1
      rw [e1, hα, hN a b W s, hM a b W s]
      show _ = fb _
      rw [map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_smul]
      congr 1
      show _ = t b W.1.1 hWb _
      have e2 := hres b W.1.1 (U b) hWb le_rfl (πM b (Pi.single r 1))
      rw [htop] at e2
      rw [e2, hα]
    intro U' hU' m
    refine sectionFamily_ext_of_isAffineOpen W.1.2
      (fun U'' h => t a U'' (h.trans hWa)) (fun U'' h => t b U'' (h.trans hWb))
      (fun U'' h => hadd a U'' (h.trans hWa)) (fun U'' h => hsmul a U'' (h.trans hWa))
      (fun U₁ U₂ h₁ h₂ => hres a U₁ U₂ h₁ (h₂.trans hWa))
      (fun U'' h => hadd b U'' (h.trans hWb)) (fun U'' h => hsmul b U'' (h.trans hWb))
      (fun U₁ U₂ h₁ h₂ => hres b U₁ U₂ h₁ (h₂.trans hWb))
      (fun m => LinearMap.congr_fun hab m) U' hU' m
  obtain ⟨φ, hφ⟩ := exists_hom_app_eq_of_cover U hcov t hadd hsmul hres (by
    intro a b U' ha hb m
    refine N.isSheaf.section_ext (U := op U') ?_
    intro x hx
    obtain ⟨W, hWV, hxW⟩ := hVcov a b x ⟨ha hx, hb hx⟩
    refine ⟨U' ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
    rw [← hres a _ _ inf_le_left ha, ← hres b _ _ inf_le_left hb]
    exact hW a b ⟨W, hWV⟩ (U' ⊓ W) inf_le_right _)
  exact ⟨φ, fun i s => by rw [hφ i (U i) le_rfl, htop, hα]⟩

include hU hcov hVcov in
/-- **Two quasi-coherent modules with the same generators-and-relations data are isomorphic.**
If `M` and `N` have generators over the `U i` indexed by the same sets, with the same kernels and
satisfying the same relations over the cover of the overlaps, then `M ≅ N`. -/
theorem nonempty_iso_of_relations {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    {n : I → ℕ} (πM : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i))
    (πN : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(N, U i))
    (hπM : ∀ i, Function.Surjective (πM i)) (hπN : ∀ i, Function.Surjective (πN i))
    (hker : ∀ i v, πM i v = 0 ↔ πN i v = 0)
    {c : ∀ i j, ∀ W : V i j, Fin (n i) → Fin (n j) → Γ(X, W.1.1)}
    (hM : Relations U V hVle M n πM c) (hN : Relations U V hVle N n πN c) :
    Nonempty (M ≅ N) := by
  -- a linear map out of `Γ(P, U i)` sending the generators of `P` to those of `Q`
  have hlin : ∀ (P Q : X.Modules) (πP : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(P, U i))
      (πQ : ∀ i, (Fin (n i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(Q, U i)),
      (∀ i, Function.Surjective (πP i)) → (∀ i, LinearMap.ker (πP i) ≤ LinearMap.ker (πQ i)) →
      ∃ α : ∀ i, Γ(P, U i) →ₗ[Γ(X, U i)] Γ(Q, U i), ∀ i v, α i (πP i v) = πQ i v := by
    intro P Q πP πQ hP hPQ
    refine ⟨fun i => ((LinearMap.ker (πP i)).liftQ (πQ i) (hPQ i)).comp
      ((πP i).quotKerEquivOfSurjective (hP i)).symm.toLinearMap, fun i v => ?_⟩
    have : ((πP i).quotKerEquivOfSurjective (hP i)).symm (πP i v) =
        Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [this]
  obtain ⟨α, hα⟩ := hlin M N πM πN hπM fun i v hv => (hker i v).mp hv
  obtain ⟨β, hβ⟩ := hlin N M πN πM hπN fun i v hv => (hker i v).mpr hv
  obtain ⟨φ, hφ⟩ := exists_hom_of_relations U hU hcov V hVle hVcov πM πN hπM hM hN α
    fun i s => hα i _
  obtain ⟨ψ, hψ⟩ := exists_hom_of_relations U hU hcov V hVle hVcov πN πM hπN hN hM β
    fun i s => hβ i _
  refine ⟨{ hom := φ, inv := ψ, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · refine hom_ext_of_generators U hU hcov πM hπM fun i s => ?_
    simp [hφ, hψ]
  · refine hom_ext_of_generators U hU hcov πN hπN fun i s => ?_
    simp [hφ, hψ]

end Cover

end AlgebraicGeometry.CoherentCountability

namespace AlgebraicGeometry

open CoherentCountability

/-- **The category `Coh(𝒪_X)` is essentially countable** on a Noetherian scheme whose rings of
sections over affine opens are countable: it has countably many morphisms between any two
objects and countably many isomorphism classes of objects. -/
theorem essentiallyCountable_coherentModules (X : Scheme.{u}) [IsNoetherian X]
    (hΓ : ∀ U : X.Opens, IsAffineOpen U → Countable Γ(X, U)) :
    EssentiallyCountableCategory (SheafOfModules.CoherentModules X.ringCatSheaf) := by
  classical
  -- every open is covered by finitely many affine opens contained in it
  have hfc : ∀ O : X.Opens, ∃ t : Finset X.affineOpens, (∀ W ∈ t, (W : X.Opens) ≤ O) ∧
      ∀ x ∈ O, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    intro O
    obtain ⟨t, ht, htU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := O)).mp (TopologicalSpace.NoetherianSpace.isCompact _)
    refine ⟨ht.toFinset, fun W hW => ?_, fun x hx => ?_⟩
    · rw [htU]
      exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ t) => (W : X.Opens)) W
        (ht.mem_toFinset.mp hW)
    · rw [htU] at hx
      simp only [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      exact ⟨W, ht.mem_toFinset.mpr hW, hxW⟩
  -- a finite affine open cover `U` of `X`
  obtain ⟨s, -, hsU⟩ := hfc ⊤
  let U : s → X.Opens := fun i => i.1.1
  have hU : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have hcov : ∀ x : X, ∃ i, x ∈ U i := fun x => by
    obtain ⟨W, hW, hx⟩ := hsU x trivial
    exact ⟨⟨W, hW⟩, hx⟩
  -- finite affine open covers `V i j` of the overlaps
  have hov := fun i j : s => hfc (U i ⊓ U j)
  choose V hVle hVcov using hov
  have hA : ∀ i, Countable Γ(X, U i) := fun i => hΓ _ (hU i)
  have hcoh (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
      (M.obj : X.Modules).IsQuasicoherent ∧ (M.obj : X.Modules).IsFiniteType :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X M.obj
      M.property
  refine ⟨fun M N => ?_, ?_⟩
  · obtain ⟨_, _⟩ := hcoh M
    obtain ⟨_, _⟩ := hcoh N
    exact @Function.Injective.countable _ ((M.obj : X.Modules) ⟶ N.obj)
      (countable_hom U hU hcov hA _ _) (fun f : M ⟶ N => f.hom)
      fun f g h => ObjectProperty.hom_ext _ h
  · -- the countable type of generators-and-relations data
    let Code := Σ n : s → ℕ, (∀ i, Submodule Γ(X, U i) (Fin (n i) → Γ(X, U i))) ×
      (∀ i j (W : V i j), Fin (n i) → Fin (n j) → Γ(X, W.1.1))
    have : Countable Code := by
      have (i : s) : IsNoetherianRing Γ(X, U i) :=
        IsLocallyNoetherian.component_noetherian ⟨U i, hU i⟩
      have (n : s → ℕ) (i : s) : Countable (Submodule Γ(X, U i) (Fin (n i) → Γ(X, U i))) :=
        countable_submodule _ _
      have (i j : s) (W : V i j) : Countable Γ(X, W.1.1) := hΓ _ W.1.2
      infer_instance
    -- `M` is described by the code `τ` if it has generators with these kernels and relations
    let Describes (M : X.Modules) (τ : Code) : Prop :=
      ∃ (π : ∀ i, (Fin (τ.1 i) → Γ(X, U i)) →ₗ[Γ(X, U i)] Γ(M, U i)),
        (∀ i, Function.Surjective (π i)) ∧ (∀ i v, π i v = 0 ↔ v ∈ τ.2.1 i) ∧
          Relations U V hVle M τ.1 π τ.2.2
    have hex (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
        ∃ τ, Describes M.obj τ := by
      obtain ⟨_, _⟩ := hcoh M
      obtain ⟨n, π, hπ, ⟨K, hK⟩, c, hc⟩ :=
        exists_generators_relations U hU V hVle (M.obj : X.Modules)
      exact ⟨⟨n, K, c⟩, π, hπ, hK, hc⟩
    choose τ hτ using hex
    let C := SheafOfModules.CoherentModules X.ringCatSheaf
    refine (show Function.Injective (fun S : Skeleton C => τ ((fromSkeleton C).obj S)) from
      fun S S' h => ?_).countable
    obtain ⟨_, _⟩ := hcoh ((fromSkeleton C).obj S)
    obtain ⟨_, _⟩ := hcoh ((fromSkeleton C).obj S')
    have hS' := hτ ((fromSkeleton C).obj S')
    simp only at h
    rw [← h] at hS'
    obtain ⟨πM, hπM, hkM, hM⟩ := hτ ((fromSkeleton C).obj S)
    obtain ⟨πN, hπN, hkN, hN⟩ := hS'
    obtain ⟨e⟩ := nonempty_iso_of_relations U hU hcov V hVle hVcov πM πN hπM hπN
      (fun i v => (hkM i v).trans (hkN i v).symm) hM hN
    have := congr_toSkeleton_of_iso (ObjectProperty.isoMk _ e :
      (fromSkeleton C).obj S ≅ (fromSkeleton C).obj S')
    rwa [toSkeleton_fromSkeleton_obj, toSkeleton_fromSkeleton_obj] at this

/-- On a scheme of finite type over a countable ring, the ring of sections over every affine open
is countable. -/
theorem countable_sections_of_finiteType {R : Type u} [CommRing R] [Countable R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    {U : X.Opens} (hU : IsAffineOpen U) : Countable Γ(X, U) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hR : Cardinal.mk Γ(Spec (.of R), ⊤) ≤ Cardinal.aleph0 := by
    rw [Cardinal.mk_congr (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toEquiv]
    exact Cardinal.mk_le_aleph0
  have hsize : X.size ≤ Cardinal.aleph0 :=
    (Scheme.size_le_of_locallyOfFiniteType f).trans <| by
      rw [Scheme.size_of_isAffine]
      exact max_le le_rfl hR
  exact Cardinal.mk_le_aleph0_iff.mp ((Scheme.mk_sections_le_size X ⟨U, hU⟩).trans hsize)

/-- **The category `Coh(𝒪_X)` is essentially countable** for a scheme `X` of finite type over a
countable Noetherian ring: it has countably many morphisms between any two coherent
`𝒪_X`-modules and countably many isomorphism classes of coherent `𝒪_X`-modules. -/
theorem essentiallyCountable_coherentModules_of_finiteType {R : Type u} [CommRing R]
    [Countable R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    EssentiallyCountableCategory (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  essentiallyCountable_coherentModules X fun _ hU => countable_sections_of_finiteType f hU

end AlgebraicGeometry
