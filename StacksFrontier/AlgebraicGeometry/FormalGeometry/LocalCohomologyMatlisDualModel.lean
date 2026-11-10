module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisApproximation
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityMatlis
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityMatlisNatural
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# The Matlis dual model of a local cohomology system

In the situation of Stacks 0EHC with `A` local and `𝔪 = 𝔞`, let `(M_n)` be an inverse system of
finite `A`-modules each annihilated by a power of `I`, and let `ω` be a normalized dualizing
complex with `E` an injective hull of the residue field. This file constructs a
`Stacks.Algebraization.MatlisDualModel` of the local cohomology system `(H^i_𝔪(M_n))`, which is
the hypothesis `hmodel` of
`Stacks.Algebraization.exists_matlisDual_approximation_localCohomologySystem`, except for the
essential constancy of the resulting direct system.

The direct system is `G_n = H^{-i}(RHom_A(M_n, ω))`, in the very spelling in which local duality
in Matlis form, `Dualizing.LocalDuality.localDualityMatlisEquiv`, states its target, and with the
transition maps that `Dualizing.LocalDuality.localDualityMatlisEquiv_comp` states its naturality
against. So both `MatlisDualModel.dualEquiv` and `MatlisDualModel.dualEquiv_comp` are that one
pair of declarations, read off with no further comparison. No identification of
`H^{-i}(RHom_A(M_n, ω))` with `Ext^{-i}_A(M_n, ω)` is used, and none is needed: the structure
asks for *some* direct system of finite modules annihilated by powers of `I`, not for the `Ext`
modules on the nose.

The two remaining fields are properties of the modules `G_n` rather than data, and are proved
where the modules live:

* `finite` is pseudo-coherence of `RHom_A(M_n, ω)`,
  `Dualizing.isPseudoCoherent_derivedHom_of_isDualizingComplex`, read as finiteness of the
  cohomology modules;
* `annihilated` is the `A`-linearity of derived Hom in its source variable,
  `Dualizing.modelHom_map_smul_id_left`, together with the linearity of the single-object functor
  and of `H^j`: a scalar annihilating `M_n` annihilates every functorial invariant of it.

## Main definitions

* `Stacks.Algebraization.dualizingExtFunctor` — the functor `X ↦ H^{-i}(RHom_A(X, ω))` on
  modules, of which the direct system is the restriction along `(M_n)`.
* `Stacks.Algebraization.dualizingExtSystem` — the direct system `n ↦ H^{-i}(RHom_A(M_n, ω))`.
* `Stacks.Algebraization.dualizingExtLimit` — the value `H^{-i}(RHom_A(lim M_n, ω))` of the
  system over `A`, and `Stacks.Algebraization.dualizingExtSystemToLimit` — the `A`-side
  analogue of the maps `α_n` of the source, which
  `Stacks.Algebraization.dualizingExtSystemToLimit_comp` shows form a cocone. Over `A` itself
  the vertex of this cocone need not be a finite `A`-module; see the implementation notes.
* `Stacks.Algebraization.matlisDualModel` — the model.

## Main results

* `Stacks.Algebraization.nonempty_localCohomology_iso_single_injectiveHull_of_isNormalized` —
  the identification `RΓ_𝔪(ω) ≅ E[0]` of Stacks 0A82, stated for an externally given injective
  hull `E`. This is the datum `θ` that local duality in Matlis form takes as input.
* `Stacks.Algebraization.nonempty_matlisDualModel` — a Matlis dual model of the local cohomology
  system exists under the hypotheses of Stacks 0EHK themselves: a dualizing complex is normalized
  by a shift, and the maximal ideal of a Noetherian ring has a finite generating family.
* `Stacks.Algebraization.exists_matlisDual_approximation_of_isEssentiallyConstant` — the
  conclusion of Stacks 0EHK with `hmodel` replaced by the essential constancy modulo finite
  length of `Stacks.Algebraization.dualizingExtSystem` alone.

## Implementation notes

The vertex `dualizingExtLimit M ω i` of the `A`-side cocone is in general not a Noetherian
`A`-module, so the essential constancy of the system cannot be read off from this cocone over
`A`. Take `A = ℚ[x]_{(x)}`, `I = 𝔞 = 𝔪 = (x)` and `M_n = A/x^{n+1}` with the quotient
transitions, `ω = A[1]` and `i = 0`. Then `lim M_n = B = ℚ[[x]]`, the system is
`n ↦ Ext¹_A(A/x^{n+1}, A) ≅ A/x^{n+1}` and the vertex is `Ext¹_A(B, A)`. Here `Hom_A(B, A) = 0`,
since an `A`-linear `φ : B → A` satisfies `φ(1) · B ⊆ A`, which for `φ(1) ≠ 0` would inject the
uncountable `B` into the countable `A`. The long exact sequence of
`0 → B → B → A/x^{n+1} → 0` therefore makes every `α_n` injective, and the images of the `α_n`
form a strictly increasing chain of submodules of `Ext¹_A(B, A)`.

The source avoids this by localising at an `f` from a finite generating family of `𝔪` and
completing `I`-adically, to `B = (A_f)^∧`, where `lim M_{n, f}` is a finite `B`-module; the
essential constancy over `A` is assembled from the statements at the `f`'s.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
* [Stacks Project, Tag 0A82](https://stacks.math.columbia.edu/tag/0A82), the hull and `θ`.
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C), coherence of `RHom`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite StacksDraft.DerivedHom
open Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The direct system of derived duals -/

section ExtSystem

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The direct system `n ↦ H^{-i}(RHom_A(M_n, ω))` attached to an inverse system `(M_n)` of
`A`-modules and an object `ω` of `D(A)`: the degree-`(-i)` cohomology of derived Hom into `ω`,
applied to the terms of `(M_n)` placed in degree zero. Over a normalized dualizing complex `ω`
these are the modules `Ext^{-i}_A(M_n, ω)`, but no such identification is used here; what matters
is that this is the spelling in which `Dualizing.LocalDuality.localDualityMatlisEquiv` states
local duality, so that both the identification and its naturality are available verbatim. -/
public def dualizingExtSystem (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ℕ ⥤ ModuleCat.{u} A :=
  M.rightOp ⋙ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
    Dualizing.derivedHomIntoFunctor ω ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)

omit [IsNoetherianRing A] in
/-- The terms of `Stacks.Algebraization.dualizingExtSystem`. -/
public theorem dualizingExtSystem_obj (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    (dualizingExtSystem M ω i).obj n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        ((derivedHomAdjunction (R := A)).hom.obj
          (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (M.obj (op n))), ω)) :=
  rfl

omit [IsNoetherianRing A] in
/-- The transition maps of `Stacks.Algebraization.dualizingExtSystem` are the maps that
`Dualizing.LocalDuality.localDualityMatlisEquiv_comp` states naturality against. -/
public theorem dualizingExtSystem_map (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {m n : ℕ} (h : m ≤ n) :
    (dualizingExtSystem M ω i).map (homOfLE h) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).map
        ((derivedHomAdjunction (R := A)).hom.map
          ((((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
            (M.map (homOfLE h).op)).op, 𝟙 ω) : _ ⟶ _)) :=
  rfl

/-- `a • 𝟙 X = 0` in `ModuleCat` iff `a` kills every element of `X`. -/
private theorem smul_id_eq_zero_iff {R : Type u} [CommRing R] {X : ModuleCat.{u} R} {a : R} :
    a • 𝟙 X = 0 ↔ ∀ y : X, a • y = 0 := by
  rw [ModuleCat.hom_ext_iff, LinearMap.ext_iff]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.zero_apply]

omit [IsNoetherianRing A] in
/-- A scalar annihilating a module annihilates the identity of that module in `ModuleCat`. -/
private theorem smul_id_eq_zero_of_smul_top_eq_bot {X : ModuleCat.{u} A} {J : Ideal A}
    (hJ : J • (⊤ : Submodule A X) = ⊥) {a : A} (ha : a ∈ J) : a • 𝟙 X = 0 :=
  smul_id_eq_zero_iff.mpr fun y => (Submodule.mem_bot A).mp <| hJ ▸
    Submodule.smul_mem_smul ha (Submodule.mem_top (R := A) (x := y))

omit [IsNoetherianRing A] in
/-- **A scalar annihilating `K` annihilates the cohomology of `RHom_A(K, ω)`.** Derived Hom is
`A`-linear in its source variable, `Dualizing.modelHom_map_smul_id_left`, and `H^j` is `A`-linear;
so the image of `a • 𝟙 K` is `a` on the cohomology module. Comparing the images of `a • 𝟙 K` and
of `0 • 𝟙 K`, which are the same morphism, identifies `a` with `0` there. -/
private theorem smul_id_homology_derivedHom_eq_zero
    (K ω : DerivedCategory (ModuleCat.{u} A)) (j : ℤ) {a : A} (hK : a • 𝟙 K = 0) :
    a • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((derivedHomAdjunction (R := A)).hom.obj (op K, ω))) = 0 := by
  have h1 := Dualizing.modelHom_map_smul_id_left K ω a
  have h2 := Dualizing.modelHom_map_smul_id_left K ω (0 : A)
  rw [hK] at h1
  simp only [zero_smul] at h2
  have hD : a • 𝟙 ((derivedHomAdjunction (R := A)).hom.obj (op K, ω)) = 0 := h1.symm.trans h2
  have hmap := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map_smul a
    (𝟙 ((derivedHomAdjunction (R := A)).hom.obj (op K, ω)))
  rw [hD, Functor.map_zero, CategoryTheory.Functor.map_id] at hmap
  exact hmap.symm

omit [IsNoetherianRing A] in
/-- **The terms of `Stacks.Algebraization.dualizingExtSystem` are annihilated by every ideal that
annihilates the corresponding term of `(M_n)`.** -/
public theorem smul_top_dualizingExtSystem_eq_bot (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) {J : Ideal A}
    (hJ : J • (⊤ : Submodule A (M.obj (op n))) = ⊥) :
    J • (⊤ : Submodule A ((dualizingExtSystem M ω i).obj n)) = ⊥ := by
  refine le_antisymm (Submodule.smul_le.mpr ?_) bot_le
  intro a ha x _
  have hM : a • 𝟙 (M.obj (op n)) = 0 := smul_id_eq_zero_of_smul_top_eq_bot hJ ha
  have hK : a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (M.obj (op n))) = 0 := by
    rw [← CategoryTheory.Functor.map_id (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0),
      ← Functor.map_smul, hM, Functor.map_zero]
  have hG := smul_id_homology_derivedHom_eq_zero
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (M.obj (op n))) ω (-i) hK
  exact (Submodule.mem_bot A).mpr (smul_id_eq_zero_iff.mp hG x)

/-! ### The value of the system, and the maps into it -/

/-- `X ↦ H^{-i}(RHom_A(X, ω))` on modules: the functor of which
`Stacks.Algebraization.dualizingExtSystem` is the restriction along the inverse system,
`dualizingExtSystem M ω i = M.rightOp ⋙ dualizingExtFunctor ω i`
(`Stacks.Algebraization.dualizingExtSystem_eq`). Reading the system this way is what makes its
transition maps and the maps into its value one and the same functorial construction. -/
public def dualizingExtFunctor (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
    Dualizing.derivedHomIntoFunctor ω ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)

omit [IsNoetherianRing A] in
/-- `Stacks.Algebraization.dualizingExtSystem` is `Stacks.Algebraization.dualizingExtFunctor`
restricted along the inverse system. -/
public theorem dualizingExtSystem_eq (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    dualizingExtSystem M ω i = M.rightOp ⋙ dualizingExtFunctor ω i :=
  rfl

/-- **`Ext^{-i}_A(-, ω)` depends on `ω` only up to isomorphism.** Whiskering
`Dualizing.derivedHomIntoFunctorCongr`. -/
public def dualizingExtFunctorCongr {ω ω' : DerivedCategory (ModuleCat.{u} A)} (e : ω ≅ ω')
    (i : ℤ) : dualizingExtFunctor ω i ≅ dualizingExtFunctor ω' i :=
  Functor.isoWhiskerLeft _
    (Functor.isoWhiskerRight (Dualizing.derivedHomIntoFunctorCongr e) _)

/-- **The Ext system against `ω` depends on `ω` only up to isomorphism**, compatibly with the
transition maps. `Stacks.Algebraization.dualizingExtFunctorCongr` restricted along the inverse
system. -/
public def dualizingExtSystemCongr (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    {ω ω' : DerivedCategory (ModuleCat.{u} A)} (e : ω ≅ ω') (i : ℤ) :
    dualizingExtSystem M ω i ≅ dualizingExtSystem M ω' i :=
  Functor.isoWhiskerLeft _ (dualizingExtFunctorCongr e i)

/-- `H^{-i}(RHom_A(lim M_n, ω))`: derived Hom into `ω` out of the limit of the inverse system
`(M_n)`, in degree `-i`, taken over `A` itself and with no localization and no completion.

This is *not* the module the source of Stacks 0EHK calls `Ext^{-i}_B(M, ω_B^∙)`, which is an
`Ext` over the `I`-adic completion `B` of a localization `A_f` of the finite `B`-module
`lim M_{n, f}`. The difference is not bookkeeping: over a discrete valuation ring which is not
complete this module can fail to be a Noetherian `A`-module, while the source's value is a
finite `B`-module. The implementation notes of this file carry the example. -/
public abbrev dualizingExtLimit (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) : ModuleCat.{u} A :=
  (dualizingExtFunctor ω i).obj (op (CategoryTheory.Limits.limit M))

/-- **The `A`-side analogue of the maps `α_n` of the source of Stacks 0EHK.** Derived Hom into
`ω` applied to the limit projection `lim M_k → M_n`, read in degree `-i`: a map from the `n`-th
term of `Stacks.Algebraization.dualizingExtSystem` to
`Stacks.Algebraization.dualizingExtLimit`. The source's `α_n` are the same construction carried
out over the completion `B` of a localization `A_f`, where the target is a finite module; see
the docstring of `Stacks.Algebraization.dualizingExtLimit`. -/
public def dualizingExtSystemToLimit (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (n : ℕ) :
    (dualizingExtSystem M ω i).obj n ⟶ dualizingExtLimit M ω i :=
  (dualizingExtFunctor ω i).map (CategoryTheory.Limits.limit.π M (op n)).op

omit [IsNoetherianRing A] in
/-- **The maps `α_n` are compatible with the transition maps of the system**, so they form a
cocone on `Stacks.Algebraization.dualizingExtSystem` with vertex
`Stacks.Algebraization.dualizingExtLimit`. This is pure functoriality: the composite of the
limit projection `lim M_k → M_n` with the transition `M_n → M_m` is the projection
`lim M_k → M_m`, so the two images under
`Stacks.Algebraization.dualizingExtFunctor` agree. -/
public theorem dualizingExtSystemToLimit_comp (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {m n : ℕ} (h : m ≤ n) :
    (dualizingExtSystemToLimit M ω i n).hom ∘ₗ
        ((dualizingExtSystem M ω i).map (homOfLE h)).hom =
      (dualizingExtSystemToLimit M ω i m).hom := by
  have hw : (M.map (homOfLE h).op).op ≫ (CategoryTheory.Limits.limit.π M (op n)).op =
      (CategoryTheory.Limits.limit.π M (op m)).op := by
    rw [← op_comp, CategoryTheory.Limits.limit.w]
  have key : (dualizingExtSystem M ω i).map (homOfLE h) ≫
      dualizingExtSystemToLimit M ω i n = dualizingExtSystemToLimit M ω i m := by
    change (dualizingExtFunctor ω i).map ((M.map (homOfLE h).op).op) ≫
      (dualizingExtFunctor ω i).map (CategoryTheory.Limits.limit.π M (op n)).op = _
    rw [← Functor.map_comp, hw]
    rfl
  rw [← ModuleCat.hom_comp, key]

/-! ### Finiteness of the values -/

/-- **`H^{-i}(RHom_A(X, ω))` is a finite module for every finite `X`**, by coherence of derived
Hom against a dualizing complex, Stacks 0A7C: `RHom_A(X, ω)` is pseudo-coherent, and over a
Noetherian ring pseudo-coherence gives finiteness of every cohomology module.

Stated at a single module rather than at a term of an inverse system, which is the form the
route of [Stacks, Tag 0EHK] needs at the *vertex* of its cocone; see
`Stacks.Algebraization.finite_dualizingExtLimit`. -/
public theorem finite_dualizingExtFunctor_obj (X : ModuleCat.{u} A)
    (hX : Module.Finite A X) (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) (i : ℤ) :
    Module.Finite A ((dualizingExtFunctor ω i).obj (op X)) := by
  have := hX
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology.{u, u}
    _ 0 A).2.1.mp ?_).2 (-i)
  exact Dualizing.isPseudoCoherent_derivedHom_of_isDualizingComplex ω
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj X) hω 0
    inferInstance (fun j => Dualizing.finite_homology_single X j)

/-- The terms of `Stacks.Algebraization.dualizingExtSystem` are finite modules.
`Stacks.Algebraization.finite_dualizingExtFunctor_obj` at each term of the system. -/
public theorem finite_dualizingExtSystem (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hM : ∀ n : ℕ, Module.Finite A (M.obj (op n)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (n : ℕ) : Module.Finite A ((dualizingExtSystem M ω i).obj n) :=
  finite_dualizingExtFunctor_obj (M.obj (op n)) (hM n) ω hω i

/-- **The vertex of the cocone is a finite module as soon as the limit of the system is.**
`Stacks.Algebraization.dualizingExtLimit` is `H^{-i}(RHom_A(-, ω))` of `lim M_n`, so
`Stacks.Algebraization.finite_dualizingExtFunctor_obj` applies to it verbatim once `lim M_n` is
finite.

Over `A` itself `lim M_n` need not be a finite `A`-module (the counterexample is in the
implementation notes of this file); over the `I`-adic completion `B` of a localization `A_f` it
is, and that is the ring over which the source forms this cocone. -/
public theorem finite_dualizingExtLimit (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hlim : Module.Finite A (CategoryTheory.Limits.limit M : ModuleCat.{u} A))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) (i : ℤ) :
    Module.Finite A (dualizingExtLimit M ω i) :=
  finite_dualizingExtFunctor_obj (CategoryTheory.Limits.limit M) hlim ω hω i

end ExtSystem

/-! ### The identification of the local cohomology of `ω` with the injective hull -/

/-- **Stacks Project, Tag 0A82, for an externally given injective hull.** For a normalized
dualizing complex `ω` over a Noetherian local ring and an injective hull `E` of the residue
field, `RΓ_𝔪(ω) ≅ E[0]`. This is the datum `θ` of
`Dualizing.LocalDuality.localDualityMatlisEquiv`.

Stacks 0A82 produces the isomorphism with `E` replaced by `R^0Γ_𝔪(ω)`, which it also exhibits as
an injective hull of a universe lift of the residue field; the two hulls are isomorphic by
Stacks 08Y4, after `Module.isInjectiveHull_iso_comp` moves the given hull across the universe
lift. -/
public theorem nonempty_localCohomology_iso_single_injectiveHull_of_isNormalized
    (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) (E : ModuleCat.{u} A)
    (ιE : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono ιE]
    (hιE : Module.IsInjectiveHull ιE) :
    Nonempty ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
        (IsNoetherian.noetherian _)).obj ω ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) := by
  obtain ⟨concentrated⟩ :=
    Dualizing.LocalDuality.nonempty_localCohomology_iso_single_homology_zero.{u, u} A ω hω
  obtain ⟨j, hj, hjhull⟩ :=
    Dualizing.LocalDuality.exists_isInjectiveHull_homology_zero_localCohomology.{u, u} A ω hω
  let := hj
  let e : (ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)) ≅
      ModuleCat.of A (IsLocalRing.ResidueField A) :=
    (ULift.moduleEquiv (R := A)
      (M := (ModuleCat.of A (IsLocalRing.ResidueField A) : Type u))).toModuleIso
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull j (e.hom ≫ ιE) hjhull
    (Module.isInjectiveHull_iso_comp e ιE hιE)
  exact ⟨concentrated ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso hullIso⟩

/-! ### The model -/

section Model

variable (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (M : ℕᵒᵖ ⥤ ModuleCat.{u} S.A)

/-- Local duality is invertible at each term of the system: the terms are finite modules, so
their single complexes are bounded below with finite cohomology. -/
public theorem isIso_localDualityMor_single
    (hfin : ∀ n : ℕ, Module.Finite S.A (M.obj (op n))) {r : ℕ} (f : Fin r → S.A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal S.A)
    (ω : DerivedCategory (ModuleCat.{u} S.A)) (hω : Dualizing.IsDualizingComplex ω)
    (E : ModuleCat.{u} S.A)
    (θ : (localCohomologyEndofunctor S.A (IsLocalRing.maximalIdeal S.A)
        (IsNoetherian.noetherian _)).obj ω ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj E) (n : ℕ) :
    IsIso (Dualizing.LocalDuality.localDualityMor (IsLocalRing.maximalIdeal S.A)
      (IsNoetherian.noetherian _) f hf ω E θ
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (M.obj (op n)))) := by
  have := hfin n
  exact Dualizing.LocalDuality.isIso_localDualityMor (IsLocalRing.maximalIdeal S.A)
    (IsNoetherian.noetherian _) f hf ω E θ _ hω 0 inferInstance
    (fun j => Dualizing.finite_homology_single (M.obj (op n)) j)

/-- **The Matlis dual model of the local cohomology system.** Its direct system is
`Stacks.Algebraization.dualizingExtSystem`; the identification of `H^i_𝔪(M_n)` with the Matlis
dual of its `n`-th term, and the compatibility of those identifications with the transition maps,
are `Dualizing.LocalDuality.localDualityMatlisEquiv` and
`Dualizing.LocalDuality.localDualityMatlisEquiv_comp` with no intervening comparison. -/
public def matlisDualModel
    (hfin : ∀ n : ℕ, Module.Finite S.A (M.obj (op n)))
    (hann : ∀ n : ℕ, ∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A (M.obj (op n))) = ⊥)
    {r : ℕ} (f : Fin r → S.A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal S.A)
    (ω : DerivedCategory (ModuleCat.{u} S.A)) (hω : Dualizing.IsDualizingComplex ω)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    [CategoryTheory.Injective (ModuleCat.of S.A E)]
    (θ : (localCohomologyEndofunctor S.A (IsLocalRing.maximalIdeal S.A)
        (IsNoetherian.noetherian _)).obj ω ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A E))
    (i : ℤ) :
    MatlisDualModel S M E i where
  G := dualizingExtSystem M ω i
  finite := finite_dualizingExtSystem M hfin ω hω i
  annihilated n := ⟨(hann n).choose,
    smul_top_dualizingExtSystem_eq_bot M ω i n (hann n).choose_spec⟩
  dualEquiv n :=
    Dualizing.LocalDuality.localDualityMatlisEquiv (IsLocalRing.maximalIdeal S.A)
      (IsNoetherian.noetherian _) f hf ω (ModuleCat.of S.A E) θ i _
      (isIso_localDualityMor_single S M hfin f hf ω hω (ModuleCat.of S.A E) θ n)
  dualEquiv_comp m n h x :=
    Dualizing.LocalDuality.localDualityMatlisEquiv_comp (IsLocalRing.maximalIdeal S.A)
      (IsNoetherian.noetherian _) f hf ω (ModuleCat.of S.A E) θ i
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).map (M.map (homOfLE h).op))
      (isIso_localDualityMor_single S M hfin f hf ω hω (ModuleCat.of S.A E) θ n)
      (isIso_localDualityMor_single S M hfin f hf ω hω (ModuleCat.of S.A E) θ m) x

/-- The direct system of `Stacks.Algebraization.matlisDualModel`. -/
public theorem matlisDualModel_G
    (hfin : ∀ n : ℕ, Module.Finite S.A (M.obj (op n)))
    (hann : ∀ n : ℕ, ∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A (M.obj (op n))) = ⊥)
    {r : ℕ} (f : Fin r → S.A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal S.A)
    (ω : DerivedCategory (ModuleCat.{u} S.A)) (hω : Dualizing.IsDualizingComplex ω)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    [CategoryTheory.Injective (ModuleCat.of S.A E)]
    (θ : (localCohomologyEndofunctor S.A (IsLocalRing.maximalIdeal S.A)
        (IsNoetherian.noetherian _)).obj ω ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (ModuleCat.of S.A E))
    (i : ℤ) :
    (matlisDualModel S M hfin hann f hf ω hω E θ i).G = dualizingExtSystem M ω i :=
  rfl

/-- **A Matlis dual model of the local cohomology system exists**, under the hypotheses of
Stacks 0EHK themselves: the maximal ideal of a Noetherian ring has a finite generating family,
and a dualizing complex over a Noetherian local ring becomes normalized after a shift
(`Dualizing.exists_isNormalizedDualizingComplex_shift`), a shift which is again dualizing
(`Dualizing.isDualizingComplex_shift`). -/
public theorem nonempty_matlisDualModel (hM : IsFiniteModuleModel S M)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    (ιE : IsLocalRing.ResidueField S.A →ₗ[S.A] E) [Mono (ModuleCat.ofHom ιE)]
    (hιE : Module.IsInjectiveHull (ModuleCat.ofHom ιE)) (i : ℤ) :
    Nonempty (MatlisDualModel S M E i) := by
  have : CategoryTheory.Injective (ModuleCat.of S.A E) := hιE.1
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal S.A))
  obtain ⟨K, hK⟩ := hdualizing
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} K hK
  obtain ⟨θ⟩ := nonempty_localCohomology_iso_single_injectiveHull_of_isNormalized S.A (K⟦-m⟧) hm
    (ModuleCat.of S.A E) (ModuleCat.ofHom ιE) hιE
  exact ⟨matlisDualModel S M hM.1 (fun n => ⟨n + 1, hM.2.1 n⟩) f hf (K⟦-m⟧) hm.1 E θ i⟩

/-- **Stacks Project, Tag 0EHK, with the Matlis dual model constructed.** The conclusion of
`Stacks.Algebraization.exists_matlisDual_approximation_localCohomologySystem` with the hypothesis
`hmodel` replaced by the essential constancy modulo finite length of
`Stacks.Algebraization.dualizingExtSystem` alone: the rest of `hmodel` — the direct system, its
finiteness, its annihilation by powers of `I`, and the Matlis identification of the local
cohomology modules with its duals compatibly with the transition maps — is
`Stacks.Algebraization.matlisDualModel`. -/
public theorem exists_matlisDual_approximation_of_isEssentiallyConstant
    (hM : IsFiniteModuleModel S M) (d s : ℤ)
    (E : Type u) [AddCommGroup E] [Module S.A E]
    (ιE : IsLocalRing.ResidueField S.A →ₗ[S.A] E) [Mono (ModuleCat.ofHom ιE)]
    (hιE : Module.IsInjectiveHull (ModuleCat.ofHom ιE))
    (hmaximal : IsLocalRing.maximalIdeal S.A = S.a)
    {r : ℕ} (f : Fin r → S.A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal S.A)
    (ω : DerivedCategory (ModuleCat.{u} S.A))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hineq : SatisfiesDepthInequalities S
      (coherentAdicSystemOfFiniteModuleModel S M hM) s (s + d))
    (hcd : _root_.Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (Ideal.fg_of_isNoetherianRing S.I) ≤ d)
    (hs : 0 ≤ s)
    (hconst : ∀ i : ℤ, i ≤ s →
      IsEssentiallyConstantModFiniteLength S.A S.I (dualizingExtSystem M ω i)) :
    ∀ i : ℤ, i ≤ s →
      ∃ (N : ModuleCat.{u} S.A) (n₀ : ℕ)
        (φ : ∀ n : ℕ,
          (localCohomologySystem S M i).obj (op (n₀ + n)) →ₗ[S.A] (N →ₗ[S.A] E)),
        Module.Finite S.A N ∧
        (∃ k : ℕ, S.I ^ k • (⊤ : Submodule S.A N) = ⊥) ∧
        (∀ (m n : ℕ) (h : m ≤ n),
          φ m ∘ₗ ((localCohomologySystem S M i).map
            (homOfLE (Nat.add_le_add_left h n₀)).op).hom = φ n) ∧
        (∀ n : ℕ, IsFiniteLength S.A ((N →ₗ[S.A] E) ⧸ LinearMap.range (φ n))) ∧
        (∀ m : ℕ, ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
          IsFiniteLength S.A
            (Submodule.map ((localCohomologySystem S M i).map
              (homOfLE (Nat.add_le_add_left hmn n₀)).op).hom (LinearMap.ker (φ n)))) := by
  have : CategoryTheory.Injective (ModuleCat.of S.A E) := hιE.1
  obtain ⟨θ⟩ := nonempty_localCohomology_iso_single_injectiveHull_of_isNormalized S.A ω hω
    (ModuleCat.of S.A E) (ModuleCat.ofHom ιE) hιE
  exact exists_matlisDual_approximation_localCohomologySystem S M hM d s E ιE hιE hmaximal
    ⟨ω, hω.1⟩ hineq hcd hs
    (fun i hi => ⟨matlisDualModel S M hM.1 (fun n => ⟨n + 1, hM.2.1 n⟩) f hf ω hω.1 E θ i,
      hconst i hi⟩)

end Model

end Stacks.Algebraization

end
