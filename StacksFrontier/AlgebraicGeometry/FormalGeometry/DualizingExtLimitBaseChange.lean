module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorBaseChange

/-!
# Flat base change carries the maps `α_n` to the maps `α_n` of the base-changed data

Let `A → S` be a flat map of Noetherian rings, let `M` be an inverse system of finite
`A`-modules and let `ω` be a bounded below object of `D(A)`. This file states and proves the
compatibility of `Stacks.Algebraization.dualizingExtFunctorBaseChange` with the cocone
`Stacks.Algebraization.dualizingExtSystemToLimit`: the base change of `α_n` is the `α_n` of the
base-changed system, up to the comparison `CategoryTheory.Limits.limit.post` of the base change
with the limit of the system.

## Main results

* `Stacks.Algebraization.extendScalars_map_dualizingExtFunctor_map_comp_baseChange` — base
  change carries `H^{-i}(RHom_A(φ, ω))` to `H^{-i}(RHom_S(S ⊗_A φ, ω ⊗ᴸ_A S))`, for an
  arbitrary `φ`. Everything below is this at one morphism.
* `Stacks.Algebraization.extendScalars_map_dualizingExtFunctor_map_cone_comp_baseChange` — the
  compatibility with the Ext-cocone of an *arbitrary* cone on the system, which is the form the
  route of [Stacks, Tag 0EHK] needs; the comparison factor is
  `Stacks.Algebraization.dualizingExtSystemToLimit_comp_map_coneLift`.
* `Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange` — the
  compatibility with the cocone, at the limit cone. This is the special case in which the
  comparison factor is *never* invertible.
* `Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso_hom_app_comp_dualizingExtSystemToLimit`
  — the same read through `Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso`, whose
  components are the comparison itself
  (`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso_hom_app`).
* `Stacks.Algebraization.apply_eq_zero_dualizingExtSystemToLimit_of_baseChange` — the inclusion
  of kernels that the descent of `Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` consumes,
  and the one hypothesis it costs: injectivity of the comparison factor.
* `Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_localizationBaseChange`
  and
  `Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_adicCompletionBaseChange`
  — the two base changes the route of [Stacks, Tag 0EHK] makes, `A → A_f → (A_f)^∧`.
* `Stacks.Algebraization.comp_eq_map_comp_twoStep` — the formal shape of a two-step chase, with
  abstract objects, and
  `Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange_twoStep` —
  the cocone compatibility for a *chain* `A → S → S'`. The latter is not the former's two
  one-step instances composed: the first step's `CategoryTheory.Limits.limit.post` factor has to
  be carried across the second base change, which is that base change's own naturality at it.

## Implementation notes

**The twist by `CategoryTheory.Limits.limit.post` cannot be removed, and the untwisted statement
is false.** The vertex of the cocone over `S` is `H^{-i}(RHom_S(lim (S ⊗_A M_n), ω ⊗ᴸ_A S))`,
while what base change produces is `H^{-i}(RHom_S(S ⊗_A lim M_n, ω ⊗ᴸ_A S))`, and the two are
compared by `CategoryTheory.Limits.limit.post M (ModuleCat.extendScalars _)`, which is not
invertible for the adic quotient tower: take `A = ℤ`, `I = (p)`, `M_n = ℤ/pⁿ⁺¹` and
`S = A^∧ = ℤ_p`. Then `S ⊗_A M_n = M_n`, so `lim (S ⊗_A M_n) = ℤ_p`, while
`S ⊗_A lim M_n = ℤ_p ⊗_ℤ ℤ_p`, and the comparison is multiplication `ℤ_p ⊗_ℤ ℤ_p → ℤ_p`. Take
`a ∈ ℤ_p` transcendental over `ℚ`, which exists because `ℚ_p` has infinite transcendence degree
over `ℚ`. Then `1 ⊗ a - a ⊗ 1` is killed by multiplication, and it is not zero: its image in
`ℚ_p ⊗_ℚ ℚ_p` is a difference of two distinct members of the basis obtained from a `ℚ`-basis of
`ℚ_p` containing `1` and `a`. So base change does *not* commute with the limit of the adic
quotient tower, and no hypothesis of the situation of [Stacks, Tag 0EHK] makes it.

What the route does have is the general `φ` statement. The cocone the route of
[Stacks, Tag 0EHK] actually base changes is not indexed by the limit cone of the system over the
*localized* ring: over `A_f` the relevant vertex is the localization `M_f` of the finite module
`M` over the complete bootstrap ring, and the legs are the localizations of the limit
projections `M → M_n`, not the limit projections of the localized system — whose limit is the
`I`-adic completion of `M_f` and not `M_f`. Because the legs are then arbitrary morphisms out of
one object, the statement they need is
`Stacks.Algebraization.extendScalars_map_dualizingExtFunctor_map_comp_baseChange` and not the
limit-cone form, and there the only thing left to check is that `S ⊗_{A_f} M_f` is the limit of
the base-changed system -- which holds because `M_f` is a *finite* `A_f`-module, so that
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` applies to it, whereas it does not apply
to `lim M_n`.

Nothing here needs `Stacks.Algebraization.dualizingExtSystemToLimit_comp`, the cocone law: these
are equations between single morphisms, and the cocone law is what makes the family a cocone.
Both follow from functoriality alone, and neither uses the other.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912),
  `Stacks.flat_limit_and_tensor_limit_of_flat_quotients`, the one statement in the tree that
  inverts a comparison of this kind -- for tensoring with a *finite* module, which neither a
  localization nor a completion is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

section General

variable {A S : Type u} [CommRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S]
  (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]

omit [IsNoetherianRing A] in
/-- **Flat base change carries `H^{-i}(RHom_A(-, ω))` of a morphism to
`H^{-i}(RHom_S(-, ω ⊗ᴸ_A S))` of its base change.** This is the naturality of
`Stacks.Algebraization.dualizingExtFunctorBaseChange` at `φ.op`, named because every
compatibility below is this at one morphism.

The morphism is arbitrary: no limit, no cone and no finiteness. In particular the legs of the
cocone that the route of [Stacks, Tag 0EHK] base changes are covered -- see the implementation
notes of this file for why they are not the limit projections of the base-changed system. -/
theorem extendScalars_map_dualizingExtFunctor_map_comp_baseChange
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    {N P : ModuleCat.{u} A} (φ : N ⟶ P) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
          ((dualizingExtFunctor ω i).map φ.op) ≫
        (dualizingExtFunctorBaseChange F comparison hf ω i).app (op N) =
      (dualizingExtFunctorBaseChange F comparison hf ω i).app (op P) ≫
        (dualizingExtFunctor (F.obj ω) i).map
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map φ).op :=
  (dualizingExtFunctorBaseChange F comparison hf ω i).naturality φ.op

omit [IsNoetherianRing A] in
/-- **The `α_n` of the base-changed system, followed by the comparison of the base change of a
cone with the limit, is the `H^{-i}(RHom_S(-, -))` of the base-changed leg of the cone.** Pure
functoriality, from `CategoryTheory.Limits.limit.lift_π`.

This is the packaging that lets a consumer recognise a base-changed cocone *as*
`Stacks.Algebraization.dualizingExtSystemToLimit` over `S`, and the cone is arbitrary -- which
is what the route of [Stacks, Tag 0EHK] needs, its cone over `A_f` having vertex the
localization of the finite module over the complete bootstrap ring and not the limit of the
localized system. When `(ModuleCat.extendScalars _).mapCone c` is a limit cone the comparison is
invertible, and then the base-changed cocone is that `α` on the nose; over a localization that
holds because the vertex is a *finite* module, whereas it fails at the limit cone, where the
vertex is not. -/
theorem dualizingExtSystemToLimit_comp_map_coneLift
    (ω' : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (c : Cone M) (n : ℕ) :
    dualizingExtSystemToLimit (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) ω' i n ≫
        (dualizingExtFunctor ω' i).map
          (limit.lift (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S))
            ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapCone c)).op =
      (dualizingExtFunctor ω' i).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map (c.π.app (op n))).op := by
  show (dualizingExtFunctor ω' i).map
      (limit.π (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (op n)).op ≫ _ = _
  have h : limit.lift (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S))
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapCone c) ≫
      limit.π (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (op n) =
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map (c.π.app (op n)) :=
    limit.lift_π _ _
  rw [← h, op_comp, Functor.map_comp]

omit [IsNoetherianRing A] in
/-- **Flat base change carries the Ext-cocone of a cone to the Ext-cocone of its base change.**
`Stacks.Algebraization.extendScalars_map_dualizingExtFunctor_map_comp_baseChange` at the `n`-th
leg of the cone, with
`Stacks.Algebraization.dualizingExtSystemToLimit_comp_map_coneLift` reading its right-hand side
as the `α_n` of the base-changed system.

The limit cone is the special case
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange`; it is the
*worst* case, since there the comparison factor is never invertible. -/
theorem extendScalars_map_dualizingExtFunctor_map_cone_comp_baseChange
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : Cone M) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
          ((dualizingExtFunctor ω i).map (c.π.app (op n)).op) ≫
        (dualizingExtFunctorBaseChange F comparison hf ω i).app (op c.pt) =
      (dualizingExtFunctorBaseChange F comparison hf ω i).app (op (M.obj (op n))) ≫
        dualizingExtSystemToLimit
            (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (F.obj ω) i n ≫
          (dualizingExtFunctor (F.obj ω) i).map
            (limit.lift (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S))
              ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapCone c)).op := by
  have h := extendScalars_map_dualizingExtFunctor_map_comp_baseChange F comparison hf ω i
    (c.π.app (op n))
  rw [← dualizingExtSystemToLimit_comp_map_coneLift (A := A) (S := S)] at h
  exact h

omit [IsNoetherianRing A] in
/-- **The `α_n` of the base-changed system, followed by the limit comparison, is the
`H^{-i}(RHom_S(-, -))` of the base-changed limit projection.**
`Stacks.Algebraization.dualizingExtSystemToLimit_comp_map_coneLift` at the limit cone, whose
base-change comparison is `CategoryTheory.Limits.limit.post`. -/
theorem dualizingExtSystemToLimit_comp_map_limitPost
    (ω' : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    dualizingExtSystemToLimit (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) ω' i n ≫
        (dualizingExtFunctor ω' i).map
          (limit.post M (ModuleCat.extendScalars.{u, u, u} (algebraMap A S))).op =
      (dualizingExtFunctor ω' i).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map (limit.π M (op n))).op :=
  dualizingExtSystemToLimit_comp_map_coneLift ω' i M (limit.cone M) n

omit [IsNoetherianRing A] in
/-- **Flat base change carries the cocone `α` to the cocone `α` of the base-changed system**,
up to the comparison of the base change with the limit of the system.

`Stacks.Algebraization.extendScalars_map_dualizingExtFunctor_map_comp_baseChange` at the limit
projection `lim M_k → M_n`, with
`Stacks.Algebraization.dualizingExtSystemToLimit_comp_map_limitPost` rewriting its right-hand
side into the `α_n` of the base-changed system.

The factor `H^{-i}(RHom_S(lim.post, -))` is not removable; see the implementation notes of this
file for the counterexample at the adic quotient tower, and
`Stacks.Algebraization.dualizingExtSystemToLimit_comp_baseChange_of_isIso_limitPost` for the
hypothesis that removes it. -/
theorem extendScalars_map_dualizingExtSystemToLimit_comp_baseChange
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
          (dualizingExtSystemToLimit M ω i n) ≫
        (dualizingExtFunctorBaseChange F comparison hf ω i).app (op (limit M)) =
      (dualizingExtFunctorBaseChange F comparison hf ω i).app (op (M.obj (op n))) ≫
        dualizingExtSystemToLimit
            (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (F.obj ω) i n ≫
          (dualizingExtFunctor (F.obj ω) i).map
            (limit.post M (ModuleCat.extendScalars.{u, u, u} (algebraMap A S))).op := by
  have h := extendScalars_map_dualizingExtFunctor_map_comp_baseChange F comparison hf ω i
    (limit.π M (op n))
  rw [← dualizingExtSystemToLimit_comp_map_limitPost (A := A) (S := S)] at h
  exact h

omit [IsNoetherianRing A] in
/-- **What the descent of `Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` needs, and the
single hypothesis it costs.** If the comparison factor
`H^{-i}(RHom_S(lim.lift, ω ⊗ᴸ_A S))` is injective, then the kernel of the base change of the
`n`-th leg of the Ext-cocone of a cone `c` is contained in the kernel of the `α_n` of the
base-changed system, read through the base-change comparison at `M_n`.

This is the inclusion the descent consumes. Over `S` one proves
`ker (α'_n) ≤ ker (transition)` -- from essential constancy, or from injectivity of one later
`α'_m` -- and the base-change comparison carries the transitions of the system over `A` to
those over `S`, so with this inclusion the hypothesis
`ker (S ⊗ α_n) ≤ ker (S ⊗ transition)` of
`Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` follows. Only the inclusion in this
direction is needed; the reverse would additionally cost injectivity of the base-change
comparison at the vertex.

At the limit cone the hypothesis is *not* available: the comparison is then
`CategoryTheory.Limits.limit.post`, which in the situation of [Stacks, Tag 0EHK] is the
surjection `S ⊗_A lim M_n ↠ lim M_n` and is not injective (implementation notes), so its
`H^{-i}(RHom_S(-, -))` is injective only if the connecting map out of `H^{-i-1}` of the kernel
vanishes -- a further statement about `ω`. At a cone whose vertex is a *finite* `A`-module the
comparison is invertible and the hypothesis is free, which is why the cone here is arbitrary. -/
theorem apply_eq_zero_dualizingExtSystemToLimit_of_baseChange
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : Cone M) (n : ℕ)
    (hinj : Function.Injective ((dualizingExtFunctor (F.obj ω) i).map
      (limit.lift (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S))
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapCone c)).op).hom)
    (x : (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).obj
      ((dualizingExtSystem M ω i).obj n))
    (hx : ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
      ((dualizingExtFunctor ω i).map (c.π.app (op n)).op)).hom x = 0) :
    ((dualizingExtFunctorBaseChange F comparison hf ω i).app (op (M.obj (op n))) ≫
        dualizingExtSystemToLimit
          (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (F.obj ω) i n).hom x = 0 := by
  have h0 : ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
      ((dualizingExtFunctor ω i).map (c.π.app (op n)).op) ≫
        (dualizingExtFunctorBaseChange F comparison hf ω i).app (op c.pt)).hom x = 0 := by
    show ((dualizingExtFunctorBaseChange F comparison hf ω i).app (op c.pt)).hom
      (((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
        ((dualizingExtFunctor ω i).map (c.π.app (op n)).op)).hom x) = 0
    rw [hx, map_zero]
  rw [extendScalars_map_dualizingExtFunctor_map_cone_comp_baseChange] at h0
  refine hinj ?_
  rw [map_zero]
  exact h0

/-- The components of `Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso` are the
components of `Stacks.Algebraization.dualizingExtFunctorBaseChange`, which is what makes the
compatibility above a statement about that isomorphism of systems. -/
theorem dualizingExtSystemBaseChangeNatIso_hom_app
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A))
    (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    (dualizingExtSystemBaseChangeNatIso F comparison hf ω hωge i M hfin).hom.app n =
      (dualizingExtFunctorBaseChange F comparison hf ω i).app (op (M.obj (op n))) :=
  rfl

/-- **`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso` carries the cocone `α` of the
system to the cocone `α` of the base-changed system**, up to the comparison of the base change
with the limit of the system.
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange` with its
right-hand factor read as a component of that isomorphism of systems, by
`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso_hom_app`. -/
theorem dualizingExtSystemBaseChangeNatIso_hom_app_comp_dualizingExtSystemToLimit
    (hf : (algebraMap A S).Flat) (ω : DerivedCategory (ModuleCat.{u} A))
    (hωge : ∃ b : ℤ, ω.IsGE b) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
          (dualizingExtSystemToLimit M ω i n) ≫
        (dualizingExtFunctorBaseChange F comparison hf ω i).app (op (limit M)) =
      (dualizingExtSystemBaseChangeNatIso F comparison hf ω hωge i M hfin).hom.app n ≫
        dualizingExtSystemToLimit
            (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) (F.obj ω) i n ≫
          (dualizingExtFunctor (F.obj ω) i).map
            (limit.post M (ModuleCat.extendScalars.{u, u, u} (algebraMap A S))).op :=
  extendScalars_map_dualizingExtSystemToLimit_comp_baseChange F comparison hf ω i M n

end General

/-! ### The two base changes of the route, `A → A_f` and `A_f → (A_f)^∧` -/

section Localization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (T : Submonoid A)

omit [IsNoetherianRing A] in
/-- **Localization carries the cocone `α` to the cocone `α` of the localized system**, up to the
comparison of the localization with the limit of the system.
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange` at
`Stacks.Algebraization.dualizingExtFunctorLocalizationBaseChange`. -/
theorem extendScalars_map_dualizingExtSystemToLimit_comp_localizationBaseChange
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T))).map
          (dualizingExtSystemToLimit M ω i n) ≫
        (dualizingExtFunctorLocalizationBaseChange T ω i).app (op (limit M)) =
      (dualizingExtFunctorLocalizationBaseChange T ω i).app (op (M.obj (op n))) ≫
        dualizingExtSystemToLimit
            (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T)))
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization T))).functor.obj ω) i n ≫
          (dualizingExtFunctor
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization T))).functor.obj ω) i).map
            (limit.post M
              (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization T)))).op :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (Localization T))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization T))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  extendScalars_map_dualizingExtSystemToLimit_comp_baseChange D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization T) T)) ω i M n

end Localization

section AdicCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)

/-- **Completion carries the cocone `α` to the cocone `α` of the completed system**, up to the
comparison of the completion with the limit of the system.
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange` at
`Stacks.Algebraization.dualizingExtFunctorAdicCompletionBaseChange`.

**This is the statement the descent of
`Stacks.ker_le_ker_of_baseChange_of_faithfullyFlat` asks for, and the comparison factor is
exactly what it does not supply.** The descent needs the cocone handed over at `A^∧` to *be* the
base change of the cocone at `A`; what this provides is the base change of the cocone followed
by `H^{-i}(RHom(lim.post, -))`, and that factor is not invertible for the adic quotient tower
-- the implementation notes of this file carry the counterexample. So the descent along this
base change costs the injectivity of that factor, and nothing in the situation gives it. -/
theorem extendScalars_map_dualizingExtSystemToLimit_comp_adicCompletionBaseChange
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A))).map
          (dualizingExtSystemToLimit M ω i n) ≫
        (dualizingExtFunctorAdicCompletionBaseChange J ω i).app (op (limit M)) =
      (dualizingExtFunctorAdicCompletionBaseChange J ω i).app (op (M.obj (op n))) ≫
        dualizingExtSystemToLimit
            (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A)))
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (AdicCompletion J A))).functor.obj ω) i n ≫
          (dualizingExtFunctor
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (AdicCompletion J A))).functor.obj ω) i).map
            (limit.post M
              (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion J A)))).op :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (AdicCompletion J A))
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (AdicCompletion J A))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  extendScalars_map_dualizingExtSystemToLimit_comp_baseChange D.functor cmpD
    (RingHom.flat_algebraMap_iff.mpr inferInstance) ω i M n

end AdicCompletion

/-! ### Two base changes in a row -/

section TwoStep

variable {A S S' : Type u} [CommRing A] [IsNoetherianRing A] [CommRing S] [IsNoetherianRing S]
  [Algebra A S] [CommRing S'] [Algebra S S']
  (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
  (F' : DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} S'))
  (comparison' : DerivedCategory.Q ⋙ F' ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F'.IsLeftDerivedFunctor comparison'
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ))]

/-- **The formal shape of a two-step base-change chase.** Given a factorisation `p ≫ q = r ≫ s ≫ t`
over the first ring, a functor `Φ` to the second, and the two comparisons `h3` carrying `Φ t` past
`y` and `h2` carrying `Φ s` past `u`, the composite `Φ p ≫ Φ q ≫ y` factors through `w` with the
two comparison factors collected into the single `k`.

This is stated with abstract objects and morphisms on purpose. The chase is an identity between
composites in two categories and uses nothing about `Ext`, about flatness or about limits; the
concrete instance below has objects spelled in several defeq-but-not-syntactic ways
(`dualizingExtLimit M ω i` versus `(dualizingExtFunctor ω i).obj (op (limit M))`, and the
transported terms of a system versus the terms of the transported system), on which the rewrites
of the chase cannot be keyed. Abstracting the objects removes that obstacle and nothing else.

It is used twice: once for `A → A_f → (A_f)^∧` and once again, with the first factorisation being
the two-step statement itself, for the third step `(A_f)^∧ → ((A_f)^∧)_𝔮`. -/
public theorem comp_eq_map_comp_twoStep {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {X₀ X₁ X₂ Y₀ Y₁ : C} {E₀ E₁ E₂ E₃ : D}
    (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (r : X₀ ⟶ Y₀) (s : Y₀ ⟶ Y₁) (t : Y₁ ⟶ X₂)
    (h1 : p ≫ q = r ≫ s ≫ t)
    (y : Φ.obj X₂ ⟶ E₀) (u : Φ.obj Y₁ ⟶ E₁) (z : E₁ ⟶ E₀) (h3 : Φ.map t ≫ y = u ≫ z)
    (v : Φ.obj Y₀ ⟶ E₂) (w : E₂ ⟶ E₃) (x : E₃ ⟶ E₁) (h2 : Φ.map s ≫ u = v ≫ w ≫ x)
    (k : E₃ ⟶ E₀) (h4 : x ≫ z = k) :
    Φ.map p ≫ Φ.map q ≫ y = (Φ.map r ≫ v) ≫ w ≫ k := by
  rw [← h4, ← Category.assoc (Φ.map p), ← Φ.map_comp, h1, Φ.map_comp, Φ.map_comp]
  simp only [Category.assoc]
  rw [h3, ← Category.assoc (Φ.map s), h2]
  simp only [Category.assoc]

omit [IsNoetherianRing A] [IsNoetherianRing S] in
/-- **Two flat base changes in a row carry the cocone `α` to the cocone `α` over the second
ring**, up to the composite of the two comparisons of a base change with the limit of a system.

This is `Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_baseChange` for
a chain `A → S → S'`, and it is *not* the two one-step statements applied in turn: composing
them leaves the first step's `CategoryTheory.Limits.limit.post` factor on the wrong side of the
second base change, and moving it across is the naturality of the second comparison at that very
map. What comes out is the single factor
`H^{-i}(RHom_{S'}(S' ⊗_S lim.post ≫ lim.post, -))` on the right.

The factor is written as the honest composite
`E'.map (limit.post M E) ≫ limit.post (M ⋙ E) E'` and not collapsed to
`limit.post M (E ⋙ E')` — the two agree by `CategoryTheory.Limits.limit.post_post`, but the
composite is the form in which each half can be recognised, and *neither* half is invertible for
the adic quotient tower (see the implementation notes of this file). So this transports a cocone
forward along a chain and gives no descent backwards along it. -/
theorem extendScalars_map_dualizingExtSystemToLimit_comp_baseChange_twoStep
    (hf : (algebraMap A S).Flat) (hf' : (algebraMap S S').Flat)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).map
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).map
            (dualizingExtSystemToLimit M ω i n)) ≫
        (ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).map
            ((dualizingExtFunctorBaseChange F comparison hf ω i).app (op (limit M))) ≫
          (dualizingExtFunctorBaseChange F' comparison' hf' (F.obj ω) i).app
            (op ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).obj (limit M))) =
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).map
            ((dualizingExtFunctorBaseChange F comparison hf ω i).app (op (M.obj (op n)))) ≫
          (dualizingExtFunctorBaseChange F' comparison' hf' (F.obj ω) i).app
            (op ((M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).obj (op n)))) ≫
        dualizingExtSystemToLimit
            ((M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) ⋙
              ModuleCat.extendScalars.{u, u, u} (algebraMap S S'))
            (F'.obj (F.obj ω)) i n ≫
          (dualizingExtFunctor (F'.obj (F.obj ω)) i).map
            ((ModuleCat.extendScalars.{u, u, u} (algebraMap S S')).map
                (limit.post M (ModuleCat.extendScalars.{u, u, u} (algebraMap A S))) ≫
              limit.post (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S))
                (ModuleCat.extendScalars.{u, u, u} (algebraMap S S'))).op := by
  have hbc1 := extendScalars_map_dualizingExtSystemToLimit_comp_baseChange F comparison hf ω i M n
  have hbc2 := extendScalars_map_dualizingExtSystemToLimit_comp_baseChange F' comparison' hf'
    (F.obj ω) i (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A S)) n
  have hnat := (dualizingExtFunctorBaseChange F' comparison' hf' (F.obj ω) i).naturality
    (limit.post M (ModuleCat.extendScalars.{u, u, u} (algebraMap A S))).op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hnat
  set EA := ModuleCat.extendScalars.{u, u, u} (algebraMap A S)
  set ES := ModuleCat.extendScalars.{u, u, u} (algebraMap S S')
  set bc := dualizingExtFunctorBaseChange F comparison hf ω i
  set bc' := dualizingExtFunctorBaseChange F' comparison' hf' (F.obj ω) i
  set G'' := dualizingExtFunctor (F'.obj (F.obj ω)) i
  have hpost : G''.map (limit.post (M ⋙ EA) ES).op ≫ G''.map (ES.map (limit.post M EA)).op =
      G''.map (ES.map (limit.post M EA) ≫ limit.post (M ⋙ EA) ES).op :=
    (G''.map_comp _ _).symm.trans (congrArg G''.map op_comp.symm)
  exact comp_eq_map_comp_twoStep ES _ _ _ _ _ hbc1 _ _ _ hnat _ _ _ hbc2 _ hpost

end TwoStep


end Stacks.Algebraization

end
