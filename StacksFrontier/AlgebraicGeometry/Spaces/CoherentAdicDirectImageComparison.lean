module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Comparing a coherent adic system with the direct image of a completion

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓙 ⊆ 𝒪_Y` and
`𝓘 ⊆ 𝒪_X` be sheaves of ideals on their small étale sites, let `(𝓖_n)` be an object of
`Coh(Y, 𝓙)`, let `𝓕` be a coherent `𝒪_X`-module and let `β : (f^*𝓖_n) ⟶ 𝓕^∧` be an isomorphism
in `Coh(X, 𝓘)`.  The composites

`γ_n : 𝓖_n ⟶ f_*f^*𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`

of the adjunction map with `f_*β_n` form a morphism of inverse systems of `𝒪_Y`-modules, and the
levelwise kernels and cokernels of `γ` are annihilated by a power of a sheaf of ideals
`𝓚 ⊆ 𝒪_Y` exactly when those of the adjunction maps are.

## Main definitions

* `AlgebraicGeometry.Space.pullbackPushforwardUnitSystem` — the adjunction maps
  `𝓖_n ⟶ f_*f^*𝓖_n` of an inverse system, as a morphism of inverse systems.
* `AlgebraicGeometry.Space.directImageComparison` — **the maps `γ_n`.**

## Main results

* `AlgebraicGeometry.Space.exists_pos_idealPowerMultiple_kernel_cokernel_comp_iso_iff` —
  annihilation of the levelwise kernels and cokernels by one positive power of a sheaf of ideals
  is unchanged by composing with an isomorphism of inverse systems.
* `AlgebraicGeometry.Space.directImageComparison_app` and
  `AlgebraicGeometry.Space.pushforward_completion_obj` — `γ_n` is `f_*β_n` after the adjunction
  map, and its target at level `n` is `f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`.
* `AlgebraicGeometry.Space.kernelDirectImageComparisonIso` and
  `AlgebraicGeometry.Space.cokernelDirectImageComparisonIso` — the levelwise kernel and cokernel
  of `γ` are those of the adjunction map.
* `AlgebraicGeometry.Space.exists_pos_idealPowerMultiple_kernel_cokernel_directImageComparison_iff`
  — **the reduction of the kernel–cokernel condition of Stacks 08BD to the adjunction maps.**

## Implementation notes

`Coh(X, 𝓘)` is a full subcategory of the inverse systems of `𝒪_X`-modules, so the source's
isomorphism `β` in `Coh(X, 𝓘)` is an isomorphism of the underlying inverse systems and is taken
in that form; nothing below needs `(f^*𝓖_n)` to be recognised as an object of `Coh(X, 𝓘)`.  For
the same reason the ideal `𝓘` is an arbitrary sheaf of ideals on `X` rather than the source's
`f^{-1}𝓙 𝒪_X`, which is a generalisation: the relation between `𝓘` and `𝓙` is not used.

The system is zero-indexed, as `AlgebraicGeometry.Space.IsCoherentAdicSystem` is, so level `n`
carries the source's `𝓖_{n+1}` and `pushforward_completion_obj` produces `𝓕/𝓘 ⁿ⁺¹𝓕`.

That the levelwise kernel and cokernel of `γ` are those of the adjunction map is
`CategoryTheory.Limits.kernelCompMono` and `CategoryTheory.Limits.cokernelCompIsIso` applied to
the isomorphism `f_*β_n`; annihilation by a fixed power of a sheaf of ideals is carried across by
`AlgebraicGeometry.Space.idealPowerMultiple_eq_bot_of_iso`.

What is **not** here is the map `α : (𝓖_n) ⟶ (f_*𝓕)^∧` of Stacks 08BD.  Forming its target
needs coherence of the direct image along a representable proper morphism
([Stacks, Tag 08AR]), which this library does not prove, and the source produces `α` by étale
descent from the scheme case ([Stacks, Tag 088B]), whose proof rests on the theorem on formal
functions ([Stacks, Tag 02OC]) and on the full faithfulness of completion over a complete base
([Stacks, Tag 0883]), both of which rest in turn on the uniform Artin-Rees bounds of
[Stacks, Tag 02OB], not proved here.  The part of 08BD recorded here — the maps `γ_n`, and the
fact that the annihilation condition on them is the annihilation condition on the adjunction
maps — is independent of all of that, and it is the only step of the source's proof carried out
before the reduction to schemes.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The adjunction maps of an inverse system -/

/-- **The adjunction maps `𝓖_n ⟶ f_*f^*𝓖_n` of an inverse system of `𝒪_Y`-modules** on an
algebraic space, assembled into a morphism of inverse systems.  Naturality is naturality of the
unit of the adjunction `f^* ⊣ f_*` of Stacks 03LU. -/
def pullbackPushforwardUnitSystem (f : X ⟶ Y) (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Y.1 Y.2) :
    E ⟶ E ⋙ modulePullback B S hS f ⋙ modulePushforward B S hS f where
  app n := (modulePullbackAdjunction B S hS f).unit.app (E.obj n)
  naturality _ _ g := (modulePullbackAdjunction B S hS f).unit.naturality (E.map g)

/-- The `n`-th adjunction map of an inverse system is the adjunction map of its `n`-th term. -/
theorem pullbackPushforwardUnitSystem_app (f : X ⟶ Y)
    (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Y.1 Y.2) (n : ℕᵒᵖ) :
    (pullbackPushforwardUnitSystem B S hS f E).app n =
      (modulePullbackAdjunction B S hS f).unit.app (E.obj n) :=
  rfl

/-! ### Annihilation of levelwise kernels and cokernels is an isomorphism-invariant -/

/-- **Annihilation of the levelwise kernels and cokernels by one positive power of a sheaf of
ideals `𝓚` is unchanged by composing with an isomorphism of inverse systems.**  The kernel of
`α_n ≫ e_n` is the kernel of `α_n` and its cokernel is the cokernel of `α_n`, and annihilation
by a fixed power of a sheaf of ideals transports along an isomorphism of modules. -/
theorem exists_pos_idealPowerMultiple_kernel_cokernel_comp_iso_iff
    (𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    {A C D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Y.1 Y.2} (α : A ⟶ C) (e : C ≅ D) :
    (∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        idealPowerMultiple B S hS Y.1 Y.2 𝓚 t (kernel ((α ≫ e.hom).app (op k))) = ⊥ ∧
          idealPowerMultiple B S hS Y.1 Y.2 𝓚 t
            (cokernel ((α ≫ e.hom).app (op k))) = ⊥) ↔
      ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        idealPowerMultiple B S hS Y.1 Y.2 𝓚 t (kernel (α.app (op k))) = ⊥ ∧
          idealPowerMultiple B S hS Y.1 Y.2 𝓚 t (cokernel (α.app (op k))) = ⊥ := by
  have tr : ∀ {M N : Modules.{u, u} B S hS Y.1 Y.2} (e : M ≅ N) (t : ℕ),
      idealPowerMultiple B S hS Y.1 Y.2 𝓚 t M = ⊥ ↔
        idealPowerMultiple B S hS Y.1 Y.2 𝓚 t N = ⊥ :=
    fun e t => ⟨idealPowerMultiple_eq_bot_of_iso B S hS Y.1 Y.2 𝓚 e t,
      idealPowerMultiple_eq_bot_of_iso B S hS Y.1 Y.2 𝓚 e.symm t⟩
  exact exists_congr fun t => and_congr_right fun _ => forall_congr' fun k =>
    and_congr (tr (kernelCompMono (α.app (op k)) (e.hom.app (op k))) t)
      (tr (cokernelCompIsIso (α.app (op k)) (e.hom.app (op k))) t)

/-! ### The maps `γ_n` -/

variable (f : X ⟶ Y)
    (𝓙 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (G : CoherentAdicSystems B S hS Y.1 Y.2 𝓙)
    (F : CoherentModules.{u, u} B S hS X.1 X.2)
    (β : G.obj ⋙ modulePullback B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj)

/-- The target of `γ` has `f_*(𝓕/𝓘 ⁿ⁺¹𝓕)` at level `n`. -/
theorem pushforward_completion_obj (n : ℕ) :
    (((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj ⋙
        modulePushforward B S hS f).obj (op n) =
      (modulePushforward B S hS f).obj
        (idealPowerQuotient B S hS X.1 X.2 𝓘 (n + 1) F.obj) :=
  rfl

/-- The isomorphism `β : (f^*𝓖_n) ⟶ 𝓕^∧` of Stacks 08BD, pushed forward along `f`. -/
def directImagePushforwardIso :
    G.obj ⋙ modulePullback B S hS f ⋙ modulePushforward B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj ⋙ modulePushforward B S hS f :=
  Functor.isoWhiskerRight β (modulePushforward B S hS f)

/-- **The maps `γ_n : 𝓖_n ⟶ f_*f^*𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)` of the proof of Stacks 08BD**, as a
morphism of inverse systems of `𝒪_Y`-modules on an algebraic space: the adjunction map followed
by `f_*β_n`. -/
@[stacks 08BD "the maps gamma_n of the proof: the adjunction map followed by f_*beta_n. The map \
alpha into (f_*F)^ is a different declaration and is not constructed in this library"]
def directImageComparison :
    G.obj ⟶ ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj ⋙ modulePushforward B S hS f :=
  pullbackPushforwardUnitSystem B S hS f G.obj ≫
    (directImagePushforwardIso B S hS f 𝓙 𝓘 hI G F β).hom

/-- `γ_n` is the adjunction map followed by `f_*β_n`. -/
theorem directImageComparison_app (n : ℕᵒᵖ) :
    (directImageComparison B S hS f 𝓙 𝓘 hI G F β).app n =
      (modulePullbackAdjunction B S hS f).unit.app (G.obj.obj n) ≫
        (modulePushforward B S hS f).map (β.hom.app n) :=
  rfl

/-- The levelwise kernel of `γ` is the kernel of the adjunction map, `f_*β_n` being an
isomorphism. -/
def kernelDirectImageComparisonIso (n : ℕᵒᵖ) :
    kernel ((directImageComparison B S hS f 𝓙 𝓘 hI G F β).app n) ≅
      kernel ((pullbackPushforwardUnitSystem B S hS f G.obj).app n) :=
  kernelCompMono ((pullbackPushforwardUnitSystem B S hS f G.obj).app n)
    ((directImagePushforwardIso B S hS f 𝓙 𝓘 hI G F β).hom.app n)

/-- The levelwise cokernel of `γ` is the cokernel of the adjunction map, `f_*β_n` being an
isomorphism. -/
def cokernelDirectImageComparisonIso (n : ℕᵒᵖ) :
    cokernel ((directImageComparison B S hS f 𝓙 𝓘 hI G F β).app n) ≅
      cokernel ((pullbackPushforwardUnitSystem B S hS f G.obj).app n) :=
  cokernelCompIsIso ((pullbackPushforwardUnitSystem B S hS f G.obj).app n)
    ((directImagePushforwardIso B S hS f 𝓙 𝓘 hI G F β).hom.app n)

/-- **The reduction of the kernel–cokernel condition of Stacks 08BD to the adjunction maps.**
Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓙, 𝓚 ⊆ 𝒪_Y` and
`𝓘 ⊆ 𝒪_X` be sheaves of ideals, let `(𝓖_n)` be an object of `Coh(Y, 𝓙)`, let `𝓕` be a coherent
`𝒪_X`-module and let `β : (f^*𝓖_n) ⟶ 𝓕^∧` be an isomorphism in `Coh(X, 𝓘)`.  The maps

`γ_n : 𝓖_n ⟶ f_*f^*𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`

have their levelwise kernels and cokernels annihilated by one positive power of `𝓚` exactly when
the adjunction maps `𝓖_n ⟶ f_*f^*𝓖_n` do, because `γ_n` differs from the adjunction map by the
isomorphism `f_*β_n`.  This is the step of the source's proof which makes the isomorphism `β`
disappear from the annihilation statement, leaving the adjunction map that the closing paragraph
of the scheme case is about.

The map `α : (𝓖_n) ⟶ (f_*𝓕)^∧` which the source produces out of `γ` is not constructed; see the
implementation notes of this file. -/
@[stacks 08BD "the reduction of the lemma's kernel-cokernel condition from gamma to the \
adjunction maps. The map alpha into (f_*F)^ is not constructed in this library, which proves \
neither 08AR for a representable proper morphism nor the uniform Artin-Rees bounds 02OB behind \
the scheme case 088B"]
theorem exists_pos_idealPowerMultiple_kernel_cokernel_directImageComparison_iff
    (𝓚 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule) :
    (∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        idealPowerMultiple B S hS Y.1 Y.2 𝓚 t
            (kernel ((directImageComparison B S hS f 𝓙 𝓘 hI G F β).app (op k))) = ⊥ ∧
          idealPowerMultiple B S hS Y.1 Y.2 𝓚 t
            (cokernel ((directImageComparison B S hS f 𝓙 𝓘 hI G F β).app (op k))) = ⊥) ↔
      ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        idealPowerMultiple B S hS Y.1 Y.2 𝓚 t
            (kernel ((pullbackPushforwardUnitSystem B S hS f G.obj).app (op k))) = ⊥ ∧
          idealPowerMultiple B S hS Y.1 Y.2 𝓚 t
            (cokernel ((pullbackPushforwardUnitSystem B S hS f G.obj).app (op k))) = ⊥ :=
  exists_pos_idealPowerMultiple_kernel_cokernel_comp_iso_iff B S hS 𝓚
    (pullbackPushforwardUnitSystem B S hS f G.obj)
    (directImagePushforwardIso B S hS f 𝓙 𝓘 hI G F β)

end AlgebraicGeometry.Space

end
