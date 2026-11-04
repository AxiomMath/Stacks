module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatOverLocalBase
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactCriterion
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.RingTheory.AdicTorsion.PowerQuotient

/-!
# Short exactness of `0 → F_n → F_{n+1} → F_1 → 0` along a principal ideal

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf, `(F_n)` a coherent adic system along `ℐ`
and `t` a global section of `𝒪_X` with `ℐ = (t)` at every stalk. Multiplication by `t` on
`F_{n+1}` factors through the transition map as `ι_n : F_n ⟶ F_{n+1}`
(`Stacks.Coherent.IsCoherentAdicSystem.principalRaise`), and the resulting sequence

  `0 → F_n → F_{n+1} → F_1 → 0`

is short exact as soon as `t` is a nonzerodivisor on every stalk and each `F_m` is finite
locally free over `𝒪_X / ℐ ᵐ⁺¹`. This file proves that, which is the one step left open by
`Stacks.Algebraization.hasPrincipalShortExactSequences_of_shortExact` and hence the last
ingredient of condition (1) of [Stacks, Tag 0H39] for the tower of [Stacks, Tag 0DXW].

The argument is stalkwise. Write `R = 𝒪_{X,x}`, `𝔣 = ℐ_x`, `T` for the germ of `t` and
`M_m = (F_m)_x`. The three facts in play are that the transition `M_{n+1} ⟶ M_n` is surjective
with kernel `𝔣 ⁿ⁺¹ M_{n+1}`, that the iterated transition `M_{n+1} ⟶ M_0` has kernel
`𝔣 M_{n+1}`, and that `ι_n` composed with the transition is multiplication by `T`.

*Injectivity.* If `ι_n a = 0`, lift `a` to `b ∈ M_{n+1}`; then `T b = 0`. Finite local freeness
makes `M_{n+1}` a free `R / 𝔣 ⁿ⁺²`-module, and in `R / (Tⁿ⁺²)` an element killed by `T` is a
multiple of `Tⁿ⁺¹` because `T` is a nonzerodivisor. So `b ∈ 𝔣 ⁿ⁺¹ M_{n+1}`, which is the kernel
of the transition, and `a = 0`.

*Exactness in the middle.* The kernel of `M_{n+1} ⟶ M_0` is `𝔣 M_{n+1} = T M_{n+1}`, and every
`T b` is `ι_n` of the image of `b`.

*Surjectivity* needs nothing: the iterated transition is a composite of epimorphisms.

## Main results

* `Stacks.Coherent.modulesStalkFunctor_map_mulSection` — the stalk of multiplication by a
  global section is multiplication by its germ.
* `Stacks.Coherent.IsCoherentAdicSystem.proj_eq_map` — the iterated transition of
  `Stacks.Cohomology.InverseSystems.TorsionFreeDivisible.proj` is the system's own map
  `op k ⟶ op 0`.
* `Stacks.Coherent.IsCoherentAdicSystem.ker_stalk_map_zero` — on stalks the iterated
  transition `F_{k+1} ⟶ F_1` has kernel `ℐ_x F_{k+1,x}`.
* `Stacks.Coherent.IsCoherentAdicSystem.shortExact_principalShortComplex` — the short exactness
  above.
* `Stacks.Algebraization.shortExact_principalShortComplex` and
  `Stacks.Algebraization.hasPrincipalShortExactSequences_of_principal` — the same at an
  algebraization situation with `I = (f)`, and the hypothesis of [Stacks, Tag 0DXW] it
  produces.

## Implementation notes

Finite local freeness enters only through its consequence at a point: a linear equivalence
`(F_m)_x ≃ₗ (𝒪_{X,x} / ℐ_x ᵐ⁺¹)ʳ` for some `r`. That is what a finite locally free
`𝒪_X / ℐ ᵐ⁺¹`-module has at every point, and it is all the argument uses, so it is the shape
the hypothesis takes. Likewise `ℐ = (t)` is used only through `ℐ_x = (T)`.

Two spellings of the stalk of a morphism of modules on a scheme meet here:
`Stacks.ModuleSkyscraper.modulesStalkFunctor`, in which the ideal-power computations of
`Stacks.Algebraization.ker_stalk_coherentAdicTransition` are stated, and
`AlgebraicGeometry.stalkLinearMap`, in which multiplication by a global section is computed by
`Stacks.Algebraization.stalkLinearMap_smulPowHom_one`. They are the same linear map;
`Stacks.Coherent.modulesStalkFunctor_map_eq_stalkLinearMap` says so, by evaluating both on a
germ.

The kernel of the iterated transition is obtained by induction rather than from a single
quotient presentation: one step down, the kernel of `F_{k+2} ⟶ F_1` is the preimage of
`𝔣 F_{k+1,x}` under a surjection whose own kernel `𝔣 ᵏ⁺² F_{k+2,x}` is contained in
`𝔣 F_{k+2,x}`, so the preimage is `𝔣 F_{k+2,x}` again.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.PrincipalIdealExtension (restrictTop)
open Stacks.Cohomology.InverseSystems.TorsionFreeDivisible (proj)
open Stacks.ModuleSkyscraper (modulesStalkFunctor modulesStalkFunctor_map_germ)

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-! ### The two spellings of the stalk of a morphism -/

/-- **The two readings of the stalk of a morphism of modules on a scheme agree.** Both send the
germ of a section to the germ of its image, so they agree on every element of the stalk. -/
theorem modulesStalkFunctor_map_eq_stalkLinearMap {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (m : (modulesStalkFunctor X x).obj M) :
    ((modulesStalkFunctor X x).map (C := X.Modules) φ).hom m =
      AlgebraicGeometry.stalkLinearMap M N φ x m := by
  obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
  rw [AlgebraicGeometry.stalkLinearMap_germ M N φ U x hx m₀]
  exact modulesStalkFunctor_map_germ x φ U hx m₀

/-- **The stalk of multiplication by a global section is multiplication by its germ.** -/
theorem modulesStalkFunctor_map_mulSection (t : Γ(X, ⊤)) (N : X.Modules) (x : X)
    (m : (modulesStalkFunctor X x).obj N) :
    ((modulesStalkFunctor X x).map (C := X.Modules) (mulSection t N)).hom m =
      (X.presheaf.Γgerm x).hom t • m :=
  (modulesStalkFunctor_map_eq_stalkLinearMap (mulSection t N) x m).trans
    (Stacks.Algebraization.stalkLinearMap_smulPowHom_one N t x m)

namespace IsCoherentAdicSystem

variable {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}

/-! ### The iterated transition map -/

/-- **The iterated transition `F_{k+1} ⟶ F_1` is the system's own map.** Both are images under
`F` of the unique morphism `op k ⟶ op 0` of `ℕᵒᵖ`. -/
theorem proj_eq_map (F : ℕᵒᵖ ⥤ X.Modules) (k : ℕ) :
    proj (objFamily F) (mapFamily F) k = F.map (homOfLE (Nat.zero_le k)).op := by
  induction k with
  | zero =>
    have h : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) :=
      Subsingleton.elim _ _
    rw [show proj (objFamily F) (mapFamily F) 0 = 𝟙 _ from rfl, h, F.map_id]
    rfl
  | succ k ih =>
    have h : (homOfLE (Nat.le_succ k)).op ≫ (homOfLE (Nat.zero_le k)).op =
        (homOfLE (Nat.zero_le (k + 1))).op :=
      Subsingleton.elim _ _
    rw [show proj (objFamily F) (mapFamily F) (k + 1) =
      mapFamily F k ≫ proj (objFamily F) (mapFamily F) k from rfl, ih, ← F.map_comp, h]

/-- **On stalks, the kernel of the iterated transition `F_{k+1} ⟶ F_1` is `ℐ_x F_{k+1,x}`.**

For `k = 0` this is the kernel of a single transition map. One step up, the iterated transition
factors as a surjection `F_{k+2,x} ⟶ F_{k+1,x}` with kernel `ℐ_x ᵏ⁺² F_{k+2,x}` followed by the
iterated transition out of `F_{k+1,x}`, so its kernel is the preimage of `ℐ_x F_{k+1,x}`, which
is `ℐ_x F_{k+2,x} ⊔ ℐ_x ᵏ⁺² F_{k+2,x} = ℐ_x F_{k+2,x}`. -/
theorem ker_stalk_map_zero (hF : IsCoherentAdicSystem I F) (x : X) (k : ℕ) :
    LinearMap.ker ((modulesStalkFunctor X x).map (C := X.Modules)
        (F.map (homOfLE (Nat.zero_le (k + 1))).op)).hom =
      IdealSheafData.stalk I x •
        (⊤ : Submodule (X.presheaf.stalk x)
          ((modulesStalkFunctor X x).obj (F.obj (op (k + 1))))) := by
  induction k with
  | zero =>
    have hhom : (homOfLE (Nat.zero_le (0 + 1))).op = (homOfLE (Nat.le_succ 0)).op :=
      Subsingleton.elim _ _
    have h := Stacks.Algebraization.ker_stalk_coherentAdicTransition (J := I) ⟨F, hF⟩ x 0
    have hpow : IdealSheafData.stalk I x ^ (0 + 1) = IdealSheafData.stalk I x := pow_one _
    rw [hhom]
    exact h.trans (by rw [hpow])
  | succ k ih =>
    have hcomp : F.map (homOfLE (Nat.zero_le (k + 1 + 1))).op =
        F.map (homOfLE (Nat.le_succ (k + 1))).op ≫
          F.map (homOfLE (Nat.zero_le (k + 1))).op := by
      rw [← F.map_comp]
      exact congrArg F.map (Subsingleton.elim _ _)
    have hsurj : Function.Surjective ((modulesStalkFunctor X x).map (C := X.Modules)
        (F.map (homOfLE (Nat.le_succ (k + 1))).op)).hom :=
      Stacks.Algebraization.surjective_stalk_coherentAdicTransition (J := I) ⟨F, hF⟩ x (k + 1)
    have hmap : Submodule.map ((modulesStalkFunctor X x).map (C := X.Modules)
          (F.map (homOfLE (Nat.le_succ (k + 1))).op)).hom
        (IdealSheafData.stalk I x • (⊤ : Submodule (X.presheaf.stalk x)
          ((modulesStalkFunctor X x).obj (F.obj (op (k + 1 + 1)))))) =
        IdealSheafData.stalk I x • (⊤ : Submodule (X.presheaf.stalk x)
          ((modulesStalkFunctor X x).obj (F.obj (op (k + 1))))) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    have hker := Stacks.Algebraization.ker_stalk_coherentAdicTransition (J := I) ⟨F, hF⟩ x (k + 1)
    rw [hcomp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.ker_comp, ih, ← hmap,
      Submodule.comap_map_eq, hker]
    exact sup_eq_left.mpr
      (Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero (k + 1))))

/-! ### The factorization at a stalk -/

/-- **The factorization identity at a stalk.** The stalk of `ι_n` applied to the image of `b`
under the stalk of the transition map is `T b`, where `T` is the germ of `t`. -/
theorem stalk_principalRaise_stalk_mapFamily (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) (x : X)
    (b : (modulesStalkFunctor X x).obj (F.obj (op (n + 1)))) :
    ((modulesStalkFunctor X x).map (C := X.Modules) (principalRaise hF t ht n)).hom
        (((modulesStalkFunctor X x).map (C := X.Modules) (mapFamily F n)).hom b) =
      (X.presheaf.Γgerm x).hom t • b := by
  have h : ((modulesStalkFunctor X x).map (C := X.Modules)
      (mapFamily F n ≫ principalRaise hF t ht n)).hom b =
      (X.presheaf.Γgerm x).hom t • b := by
    rw [map_comp_principalRaise hF t ht n]
    exact modulesStalkFunctor_map_mulSection t (F.obj (op (n + 1))) x b
  rwa [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h

/-! ### The three parts of short exactness at a stalk -/

/-- **`ι_n` is injective on stalks.** An element of `F_{n,x}` killed by `ι_n` lifts to a `b` with
`T b = 0`; finite local freeness over `𝒪_{X,x} / ℐ_x ⁿ⁺²` and the regularity of `T` put `b` in
`ℐ_x ⁿ⁺¹ F_{n+1,x}`, which is the kernel of the transition map. -/
theorem injective_stalk_principalRaise (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) (x : X)
    (hgen : IdealSheafData.stalk I x = Ideal.span {(X.presheaf.Γgerm x).hom t})
    (hreg : (X.presheaf.Γgerm x).hom t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hfree : ∃ r : ℕ, Nonempty ((modulesStalkFunctor X x).obj (F.obj (op (n + 1)))
      ≃ₗ[X.presheaf.stalk x]
        (Fin r → (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x ^ (n + 1 + 1))))) :
    Function.Injective ((modulesStalkFunctor X x).map (C := X.Modules)
      (principalRaise hF t ht n)).hom := by
  obtain ⟨r, ⟨e⟩⟩ := hfree
  have hJ : IdealSheafData.stalk I x ^ (n + 1 + 1) =
      Ideal.span {(X.presheaf.Γgerm x).hom t ^ (n + 1 + 1)} := by
    rw [hgen, Ideal.span_singleton_pow]
  have hsurj : Function.Surjective ((modulesStalkFunctor X x).map (C := X.Modules)
      (mapFamily F n)).hom :=
    Stacks.Algebraization.surjective_stalk_coherentAdicTransition (J := I) ⟨F, hF⟩ x n
  have hker := Stacks.Algebraization.ker_stalk_coherentAdicTransition (J := I) ⟨F, hF⟩ x n
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a hzero
  obtain ⟨b, rfl⟩ := hsurj a
  have hTb : (X.presheaf.Γgerm x).hom t • b = 0 := by
    rw [← stalk_principalRaise_stalk_mapFamily hF t ht n x b]
    exact hzero
  obtain ⟨y, hy⟩ :=
    Stacks.AdicTorsion.exists_eq_pow_smul_of_smul_eq_zero_of_linearEquiv hreg (n + 1) r hJ e hTb
  have hmem : b ∈ IdealSheafData.stalk I x ^ (n + 1) •
      (⊤ : Submodule (X.presheaf.stalk x)
        ((modulesStalkFunctor X x).obj (F.obj (op (n + 1))))) := by
    rw [hy]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [hgen, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  exact LinearMap.mem_ker.mp (hker.ge hmem)

/-- **Exactness in the middle, at a stalk.** The kernel of the iterated transition
`F_{n+1,x} ⟶ F_{1,x}` is `ℐ_x F_{n+1,x} = T F_{n+1,x}`, and every `T b` is the image under
`ι_n` of the class of `b`. -/
theorem ker_stalk_proj_le_range_stalk_principalRaise (hF : IsCoherentAdicSystem I F)
    (t : Γ(X, ⊤)) (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V) (n : ℕ) (x : X)
    (hgen : IdealSheafData.stalk I x = Ideal.span {(X.presheaf.Γgerm x).hom t}) :
    LinearMap.ker ((modulesStalkFunctor X x).map (C := X.Modules)
        (proj (objFamily F) (mapFamily F) (n + 1))).hom ≤
      LinearMap.range ((modulesStalkFunctor X x).map (C := X.Modules)
        (principalRaise hF t ht n)).hom := by
  rw [proj_eq_map, ker_stalk_map_zero hF x n, hgen]
  refine Submodule.smul_le.mpr fun c hc z _ => ?_
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  refine ⟨((modulesStalkFunctor X x).map (C := X.Modules) (mapFamily F n)).hom (w • z), ?_⟩
  rw [stalk_principalRaise_stalk_mapFamily hF t ht n x (w • z), smul_smul, mul_comm]

/-! ### Short exactness -/

/-- **The sequence `0 → F_n → F_{n+1} → F_1 → 0` is short exact.**

Let `(F_m)` be a coherent adic system along `ℐ` on a scheme `X` and let `t` be a global section
of `𝒪_X` lying in `ℐ` on every affine open. Assume that at every point `x` the stalk `ℐ_x` is
generated by the germ `T` of `t`, that `T` is a nonzerodivisor of `𝒪_{X,x}`, and that every
`F_{m,x}` is a finite free `𝒪_{X,x} / ℐ_x ᵐ⁺¹`-module — the stalkwise content of finite local
freeness of `F_m` over `𝒪_X / ℐ ᵐ⁺¹`. Then the sequence built from the canonical
`ι_n : F_n ⟶ F_{n+1}` of `Stacks.Coherent.IsCoherentAdicSystem.principalRaise` and the iterated
transition `F_{n+1} ⟶ F_1` is short exact.

This is the step left open by the reduction of
`Stacks.Coherent.IsCoherentAdicSystem.condition1_of_shortExact`, and it is the place where the
two hypotheses of [Stacks, Tag 0DXW] on `t` and on `F_m` are used. -/
theorem shortExact_principalShortComplex (hF : IsCoherentAdicSystem I F) (t : Γ(X, ⊤))
    (ht : ∀ V : X.affineOpens, restrictTop t V.1 ∈ I.ideal V)
    (hgen : ∀ x : X, IdealSheafData.stalk I x = Ideal.span {(X.presheaf.Γgerm x).hom t})
    (hreg : ∀ x : X, (X.presheaf.Γgerm x).hom t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (hfree : ∀ (m : ℕ) (x : X), ∃ r : ℕ,
      Nonempty ((modulesStalkFunctor X x).obj (F.obj (op m)) ≃ₗ[X.presheaf.stalk x]
        (Fin r → (X.presheaf.stalk x ⧸ IdealSheafData.stalk I x ^ (m + 1)))))
    (n : ℕ) :
    (ShortComplex.mk (principalRaise hF t ht n) (proj (objFamily F) (mapFamily F) (n + 1))
      (principalRaise_comp_proj hF t ht n)).ShortExact := by
  refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact
    (O := X.ringCatSheaf) _).2 fun x => ?_
  have hinj := injective_stalk_principalRaise hF t ht n x (hgen x) (hreg x) (hfree (n + 1) x)
  have hexact := ker_stalk_proj_le_range_stalk_principalRaise hF t ht n x (hgen x)
  have hepi : Epi (proj (objFamily F) (mapFamily F) (n + 1)) := by
    rw [proj_eq_map]
    exact hF.epi_map (Nat.zero_le (n + 1))
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hinj)
    (Functor.map_epi (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x)
      (proj (objFamily F) (mapFamily F) (n + 1)))
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 hexact

end IsCoherentAdicSystem

end Stacks.Coherent

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- **When `I = (f)` the stalk of `I 𝒪_U` at a point of `U` is generated by the germ of `f`.**
The stalk is the image of `I` under `A → Γ(U, 𝒪_U) → 𝒪_{U,x}`
(`Stacks.Algebraization.stalk_idealOnOpen_eq_map_scalarMap`), and the image of a principal ideal
is principal on the image of its generator. -/
theorem stalk_idealOnOpen_eq_span_germOfBase {f : S.A} (hI : S.I = Ideal.span {f})
    (x : S.U.toScheme) :
    IdealSheafData.stalk (idealOnOpen S) x = Ideal.span {germOfBase S x f} := by
  rw [stalk_idealOnOpen_eq_map_scalarMap S x, hI, Ideal.map_span, Set.image_singleton]
  rfl

/-- **The sequences `0 → F_n → F_{n+1} → F_1 → 0` of [Stacks, Tag 0DXW] are short exact.** Here
`I = (f)` is principal, the germ of `f` is a nonzerodivisor in every local ring of `U`, and every
term of the system is finite free over the infinitesimal neighbourhood at every stalk — the
stalkwise content of hypotheses (1) and (2) of the source. The local rings of `U` are
localizations of `A`, so the condition on the germs holds whenever `f` is a nonzerodivisor
of `A`. -/
theorem shortExact_principalShortComplex {f : S.A} (hf : f ∈ S.I)
    (hI : S.I = Ideal.span {f})
    (hreg : ∀ x : S.U.toScheme,
      germOfBase S x f ∈ nonZeroDivisors (S.U.toScheme.presheaf.stalk x))
    (hfree : ∀ (m : ℕ) (x : S.U.toScheme), ∃ r : ℕ,
      Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme x).obj (systemObj S F m)
        ≃ₗ[S.U.toScheme.presheaf.stalk x]
        (Fin r → (S.U.toScheme.presheaf.stalk x ⧸
          IdealSheafData.stalk (idealOnOpen S) x ^ (m + 1)))))
    (n : ℕ) :
    (principalShortComplex S F hf n).ShortExact :=
  Stacks.Coherent.IsCoherentAdicSystem.shortExact_principalShortComplex F.property
    (scalarMap S f) (restrictTop_scalarMap_mem_idealOnOpen S hf)
    (stalk_idealOnOpen_eq_span_germOfBase S hI) hreg hfree n

/-- **The hypothesis of [Stacks, Tag 0DXW] from the hypotheses of the source.** With `I = (f)`
principal, the germ of `f` a nonzerodivisor in every local ring of `U`, and every `F_n` finite
free over `𝒪_U / I ⁿ⁺¹ 𝒪_U` at every stalk, condition (1) of [Stacks, Tag 0H39] holds for
multiplication by `f`.

This is the conjunction of
`Stacks.Algebraization.hasPrincipalShortExactSequences_of_shortExact` with the short exactness
proved above, and it is what
`Stacks.Algebraization.canonicallyExtends_of_principal_shortExactSequences` consumes. -/
theorem hasPrincipalShortExactSequences_of_principal {f : S.A} (hI : S.I = Ideal.span {f})
    (hreg : ∀ x : S.U.toScheme,
      germOfBase S x f ∈ nonZeroDivisors (S.U.toScheme.presheaf.stalk x))
    (hfree : ∀ (m : ℕ) (x : S.U.toScheme), ∃ r : ℕ,
      Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme x).obj (systemObj S F m)
        ≃ₗ[S.U.toScheme.presheaf.stalk x]
        (Fin r → (S.U.toScheme.presheaf.stalk x ⧸
          IdealSheafData.stalk (idealOnOpen S) x ^ (m + 1))))) :
    HasPrincipalShortExactSequences S F f :=
  have hf : f ∈ S.I := hI ▸ Ideal.mem_span_singleton_self f
  hasPrincipalShortExactSequences_of_shortExact S F hf
    fun n => shortExact_principalShortComplex S F hf hI hreg hfree n

end Stacks.Algebraization

end
