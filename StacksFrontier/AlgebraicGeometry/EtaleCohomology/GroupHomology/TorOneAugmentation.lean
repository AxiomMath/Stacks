module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.AugmentationIdealSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CoinvariantsAdjunction
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# `Tor₁` of the trivial module is `I / I²`

Let `Λ` be a ring and `G` a topological group, with completed group algebra `R = Λ[[G]]`,
augmentation `ε : R → Λ` and augmentation ideal `I = ker ε`. The `Tor` of the library is the left
derived functor of the coinvariants `N ↦ Λ ⊗_R N = N / I N` (`coinvariantsFunctor`). This file
computes it in degree one at a module `N` with a surjection `p : R → N` of kernel `I`, for instance
the trivial module `Λ`:

`Tor₁^R(N, Λ) ≅ I / I N|_I = I / I²`.

The proof is the long exact sequence of `0 → I → R → N → 0`: `Tor₁^R(R, Λ) = 0` since `R` is free,
and the map `I / I·I → R / I R` is zero, since `I R = I`. So the connecting map
`Tor₁^R(N, Λ) → Tor₀^R(I, Λ) = I / I·I` is an isomorphism. The submodule `I·I` of `I` spanned by the
products `a x`, `a, x ∈ I`, is the square `I²` of `augmentationIdealSq`
(`mem_augmentationSubmodule_augmentationIdealModule_iff`), so the quotient is the one studied in
`AugmentationIdealSquare.lean`.

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `augmentationIdealModule Λ G`: the augmentation ideal `I` as a `Λ[[G]]`-module.
* `augmentationShortComplex p`: the short exact sequence `0 → I → R → N → 0`.
* `torOneIso p`: `Tor₁^R(N, Λ) ≅ I / I·I`, the connecting map of its long exact sequence.
* `torOneMk p`: the surjection `I → Tor₁^R(N, Λ)`.
* `torOneAddEquiv p`: `I / I² ≃ Tor₁^R(N, Λ)`.

## Main results

* `mem_augmentationSubmodule_augmentationIdealModule_iff`: `I·I = I²`.
* `torOneMk_eq_zero_iff`: the kernel of `I → Tor₁^R(N, Λ)` is `I²`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

variable (Λ : Type u) [Ring Λ] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The augmentation ideal** `I = ker (Λ[[G]] → Λ)`, as a `Λ[[G]]`-module. -/
abbrev augmentationIdealModule : ModuleCat.{u} (CompletedGroupAlgebra Λ G) :=
  ModuleCat.of _ (RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ))

variable {Λ G}

/-- **`I · I = I²`.** An element of the augmentation ideal `I` lies in the submodule `I · I` of `I`
spanned by the products `a x` with `a, x ∈ I` exactly when it lies in the square
`augmentationIdealSq` of `I`. -/
theorem mem_augmentationSubmodule_augmentationIdealModule_iff
    (x : augmentationIdealModule Λ G) :
    x ∈ augmentationSubmodule Λ G (augmentationIdealModule Λ G) ↔
      (x : CompletedGroupAlgebra Λ G) ∈ augmentationIdealSq Λ G := by
  constructor
  · intro hx
    rw [augmentationSubmodule] at hx
    refine Submodule.span_induction
      (p := fun (y : augmentationIdealModule Λ G) _ => y.1 ∈ augmentationIdealSq Λ G) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, n, rfl⟩
      rw [augmentationIdealSq, pow_two]
      exact Submodule.mul_mem_mul (show a ∈ RingHom.ker _ from ha) n.2
    · exact zero_mem _
    · intro y z _ _ hy hz
      exact add_mem hy hz
    · intro r y _ hy
      change r * (y : CompletedGroupAlgebra Λ G) ∈ _
      rw [augmentationIdealSq, pow_two] at hy ⊢
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun _ _ h₁ h₂ => ?_
      · rw [← mul_assoc]
        exact Submodule.mul_mem_mul (Ideal.mul_mem_left (RingHom.ker _) r ha) hb
      · rw [mul_add]
        exact add_mem h₁ h₂
  · intro hx
    obtain ⟨x, hxI⟩ := x
    have hx' := hx
    rw [augmentationIdealSq, pow_two] at hx'
    have key : ∃ h : x ∈ RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ),
        (⟨x, h⟩ : augmentationIdealModule Λ G) ∈
          augmentationSubmodule Λ G (augmentationIdealModule Λ G) := by
      refine Submodule.mul_induction_on (C := fun z => ∃ h : z ∈ RingHom.ker
          (augmentation : CompletedGroupAlgebra Λ G →+* Λ), (⟨z, h⟩ : augmentationIdealModule Λ G) ∈
            augmentationSubmodule Λ G (augmentationIdealModule Λ G)) hx'
        (fun a ha b hb => ?_) fun y z ⟨hy, hy'⟩ ⟨hz, hz'⟩ => ?_
      · refine ⟨Ideal.mul_mem_left _ a hb, ?_⟩
        have : (⟨a * b, Ideal.mul_mem_left _ a hb⟩ : augmentationIdealModule Λ G) =
            a • (⟨b, hb⟩ : augmentationIdealModule Λ G) := Subtype.ext (smul_eq_mul a b).symm
        rw [this]
        exact smul_mem_augmentationSubmodule ha _
      · refine ⟨add_mem hy hz, ?_⟩
        have : (⟨y + z, add_mem hy hz⟩ : augmentationIdealModule Λ G) =
            (⟨y, hy⟩ : augmentationIdealModule Λ G) + ⟨z, hz⟩ := Subtype.ext rfl
        rw [this]
        exact add_mem hy' hz'
    obtain ⟨_, h⟩ := key
    exact h

/-- The augmentation ideal lies in `I R`: `x = x · 1`. -/
theorem mem_augmentationSubmodule_self {x : CompletedGroupAlgebra Λ G}
    (hx : augmentation x = 0) :
    x ∈ augmentationSubmodule Λ G (CompletedGroupAlgebra Λ G) := by
  simpa using smul_mem_augmentationSubmodule hx (1 : CompletedGroupAlgebra Λ G)

variable {N : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
  (p : ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶ N)

/-- **The short complex** `0 → I → R → N → 0` of a map `p : R → N` with kernel `I`,
`R = Λ[[G]]`. -/
abbrev augmentationShortComplex
    (hker : LinearMap.ker p.hom = RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)) :
    ShortComplex (ModuleCat.{u} (CompletedGroupAlgebra Λ G)) :=
  ShortComplex.mk (ModuleCat.ofHom (RingHom.ker (augmentation :
    CompletedGroupAlgebra Λ G →+* Λ)).subtype) p (by
      ext x
      change p.hom (x : CompletedGroupAlgebra Λ G) = 0
      rw [← LinearMap.mem_ker, hker]
      exact x.2)

omit [IsTopologicalGroup G] in
/-- `0 → I → R → N → 0` is short exact, for `p` surjective with kernel `I`. -/
theorem shortExact_augmentationShortComplex (hp : Function.Surjective p.hom)
    (hker : LinearMap.ker p.hom = RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)) :
    (augmentationShortComplex p hker).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (fun y => by
      change p.hom y = 0 ↔ y ∈ Set.range (RingHom.ker _).subtype
      rw [← LinearMap.mem_ker, hker]
      exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩) Subtype.val_injective hp

variable (hp : Function.Surjective p.hom)
  (hker : LinearMap.ker p.hom = RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ))

/-- The map `I / I·I → R / I R` induced by the inclusion `I → R` is zero, as `I ⊆ I R`. -/
theorem coinvariantsFunctor_map_augmentationShortComplex_f :
    (coinvariantsFunctor Λ G).map (augmentationShortComplex p hker).f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).2 (mem_augmentationSubmodule_self (RingHom.mem_ker.1 y.2))

/-- The map `Tor₀^R(I, Λ) → Tor₀^R(R, Λ)` induced by the inclusion `I → R` is zero. -/
theorem leftDerived_zero_map_augmentationShortComplex_f :
    ((coinvariantsFunctor Λ G).leftDerived 0).map (augmentationShortComplex p hker).f = 0 := by
  rw [← cancel_mono ((coinvariantsFunctor Λ G).leftDerivedZeroIsoSelf.hom.app _), zero_comp,
    NatTrans.naturality, coinvariantsFunctor_map_augmentationShortComplex_f, comp_zero]

/-- **The connecting map `Tor₁^R(N, Λ) → Tor₀^R(I, Λ)` is an isomorphism**: `Tor₁^R(R, Λ) = 0`
since `R` is projective, and `Tor₀^R(I, Λ) → Tor₀^R(R, Λ)` is zero. -/
theorem isIso_leftDerivedδ_augmentationShortComplex :
    IsIso ((coinvariantsFunctor Λ G).leftDerivedδ
      (shortExact_augmentationShortComplex p hp hker) 0) := by
  have h₁ := (coinvariantsFunctor Λ G).leftDerived_exact_δ₁
    (shortExact_augmentationShortComplex p hp hker) 0
  have h₂ := (coinvariantsFunctor Λ G).leftDerived_exact_δ₂
    (shortExact_augmentationShortComplex p hp hker) 0
  have : Mono ((coinvariantsFunctor Λ G).leftDerivedδ
      (shortExact_augmentationShortComplex p hp hker) 0) :=
    h₁.mono_g (IsZero.eq_of_src ((coinvariantsFunctor Λ G).isZero_leftDerived_obj_projective_succ 0
      (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G))) _ _)
  have : Epi ((coinvariantsFunctor Λ G).leftDerivedδ
      (shortExact_augmentationShortComplex p hp hker) 0) :=
    h₂.epi_f (leftDerived_zero_map_augmentationShortComplex_f p hker)
  exact isIso_of_mono_of_epi _

/-- **`Tor₁^R(N, Λ) ≅ I / I·I`**, `R = Λ[[G]]`, for a surjection `p : R → N` with kernel the
augmentation ideal `I`: the connecting map of `0 → I → R → N → 0`, followed by
`Tor₀^R(I, Λ) = Λ ⊗_R I = I / I·I`. Here `Tor` is the left derived functor of the coinvariants. -/
def torOneIso :
    ((coinvariantsFunctor Λ G).leftDerived 1).obj N ≅
      (coinvariantsFunctor Λ G).obj (augmentationIdealModule Λ G) :=
  haveI := isIso_leftDerivedδ_augmentationShortComplex p hp hker
  asIso ((coinvariantsFunctor Λ G).leftDerivedδ
      (shortExact_augmentationShortComplex p hp hker) 0) ≪≫
    (coinvariantsFunctor Λ G).leftDerivedZeroIsoSelf.app _

/-- The inverse of `torOneIso`, followed by the connecting map, is the identification
`Λ ⊗_R I = Tor₀^R(I, Λ)`. -/
theorem torOneIso_inv_comp_leftDerivedδ :
    (torOneIso p hp hker).inv ≫
        (coinvariantsFunctor Λ G).leftDerivedδ (shortExact_augmentationShortComplex p hp hker) 0 =
      (coinvariantsFunctor Λ G).leftDerivedZeroIsoSelf.inv.app _ := by
  have := isIso_leftDerivedδ_augmentationShortComplex p hp hker
  simp [torOneIso]

/-- The connecting map sends `torOneMk x` (below) to the class of `x` in `Tor₀^R(I, Λ)`. -/
theorem leftDerivedδ_torOneIso_inv_apply (x : (coinvariantsFunctor Λ G).obj
    (augmentationIdealModule Λ G)) :
    ((coinvariantsFunctor Λ G).leftDerivedδ (shortExact_augmentationShortComplex p hp hker) 0).hom
        ((torOneIso p hp hker).inv.hom x) =
      ((coinvariantsFunctor Λ G).leftDerivedZeroIsoSelf.inv.app _).hom x := by
  rw [← torOneIso_inv_comp_leftDerivedδ p hp hker]
  rfl

/-- **The surjection `I → Tor₁^R(N, Λ)`**: the class of `x` in `I / I·I`, read through
`torOneIso`. -/
def torOneMk : augmentationIdealModule Λ G →+ ((coinvariantsFunctor Λ G).leftDerived 1).obj N where
  toFun x := (torOneIso p hp hker).toLinearEquiv.symm (coinvariantsMk Λ G x)
  map_zero' := by rw [show coinvariantsMk Λ G (0 : augmentationIdealModule Λ G) = 0 from rfl,
    map_zero]
  map_add' x y := by rw [coinvariantsMk_add, map_add]

/-- `I → Tor₁^R(N, Λ)` is surjective. -/
theorem torOneMk_surjective : Function.Surjective (torOneMk p hp hker) := fun z => by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ ((torOneIso p hp hker).toLinearEquiv z)
  exact ⟨y, by
    change (torOneIso p hp hker).toLinearEquiv.symm (Submodule.Quotient.mk y) = z
    rw [hy, LinearEquiv.symm_apply_apply]⟩

/-- **The kernel of `I → Tor₁^R(N, Λ)` is `I²`.** -/
theorem torOneMk_eq_zero_iff (x : augmentationIdealModule Λ G) :
    torOneMk p hp hker x = 0 ↔ (x : CompletedGroupAlgebra Λ G) ∈ augmentationIdealSq Λ G := by
  rw [← mem_augmentationSubmodule_augmentationIdealModule_iff]
  exact (LinearEquiv.map_eq_zero_iff _).trans (Submodule.Quotient.mk_eq_zero _)

/-- The kernel of `I → Tor₁^R(N, Λ)`, as an additive subgroup of `I`, is `I² ∩ I`. -/
theorem ker_torOneMk :
    (torOneMk p hp hker).ker = (augmentationIdealSq Λ G).toAddSubgroup.comap
      (RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).subtype.toAddMonoidHom :=
  AddSubgroup.ext fun x => (AddMonoidHom.mem_ker).trans (torOneMk_eq_zero_iff p hp hker x)

/-- **`I / I² ≃ Tor₁^R(N, Λ)`**, `R = Λ[[G]]`, for a surjection `p : R → N` with kernel the
augmentation ideal `I`, as additive groups; `I²` is `augmentationIdealSq`. -/
def torOneAddEquiv :
    augmentationIdealModule Λ G ⧸ (augmentationIdealSq Λ G).toAddSubgroup.comap
        (RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).subtype.toAddMonoidHom ≃+
      ((coinvariantsFunctor Λ G).leftDerived 1).obj N :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_torOneMk p hp hker).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (torOneMk_surjective p hp hker))

/-- `I / I² ≃ Tor₁^R(N, Λ)` sends the class of `x` to `torOneMk x`. -/
theorem torOneAddEquiv_mk (x : augmentationIdealModule Λ G) :
    torOneAddEquiv p hp hker (QuotientAddGroup.mk x) = torOneMk p hp hker x :=
  rfl

/-- `torOneMk` depends only on the map `p`. -/
theorem torOneMk_congr
    {p' : ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶ N} (h : p = p')
    (hp' : Function.Surjective p'.hom)
    (hker' : LinearMap.ker p'.hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)) :
    torOneMk p hp hker = torOneMk p' hp' hker' := by
  subst h
  rfl

/-- The map of short exact sequences `(I → R → N) ⟶ (I → R → N')` induced by `u : N ⟶ N'` with
`p ≫ u = p'`. -/
def augmentationShortComplexMap {N' : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    {p' : ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶ N'}
    (hker' : LinearMap.ker p'.hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ))
    (u : N ⟶ N') (hu : p ≫ u = p') :
    augmentationShortComplex p hker ⟶ augmentationShortComplex p' hker' where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := u
  comm₂₃ := by
    change 𝟙 _ ≫ p' = p ≫ u
    rw [Category.id_comp, hu]

/-- **`Tor₁^R(N, Λ) ≅ I / I²` is natural in `N`**: for `u : N ⟶ N'` with `p ≫ u = p'`, the induced
map on `Tor₁` sends `torOneMk p x` to `torOneMk p' x`. -/
theorem leftDerived_map_torOneMk {N' : ModuleCat.{u} (CompletedGroupAlgebra Λ G)}
    {p' : ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶ N'}
    (hp' : Function.Surjective p'.hom)
    (hker' : LinearMap.ker p'.hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ))
    (u : N ⟶ N') (hu : p ≫ u = p') (x : augmentationIdealModule Λ G) :
    (((coinvariantsFunctor Λ G).leftDerived 1).map u).hom (torOneMk p hp hker x) =
      torOneMk p' hp' hker' x := by
  have nat := (coinvariantsFunctor Λ G).leftDerivedδ_naturality
    (shortExact_augmentationShortComplex p hp hker)
    (shortExact_augmentationShortComplex p' hp' hker')
    (augmentationShortComplexMap p hker hker' u hu) 0
  have := isIso_leftDerivedδ_augmentationShortComplex p' hp' hker'
  have hinj := (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono
    ((coinvariantsFunctor Λ G).leftDerivedδ (shortExact_augmentationShortComplex p' hp' hker') 0))
  refine hinj ?_
  refine (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom nat) (torOneMk p hp hker x)).trans ?_
  refine (congrArg (((coinvariantsFunctor Λ G).leftDerived 0).map (𝟙 _)).hom
    (leftDerivedδ_torOneIso_inv_apply p hp hker (coinvariantsMk Λ G x))).trans ?_
  refine (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (((coinvariantsFunctor Λ G).leftDerived 0).map_id _)) _).trans ?_
  exact (leftDerivedδ_torOneIso_inv_apply p' hp' hker' (coinvariantsMk Λ G x)).symm

section Trivial

variable (Λ G)

/-- **The trivial module `Λ`** over `Λ[[G]]`, acted on through the augmentation. -/
def trivialModule : ModuleCat.{u} (CompletedGroupAlgebra Λ G) :=
  (ModuleCat.restrictScalars (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).obj
    (ModuleCat.of Λ Λ)

/-- The augmentation `Λ[[G]] → Λ`, as a map of `Λ[[G]]`-modules onto the trivial module. -/
def augmentationModuleHom :
    ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶ trivialModule Λ G :=
  ModuleCat.ofHom (Y := trivialModule Λ G)
    { toFun := fun a => show Λ from augmentation a
      map_add' := map_add augmentation
      map_smul' := fun a x => by
        change augmentation (a * x) = augmentation a * augmentation x
        exact map_mul _ _ _ }

omit [IsTopologicalGroup G] in
/-- The augmentation is surjective. -/
theorem augmentationModuleHom_surjective :
    Function.Surjective (augmentationModuleHom Λ G).hom := fun c =>
  ⟨const (show Λ from c), augmentation_const (show Λ from c)⟩

omit [IsTopologicalGroup G] in
/-- The kernel of the augmentation is the augmentation ideal. -/
theorem ker_augmentationModuleHom :
    LinearMap.ker (augmentationModuleHom Λ G).hom =
      RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ) :=
  Submodule.ext fun _ => Iff.rfl

/-- **`Tor₁^{Λ[[G]]}(Λ, Λ) ≅ I / I²`**, for the trivial module `Λ`, any ring `Λ` and any topological
group `G`, with `Tor` the left derived functor of the coinvariants `coinvariantsFunctor` and `I²`
the square `augmentationIdealSq` of the augmentation ideal `I`. -/
def torOneTrivialAddEquiv :
    augmentationIdealModule Λ G ⧸ (augmentationIdealSq Λ G).toAddSubgroup.comap
        (RingHom.ker (augmentation : CompletedGroupAlgebra Λ G →+* Λ)).subtype.toAddMonoidHom ≃+
      ((coinvariantsFunctor Λ G).leftDerived 1).obj (trivialModule Λ G) :=
  torOneAddEquiv (augmentationModuleHom Λ G) (augmentationModuleHom_surjective Λ G)
    (ker_augmentationModuleHom Λ G)

end Trivial

end Stacks.GroupHomology

end
