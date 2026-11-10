module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtensionBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineToolbox
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.LimitQuotientComparison
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.CategoryTheory.Limits.ProObject.Stages
public import StacksFrontier.RingTheory.AdicCompletion.LadderStableImage
public import StacksFrontier.Topology.Algebra.AdicLimitTopology

/-!
# Mittag-Leffler and the completed module for a canonically extending system

In the algebraization situation of a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with
`X = Spec(A)` and `U = X ∖ V(𝔞)`, let `(ℱₙ)` be a coherent `I`-adic system on `U` which
canonically extends to `X`. This file proves parts (3) and (4) of [Stacks, Tag 0EIR]: the
inverse system `{H⁰(U, ℱₙ)}` satisfies the Mittag-Leffler condition, and the module
`M = limₙ H⁰(U, ℱₙ)` is finite over the `I`-adic completion of `A` with its limit topology equal
to its `I`-adic topology.

## Main results

* `Stacks.Algebraization.hasProLadder_of_proIso` — a coherent adic system on `X` pro-isomorphic
  to the sheaves associated to the global sections of `(ℱₙ)` has its own global sections linked to
  `{H⁰(U, ℱₙ)}` by an elementary ladder of maps.
* `Stacks.Algebraization.hasProLadder_of_canonicallyExtends` — a canonically extending system
  has a coherent adic extension `(𝒢ₙ)` on `X` whose global sections are linked to
  `{H⁰(U, ℱₙ)}` by an elementary ladder of maps.
* `Stacks.Algebraization.isMittagLefflerCategorical_of_canonicallyExtends` — **part (3) of
  Tag 0EIR.**
* `Stacks.Algebraization.limitTopologyAgrees_of_canonicallyExtends` — the second half of
  **part (4)**: the limit topology on `M` is the `I`-adic topology.
* `Stacks.Algebraization.isAdicComplete_and_finite_adicCompletion_of_canonicallyExtends` — the
  first half of **part (4)**: `M` is `I`-adically complete, so it is its own `I`-adic
  completion, and that completion is finite over the `I`-adic completion of `A`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: term `n` is the source's `ℱ_{n+1}`.

The source reads the conclusions off the pro-isomorphism of Definition 0EIP: the system
`{H⁰(U, ℱₙ)}` is pro-isomorphic to `{Mₙ}` with `Mₙ = M_{n+1}/IⁿM_{n+1}` a tower of finite
modules, and then Mittag-Leffler and the properties of `M` follow because the transitions of
`{Mₙ}` are surjective. The pro-isomorphism lives in an ind-category of quasi-coherent modules,
so its elementary content has to be extracted: this is `Stacks.ProObject.hasProLadder`, run
through the bridge `Stacks.Coherent.nonempty_colimitYonedaIso_iff` to colimits of
representables and transported to `A`-modules along `AlgebraicGeometry.tildeEquiv` by
`Stacks.ProObject.transportIso`. What comes out are mutually inverse families of maps between
the stages, each identity holding only after passing far enough along the index, which is
exactly what a pro-isomorphism of `ℕᵒᵖ`-indexed systems says.

The extension is used only through the affine toolbox for `Coh(X, I𝒪_X)`: `(𝒢ₙ)` corresponds by
Tag 087W to a finite module `W` over the `I`-adic completion of `Γ(X, 𝒪_X)`, with surjective
projections `W → H⁰(X, 𝒢ₙ)` of kernel `Iⁿ⁺¹W`, and `W` is the inverse limit of those sections.
The two conclusions of part (4) are then transported along the isomorphism `M ≅ W` of
`A`-modules that the ladder produces, which is where Algebra Lemmas 09B8, 031D and 05GG of the
source have already been absorbed.

Finiteness over the completion is stated through the canonical identification of `M` with its
`I`-adic completion: `M` is `I`-adically complete, so `AdicCompletion.of : M ⟶ M^` is an
isomorphism of `A`-modules, and `M^` carries its canonical `AdicCompletion I A`-module
structure, for which it is finite. No module structure on `M` is chosen.

## References

* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP), canonical extension.
* [Stacks Project, Tag 0EHD](https://stacks.math.columbia.edu/tag/0EHD), the module `M`.
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-! ### The affine side of the situation -/

/-- The structural isomorphism `A ⟶ Γ(X, 𝒪_X)` of the affine scheme `X = Spec(A)`. -/
public abbrev baseScalars : S.A →+* Γ(S.X, ⊤) := (Scheme.ΓSpecIso (.of S.A)).inv.hom

/-- The ideal `I` read inside `Γ(X, 𝒪_X)`; the ideal sheaf `I𝒪_X` is the one it generates. -/
public abbrev idealGamma : Ideal Γ(S.X, ⊤) := S.I.map (baseScalars S)

/-- `Γ(X, 𝒪_X)` is Noetherian, being isomorphic to the Noetherian ring `A`. -/
public instance isNoetherianRing_gammaTop : IsNoetherianRing Γ(S.X, ⊤) :=
  isNoetherianRing_of_ringEquiv S.A
    (Scheme.ΓSpecIso (.of S.A)).commRingCatIsoToRingEquiv.symm

/-- The inverse system of global sections of a coherent adic system on `X`, as `A`-modules. -/
public abbrev extensionSections (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
  Stacks.Coherent.globalSectionsSystem G ⋙ ModuleCat.restrictScalars (baseScalars S)

/-! ### The ladder produced by a canonical extension -/

/-- **The elementary content of canonical extension, at a given extension.** If the
quasi-coherent sheaves associated to the global sections of `(ℱₙ)` are pro-isomorphic to the
coherent `I`-adic system `(𝒢ₙ)` on `X`, then the inverse system of global sections of `(𝒢ₙ)` is
linked to `{H⁰(U, ℱₙ)}` by a ladder of maps between the stages: this is the pro-isomorphism of
Definition 0EIP, read off in `A`-modules.

The extension is a parameter rather than produced, so that the ladder and anything else drawn
from the same pro-isomorphism speak about one and the same `(𝒢ₙ)`. -/
public theorem hasProLadder_of_proIso (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
    (e : Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
      (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G) :
    Stacks.ProObject.HasProLadder (globalSectionsSystem S F) (extensionSections S G) := by
  obtain ⟨hc⟩ := (Stacks.Coherent.nonempty_colimitYonedaIso_iff
    (tildeGlobalSectionsSystem S F) (Stacks.Coherent.quasicoherentDiagram G)).1 ⟨e⟩
  have ht : colimit ((tildeGlobalSectionsSystem S F ⋙
        (tildeEquiv (R := .of S.A)).inverse).op ⋙ yoneda) ≅
      colimit ((extensionSections S G).op ⋙ yoneda) :=
    Stacks.ProObject.transportIso ((tildeEquiv (R := .of S.A)).inverse).op
      (tildeGlobalSectionsSystem S F).op (Stacks.Coherent.quasicoherentDiagram G).op hc
  have eA : tildeGlobalSectionsSystem S F ⋙ (tildeEquiv (R := .of S.A)).inverse ≅
      globalSectionsSystem S F :=
    (Functor.isoWhiskerLeft (globalSectionsSystem S F)
      (tildeEquiv (R := .of S.A)).unitIso).symm
  refine Stacks.ProObject.hasProLadder (globalSectionsSystem S F) (extensionSections S G) ?_
  exact (Stacks.ProObject.colimitYonedaIsoOfNatIso eA).symm ≪≫ ht

/-- **The elementary content of canonical extension.** If `(ℱₙ)` canonically extends to `X`, then
some coherent `I`-adic system `(𝒢ₙ)` on `X` has its inverse system of global sections linked to
`{H⁰(U, ℱₙ)}` by a ladder of maps between the stages: this is the pro-isomorphism of
Definition 0EIP, read off in `A`-modules. -/
public theorem hasProLadder_of_canonicallyExtends (h : CanonicallyExtends S F) :
    ∃ G : Stacks.Coherent.CoherentAdicSystems (idealOnX S),
      Stacks.ProObject.HasProLadder (globalSectionsSystem S F) (extensionSections S G) := by
  obtain ⟨G, ⟨e⟩⟩ := h
  exact ⟨G, hasProLadder_of_proIso S F G e⟩

/-! ### Part (3): the Mittag-Leffler condition -/

/-- Surjectivity of all the transition maps of an inverse system of modules follows from
surjectivity of the one-step transitions. -/
private theorem surjective_transition_of_succ {R : Type u} [Ring R]
    {D : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (hs : ∀ n : ℕ, Function.Surjective ((D.map (homOfLE (Nat.le_succ n)).op).hom))
    {n m : ℕ} (hnm : n ≤ m) :
    Function.Surjective ((D.map (homOfLE hnm).op).hom) := by
  induction m, hnm using Nat.le_induction with
  | base =>
    have h0 : D.map (homOfLE (le_refl n)).op = 𝟙 _ := by
      simp
    rw [h0]
    exact fun y => ⟨y, rfl⟩
  | succ m hnm ih =>
    have hsplit : D.map (homOfLE (hnm.trans (Nat.le_succ m))).op =
        D.map (homOfLE (Nat.le_succ m)).op ≫ D.map (homOfLE hnm).op := by
      rw [← D.map_comp]
      exact congrArg D.map (Subsingleton.elim _ _)
    rw [hsplit]
    exact ih.comp (hs m)

/-- The transitions of the system of global sections of a coherent adic system on the affine `X`
are surjective. -/
private theorem surjective_extensionSections_transition
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) {n m : ℕ} (hnm : n ≤ m) :
    Function.Surjective (((extensionSections S G).map (homOfLE hnm).op).hom) :=
  surjective_transition_of_succ
    (fun k => Stacks.Coherent.coherentSystem_globalSectionsTransition_surjective
      S.X (idealGamma S) G k) hnm

/-- **Part (3) of Stacks Project, Tag 0EIR.** If a coherent `I`-adic system on the open
complement `U` canonically extends to `X`, then the inverse system `{H⁰(U, ℱₙ)}` of its modules
of sections satisfies the Mittag-Leffler condition. -/
@[stacks 0EIR "part (3): the inverse system of global sections of a canonically extending \
coherent adic system on the open complement satisfies Mittag-Leffler"]
public theorem isMittagLefflerCategorical_of_canonicallyExtends (h : CanonicallyExtends S F) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  obtain ⟨G, p, f, q, g, -, hcg, hfg, -⟩ := hasProLadder_of_canonicallyExtends S F h
  choose b hb₁ hb₂ hbeq using hfg
  refine isMittagLefflerCategorical_of_range_eq_submodule (globalSectionsSystem S F) b hb₂
    (fun i => LinearMap.range (g i).hom) ?_
  intro i k hbk hik
  change LinearMap.range (Stacks.ProObject.invTransition (globalSectionsSystem S F) hik).hom = _
  apply le_antisymm
  · have hsplit : Stacks.ProObject.invTransition (globalSectionsSystem S F) hik =
        Stacks.ProObject.invTransition (globalSectionsSystem S F) hbk ≫
          (Stacks.ProObject.invTransition (globalSectionsSystem S F) (hb₁ i) ≫
            f (q i) ≫ g i) := by
      rw [hbeq i, Stacks.ProObject.invTransition, Stacks.ProObject.invTransition,
        Stacks.ProObject.invTransition, ← Functor.map_comp]
      exact congrArg _ (Subsingleton.elim _ _)
    rw [hsplit]
    simp only [← Category.assoc, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  · obtain ⟨k', h₁, h₂, hk'⟩ := hcg i k hik
    have hleft : LinearMap.range (g i).hom =
        LinearMap.range
          ((Stacks.ProObject.invTransition (extensionSections S G) h₁ ≫ g i).hom) := by
      rw [ModuleCat.hom_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr (surjective_extensionSections_transition S G h₁),
        Submodule.map_top]
    rw [hleft, hk']
    simp only [← Category.assoc, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _


/-! ### Transport along the structural isomorphism `A ≅ Γ(X, 𝒪_X)`

The affine toolbox for coherent adic systems is stated over `Γ(X, 𝒪_X)`, while the algebraization
situation works over `A`. The lemmas below move the ideal-power filtration, finiteness and adic
completeness across a *surjective* ring map, which covers the structural isomorphism. -/

section Transport

variable {R T : Type u} [CommRing R] [CommRing T] {ρ : R →+* T}

/-- A member of the `J`-multiples computed over `R` is a member of the `(Jρ)`-multiples
computed over `T`: the two scalar actions agree. -/
private theorem mem_map_smul_top_of_mem_smul_top (J : Ideal R) (N : ModuleCat.{u} T)
    {x : ((ModuleCat.restrictScalars ρ).obj N : Type u)}
    (hx : x ∈ J • (⊤ : Submodule R ((ModuleCat.restrictScalars ρ).obj N))) :
    (show (N : Type u) from x) ∈ J.map ρ • (⊤ : Submodule T N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem ρ ha) Submodule.mem_top
  · exact Submodule.add_mem _ hy hz

/-- When `ρ` is surjective, conversely. -/
private theorem mem_smul_top_of_mem_map_smul_top (hρ : Function.Surjective ρ) (J : Ideal R)
    (N : ModuleCat.{u} T) {x : ((ModuleCat.restrictScalars ρ).obj N : Type u)}
    (hx : (show (N : Type u) from x) ∈ J.map ρ • (⊤ : Submodule T N)) :
    x ∈ J • (⊤ : Submodule R ((ModuleCat.restrictScalars ρ).obj N)) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
  · obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective ρ hρ).1 hr
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · exact Submodule.add_mem _ hy hz

/-- Restriction of scalars along a surjective ring map preserves finiteness. -/
private theorem finite_restrictScalars (hρ : Function.Surjective ρ) (N : ModuleCat.{u} T)
    [Module.Finite T N] : Module.Finite R ((ModuleCat.restrictScalars ρ).obj N) := by
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (inferInstance : Module.Finite T N))
  let s' : Finset ((ModuleCat.restrictScalars ρ).obj N : Type u) := s
  have key : ∀ y : ((ModuleCat.restrictScalars ρ).obj N : Type u),
      (show (N : Type u) from y) ∈ Submodule.span T (s : Set (N : Type u)) →
        y ∈ Submodule.span R (s' : Set ((ModuleCat.restrictScalars ρ).obj N : Type u)) := by
    have hsmul : ∀ (r : T) (z : (N : Type u)),
        z ∈ Submodule.span T (s : Set (N : Type u)) →
        (show ((ModuleCat.restrictScalars ρ).obj N : Type u) from z) ∈
          Submodule.span R (s' : Set ((ModuleCat.restrictScalars ρ).obj N : Type u)) →
        (show ((ModuleCat.restrictScalars ρ).obj N : Type u) from r • z) ∈
          Submodule.span R (s' : Set ((ModuleCat.restrictScalars ρ).obj N : Type u)) := by
      intro r z _ hz
      obtain ⟨a, rfl⟩ := hρ r
      exact Submodule.smul_mem _ a hz
    intro y hy
    exact Submodule.span_induction
      (p := fun z _ => (show ((ModuleCat.restrictScalars ρ).obj N : Type u) from z) ∈
        Submodule.span R (s' : Set ((ModuleCat.restrictScalars ρ).obj N : Type u)))
      (fun z hz => Submodule.subset_span hz) (Submodule.zero_mem _)
      (fun z w _ _ hz hw => Submodule.add_mem _ hz hw) hsmul hy
  exact Module.finite_def.2 ⟨s', eq_top_iff.2 fun x _ => key x (by rw [hs]; trivial)⟩

/-- Membership in `Jᵏ • ⊤` over `R` is membership in `(Jρ)ᵏ • ⊤` over `T`. -/
private theorem mem_pow_smul_top_restrictScalars_iff (hρ : Function.Surjective ρ) (J : Ideal R)
    (N : ModuleCat.{u} T) (k : ℕ) (x : ((ModuleCat.restrictScalars ρ).obj N : Type u)) :
    x ∈ J ^ k • (⊤ : Submodule R ((ModuleCat.restrictScalars ρ).obj N)) ↔
      (show (N : Type u) from x) ∈ (J.map ρ) ^ k • (⊤ : Submodule T N) := by
  rw [← Ideal.map_pow]
  exact ⟨fun hx => mem_map_smul_top_of_mem_smul_top _ N hx,
    fun hx => mem_smul_top_of_mem_map_smul_top hρ _ N hx⟩

/-- A map of `T`-modules whose kernel is `(Jρ)ᵏ • ⊤` has kernel `Jᵏ • ⊤` over `R`. -/
private theorem ker_restrictScalars_eq_smul_top (hρ : Function.Surjective ρ) (J : Ideal R)
    (k : ℕ) {N N' : ModuleCat.{u} T} (f : N ⟶ N')
    (hf : LinearMap.ker f.hom = (J.map ρ) ^ k • (⊤ : Submodule T N)) :
    LinearMap.ker ((ModuleCat.restrictScalars ρ).map f).hom =
      J ^ k • (⊤ : Submodule R ((ModuleCat.restrictScalars ρ).obj N)) := by
  ext x
  rw [mem_pow_smul_top_restrictScalars_iff hρ J N k x, ← hf]
  rfl

/-- Restriction of scalars along a surjective ring map preserves adic completeness. -/
private theorem isAdicComplete_restrictScalars (hρ : Function.Surjective ρ) (J : Ideal R)
    (N : ModuleCat.{u} T) (h : IsAdicComplete (J.map ρ) N) :
    IsAdicComplete J ((ModuleCat.restrictScalars ρ).obj N) := by
  have hmem := mem_pow_smul_top_restrictScalars_iff hρ J N
  refine { toIsHausdorff := ⟨fun x hx => h.haus x fun k => ?_⟩,
           toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · exact SModEq.zero.2 ((hmem k x).1 (SModEq.zero.1 (hx k)))
  · obtain ⟨y, hy⟩ := h.prec' f fun {m k} hmk =>
      SModEq.sub_mem.2 ((hmem m _).1 (SModEq.sub_mem.1 (hf hmk)))
    exact ⟨y, fun k => SModEq.sub_mem.2 ((hmem k _).2 (SModEq.sub_mem.1 (hy k)))⟩

/-- A linear equivalence pulls `J • ⊤` back to `J • ⊤`. -/
private theorem comap_smul_top_linearEquiv {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (J : Ideal R) :
    Submodule.comap (e : M →ₗ[R] N) (J • (⊤ : Submodule R N)) = J • (⊤ : Submodule R M) := by
  rw [Submodule.comap_smul_top_of_surjective J _ e.surjective, LinearEquiv.ker, sup_bot_eq]

/-- Adic completeness transports along an isomorphism of modules. -/
private theorem isAdicComplete_of_linearEquiv {J : Ideal R} {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (h : IsAdicComplete J N) : IsAdicComplete J M := by
  have hmem : ∀ (k : ℕ) (x : M), x ∈ J ^ k • (⊤ : Submodule R M) ↔
      e x ∈ J ^ k • (⊤ : Submodule R N) := fun k x => by
    rw [← comap_smul_top_linearEquiv e, Submodule.mem_comap]
    rfl
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine e.injective ?_
    rw [map_zero]
    refine h.haus (e x) fun k => ?_
    rw [SModEq.zero]
    exact (hmem k x).1 (SModEq.zero.1 (hx k))
  · obtain ⟨y, hy⟩ := h.prec' (fun k => e (f k)) fun {m k} hmk => by
      rw [SModEq.sub_mem, ← map_sub]
      exact (hmem m _).1 (SModEq.sub_mem.1 (hf hmk))
    refine ⟨e.symm y, fun k => ?_⟩
    rw [SModEq.sub_mem]
    refine (hmem k _).2 ?_
    rw [map_sub, e.apply_symm_apply]
    exact SModEq.sub_mem.1 (hy k)

end Transport

/-! ### Part (4): the module `M` -/

/-- **A ladder computes the limit.** A ladder between inverse systems of modules induces an
isomorphism from the limit of the first onto the vertex of a limit cone on the second, and each
projection of the second system is then dominated by one of the projections of the first. -/
private theorem exists_limitIso_of_hasProLadder
    {R : Type u} [CommRing R] {A B : ℕᵒᵖ ⥤ ModuleCat.{u} R} [HasLimit A]
    (D : Cone B) (hD : IsLimit D) (hl : Stacks.ProObject.HasProLadder A B) :
    ∃ e : limit A ≅ D.pt, ∀ n : ℕ, ∃ k : ℕ,
      LinearMap.ker (limit.π A (op k)).hom ≤
        LinearMap.ker ((e.hom ≫ D.π.app (op n)).hom) :=
  Stacks.ProObject.exists_limitIso_of_hasProLadder D hD hl


/-! ### The extension read as a limit of `A`-modules -/

/-- Restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` preserves limits, so the inverse limit of the
global sections of a coherent adic system on `X` — by Tag 087W the finite module over the
`I`-adic completion of `Γ(X, 𝒪_X)` that the system corresponds to — is a limit in `A`-modules
too. -/
private def extensionLimitCone (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    Cone (extensionSections S G) :=
  (ModuleCat.restrictScalars (baseScalars S)).mapCone
    (limit.cone (Stacks.Coherent.globalSectionsSystem G))

private def isLimit_extensionLimitCone
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    IsLimit (extensionLimitCone S G) :=
  isLimitOfPreserves _ (limit.isLimit _)

/-- `A ⟶ Γ(X, 𝒪_X)` is surjective, being half of an isomorphism. -/
private theorem surjective_baseScalars : Function.Surjective (baseScalars S) :=
  (Scheme.ΓSpecIso (.of S.A)).commRingCatIsoToRingEquiv.symm.surjective

/-- **The kernel of the `n`-th projection out of the extension's completed module** is the
`(n+1)`-st power of `I` times it, read over `A`. -/
private theorem ker_extensionLimitCone_π
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) (n : ℕ) :
    LinearMap.ker ((extensionLimitCone S G).π.app (op n)).hom =
      S.I ^ (n + 1) • (⊤ : Submodule S.A (extensionLimitCone S G).pt) := by
  exact ker_restrictScalars_eq_smul_top (surjective_baseScalars S) S.I (n + 1) _
    (Stacks.Coherent.coherentSystem_limitProjection_ker S.X (idealGamma S) G n)

/-! ### Part (4) -/

/-- Every term of the system of global sections of a coherent adic system on the affine `X` is a
finite `A`-module. -/
private theorem finite_extensionSections_aux
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) (j : ℕ) :
    Module.Finite S.A ((extensionSections S G).obj (op j)) := by
  have hcoh : (G.obj.obj (op j)).IsCoherent := G.property.1 j
  have : Module.Finite Γ(S.X, ⊤) ((Stacks.Coherent.globalSectionsSystem G).obj (op j)) :=
    Stacks.Coherent.coherentAdicTerm_finiteSections S.X (G.obj.obj (op j))
  exact finite_restrictScalars (surjective_baseScalars S) _

/-- **The three module-theoretic consequences of canonical extension.** Every `I`-adic
neighbourhood of `0` in `M = limₙ H⁰(U, ℱₙ)` contains the kernel of a projection; `M` is
`I`-adically complete; and `M/IM` is a finite `A`-module. -/
private theorem limitGlobalSections_properties (h : CanonicallyExtends S F) :
    (∀ n : ℕ, ∃ k : ℕ,
        LinearMap.ker (limit.π (globalSectionsSystem S F) (op k)).hom ≤
          S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F))) ∧
      IsAdicComplete S.I (limitGlobalSections S F) ∧
      Module.Finite S.A ((limitGlobalSections S F : Type u) ⧸
        S.I • (⊤ : Submodule S.A (limitGlobalSections S F))) := by
  obtain ⟨G, hl⟩ := hasProLadder_of_canonicallyExtends S F h
  obtain ⟨e, hker⟩ := exists_limitIso_of_hasProLadder (extensionLimitCone S G)
    (isLimit_extensionLimitCone S G) hl
  have hcomap : ∀ J : Ideal S.A,
      Submodule.comap e.hom.hom (J • (⊤ : Submodule S.A (extensionLimitCone S G).pt)) =
        J • (⊤ : Submodule S.A (limitGlobalSections S F)) := by
    intro J
    exact comap_smul_top_linearEquiv e.toLinearEquiv J
  have hkerComp : ∀ n : ℕ,
      LinearMap.ker ((e.hom ≫ (extensionLimitCone S G).π.app (op n)).hom) =
        S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F)) := by
    intro n
    rw [ModuleCat.hom_comp, LinearMap.ker_comp, ker_extensionLimitCone_π, hcomap]
  refine ⟨fun n => ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hker n
    exact ⟨k, by rw [← hkerComp n]; exact hk⟩
  · refine isAdicComplete_of_linearEquiv e.toLinearEquiv ?_
    exact isAdicComplete_restrictScalars (surjective_baseScalars S) S.I _
      (Stacks.Coherent.coherentSystem_globalSectionsLimit_isAdicComplete
        S.X (idealGamma S) G)
  · -- `M/IM` is the module of sections of the first term of the extension
    have hsurj : Function.Surjective ((e.hom ≫
        (extensionLimitCone S G).π.app (op 0)).hom) := by
      intro y
      obtain ⟨z, hz⟩ := Stacks.Coherent.coherentSystem_limitProjection_surjective
        S.X (idealGamma S) G 0 y
      obtain ⟨w, hw⟩ := e.toLinearEquiv.surjective
        (show (((extensionLimitCone S G).pt) : Type u) from z)
      refine ⟨w, ?_⟩
      change ((extensionLimitCone S G).π.app (op 0)).hom (e.hom.hom w) = y
      rw [show e.hom.hom w = z from hw]
      exact hz
    have hfinB := finite_extensionSections_aux S G 0
    have heq : S.I • (⊤ : Submodule S.A (limitGlobalSections S F)) =
        LinearMap.ker ((e.hom ≫ (extensionLimitCone S G).π.app (op 0)).hom) := by
      rw [hkerComp 0, pow_one]
    exact Module.Finite.equiv
      ((Submodule.quotEquivOfEq _ _ heq).trans
        (LinearMap.quotKerEquivOfSurjective _ hsurj)).symm

/-- **Part (4) of Stacks Project, Tag 0EIR, second half.** The limit topology on
`M = limₙ H⁰(U, ℱₙ)` is the `I`-adic topology. -/
@[stacks 0EIR "part (4), the equality of topologies: the limit topology on M is the I-adic \
topology, for a canonically extending coherent adic system on the open complement"]
public theorem limitTopologyAgrees_of_canonicallyExtends (h : CanonicallyExtends S F) :
    LimitTopologyAgrees S F := by
  obtain ⟨hker, -, -⟩ := limitGlobalSections_properties S F h
  refine Stacks.AdicLimit.iInf_induced_eq_adicModuleTopology S.I
    (fun n => (limit.π (globalSectionsSystem S F) (op n)).hom) ?_ ?_ ?_
  · intro i j hij x hx
    have hw := limit.w (globalSectionsSystem S F) (homOfLE hij).op
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hw, ModuleCat.hom_comp]
    simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero]
  · exact fun n => ⟨n + 1, limitProjection_kills_idealPower S F n⟩
  · intro k
    match k with
    | 0 => exact ⟨0, by simp⟩
    | (n + 1) => exact hker n

/-- **Part (4) of Stacks Project, Tag 0EIR, first half.** The module `M = limₙ H⁰(U, ℱₙ)` is
finite over the `I`-adic completion `Â` of `A`: it is `I`-adically complete, so the canonical map
`M ⟶ M^ = limₙ M/IⁿM` (`AdicCompletion.of`) is an isomorphism of `A`-modules, and its completion
`M^`, with its canonical structure of `Â`-module, is a finite `Â`-module. -/
@[stacks 0EIR "part (4), finiteness: M is finite over the I-adic completion of A, for a \
canonically extending coherent adic system on the open complement"]
public theorem isAdicComplete_and_finite_adicCompletion_of_canonicallyExtends
    (h : CanonicallyExtends S F) :
    IsAdicComplete S.I (limitGlobalSections S F) ∧
      Module.Finite (AdicCompletion S.I S.A)
        (AdicCompletion S.I (limitGlobalSections S F : Type u)) := by
  obtain ⟨-, hcomplete, hfin⟩ := limitGlobalSections_properties S F h
  exact ⟨hcomplete, Stacks.Coherent.finite_adicCompletion_of_finite_reduction
    S.I.fg_of_isNoetherianRing _ hfin⟩

/-! ### The extension's sections as an adic tower

The system of global sections of a coherent adic system on the affine `X` is an *adic tower* in
the sense of `Stacks.ProObject.IsAdicTower`: its transitions are surjective with kernel exactly
`I^{j+1}`. Together with the ladder of `hasProLadder_of_proIso` this is the input of the
stabilization results for the system `{H⁰(U, ℱₙ)}`. -/

/-- Every term of the system of global sections of a coherent adic system on the affine `X` is a
finite `A`-module. -/
public theorem finite_extensionSections (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
    (j : ℕ) : Module.Finite S.A ((extensionSections S G).obj (op j)) :=
  finite_extensionSections_aux S G j

/-- **The global sections of a coherent adic system on the affine `X` form an adic tower.** The
transitions are surjective and the kernel of the one-step transition at level `j` is `I^{j+1}`
times everything, read over `A` along the structural isomorphism `A ≅ Γ(X, 𝒪_X)`. -/
public theorem isAdicTower_extensionSections
    (G : Stacks.Coherent.CoherentAdicSystems (idealOnX S)) :
    Stacks.ProObject.IsAdicTower S.I (extensionSections S G) where
  surjective j := Stacks.Coherent.coherentSystem_globalSectionsTransition_surjective
    S.X (idealGamma S) G j
  ker j := ker_restrictScalars_eq_smul_top (surjective_baseScalars S) S.I (j + 1) _
    (Stacks.Coherent.coherentSystem_globalSectionsTransition_ker S.X (idealGamma S) G j)

end Stacks.Algebraization

end
