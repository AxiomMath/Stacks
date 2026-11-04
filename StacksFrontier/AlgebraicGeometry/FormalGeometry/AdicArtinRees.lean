module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf-level Artin–Rees and injectivity on formal sections

Let `X` be a quasi-compact locally Noetherian scheme, `I` a quasi-coherent ideal sheaf and
`f : M ⟶ N` a monomorphism of coherent modules. The Artin–Rees lemma, applied on each member of
a finite affine cover, produces a single `c` with `M ⊓ I ^ (n + c) N ≤ I ^ n M` for every `n`.
Consequently the induced map of inverse systems `Γ(X, M / I ⁿ M) ⟶ Γ(X, N / I ⁿ N)` is injective
on the inverse limits: a compatible family killed by it is killed at every level, because its
level `n + c` term is killed already at level `n`.

For `X = Spec(A) ∖ V(𝔞)` this is the injectivity of the left-hand vertical map of the ladder of
Stacks 0H48 on the limit side.

## Main definitions

* `Stacks.Algebraization.adicQuotientSystemMap` — the morphism of towers
  `(M / I ⁿ M) ⟶ (N / I ⁿ N)` induced by `f : M ⟶ N`.
* `Stacks.Algebraization.formalSectionsMap` — the induced morphism of the inverse systems of
  sections `Stacks.Algebraization.formalSections`.

## Main results

* `Stacks.Algebraization.exists_artinRees_affineCover` — **sheaf-level Artin–Rees**: a uniform
  constant `c` and a finite affine cover on each member of which a section of `M` landing in
  `I ^ (n + c) N` already lies in `I ^ n M`.
* `Stacks.Algebraization.exists_forall_quotientMapOfLE_app_top_eq_zero` — a global section of
  `M / I ^ (n + c) M` killed by the comparison with `N` dies already in `M / I ⁿ M`.
* `Stacks.Algebraization.injective_limMap_formalSectionsMap` and
  `Stacks.Algebraization.mono_limMap_formalSectionsMap` — the induced map
  `lim Γ(U, M / I ⁿ M) ⟶ lim Γ(U, N / I ⁿ N)` is injective.

## Implementation notes

The constant is uniform only over a chosen finite affine cover, not over every affine open: the
Artin–Rees constant of a smaller affine open is not controlled by that of a larger one without a
flat base-change argument. That suffices, because the conclusion is about sections over `⊤`, and
a section of a sheaf vanishes as soon as it vanishes on a cover.

Injectivity on sections of a monomorphism is obtained from the evaluation functor, which
preserves finite limits; `AlgebraicGeometry.Scheme.Modules` is a `def` for
`SheafOfModules X.ringCatSheaf`, so the monomorphism hypothesis is transported by hand between
the two separately declared category instances, as elsewhere in this subtree.

## References

* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
* [Stacks Project, Tag 0H48](https://stacks.math.columbia.edu/tag/0H48)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (sectionsLinearMap)

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### The tower of ideal-power quotients is functorial in the module -/

/-- The maps `M / I ⁿ M ⟶ N / I ⁿ N` induced by `f : M ⟶ N` commute with the transitions of the
two towers of ideal-power quotients. -/
theorem idealPowerQuotientMap_comp_map (I : X.IdealSheafData)
    {M N : X.Modules} (f : M ⟶ N) {m n : ℕᵒᵖ} (h : m ⟶ n) :
    (adicQuotientSystem I M).map h ≫ idealPowerQuotientMap I I n.unop n.unop le_rfl f =
      idealPowerQuotientMap I I m.unop m.unop le_rfl f ≫ (adicQuotientSystem I N).map h := by
  refine (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple I m.unop M).ι)).1 ?_
  have hM := quotientMapOfLE_π (idealPowerMultiple_antitone I M (leOfHom h.unop))
  have hN := quotientMapOfLE_π (idealPowerMultiple_antitone I N (leOfHom h.unop))
  refine Eq.trans ((Category.assoc (obj := X.Modules) _ _ _).symm.trans
    (((congrArg (fun z => z ≫ idealPowerQuotientMap I I n.unop n.unop le_rfl f) hM)).trans
      (idealPowerQuotientMap_π I I n.unop n.unop le_rfl f))) ?_
  refine Eq.trans ((congrArg (fun z => f ≫ z) hN.symm).trans
    (Category.assoc (obj := X.Modules) _ _ _).symm) ?_
  exact (congrArg (fun z => z ≫ (adicQuotientSystem I N).map h)
    (idealPowerQuotientMap_π I I m.unop m.unop le_rfl f).symm).trans
      (Category.assoc (obj := X.Modules) _ _ _)

/-- The morphism of towers `(M / I ⁿ M)ₙ ⟶ (N / I ⁿ N)ₙ` induced by `f : M ⟶ N`. -/
def adicQuotientSystemMap (I : X.IdealSheafData) {M N : X.Modules} (f : M ⟶ N) :
    adicQuotientSystem I M ⟶ adicQuotientSystem I N where
  app n := idealPowerQuotientMap I I n.unop n.unop le_rfl f
  naturality _ _ h := idealPowerQuotientMap_comp_map I f h

/-! ### Artin–Rees on an affine open -/

/-- A monomorphism of modules on a scheme is injective on the sections over every open:
evaluation at an open preserves finite limits, hence monomorphisms, and a monomorphism of
modules over a ring is an injective map. -/
theorem app_injective_of_mono {M N : X.Modules} (f : M ⟶ N) (hf : Mono (C := X.Modules) f)
    (U : X.Opens) : Function.Injective (f.app U) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  exact (ModuleCat.mono_iff_injective (T.map f)).1 (preserves_mono_of_preservesLimit T f)

/-- **Artin–Rees on an affine open.** On an affine open of a locally Noetherian scheme there is a
constant `c` such that a section of a coherent `M` whose image in a coherent `N` lies in
`I ^ (n + c) N` already lies in `I ^ n M`, for every `n`. -/
theorem exists_artinRees_affine (I : X.IdealSheafData) [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N)
    (hf : Mono (C := X.Modules) f) (W : X.affineOpens) :
    ∃ c : ℕ, ∀ (n : ℕ) (t : Γ(M, W.1)),
      f.app W.1 t ∈ (idealPowerMultiple I (n + c) N).toSubmodule.obj (op W.1) →
      t ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W.1) := by
  obtain ⟨hqM, hftM⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  obtain ⟨hqN, hftN⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent N
  have hnoeth : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  have hfinM : Module.Finite Γ(X, W.1) Γ(M, W.1) := moduleFinite_sections_on_affine M W.1 W.2
  have hfinN : Module.Finite Γ(X, W.1) Γ(N, W.1) := moduleFinite_sections_on_affine N W.1 W.2
  obtain ⟨c, hc⟩ :=
    Ideal.exists_pow_inf_eq_pow_smul (I.ideal W) (LinearMap.range (sectionsLinearMap f W.1))
  refine ⟨c, fun n t ht => ?_⟩
  rw [idealPowerMultiple_toSubmodule_obj_affine I (n + c) N W] at ht
  rw [idealPowerMultiple_toSubmodule_obj_affine I n M W]
  have hmem : sectionsLinearMap f W.1 t ∈
      (I.ideal W ^ (n + c) • (⊤ : Submodule Γ(X, W.1) Γ(N, W.1))) ⊓
        LinearMap.range (sectionsLinearMap f W.1) := ⟨ht, ⟨t, rfl⟩⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel] at hmem
  have hle2 : I.ideal W ^ n • ((I.ideal W ^ c • (⊤ : Submodule Γ(X, W.1) Γ(N, W.1))) ⊓
      LinearMap.range (sectionsLinearMap f W.1)) ≤
      I.ideal W ^ n • LinearMap.range (sectionsLinearMap f W.1) :=
    smul_mono_right _ inf_le_right
  have hmem2 : sectionsLinearMap f W.1 t ∈
      I.ideal W ^ n • LinearMap.range (sectionsLinearMap f W.1) := hle2 hmem
  rw [← Submodule.map_top (sectionsLinearMap f W.1), ← Submodule.map_smul'',
    Submodule.mem_map] at hmem2
  obtain ⟨t', ht', hφ⟩ := hmem2
  exact app_injective_of_mono f hf W.1 hφ ▸ ht'

/-- **Sheaf-level Artin–Rees.** On a quasi-compact locally Noetherian scheme there is a single
constant `c` and a finite cover by affine opens on each of which a section of the coherent `M`
whose image in the coherent `N` lies in `I ^ (n + c) N` already lies in `I ^ n M`. -/
theorem exists_artinRees_affineCover (I : X.IdealSheafData) [IsLocallyNoetherian X]
    [CompactSpace X] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N)
    (hf : Mono (C := X.Modules) f) :
    ∃ (c : ℕ) (s : Finset X.affineOpens), (∀ x : X, ∃ W ∈ s, x ∈ W.1) ∧
      ∀ W ∈ s, ∀ (n : ℕ) (t : Γ(M, W.1)),
        f.app W.1 t ∈ (idealPowerMultiple I (n + c) N).toSubmodule.obj (op W.1) →
        t ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W.1) := by
  classical
  choose cst hcst using fun W : X.affineOpens => exists_artinRees_affine I f hf W
  have hcov : (Set.univ : Set X) ⊆ ⋃ W : X.affineOpens, (W.1 : Set X) := by
    intro x _
    obtain ⟨V, hVaff, hxV, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := ⊤) (x := x) trivial
    exact Set.mem_iUnion.2 ⟨⟨V, hVaff⟩, hxV⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun W : X.affineOpens => (W.1 : Set X)) (fun W => W.1.2) hcov
  have hcover : ∀ x : X, ∃ W ∈ s, x ∈ W.1 := fun x => by simpa using hs (Set.mem_univ x)
  refine ⟨s.sup cst, s, hcover, fun W hW n t ht => ?_⟩
  have hle : cst W ≤ s.sup cst := Finset.le_sup hW
  have he : n + (s.sup cst - cst W) + cst W = n + s.sup cst := by omega
  have ht' : f.app W.1 t ∈
      (idealPowerMultiple I (n + (s.sup cst - cst W) + cst W) N).toSubmodule.obj (op W.1) := by
    rwa [he]
  exact idealPowerMultiple_antitone I M (Nat.le_add_right n (s.sup cst - cst W)) (op W.1)
    (hcst W (n + (s.sup cst - cst W)) t ht')

/-! ### Killing a compatible family of global sections -/

/-- The action on sections of a composite of morphisms of modules. -/
theorem app_comp_apply {M N P : X.Modules} (α : M ⟶ N) (β : N ⟶ P) (U : X.Opens)
    (x : Γ(M, U)) : (α ≫ β).app U x = β.app U (α.app U x) :=
  rfl

/-- On an affine open carrying the Artin–Rees bound, a section of `M / I ^ (n + c) M` whose
image in `N / I ^ (n + c) N` vanishes already vanishes in `M / I ⁿ M`. -/
theorem quotientMapOfLE_app_eq_zero_of_affine (I : X.IdealSheafData)
    {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (f : M ⟶ N) (W : X.affineOpens) {c n : ℕ}
    (hAR : ∀ t : Γ(M, W.1),
      f.app W.1 t ∈ (idealPowerMultiple I (n + c) N).toSubmodule.obj (op W.1) →
      t ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W.1))
    (sW : Γ(idealPowerQuotient I (n + c) M, W.1))
    (hsW : (idealPowerQuotientMap I I (n + c) (n + c) le_rfl f).app W.1 sW = 0) :
    (quotientMapOfLE (idealPowerMultiple_antitone I M (Nat.le_add_right n c))).app W.1 sW = 0 := by
  obtain ⟨hqM, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  obtain ⟨hqN, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent N
  obtain ⟨t, ht⟩ := surjective_app_of_epi_of_isAffineOpen
    (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + c) M).ι) W sW
  have h1 := congrArg (fun k : M ⟶ idealPowerQuotient I (n + c) N => k.app W.1 t)
    (idealPowerQuotientMap_π I I (n + c) (n + c) le_rfl f)
  rw [app_comp_apply, app_comp_apply, ht] at h1
  have h0 : (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + c) N).ι).app W.1
      (f.app W.1 t) = 0 := h1.symm.trans hsW
  have h2 : (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).app W.1 t = 0 :=
    (adicProj_app_apply_eq_zero_iff I M (op n) W.1 t).2
      (hAR t ((adicProj_app_apply_eq_zero_iff I N (op (n + c)) W.1 (f.app W.1 t)).1 h0))
  have h3 := congrArg (fun k : M ⟶ idealPowerQuotient I n M => k.app W.1 t)
    (quotientMapOfLE_π (idealPowerMultiple_antitone I M (Nat.le_add_right n c)))
  rw [app_comp_apply, ht] at h3
  exact h3.trans h2

/-- **The Artin–Rees bound on global sections.** On a quasi-compact locally Noetherian scheme
there is a `c` such that, for every `n`, a section of `M / I ^ (n + c) M` on all of `X` whose
image in `N / I ^ (n + c) N` vanishes already vanishes in `M / I ⁿ M`. -/
theorem exists_forall_quotientMapOfLE_app_top_eq_zero (I : X.IdealSheafData)
    [IsLocallyNoetherian X] [CompactSpace X] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent]
    (f : M ⟶ N) (hf : Mono (C := X.Modules) f) :
    ∃ c : ℕ, ∀ (n : ℕ) (s : Γ(idealPowerQuotient I (n + c) M, ⊤)),
      (idealPowerQuotientMap I I (n + c) (n + c) le_rfl f).app ⊤ s = 0 →
      (quotientMapOfLE (idealPowerMultiple_antitone I M (Nat.le_add_right n c))).app ⊤ s = 0 := by
  obtain ⟨c, cover, hcover, hAR⟩ := exists_artinRees_affineCover I f hf
  refine ⟨c, fun n z hz => ?_⟩
  refine TopCat.Presheaf.section_ext
    (⟨(idealPowerQuotient I n M).presheaf, (idealPowerQuotient I n M).isSheaf⟩ :
      TopCat.Sheaf Ab.{u} X) ⊤ _ 0 fun x _ => ?_
  obtain ⟨W, hW, hxW⟩ := hcover x
  have hnat : ∀ {P Q : X.Modules} (g : P ⟶ Q) (y : Γ(P, ⊤)),
      g.app W.1 (P.presheaf.map (homOfLE (le_top (a := W.1))).op y) =
        Q.presheaf.map (homOfLE (le_top (a := W.1))).op (g.app ⊤ y) := fun g y =>
    congrArg (fun k => k y) (g.mapPresheaf.naturality (homOfLE (le_top (a := W.1))).op)
  have hzW : (idealPowerQuotientMap I I (n + c) (n + c) le_rfl f).app W.1
      ((idealPowerQuotient I (n + c) M).presheaf.map
        (homOfLE (le_top (a := W.1))).op z) = 0 := by
    rw [hnat _ z, hz]
    simp
  have hres : (idealPowerQuotient I n M).presheaf.map (homOfLE (le_top (a := W.1))).op
      ((quotientMapOfLE
        (idealPowerMultiple_antitone I M (Nat.le_add_right n c))).app ⊤ z) = 0 :=
    (hnat _ z).symm.trans (quotientMapOfLE_app_eq_zero_of_affine I f W (hAR W hW n) _ hzW)
  have hgerm := TopCat.Presheaf.germ_res_apply (idealPowerQuotient I n M).presheaf
    (homOfLE (le_top (a := W.1))) x hxW
    ((quotientMapOfLE (idealPowerMultiple_antitone I M (Nat.le_add_right n c))).app ⊤ z)
  rw [hres] at hgerm
  exact hgerm.symm.trans (by simp)

/-! ### Injectivity on the formal sections of `Spec(A) ∖ V(𝔞)` -/

open Stacks.LocalCohomology

/-- For a Noetherian ring the open subscheme `Spec(A) ∖ V(𝔞)` is quasi-compact: a quasi-compact
open of a prime spectrum is exactly the complement of the zero locus of a finitely generated
ideal, and over a Noetherian ring every ideal is finitely generated. -/
@[ega "I 1.1.10" "(ii), special case"]
instance compactSpace_complementZeroLocus (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) : CompactSpace (complementZeroLocus A a : Scheme) := by
  have h : IsCompact ((complementZeroLocus A a).1 : Set (Spec (CommRingCat.of A))) := by
    change @IsCompact (PrimeSpectrum A) PrimeSpectrum.zariskiTopology
      (PrimeSpectrum.zeroLocus (a : Set A))ᶜ
    exact (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨a, IsNoetherian.noetherian a, rfl⟩).1
  exact isCompact_iff_compactSpace.mp h

/-- The morphism of inverse systems `Γ(U, F / Iⁿ F) ⟶ Γ(U, G / Iⁿ G)` induced by a morphism
`f : F ⟶ G` of modules on `U = Spec(A) ∖ V(𝔞)`. -/
def formalSectionsMap (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) :
    formalSections A I a F ⟶ formalSections A I a G where
  app n := (idealPowerQuotientMap (idealSheafNearVanishing A I a)
    (idealSheafNearVanishing A I a) n.unop n.unop le_rfl f).app ⊤
  naturality m n h :=
    congrArg (fun φ : idealPowerQuotient (idealSheafNearVanishing A I a) m.unop F ⟶
        idealPowerQuotient (idealSheafNearVanishing A I a) n.unop G => φ.app ⊤)
      (idealPowerQuotientMap_comp_map (idealSheafNearVanishing A I a) f h)

/-- The component at `n` of the induced morphism of inverse systems of sections is the induced
map on the quotients, read on sections over all of `U`. -/
theorem formalSectionsMap_app (A : Type u) [CommRing A] (I a : Ideal A)
    {F G : (complementZeroLocus A a : Scheme).Modules} (f : F ⟶ G) (n : ℕᵒᵖ) :
    (formalSectionsMap A I a f).app n =
      (idealPowerQuotientMap (idealSheafNearVanishing A I a) (idealSheafNearVanishing A I a)
        n.unop n.unop le_rfl f).app ⊤ :=
  rfl

/-- **The bottom row of the ladder of Stacks 0H48 is left exact.** For a monomorphism `f` of
coherent modules on `U = Spec(A) ∖ V(𝔞)` with `A` Noetherian, the induced map
`lim Γ(U, F / Iⁿ F) ⟶ lim Γ(U, G / Iⁿ G)` is injective. -/
theorem injective_limMap_formalSectionsMap (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) {F G : (complementZeroLocus A a : Scheme).Modules}
    [F.IsCoherent] [G.IsCoherent] (f : F ⟶ G)
    (hf : Mono (C := (complementZeroLocus A a : Scheme).Modules) f) :
    Function.Injective (ConcreteCategory.hom (limMap (formalSectionsMap A I a f))) := by
  obtain ⟨c, hc⟩ :=
    exists_forall_quotientMapOfLE_app_top_eq_zero (idealSheafNearVanishing A I a) f hf
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  refine Concrete.limit_ext _ z 0 fun n => ?_
  rw [map_zero]
  have hπ : ConcreteCategory.hom
      ((idealPowerQuotientMap (idealSheafNearVanishing A I a) (idealSheafNearVanishing A I a)
        (n.unop + c) (n.unop + c) le_rfl f).app ⊤)
      (ConcreteCategory.hom (limit.π (formalSections A I a F) (op (n.unop + c))) z) = 0 := by
    have h1 : ConcreteCategory.hom (limit.π (formalSections A I a G) (op (n.unop + c)))
        (ConcreteCategory.hom (limMap (formalSectionsMap A I a f)) z) = 0 := by
      rw [hz, map_zero]
    rwa [← ConcreteCategory.comp_apply, limMap_π, ConcreteCategory.comp_apply] at h1
  have hw : ConcreteCategory.hom ((formalSections A I a F).map
        (homOfLE (Nat.le_add_right n.unop c)).op)
      (ConcreteCategory.hom (limit.π (formalSections A I a F) (op (n.unop + c))) z) =
      ConcreteCategory.hom (limit.π (formalSections A I a F) n) z := by
    rw [← ConcreteCategory.comp_apply, limit.w]
  exact hw.symm.trans
    (hc n.unop (ConcreteCategory.hom (limit.π (formalSections A I a F) (op (n.unop + c))) z) hπ)

/-- The induced map `lim Γ(U, F / Iⁿ F) ⟶ lim Γ(U, G / Iⁿ G)` of a monomorphism of coherent
modules is a monomorphism. -/
theorem mono_limMap_formalSectionsMap (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) {F G : (complementZeroLocus A a : Scheme).Modules}
    [F.IsCoherent] [G.IsCoherent] (f : F ⟶ G)
    (hf : Mono (C := (complementZeroLocus A a : Scheme).Modules) f) :
    Mono (limMap (formalSectionsMap A I a f)) :=
  ConcreteCategory.mono_of_injective _ (injective_limMap_formalSectionsMap A I a f hf)

end Stacks.Algebraization

end
