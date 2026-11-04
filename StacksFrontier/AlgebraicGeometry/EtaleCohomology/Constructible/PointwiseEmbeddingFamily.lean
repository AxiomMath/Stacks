module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter
public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Finitely many pointwise embeddings of a constructible sheaf of modules embed it

Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a Noetherian ring and `ℱ` a
constructible sheaf of `Λ`-modules on `X_étale`. Suppose that for every point `x ∈ X` we are given
a finite morphism of finite presentation `f_x : Y_x → X`, a constructible sheaf `𝒢_x` on
`(Y_x)_étale` and a map `ψ_x : f_x^{-1} ℱ → 𝒢_x` whose kernel vanishes at a geometric point of
`Y_x` lying over a point of the fibre over `x`. Then finitely many of the adjoint maps
`ℱ → f_{x,*} 𝒢_x` give a monomorphism `ℱ → ⨁_k f_{x_k,*} 𝒢_{x_k}`.

This is the finiteness step of the proof of Stacks 09Z6, run over a quasi-compact and
quasi-separated base rather than a Noetherian one. The source argues with the ascending chain
condition (Stacks 09YV), available only over a Noetherian base; here compactness of the
constructible topology replaces it. The kernel of `ψ_x` is constructible (Stacks 03RZ (3)), so its
support is constructible (Stacks 09YS (3)); the image under `f_x` of the complement of that
support is constructible by Chevalley's theorem, and contains `x`. These images cover `X`, and
finitely many of them do because `X` is compact in the constructible topology.

The joint kernel `𝒦` of the selected adjoint maps vanishes at every geometric point `ȳ` of `X`:
choose `k` with `ȳ` over the image of a point `z` outside the support of `ker ψ_{x_k}`, and a
geometric point `t` of `Y_{x_k}` over `z`. The inverse image of `𝒦 ↪ ℱ` along `f_{x_k}` composed
with `ψ_{x_k}` is the adjoint of `𝒦 ↪ ℱ → f_{x_k,*}𝒢_{x_k}`, which is zero, so it factors through a
monomorphism into `ker ψ_{x_k}`; stalks preserve monomorphisms, so the stalk of `f_{x_k}^{-1}𝒦`
at `t` — which is the stalk of `𝒦` at `f_{x_k} ∘ t`, a geometric point over the same point as
`ȳ` — vanishes.

Only stalks of sheaves on the source are used, never the stalk formula for a finite direct image
(Stacks 03QP), and constructibility of `f_{x,*}𝒢_x` (Stacks 095R) is not needed.

## Main results

* `AlgebraicGeometry.exists_mono_biproduct_lift_of_forall_isZero_etaleStalk_kernel` — the finite
  subfamily.

## References

* [Stacks Project, Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
* [Stacks Project, Tag 09YS](https://stacks.math.columbia.edu/tag/09YS)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

attribute [local instance 3000] Abelian.hasFiniteBiproducts

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- Limits of the size of the small étale site in `ModuleCat.{u + 1} Λ`, with the universes
pinned so that instance search does not have to solve `u + 1 = max u ?v`. -/
instance (priority := high) hasLimitsOfSize_moduleCat_of_univ_succ (R : Type (u + 1)) [Ring R] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1}

/-- A monomorphism into a sheaf of `Λ`-modules whose stalk at a geometric point vanishes has a
source with vanishing stalk there: stalks are the fibre functor of a point of the site, which is
left exact. -/
theorem isZero_etaleStalk_of_mono_module (S : Scheme.{u}) (hS : B.Contains S)
    (t : GeometricPoint S) {K L : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ)}
    (m : K ⟶ L) [Mono m] (hL : IsZero (etaleStalk B S hS t L.obj)) :
    IsZero (etaleStalk B S hS t K.obj) := by
  have hfil : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have hab : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have hm : Mono (((geometricPointSitePoint B S hS t).sheafFiber
    (A := ModuleCat.{u + 1} Λ)).map m) := Functor.map_mono _ _
  exact (IsZero.iff_id_eq_zero _).2 <|
    (cancel_mono (((geometricPointSitePoint B S hS t).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map m)).1 (hL.eq_of_tgt _ _)

/-- Vanishing of the stalk of a sheaf of modules transfers between geometric points over the same
point. -/
private theorem isZero_etaleStalk_of_eq_base (S : Scheme.{u}) (hS : B.Contains S)
    {p q : GeometricPoint S} (h : p.hom default = q.hom default)
    (K : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ))
    (hq : IsZero (etaleStalk B S hS q K.obj)) : IsZero (etaleStalk B S hS p K.obj) :=
  IsZero.of_iso hq ((etaleStalkPresheafFunctorIsoOfEqBase B S hS h (ModuleCat.{u + 1} Λ)).app K.obj)

/-- Let `ψ : f^{-1} ℱ ⟶ 𝒢` and let `𝒦 ↪ ℱ` be killed by the adjoint `ℱ ⟶ f_* 𝒢` of `ψ`. If the
stalks of `ker ψ` vanish at every geometric point over `z`, then the stalk of `𝒦` vanishes at every
geometric point over `f z`. -/
private theorem isZero_etaleStalk_of_comp_homEquiv_eq_zero {X Y : B.Scheme} (f : Y ⟶ X)
    {F K : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    {G : Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ)}
    (ψ : ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Y.obj Y.property)).obj F ⟶ G)
    (i : K ⟶ F) [Mono i]
    (hi : i ≫ ((smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Y.obj Y.property)).homEquiv _ _ ψ = 0)
    {z : Y.obj} (hz : ∀ t : GeometricPoint Y.obj, t.LiesOver z →
      IsZero (etaleStalk B Y.obj Y.property t (kernel ψ).obj))
    (ybar : GeometricPoint X.obj) (hzy : (B.inclusion.map f) z = ybar.hom default) :
    IsZero (etaleStalk B X.obj X.property ybar K.obj) := by
  let t : GeometricPoint Y.obj := GeometricPoint.ofPoint _ z
  have htz : t.LiesOver z := GeometricPoint.ofPoint_liesOver _ z
  let adj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)
  let T := (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)
  have := additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B f Λ
  have := preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B f Λ
  have hi' : i ≫ adj.homEquiv _ _ ψ = 0 := hi
  have hcomp : T.map i ≫ ψ = 0 := by
    have h := congrArg (adj.homEquiv _ _).symm hi'
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply] at h
    rw [h, Adjunction.homEquiv_counit, T.map_zero, zero_comp]
  have : Mono (T.map i) := Functor.map_mono _ _
  have : Mono (kernel.lift ψ (T.map i) hcomp) := mono_of_mono_fac (kernel.lift_ι _ _ _)
  have hbase : ybar.hom default = (t.map (B.inclusion.map f)).hom default := by
    simp only [GeometricPoint.map_hom]
    rw [← hzy, ← htz]
    rfl
  exact isZero_etaleStalk_of_eq_base B Λ X.obj X.property hbase K
    (IsZero.of_iso (isZero_etaleStalk_of_mono_module B Λ Y.obj Y.property t
      (kernel.lift ψ (T.map i) hcomp) (hz t htz))
      (etaleStalkSmallEtalePullObjIso B f t (ModuleCat.{u + 1} Λ) K).symm)

variable [IsNoetherianRing Λ]

/-- The locus of points of `Y` over which the kernel of a map `f^{-1} ℱ ⟶ 𝒢` of constructible
sheaves has a non-vanishing stalk is constructible. -/
private theorem isConstructible_support_kernel_pullback {X Y : B.Scheme} [CompactSpace Y.obj]
    [QuasiSeparatedSpace Y.obj] (f : Y ⟶ X)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (hF : IsConstructibleModuleSheaf B X Λ F)
    {G : Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ)}
    (hG : IsConstructibleModuleSheaf B Y Λ G)
    (ψ : ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Y.obj Y.property)).obj F ⟶ G) :
    IsConstructible {y | ∃ t : GeometricPoint Y.obj, t.LiesOver y ∧
      ¬ IsZero (etaleStalk B Y.obj Y.property t (kernel ψ).obj)} := by
  let P : ObjectProperty (Sheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{u + 1} Λ)) := fun H => IsConstructibleModuleSheaf B Y Λ H
  let _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  exact isConstructible_support_moduleSheaf.{u + 1, u, u + 1} B Y Λ _
    (P.prop_kernel ψ (isConstructibleModuleSheaf_pullback B Λ f F hF) hG)

/-- **The finite subfamily of pointwise embeddings.** Let `X` be a quasi-compact quasi-separated
scheme and `ℱ` a constructible sheaf of `Λ`-modules on `X_étale`. Suppose that for every point
`x` there are a finite morphism of finite presentation `f_x : Y_x ⟶ X`, a constructible sheaf
`𝒢_x` on `(Y_x)_étale` and a map `ψ_x : f_x^{-1} ℱ ⟶ 𝒢_x` whose kernel has vanishing stalk at a
geometric point of `Y_x` mapping to `x`. Then for finitely many points `x_1, …, x_n` the map
`ℱ ⟶ ⨁_k f_{x_k,*} 𝒢_{x_k}` with components the adjoints of the `ψ_{x_k}` is a monomorphism. -/
theorem exists_mono_biproduct_lift_of_forall_isZero_etaleStalk_kernel (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F)
    (Y : X.obj → B.Scheme) (f : ∀ x, Y x ⟶ X)
    [hfin : ∀ x, IsFinite (B.inclusion.map (f x))]
    [hfp : ∀ x, LocallyOfFinitePresentation (B.inclusion.map (f x))]
    (G : ∀ x, Sheaf (SmallEtale.topology B (Y x).obj (Y x).property) (ModuleCat.{u + 1} Λ))
    (hG : ∀ x, IsConstructibleModuleSheaf B (Y x) Λ (G x))
    (ψ : ∀ x, ((smallEtaleBaseChange B (f x)).sheafPullback (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (Y x).obj (Y x).property)).obj F ⟶ G x)
    (hψ : ∀ x, ∃ t : GeometricPoint (Y x).obj, (B.inclusion.map (f x)) (t.hom default) = x ∧
      IsZero (etaleStalk B (Y x).obj (Y x).property t (kernel (ψ x)).obj)) :
    ∃ (n : ℕ) (p : Fin n → X.obj),
      Mono (biproduct.lift fun k : Fin n =>
        ((smallEtaleBaseChange B (f (p k))).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (Y (p k)).obj (Y (p k)).property)).homEquiv _ _ (ψ (p k))) := by
  classical
  have : CompactSpace (B.inclusion.obj X) := ‹CompactSpace X.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj X) := ‹QuasiSeparatedSpace X.obj›
  have hqc : ∀ x, CompactSpace (Y x).obj := fun x =>
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map (f x))
  have hqs : ∀ x, QuasiSeparatedSpace (Y x).obj := fun x =>
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map (f x))
  let supp : ∀ x, Set (Y x).obj := fun x =>
    {y | ∃ t : GeometricPoint (Y x).obj, t.LiesOver y ∧
      ¬ IsZero (etaleStalk B (Y x).obj (Y x).property t (kernel (ψ x)).obj)}
  let L : X.obj → Set X.obj := fun x => (B.inclusion.map (f x)) '' (supp x)ᶜ
  have hL : ∀ x, IsConstructible (L x) := fun x =>
    (B.inclusion.map (f x)).isConstructible_image
      (isConstructible_support_kernel_pullback B Λ (f x) hF (hG x) (ψ x)).compl
  have hxL : ∀ x, x ∈ L x := by
    intro x
    obtain ⟨t, htx, ht⟩ := hψ x
    refine ⟨t.hom default, ?_, htx⟩
    rintro ⟨t', ht', hne⟩
    exact hne (isZero_etaleStalk_of_eq_base B Λ (Y x).obj (Y x).property ht' _ ht)
  let _ : SpectralSpace X.obj := ⟨⟩
  obtain ⟨s, hs⟩ := @IsCompact.elim_finite_subcover X.obj (constructibleTopology X.obj)
    Set.univ X.obj (@isCompact_univ X.obj (constructibleTopology X.obj)
      (compactSpace_constructibleTopology X.obj)) L (fun x => (hL x).isOpen_constructibleTopology)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxL x⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let p : Fin (Fintype.card s) → X.obj := fun k => (e.symm k).val
  refine ⟨Fintype.card s, p, ?_⟩
  set Φ := biproduct.lift fun k : Fin (Fintype.card s) =>
    ((smallEtaleBaseChange B (f (p k))).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (Y (p k)).obj (Y (p k)).property)).homEquiv _ _ (ψ (p k)) with hΦ
  have hK : IsZero (kernel Φ) := by
    refine isZero_of_forall_isZero_etaleStalk_module B Λ X.obj X.property _ fun ybar => ?_
    obtain ⟨x, hxs, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ybar.hom default)))
    obtain ⟨k, rfl⟩ : ∃ k, p k = x := ⟨e ⟨x, hxs⟩, by simp [p]⟩
    obtain ⟨z, hz, hzy⟩ := hy
    have hπ : ((smallEtaleBaseChange B (f (p k))).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (Y (p k)).obj (Y (p k)).property)).homEquiv _ _ (ψ (p k)) =
        Φ ≫ biproduct.π _ k := by
      rw [hΦ, biproduct.lift_π]
    refine isZero_etaleStalk_of_comp_homEquiv_eq_zero B Λ (f (p k)) (ψ (p k)) (kernel.ι Φ) ?_
      (fun t ht => not_not.1 fun hne => hz ⟨t, ht, hne⟩) ybar hzy
    rw [hπ, kernel.condition_assoc, zero_comp]
  exact Preadditive.mono_of_kernel_zero (hK.eq_of_src _ _)

end AlgebraicGeometry

end
