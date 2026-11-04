module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisDualModel
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TraceCokernelAnnihilation
public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator

/-!
# Local duality turns a surjection onto stable images into a vanishing of kernels

Let `R` be a Noetherian local ring with a normalized dualizing complex `ω`, let `X` be a finite
`R`-module with a cone `π_n : X → N_n` onto an inverse system `(N_n)` of finite `R`-modules, and
write `H(-) = Hʲ_𝔪(-)` and `D(-) = Ext^{-j}_R(-, ω)` (in the spelling
`Stacks.Algebraization.dualizingExtFunctor`). Local duality identifies `H(K)` with the Matlis
dual `Hom_R(D(K), E)` naturally in `K` (`Dualizing.LocalDuality.localDualityMatlisEquiv_comp`),
and `E` separates the elements of every module
(`Dualizing.exists_hom_apply_ne_zero_of_isInjectiveHull`). Consequently, if, for every `n`, the
image of some later `H(N_m) → H(N_n)` lies in the image of `H(π_n) : H(X) → H(N_n)`, then, for
every `n`, the kernel of `D(π_n) : D(N_n) → D(X)` dies in `D(N_m)` for some `m ≥ n`.

## Main results

* `Dualizing.LocalDuality.exists_injectiveHull_and_localCohomology_iso` — a normalized dualizing
  complex comes with an injective hull `E` of the residue field and an identification
  `RΓ_𝔪(ω) ≅ E[0]`.
* `Dualizing.LocalDuality.exists_map_eq_zero_of_dualizingExt_ker` — the vanishing of kernels.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK), local duality.
* [Stacks Project, Tag 0A82](https://stacks.math.columbia.edu/tag/0A82), the hull.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite StacksDraft.DerivedHom
open Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing.LocalDuality

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- **The data of local duality at a normalized dualizing complex.** An injective hull `E` of
the residue field together with `RΓ_𝔪(ω) ≅ E[0]`, both from [Stacks, Tag 0A82]. -/
public theorem exists_injectiveHull_and_localCohomology_iso
    (ω : DerivedCategory (ModuleCat.{u} R)) (hω : IsNormalizedDualizingComplex.{u, u} ω) :
    ∃ (E : ModuleCat.{u} R) (i : residueFieldModule.{u, u} R ⟶ E) (_ : Mono i),
      Module.IsInjectiveHull i ∧
        Nonempty ((localCohomologyEndofunctor R (IsLocalRing.maximalIdeal R)
            (IsNoetherian.noetherian _)).obj ω ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj E) := by
  obtain ⟨i, hi, hhull⟩ := exists_isInjectiveHull_homology_zero_localCohomology.{u, u} R ω hω
  obtain ⟨θ⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, u} R ω hω
  exact ⟨_, i, hi, hhull, ⟨θ⟩⟩

/-- Local duality is invertible at a finite module placed in degree zero. -/
private theorem isIso_localDualityMor_single_of_finite {r : ℕ} (f : Fin r → R)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal R)
    (ω : DerivedCategory (ModuleCat.{u} R)) (hω : IsDualizingComplex ω) (E : ModuleCat.{u} R)
    (θ : (localCohomologyEndofunctor R (IsLocalRing.maximalIdeal R)
        (IsNoetherian.noetherian _)).obj ω ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj E)
    (X : ModuleCat.{u} R) [Module.Finite R X] :
    IsIso (localDualityMor (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) f hf ω E θ
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X)) :=
  isIso_localDualityMor (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) f hf ω E θ _ hω
    0 inferInstance (fun j => Dualizing.finite_homology_single X j)

/-- **Local duality turns a surjection onto stable images into a vanishing of kernels.** Let `ω`
be a normalized dualizing complex over the Noetherian local ring `R`, let `π_n : X → N_n` be maps
from a finite module to an inverse system of finite modules, and suppose that for every `n` the
image of some later transition `Hʲ_𝔪(N_m) → Hʲ_𝔪(N_n)` lies in the image of `Hʲ_𝔪(π_n)`. Then
for every `n` there is an `m ≥ n` such that every element of `Ext^{-j}(N_n, ω)` killed by
`Ext^{-j}(π_n, ω)` is killed by the transition map `Ext^{-j}(N_n, ω) → Ext^{-j}(N_m, ω)`. -/
public theorem exists_map_eq_zero_of_dualizingExt_ker
    (ω : DerivedCategory (ModuleCat.{u} R)) (hω : IsNormalizedDualizingComplex.{u, u} ω) (j : ℤ)
    (X : ModuleCat.{u} R) [Module.Finite R X] (N : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (hN : ∀ n : ℕ, Module.Finite R (N.obj (op n))) (π : ∀ n : ℕ, X ⟶ N.obj (op n))
    (hsurj : ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor R j).map
          (N.map (homOfLE h).op)).hom ≤
        LinearMap.range ((Stacks.LocalCohomology.localCohomologyModuleFunctor R j).map
          (π n)).hom) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ h : n ≤ m,
      ∀ x : (Stacks.Algebraization.dualizingExtFunctor ω j).obj (op (N.obj (op n))),
        ((Stacks.Algebraization.dualizingExtFunctor ω j).map (π n).op).hom x = 0 →
          ((Stacks.Algebraization.dualizingExtFunctor ω j).map
            (N.map (homOfLE h).op).op).hom x = 0 := by
  obtain ⟨E, i, hi, hhull, ⟨θ⟩⟩ := exists_injectiveHull_and_localCohomology_iso ω hω
  have : Injective E := hhull.1
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R))
  have hiso : ∀ (Y : ModuleCat.{u} R) [Module.Finite R Y],
      IsIso (localDualityMor (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) f hf ω E θ
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)) :=
    fun Y _ => isIso_localDualityMor_single_of_finite f hf ω hω.1 E θ Y
  let Λ : ∀ (Y : ModuleCat.{u} R) [Module.Finite R Y], _ := fun Y _ =>
    localDualityMatlisEquiv (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) f hf ω E θ j
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y) (hiso Y)
  have hnat : ∀ {Y Y' : ModuleCat.{u} R} [Module.Finite R Y] [Module.Finite R Y'] (g : Y ⟶ Y')
      (h : (Stacks.LocalCohomology.localCohomologyModuleFunctor R j).obj Y)
      (x : (Stacks.Algebraization.dualizingExtFunctor ω j).obj (op Y')),
      Λ Y' (((Stacks.LocalCohomology.localCohomologyModuleFunctor R j).map g).hom h) x =
        Λ Y h (((Stacks.Algebraization.dualizingExtFunctor ω j).map g.op).hom x) := by
    intro Y Y' _ _ g h x
    have := localDualityMatlisEquiv_comp (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _)
      f hf ω E θ j ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g) (hiso Y) (hiso Y') h
    exact LinearMap.congr_fun this x
  intro n
  obtain ⟨m, h, hle⟩ := hsurj n
  have := hN n
  have := hN m
  refine ⟨m, h, fun x hx => ?_⟩
  by_contra hne
  obtain ⟨φ, hφ⟩ := Dualizing.exists_hom_apply_ne_zero_of_isInjectiveHull.{u, u} R E i hhull
    ((Stacks.Algebraization.dualizingExtFunctor ω j).obj (op (N.obj (op m)))) _ hne
  obtain ⟨hm, hhm⟩ := (Λ (N.obj (op m))).surjective φ.hom
  obtain ⟨g, hg⟩ := hle ⟨hm, rfl⟩
  apply hφ
  rw [← hhm]
  refine (hnat (N.map (homOfLE h).op) hm x).symm.trans ?_
  refine (congrArg (fun z => Λ (N.obj (op n)) z x) hg.symm).trans ?_
  refine (hnat (π n) g x).trans ?_
  exact (congrArg (Λ X g) hx).trans (map_zero _)

end Dualizing.LocalDuality

end
