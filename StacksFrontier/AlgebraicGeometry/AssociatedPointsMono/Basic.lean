module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs

/-!
# Injectivity of a map of quasi-coherent modules detected at associated points

Let `X` be a locally Noetherian scheme and let `φ : F ⟶ G` be a map of quasi-coherent
`𝒪_X`-modules. This file proves that `φ` is a monomorphism as soon as, at every point `x`
of `X`, either the induced map on stalks `F_x → G_x` is injective or `x` is not an
associated point of `F`.

The argument is the one of the source, carried out on a fixed affine open `U = Spec A` with
`A = Γ(X, U)` Noetherian. Writing `M = Γ(F, U)` and `K` for the kernel of
`Γ(F, U) → Γ(G, U)`, if `K ≠ 0` then `A` Noetherian gives an associated prime
`p = Ann_A(k)` of `K` for some `k ∈ K`. The point `y ∈ U` corresponding to `p` then has
`Ann_{𝒪_{X,y}}(germ_y k) = 𝔪_y`, so `y` is an associated point of `F` while `germ_y k ≠ 0`
is killed by the map on stalks at `y` — contradicting the hypothesis at `y`. Hence `φ` is
injective on sections over every affine open, therefore injective on all stalks, therefore
injective on sections over every open, and finally a monomorphism.

The computation of `Ann_{𝒪_{X,y}}(germ_y k)` only needs that a germ of a section of a
quasi-coherent module over an affine open vanishes exactly when some function not vanishing
at the point kills the section; this is `exists_smul_eq_zero_of_germ_eq_zero`, the `t = 0`
case of `Stacks.ModuleStalkSpecialization.exists_smul_eq_of_germ_eq`, which in turn rests on
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`: sections over
a basic open of an affine open are a localization of sections over the affine open.

The `𝒪_{X,x}`-module structure on a stalk is
`Stacks.ModuleStalkSpecialization.stalkModule`, re-exported into this namespace, and the
statement that a function not vanishing at a point of an affine open avoids the prime of that
point is `Stacks.ModuleStalkSpecialization.mem_primeCompl_of_mem_basicOpen`.

## Main definitions

* `IsAssociatedPoint` and `associatedPoints`: a point is associated to an `𝒪_X`-module when
  the maximal ideal of the local ring at the point is an associated prime of the stalk, in
  the sense of `IsAssociatedPrimeStacks`.

## Main results

* `mono_of_stalk_injective_on_associatedPoints` (Stacks tag 0AVL): a map of quasi-coherent
  modules on a locally Noetherian scheme is a monomorphism if at every point either the map
  on stalks is injective or the point is not associated to the source.
* `injective_app_of_isAffineOpen`: under the same hypotheses, the map on sections over an
  affine open is injective.
* `colon_germ_eq`: on an affine open, the annihilator of the germ of a section whose
  annihilator is the prime of the point is the maximal ideal of the local ring.

## References

* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.AssociatedPointsMono

variable {X : Scheme.{u}}

-- `stalkModule` was duplicated here; the surviving copy is
-- `Stacks.ModuleStalkSpecialization.stalkModule`, at
-- `StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean:235`. It is
-- re-exported so that the bare spelling keeps resolving in this namespace and in the files
-- that open it.

export Stacks.ModuleStalkSpecialization (stalkModule)

/-! `IsAssociatedPoint` and `associatedPoints` are `Stacks.Divisors.IsAssociatedPoint` and
`Stacks.Divisors.associatedPoints`, exported into this namespace so that the development below
and its consumers can use them unqualified.  They are defined, and carry Tag 02OJ, in
`StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints`. -/

export Stacks.Divisors (IsAssociatedPoint associatedPoints)


-- `mem_primeCompl_of_mem_basicOpen` was duplicated here; the surviving copy is
-- `Stacks.ModuleStalkSpecialization.mem_primeCompl_of_mem_basicOpen`, at
-- `StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean:278`, which
-- takes the point implicitly. It had no user outside this file, so it is not re-exported.

/-- On an affine open, the germ at a point of a section of a quasi-coherent module vanishes
only if some function not vanishing at that point kills the section. -/
theorem exists_smul_eq_zero_of_germ_eq_zero (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) (s : Γ(F, U))
    (hs : F.presheaf.germ U y hy s = 0) :
    ∃ a ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl, a • s = 0 := by
  obtain ⟨c, hc, hcs⟩ := Stacks.ModuleStalkSpecialization.exists_smul_eq_of_germ_eq
    F hU hy s 0 (hs.trans (map_zero _).symm)
  exact ⟨c, hc, hcs.trans (smul_zero c)⟩

/-- An element lies in the colon ideal of the span of `m` over `⊥` iff it kills `m`. -/
private theorem mem_colon_span_singleton_bot {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (m : M) :
    r ∈ (⊥ : Submodule R M).colon (Submodule.span R {m}) ↔ r • m = 0 := by
  rw [Submodule.colon_span, Submodule.mem_colon_singleton, Submodule.mem_bot]

/-- Let `F` be quasi-coherent on a scheme, `U` an affine open, `y ∈ U` and `k` a section of
`F` over `U` whose annihilator in `Γ(X, U)` is the prime ideal of `y`. Then the annihilator
of the germ of `k` at `y` is the maximal ideal of `𝒪_{X,y}`. -/
theorem colon_germ_eq (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (y : X) (hy : y ∈ U) (k : Γ(F, U))
    (hk : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon (Submodule.span Γ(X, U) {k})
            = (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    letI := stalkModule F y
    (⊥ : Submodule (X.presheaf.stalk y) (F.presheaf.stalk y)).colon
      (Submodule.span (X.presheaf.stalk y) {F.presheaf.germ U y hy k}) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) := stalkModule F y
  set p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal
  have hpp : p.IsPrime := (hU.primeIdealOf ⟨y, hy⟩).isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hy⟩
  have hgerm : ∀ r : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk y) r •
      F.presheaf.germ U y hy k = F.presheaf.germ U y hy (r • k) := fun r =>
    (PresheafOfModules.germ_smul F.val y U hy r k).symm
  have hkey : ∀ r : Γ(X, U), (F.presheaf.germ U y hy (r • k) = 0) ↔ r ∈ p := by
    refine fun r => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨t, ht, htz⟩ := exists_smul_eq_zero_of_germ_eq_zero F hU y hy (r • k) h
      refine (hpp.mem_or_mem ?_).resolve_left ht
      rwa [← hk, mem_colon_span_singleton_bot, mul_smul]
    · rw [← hk, mem_colon_span_singleton_bot] at h
      rw [h, map_zero]
  ext b
  rw [mem_colon_span_singleton_bot]
  obtain ⟨⟨r, c⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl b
  rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (X.presheaf.stalk y) p r c]
  have hcu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk y) c.1) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y) p c.1).mpr c.2
  have hmul : algebraMap Γ(X, U) (X.presheaf.stalk y) c.1 *
      IsLocalization.mk' (X.presheaf.stalk y) r c
      = algebraMap Γ(X, U) (X.presheaf.stalk y) r :=
    IsLocalization.mk'_spec' _ r c
  rw [← hkey r, ← hgerm r, ← hmul, mul_smul]
  exact ⟨fun h => by rw [h, smul_zero], fun h => hcu.smul_left_cancel.mp (by rw [h, smul_zero])⟩

/-- The point of an affine open attached to a prime of its ring of functions has that prime
as its prime ideal. -/
theorem primeIdealOf_isoSpec_inv {U : X.Opens} (hU : IsAffineOpen U) (z : Spec Γ(X, U)) :
    hU.primeIdealOf (hU.isoSpec.inv z) = z := by
  change hU.isoSpec.hom (hU.isoSpec.inv z) = z
  rw [← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
  rfl

variable {F G : X.Modules}

/-- **Stacks Project, Tag 0AVL**, on an affine open: if at every point the map on stalks is
injective or the point is not associated to the source, then the map on sections over an
affine open is injective. -/
theorem injective_app_of_isAffineOpen [IsLocallyNoetherian X]
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y : X, Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map f.mapPresheaf)) ∨
      y ∉ associatedPoints F)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (f.app U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) :=
    { toFun := f.app U
      map_add' := map_add _
      map_smul' := fun r x => f.app_smul r x }
  have hker : LinearMap.ker φ = ⊥ := by
    by_contra hne
    have : Nontrivial (LinearMap.ker φ) := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨q, hq⟩ := associatedPrimes.nonempty Γ(X, U) (LinearMap.ker φ)
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq
    obtain ⟨hqp, k, hkq⟩ := hq
    have hcol : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))}) = q := by
      ext r
      rw [mem_colon_span_singleton_bot, hkq, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    set u : U := hU.isoSpec.inv ⟨q, hqp⟩
    have hpq : hU.primeIdealOf u = ⟨q, hqp⟩ := primeIdealOf_isoSpec_inv hU _
    have hcol' : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))})
          = (hU.primeIdealOf ⟨(u : X), u.2⟩).asIdeal := by
      rw [hcol]
      exact congrArg PrimeSpectrum.asIdeal hpq.symm
    let : Module (X.presheaf.stalk (u : X)) (F.presheaf.stalk (u : X)) :=
      stalkModule F (u : X)
    have hann := colon_germ_eq F hU (u : X) u.2 (k : Γ(F, U)) hcol'
    have hassoc : (u : X) ∈ associatedPoints F := ⟨inferInstance, _, hann⟩
    have hgz : F.presheaf.germ U (u : X) u.2 (k : Γ(F, U)) ≠ 0 := by
      intro h
      have h1 : (1 : X.presheaf.stalk (u : X)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk (u : X)) := by
        rw [← hann, mem_colon_span_singleton_bot, h, smul_zero]
      exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (u : X))).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    refine hgz ((hf (u : X)).resolve_right (fun h => h hassoc) ?_)
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U (u : X) u.2 f.mapPresheaf (k : Γ(F, U))]
    have hk0 : (f.mapPresheaf.app (Opposite.op U)) (k : Γ(F, U)) = 0 := k.2
    rw [hk0, map_zero]
    exact (map_zero _).symm
  intro a b hab
  refine sub_eq_zero.mp ?_
  have htk : a - b ∈ LinearMap.ker φ := by
    change f.app U (a - b) = 0
    rw [map_sub, hab, sub_self]
  rwa [hker, Submodule.mem_bot] at htk

/-- **Stacks Project, Tag 0AVL**, on stalks: under the hypothesis of the tag, the map on
stalks is injective at every point. -/
theorem injective_stalkFunctor_map [IsLocallyNoetherian X]
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y : X, Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map f.mapPresheaf)) ∨
      y ∉ associatedPoints F)
    (x : X) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map f.mapPresheaf)) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq z
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV f.mapPresheaf s,
    Scheme.Modules.mapPresheaf_app] at hz
  have hz' : G.presheaf.germ V x hxV (f.app V s) = G.presheaf.germ V x hxV (0 : Γ(G, V)) :=
    hz.trans (map_zero _).symm
  obtain ⟨W, hxW, iV, iV', hres⟩ :=
    TopCat.Presheaf.germ_eq G.presheaf x hxV hxV (f.app V s) (0 : Γ(G, V)) hz'
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW'⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hUW : (U : X.Opens) ≤ W := hUW'
  have hUV : (U : X.Opens) ≤ V := hUW.trans iV.le
  have hres0 : G.presheaf.map (homOfLE hUV).op (f.app V s) = 0 := by
    have hfac : (homOfLE hUV : (U : X.Opens) ⟶ V) = homOfLE hUW ≫ iV :=
      Subsingleton.elim _ _
    rw [hfac, show ((homOfLE hUW ≫ iV : (U : X.Opens) ⟶ V)).op
        = iV.op ≫ (homOfLE hUW).op from rfl,
      Functor.map_comp_apply, hres, map_zero, map_zero]
  have hnat : f.app (U : X.Opens) (F.presheaf.map (homOfLE hUV).op s)
      = G.presheaf.map (homOfLE hUV).op (f.app V s) := by
    simpa only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] using
      congr($(f.mapPresheaf.naturality (homOfLE hUV).op) s)
  have hs0 : F.presheaf.map (homOfLE hUV).op s = 0 := by
    refine injective_app_of_isAffineOpen f hf hU ?_
    rw [hnat, hres0, map_zero]
  rw [← F.presheaf.germ_res_apply (homOfLE hUV) x hxU s, hs0]
  exact map_zero _

/-- A morphism of `𝒪_X`-modules which is injective on sections over every open is a
monomorphism. -/
theorem mono_of_app_injective (f : F ⟶ G) (h : ∀ U : X.Opens, Function.Injective (f.app U)) :
    Mono f :=
  ⟨fun g₁ g₂ he => Scheme.Modules.hom_ext _ _ fun U => by
    have h1 : g₁.app U ≫ f.app U = g₂.app U ≫ f.app U := by
      rw [← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, he]
    ext t
    exact h U congr($h1 t)⟩

/-- **Stacks Project, Tag 0AVL.** A morphism of quasi-coherent modules on a locally
Noetherian scheme is a monomorphism if it is injective on the stalk at every associated
point of its source. -/
@[stacks 0AVL]
theorem mono_of_stalk_injective_on_associatedPoints
    {X : Scheme.{u}} [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ x : X,
      Function.Injective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)).hom ∨
        x ∉ associatedPoints F) :
    Mono f :=
  mono_of_app_injective f fun U =>
    TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := ⟨F.presheaf, F.isSheaf⟩) f.mapPresheaf U
      fun y _ => injective_stalkFunctor_map f hf y

end Stacks.AlgebraicGeometry.AssociatedPointsMono
