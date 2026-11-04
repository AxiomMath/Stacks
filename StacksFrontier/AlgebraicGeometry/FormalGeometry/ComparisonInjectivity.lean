module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import Mathlib.RingTheory.Filtration
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# The kernel of the comparison map of Stacks 0EG2

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. `Stacks.Algebraization.comparisonMap` compares the sections of `F`
defined on arbitrarily small neighbourhoods of the formal locus `U ∩ V(I)` with the compatible
families of sections of `F / Iⁿ F` on all of `U`. This file identifies its kernel and proves
the part of Stacks 0EG2's injectivity argument that is Krull's intersection theorem.

The reduction is in two steps. First, the comparison kills a section exactly when every
reduction `F ⟶ F / Iⁿ F` kills it — equivalently, when the section is a section of `Iⁿ F` for
every `n`. Second, on an affine open the sections of `Iⁿ F` are `I(W)ⁿ Γ(F, W)`, so such a
section lies in `⋂ₙ I(W)ⁿ Γ(F, W)`; Krull's intersection theorem in the form
`Ideal.mem_iInf_smul_pow_eq_bot_iff` then makes it fixed by an element of `I(W)`, hence killed
by a function invertible at any point of the support of `I`, hence of vanishing germ there.

What remains of 0EG2's injectivity half is therefore exactly the geometric statement that a
section of `F` whose germs vanish along the formal locus vanishes — in the source, the step
"a section in the kernel would have to have empty support, hence would have to be zero", which
uses the associated points of `F`. That is isolated as the hypothesis of
`Stacks.Algebraization.mono_comparisonMap_of_forall_germ_eq_zero`.

## Main results

* `Stacks.Algebraization.kernelSubmodule_cokernel_π_ι` — a submodule of a sheaf of modules on a
  scheme is the sectionwise kernel of the projection onto its quotient.
* `Stacks.Algebraization.adicProj_app_apply_eq_zero_iff` — a section is killed by
  `F ⟶ F / Iⁿ F` exactly when it is a section of `Iⁿ F`.
* `Stacks.Algebraization.germ_eq_zero_of_forall_mem_idealPowerMultiple` — **Krull's
  intersection theorem for the adic filtration**: a section of a coherent module over an affine
  open lying in `Iⁿ F` for every `n` has vanishing germ at every point of the support of `I`.
* `Stacks.Algebraization.isFiltered_opensNearVanishing` — the neighbourhoods of the formal
  locus form a filtered category, so every element of the colimit comes from one of them.
* `Stacks.Algebraization.comparisonAt_apply_eq_zero_iff` — the kernel of the comparison at a
  single neighbourhood.
* `Stacks.Algebraization.mono_comparisonMap_of_forall` — the comparison map is a monomorphism
  as soon as it is injective at each neighbourhood.
* `Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero` — a section killed by the
  comparison has vanishing germ along the formal locus.
* `Stacks.Algebraization.mono_comparisonMap_of_forall_germ_eq_zero` — **the injectivity
  criterion for Stacks 0EG2**: the comparison map is a monomorphism provided a section of `F`
  near the formal locus whose germs vanish along it is zero.

## Implementation notes

`Mono` of a submodule inclusion is not synthesized at the concrete site `X.Modules`:
`SheafOfModules.instCategory` hides its universe levels inside a `max`, so the unification
`max ?a ?b ≟ u` fails, and `inferInstanceAs` does not cross from the `SheafOfModules` spelling
either. `AlgebraicGeometry.Scheme.Modules.mono_submodule_ι` of
`StacksFrontier/AlgebraicGeometry/Modules/SubobjectSubmodule.lean` goes through the faithful
forgetful functor instead, and is the library's one declaration of the fact.

`Concrete.colimit_exists_rep` needs the forgetful functor of `Ab` to preserve colimits of the
shape at hand. The index category of neighbourhoods has objects in `Type u` and morphisms in
`Type 0`, which is not the `PreservesFilteredColimits` size that Mathlib declares for `Ab`, so
`preservesFilteredColimitsOfSize_of_univLE` is applied with its universes written out.

The germ-vanishing statements are phrased with membership in
`Scheme.IdealSheafData.support` of `I · 𝒪_U` rather than with `I ≤ 𝔭` directly, because that is
the hypothesis `Stacks.Algebraization.support_idealSheafNearVanishing_le` consumes to place the
point inside the neighbourhood, and because Krull's intersection theorem is applied through the
affine-open ideal `I.ideal W`, which is what the support is defined by.

The remaining architecture of Stacks 0EG2, for the record, is: the reduction to depth `≥ 1` off
the locus `{x | closure {x} ∩ V(I) ⊆ V(𝔞)}` is `AlgebraicGeometry.IsDepthOneQuotient`
and `AlgebraicGeometry.depthOneQuotient_spec` (Tag 0DX3); the finish of the injectivity half
needs `Supp(F) = closure (Ass F)`, which is not in the tree (the two halves
`AlgebraicGeometry.associatedPoints_subset_support` and
`AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization` are), together with the
transport of germ vanishing along a specialization, for which Mathlib supplies only the bare
map `TopCat.Presheaf.stalkSpecializes`; and surjectivity is a separate induction on the
associated primes of a finite module presenting `F`, resting on Tags 0EIF and 0H48, neither of
which is formalized here.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

end Stacks.SheafOfModules

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### A submodule is the kernel of its own quotient projection -/

/-- A submodule of a sheaf of modules on a scheme is the sectionwise kernel of the projection
onto its quotient: a submodule is the kernel of its own cokernel. -/
theorem kernelSubmodule_cokernel_π_ι {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) :
    kernelSubmodule (cokernel.π (C := X.Modules) N.ι) = N := by
  have hmono : Mono (C := X.Modules) N.ι := AlgebraicGeometry.Scheme.Modules.mono_submodule_ι N
  have hker : IsLimit (KernelFork.ofι (f := cokernel.π (C := X.Modules) N.ι) N.ι
      (cokernel.condition (C := X.Modules) N.ι)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π (C := X.Modules) N.ι)
        (cokernel.condition (C := X.Modules) N.ι))
      (cokernelIsCokernel (C := X.Modules) N.ι)
  let e : (N.toSheafOfModules : X.Modules) ≅
      kernel (C := X.Modules) (cokernel.π (C := X.Modules) N.ι) :=
    IsLimit.conePointUniqueUpToIso hker (limit.isLimit _)
  exact (submodule_eq_of_iso N _
    (e.trans (kernelSubmoduleIso (cokernel.π (C := X.Modules) N.ι)).symm)
    ((Category.assoc _ _ _).trans ((congrArg (fun g => e.hom ≫ g)
      (kernelSubmoduleCorestrict_comp_ι (cokernel.π (C := X.Modules) N.ι))).trans
        (IsLimit.conePointUniqueUpToIso_hom_comp hker (limit.isLimit _)
          WalkingParallelPair.zero)))).symm

/-- A section of `F` over an open is killed by the projection `F ⟶ F / Iⁿ F` exactly when it is
a section of `Iⁿ F`. -/
theorem adicProj_app_apply_eq_zero_iff {X : Scheme.{u}} (I : X.IdealSheafData) (F : X.Modules)
    (n : ℕᵒᵖ) (W : X.Opens) (s : Γ(F, W)) :
    (adicProj I F n).app W s = 0 ↔
      s ∈ (idealPowerMultiple I n.unop F).toSubmodule.obj (op W) := by
  rw [← kernelSubmodule_cokernel_π_ι (idealPowerMultiple I n.unop F),
    kernelSubmodule_toSubmodule_obj]
  exact Iff.rfl

/-! ### Krull's intersection theorem for the adic filtration -/

/-- On an affine open, a function outside whose basic open a point lies belongs to the prime of
that point. -/
theorem mem_primeIdealOf_of_notMem_basicOpen {X : Scheme.{u}} (W : X.affineOpens) {y : X}
    (hy : y ∈ W.1) (f : Γ(X, W.1)) (h : y ∉ X.basicOpen f) :
    f ∈ (W.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  by_contra hf
  refine h ?_
  have h1 : W.2.primeIdealOf ⟨y, hy⟩ ∈ PrimeSpectrum.basicOpen f :=
    (PrimeSpectrum.mem_basicOpen f _).2 hf
  rw [← W.2.fromSpec_preimage_basicOpen] at h1
  have h2 : W.2.fromSpec (W.2.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen f := h1
  rwa [W.2.fromSpec_primeIdealOf ⟨y, hy⟩] at h2

/-- An ideal sheaf is contained in the prime of any point of its support, on any affine open
containing that point. -/
theorem ideal_le_primeIdealOf_of_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (W : X.affineOpens) {y : X} (hy : y ∈ W.1) (hyI : y ∈ I.support) :
    I.ideal W ≤ (W.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := W) hy, Scheme.mem_zeroLocus_iff] at hyI
  exact fun f hf => mem_primeIdealOf_of_notMem_basicOpen W hy f (hyI f hf)

/-- **Krull's intersection theorem for the adic filtration of a coherent module.**

Let `I` be a quasi-coherent ideal sheaf on a locally Noetherian scheme and `F` a coherent
module. A section of `F` over an affine open which is a section of `Iⁿ F` for every `n` has
vanishing germ at every point of the support of `I`.

The sections of `Iⁿ F` over an affine open `W` are `I(W)ⁿ Γ(F, W)`, so the section lies in
`⋂ₙ I(W)ⁿ Γ(F, W)`. By `Ideal.mem_iInf_smul_pow_eq_bot_iff` it is therefore fixed by some
`r ∈ I(W)`, hence killed by `1 - r`; and `r` lies in the prime of the point, so `1 - r` does
not, which for a quasi-coherent module is exactly the vanishing of the germ. -/
theorem germ_eq_zero_of_forall_mem_idealPowerMultiple {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent] (W : X.affineOpens) {y : X}
    (hy : y ∈ W.1) (hyI : y ∈ I.support) (s : Γ(F, W.1))
    (hs : ∀ n : ℕ, s ∈ (idealPowerMultiple I n F).toSubmodule.obj (op W.1)) :
    F.presheaf.germ W.1 y hy s = 0 := by
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hft : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hnoeth : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  have hfin : Module.Finite Γ(X, W.1) Γ(F, W.1) := moduleFinite_sections_on_affine F W.1 W.2
  have hmem : s ∈ ⨅ i : ℕ, I.ideal W ^ i • (⊤ : Submodule Γ(X, W.1) Γ(F, W.1)) :=
    Submodule.mem_iInf _ |>.2 fun n =>
      (idealPowerMultiple_toSubmodule_obj_affine I n F W) ▸ hs n
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (I.ideal W) s).1 hmem
  have hrp : (r : Γ(X, W.1)) ∈ (W.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    ideal_le_primeIdealOf_of_mem_support I W hy hyI r.2
  refine (germ_eq_zero_iff_exists_smul_eq_zero_affine F W.1 W.2 y hy s).2
    ⟨1 - (r : Γ(X, W.1)), fun hc => ?_, ?_⟩
  · exact (W.2.primeIdealOf ⟨y, hy⟩).isPrime.ne_top
      ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem hc hrp))
  · rw [sub_smul, one_smul, hr, sub_self]

/-! ### The neighbourhoods of the formal locus are filtered -/

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- The neighbourhoods of the formal locus are a filtered category: the intersection of two of
them is again one, and the morphisms between any two objects are propositions. Consequently
every element of `colimit (sectionsNearVanishing …)` is a section over a single
neighbourhood. -/
instance isFiltered_opensNearVanishing : IsFiltered (OpensNearVanishing A I a) where
  cocone_objs V W :=
    ⟨{ openSet := V.openSet ⊓ W.openSet
       contains_vanishing := fun x hx => ⟨V.contains_vanishing x hx, W.contains_vanishing x hx⟩ },
      ⟨inf_le_left⟩, ⟨inf_le_right⟩, trivial⟩
  cocone_maps V W f g := ⟨W, 𝟙 W, by cases f; cases g; rfl⟩
  nonempty := ⟨{ openSet := ⊤, contains_vanishing := fun _ _ => trivial }⟩

/-! ### The kernel of the comparison -/

/-- A section of `F` on a neighbourhood `V` of the formal locus is killed by the comparison at
`V` exactly when it is killed by every reduction `F ⟶ F / Iⁿ F`.

The comparison at `V` is the reduction modulo `Iⁿ` followed by the inverse of the restriction
isomorphism, so its components are injectively related to the reductions; and an element of a
limit vanishes exactly when all its components do. -/
theorem comparisonAt_apply_eq_zero_iff (V : OpensNearVanishing A I a)
    (s : ToType ((sectionsNearVanishing A I a F).obj V)) :
    ConcreteCategory.hom (comparisonAt A I a F V) s = 0 ↔
      ∀ n : ℕᵒᵖ, ConcreteCategory.hom (projNearVanishing A I a F V n) s = 0 := by
  refine ⟨fun h n => ?_, fun h => Concrete.limit_ext _ _ 0 fun n => ?_⟩
  · have hn := congrArg (ConcreteCategory.hom (limit.π (formalSections A I a F) n)) h
    rw [map_zero, ← ConcreteCategory.comp_apply, comparisonAt_π,
      ConcreteCategory.comp_apply] at hn
    exact ((ConcreteCategory.isIso_iff_bijective
      (inv (resNearVanishing A I a F V n))).1 inferInstance).1 (hn.trans (map_zero _).symm)
  · rw [map_zero, ← ConcreteCategory.comp_apply, comparisonAt_π, ConcreteCategory.comp_apply,
      h n, map_zero]

/-- **The injectivity criterion for the comparison map of Stacks 0EG2.** The comparison map is a
monomorphism as soon as, on each neighbourhood of the formal locus, a section killed by every
reduction `F ⟶ F / Iⁿ F` is zero.

Every element of the colimit is a section over a single neighbourhood, because that index
category is filtered, so injectivity of the comparison reduces to injectivity of the comparison
at each neighbourhood. -/
theorem mono_comparisonMap_of_forall
    (h : ∀ (V : OpensNearVanishing A I a) (s : ToType ((sectionsNearVanishing A I a F).obj V)),
      (∀ n : ℕᵒᵖ, ConcreteCategory.hom (projNearVanishing A I a F V n) s = 0) → s = 0) :
    Mono (comparisonMap A I a F) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, u} (forget Ab.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, u} _
  refine ConcreteCategory.mono_of_injective _ ((injective_iff_map_eq_zero _).2 fun z hz => ?_)
  obtain ⟨V, y, rfl⟩ := Concrete.colimit_exists_rep (sectionsNearVanishing A I a F) z
  rw [← ConcreteCategory.comp_apply, colimit_ι_comp_comparisonMap] at hz
  rw [h V y ((comparisonAt_apply_eq_zero_iff A I a F V y).1 hz), map_zero]

/-! ### Germs along the formal locus -/

/-- A section of `F` near the formal locus which the comparison kills has vanishing germ at
every point of the support of `I · 𝒪_U`: the comparison kills it modulo `Iⁿ` for every `n`, and
Krull's intersection theorem does the rest on an affine neighbourhood of the point. -/
theorem germ_eq_zero_of_comparisonAt_apply_eq_zero [IsNoetherianRing A] [F.IsCoherent]
    (V : OpensNearVanishing A I a) (s : ToType ((sectionsNearVanishing A I a F).obj V))
    (hsz : ConcreteCategory.hom (comparisonAt A I a F V) s = 0)
    {y : (complementZeroLocus A a : Scheme)}
    (hyI : y ∈ (idealSheafNearVanishing A I a).support) :
    F.presheaf.germ V.openSet y (support_idealSheafNearVanishing_le A I a V hyI) s = 0 := by
  obtain ⟨W, hWaff, hyW, hWle⟩ :=
    Opens.isBasis_iff_nbhd.mp (complementZeroLocus A a : Scheme).isBasis_affineOpens
      (U := V.openSet) (x := y) (support_idealSheafNearVanishing_le A I a V hyI)
  have hmemV : ∀ n : ℕ,
      s ∈ (idealPowerMultiple (idealSheafNearVanishing A I a) n F).toSubmodule.obj
        (op V.openSet) := fun n =>
    (adicProj_app_apply_eq_zero_iff (idealSheafNearVanishing A I a) F (op n) V.openSet s).1
      ((comparisonAt_apply_eq_zero_iff A I a F V s).1 hsz (op n))
  have hmemW : ∀ n : ℕ,
      F.presheaf.map (homOfLE hWle).op s ∈
        (idealPowerMultiple (idealSheafNearVanishing A I a) n F).toSubmodule.obj (op W) :=
    fun n => (idealPowerMultiple (idealSheafNearVanishing A I a) n F).toSubmodule.map
      (homOfLE hWle).op (hmemV n)
  refine Eq.trans (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hWle) y hyW s).symm ?_
  exact germ_eq_zero_of_forall_mem_idealPowerMultiple (idealSheafNearVanishing A I a) F
    ⟨W, hWaff⟩ hyW hyI _ hmemW

/-- **Stacks 0EG2, the injectivity half, reduced to its geometric content.** The comparison map
is a monomorphism provided a section of `F` on a neighbourhood of the formal locus whose germs
vanish at every point of the support of `I · 𝒪_U` is itself zero.

In the source this residual hypothesis is the sentence "a section `s ∈ F(V)` in the kernel would
have to have empty support, hence would have to be zero": the germs of such a section vanish
along the formal locus by Krull's intersection theorem, which is
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`, and the support of `F` is
the closure of its associated points, each of which specializes into the formal locus after the
depth-one reduction of Tag 0DX3. -/
theorem mono_comparisonMap_of_forall_germ_eq_zero [IsNoetherianRing A] [F.IsCoherent]
    (h : ∀ (V : OpensNearVanishing A I a) (s : ToType ((sectionsNearVanishing A I a F).obj V)),
      (∀ (y : (complementZeroLocus A a : Scheme))
        (hy : y ∈ (idealSheafNearVanishing A I a).support),
          F.presheaf.germ V.openSet y (support_idealSheafNearVanishing_le A I a V hy) s = 0) →
      s = 0) :
    Mono (comparisonMap A I a F) :=
  mono_comparisonMap_of_forall A I a F fun V s hz =>
    h V s fun _ hy => germ_eq_zero_of_comparisonAt_apply_eq_zero A I a F V s
      ((comparisonAt_apply_eq_zero_iff A I a F V s).2 hz) hy

end Stacks.Algebraization

end
