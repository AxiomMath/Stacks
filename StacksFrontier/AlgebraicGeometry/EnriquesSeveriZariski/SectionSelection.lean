module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist
public import StacksFrontier.AlgebraicGeometry.AsymptoticSectionGrowth.ClosurePoint
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SpanRestrictInvertible
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EventualClosedRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Scheme.IntegralClosedSubschemeResidueField

/-!
# The sections vanishing at a non-closed point have large codimension

Let `k` be a field, `X` a scheme proper over `k`, `ℒ` an ample invertible `𝒪_X`-module and `x` a
point of `X` which is **not closed**.  The global sections of `ℒ^{⊗ d}` whose germ at `x` lies in
`𝔪_x (ℒ^{⊗ d})_x` — the sections that *vanish at* `x` — form a `k`-subspace of
`Γ(X, ℒ^{⊗ d})`, and this file shows that its codimension tends to infinity with `d`: for every
`c` there is a `d₀` with

`c + dim_k {s : s vanishes at x} ≤ dim_k Γ(X, ℒ^{⊗ d})` for all `d ≥ d₀`.

This is the selection step of [Stacks, Tag 0FD8]: a subspace of codimension at least `c` can be
avoided by a section even after `c` linear conditions have been imposed elsewhere, which is how
the Stacks Project produces a section not vanishing at any of finitely many prescribed points and
vanishing at none of the associated points of a coherent module.

The argument is the Stacks Project's own.  Let `Z` be the reduced induced closed subscheme on
`closure {x}` and `i : Z ⟶ X` its inclusion.  Then `Z` is integral with generic point above `x`,
and `dim Z ≥ 1` because `x` is not closed, so

* restriction `Γ(X, ℒ^{⊗ d}) → Γ(Z, (ℒ|_Z)^{⊗ d})` is onto for `d ≫ 0`
  (`AlgebraicGeometry.exists_forall_surjective_pullbackGlobalSection_tensorPower`), and
* `dim_k Γ(Z, (ℒ|_Z)^{⊗ d}) → ∞`
  (`AlgebraicGeometry.exists_forall_le_finrank_globalSections_subscheme_closure`),

while a section vanishing at `x` restricts to zero on `Z`, so the vanishing subspace is contained
in the kernel of the restriction.  Rank–nullity finishes the argument.

## Main results

* `Stacks.EnriquesSeveriZariski.vanishingSubmodule`: the sections of `ℒ^{⊗ d}` vanishing at `x`,
  as a `k`-subspace of `Γ(X, ℒ^{⊗ d})`, with `notMem_vanishingSubmodule_iff` identifying its
  complement with the nonvanishing locus condition at `x`.
* `Stacks.EnriquesSeveriZariski.pullbackGlobalSectionsOverField`: restriction of global sections
  along a morphism of schemes over `k`, as a `k`-linear map between the spaces
  `AlgebraicGeometry.globalSectionsOverField`.
* `Stacks.EnriquesSeveriZariski.pullbackGlobalSection_eq_zero_of_mem_maximalSmul`: a global
  section of an invertible module whose germ at the image of the generic point of an integral
  closed subscheme lies in the maximal ideal times the stalk restricts to zero on that
  subscheme.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_codim_vanishingSubmodule`: **the codimension of
  the sections vanishing at a non-closed point is unbounded in the degree.**

## Implementation notes

`vanishingSubmodule` is a submodule because the germ map is additive and semilinear over
`Γ(X, 𝒪_X) → 𝒪_{X,x}` (`Stacks.ModuleStalk.Γgerm_smul`), the `k`-action on
`AlgebraicGeometry.globalSectionsOverField` is through `Γ(X, 𝒪_X)`, and
`Stacks.ModuleStalk.maximalSmul` is a submodule of the stalk.  Membership is stated so that
`notMem_vanishingSubmodule_iff` needs no more than `not_congr Iff.rfl`.

`pullbackGlobalSectionsOverField` is the counterpart, for
`AlgebraicGeometry.globalSectionsOverField`, of `Stacks.Bertini.restrictionMap`.  The two cannot
be shared: `Stacks.Bertini.globalSections` restricts scalars along
`(Scheme.ΓSpecIso _).inv ≫ f.appTop` and `AlgebraicGeometry.globalSectionsOverField` along
`(Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ ⊤ _`, which are equal — by
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` — but not definitionally so, hence carry different
`Module k` instances on the one underlying abelian group.  `k`-linearity is
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul` together with the composition
law `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` for the structure morphisms.

The restriction-to-zero statement is the only genuinely new piece of mathematics.  The germ at the
generic point `z` of `Z` of the restriction of `s` is carried by
`AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv` to `1 ⊗ (germ of s at x)` in
`𝒪_{Z,z} ⊗_{𝒪_{X,x}} (ℒ^{⊗ d})_x`; the germ of `s` lies in `𝔪_x · (ℒ^{⊗ d})_x`, and
`1 ⊗ (r • t) = (r • 1) ⊗ t` vanishes for `r ∈ 𝔪_x` because
`AlgebraicGeometry.ker_stalkMap_genericPoint_eq_maximalIdeal` identifies `𝔪_x` with the kernel of
the stalk map at the generic point.  So the germ of the restriction vanishes, and
`Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero` — the module is
invertible on an integral locally Noetherian scheme — forces the restriction itself to vanish.

The ampleness hypothesis is `AlgebraicGeometry.Scheme.Modules.IsAmple`, the spelling both of the
two inputs are stated at; `Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple` converts it to
`Stacks.Ample.IsAmple` where that is wanted.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct

universe u

namespace Stacks.EnriquesSeveriZariski

attribute [local instance] HasDerivedCategory.standard

/-! ### The sections vanishing at a point -/

/-- **The global sections of `ℒ^{⊗ d}` vanishing at `x`.**  These are the sections whose germ at
`x` lies in `𝔪_x · (ℒ^{⊗ d})_x`, read as a `k`-subspace of `Γ(X, ℒ^{⊗ d})`: the germ map is
additive, and it carries a scalar multiple by `a ∈ Γ(X, 𝒪_X)` to the multiple by the germ of `a`,
which `𝔪_x · (ℒ^{⊗ d})_x` absorbs. -/
def vanishingSubmodule (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) (x : X) :
    Submodule k (AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)) where
  carrier := {s | ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom s ∈
    Stacks.ModuleStalk.maximalSmul (Stacks.Algebraization.tensorPowScheme X L d) x}
  add_mem' {a b} ha hb :=
    (fun (u v : Γ(Stacks.Algebraization.tensorPowScheme X L d, ⊤))
        (hu : ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom u ∈
          Stacks.ModuleStalk.maximalSmul (Stacks.Algebraization.tensorPowScheme X L d) x)
        (hv : ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom v ∈
          Stacks.ModuleStalk.maximalSmul (Stacks.Algebraization.tensorPowScheme X L d) x) =>
      Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul
          (Stacks.Algebraization.tensorPowScheme X L d) x)
        (map_add ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom u v))
        (Submodule.add_mem _ hu hv)) a b ha hb
  zero_mem' :=
    Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul
        (Stacks.Algebraization.tensorPowScheme X L d) x)
      (map_zero ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom))
      (Submodule.zero_mem _)
  smul_mem' c s hs :=
    (fun (a : Γ(X, ⊤)) (u : Γ(Stacks.Algebraization.tensorPowScheme X L d, ⊤))
        (hu : ((Stacks.Algebraization.tensorPowScheme X L d).presheaf.Γgerm x).hom u ∈
          Stacks.ModuleStalk.maximalSmul (Stacks.Algebraization.tensorPowScheme X L d) x) =>
      Eq.mpr (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul
          (Stacks.Algebraization.tensorPowScheme X L d) x)
        (Stacks.ModuleStalk.Γgerm_smul (Stacks.Algebraization.tensorPowScheme X L d) x a u))
        (Submodule.smul_mem _ _ hu))
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) s hs

/-- **A section fails to vanish at `x` exactly when `x` lies in its nonvanishing locus.**  The two
sides are the same condition on the germ, read once as membership in a subspace of the global
sections and once as membership of the point in `X_s`. -/
theorem notMem_vanishingSubmodule_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℤ) (x : X)
    (s : AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)) :
    s ∉ vanishingSubmodule k f L d x ↔
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L d) s :=
  not_congr Iff.rfl

/-! ### Restriction to a subscheme, as a `k`-linear map -/

/-- **Restriction of global sections along a morphism of schemes over `k`, as a `k`-linear
map.**  The underlying function is `AlgebraicGeometry.pullbackGlobalSections`; it is additive, and
it is `k`-linear because the image of a scalar in `Γ(X, 𝒪_X)` pulls back to the image of that
scalar in `Γ(Z, 𝒪_Z)`. -/
def pullbackGlobalSectionsOverField (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Z ⟶ X) (M : X.Modules) :
    AlgebraicGeometry.globalSectionsOverField k f M →ₗ[k]
      AlgebraicGeometry.globalSectionsOverField k (i ≫ f)
        ((Scheme.Modules.pullback i).obj M) where
  toFun s := AlgebraicGeometry.pullbackGlobalSections i M s
  map_add' s t := map_add (ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections i M)) s t
  map_smul' c s := by
    refine (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul i M _ s).trans ?_
    congr 1
    have happ : i.appLE (⊤ : X.Opens) (⊤ : Z.Opens) (by simp) = i.appTop :=
      Scheme.Hom.appLE_eq_app i
    have h := Scheme.Hom.appLE_comp_appLE i f (⊤ : (Spec (CommRingCat.of k)).Opens)
      (⊤ : X.Opens) (⊤ : Z.Opens) (by simp) (by simp)
    rw [happ] at h
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) h

/-! ### A section vanishing at the image of the generic point restricts to zero -/

/-- **A global section vanishing at the image of the generic point of an integral closed
subscheme restricts to zero on that subscheme.**  The germ at the generic point `z` of `Z` of the
restriction of `s` corresponds, under [Stacks, Tag 0098], to `1 ⊗ (germ of s at x)`, and that
tensor vanishes because `𝔪_x` is the kernel of the stalk map at `z`
(`AlgebraicGeometry.ker_stalkMap_genericPoint_eq_maximalIdeal`).  A section of an invertible
module on an integral scheme with vanishing germ at the generic point is zero. -/
theorem pullbackGlobalSection_eq_zero_of_mem_maximalSmul {X Z : Scheme.{u}} [IsIntegral Z]
    [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i] (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule Z ((Scheme.Modules.pullback i).obj A)] {x : X}
    (hx : i.base (genericPoint (Z : Type u)) = x) (s : Γ(A, ⊤))
    (hs : (A.presheaf.Γgerm x).hom s ∈ Stacks.ModuleStalk.maximalSmul A x) :
    Stacks.NonvanishingPullback.pullbackGlobalSection i A s = 0 := by
  subst hx
  set z := genericPoint (Z : Type u)
  set x := i.base z
  let : Algebra (X.presheaf.stalk (x))
      (Z.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  have hker := AlgebraicGeometry.ker_stalkMap_genericPoint_eq_maximalIdeal i
  have hgerm := Scheme.Modules.pullbackStalkEquiv_germ i A z ⊤
    (Set.mem_univ _) s
  have hzero : (1 : Z.presheaf.stalk z)
      ⊗ₜ[X.presheaf.stalk (x)]
        ((A.presheaf.Γgerm (x)).hom s) = 0 := by
    have hle : Stacks.ModuleStalk.maximalSmul A (x) ≤
        LinearMap.ker (TensorProduct.mk (X.presheaf.stalk (x))
          (Z.presheaf.stalk z)
          (TopCat.Presheaf.stalk (C := Ab.{u}) A.presheaf
            (x)) 1) := by
      refine Submodule.smul_le.2 fun r hr t _ => ?_
      have hrk : r ∈ RingHom.ker (i.stalkMap z).hom := by
        rw [hker]; exact hr
      have hr0 : (algebraMap (X.presheaf.stalk (x))
          (Z.presheaf.stalk z)) r = 0 := by
        rw [RingHom.algebraMap_toAlgebra]
        exact RingHom.mem_ker.mp hrk
      simp only [LinearMap.mem_ker, TensorProduct.mk_apply]
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hr0, TensorProduct.zero_tmul]
    exact hle hs
  have hg0 : (((Scheme.Modules.pullback i).obj A).presheaf.Γgerm
      z).hom
      (Stacks.NonvanishingPullback.pullbackGlobalSection i A s) = 0 :=
    (map_eq_zero_iff _ (Scheme.Modules.pullbackStalkEquiv i A
      z).injective).1 (hgerm.trans hzero)
  by_contra hne
  exact Stacks.AlgebraicGeometry.ReflexiveModules.Γgerm_genericPoint_ne_zero_of_ne_zero
    ((Scheme.Modules.pullback i).obj A) hne hg0

/-! ### The codimension bound -/

/-- **The sections vanishing at a non-closed point have unbounded codimension.**  For `X` proper
over a field `k`, `ℒ` ample invertible and `x` a point of `X` which is not closed, the subspace of
`Γ(X, ℒ^{⊗ d})` cut out by vanishing at `x` has codimension at least `c` for every `d` large
enough.

The reduced induced subscheme `Z` on `closure {x}` is integral of dimension at least one, so
restriction to `Z` is onto in large degrees and `dim_k Γ(Z, (ℒ|_Z)^{⊗ d})` exceeds `c` in large
degrees; a section vanishing at `x` restricts to zero on `Z`, so the vanishing subspace lies in
the kernel of the restriction, whose codimension is the dimension of `Γ(Z, (ℒ|_Z)^{⊗ d})`. -/
theorem exists_forall_le_codim_vanishingSubmodule (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Scheme.Modules.IsAmple X L)
    (x : X) (hx : ¬ IsClosed ({x} : Set X)) (c : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      c + Module.finrank k (vanishingSubmodule k f L (d : ℤ) x) ≤
        Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
          (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hrange : Set.range I.subschemeι.base = closure ({x} : Set X) := by
    rw [hI, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]; rfl
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by
      rw [hrange]; exact (isIrreducible_singleton (x := x)).closure)
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsLocallyNoetherian I.subscheme := isLocallyNoetherian_of_isImmersion I.subschemeι
  have hgen : I.subschemeι.base (genericPoint (I.subscheme : Type u)) = x := by
    have h := (genericPoint_spec (I.subscheme : Type u)).image
      (f := I.subschemeι.base) I.subschemeι.base.hom.continuous
    rw [Set.image_univ, hrange, closure_closure] at h
    exact h.eq isGenericPoint_closure
  obtain ⟨n₁, hn₁⟩ := AlgebraicGeometry.exists_forall_surjective_pullbackGlobalSection_tensorPower
    f I.subschemeι L hL
  obtain ⟨n₂, hn₂⟩ :=
    AlgebraicGeometry.exists_forall_le_finrank_globalSections_subscheme_closure k f L hL x hx c
  refine ⟨max n₁ n₂, fun d hd => ?_⟩
  have : Stacks.Ample.IsInvertibleModule X
      (Stacks.Algebraization.tensorPowScheme X L (d : ℤ)) :=
    Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L (d : ℤ)
  have : Stacks.Ample.IsInvertibleModule I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj
      (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := inferInstance
  have : (Stacks.Algebraization.tensorPowScheme X L (d : ℤ)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  have hres : ∀ s, pullbackGlobalSectionsOverField k f I.subschemeι
      (Stacks.Algebraization.tensorPowScheme X L (d : ℤ)) s =
      Stacks.NonvanishingPullback.pullbackGlobalSection I.subschemeι _ s := fun _ =>
    Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection _ _ _
  have hsurj : Function.Surjective (pullbackGlobalSectionsOverField k f I.subschemeι
      (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := by
    intro t
    obtain ⟨s, hs⟩ := hn₁ d (le_of_max_le_left hd) t
    exact ⟨s, (hres s).trans hs⟩
  have hiso : Module.finrank k (AlgebraicGeometry.globalSectionsOverField k
        (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj
          (Stacks.Algebraization.tensorPowScheme X L (d : ℤ)))) =
      Module.finrank k (AlgebraicGeometry.globalSectionsOverField k (I.subschemeι ≫ f)
        (Stacks.Algebraization.tensorPowScheme I.subscheme
          ((Scheme.Modules.pullback I.subschemeι).obj L) (d : ℤ))) :=
    LinearEquiv.finrank_eq ((globalSectionsFunctor k (I.subschemeι ≫ f)).mapIso
      (Stacks.Algebraization.pullbackTensorPowSchemeIso I.subschemeι L (d : ℤ))).toLinearEquiv
  have hc : c ≤ Module.finrank k (AlgebraicGeometry.globalSectionsOverField k
      (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj
        (Stacks.Algebraization.tensorPowScheme X L (d : ℤ)))) := by
    rw [hiso]; exact hn₂ d (le_of_max_le_right hd)
  have hVk : vanishingSubmodule k f L (d : ℤ) x ≤
      LinearMap.ker (pullbackGlobalSectionsOverField k f I.subschemeι
        (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))) := fun s hs =>
    LinearMap.mem_ker.2
      ((hres s).trans (pullbackGlobalSection_eq_zero_of_mem_maximalSmul I.subschemeι _ hgen s hs))
  have hrn := (pullbackGlobalSectionsOverField k f I.subschemeι
    (Stacks.Algebraization.tensorPowScheme X L (d : ℤ))).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrn
  have hle := Submodule.finrank_mono hVk
  omega

end Stacks.EnriquesSeveriZariski

end
