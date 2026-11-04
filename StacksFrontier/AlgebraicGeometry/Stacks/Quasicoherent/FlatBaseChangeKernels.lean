module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerre

/-!
# The kernel clause of Stacks 0754 for the flat base change property, reduced to monomorphy

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  **Stacks 0762** attaches to a
presheaf of `𝒪_𝒳`-modules the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`.  Part (2) of
**Stacks 0764** says that the modules with the property form a weak Serre subcategory, which by
**Stacks 0754** asks for a zero object, strict fullness, closure under kernels and cokernels, and
closure under extensions.  Of those five,
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean` has the zero
object, the strict fullness and the cokernels, and
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeExtensions.lean` the
extensions, all at the level of presheaves of modules.  The kernel clause is the one that is
missing, and the reason is recorded in the implementation notes of that second file: it is the
only clause whose proof consumes *left* exactness of `a_{small}^*`, which at the presheaf reading
is the left adjoint `PresheafOfModules.pullback`.

This file reduces the clause to a strictly weaker statement, and only to that one: the kernel
clause holds as soon as `c_φ` is a **monomorphism** at the kernel of every morphism of modules
with the property.  No left exactness of `a_{small}^*` is used; only its right exactness, which
is formal.

## The reduction

Write `Φ : F ↦ a_{small}^*(F|_{V_ét})` and `Ψ : F ↦ F|_{U_ét}`, so that `c_φ` is a natural
transformation `η : Φ ⟶ Ψ`.  `Ψ` is exact and `Φ` is right exact, both unconditionally.  For a
short exact sequence `T` with `η` invertible at `T.X₂` and at `T.X₃`, monomorphy of `η` at `T.X₁`
is already enough to make `η` invertible at `T.X₁`: monomorphy of `η` at `T.X₁` forces `Φ T.f` to
be a monomorphism, because its composite with the isomorphism `η` at `T.X₂` is `η` at `T.X₁`
followed by the monomorphism `Ψ T.f`; so `Φ` carries `T` to a short exact sequence, `Ψ` does too,
and a map of short exact sequences which is invertible at the second and third terms is
invertible at the first, the first terms being the kernels of the respective second maps.

Given `α : F ⟶ G` with `F` and `G` having the property, the clause follows by applying that twice
along the canonical factorization of `α`:

* `0 ⟶ Im α ⟶ G ⟶ Coker α ⟶ 0` is short exact, `G` has the property and so does `Coker α`, by
  the cokernel clause already proved; so monomorphy at `Im α = Ker (Coker α ⟵ G)` gives `Im α`
  the property.
* `0 ⟶ Ker α ⟶ F ⟶ Im α ⟶ 0` is short exact, `F` has the property and now so does `Im α`; so
  monomorphy at `Ker α` gives `Ker α` the property.

Both `Im α` and `Ker α` are kernels of morphisms between modules with the property — the first of
`G ⟶ Coker α`, the second of `F ⟶ Im α` — so the single hypothesis `hmono` below covers both
uses.

## Main results

* `CategoryTheory.ShortComplex.isIso_app_of_shortExact_of_mono`: for a natural transformation
  from a right exact functor to an exact functor which is invertible at the second and third
  terms of a short exact sequence, monomorphy at the first term implies invertibility there.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_kernel_of_mono`: the kernel clause of
  **Stacks 0764** part (2), for presheaves of modules, over monomorphy of `c_φ` at kernels.

## Implementation notes

No `@[stacks]` attribute is carried and the kernel clause is **not** discharged here.
`hasFlatBaseChangeProperty_kernel_of_mono` takes the hypothesis `hmono`, which is not among the
conditions the subcategory carries, so it does not establish part (2) of **Stacks 0764** and does
not supply the weak Serre property of `LQCoh^fbc(𝒪_𝒳)` that **Stacks 0771** part (2) asks for.

What `hmono` amounts to is worth recording, because it is what any proof of the clause has to
produce.  A module with the property has, below a flat arrow, a presheaf-level inverse image
which is already a sheaf
(`AlgebraicGeometry.Stack.isSheaf_modulePullback_restrictModuleToSmallEtale`), and the sheaf-level
comparison map is invertible at the kernel, by the sheaf-reading kernel clause
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isLimit_kernelFork`.  So `c_φ` at the
kernel is the unit of sheafification of its source: it is invertible exactly when that source is
a sheaf, and it is a monomorphism exactly when that source is *separated*.  The reduction below
therefore turns the clause from a sheaf condition into a separatedness condition on the same
presheaf.

The two functors and the natural transformation are the ones set up in
`FlatBaseChangeExtensions.lean`: `AlgebraicGeometry.Stack.flatBaseChangeComparisonSource`,
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor` and
`AlgebraicGeometry.Stack.restrictModulePullbackComparisonNatTrans`, together with the instances
recorded there for their additivity and exactness; nothing about them is reproved.

The factorization of `α` is the abelian one, `Abelian.factorThruImage` followed by
`Abelian.image.ι`, and `Ker α` is identified with `Ker (Abelian.factorThruImage α)` through
`CategoryTheory.Limits.kernelCompMono`, the image inclusion being a monomorphism.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

universe uA vA uA' vA'

variable {A : Type uA} [Category.{vA} A] [Abelian A] {A' : Type uA'} [Category.{vA'} A']
  [Abelian A']

/-- **Short five lemma against a right exact functor, at the first term.**  Let `η : Φ ⟶ Ψ` be a
natural transformation of additive functors of abelian categories with `Φ` right exact and `Ψ`
exact.  If `η` is an isomorphism at the second and third terms of a short exact sequence `T` and
a monomorphism at the first term, it is an isomorphism at the first term.

Left exactness of `Φ` is not needed.  Monomorphy of `η` at `T.X₁` makes `Φ T.f` a monomorphism,
its composite with the isomorphism `η` at `T.X₂` being `η` at `T.X₁` followed by the monomorphism
`Ψ T.f`; right exactness makes `Φ T.g` a cokernel of `Φ T.f` and an epimorphism.  So `Φ` carries
`T` to a short exact sequence, and `CategoryTheory.ShortComplex.isIso₁_of_shortExact_of_isIso₂₃`
applies. -/
theorem isIso_app_of_shortExact_of_mono (Φ Ψ : A ⥤ A') [Φ.Additive] [Ψ.Additive]
    [Limits.PreservesFiniteColimits Φ] [Limits.PreservesFiniteLimits Ψ]
    [Limits.PreservesFiniteColimits Ψ] (η : Φ ⟶ Ψ) {T : ShortComplex A} (hT : T.ShortExact)
    (h₂ : IsIso (η.app T.X₂)) (h₃ : IsIso (η.app T.X₃)) (hm : Mono (η.app T.X₁)) :
    IsIso (η.app T.X₁) := by
  have := hT.mono_f
  have := hT.epi_g
  have := h₂
  have := h₃
  have := hm
  have hΨ : (T.map Ψ).ShortExact := hT.map Ψ
  have : Mono (Ψ.map T.f) := hΨ.mono_f
  have hcok : Limits.IsColimit
      (Limits.CokernelCofork.ofπ (Φ.map T.g) (by rw [← Φ.map_comp, T.zero, Φ.map_zero])) :=
    Limits.IsColimit.ofIsoColimit
      (Limits.CokernelCofork.mapIsColimit _ hT.gIsCokernel Φ) (Limits.Cofork.ext (Iso.refl _))
  have hmono : Mono (Φ.map T.f) := by
    have hnat := η.naturality T.f
    have : Mono (Φ.map T.f ≫ η.app T.X₂) := by
      rw [hnat]; infer_instance
    exact mono_of_mono _ (η.app T.X₂)
  have hΦ : (T.map Φ).ShortExact :=
    { exact := (T.map Φ).exact_of_g_is_cokernel hcok
      mono_f := hmono
      epi_g := Limits.epi_of_isColimit_cofork hcok }
  have : IsIso (mapNatTrans T η).τ₂ := h₂
  have : IsIso (mapNatTrans T η).τ₃ := h₃
  exact isIso₁_of_shortExact_of_isIso₂₃ (mapNatTrans T η) hΦ hΨ

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **The kernel clause of Stacks 0764 part (2), for presheaves of modules, over monomorphy of
`c_φ` at kernels.**  Let `α : F ⟶ G` be a morphism of presheaves of `𝒪_𝒳`-modules both of which
have the flat base change property of **Stacks 0762**.  If, below every arrow lying over a flat
morphism of schemes, the comparison map `c_φ` of **Stacks 06WC** is a monomorphism at the kernel
of every morphism between modules with the property, then the kernel of `α` has the flat base
change property.

The hypothesis `hmono` is **not** one of the conditions of **Stacks 0754**, so this does not
discharge the kernel clause; it is the reduction of that clause to monomorphy, which needs only
right exactness of `a_{small}^*`.  The proof applies
`CategoryTheory.ShortComplex.isIso_app_of_shortExact_of_mono` twice along the abelian
factorization of `α`: first to `0 ⟶ Im α ⟶ G ⟶ Coker α ⟶ 0`, whose outer terms have the property
by hypothesis and by `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_cokernel`, and then to
`0 ⟶ Ker α ⟶ F ⟶ Im α ⟶ 0`. -/
theorem hasFlatBaseChangeProperty_kernel_of_mono
    (hmono : ∀ {M N : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj}
      (β : M ⟶ N), HasFlatBaseChangeProperty B E h S hS p hp τ hτ M →
        HasFlatBaseChangeProperty B E h S hS p hp τ hτ N →
        ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
          Mono ((restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ).app
            (kernel β)))
    {F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ G)
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F)
    (hG : HasFlatBaseChangeProperty B E h S hS p hp τ hτ G) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ (kernel α) := by
  have hC : HasFlatBaseChangeProperty B E h S hS p hp τ hτ (cokernel α) :=
    hasFlatBaseChangeProperty_cokernel B E h S hS p hp τ hτ α hF hG
  have hI : HasFlatBaseChangeProperty B E h S hS p hp τ hτ (Abelian.image α) :=
    fun {_ _} φ hflat =>
      ShortComplex.isIso_app_of_shortExact_of_mono
        (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ)
        (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ _)
        (restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ)
        (T := ShortComplex.kernelSequence (cokernel.π α))
        (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
          (show Epi (cokernel.π α) from inferInstance))
        (hG φ hflat) (hC φ hflat) (hmono (cokernel.π α) hG hC φ hflat)
  have hK : HasFlatBaseChangeProperty B E h S hS p hp τ hτ
      (kernel (Abelian.factorThruImage α)) :=
    fun {_ _} φ hflat =>
      ShortComplex.isIso_app_of_shortExact_of_mono
        (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ)
        (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ _)
        (restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ)
        (T := ShortComplex.kernelSequence (Abelian.factorThruImage α))
        (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
          (show Epi (Abelian.factorThruImage α) from inferInstance))
        (hF φ hflat) (hI φ hflat) (hmono (Abelian.factorThruImage α) hF hI φ hflat)
  exact fun {_ _} φ hflat => hasFlatBaseChangeProperty_of_iso B E h S hS p hp τ hτ
    ((kernelCompMono (Abelian.factorThruImage α) (Abelian.image.ι α)).symm ≪≫
      kernelIsoOfEq (Abelian.image.fac α)) hK φ hflat

end AlgebraicGeometry.Stack

end
