module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Mono, epi and exactness of a map of modules read off the geometric stalks

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `φ : F → G` be a map
of `𝒪_X`-modules on the small étale site of `X`. This file proves the direction of Stacks 04K5
which deduces a property of `φ` from the corresponding property of the induced maps
`F_x̄ → G_x̄` of stalks at the geometric points of `X`: `φ` is a monomorphism as soon as every
`F_x̄ → G_x̄` is injective, an epimorphism as soon as every `F_x̄ → G_x̄` is surjective, and a
short complex of `𝒪_X`-modules is exact as soon as its sequence of geometric stalks is exact at
every geometric point.

In each case the argument applies the forward direction to the kernel, the cokernel, or the
kernel of the second map of the complex, and concludes that the object in question has vanishing
geometric stalks, hence is zero: a module whose geometric stalks all vanish has empty support,
and a module with empty support is zero.

## Main results

* `AlgebraicGeometry.Space.isZero_iff_subsingleton_geometricModuleStalk`: an `𝒪_X`-module is zero
  exactly when all of its geometric stalks vanish.
* `AlgebraicGeometry.Space.mono_of_injective_geometricModuleStalkMap` and
  `AlgebraicGeometry.Space.mono_iff_injective_geometricModuleStalkMap`: **Stacks 04K5**,
  injectivity clause for modules.
* `AlgebraicGeometry.Space.epi_of_surjective_geometricModuleStalkMap` and
  `AlgebraicGeometry.Space.epi_iff_surjective_geometricModuleStalkMap`: **Stacks 04K5**,
  surjectivity clause for modules.
* `AlgebraicGeometry.Space.exact_of_exact_geometricModuleStalkMap` and
  `AlgebraicGeometry.Space.shortExact_iff_geometricModuleStalk`: **Stacks 04K5**, exactness clause
  for modules.

## Implementation notes

The module universe of the four statements about monomorphisms, epimorphisms and exactness is the
universe `u` of the schemes, since kernels and cokernels of maps of `𝒪_X`-modules need the abelian
structure of `AlgebraicGeometry.Space.Modules`, which is available only there. The criterion for
vanishing and the functoriality of the geometric stalk hold at an arbitrary module universe.

`AlgebraicGeometry.Space.exact_iff_stalk_exact` is the same clause of Stacks 04K5 for sheaves of
abelian groups, but with sections in `AddCommGrpCat.{max (u + 1) w}`; it therefore says nothing
about the abelian sheaf underlying a module with sections in the universe of the schemes, which is
what is proved here.

The abelian structure is supplied as a local instance —
`AlgebraicGeometry.Space.smallEtaleModulesAbelian` — rather than left to instance search, which
is unusable in a file importing
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsAndCokernels`: the two sheafification
instances it declares for every universe of module sections containing the objects of the site
have a universe parameter occurring only inside a `max`, so matching them against a goal at the
universe of the schemes leaves an unsolvable universe constraint postponed rather than failing.
The local instance is the very term the search returns when those two are absent.

Two steps of the exactness clause are written in term mode rather than with `obtain` and `rw`:
the preimage produced by the stalk exactness hypothesis is consumed by `Exists.elim`, and the
closing identity is assembled from
`AlgebraicGeometry.Space.geometricModuleStalkMap_comp` and `kernel.lift_ι`. Both tactics force
whnf of the kernel of the second map, whose typeclass data is that written-out abelian structure,
and exceed the heartbeat limit there.

## References

* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-! ### Functoriality of the geometric stalk -/

section Functoriality

variable (x : GeometricPoint B S hS X.1)

/-- The identity map of an `𝒪_X`-module induces the identity on each geometric stalk. -/
theorem geometricModuleStalkMap_id (F : Modules.{u, m} B S hS X.1 X.2)
    (z : geometricModuleStalk B S hS X x F) :
    geometricModuleStalkMap B S hS X x (𝟙 F) z = z := by
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
  rw [geometricModuleStalkMap_germ]
  rfl

/-- The map of geometric stalks induced by a composite of maps of `𝒪_X`-modules is the composite
of the induced maps. -/
theorem geometricModuleStalkMap_comp {F G H : Modules.{u, m} B S hS X.1 X.2} (φ : F ⟶ G)
    (ψ : G ⟶ H) (z : geometricModuleStalk B S hS X x F) :
    geometricModuleStalkMap B S hS X x (φ ≫ ψ) z =
      geometricModuleStalkMap B S hS X x ψ (geometricModuleStalkMap B S hS X x φ z) := by
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
  simp only [geometricModuleStalkMap_germ]
  rfl

/-- The zero map of `𝒪_X`-modules induces the zero map on each geometric stalk. -/
theorem geometricModuleStalkMap_zero {F G : Modules.{u, m} B S hS X.1 X.2}
    (z : geometricModuleStalk B S hS X x F) :
    geometricModuleStalkMap B S hS X x (0 : F ⟶ G) z = 0 := by
  obtain ⟨N, s, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
  have hzero : ((0 : F ⟶ G).val.app (op N.chart)).hom s = 0 := rfl
  rw [geometricModuleStalkMap_germ, hzero, map_zero]

/-- The composite of the geometric stalk maps of two composable maps with zero composite
vanishes. -/
private theorem geometricModuleStalkMap_comp_apply_eq_zero {F G H : Modules.{u, m} B S hS X.1 X.2}
    (φ : F ⟶ G) (ψ : G ⟶ H) (h : φ ≫ ψ = 0) (z : geometricModuleStalk B S hS X x F) :
    geometricModuleStalkMap B S hS X x ψ (geometricModuleStalkMap B S hS X x φ z) = 0 := by
  rw [← geometricModuleStalkMap_comp, h, geometricModuleStalkMap_zero]

end Functoriality

/-! ### Vanishing read off the geometric stalks -/

/-- **Stacks 04KA.** An `𝒪_X`-module is zero exactly when its geometric stalk at every geometric
point of `X` vanishes: the support of the underlying abelian sheaf is the set of points carrying a
nonzero geometric stalk, and a module with empty support is zero. -/
theorem isZero_iff_subsingleton_geometricModuleStalk (F : Modules.{u, m} B S hS X.1 X.2) :
    IsZero F ↔
      ∀ x : GeometricPoint B S hS X.1, Subsingleton (geometricModuleStalk B S hS X x F) := by
  rw [← supportOfSheaf_eq_empty_iff_isZero B S hS X F]
  constructor
  · intro h x
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact Set.eq_empty_iff_forall_notMem.mp h x.image
      ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F x.image).mpr
        ⟨x, rfl, hnt⟩)
  · intro h
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    obtain ⟨ybar, -, hnt⟩ :=
      (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F y).mp hy
    exact not_subsingleton_iff_nontrivial.mpr hnt (h ybar)

/-! ### Stacks 04K5 for modules -/

section Stalkwise

attribute [local instance 10000] smallEtaleModulesAbelian

/-- A monomorphism of `𝒪_X`-modules is injective on every geometric stalk: it is the first map of
the short exact sequence it forms with its cokernel. -/
theorem injective_geometricModuleStalkMap_of_mono (x : GeometricPoint B S hS X.1)
    {F G : Modules.{u, u} B S hS X.1 X.2} (φ : F ⟶ G) [Mono φ] :
    Function.Injective (geometricModuleStalkMap B S hS X x φ) := by
  let σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
    ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hσ : σ.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel σ
        (Abelian.monoIsKernelOfCokernel (f := φ) _ (colimit.isColimit _))
      mono_f := inferInstanceAs (Mono φ)
      epi_g := inferInstanceAs (Epi (cokernel.π φ)) }
  exact injective_geometricModuleStalkMap_f_of_shortExact B S hS X x σ hσ

/-- **Stacks 04K5**, injectivity clause for `𝒪_X`-modules. A map of `𝒪_X`-modules which is
injective on every geometric stalk is a monomorphism: its kernel has vanishing geometric stalks,
hence is zero. -/
theorem mono_of_injective_geometricModuleStalkMap {F G : Modules.{u, u} B S hS X.1 X.2}
    (φ : F ⟶ G) (h : ∀ x : GeometricPoint B S hS X.1,
      Function.Injective (geometricModuleStalkMap B S hS X x φ)) :
    Mono φ := by
  refine (Preadditive.mono_iff_isZero_kernel φ).mpr ?_
  refine (isZero_iff_subsingleton_geometricModuleStalk B S hS X (kernel φ)).mpr fun x =>
    subsingleton_of_forall_eq 0 fun z => ?_
  have hz : geometricModuleStalkMap B S hS X x (kernel.ι φ) z = 0 :=
    (map_eq_zero_iff _ (h x)).mp
      (geometricModuleStalkMap_comp_apply_eq_zero B S hS X x _ _ (kernel.condition φ) z)
  exact (map_eq_zero_iff _
    (injective_geometricModuleStalkMap_of_mono B S hS X x (kernel.ι φ))).mp hz

/-- **Stacks 04K5**, injectivity clause for `𝒪_X`-modules. A map of `𝒪_X`-modules is a
monomorphism exactly when it is injective on every geometric stalk. -/
theorem mono_iff_injective_geometricModuleStalkMap {F G : Modules.{u, u} B S hS X.1 X.2}
    (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : GeometricPoint B S hS X.1,
      Function.Injective (geometricModuleStalkMap B S hS X x φ) :=
  ⟨fun _ x => injective_geometricModuleStalkMap_of_mono B S hS X x φ,
    mono_of_injective_geometricModuleStalkMap B S hS X φ⟩

/-- **Stacks 04K5**, surjectivity clause for `𝒪_X`-modules. A map of `𝒪_X`-modules which is
surjective on every geometric stalk is an epimorphism: its cokernel has vanishing geometric
stalks, hence is zero. -/
theorem epi_of_surjective_geometricModuleStalkMap {F G : Modules.{u, u} B S hS X.1 X.2}
    (φ : F ⟶ G) (h : ∀ x : GeometricPoint B S hS X.1,
      Function.Surjective (geometricModuleStalkMap B S hS X x φ)) :
    Epi φ := by
  refine (Preadditive.epi_iff_isZero_cokernel φ).mpr ?_
  refine (isZero_iff_subsingleton_geometricModuleStalk B S hS X (cokernel φ)).mpr fun x =>
    subsingleton_of_forall_eq 0 fun z => ?_
  obtain ⟨w, rfl⟩ := surjective_geometricModuleStalkMap_of_epi B S hS X x (cokernel.π φ) z
  obtain ⟨v, rfl⟩ := h x w
  exact geometricModuleStalkMap_comp_apply_eq_zero B S hS X x _ _ (cokernel.condition φ) v

/-- **Stacks 04K5**, surjectivity clause for `𝒪_X`-modules. A map of `𝒪_X`-modules is an
epimorphism exactly when it is surjective on every geometric stalk. -/
theorem epi_iff_surjective_geometricModuleStalkMap {F G : Modules.{u, u} B S hS X.1 X.2}
    (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : GeometricPoint B S hS X.1,
      Function.Surjective (geometricModuleStalkMap B S hS X x φ) :=
  ⟨fun _ x => surjective_geometricModuleStalkMap_of_epi B S hS X x φ,
    epi_of_surjective_geometricModuleStalkMap B S hS X φ⟩

/-- **Stacks 04K5**, exactness clause for `𝒪_X`-modules. A short complex of `𝒪_X`-modules whose
sequence of geometric stalks is exact at every geometric point is exact: the map from its first
term to the kernel of its second map is surjective on every geometric stalk, hence an
epimorphism. -/
theorem exact_of_exact_geometricModuleStalkMap
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (h : ∀ x : GeometricPoint B S hS X.1,
      Function.Exact (geometricModuleStalkMap B S hS X x σ.f)
        (geometricModuleStalkMap B S hS X x σ.g)) :
    σ.Exact := by
  rw [σ.exact_iff_epi_kernel_lift]
  refine epi_of_surjective_geometricModuleStalkMap B S hS X
    (kernel.lift σ.g σ.f σ.zero) fun x z => ?_
  have hex := h x (geometricModuleStalkMap B S hS X x (kernel.ι σ.g) z)
  refine (Set.mem_range.mp (hex.mp
    (geometricModuleStalkMap_comp_apply_eq_zero B S hS X x _ _ (kernel.condition σ.g) z))).elim
    fun w hw => ?_
  refine ⟨w, injective_geometricModuleStalkMap_of_mono B S hS X x (kernel.ι σ.g) ?_⟩
  refine (geometricModuleStalkMap_comp B S hS X x (kernel.lift σ.g σ.f σ.zero)
    (kernel.ι σ.g) w).symm.trans ?_
  exact Eq.trans (congrArg (fun ψ : σ.X₁ ⟶ σ.X₂ =>
    geometricModuleStalkMap B S hS X x ψ w) (kernel.lift_ι σ.g σ.f σ.zero)) hw

/-- **Stacks 04K5** for `𝒪_X`-modules. A short complex of `𝒪_X`-modules is short exact exactly
when, at every geometric point of `X`, its sequence of geometric stalks is short exact. -/
theorem shortExact_iff_geometricModuleStalk
    (σ : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) :
    σ.ShortExact ↔ ∀ x : GeometricPoint B S hS X.1,
      Function.Injective (geometricModuleStalkMap B S hS X x σ.f) ∧
        Function.Exact (geometricModuleStalkMap B S hS X x σ.f)
          (geometricModuleStalkMap B S hS X x σ.g) ∧
        Function.Surjective (geometricModuleStalkMap B S hS X x σ.g) := by
  refine ⟨fun hσ x => ?_, fun h =>
    { exact := exact_of_exact_geometricModuleStalkMap B S hS X σ fun x => (h x).2.1
      mono_f := mono_of_injective_geometricModuleStalkMap B S hS X σ.f fun x => (h x).1
      epi_g := epi_of_surjective_geometricModuleStalkMap B S hS X σ.g fun x => (h x).2.2 }⟩
  have := hσ.epi_g
  exact ⟨injective_geometricModuleStalkMap_f_of_shortExact B S hS X x σ hσ,
    exact_geometricModuleStalkMap_of_shortExact B S hS X x σ hσ,
    surjective_geometricModuleStalkMap_of_epi B S hS X x σ.g⟩

end Stalkwise

end AlgebraicGeometry.Space

end
