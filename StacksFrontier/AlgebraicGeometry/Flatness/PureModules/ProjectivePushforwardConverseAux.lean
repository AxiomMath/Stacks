module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin.Defs

/-!
# Auxiliary bridges for the converse of Tag 05MD

The converse half of Tag 05MD — that relative purity of a finitely presented flat module makes
its direct image locally projective — is assembled from a ring-theoretic core and a geometric
chart. Joining the two needs a handful of translations between spellings that are equal but not
syntactically so, and those translations are collected here so that the main argument reads as
mathematics.

Three concern the ring core. `IsAssociatedPrimeStacks` annihilates the *span* of an element
while `Module.relativeAssassin` annihilates the element, and the contraction of a prime is
written `Ideal.under` on one side and `PrimeSpectrum.comap` on the other; the two are reconciled
by `Module.mem_relativeAssassin_of_isAssociatedPrimeStacks` and
`isAssociatedPrimeStacks_congr_ideal`.

The rest concern the geometry. Sections of a direct image over an open `V` are by definition the
sections of the module over `q ⁻¹ᵁ V`, with scalars restricted along `q.app V`; the relative
assassin of sections is instead phrased with `q.appLE`, and the two ring maps agree. Finally a
section of an étale morphism is an open immersion, which is what makes the étale lift into a
fibre product — `AlgebraicGeometry.etale_pullback_lift_of_etale`, imported from
`StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterionLimits` — available to
the chart argument.

## Main results

* `Module.mem_relativeAssassin_of_isAssociatedPrimeStacks`: the associated-prime bridge.
* `AlgebraicGeometry.projective_pushforward_sections_iff`: sections of a direct image.
* `AlgebraicGeometry.isLocallyProjective_pushforward_of_projective_sections`: the affine case.

## References

* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct AlgebraicGeometry

universe u v w

/-! ### The associated-prime bridges -/

namespace Module

/-- An associated prime of the fibre module, in the `IsAssociatedPrimeStacks` spelling, lies in
the relative assassin of the module over the ring map. The two differ only in annihilating the
span of an element rather than the element. -/
theorem mem_relativeAssassin_of_isAssociatedPrimeStacks
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] (q : PrimeSpectrum S)
    (h : IsAssociatedPrimeStacks S
      (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) q.asIdeal) :
    q ∈ Module.relativeAssassin R S N := by
  obtain ⟨-, m, hm⟩ := h
  refine ⟨m, ?_⟩
  rwa [← Stacks.RingTheory.AssociatedPrimeStacks.colon_span_singleton_eq_colon_singleton m]

end Module

/-- Being an associated prime of a fibre module depends on the base prime only through its
value, so equal base primes give the same condition. -/
theorem isAssociatedPrimeStacks_congr_ideal
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (p₁ p₂ : Ideal R) [p₁.IsPrime] [p₂.IsPrime] (q : Ideal S) (he : p₁ = p₂) :
    IsAssociatedPrimeStacks S (N ⊗[R] p₁.ResidueField) q ↔
      IsAssociatedPrimeStacks S (N ⊗[R] p₂.ResidueField) q := by
  subst he
  rfl

namespace AlgebraicGeometry

/-! ### Sections of a direct image -/

/-- The ring map restricting scalars from an open to its tautological preimage is the one the
direct image uses. -/
theorem appLE_preimage_self {Y T : Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) :
    q.appLE V (q ⁻¹ᵁ V) le_rfl = q.app V := by
  simp [Scheme.Hom.appLE]

/-- Sections of a direct image over an open are the sections of the module over the preimage of
that open, with scalars restricted along the morphism. Hence one is projective exactly when the
other is. -/
theorem projective_pushforward_sections_iff {Y T : Scheme.{u}} (q : Y ⟶ T) (G : Y.Modules)
    (V : T.Opens) :
    Module.Projective Γ(T, V) Γ((Scheme.Modules.pushforward q).obj G, V) ↔
      (letI : Module Γ(T, V) Γ(G, q ⁻¹ᵁ V) := Module.compHom Γ(G, q ⁻¹ᵁ V) (q.app V).hom
       Module.Projective Γ(T, V) Γ(G, q ⁻¹ᵁ V)) := Iff.rfl

/-- The `appLE` spelling of the scalars on the sections over a tautological preimage agrees with
the `app` spelling that the direct image uses. -/
theorem projective_sections_appLE_iff_app {Y T : Scheme.{u}} (q : Y ⟶ T) (G : Y.Modules)
    (V : T.Opens) :
    (letI : Module Γ(T, V) Γ(G, q ⁻¹ᵁ V) :=
      Module.compHom Γ(G, q ⁻¹ᵁ V) (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom
     Module.Projective Γ(T, V) Γ(G, q ⁻¹ᵁ V)) ↔
      (letI : Module Γ(T, V) Γ(G, q ⁻¹ᵁ V) := Module.compHom Γ(G, q ⁻¹ᵁ V) (q.app V).hom
       Module.Projective Γ(T, V) Γ(G, q ⁻¹ᵁ V)) := by
  rw [appLE_preimage_self]

/-- On an affine base, projectivity of the global sections of a quasi-coherent module over an
affine morphism makes its direct image locally projective. -/
theorem isLocallyProjective_pushforward_of_projective_sections {Y T : Scheme.{u}} [IsAffine T]
    (q : Y ⟶ T) [IsAffineHom q] (G : Y.Modules) [G.IsQuasicoherent]
    (hproj : letI : Module Γ(T, ⊤) Γ(G, ⊤) := Module.compHom Γ(G, ⊤) q.appTop.hom
      Module.Projective Γ(T, ⊤) Γ(G, ⊤)) :
    Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward q).obj G) := by
  let : Module Γ(T, ⊤) Γ(G, ⊤) := Module.compHom Γ(G, ⊤) q.appTop.hom
  refine (isLocallyProjective_iff_exists_affineOpen_cover _).2
    ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (by simp),
      fun _ => isAffineOpen_top _, fun _ => ?_⟩
  change Module.Projective Γ(T, ⊤) Γ(G, ⊤)
  exact hproj

/-! ### Sections of étale morphisms -/

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
theorem isQuasicoherent_pullback_obj {A B : Scheme.{u}} (u : A ⟶ B) (G : B.Modules)
    [G.IsQuasicoherent] : ((Scheme.Modules.pullback u).obj G).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent A.toRingedSpace B.toRingedSpace
    u.toLRSHom.toShHom G (show G.IsQuasicoherent from inferInstance)

/-- Projectivity of the sections over an open transports along an isomorphism of modules. -/
theorem projective_sections_of_iso_at {T : Scheme.{u}} {M N : T.Modules} (e : M ≅ N)
    (V : T.Opens) (hM : Module.Projective Γ(T, V) Γ(M, V)) :
    Module.Projective Γ(T, V) Γ(N, V) := by
  have := hM
  let φ : Γ(M, V) →ₗ[Γ(T, V)] Γ(N, V) :=
    { toFun := fun x => e.hom.app V x
      map_add' := fun x y => map_add (e.hom.app V).hom x y
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul e.hom r x }
  exact Module.Projective.of_equiv'
    (LinearEquiv.ofBijective φ (ConcreteCategory.bijective_of_isIso (e.hom.app V)))

end AlgebraicGeometry

end
