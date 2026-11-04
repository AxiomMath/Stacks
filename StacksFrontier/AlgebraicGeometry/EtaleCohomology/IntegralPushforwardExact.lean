module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrim
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyB
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralQuasiFinitePushforward

/-!
# Direct image along an integral morphism of schemes

Let `f : X ⟶ Y` be an integral morphism of schemes — a finite morphism, for instance. This file
proves [Stacks, Tag 04C2]: direct image along the induced morphism of small étale sites carries
surjections to surjections, both on sheaves of sets and on abelian sheaves; the counit
`f^{-1} f_* F ⟶ F` of the inverse-image/direct-image adjunction is surjective for every abelian
sheaf `F` on `X_étale`; direct image `Ab(X_étale) ⥤ Ab(Y_étale)` is faithful and reflects
injections and surjections; and that functor is exact.

## The shape of the argument

An integral morphism has property (B), by [Stacks, Tag 04DR], and preservation of surjections of
sheaves of sets is the conclusion of [Stacks, Tag 04DO] for a morphism with property (B).

The abelian case is transported from the set-valued one along the forgetful functor: a morphism of
abelian sheaves is epimorphic exactly when it is locally surjective, local surjectivity is a
property of the underlying morphism of sheaves of sets, and the underlying sheaf of sets of a
direct image is the direct image of the underlying sheaf of sets, both being restriction along the
base-change functor `Y_étale ⥤ X_étale`, `V ↦ X ×_Y V`.

Surjectivity of the counit, faithfulness, and reflection of injections and surjections on abelian
sheaves hold for every integral morphism by [Stacks, Tag 04C9].

Exactness is then formal: direct image is a right adjoint, so it preserves finite limits and is
therefore additive; an additive functor between abelian categories which preserves kernels and
epimorphisms preserves homology, hence also finite colimits.

## Main results

All of the following concern an integral morphism of schemes `f : X ⟶ Y`.

* `Stacks.EtaleCohomology.smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom` and
  `Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom` —
  direct image carries surjections to surjections, on sheaves of sets and on abelian sheaves.
* `Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom` — direct image of
  abelian sheaves is an exact functor.
* `Stacks.EtaleCohomology.smallEtalePushforwardAb_properties_of_isIntegralHom` — the four
  assertions of [Stacks, Tag 04C2] together.

## Implementation notes

The small étale site of `X : Scheme.{u}` has objects in `Type (u + 1)`, so `Ab.{u + 1}` is the
category of coefficients for which `Ab(X_étale)` is the category of abelian sheaves on it, and
`Type (u + 1)` the corresponding category of coefficients for sheaves of sets. Preservation of
surjections of sheaves of sets needs no sheafification and is stated for an arbitrary `Type v`;
the bundled statement of the tag uses the canonical choice `Type (u + 1)`.

Surjections of sheaves are the epimorphisms and injections the monomorphisms, so the assertions
about surjections and injections are about `Functor.PreservesEpimorphisms`,
`Functor.ReflectsEpimorphisms` and `Functor.ReflectsMonomorphisms`, and exactness of a functor
between abelian categories is preservation of both finite limits and finite colimits.

## References

* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 04C9](https://stacks.math.columbia.edu/tag/04C9)
* [Stacks Project, Tag 04DO](https://stacks.math.columbia.edu/tag/04DO)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- For an integral morphism of schemes `f : X ⟶ Y`, direct image
`f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` carries surjections of sheaves of sets to surjections.

An integral morphism has property (B) by [Stacks, Tag 04DR], which is the hypothesis of
[Stacks, Tag 04DO]. -/
public theorem smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v) (smallEtaleTopology Y)
      (smallEtaleTopology X)).PreservesEpimorphisms :=
  smallEtalePushforward_preservesEpimorphisms_of_hasPropertyB f (hasPropertyB_of_isIntegralHom f)

/-- For an integral morphism of schemes `f : X ⟶ Y`, direct image
`f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` carries surjections of abelian sheaves to surjections.

A morphism of abelian sheaves is epimorphic exactly when it is locally surjective, and local
surjectivity is a property of the underlying morphism of sheaves of sets. Since the underlying
sheaf of sets of a direct image is the direct image of the underlying sheaf of sets, the statement
reduces to its set-valued counterpart. -/
public theorem smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    (smallEtalePushforwardAb f).PreservesEpimorphisms := by
  constructor
  intro F G φ hφ
  have hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} φ).2 hφ
  have hset' : Epi (((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Y) (smallEtaleTopology X)).map
      ((sheafCompose (smallEtaleTopology X) (forget Ab.{u + 1})).map φ)) :=
    (smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom f).preserves _
  have hforget : Epi ((sheafCompose (smallEtaleTopology Y) (forget Ab.{u + 1})).map
      ((smallEtalePushforwardAb f).map φ)) := hset'
  have hlocforget : Sheaf.IsLocallySurjective
      ((sheafCompose (smallEtaleTopology Y) (forget Ab.{u + 1})).map
        ((smallEtalePushforwardAb f).map φ)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hforget
  have : Sheaf.IsLocallySurjective ((smallEtalePushforwardAb f).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (smallEtaleTopology Y) _).2 hlocforget
  exact Sheaf.epi_of_isLocallySurjective _

/-- For an integral morphism of schemes `f : X ⟶ Y`, direct image
`f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` is an exact functor.

Direct image is a right adjoint, so it preserves finite limits and is therefore additive; it
preserves epimorphisms because `f` is integral; and an additive functor between abelian categories
which preserves kernels and epimorphisms preserves homology, hence finite colimits as well. -/
public theorem smallEtalePushforwardAb_exact_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    exactFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1})
      (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (smallEtalePushforwardAb f) := by
  have hra : (smallEtalePushforwardAb f).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb f⟩⟩
  have hadd : (smallEtalePushforwardAb f).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hepi : (smallEtalePushforwardAb f).PreservesEpimorphisms :=
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom f
  have hhom := Functor.preservesHomology_of_preservesEpis_and_kernels (smallEtalePushforwardAb f)
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- **Stacks Project, Tag 04C2.** Let `f : X ⟶ Y` be an integral morphism of schemes — a finite
morphism, for instance. Then

1. `f_{small, *}` transforms surjections into surjections, on sheaves of sets and on abelian
   sheaves,
2. the counit `f^{-1} f_* F ⟶ F` is surjective for every abelian sheaf `F` on `X_étale`,
3. `f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` is faithful and reflects injections and
   surjections, and
4. `f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` is exact.

The seven conjuncts are, in order: part (1) on sheaves of sets, part (1) on abelian sheaves,
part (2), the three assertions of part (3), and part (4). -/
@[stacks 04C2]
public theorem smallEtalePushforwardAb_properties_of_isIntegralHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegralHom f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (u + 1)) (smallEtaleTopology Y)
        (smallEtaleTopology X)).PreservesEpimorphisms ∧
      (smallEtalePushforwardAb f).PreservesEpimorphisms ∧
      (∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
          Epi ((smallEtaleAdjunctionAb f).counit.app F)) ∧
        (smallEtalePushforwardAb f).Faithful ∧
          (smallEtalePushforwardAb f).ReflectsMonomorphisms ∧
            (smallEtalePushforwardAb f).ReflectsEpimorphisms ∧
              exactFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1})
                (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (smallEtalePushforwardAb f) :=
  have h := smallEtalePushforwardAb_properties_of_isIntegralHom_or_locallyQuasiFinite f
    (Or.inl inferInstance)
  ⟨smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom f,
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom f, h.1, h.2.1, h.2.2.1,
    h.2.2.2, smallEtalePushforwardAb_exact_of_isIntegralHom f⟩

end Stacks.EtaleCohomology

end
