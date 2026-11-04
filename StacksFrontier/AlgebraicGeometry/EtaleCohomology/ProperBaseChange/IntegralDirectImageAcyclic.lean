module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.CategoryTheory.Functor.Derived.LocalizationLeftKanExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Acyclicity of the direct image along an integral morphism, in the unbounded derived category

Let `f : X ⟶ Y` be an integral morphism of schemes — a finite morphism, for instance. Direct
image of abelian sheaves on the small étale sites is then an exact functor, so it has no higher
right derived functors and, what the unbounded theory needs, its **total** right derived functor
is the degreewise functor itself: the derived-functor unit of `Rf_*` is invertible and
`Rf_* = f_*` on the whole of `D(X_étale)`, with no boundedness condition on the complex.

The content is already in the library at the coefficients `Ab.{u + 1}`
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom` and
`Stacks.EtaleCohomology.isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom`). What is
added here is the same content at the coefficients `AddCommGrpCat.{max (u + 1) v}` in which the
proper base change development is written, and — new at either coefficients — the unbounded
identification of `Rf_*` with the degreewise direct image. The bounded below identification of
the right derived functor of an exact functor with the degreewise functor is
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso`; the statements here are its unbounded
counterparts for the direct image, and they are what identifies the derived base change map
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` with an underived comparison.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImageIso_of_isIntegralHom` — the
  identification `Rf_* ≅ f_*` of functors on the unbounded derived categories.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDirectImage_preservesEpimorphisms_of_isIntegralHom` —
  direct image carries surjections of abelian sheaves to surjections.
* `Stacks.EtaleCohomology.preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom` and
  `Stacks.EtaleCohomology.etaleAbelianDirectImage_preservesHomology_of_isIntegralHom` — direct
  image is exact, hence preserves homology.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom` —
  `R^q f_* F = 0` for `q ≥ 1`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom` — the
  derived-functor unit of the unbounded `Rf_*` is an isomorphism.

## Implementation notes

Preservation of epimorphisms is read off from its counterpart for sheaves of sets, which is
already stated for an arbitrary coefficient universe: a morphism of abelian sheaves is
epimorphic exactly when it is locally surjective, local surjectivity is a property of the
underlying morphism of sheaves of sets, and the underlying sheaf of sets of a direct image is
the direct image of the underlying sheaf of sets. This is the proof of the `Ab.{u + 1}` case
verbatim, with the coefficient universe left free.

The unbounded unit is handled by
`CategoryTheory.Functor.isIso_of_isRightDerivedFunctor_of_inverts`: the derived-functor unit of a
right derived functor is invertible as soon as the functor being derived already inverts the
quasi-isomorphisms, and degreewise direct image followed by the localization does invert them,
because it is isomorphic to the localization followed by the functor
`CategoryTheory.Functor.mapDerivedCategory` induced by the exact direct image. No K-injective
resolution is chosen anywhere, and nothing is assumed about the complex.

The identification of `Rf_*` with the degreewise functor is then the composite of that unit with
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, descended along the localization; the
descent is legitimate because both sides are left Kan extensions of the same functor, by
`CategoryTheory.Functor.isLeftKanExtension_of_isIso_of_isLocalization`.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- **Stacks 04C2, part (1), at the coefficients of the proper base change development.** For an
integral morphism of schemes `f : X ⟶ Y` — a finite morphism, for instance — direct image
`f_* : Ab(X_étale) ⥤ Ab(Y_étale)` carries surjections of abelian sheaves with values in
`AddCommGrpCat.{max (u + 1) v}` to surjections.

A morphism of abelian sheaves is epimorphic exactly when it is locally surjective, and local
surjectivity is a property of the underlying morphism of sheaves of sets. Since the underlying
sheaf of sets of a direct image is the direct image of the underlying sheaf of sets, the
statement reduces to its set-valued counterpart, which is stated for an arbitrary coefficient
universe. -/
@[stacks 04C2 "part (1) for abelian sheaves, at the coefficients of proper base change"]
public theorem etaleAbelianDirectImage_preservesEpimorphisms_of_isIntegralHom
    (f : X ⟶ Y) [IsIntegralHom f] :
    (etaleAbelianDirectImage.{u, v} f).PreservesEpimorphisms := by
  have hset :
      ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).PreservesEpimorphisms :=
    smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom f
  constructor
  intro F G φ hφ
  have hloc : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max (u + 1) v} φ).2 hφ
  have hset' : Epi (((smallEtaleBaseChange f).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X)).map
      ((sheafCompose (smallEtaleTopology X)
        (forget AddCommGrpCat.{max (u + 1) v})).map φ)) :=
    hset.preserves _
  have hforget : Epi ((sheafCompose (smallEtaleTopology Y)
      (forget AddCommGrpCat.{max (u + 1) v})).map
      ((etaleAbelianDirectImage.{u, v} f).map φ)) := hset'
  have hlocforget : Sheaf.IsLocallySurjective
      ((sheafCompose (smallEtaleTopology Y) (forget AddCommGrpCat.{max (u + 1) v})).map
        ((etaleAbelianDirectImage.{u, v} f).map φ)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hforget
  have : Sheaf.IsLocallySurjective ((etaleAbelianDirectImage.{u, v} f).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (smallEtaleTopology Y) _).2 hlocforget
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Stacks 04C2, part (2), at the coefficients of the proper base change development.** For an
integral morphism `f : X ⟶ Y`, direct image of abelian sheaves on the small étale sites
preserves finite colimits.

Direct image is a right adjoint, so it preserves finite limits and is therefore additive; it
preserves epimorphisms because `f` is integral; and an additive functor between abelian
categories which preserves kernels and epimorphisms preserves homology, hence finite colimits
as well. -/
@[stacks 04C2 "part (2) for abelian sheaves, at the coefficients of proper base change"]
public instance preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom
    (f : X ⟶ Y) [IsIntegralHom f] :
    PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) := by
  have hepi : (etaleAbelianDirectImage.{u, v} f).PreservesEpimorphisms :=
    etaleAbelianDirectImage_preservesEpimorphisms_of_isIntegralHom.{u, v} f
  have hhom :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (etaleAbelianDirectImage.{u, v} f)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- For an integral morphism `f : X ⟶ Y`, direct image of abelian sheaves on the small étale
sites preserves homology: it is additive, preserves kernels as a right adjoint, and preserves
epimorphisms because `f` is integral. -/
public theorem etaleAbelianDirectImage_preservesHomology_of_isIntegralHom
    (f : X ⟶ Y) [IsIntegralHom f] :
    (etaleAbelianDirectImage.{u, v} f).PreservesHomology := by
  have hepi : (etaleAbelianDirectImage.{u, v} f).PreservesEpimorphisms :=
    etaleAbelianDirectImage_preservesEpimorphisms_of_isIntegralHom.{u, v} f
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- **Stacks 03QP, part (2), at the coefficients of the proper base change development.** The
positive higher direct images of an abelian sheaf along an integral morphism of schemes vanish:
an integral morphism — a finite morphism, for instance — is acyclic for étale cohomology.

Direct image is exact, and applying an exact functor degreewise to an injective resolution
gives a resolution again, so the homology of the image complex vanishes in positive degrees. -/
@[stacks 03QP "part (2) at the coefficients of proper base change",
  sga "4 VIII 5.5" "more general",
  sga "4 VIII 5.6",
  sga "4 Vbis 4.3.4",
  sga "4 XII 5.3bis" "special case",
  sga "4 XIV 1.11" "partial",
  sga "4 XVII 4.3.1" "special case",
  sga "4½ Arcata 2.3.6"]
public theorem isZero_rightDerived_etaleAbelianDirectImage_of_isIntegralHom
    (f : X ⟶ Y) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) (hq : 0 < q) :
    IsZero (((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj F) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have hhom : (etaleAbelianDirectImage.{u, v} f).PreservesHomology :=
    etaleAbelianDirectImage_preservesHomology_of_isIntegralHom.{u, v} f
  exact Stacks.RightDerivedTransport.isZero_rightDerived_succ_of_preservesHomology _ n F

section Unbounded

variable (f : X ⟶ Y) [IsIntegralHom f]

/-- Degreewise direct image along an integral morphism, followed by the localization onto the
derived category of the target, inverts the quasi-isomorphisms. Direct image being exact, that
composite is isomorphic to the localization followed by the functor
`CategoryTheory.Functor.mapDerivedCategory` induced by it, and a localization functor inverts
the quasi-isomorphisms by definition. -/
private theorem pushforwardToDerivedCategory_isInvertedBy :
    (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).IsInvertedBy
      (etaleAbelianPushforwardToDerivedCategory.{u, v} f) := by
  have hcol : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f
  intro K L φ hφ
  have hQ : IsIso (DerivedCategory.Qh.map φ) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)) φ hφ
  have hmap : IsIso ((DerivedCategory.Qh ⋙
      (etaleAbelianDirectImage.{u, v} f).mapDerivedCategory).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff
    (etaleAbelianDirectImage.{u, v} f).mapDerivedCategoryFactorsh φ).1 hmap

/-- **The unbounded derived direct image along an integral morphism is the degreewise direct
image.** For an integral morphism of schemes `f : X ⟶ Y` — a finite morphism, for instance — the
derived-functor unit comparing degreewise direct image with `Rf_*` is an isomorphism.

The unit of a right derived functor is invertible as soon as the functor being derived already
inverts the quasi-isomorphisms, and degreewise direct image followed by the localization does so
because direct image is exact. Nothing is assumed about the complex: this is a statement on the
whole of the unbounded derived category, not on complexes bounded below. -/
public theorem isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom :
    IsIso (etaleAbelianDerivedDirectImageUnit.{u, v} f) :=
  Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (etaleAbelianDerivedDirectImage.{u, v} f) (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    (pushforwardToDerivedCategory_isInvertedBy.{u, v} f)

/-- **The identification `Rf_* ≅ f_*` on unbounded derived categories, for `f` integral.** Both
functors are left Kan extensions of degreewise direct image along the localization of the
homotopy category of unbounded complexes: the derived direct image by construction, and the
functor induced by the exact direct image because its structural comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an isomorphism. -/
public def etaleAbelianDerivedDirectImageIso_of_isIntegralHom :
    etaleAbelianDerivedDirectImage.{u, v} f ≅
      (etaleAbelianDirectImage.{u, v} f).mapDerivedCategory :=
  haveI : PreservesFiniteColimits (etaleAbelianDirectImage.{u, v} f) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, v} f
  haveI : IsIso (etaleAbelianDerivedDirectImageUnit.{u, v} f) :=
    isIso_etaleAbelianDerivedDirectImageUnit_of_isIntegralHom.{u, v} f
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ))
    (DerivedCategory.Qh ⋙ etaleAbelianDerivedDirectImage.{u, v} f)
    (DerivedCategory.Qh ⋙ (etaleAbelianDirectImage.{u, v} f).mapDerivedCategory)
    (etaleAbelianDerivedDirectImage.{u, v} f)
    ((etaleAbelianDirectImage.{u, v} f).mapDerivedCategory)
    ((asIso (etaleAbelianDerivedDirectImageUnit.{u, v} f)).symm ≪≫
      (etaleAbelianDirectImage.{u, v} f).mapDerivedCategoryFactorsh.symm)

end Unbounded

end Stacks.EtaleCohomology

end
