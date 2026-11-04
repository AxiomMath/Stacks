module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Comp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01MZ in one statement

Let `𝒜`, `ℬ` and `𝒞` be nonnegatively graded rings, write `X = Proj 𝒜`, `Y = Proj ℬ` and
`Z = Proj 𝒞`, and let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be homomorphisms of graded rings. Tag
01MZ makes three assertions about the data `(U, r, θ)` of Tag 01MY attached to the composite
`ψ ∘ φ`: the domain of definition `U(ψ ∘ φ) ⊆ Z` is the inverse image under `r_ψ` of
`U(φ) ⊆ Y`, the morphism `r_{ψ ∘ φ}` is `r_φ ∘ r_ψ` restricted to that open, and the comparison
maps on the twists compose, `θ_ψ ∘ r_ψ^* θ_φ = θ_{ψ ∘ φ}`.

Each of the three is established separately —
`Stacks.AlgebraicGeometry.ProjTwistChain.mapDomain_comp`,
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.mapDomainCompIso_hom_mapHom` and
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.twistMap_comp` — and this file states all three
together, so that a single declaration says what the tag says.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.mapDomain_mapHom_twistMap_comp`: **the three
  assertions of Tag 01MZ in one statement.**

## Implementation notes

The three conjuncts are stated at the canonical isomorphism
`Stacks.AlgebraicGeometry.ProjTwistCompTwistMap.mapDomainCompIso : r_ψ⁻¹(U(φ)) ≅ U(ψ ∘ φ)`,
which is the first conjunct read as an isomorphism of schemes: the second and third conjuncts
are equalities of morphisms out of `r_ψ⁻¹(U(φ))` and of maps of modules pulled back along them,
so some identification of that open with `U(ψ ∘ φ)` has to appear in them. It is a definition
rather than a `let`, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjTwistCompTwistMap/Comp.lean`: with thirteen occurrences inside
the nine factors of the third conjunct, zeta-expanding it exhausts the kernel's budget.

The statement lives in its own module so that elaborating this second copy of the nine-factor
equation is elaborated on its own rather than within the budget of the file that proves it.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistCompFunctoriality
open Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w' w''

variable {A B C : Type u} {σ : Type w} {τ : Type w'} {υ : Type w''}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike υ C] [AddSubgroupClass υ C]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (𝒞 : ℕ → υ) [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **[Stacks, Tag 01MZ].** Let `𝒜`, `ℬ`, `𝒞` be nonnegatively graded rings, write
`X = Proj 𝒜`, `Y = Proj ℬ`, `Z = Proj 𝒞`, and let `φ : 𝒜 →+*ᵍ ℬ` and `ψ : ℬ →+*ᵍ 𝒞` be
homomorphisms of graded rings. Then `U(ψ ∘ φ) = r_ψ⁻¹(U(φ))`, the morphism
`r_{ψ ∘ φ} : U(ψ ∘ φ) ⟶ X` is `r_φ ∘ r_ψ|_{U(ψ ∘ φ)}`, and `θ_ψ ∘ r_ψ^* θ_φ = θ_{ψ ∘ φ}` on
every twist.

The three conjuncts are, in order:

1. **The domain of definition of the composite.** `U(ψ ∘ φ)`, an open of `Z`, is the image under
  the inclusion of `U(ψ)` of the open `r_ψ⁻¹(U(φ))` of `U(ψ)`. This is `mapDomain_comp`.
2. **The morphism of the composite.** Read through the canonical isomorphism
  `mapDomainCompIso : r_ψ⁻¹(U(φ)) ≅ U(ψ ∘ φ)` that the first conjunct supplies,
  `r_{ψ ∘ φ}` is the restriction `r_ψ|_{r_ψ⁻¹(U(φ))} : r_ψ⁻¹(U(φ)) ⟶ U(φ)` followed by `r_φ`.
  This is `mapDomainCompIso_hom_mapHom`.
3. **The comparison maps on the twists.** For every `n : ℤ`, Tag 01MY's comparison
  `θ_{ψ ∘ φ}` on the `n`-th twist, pulled back along the canonical isomorphism, is `θ_φ` pulled
  back along `r_ψ|_{r_ψ⁻¹(U(φ))}` followed by `θ_ψ` pulled back along the inclusion of
  `r_ψ⁻¹(U(φ))`, the pseudofunctoriality isomorphisms of the inverse image and the three
  identifications of composites of the first two conjuncts mediating between the two sides.
  This is `twistMap_comp`.

The source's data are the three graded rings and the two homomorphisms, and those are the only
binders here: every domain of definition is an arbitrary open, and `θ` is Tag 01MY's comparison
for an arbitrary homomorphism of nonnegatively graded rings. -/
@[stacks 01MZ "the tag's three assertions in one statement, for an arbitrary composable pair of
homomorphisms of nonnegatively graded rings: the domain of definition of the composite is the
inverse image under `r_ψ` of the domain of definition of `φ`, the morphism of the composite is
`r_φ ∘ r_ψ` restricted to that open, and the comparison maps on every twist compose",
  ega "II 2.8.4"]
public theorem mapDomain_mapHom_twistMap_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) :
    mapDomain 𝒜 𝒞 (ψ.comp φ) =
        (mapDomain ℬ 𝒞 ψ).ι ''ᵁ (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ) ∧
      (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom ≫ mapHom 𝒜 𝒞 (ψ.comp φ) =
        (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ) ≫ mapHom 𝒜 ℬ φ ∧
      ∀ n : ℤ,
        (Scheme.Modules.pullbackComp (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom
              (mapHom 𝒜 𝒞 (ψ.comp φ))).inv.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullback (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom).map
              (twistMap 𝒜 𝒞 (ψ.comp φ) n) ≫
            (Scheme.Modules.pullbackComp (mapDomainCompIso 𝒜 ℬ 𝒞 φ ψ).hom
              (mapDomain 𝒜 𝒞 (ψ.comp φ)).ι).hom.app (twistingSheaf 𝒞 n) =
          (Scheme.Modules.pullbackCongr
              (mapDomainCompIso_hom_mapHom 𝒜 ℬ 𝒞 φ ψ)).hom.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)
              (mapHom 𝒜 ℬ φ)).inv.app (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullback (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)).map
              (twistMap 𝒜 ℬ φ n) ≫
            (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ∣_ mapDomain 𝒜 ℬ φ)
              (mapDomain 𝒜 ℬ φ).ι).hom.app (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackCongr
              (morphismRestrict_ι (mapHom ℬ 𝒞 ψ) (mapDomain 𝒜 ℬ φ))).hom.app
                (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι
              (mapHom ℬ 𝒞 ψ)).inv.app (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullback (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι).map
              (twistMap ℬ 𝒞 ψ n) ≫
            (Scheme.Modules.pullbackComp (mapHom ℬ 𝒞 ψ ⁻¹ᵁ mapDomain 𝒜 ℬ φ).ι
              (mapDomain ℬ 𝒞 ψ).ι).hom.app (twistingSheaf 𝒞 n) ≫
            (Scheme.Modules.pullbackCongr
              (mapDomainCompIso_hom_ι 𝒜 ℬ 𝒞 φ ψ)).inv.app (twistingSheaf 𝒞 n) :=
  ⟨mapDomain_comp 𝒜 ℬ 𝒞 φ ψ, mapDomainCompIso_hom_mapHom 𝒜 ℬ 𝒞 φ ψ,
    fun n => twistMap_comp 𝒜 ℬ 𝒞 φ ψ n⟩

end Stacks.AlgebraicGeometry.ProjTwistCompTwistMap

end
