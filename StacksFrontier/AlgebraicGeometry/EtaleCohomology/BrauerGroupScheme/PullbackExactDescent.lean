module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatSurjectiveModuleDescent
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the pullback of sheaves of modules, and descent along an étale covering

The Brauer group of a scheme is built from sheaves of `𝒪_S`-algebras and their pullbacks, in the
spelling of `Stacks.EtaleCohomology.BrauerScheme`: `ModuleSheaf S` for the sheaves of
`𝒪_S`-modules carrying the tensor product sheaf of [Stacks, Tag 01CA], `modulePullback φ` for
the inverse image along a morphism of schemes, and `AlgebraSheaf S` and `algebraPullback φ` for
the monoid objects and their pullback. The exactness and descent properties of that pullback are
already proved elsewhere in the library, but at the spelling `AlgebraicGeometry.Scheme.Modules`
and `AlgebraicGeometry.Scheme.Modules.pullback`. This file restates them for `ModuleSheaf` and
`modulePullback`, and adds the two statements the Azumaya theory needs and which are not
available in that form anywhere: that the pullback along a flat morphism commutes with the image
of a morphism, and that isomorphy and finite local freeness descend along an étale covering.

The identification `modulePullback φ = Scheme.Modules.pullback φ` is `rfl`
(`modulePullback_eq_schemeModulesPullback`), so none of this is new mathematics; what it buys is
that a consumer working in `Stacks.EtaleCohomology.BrauerScheme` can apply the statements without
re-deriving the identification each time, and that the descent statements are available for a
whole covering family rather than for a single flat surjection.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.modulePullback_eq_schemeModulesPullback`: the pullback
  functor of this namespace is `AlgebraicGeometry.Scheme.Modules.pullback`.
* `Stacks.EtaleCohomology.BrauerScheme.preservesFiniteLimits_modulePullback` and
  `Stacks.EtaleCohomology.BrauerScheme.preservesFiniteColimits_modulePullback`: **the pullback
  of sheaves of modules along a flat morphism is exact** — right exact for any morphism, being a
  left adjoint, and left exact for a flat one.
* `Stacks.EtaleCohomology.BrauerScheme.preservesMonomorphisms_modulePullback`: the pullback
  along a flat morphism preserves monomorphisms.
* `Stacks.EtaleCohomology.BrauerScheme.modulePullbackImageIso`: **the pullback along a flat
  morphism commutes with images**, `φ^*(im f) ≅ im (φ^* f)`, together with
  `Stacks.EtaleCohomology.BrauerScheme.modulePullbackImageIso_hom_comp_ι` and
  `Stacks.EtaleCohomology.BrauerScheme.map_factorThruImage_comp_modulePullbackImageIso_hom`,
  which say that it is compatible with the image factorisation on both sides.
* `Stacks.EtaleCohomology.BrauerScheme.isIso_of_isIso_modulePullback_family`: **isomorphy of a
  morphism of sheaves of modules descends along a jointly surjective family of flat
  morphisms.**
* `Stacks.EtaleCohomology.BrauerScheme.isIso_of_isIso_modulePullback_cover` and
  `Stacks.EtaleCohomology.BrauerScheme.isIso_of_isIso_algebraPullback_cover`: **isomorphy
  descends along an étale covering**, for morphisms of sheaves of modules and for morphisms of
  sheaves of algebras.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_of_etale_cover`: **finite local
  freeness of a quasi-coherent sheaf of modules descends along an étale covering**, Tag 05B2
  specialised to the étale topology.

## Implementation notes

**Why the image statement is not `CategoryTheory.Abelian.PreservesImage.iso`.** Mathlib's
`CategoryTheory.Abelian.PreservesImage.iso` compares `Abelian.image`, the kernel of the
cokernel, whereas the statements here are about `CategoryTheory.Limits.image`, the image of the
strong-epi-mono factorisation, which is the one the monoidal and locally-free machinery of this
namespace uses. The two agree in an abelian category, but the comparison is itself an
isomorphism one would have to insert. Instead `modulePullbackImageIso` is built directly from
`CategoryTheory.Limits.image.isoStrongEpiMono`: the pullback carries the image factorisation
`f = factorThruImage f ≫ image.ι f` to a factorisation of `φ^* f` whose first factor is epi
(the pullback is right exact, being a left adjoint, and in an abelian category an epi is a
strong epi) and whose second factor is mono (the pullback is left exact because `φ` is flat), and
in a category with strong-epi-mono factorisations such a factorisation is *the* image
factorisation up to a unique isomorphism. The two characterising lemmas are then exactly the two
triangles of that uniqueness.

**The descent statements are stalkwise, not a new descent argument.**
`isIso_of_isIso_modulePullback_family` is
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_of_flat_surjective` with the single
flat surjection replaced by a jointly surjective family: the proof is unchanged, because the
only use of surjectivity there is to produce one point above the given point of `S`, and a
jointly surjective family produces one in some member. No disjoint union of the family has to be
formed, which is what makes the family version worth stating — the étale coverings the Azumaya
condition is phrased with are families, and their disjoint union need not be a scheme in the
same universe.

`isFiniteLocallyFree_of_etale_cover`, by contrast, is a genuine descent theorem, and it is not
reproved: `AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover` is Tag 05B2 for an fpqc
covering, and an étale covering is an fpqc covering by
`AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage` (Tag 022C). An
`AlgebraicGeometry.Scheme.Cover` is a `CategoryTheory.Precoverage.ZeroHypercover`, i.e. a family
together with membership of the presieve it generates in the precoverage, so the comparison of
precoverages transports the cover itself: the same family with the fpqc membership proof.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 0A2J](https://stacks.math.columbia.edu/tag/0A2J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {T S : Scheme.{u}}

/-- The pullback of sheaves of modules of this namespace is the pullback functor
`AlgebraicGeometry.Scheme.Modules.pullback` of the library: `ModuleSheaf S` and `S.Modules` are
the same type, and the two functors are the same term. This is the identification every
statement below rests on. -/
theorem modulePullback_eq_schemeModulesPullback (φ : T ⟶ S) :
    modulePullback φ = Scheme.Modules.pullback φ :=
  rfl

/-- **The pullback of sheaves of modules along a flat morphism of schemes is left exact.** On
underlying ringed spaces it is the module pullback of a flat morphism of ringed spaces, whose
stalks are flat ring maps. -/
theorem preservesFiniteLimits_modulePullback (φ : T ⟶ S) [AlgebraicGeometry.Flat φ] :
    PreservesFiniteLimits (modulePullback φ) :=
  AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat φ

/-- **The pullback of sheaves of modules along any morphism of schemes is right exact**, being a
left adjoint — the right adjoint is the pushforward. -/
theorem preservesFiniteColimits_modulePullback (φ : T ⟶ S) :
    PreservesFiniteColimits (modulePullback φ) :=
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback φ

/-- The pullback of sheaves of modules along a flat morphism of schemes preserves
monomorphisms, being left exact. -/
theorem preservesMonomorphisms_modulePullback (φ : T ⟶ S) [AlgebraicGeometry.Flat φ] :
    (modulePullback φ).PreservesMonomorphisms :=
  let := preservesFiniteLimits_modulePullback φ
  inferInstance

/-- The pullback of sheaves of modules along any morphism of schemes preserves epimorphisms,
being right exact. -/
theorem preservesEpimorphisms_modulePullback (φ : T ⟶ S) :
    (modulePullback φ).PreservesEpimorphisms :=
  let := preservesFiniteColimits_modulePullback φ
  inferInstance

section Image

variable {M N : ModuleSheaf S}

/-- **The pullback along a flat morphism of schemes commutes with images**,
`φ^*(im f) ≅ im (φ^* f)`.

The pullback carries the image factorisation `f = factorThruImage f ≫ image.ι f` to a
factorisation of `φ^* f` whose first factor is a strong epimorphism — the pullback is right
exact, and in an abelian category every epimorphism is strong — and whose second factor is a
monomorphism, because the pullback is left exact for a flat `φ`. In a category with
strong-epi-mono factorisations such a factorisation is the image factorisation up to a unique
isomorphism, and this is that isomorphism. -/
def modulePullbackImageIso (φ : T ⟶ S) [AlgebraicGeometry.Flat φ] (f : M ⟶ N) :
    (modulePullback φ).obj (image f) ≅ image ((modulePullback φ).map f) :=
  letI := preservesMonomorphisms_modulePullback φ
  letI := preservesEpimorphisms_modulePullback φ
  letI : Mono ((modulePullback φ).map (image.ι f)) := (modulePullback φ).map_mono _
  letI : Epi ((modulePullback φ).map (factorThruImage f)) := (modulePullback φ).map_epi _
  letI : StrongEpi ((modulePullback φ).map (factorThruImage f)) := strongEpi_of_epi _
  image.isoStrongEpiMono ((modulePullback φ).map (factorThruImage f))
    ((modulePullback φ).map (image.ι f)) (by rw [← Functor.map_comp, image.fac])

/-- The comparison `φ^*(im f) ≅ im (φ^* f)` is compatible with the inclusion of the image: it
carries the inclusion of `im (φ^* f)` back to the pullback of the inclusion of `im f`. -/
@[reassoc (attr := simp)]
theorem modulePullbackImageIso_hom_comp_ι (φ : T ⟶ S) [AlgebraicGeometry.Flat φ] (f : M ⟶ N) :
    (modulePullbackImageIso φ f).hom ≫ image.ι ((modulePullback φ).map f) =
      (modulePullback φ).map (image.ι f) :=
  let := preservesMonomorphisms_modulePullback φ
  let := preservesEpimorphisms_modulePullback φ
  let : Mono ((modulePullback φ).map (image.ι f)) := (modulePullback φ).map_mono _
  let : Epi ((modulePullback φ).map (factorThruImage f)) := (modulePullback φ).map_epi _
  let : StrongEpi ((modulePullback φ).map (factorThruImage f)) := strongEpi_of_epi _
  image.isoStrongEpiMono_hom_comp_ι _ _ _

/-- The comparison `φ^*(im f) ≅ im (φ^* f)` is compatible with the factorisation through the
image: it carries the pullback of the factorisation of `f` to the factorisation of `φ^* f`. -/
@[reassoc (attr := simp)]
theorem map_factorThruImage_comp_modulePullbackImageIso_hom (φ : T ⟶ S)
    [AlgebraicGeometry.Flat φ] (f : M ⟶ N) :
    (modulePullback φ).map (factorThruImage f) ≫ (modulePullbackImageIso φ f).hom =
      factorThruImage ((modulePullback φ).map f) := by
  rw [← cancel_mono (image.ι ((modulePullback φ).map f)), Category.assoc,
    modulePullbackImageIso_hom_comp_ι, ← Functor.map_comp, image.fac, image.fac]

end Image

/-- **Isomorphy of a morphism of sheaves of modules descends along a jointly surjective family
of flat morphisms.** If `g` becomes an isomorphism after pullback to every member of a family of
flat morphisms whose images cover `S`, then `g` is an isomorphism.

Isomorphy is detected on stalks, and a point of `S` is the image of a point of some member of
the family; there the stalk of `g` is injective and surjective because the stalk of the pullback
of `g` is, the stalk of a flat morphism being a faithfully flat ring map. -/
@[ega "IV 2.2.7" "partial"]
theorem isIso_of_isIso_modulePullback_family {I : Type*} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, AlgebraicGeometry.Flat (f i)]
    (hsurj : ∀ x : S, ∃ i, x ∈ Set.range (f i)) {M N : ModuleSheaf S} (g : M ⟶ N)
    (h : ∀ i, IsIso ((modulePullback (f i)).map g)) : IsIso g := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap g).2 fun x => ?_
  obtain ⟨i, x₁, rfl⟩ := hsurj x
  have hx₁ := (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    ((Scheme.Modules.pullback (f i)).map g)).1 (h i) x₁
  exact ⟨(AlgebraicGeometry.injective_stalkMap_modulePullback_iff (f i) g x₁).1 hx₁.1,
    (AlgebraicGeometry.surjective_stalkMap_modulePullback_iff (f i) g x₁).1 hx₁.2⟩

/-- **Isomorphy of a morphism of sheaves of modules descends along an étale covering.** An
`AlgebraicGeometry.Scheme.Cover` at `AlgebraicGeometry.Scheme.etalePrecoverage` is jointly
surjective with étale members (`Stacks.EtaleCohomology.BrauerScheme.etaleCover_spec`), and an
étale morphism is flat, so this is
`Stacks.EtaleCohomology.BrauerScheme.isIso_of_isIso_modulePullback_family`. -/
theorem isIso_of_isIso_modulePullback_cover (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    {M N : ModuleSheaf S} (g : M ⟶ N)
    (h : ∀ i, IsIso ((modulePullback (𝒰.f i)).map g)) : IsIso g :=
  have (i : 𝒰.I₀) : AlgebraicGeometry.Etale (𝒰.f i) := (etaleCover_spec 𝒰).2 i
  isIso_of_isIso_modulePullback_family 𝒰.f (etaleCover_spec 𝒰).1 g h

/-- **Isomorphy of a morphism of sheaves of algebras descends along an étale covering.** The
forgetful functor from monoid objects reflects isomorphisms, and the underlying morphism of
sheaves of modules of `(algebraPullback φ).map g` is `(modulePullback φ).map g.hom`, so this
reduces to `Stacks.EtaleCohomology.BrauerScheme.isIso_of_isIso_modulePullback_cover`. -/
theorem isIso_of_isIso_algebraPullback_cover (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    {A B : AlgebraSheaf S} (g : A ⟶ B)
    (h : ∀ i, IsIso ((algebraPullback (𝒰.f i)).map g)) : IsIso g := by
  have hhom : IsIso g.hom := by
    refine isIso_of_isIso_modulePullback_cover 𝒰 g.hom fun i => ?_
    have := h i
    exact inferInstanceAs (IsIso ((algebraPullback (𝒰.f i)).map g).hom)
  have : IsIso ((Mon.forget (ModuleSheaf S)).map g) := hhom
  exact isIso_of_reflects_iso g (Mon.forget (ModuleSheaf S))

/-- **Finite local freeness of a quasi-coherent sheaf of `𝒪_S`-modules descends along an étale
covering**: Tag 05B2 for an étale covering. Every étale covering family is an fpqc covering
family (Tag 022C,
`AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage`), so the same family of morphisms
with the transported membership proof is an fpqc cover, and
`AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover` applies to it. -/
@[ega "IV 2.5.2" "Clause (iii)"]
theorem isFiniteLocallyFree_of_etale_cover {M : ModuleSheaf S}
    (hM : SheafOfModules.IsQuasicoherent.{u, u, u} M)
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((modulePullback (𝒰.f i)).obj M)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover (hqc := hM) M
    { I₀ := 𝒰.I₀
      X := 𝒰.X
      f := 𝒰.f
      mem₀ := AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage _ 𝒰.mem₀ } h

end Stacks.EtaleCohomology.BrauerScheme

end

end
