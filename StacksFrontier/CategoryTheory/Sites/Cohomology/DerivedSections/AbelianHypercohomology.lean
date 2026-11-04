module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Hypercohomology of abelian sheaves on a site

Let `C` be a small category, `J` a Grothendieck topology on `C` and `U` an object of `C`.
Taking sections over `U` is an additive functor `Γ(U, -) : Sh(J, Ab) ⥤ Ab`, and the category of
abelian sheaves has enough injectives, so that functor has a right derived functor

`RΓ(U, -) : D⁺(Sh(J, Ab)) ⥤ D⁺(Ab)`

on bounded below derived categories. This file introduces that functor under the name
`Stacks.Cohomology.derivedSectionsPlus`, defines the hypercohomology groups
`H^n(U, K) = H^n(RΓ(U, K))` of a bounded below complex of abelian sheaves, and records the
formal properties of hypercohomology that a dévissage argument consumes: it is a triangulated
functor, it agrees with the cohomology of a single sheaf, it vanishes below the bound of `K`,
it has a long exact sequence for every distinguished triangle, and it is contravariant in the
object of the site.

The analogous theory for sheaves of *modules* on a ringed site already exists in
`StacksFrontier/CategoryTheory/Sites/Cohomology/HypercohomologyEdge/`, which builds unbounded
derived sections `Stacks.Cohomology.HypercohomologyEdge.derivedSections` and from them the
hypercohomology edge morphism `H^q(U, K) ⟶ Γ(U, H^q(K))`. This module is the abelian-sheaf
counterpart of the *first half* of that development — the functor and its formal properties —
and not a duplicate of its edge-morphism theory: nothing here compares hypercohomology with the
sections of a cohomology sheaf.

## Main definitions

* `Stacks.Cohomology.derivedSectionsPlus`: the right derived functor `RΓ(U, -)` of sections
  over `U`, on bounded below derived categories of abelian sheaves.
* `Stacks.Cohomology.hypercohomologyFunctor` and `Stacks.Cohomology.hypercohomology`: the
  degree-`n` hypercohomology over `U`, as a functor on `D⁺(Sh(J, Ab))` and on objects.
* `Stacks.Cohomology.hypercohomologyδ`: the connecting morphism
  `H^{n₀}(U, T₃) ⟶ H^{n₁}(U, T₁)` of a distinguished triangle `T`.
* `Stacks.Cohomology.sectionsRestrictionOnHomotopy`,
  `Stacks.Cohomology.derivedSectionsPlusRestriction` and
  `Stacks.Cohomology.hypercohomologyRestriction`: the restriction maps along a morphism
  `f : V ⟶ U` of the site, on bounded below homotopy categories, on derived sections and on
  hypercohomology.
* `Stacks.Cohomology.hypercohomologyRestriction_app_singleFunctor`: at a sheaf placed in degree
  `0`, restriction on hypercohomology is restriction on sheaf cohomology.

## Main results

* `Stacks.Cohomology.isTriangulated_derivedSectionsPlus` and
  `Stacks.Cohomology.derivedSectionsPlus_map_distinguished`: `RΓ(U, -)` is an exact functor of
  triangulated categories, so it preserves distinguished triangles.
* `Stacks.Cohomology.hypercohomologySingleFunctorIso` and
  `Stacks.Cohomology.hypercohomologySingleIso`: hypercohomology of a single sheaf placed in
  degree `0` is the sheaf cohomology `Stacks.sheafCohomology`, naturally in the sheaf.
* `Stacks.Cohomology.isZero_hypercohomology_of_isGE`: hypercohomology vanishes below the bound.
* `Stacks.Cohomology.hypercohomology_exact₁`, `hypercohomology_exact₂`,
  `hypercohomology_exact₃` and `Stacks.Cohomology.exact_composableArrows₅`: the long exact
  sequence of a distinguished triangle.
* `Stacks.Cohomology.epi_hypercohomology_map_mor₁_iff`,
  `mono_hypercohomology_map_mor₁_iff`, `epi_hypercohomology_map_mor₂_iff` and
  `mono_hypercohomology_map_mor₂_iff`: the four criteria the long exact sequence provides for a
  morphism in it to be epi or mono.

## Implementation notes

Nothing in this file carries a Stacks attribute: this is infrastructure. The statements that
the Stacks Project makes in this vicinity — Tag 013R on the cohomology of abelian sheaves on a
site, Tag 072W and Tag 0D6H on the derived functors available there — are about other objects,
and the content of Tag 0159 (the right derived functor on `D⁺` is triangulated) and Tag 05TC
(it moves cohomology to the right) is already carried by
`CategoryTheory.Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus` and
`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`. What is new here is only the
specialization of the general machinery to `Γ(U, -)` on abelian sheaves, in a spelling that the
change-of-topology arguments can quote.

For that reason the two inputs are *reused* rather than reproved: triangulatedness is
`Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus`, which packages the Tag 0159
statement above together with the shift compatibility
`Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus` of the right derived functor; and the
comparison with sheaf cohomology is `Stacks.DerivedIndexing.rightDerivedIso`, the natural
isomorphism between Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` and the
`ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`. Because `derivedSectionsPlus` is a
reducible abbreviation for `CategoryTheory.Functor.rightDerivedFunctorPlus`, these transfer by
definitional unfolding and the comparison of item four is an application of the natural
isomorphism, with no gluing isomorphism in the statement.

The long exact sequence is not built by hand. The functor `RΓ(U, -)` is triangulated, so it
carries a distinguished triangle of `D⁺(Sh(J, Ab))` to a distinguished triangle of `D⁺(Ab)`,
and `DerivedCategory.Plus.homologyFunctor Ab 0` is a homological functor equipped with a shift
sequence whose degree-`n` member is `DerivedCategory.Plus.homologyFunctor Ab n` *by
definition*. Mathlib's homological-functor API (`CategoryTheory.Functor.homologySequenceδ` and
the exactness and epi/mono lemmas around it) therefore applies verbatim, and the statements
below are its specializations, written in the `hypercohomology` spelling.

The comparison of `Stacks.Cohomology.hypercohomologyRestriction` with
`Stacks.sheafCohomologyRestriction` at a single sheaf is
`Stacks.Cohomology.hypercohomologyRestriction_app_singleFunctor`. The restriction map on
hypercohomology is obtained from the universal property of right derivation
(`CategoryTheory.Functor.rightDerivedNatTrans`), whereas `Stacks.sheafCohomologyRestriction` is
`CategoryTheory.NatTrans.rightDerived`, which is computed on chosen injective resolutions;
identifying the two is exactly the naturality of `Stacks.DerivedIndexing.rightDerivedIso` in the
functor variable, `Stacks.DerivedIndexing.rightDerivedIso_hom_naturality`. No gluing enters the
proof: `Stacks.Cohomology.derivedSectionsPlusRestriction` and
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` of the restriction of sections are the
same term, both being `CategoryTheory.Functor.rightDerivedNatTrans` of the same datum.

## References

* [Stacks Project, Tag 013R](https://stacks.math.columbia.edu/tag/013R)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Functoriality

variable (U : C)

/-- **Derived sections over an object of a site**, `RΓ(U, -) : D⁺(Sh(J, Ab)) ⥤ D⁺(Ab)`: the
right derived functor on bounded below derived categories of the additive functor "sections
over `U`" of [Stacks, Tag 013R]. -/
abbrev derivedSectionsPlus :
    DerivedCategory.Plus (Sheaf J Ab.{max u v}) ⥤ DerivedCategory.Plus Ab.{max u v} :=
  ((sheafSections J Ab.{max u v}).obj (op U)).rightDerivedFunctorPlus

/-- Derived sections commute with the shift, by the universal property of right derivation. -/
instance commShiftDerivedSectionsPlus : (derivedSectionsPlus J U).CommShift ℤ :=
  Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus _

/-- **Derived sections are an exact functor of triangulated categories**, [Stacks, Tag 0159]
applied to the functor "sections over `U`". -/
instance isTriangulated_derivedSectionsPlus : (derivedSectionsPlus J U).IsTriangulated :=
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus _

/-- Derived sections carry a distinguished triangle of bounded below complexes of abelian
sheaves to a distinguished triangle of bounded below complexes of abelian groups, [Stacks,
Tag 0159]. -/
theorem derivedSectionsPlus_map_distinguished
    (T : Triangle (DerivedCategory.Plus (Sheaf J Ab.{max u v}))) (hT : T ∈ distTriang _) :
    (derivedSectionsPlus J U).mapTriangle.obj T ∈ distTriang (DerivedCategory.Plus Ab.{max u v}) :=
  (derivedSectionsPlus J U).map_distinguished T hT

/-- **Degree-`n` hypercohomology over `U` as a functor** on the bounded below derived category
of abelian sheaves, `K ↦ H^n(U, K)`: the degree-`n` cohomology of derived sections. For a
single sheaf in degree `0` this is the cohomology of [Stacks, Tag 013R]. -/
abbrev hypercohomologyFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf J Ab.{max u v}) ⥤ Ab.{max u v} :=
  derivedSectionsPlus J U ⋙ DerivedCategory.Plus.homologyFunctor Ab.{max u v} n

/-- **Degree-`n` hypercohomology over `U`** of a bounded below complex of abelian sheaves,
`H^n(U, K)`, [Stacks, Tag 015A]. -/
abbrev hypercohomology (n : ℤ) (K : DerivedCategory.Plus (Sheaf J Ab.{max u v})) : Ab.{max u v} :=
  (hypercohomologyFunctor J U n).obj K

end Functoriality

section SingleSheaf

variable (U : C)

/-- **Hypercohomology of a single sheaf is sheaf cohomology**, naturally in the sheaf: the
composite of placing an abelian sheaf in degree `0` with degree-`n` hypercohomology over `U` is
the `n`-th right derived functor of sections over `U` in the sense of [Stacks, Tag 013R]. This
is the comparison of the two indexings of the right derived functors, [Stacks, Tag 015A]. -/
def hypercohomologySingleFunctorIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor (Sheaf J Ab.{max u v}) 0 ⋙
        hypercohomologyFunctor J U (n : ℤ) ≅
      ((sheafSections J Ab.{max u v}).obj (op U)).rightDerived n :=
  (Stacks.DerivedIndexing.rightDerivedIso _ n).symm

/-- Degree-`n` hypercohomology over `U` of an abelian sheaf placed in degree `0` is its `n`-th
sheaf cohomology over `U`, [Stacks, Tag 013R]. -/
def hypercohomologySingleIso (M : Sheaf J Ab.{max u v}) (n : ℕ) :
    hypercohomology J U (n : ℤ) ((DerivedCategory.Plus.singleFunctor _ 0).obj M) ≅
      sheafCohomology J M U n :=
  (hypercohomologySingleFunctorIso J U n).app M

end SingleSheaf

section Vanishing

variable (U : C)

/-- **Hypercohomology vanishes below the bound**: if the cohomology of `K` lives in degrees
`≥ a` then `H^n(U, K) = 0` for `n < a`. Derived sections move cohomology to the right,
[Stacks, Tag 05TC]. -/
theorem isZero_hypercohomology_of_isGE (K : DerivedCategory.Plus (Sheaf J Ab.{max u v})) (a n : ℤ)
    [K.IsGE a] (hn : n < a) : IsZero (hypercohomology J U n K) :=
  have := Functor.isGE_rightDerivedFunctorPlus_obj ((sheafSections J Ab.{max u v}).obj (op U)) K a
  DerivedCategory.Plus.isZero_homology_of_isGE _ a n hn

end Vanishing

section LongExactSequence

variable (U : C) (T : Triangle (DerivedCategory.Plus (Sheaf J Ab.{max u v})))

/-- **The connecting morphism of the long exact sequence of hypercohomology**,
`H^{n₀}(U, T₃) ⟶ H^{n₁}(U, T₁)` for a triangle `T` of bounded below complexes of abelian
sheaves and `n₀ + 1 = n₁`. It is the connecting morphism of the homological functor
`DerivedCategory.Plus.homologyFunctor Ab 0` at the image triangle, [Stacks, Tag 015A]. -/
def hypercohomologyδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    hypercohomology J U n₀ T.obj₃ ⟶ hypercohomology J U n₁ T.obj₁ :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequenceδ
    ((derivedSectionsPlus J U).mapTriangle.obj T) n₀ n₁ h

/-- The connecting morphism is natural in the triangle, [Stacks, Tag 015A]. -/
@[reassoc]
theorem hypercohomologyδ_naturality {T T' : Triangle (DerivedCategory.Plus (Sheaf J Ab.{max u v}))}
    (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (hypercohomologyFunctor J U n₀).map φ.hom₃ ≫ hypercohomologyδ J U T' n₀ n₁ h =
      hypercohomologyδ J U T n₀ n₁ h ≫ (hypercohomologyFunctor J U n₁).map φ.hom₁ :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequenceδ_naturality
    ((derivedSectionsPlus J U).mapTriangle.map φ) n₀ n₁ h

variable (hT : T ∈ distTriang (DerivedCategory.Plus (Sheaf J Ab.{max u v})))

include hT

/-- Two consecutive morphisms of the long exact sequence of a distinguished triangle compose to
zero, in the same degree, [Stacks, Tag 015A]. -/
@[reassoc]
theorem hypercohomology_comp (n : ℤ) :
    (hypercohomologyFunctor J U n).map T.mor₁ ≫ (hypercohomologyFunctor J U n).map T.mor₂ = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_comp _
    (derivedSectionsPlus_map_distinguished J U T hT) n

/-- The second morphism of the long exact sequence followed by the connecting morphism is
zero, [Stacks, Tag 015A]. -/
@[reassoc]
theorem comp_hypercohomologyδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (hypercohomologyFunctor J U n₀).map T.mor₂ ≫ hypercohomologyδ J U T n₀ n₁ h = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).comp_homologySequenceδ _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- The connecting morphism followed by the first morphism of the long exact sequence is
zero, [Stacks, Tag 015A]. -/
@[reassoc]
theorem hypercohomologyδ_comp (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    hypercohomologyδ J U T n₀ n₁ h ≫ (hypercohomologyFunctor J U n₁).map T.mor₁ = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequenceδ_comp _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- **Exactness of the long exact sequence at `H^{n₁}(U, T₁)`**: the sequence
`H^{n₀}(U, T₃) ⟶ H^{n₁}(U, T₁) ⟶ H^{n₁}(U, T₂)` is exact, [Stacks, Tag 015A]. -/
theorem hypercohomology_exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (hypercohomologyδ_comp J U T hT n₀ n₁ h)).Exact :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_exact₁ _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- **Exactness of the long exact sequence at `H^n(U, T₂)`**: the sequence
`H^n(U, T₁) ⟶ H^n(U, T₂) ⟶ H^n(U, T₃)` is exact, [Stacks, Tag 015A]. -/
theorem hypercohomology_exact₂ (n : ℤ) :
    (ShortComplex.mk _ _ (hypercohomology_comp J U T hT n)).Exact :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_exact₂ _
    (derivedSectionsPlus_map_distinguished J U T hT) n

/-- **Exactness of the long exact sequence at `H^{n₀}(U, T₃)`**: the sequence
`H^{n₀}(U, T₂) ⟶ H^{n₀}(U, T₃) ⟶ H^{n₁}(U, T₁)` is exact, [Stacks, Tag 015A]. -/
theorem hypercohomology_exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _ (comp_hypercohomologyδ J U T hT n₀ n₁ h)).Exact :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_exact₃ _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- The first morphism of the long exact sequence is an epimorphism in degree `n` exactly when
the second one vanishes there, [Stacks, Tag 015A]. -/
theorem epi_hypercohomology_map_mor₁_iff (n : ℤ) :
    Epi ((hypercohomologyFunctor J U n).map T.mor₁) ↔
      (hypercohomologyFunctor J U n).map T.mor₂ = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_epi_shift_map_mor₁_iff _
    (derivedSectionsPlus_map_distinguished J U T hT) n

/-- The first morphism of the long exact sequence is a monomorphism in degree `n₁` exactly when
the connecting morphism into that degree vanishes, [Stacks, Tag 015A]. -/
theorem mono_hypercohomology_map_mor₁_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Mono ((hypercohomologyFunctor J U n₁).map T.mor₁) ↔ hypercohomologyδ J U T n₀ n₁ h = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_mono_shift_map_mor₁_iff _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- The second morphism of the long exact sequence is an epimorphism in degree `n₀` exactly
when the connecting morphism out of that degree vanishes, [Stacks, Tag 015A]. -/
theorem epi_hypercohomology_map_mor₂_iff (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Epi ((hypercohomologyFunctor J U n₀).map T.mor₂) ↔ hypercohomologyδ J U T n₀ n₁ h = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_epi_shift_map_mor₂_iff _
    (derivedSectionsPlus_map_distinguished J U T hT) n₀ n₁ h

/-- The second morphism of the long exact sequence is a monomorphism in degree `n` exactly when
the first one vanishes there, [Stacks, Tag 015A]. -/
theorem mono_hypercohomology_map_mor₂_iff (n : ℤ) :
    Mono ((hypercohomologyFunctor J U n).map T.mor₂) ↔
      (hypercohomologyFunctor J U n).map T.mor₁ = 0 :=
  (DerivedCategory.Plus.homologyFunctor Ab.{max u v} 0).homologySequence_mono_shift_map_mor₂_iff _
    (derivedSectionsPlus_map_distinguished J U T hT) n

/-- **The long exact sequence of hypercohomology of a distinguished triangle**: the six-term
window

  `H^{n₀}(U, T₁) ⟶ H^{n₀}(U, T₂) ⟶ H^{n₀}(U, T₃) ⟶ H^{n₁}(U, T₁) ⟶ H^{n₁}(U, T₂) ⟶
   H^{n₁}(U, T₃)`

is exact, with `Stacks.Cohomology.hypercohomologyδ` as the connecting morphism. Letting `n₀`
range over `ℤ` these windows overlap in two consecutive arrows, so they are the long exact
sequence in all degrees, [Stacks, Tag 015A]. -/
theorem exact_composableArrows₅ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ComposableArrows.mk₅ ((hypercohomologyFunctor J U n₀).map T.mor₁)
      ((hypercohomologyFunctor J U n₀).map T.mor₂) (hypercohomologyδ J U T n₀ n₁ h)
      ((hypercohomologyFunctor J U n₁).map T.mor₁)
      ((hypercohomologyFunctor J U n₁).map T.mor₂)).Exact :=
  ComposableArrows.exact_of_δ₀ (hypercohomology_exact₂ J U T hT n₀).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (hypercohomology_exact₃ J U T hT n₀ n₁ h).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (hypercohomology_exact₁ J U T hT n₀ n₁ h).exact_toComposableArrows
        (hypercohomology_exact₂ J U T hT n₁).exact_toComposableArrows))

end LongExactSequence

section MorphismOfTriangles

variable (U : C)

/-- **A class killed in the long exact sequence lifts along a morphism of triangles which is
surjective on the third terms.** Let `φ : T ⟶ T'` be a morphism of distinguished triangles of
bounded below complexes of abelian sheaves such that `H^{n₀}(U, φ₃)` is surjective, and let
`x ∈ H^{n₁}(U, T'₁)` be killed by `H^{n₁}(U, T'₁) ⟶ H^{n₁}(U, T'₂)`, where `n₀ + 1 = n₁`. Then
`x` comes from `H^{n₁}(U, T₁)` along `φ₁`.

By exactness `x` is the connecting image of a class of `H^{n₀}(U, T'₃)`, which lifts to
`H^{n₀}(U, T₃)`, and the connecting morphisms commute with `φ`. -/
theorem exists_hypercohomology_map_hom₁_eq
    {T T' : Triangle (DerivedCategory.Plus (Sheaf J Ab.{max u v}))}
    (hT' : T' ∈ distTriang _) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (hepi : Epi ((hypercohomologyFunctor J U n₀).map φ.hom₃))
    (x : hypercohomology J U n₁ T'.obj₁)
    (hx : (hypercohomologyFunctor J U n₁).map T'.mor₁ x = 0) :
    ∃ y : hypercohomology J U n₁ T.obj₁, (hypercohomologyFunctor J U n₁).map φ.hom₁ y = x := by
  obtain ⟨y, hy⟩ :=
    (ShortComplex.ab_exact_iff _).1 (hypercohomology_exact₁ J U T' hT' n₀ n₁ h) x hx
  obtain ⟨y', hy'⟩ := (AddCommGrpCat.epi_iff_surjective _).1 hepi y
  refine ⟨hypercohomologyδ J U T n₀ n₁ h y', ?_⟩
  rw [← hy, ← hy', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    hypercohomologyδ_naturality]

end MorphismOfTriangles

section Restriction

variable {U V : C} (f : V ⟶ U)

/-- Restriction along `f : V ⟶ U` on bounded below homotopy categories: the natural
transformation of functors `K⁺(Sh(J, Ab)) ⥤ D⁺(Ab)` induced degreewise by the restriction map
`Γ(U, -) ⟶ Γ(V, -)` on sections, [Stacks, Tag 013R]. -/
def sectionsRestrictionOnHomotopy :
    ((sheafSections J Ab.{max u v}).obj (op U)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      ((sheafSections J Ab.{max u v}).obj (op V)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh :=
  Functor.whiskerRight
    (Functor.mapHomotopyCategoryPlusNatTrans ((sheafSections J Ab.{max u v}).map f.op))
    DerivedCategory.Plus.Qh

/-- **Restriction of derived sections along a morphism of the site**,
`RΓ(U, -) ⟶ RΓ(V, -)` for `f : V ⟶ U`: the morphism of right derived functors induced by
restriction of sections, [Stacks, Tag 015A]. -/
def derivedSectionsPlusRestriction : derivedSectionsPlus J U ⟶ derivedSectionsPlus J V :=
  Functor.rightDerivedNatTrans _ _
    ((sheafSections J Ab.{max u v}).obj (op U)).rightDerivedFunctorPlusUnit
    ((sheafSections J Ab.{max u v}).obj (op V)).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso (Sheaf J Ab.{max u v})) (sectionsRestrictionOnHomotopy J f)

/-- The defining equation of the restriction of derived sections: it is the unique morphism of
derived functors compatible with restriction of sections on bounded below homotopy categories,
[Stacks, Tag 015A]. -/
@[reassoc]
theorem derivedSectionsPlusRestriction_fac :
    ((sheafSections J Ab.{max u v}).obj (op U)).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (derivedSectionsPlusRestriction J f) =
      sectionsRestrictionOnHomotopy J f ≫
        ((sheafSections J Ab.{max u v}).obj (op V)).rightDerivedFunctorPlusUnit :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- **Restriction on hypercohomology along a morphism of the site**,
`H^n(U, -) ⟶ H^n(V, -)` for `f : V ⟶ U`, natural in the bounded below complex, [Stacks,
Tag 015A]. -/
def hypercohomologyRestriction (n : ℤ) :
    hypercohomologyFunctor J U n ⟶ hypercohomologyFunctor J V n :=
  Functor.whiskerRight (derivedSectionsPlusRestriction J f)
    (DerivedCategory.Plus.homologyFunctor Ab.{max u v} n)

/-- **Restriction on hypercohomology is restriction on sheaf cohomology**, at an abelian sheaf
placed in degree `0`: the square formed by `Stacks.sheafCohomologyRestriction`, the restriction
`Stacks.Cohomology.hypercohomologyRestriction` of hypercohomology and the comparison
`Stacks.Cohomology.hypercohomologySingleIso` of the two commutes, [Stacks, Tag 015A].

Both restriction maps are induced by the same natural transformation `Γ(U, -) ⟶ Γ(V, -)` of
functors on abelian sheaves, the first by Mathlib's `CategoryTheory.NatTrans.rightDerived` on
chosen injective resolutions and the second by the universal property of right derivation on
bounded below derived categories. They agree because the comparison of the two indexings of the
right derived functors is natural in the functor variable,
`Stacks.DerivedIndexing.rightDerivedIso_hom_naturality`. -/
theorem hypercohomologyRestriction_app_singleFunctor (n : ℕ) (M : Sheaf J Ab.{max u v}) :
    sheafCohomologyRestriction J f n M ≫ (hypercohomologySingleIso J V M n).inv =
      (hypercohomologySingleIso J U M n).inv ≫
        (hypercohomologyRestriction J f (n : ℤ)).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf J Ab.{max u v}) 0).obj M) :=
  NatTrans.congr_app
    (Stacks.DerivedIndexing.rightDerivedIso_hom_naturality
      ((sheafSections J Ab.{max u v}).map f.op) n) M

/-- Restriction on hypercohomology is natural in the bounded below complex of abelian
sheaves, [Stacks, Tag 015A]. -/
@[reassoc]
theorem hypercohomologyRestriction_naturality (n : ℤ)
    {K L : DerivedCategory.Plus (Sheaf J Ab.{max u v})} (g : K ⟶ L) :
    (hypercohomologyFunctor J U n).map g ≫ (hypercohomologyRestriction J f n).app L =
      (hypercohomologyRestriction J f n).app K ≫ (hypercohomologyFunctor J V n).map g :=
  (hypercohomologyRestriction J f n).naturality g

end Restriction

end Stacks.Cohomology
