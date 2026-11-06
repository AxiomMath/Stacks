module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# The transitivity sequence of sheaves of differentials of algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ B` be morphisms of algebraic spaces over a scheme `S`.  Stacks 05Z8
attaches to them a canonical exact sequence
```
  f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0
```
of sheaves of `𝒪_X`-modules on the small étale site of `X`, whose first map is the comparison map
of Stacks 04CX for the square with top edge `f`, right edge `g`, left edge `f ≫ g` and bottom edge
the identity of `B`.

The first map is *not* built here.  It is the comparison map
`AlgebraicGeometry.Space.sheafOfDifferentialsMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean`, read at that square; this
file only names that instance of it.  The second map is constructed, not chosen: it is produced
from the universal property of a sheaf of differentials applied to an explicitly built
derivation, through `AlgebraicGeometry.Space.differentialsHomEquiv`.  Exactness is proved from
that same universal property throughout, with no passage to stalks: the claim is exactly that
`Ω_{X/Y}` is a *cokernel* of the first map, a cokernel is tested by morphisms out of the two
objects, and the universal property turns those into derivations.  Exactness at `Ω_{X/Y}` is the
statement that the second map is an epimorphism, and that is the uniqueness half of the same
universal property.

## Main definitions

* `AlgebraicGeometry.Space.relativeUniversalDerivation` is the universal `Y`-derivation
  `d_{X/Y}`, read as a `B`-derivation along the factorization of the structure map of `f ≫ g`
  through that of `f`, and `AlgebraicGeometry.Space.toRelativeDifferentials` is the canonical
  map `Ω_{X/B} ⟶ Ω_{X/Y}` it induces.
* `AlgebraicGeometry.Space.pullbackDifferentialsMap` is the first map of the transitivity
  sequence, `c_f : f^*Ω_{Y/B} ⟶ Ω_{X/B}`: the comparison map of Stacks 04CX at the square over
  the identity of `B`.
* `AlgebraicGeometry.Space.derivationOfCompEqZero` and
  `AlgebraicGeometry.Space.descOfCompEqZero` produce, from a morphism out of `Ω_{X/B}` that the
  first map annihilates, the `Y`-derivation it defines and the induced morphism out of
  `Ω_{X/Y}`, and `AlgebraicGeometry.Space.isColimitCokernelCoforkToRelativeDifferentials` says
  that `Ω_{X/Y}` is thereby a cokernel of `f^*Ω_{Y/B} ⟶ Ω_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.exists_structureSharpInverseImage_comp_factorization`: the structure
  map `(f ≫ g)♯ : (f ≫ g)⁻¹𝒪_B ⟶ 𝒪_X` factors through `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.  This is what makes
  `d_{X/Y}` a `B`-derivation.
* `AlgebraicGeometry.Space.toRelativeDifferentials_app_d`: the canonical map
  `Ω_{X/B} ⟶ Ω_{X/Y}` carries `d_{X/B}(t)` to `d_{X/Y}(t)`, and
  `AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext`: two morphisms out of a sheaf of
  differentials agreeing on universal differentials are equal.
* `AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff`: two morphisms out of
  `Ω_{X'/Y'}` agree after the comparison map of a commutative square exactly when they agree on
  `d_{X'/Y'}(f♯ s)` for every section `s` of `f⁻¹𝒪_X`.  This is the transposition across
  `f⁻¹ ⊣ f_*` that both remaining clauses of 05Z8 rest on;
  `AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff_structureSharpSet` is the same
  equivalence stopped at the direct-image side.
* `AlgebraicGeometry.Space.triangleDifferentials_epi`: **Stacks 05Z8**, exactness of
  `f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0` at `Ω_{X/Y}`: the canonical map `Ω_{X/B} ⟶ Ω_{X/Y}` is an
  epimorphism.
* `AlgebraicGeometry.Space.pullbackDifferentialsMap_comp_toRelativeDifferentials` and
  `AlgebraicGeometry.Space.triangleDifferentials_exact`: **Stacks 05Z8**, the other two clauses
  — the composite of the two maps is zero, and the short complex they form is exact at
  `Ω_{X/B}`.

## Implementation notes

The universal property of Stacks 04CT is used in the `Equiv` form
`AlgebraicGeometry.Space.differentialsHomEquiv` of
`StacksFrontier/AlgebraicGeometry/Spaces/DerivationsIntoDirectImage.lean`, not in the `∃!` form
`AlgebraicGeometry.Space.universalDerivation_isUniversal`: the latter cannot be used to
*construct* the second map without choosing a witness of an existence statement.

The second map is *not* built as the comparison map of the square with top edge the identity of
`X`, which is how the ringed-space analogue
`Stacks.Sheaves.RingedSpaceDifferentials.toRelativeDifferentials` proceeds; that route needs the
identification of `(𝟙 X)^*` with the identity functor.  It is built instead from the universal
property directly, as the unique morphism carrying `d_{X/B}(t)` to `d_{X/Y}(t)`, which is the
characterization the Stacks project names it by.  The input that makes `d_{X/Y}` a
`B`-derivation is the factorization of the structure map of `f ≫ g` through that of `f`; it is
obtained from the direct-image factorization
`AlgebraicGeometry.Space.inverseImageStructureSheafSection_comp` of Stacks 03G8 by transposing
across `(f ≫ g)⁻¹ ⊣ (f ≫ g)_*`, exactly as the square factorization of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSharpCompFactorization.lean` is.

### How the three clauses of Stacks 05Z8 are distributed

The tag has three clauses, and two declarations carry them: `triangleDifferentials_epi` is
exactness at the right term, and `triangleDifferentials_exact` is the composite being zero
together with exactness at `Ω_{X/B}`.  The same split, with the same two names, is what the
ringed-space analogue of Tag 0H79 in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedSpaceDifferentials.lean` does.

All three rest on one transposition, `sheafOfDifferentialsMap_comp_eq_iff`: two morphisms out of
`Ω_{X'/Y'}` agree after the comparison map of a square exactly when they agree on the image of
`d_{X'/Y'} ∘ f♯`.  It is proved from the characterizing property
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` of the comparison map, which
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap` supplies: naturality
of the hom-set bijection of `f^* ⊣ f_*` in the target and the universal property of `Ω_{X/Y}`
turn the equation into an identity of morphisms of *sheaves of sets* on the small étale site of
`X`, namely that `f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` followed by the direct image of `d_{X'/Y'} ∘ k₁` and of
`d_{X'/Y'} ∘ k₂` agree; and the two forms of the structure map are adjunct, so
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and
`AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage` carry that back and
forth to the inverse-image form `f♯ : f⁻¹𝒪_X ⟶ 𝒪_{X'}`, where the condition is read off on
sections of `f⁻¹𝒪_X`.  Both directions of that transport are available, which is what makes the
statement an equivalence; nothing here compares the two direct images of sheaves of modules, so
`AlgebraicGeometry.Space.modulePushforwardIso` is not used and no compiler option is raised.

With that in hand the composite being zero is the vanishing clause of `d_{X/Y}` itself, and the
cokernel property is the universal property of `Ω_{X/Y}` applied to
`AlgebraicGeometry.Space.derivationOfCompEqZero`, whose own vanishing clause is the
transposition read in the other direction.

Additivity of the direct image of sheaves of modules is not needed: the zero morphism is never
identified with `f_*` of the zero morphism, because the universal property is applied to the
zero morphism of `𝒪_{X'}`-modules directly, in the right-hand side of the transposition.

The exactness clause is stated as `CategoryTheory.ShortComplex.Exact` of the short complex of
the two maps; `AlgebraicGeometry.Space.isColimitCokernelCoforkToRelativeDifferentials`, the
cokernel colimit it is derived from, is the stronger statement and is available separately.

Everything is at the universes of the small étale site, `RingedSite.{u + 1, u, u}`, with modules
`Modules.{u, u}`; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean` for why the module universe
is not independent there.

## References

* [Stacks Project, Tag 05Z8](https://stacks.math.columbia.edu/tag/05Z8)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal property.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square, constructed in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMap.lean`.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the universal property
  of the sheaf of differentials as a bijection.
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79), the same sequence for
  morphisms of ringed spaces.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

section Presheaf

universe v₁ u₁ w

variable {C : Type u₁} [Category.{v₁} C]

/-- A factorization of the adjunct of `t` through `R.map α` gives a factorization of `t` itself
through `α`: naturality of the hom-set bijection in its right argument is all that is used.  The
statement is at an arbitrary adjunction so that the rewriting below is performed on small terms;
at the concrete ringed topoi of the applications it is not. -/
private theorem exists_transposeFactorizationAux {D : Type u₁} [Category.{v₁} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {Bb Bb' : D}
    (α : Bb' ⟶ Bb) (t : L.obj A ⟶ Bb) (fs : A ⟶ R.obj Bb)
    (ht : adj.homEquiv A Bb t = fs) (γ : A ⟶ R.obj Bb') (h : γ ≫ R.map α = fs) :
    ∃ ψ : L.obj A ⟶ Bb', t = ψ ≫ α := by
  refine ⟨(adj.homEquiv A Bb').symm γ, ?_⟩
  apply (adj.homEquiv A Bb).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, h, ht]

/-- Equal morphisms of sheaves of types have equal effects on every section.  Stated at an
arbitrary site so that the applications below, where the morphisms are large terms, do not
rewrite inside them. -/
private theorem congr_sections {J : GrothendieckTopology C} {A A' : Sheaf J (Type w)}
    {m m' : A ⟶ A'} (h : m = m') (U : Cᵒᵖ) (s : (Sheaf.sectionsFunctor J U).obj A) :
    (ConcreteCategory.hom ((Sheaf.sectionsFunctor J U).map m)) s =
      (ConcreteCategory.hom ((Sheaf.sectionsFunctor J U).map m')) s := by
  rw [h]

end Presheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Universal

variable {X Y : AlgebraicSpaces B S hS}

/-- Two morphisms of `𝒪_X`-modules out of `Ω_{X/Y}` which agree on the universal differential of
every local section of `𝒪_X` are equal: the uniqueness half of Stacks 04CT. -/
theorem sheafOfDifferentials_hom_ext (p : X ⟶ Y) {F : Modules.{u, u} B S hS X.1 X.2}
    {ψ₁ ψ₂ : sheafOfDifferentials B S hS p ⟶ F}
    (h : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U),
      (ψ₁.val.app U).hom ((universalDerivation B S hS p).d t) =
        (ψ₂.val.app U).hom ((universalDerivation B S hS p).d t)) :
    ψ₁ = ψ₂ := by
  apply (differentialsHomEquiv B S hS p F).injective
  rw [differentialsHomEquiv_apply, differentialsHomEquiv_apply]
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  exact h U t

/-- The morphism of `𝒪_X`-modules `Ω_{X/Y} ⟶ F` that the universal property of Stacks 04CT
attaches to a `Y`-derivation `D` carries the universal differential `d_{X/Y}(t)` of a local
section `t` of `𝒪_X` to `D(t)`.  This is the property that characterizes it. -/
theorem differentialsHomEquiv_symm_app_d (p : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (D : PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS p).hom)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    ((((differentialsHomEquiv B S hS p F).symm D).val).app U).hom
        ((universalDerivation B S hS p).d t) = D.d t :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    ((differentialsHomEquiv_apply B S hS p F
        ((differentialsHomEquiv B S hS p F).symm D)).symm.trans
      ((differentialsHomEquiv B S hS p F).apply_symm_apply D)) t

end Universal

section Triangle

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The inverse-image form of the structure map of a composite factors through the inverse-image
form of the structure map of its first factor: there is a homomorphism
`τ : (f ≫ g)⁻¹𝒪_B ⟶ f⁻¹𝒪_Y` of sheaves of commutative rings on the small étale site of `X` with
`(f ≫ g)♯ = τ ≫ f♯`.

This is `AlgebraicGeometry.Space.inverseImageStructureSheafSection_comp`, the direct-image
factorization of Stacks 03G8, transposed across the adjunction `(f ≫ g)⁻¹ ⊣ (f ≫ g)_*`.  Only
the existence of the factorization is transported, and naturality of the hom-set bijection in
its right argument suffices for that. -/
theorem exists_structureSharpInverseImage_comp_factorization (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ τ : inverseImageStructureSheaf B S hS (f ≫ g) ⟶ inverseImageStructureSheaf B S hS f,
      structureSharpInverseImage B S hS (f ≫ g) = τ ≫ structureSharpInverseImage B S hS f :=
  exists_transposeFactorizationAux
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom)
    (structureSharpInverseImage B S hS f) (structureSharpInverseImage B S hS (f ≫ g))
    (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharp (Equiv.apply_symm_apply _ _)
    (inverseImageStructureSheafSection B S hS f g)
    (inverseImageStructureSheafSection_comp B S hS f g)

/-- The universal `Y`-derivation `d_{X/Y}` read as a `B`-derivation: the same additive maps on
sections, with the vanishing clause taken along the structure map of `f ≫ g` instead of that of
`f`.  It vanishes there because that structure map factors through `f♯`. -/
noncomputable def relativeUniversalDerivation (f : X ⟶ Y) (g : Y ⟶ Z) :
    PresheafOfModulesOfCommRing.Derivation' (sheafOfDifferentials B S hS f).val
      (structureSharpInverseImage B S hS (f ≫ g)).hom where
  d := (universalDerivation B S hS f).d
  d_mul := (universalDerivation B S hS f).d_mul
  d_map := (universalDerivation B S hS f).d_map
  d_app {U} s := by
    obtain ⟨τ, hτ⟩ := exists_structureSharpInverseImage_comp_factorization B S hS f g
    have h : ((structureSharpInverseImage B S hS (f ≫ g)).hom.app U).hom s =
        ((structureSharpInverseImage B S hS f).hom.app U).hom ((τ.hom.app U).hom s) :=
      ConcreteCategory.congr_hom (congr_app (congrArg (fun z ↦ z.hom) hτ) U) s
    change (universalDerivation B S hS f).d
      (((structureSharpInverseImage B S hS (f ≫ g)).hom.app U).hom s) = 0
    rw [h]
    exact (universalDerivation B S hS f).d_app _

/-- The canonical map `Ω_{X/B} ⟶ Ω_{X/Y}` of the transitivity sequence of Stacks 05Z8: the
morphism of `𝒪_X`-modules corresponding, under the universal property of `Ω_{X/B}`, to the
universal `Y`-derivation read as a `B`-derivation. -/
noncomputable def toRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ Z) :
    sheafOfDifferentials B S hS (f ≫ g) ⟶ sheafOfDifferentials B S hS f :=
  (differentialsHomEquiv B S hS (f ≫ g) (sheafOfDifferentials B S hS f)).symm
    (relativeUniversalDerivation B S hS f g)

/-- The canonical map `Ω_{X/B} ⟶ Ω_{X/Y}` carries the universal differential `d_{X/B}(t)` of a
local section `t` of `𝒪_X` to its universal differential `d_{X/Y}(t)`.  This is the property the
Stacks project names the map by, and the map was constructed from it. -/
theorem toRelativeDifferentials_app_d (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    ((toRelativeDifferentials B S hS f g).val.app U).hom
        ((universalDerivation B S hS (f ≫ g)).d t) =
      (universalDerivation B S hS f).d t :=
  differentialsHomEquiv_symm_app_d B S hS (f ≫ g) (sheafOfDifferentials B S hS f)
    (relativeUniversalDerivation B S hS f g) U t

/-- A morphism out of `Ω_{X/Y}`, precomposed with the canonical map `Ω_{X/B} ⟶ Ω_{X/Y}`, sends
`d_{X/B}(t)` to the image of `d_{X/Y}(t)`. -/
private theorem toRelativeDifferentials_comp_app_d (f : X ⟶ Y) (g : Y ⟶ Z)
    {F : Modules.{u, u} B S hS X.1 X.2} (ψ : sheafOfDifferentials B S hS f ⟶ F)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    ((toRelativeDifferentials B S hS f g ≫ ψ).val.app U).hom
        ((universalDerivation B S hS (f ≫ g)).d t) =
      (ψ.val.app U).hom ((universalDerivation B S hS f).d t) := by
  show (ψ.val.app U).hom (((toRelativeDifferentials B S hS f g).val.app U).hom
    ((universalDerivation B S hS (f ≫ g)).d t)) = _
  rw [toRelativeDifferentials_app_d]

/-- **Stacks 05Z8**, exactness at the right term of the transitivity sequence
`f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0`: the canonical map `Ω_{X/B} ⟶ Ω_{X/Y}` is an epimorphism.

Two morphisms out of `Ω_{X/Y}` agreeing after it agree on every `d_{X/Y}(t)`, because
`d_{X/B}(t)` is carried to `d_{X/Y}(t)`, so they are equal by the uniqueness half of
Stacks 04CT. -/
@[stacks 05Z8 "exactness at the right term: the map to Ω_{X/Y} is an epimorphism", instance]
theorem triangleDifferentials_epi (f : X ⟶ Y) (g : Y ⟶ Z) :
    Epi (toRelativeDifferentials B S hS f g) where
  left_cancellation {F} ψ₁ ψ₂ e := by
    refine sheafOfDifferentials_hom_ext B S hS f fun U t ↦ ?_
    have h1 := congrArg (fun (k : sheafOfDifferentials B S hS (f ≫ g) ⟶ F) ↦
      (k.val.app U).hom ((universalDerivation B S hS (f ≫ g)).d t)) e
    rwa [toRelativeDifferentials_comp_app_d, toRelativeDifferentials_comp_app_d] at h1

end Triangle

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **The comparison map of a commutative square, tested on the direct-image side.**  Two
morphisms `k₁, k₂ : Ω_{X'/Y'} ⟶ N` of `𝒪_{X'}`-modules agree after the comparison map
`c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of Stacks 04CX exactly when the direct-image form
`f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` of the structure map followed by the direct image of `d_{X'/Y'} ∘ k₁` and
of `d_{X'/Y'} ∘ k₂` agree.

Everything is an equivalence: the hom-set bijection of `f^* ⊣ f_*` is one, the universal property
`AlgebraicGeometry.Space.differentialsHomEquiv` of `Ω_{X/Y}` is one, and the value of the
transpose of `c_f` on a universal differential is pinned by
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap`, which says it is
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom`, the composite `f_*d_{X'/Y'} ∘ f♯`
on underlying sheaves of sets. -/
theorem sheafOfDifferentialsMap_comp_eq_iff_structureSharpSet (f : X' ⟶ X) (p : X ⟶ Y)
    (p' : X' ⟶ Y') (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q)
    {N : Modules.{u, u} B S hS X'.1 X'.2} (k₁ k₂ : sheafOfDifferentials B S hS p' ⟶ N) :
    sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ k₁ =
        sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ k₂ ↔
      structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
          (universalDerivationHom B S hS p' ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k₁) =
        structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
          (universalDerivationHom B S hS p' ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k₂) := by
  have hpt (k : sheafOfDifferentials B S hS p' ⟶ N)
      (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
      ((((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p) N
            (sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ k)).val.app U).hom)
          ((universalDerivation B S hS p).d t) =
        ((smallEtaleDirectImage B S hS f).map
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k)).hom.app U
          ((pushforwardUniversalDerivationHom B S hS f p').hom.app U t) := by
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg _
      (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS f p p' q hcomm U t)
  have hcomp (k : sheafOfDifferentials B S hS p' ⟶ N) :
      structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map
          (universalDerivationHom B S hS p' ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k) =
        pushforwardUniversalDerivationHom B S hS f p' ≫
          (smallEtaleDirectImage B S hS f).map
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k) := by
    rw [Functor.map_comp]
    rfl
  rw [hcomp k₁, hcomp k₂]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine Sheaf.hom_ext_sections fun U t ↦ ?_
    have hm := congrArg (fun m ↦ (SheafOfModules.Hom.val
      ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p) N m)).app U) h
    exact (hpt k₁ U t).symm.trans
      ((congrArg (fun m ↦ (ModuleCat.Hom.hom m) ((universalDerivation B S hS p).d t)) hm).trans
        (hpt k₂ U t))
  · refine ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
      N).injective ?_
    refine (differentialsHomEquiv B S hS p
      ((modulePushforward B S hS f).obj N)).injective ?_
    refine PresheafOfModulesOfCommRing.Derivation.ext ?_
    ext U t
    exact (hpt k₁ U t).trans ((congr_sections h U t).trans (hpt k₂ U t).symm)

/-- Two morphisms `k₁, k₂ : Ω_{X'/Y'} ⟶ N` of `𝒪_{X'}`-modules agree after the comparison map
`c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of a commutative square exactly when they agree on the
differential `d_{X'/Y'}(f♯ s)` of every section pulled back along `f♯ : f⁻¹𝒪_X ⟶ 𝒪_{X'}`.

This is `AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff_structureSharpSet` carried
to the inverse-image form of the structure map.  The two forms are adjunct, by Stacks 03G8, and
both directions of the transport are available —
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and
`AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage` — so the
equivalence survives it.  On the inverse-image side the condition is pointwise: it is read off on
sections of `f⁻¹𝒪_X`, which is the form both remaining clauses of Stacks 05Z8 consume. -/
theorem sheafOfDifferentialsMap_comp_eq_iff (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (q : Y' ⟶ Y) (hcomm : f ≫ p = p' ≫ q) {N : Modules.{u, u} B S hS X'.1 X'.2}
    (k₁ k₂ : sheafOfDifferentials B S hS p' ⟶ N) :
    sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ k₁ =
        sheafOfDifferentialsMap B S hS f p p' q hcomm ≫ k₂ ↔
      ∀ (U : (SmallEtale B S hS X'.1)ᵒᵖ)
        (s : (inverseImageStructureSheaf B S hS f).obj.obj U),
        (k₁.val.app U).hom ((universalDerivation B S hS p').d
            (((structureSharpInverseImage B S hS f).hom.app U).hom s)) =
          (k₂.val.app U).hom ((universalDerivation B S hS p').d
            (((structureSharpInverseImage B S hS f).hom.app U).hom s)) :=
  (sheafOfDifferentialsMap_comp_eq_iff_structureSharpSet B S hS f p p' q hcomm k₁ k₂).trans
    ⟨fun h U s ↦
      congr_sections (structureSharpInverseImage_of_structureSharpSetComp B S hS f _ _ h) U s,
     fun h ↦ structureSharpSetComp_of_structureSharpInverseImage B S hS f _ _
      (Sheaf.hom_ext_sections fun U s ↦ h U s)⟩

end Square

section FirstMap

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The first map `f^*Ω_{Y/B} ⟶ Ω_{X/B}` of the transitivity sequence of Stacks 05Z8: the
comparison map of Stacks 04CX for the square with top edge `f : X ⟶ Y`, right edge `g : Y ⟶ B`,
left edge `f ≫ g` and bottom edge the identity of `B`. -/
noncomputable def pullbackDifferentialsMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullback B S hS f).obj (sheafOfDifferentials B S hS g) ⟶
      sheafOfDifferentials B S hS (f ≫ g) :=
  sheafOfDifferentialsMap B S hS f g (f ≫ g) (𝟙 Z) (by simp)

end FirstMap

section Exactness

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The two maps of the transitivity sequence of Stacks 05Z8 compose to zero: the canonical map
`Ω_{X/B} ⟶ Ω_{X/Y}` annihilates the image of `f^*Ω_{Y/B} ⟶ Ω_{X/B}`.

By `AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff` this is the statement that
`d_{X/Y}` and the zero map agree on the differential `d_{X/B}(f♯ s)` of every section pulled
back from `𝒪_Y`, and `AlgebraicGeometry.Space.toRelativeDifferentials_app_d` turns that into
`d_{X/Y}(f♯ s) = 0`, which is the vanishing clause of `d_{X/Y}` itself. -/
theorem pullbackDifferentialsMap_comp_toRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0 :=
  ((sheafOfDifferentialsMap_comp_eq_iff B S hS f g (f ≫ g) (𝟙 Z) (by simp)
    (toRelativeDifferentials B S hS f g) 0).mpr fun U s ↦
      (toRelativeDifferentials_app_d B S hS f g U _).trans
        (((universalDerivation B S hS f).d_app s).trans rfl)).trans Limits.comp_zero

/-- A morphism `b : Ω_{X/B} ⟶ W` of `𝒪_X`-modules annihilated by the first map of the
transitivity sequence defines a `Y`-derivation of `𝒪_X` with values in `W`: the same additive
maps on sections as the `B`-derivation `d_{X/B}` followed by `b`, with the vanishing clause
taken along `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` instead of along the structure map of `f ≫ g`.

Additivity and the Leibniz rule do not mention the base and are inherited verbatim.  The
vanishing clause is the one non-formal step, and it is exactly what the hypothesis says once
`AlgebraicGeometry.Space.sheafOfDifferentialsMap_comp_eq_iff` has transposed it: `b` kills
`d_{X/B}(f♯ s)` for every section `s` of `f⁻¹𝒪_Y`. -/
noncomputable def derivationOfCompEqZero (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : Modules.{u, u} B S hS X.1 X.2} (b : sheafOfDifferentials B S hS (f ≫ g) ⟶ W)
    (hb : pullbackDifferentialsMap B S hS f g ≫ b = 0) :
    PresheafOfModulesOfCommRing.Derivation' W.val (structureSharpInverseImage B S hS f).hom where
  d := ((universalDerivation B S hS (f ≫ g)).postcomp b.val).d
  d_mul := ((universalDerivation B S hS (f ≫ g)).postcomp b.val).d_mul
  d_map := ((universalDerivation B S hS (f ≫ g)).postcomp b.val).d_map
  d_app {U} s :=
    ((sheafOfDifferentialsMap_comp_eq_iff B S hS f g (f ≫ g) (𝟙 Z) (by simp) b 0).mp
      (hb.trans Limits.comp_zero.symm) U s).trans rfl

/-- The factorization through `Ω_{X/Y}` of a morphism `b : Ω_{X/B} ⟶ W` of `𝒪_X`-modules
annihilated by the first map of the transitivity sequence: the morphism attached by the
universal property of Stacks 04CT to the `Y`-derivation
`AlgebraicGeometry.Space.derivationOfCompEqZero`. -/
noncomputable def descOfCompEqZero (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : Modules.{u, u} B S hS X.1 X.2} (b : sheafOfDifferentials B S hS (f ≫ g) ⟶ W)
    (hb : pullbackDifferentialsMap B S hS f g ≫ b = 0) :
    sheafOfDifferentials B S hS f ⟶ W :=
  (differentialsHomEquiv B S hS f W).symm (derivationOfCompEqZero B S hS f g b hb)

/-- `AlgebraicGeometry.Space.descOfCompEqZero` is a factorization of `b` through the canonical
map `Ω_{X/B} ⟶ Ω_{X/Y}`. -/
theorem toRelativeDifferentials_comp_descOfCompEqZero (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : Modules.{u, u} B S hS X.1 X.2} (b : sheafOfDifferentials B S hS (f ≫ g) ⟶ W)
    (hb : pullbackDifferentialsMap B S hS f g ≫ b = 0) :
    toRelativeDifferentials B S hS f g ≫ descOfCompEqZero B S hS f g b hb = b := by
  refine sheafOfDifferentials_hom_ext B S hS (f ≫ g) fun U t ↦ ?_
  rw [toRelativeDifferentials_comp_app_d]
  exact differentialsHomEquiv_symm_app_d B S hS f W
    (derivationOfCompEqZero B S hS f g b hb) U t

/-- `Ω_{X/Y}`, with the canonical map out of `Ω_{X/B}`, is a cokernel of the first map
`f^*Ω_{Y/B} ⟶ Ω_{X/B}` of the transitivity sequence.

Existence of the factorization is `AlgebraicGeometry.Space.descOfCompEqZero`; its uniqueness is
the uniqueness half of Stacks 04CT in the form of
`AlgebraicGeometry.Space.triangleDifferentials_epi`. -/
noncomputable def isColimitCokernelCoforkToRelativeDifferentials (f : X ⟶ Y) (g : Y ⟶ Z) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (toRelativeDifferentials B S hS f g)
      (pullbackDifferentialsMap_comp_toRelativeDifferentials B S hS f g)) :=
  Limits.CokernelCofork.IsColimit.ofπ' _ _ fun {_} k hk ↦
    ⟨descOfCompEqZero B S hS f g k hk,
      toRelativeDifferentials_comp_descOfCompEqZero B S hS f g k hk⟩

/-- **Stacks 05Z8**, the two clauses of the transitivity sequence
`f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0` that concern its left half: the composite of the two maps
is zero, and the resulting short complex is exact at `Ω_{X/B}`.  Together with
`AlgebraicGeometry.Space.triangleDifferentials_epi`, which is exactness at `Ω_{X/Y}`, this is
the exactness of the whole sequence.

Both come from `AlgebraicGeometry.Space.isColimitCokernelCoforkToRelativeDifferentials`: the
cokernel cofork carries the vanishing of the composite, and
`CategoryTheory.ShortComplex.exact_of_g_is_cokernel` turns the colimit into exactness in the
middle.  The homology of the short complex is formed in the abelian category of `𝒪_X`-modules;
the instance that makes it abelian is `HasSheafify` for abelian sheaves on the small étale
site, which instance search does not find at the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite B S hS X.1 X.2).J` of the ringed site, exactly as
for `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify`. -/
@[stacks 05Z8 "the composite of the two maps is zero, and exactness at the middle term Ω_{X/B}"]
theorem triangleDifferentials_exact (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).Exact :=
  ⟨pullbackDifferentialsMap_comp_toRelativeDifferentials B S hS f g, by
    have : HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} := by
      show HasSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}
      infer_instance
    exact ShortComplex.exact_of_g_is_cokernel _
      (isColimitCokernelCoforkToRelativeDifferentials B S hS f g)⟩

end Exactness
end AlgebraicGeometry.Space

end
