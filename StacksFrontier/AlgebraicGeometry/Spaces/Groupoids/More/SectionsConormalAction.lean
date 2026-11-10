module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Sections
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos

/-!
# A section of a groupoid acts trivially on the conormal module

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be an
`R`-invariant closed subspace, and let `δ : U ⟶ R` be a section of the source which agrees with
the unit `e` on `U₀`.  Then `f = t ∘ δ : U ⟶ U` restricts to the identity on `U₀`, so it induces
an endomorphism of the conormal module `𝒞_{U₀/U}`, and that endomorphism is the identity.

The argument is the one of the source, run on the two stacked squares

```
U₀ --i--→ U        R₀ --j--→ R
|          |        |         |
d          δ, e     s₀, t₀    s, t
↓          ↓        ↓         ↓
R₀ --j--→ R        U₀ --i--→ U
```

where `R₀ = s⁻¹(U₀)` and `d` is the restriction of `δ` to `U₀`, which factors through `R₀`
because `s ∘ δ = id`.  Composing the left square with the square over `s` gives, in both the
`δ` and the `e` case, the same square over `id_U`; the conormal maps of the composites are
computed by the composition formula of [Stacks Project, Tag 04G2], part (3)
(`AlgebraicGeometry.Space.conormalMap_comp`), and since the conormal map of the square over `s`
is invertible — the square is a fibre product and `s` is flat, [Stacks Project, Tag 04CQ], which
is what the source's appeal to [Stacks Project, Tag 06BH] uses — the conormal maps of the two
left squares agree.  Composing the left squares with the square over `t` instead turns that
agreement into the assertion for `f = t ∘ δ`.

## Main results

* `AlgebraicGeometry.Space.conormalMap_congr_lower`: the conormal map of a square depends on
  the lower edge only through its value.
* `AlgebraicGeometry.Space.isIso_conormalMap_id`: the conormal map of the identity square is an
  isomorphism.
* `AlgebraicGeometry.Space.conormalMap_comp_of_spaces`: the composition formula for conormal maps
  of [Stacks Project, Tag 04G2], part (3), with the ambient algebraic spaces of its two lower
  closed subspaces handed over in arguments.
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso_hom_comp`: **Stacks 04CO, the
  functoriality in the étale source** — the identification of [Stacks Project, Tag 04CO] taken in
  two steps along `ψ` and `φ` is the identification taken in one step along `ψ ≫ φ`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.subspaceInclusion_comp_sectionTarget`: the
  morphism `f = t ∘ δ` restricts to the identity on `U₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.conormalMap_sectionTarget_eq_conormalMap_id`:
  **Stacks 0CKD**, the conormal map induced by `f = t ∘ δ` is the conormal map of the identity
  square.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.conormalMap_sectionTarget_comp_inv_eq_id`:
  **Stacks 0CKD**, the same statement read as `f` acting by the identity on the conormal module.

## Implementation notes

**The conormal map of the identity square, not the identity map.**  The conormal map of the
square with lower edge `f` goes `(id_{U₀})^*𝒞_{U₀/U} ⟶ 𝒞_{U₀/U}`, out of the inverse image of
the conormal module along the identity rather than out of the conormal module itself.  The
source's "is the identity map" is therefore read here as the equality with the conormal map of
the square whose lower edge is `id_U`, which is that canonical identification, and which is an
isomorphism by `AlgebraicGeometry.Space.isIso_conormalMap_id`;
`conormalMap_sectionTarget_comp_inv_eq_id` transports the statement across it and gets the
identity on the nose.

**Why the unit is `identityArrow` and not a field.**
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` stores its groupoid structure through the
pointwise groupoids at the test schemes rather than as a unit morphism, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow` of [Stacks Project, Tag 06K5] is
the morphism of algebraic spaces that recovers it; the membership `δ ∈ Γ₀` of the source is the
hypothesis `hδ` below, that `δ` and `identityArrow` agree after restriction to `U₀`.

**Generality.**  Flatness of the source `s` is the hypothesis `hs`, in the chartwise sense of
`AlgebraicGeometry.Space.IsFlat`.  Flatness of the target `t` and the hypothesis that `U` is a
first-order thickening of `U₀`, both in force in the source's section, are not needed by the
argument above and are not assumed.

**Why the functoriality of Stacks 04CO is hosted here, and why it is stated with the two-step
composite written out.**  The route to that clause reads both of its sides through
`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeFlat.lean` and then applies the
composition formula of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`.
That identification is strictly *downstream* of the file which constructs the isomorphism, so no
module in that neighbourhood can see both; this file is one of the few downstream of both, and it
is the one that already carries the transport lemmas for conormal maps of étale restriction
squares (`conormalMap_congr_lower`, `isIso_conormalMap_id`) and already consumes
`AlgebraicGeometry.Space.conormalMap_comp` at two stacked squares.

The clause is stated with the two-step composite written out rather than as an equation on
`AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`, and that is forced.  That definition's
body is elaborated in its own file *against its declared type*, and the two do not use one
spelling of the ambient space of the lower closed subspace: the declared type says
`(ψ ≫ φ)⁻¹(Z)`, the body's three factors say `ψ⁻¹(φ⁻¹(Z))`, and the implicit object and category
arguments of the composition `≫` are solved from the declared type while those of the factors are
solved from the factors.  A consumer outside that file cannot reproduce the mixture: taking the
ambient space from the factors reproduces the factors and not the composition, taking it from the
declared type reproduces the composition and not the factors, and supplying both — the ambient
space of the composition, of each factor and of the middle object each in its own argument, with
their values in heterogeneous equalities, which is the discipline of
`AlgebraicGeometry.Space.conormalMap_comp_of_spaces` applied once more — is accepted by the
elaborator only through the cast chain that `convert` builds, which the **kernel** then refuses
with `(kernel) deterministic timeout`.  At the default budget: the assembled term, the
composition-congruence bridge and all of their heterogeneous equalities elaborate and are
kernel-checked in about two seconds; `exact` of the bridged term against the opened goal exhausts
the budget at `whnf`; `convert ... using 1` reaches an `Iff` of two propositions that print
character for character the same in 1.5 s, and `using 2`, `using 4` and `using 6` each close the
goal for the elaborator and are each rejected by the kernel.  What that spelling waits on is one
line in the file which owns the definition — the equation stating its body, elaborated in the
same context, where `rfl` is syntactic — and not any further mathematics: the clause itself, as
stated below, is proved and kernel-clean.

## References

* [Stacks Project, Tag 0CKD](https://stacks.math.columbia.edu/tag/0CKD)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Dependence of the conormal map on the square -/

/-- **The conormal map of a square depends on the lower edge only through its value.**  Its
source and target do not mention the lower edge, so two equal lower edges give literally the
same morphism of conormal modules. -/
theorem conormalMap_congr_lower {X X' : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X.1) (Z' : ClosedSubspaces C S hS X'.1) {g g' : X ⟶ X'}
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces C S hS))
    (h : g = g')
    (hsq : subspaceInclusion C S hS X Z ≫ g = f ≫ subspaceInclusion C S hS X' Z')
    (hsq' : subspaceInclusion C S hS X Z ≫ g' = f ≫ subspaceInclusion C S hS X' Z') :
    conormalMap C S hS Z Z' g f hsq = conormalMap C S hS Z Z' g' f hsq' := by
  subst h; rfl

/-- The inclusion of a closed subspace of an algebraic space is a monomorphism. -/
private theorem mono_subspaceInclusion (X : AlgebraicSpaces C S hS)
    (Z : ClosedSubspaces C S hS X.1) : Mono (subspaceInclusion C S hS X Z) := by
  apply (ObjectProperty.ι _).mono_of_mono_map
  change Mono Z.1.ι
  infer_instance

/-- **The conormal map of the identity square is an isomorphism.**  It is the canonical
identification of `(id_Z)^*𝒞_{Z/X}` with `𝒞_{Z/X}`.

The identity of `X` is flat, and the inverse image of `Z` along it is `Z` itself, so this is the
flat clause of [Stacks Project, Tag 04CQ], `AlgebraicGeometry.Space.isIso_conormalMap_of_isFlat`,
at the identity; the upper edge of the square is forced to be the identity of `Z` because the
inclusion of `Z` is a monomorphism. -/
theorem isIso_conormalMap_id {X : AlgebraicSpaces C S hS} (Z : ClosedSubspaces C S hS X.1)
    (hsq : subspaceInclusion C S hS X Z ≫ 𝟙 X = 𝟙 _ ≫ subspaceInclusion C S hS X Z) :
    IsIso (conormalMap C S hS Z Z (𝟙 X) (𝟙 _) hsq) := by
  have key : ∀ (Z₁ : ClosedSubspaces C S hS X.1), Z₁ = Z →
      ∀ (p : (⟨Z₁.1.toFunctor, Z₁.2.1⟩ : AlgebraicSpaces C S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))
        (sq : subspaceInclusion C S hS X Z₁ ≫ 𝟙 X = p ≫ subspaceInclusion C S hS X Z),
        IsIso (conormalMap C S hS Z₁ Z (𝟙 X) p sq) →
          IsIso (conormalMap C S hS Z Z (𝟙 X) (𝟙 _) hsq) := by
    rintro Z₁ rfl p sq hp
    have hmono := mono_subspaceInclusion C S hS X Z₁
    obtain rfl : p = 𝟙 _ := by
      rw [← cancel_mono (subspaceInclusion C S hS X Z₁), ← sq, Category.comp_id,
        Category.id_comp]
    exact hp
  exact key (preimageSubspace C S hS (𝟙 X) Z) rfl (preimageProjection C S hS (𝟙 X) Z)
    (conormalEtaleRestrictionSquare C S hS (𝟙 X) Z)
    (isIso_conormalMap_of_isFlat C S hS (𝟙 X) Z
      ((isFlat_iff_smallEtaleRingedToposHom_isFlat C S hS (𝟙 X)).mp (isFlat_id C S hS X.2)))

/-! ### Functoriality of the conormal module under a composite of étale morphisms -/

/-- Pasting two commutative squares, in a bare category: the outer rectangle of two squares
stacked along their common edge commutes.

Stated with every object and morphism a variable, so that at an instance no step can drive the
unifier into the construction of the inverse image of modules. -/
private theorem pasteCommSq {D : Type*} [Category D] {A A' A'' Bb Bb' Bb'' : D}
    (i : A ⟶ Bb) (p : Bb ⟶ Bb') (q : Bb' ⟶ Bb'') (u : A ⟶ A') (j : A' ⟶ Bb')
    (v : A' ⟶ A'') (k : A'' ⟶ Bb'') (h₁ : i ≫ p = u ≫ j) (h₂ : j ≫ q = v ≫ k) :
    i ≫ p ≫ q = (u ≫ v) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-- **The composition formula for conormal maps, with the ambient algebraic spaces of the two
lower closed subspaces handed over in arguments.**  This is
`AlgebraicGeometry.Space.conormalMap_comp`, part (3) of [Stacks Project, Tag 04G2], restated so
that a consumer whose goal spells those ambient spaces otherwise than as `⟨Z.1.toFunctor, Z.2.1⟩`
of the subspace the law is instantiated at never asks for the two spellings to be identified
under a `CategoryTheory.Functor.map` or a `CategoryTheory.NatTrans.app`.

`AlgebraicGeometry.Space.conormalMap_comp_of_eq` applies that discipline to the *upper edge* of
the outer rectangle; this applies it to the *ambient spaces*.  Every object and morphism of the
conclusion is a variable — the spaces `𝒵`, `𝒵'`, `𝒲`, the edges `f`, `f'`, `fc`, the modules
`N`, `N'`, `Nc` and the three conormal maps — and each carries its value in an equation of
spaces or a heterogeneous equality, so that the whole statement is type-correct before any of
them is identified with what the law produces.  The conclusion is heterogeneous for the same
reason: the two sides are read at two spellings of one ambient space, and demanding they agree is
what a consumer cannot afford.

At a use site every equation is `rfl` or `HEq.rfl` once the law's own spelling is supplied, and
the one-step identification of [Stacks Project, Tag 04CO] discharges the three conormal maps. -/
theorem conormalMap_comp_of_spaces {X X' X'' : AlgebraicSpaces C S hS}
    (g : X ⟶ X') (g' : X' ⟶ X'')
    (Z : ClosedSubspaces C S hS X.1) (Z' : ClosedSubspaces C S hS X'.1)
    (Z'' : ClosedSubspaces C S hS X''.1)
    (f₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces C S hS))
    (f₀' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces C S hS))
    (hsq : subspaceInclusion C S hS X Z ≫ g = f₀ ≫ subspaceInclusion C S hS X' Z')
    (hsq' : subspaceInclusion C S hS X' Z' ≫ g' = f₀' ≫ subspaceInclusion C S hS X'' Z'')
    (hsq'' : subspaceInclusion C S hS X Z ≫ g ≫ g' =
      (f₀ ≫ f₀') ≫ subspaceInclusion C S hS X'' Z'')
    (𝒵 𝒵' 𝒲 : AlgebraicSpaces C S hS) (f : 𝒵 ⟶ 𝒵')
    (f' : 𝒵' ⟶ (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces C S hS))
    (fc : 𝒲 ⟶ (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces C S hS))
    {N : Modules.{u, u} C S hS 𝒵.1 𝒵.2} {N' : Modules.{u, u} C S hS 𝒵'.1 𝒵'.2}
    {Nc : Modules.{u, u} C S hS 𝒲.1 𝒲.2}
    (cm' : (modulePullback C S hS f').obj (conormalModule C S hS X'' Z'') ⟶ N')
    (cm : (modulePullback C S hS f).obj N' ⟶ N)
    (cmO : (modulePullback C S hS fc).obj (conormalModule C S hS X'' Z'') ⟶ Nc)
    (h𝒵 : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) = 𝒵)
    (h𝒵' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces C S hS) = 𝒵')
    (h𝒲 : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) = 𝒲)
    (hN : HEq N (conormalModule C S hS X Z)) (hN' : HEq N' (conormalModule C S hS X' Z'))
    (hNc : HEq Nc (conormalModule C S hS X Z))
    (hf : HEq f f₀) (hf' : HEq f' f₀') (hfc : HEq fc (f₀ ≫ f₀'))
    (hcm' : HEq cm' (conormalMap C S hS Z' Z'' g' f₀' hsq'))
    (hcm : HEq cm (conormalMap C S hS Z Z' g f₀ hsq))
    (hcmO : HEq cmO (conormalMap C S hS Z Z'' (g ≫ g') (f₀ ≫ f₀') hsq'')) :
    HEq ((modulePullbackCompIso C S hS f f').inv.app (conormalModule C S hS X'' Z'') ≫
      (modulePullback C S hS f).map cm' ≫ cm) cmO := by
  subst h𝒵
  subst h𝒵'
  subst h𝒲
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hf'
  obtain rfl := eq_of_heq hfc
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hN'
  obtain rfl := eq_of_heq hNc
  obtain rfl := eq_of_heq hcm'
  obtain rfl := eq_of_heq hcm
  obtain rfl := eq_of_heq hcmO
  exact heq_of_eq (conormalMap_comp C S hS g g' Z Z' Z'' _ _ hsq hsq' hsq'').symm

section EtaleSource

variable {U V X : AlgebraicSpaces C S hS}

/-- **The functoriality of Stacks 04CO in the étale source.**  For étale morphisms
`ψ : V ⟶ U` and `φ : U ⟶ X` of algebraic spaces with étale composite and a closed subspace
`Z ⊆ X`, the identification `p^*𝒞_{Z/X} ≅ 𝒞_{Z_V/V}` of [Stacks Project, Tag 04CO] taken in two
steps — the comparison of the inverse images along the two projections of [Stacks Project,
Tag 03LU], then the inverse image along `q : ψ⁻¹(φ⁻¹Z) ⟶ φ⁻¹Z` of the identification for `φ`,
then the identification for `ψ` over `φ⁻¹(Z)` — is the identification for `ψ ≫ φ` taken in one
step.  This is the "functorially in `U`" of the source.

The route is the one of [Stacks Project, Tag 04CP]: both sides are read through
`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom`, which identifies
the canonical map of that tag at an étale restriction square with the forward map constructed by
[Stacks Project, Tag 04CO], and the clause becomes part (3) of [Stacks Project, Tag 04G2] at the
two stacked étale restriction squares, in the form
`AlgebraicGeometry.Space.conormalMap_comp_of_spaces`.  The one-step identification for `ψ ≫ φ` is
read at the *iterated* spelling `ψ⁻¹(φ⁻¹Z)` of the upper closed subspace and with the projection
written as the composite `q ≫ p`, which costs nothing: an iota-crossing in a first-order argument
position of `AlgebraicGeometry.Space.conormalMap` is free, so neither
`AlgebraicGeometry.Space.closedSubspacePreimage_comp` nor
`AlgebraicGeometry.Space.subspaceProjection_comp` has to be rewritten.

The two-step composite is written out here rather than quoted as
`AlgebraicGeometry.Space.conormalEtaleRestrictionTwoStep`; the implementation notes of this file
record why, and that the difference is one of spelling and not of content. -/
@[stacks 04CO "functoriality in the étale source"]
theorem conormalModuleEtaleRestrictionIso_hom_comp (ψ : V ⟶ U) (φ : U ⟶ X)
    (hψ : IsEtale C S hS ψ.hom) (hφ : IsEtale C S hS φ.hom)
    (hψφ : IsEtale C S hS (ψ ≫ φ).hom) (Z : ClosedSubspaces C S hS X.1) :
    (modulePullbackCompIso C S hS
          (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
        (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
            (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
        AlgebraicSpaces C S hS) ⟶
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS))
          (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS) ⟶
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))).inv.app (conormalModule C S hS X Z) ≫
        (modulePullback C S hS
            (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
        (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
            (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
        AlgebraicSpaces C S hS) ⟶
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS))).map
          (conormalModuleEtaleRestrictionIso C S hS φ hφ Z).hom ≫
          (conormalModuleEtaleRestrictionIso C S hS ψ hψ
            (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces C S hS U.1)).hom =
      (conormalModuleEtaleRestrictionIso C S hS (ψ ≫ φ) hψφ Z).hom := by
  have hsq'' := pasteCommSq
    (subspaceInclusion C S hS V (preimageSubspace C S hS ψ (preimageSubspace C S hS φ Z)))
    ψ φ (preimageProjection C S hS ψ (preimageSubspace C S hS φ Z))
    (subspaceInclusion C S hS U (preimageSubspace C S hS φ Z))
    (preimageProjection C S hS φ Z) (subspaceInclusion C S hS X Z)
    (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z))
    (conormalEtaleRestrictionSquare C S hS φ Z)
  exact eq_of_heq (conormalMap_comp_of_spaces C S hS ψ φ
    (preimageSubspace C S hS ψ (preimageSubspace C S hS φ Z))
    (preimageSubspace C S hS φ Z) Z
    (preimageProjection C S hS ψ (preimageSubspace C S hS φ Z))
    (preimageProjection C S hS φ Z)
    (conormalEtaleRestrictionSquare C S hS ψ (preimageSubspace C S hS φ Z))
    (conormalEtaleRestrictionSquare C S hS φ Z) hsq''
    (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
            (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
        AlgebraicSpaces C S hS)
    (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS)
    (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
        (isClosedSubspace_preimage C S hS (ψ ≫ φ).hom Z.1 X.2 V.2 Z.2).1⟩ :
      AlgebraicSpaces C S hS)
    (ObjectProperty.homMk ((Z.1.preimage φ.hom).fromPreimage ψ.hom) :
        (⟨((Z.1.preimage φ.hom).preimage ψ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS ψ.hom (Z.1.preimage φ.hom) U.2 V.2
            (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2)).1⟩ :
        AlgebraicSpaces C S hS) ⟶
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS))
    (ObjectProperty.homMk (Z.1.fromPreimage φ.hom) :
        (⟨(Z.1.preimage φ.hom).toFunctor,
          (isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2).1⟩ :
        AlgebraicSpaces C S hS) ⟶
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))
    (ObjectProperty.homMk (Z.1.fromPreimage (ψ ≫ φ).hom) :
      (⟨(Z.1.preimage (ψ ≫ φ).hom).toFunctor,
        (isClosedSubspace_preimage C S hS (ψ ≫ φ).hom Z.1 X.2 V.2 Z.2).1⟩ :
      AlgebraicSpaces C S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS))
    (conormalModuleEtaleRestrictionIso C S hS φ hφ Z).hom
    (conormalModuleEtaleRestrictionIso C S hS ψ hψ
      (⟨Z.1.preimage φ.hom,
          isClosedSubspace_preimage C S hS φ.hom Z.1 X.2 U.2 Z.2⟩ :
          ClosedSubspaces C S hS U.1)).hom
    (conormalModuleEtaleRestrictionIso C S hS (ψ ≫ φ) hψφ Z).hom
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (heq_of_eq (conormalMap_eq_conormalModuleEtaleRestrictionIso_hom C S hS φ hφ Z).symm)
    (HEq.symm
      (heq_of_eq (conormalMap_eq_conormalModuleEtaleRestrictionIso_hom C S hS ψ hψ
        (preimageSubspace C S hS φ Z))))
    (HEq.symm
      (heq_of_eq (conormalMap_eq_conormalModuleEtaleRestrictionIso_hom C S hS (ψ ≫ φ) hψφ Z))))

end EtaleSource

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)
  (U₀ : ClosedSubspaces C S hS G.objects.1)

/-- **A section of the source which agrees with the unit on `U₀` has `t ∘ δ` restricting to the
identity on `U₀`.**  Indeed `t ∘ e = id_U`, so `i ∘ (t ∘ δ) = i ∘ (t ∘ e) = i`.

This is what makes the conormal map of [Stacks Project, Tag 0CKD] an endomorphism of
`𝒞_{U₀/U}`: the square of `i` with lower edge `f = t ∘ δ` has the identity of `U₀` as its
upper edge. -/
theorem subspaceInclusion_comp_sectionTarget (δ : Section G)
    (hδ : subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
      subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G) :
    subspaceInclusion C S hS G.objects U₀ ≫ (δ.1 ≫ G.target) =
      𝟙 _ ≫ subspaceInclusion C S hS G.objects U₀ := by
  rw [← Category.assoc, hδ, Category.assoc, identityArrow_comp_target, Category.comp_id,
    Category.id_comp]

/-- **Stacks 0CKD.**  Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, let
`U₀ ⊆ U` be a closed subspace whose inverse images along the source and the target agree — the
invariance of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantClosed` — and let
`δ : U ⟶ R` be a section of the source agreeing with the unit on `U₀`, and let `s` be flat.
Then the conormal map of `𝒞_{U₀/U}` induced by `f = t ∘ δ` is the conormal map induced by
`id_U`, which is the canonical identification of `(id_{U₀})^*𝒞_{U₀/U}` with `𝒞_{U₀/U}`.  In the
language of the source, `f` acts as the identity on `𝒞_{U₀/U}`.

The source assumes `s` and `t` flat and `U` a first-order thickening of `U₀`; only flatness of
`s` is used. -/
@[stacks 0CKD "the conormal map induced by f = t ∘ δ equals the conormal map induced by the \
identity; only flatness of s is assumed"]
theorem conormalMap_sectionTarget_eq_conormalMap_id (δ : Section G)
    (hδ : subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
      subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G)
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (hs : Space.IsFlat C S hS G.source.hom)
    (hsq : subspaceInclusion C S hS G.objects U₀ ≫ (δ.1 ≫ G.target) =
      𝟙 _ ≫ subspaceInclusion C S hS G.objects U₀)
    (hsqId : subspaceInclusion C S hS G.objects U₀ ≫ 𝟙 G.objects =
      𝟙 _ ≫ subspaceInclusion C S hS G.objects U₀) :
    conormalMap C S hS U₀ U₀ (δ.1 ≫ G.target) (𝟙 _) hsq =
      conormalMap C S hS U₀ U₀ (𝟙 G.objects) (𝟙 _) hsqId := by
  set i := subspaceInclusion C S hS G.objects U₀ with hi_def
  set R₀ := preimageSubspace C S hS G.source U₀ with hR₀_def
  set j := subspaceInclusion C S hS G.arrows R₀ with hj_def
  set s₀ := preimageProjection C S hS G.source U₀ with hs₀_def
  have hsq_s : j ≫ G.source = s₀ ≫ i := conormalEtaleRestrictionSquare C S hS G.source U₀
  have hmono : Mono i := mono_subspaceInclusion C S hS G.objects U₀
  -- The target carries `R₀ = s⁻¹(U₀)` into `U₀`, by invariance.
  have htrange : Subfunctor.range (j ≫ G.target).hom ≤ U₀.1 := by
    intro T point hpoint
    obtain ⟨arrow, rfl⟩ := hpoint
    have h : arrow.val ∈ (U₀.1.preimage G.target.hom).obj T := by
      rw [hinv]; exact arrow.property
    exact h
  set t₀ : (⟨R₀.1.toFunctor, R₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) :=
    ObjectProperty.homMk (Subfunctor.lift (j ≫ G.target).hom htrange) with ht₀_def
  have hsq_t : j ≫ G.target = t₀ ≫ i :=
    (ObjectProperty.hom_ext _ (Subfunctor.lift_ι (j ≫ G.target).hom htrange)).symm
  -- The restriction of `δ` to `U₀` factors through `R₀`, because `s ∘ δ = id`.
  have hps : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (y : G.objects.obj.obj T),
      G.source.hom.app T (δ.1.hom.app T y) = y := fun T y =>
    congrArg (fun m : G.objects ⟶ G.objects => m.hom.app T y) δ.2
  have hdrange : Subfunctor.range (i ≫ δ.1).hom ≤ U₀.1.preimage G.source.hom := by
    intro T point hpoint
    obtain ⟨x, rfl⟩ := hpoint
    change G.source.hom.app T ((i ≫ δ.1).hom.app T x) ∈ U₀.1.obj T
    have hcast : G.source.hom.app T ((i ≫ δ.1).hom.app T x) = x.val := hps T x.val
    rw [hcast]
    exact x.property
  set d : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨R₀.1.toFunctor, R₀.2.1⟩ : AlgebraicSpaces C S hS) :=
    ObjectProperty.homMk (Subfunctor.lift (i ≫ δ.1).hom hdrange) with hd_def
  have hd : d ≫ j = i ≫ δ.1 :=
    ObjectProperty.hom_ext _ (Subfunctor.lift_ι (i ≫ δ.1).hom hdrange)
  have hd' : d ≫ j = i ≫ identityArrow G := hd.trans hδ
  -- Both projections of `R₀` retract `d`.
  have hds : d ≫ s₀ = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, ← hsq_s, ← Category.assoc, hd, Category.assoc, δ.2,
      Category.comp_id, Category.id_comp]
  have hdt : d ≫ t₀ = 𝟙 _ := by
    rw [← cancel_mono i, Category.assoc, ← hsq_t, ← Category.assoc, hd', Category.assoc,
      identityArrow_comp_target, Category.comp_id, Category.id_comp]
  have hSiso : IsIso (conormalMap C S hS R₀ U₀ G.source s₀ hsq_s) :=
    isIso_conormalMap_of_isFlat C S hS G.source U₀
      ((isFlat_iff_smallEtaleRingedToposHom_isFlat C S hS G.source).mp hs)
  -- Composing with the square over the source identifies the two left-hand conormal maps.
  have hsqδs : i ≫ (δ.1 ≫ G.source) = (d ≫ s₀) ≫ i := by
    rw [hds, Category.id_comp, δ.2, Category.comp_id]
  have hsqes : i ≫ (identityArrow G ≫ G.source) = (d ≫ s₀) ≫ i := by
    rw [hds, Category.id_comp, identityArrow_comp_source, Category.comp_id]
  have hAeq : conormalMap C S hS U₀ R₀ δ.1 d hd.symm =
      conormalMap C S hS U₀ R₀ (identityArrow G) d hd'.symm := by
    have e1 := conormalMap_comp C S hS δ.1 G.source U₀ R₀ U₀ d s₀ hd.symm hsq_s hsqδs
    have e2 := conormalMap_comp C S hS (identityArrow G) G.source U₀ R₀ U₀ d s₀ hd'.symm hsq_s
      hsqes
    have ecg := conormalMap_congr_lower C S hS U₀ U₀ (d ≫ s₀)
      (show δ.1 ≫ G.source = identityArrow G ≫ G.source from
        δ.2.trans (identityArrow_comp_source G).symm) hsqδs hsqes
    have hchain := e1.symm.trans (ecg.trans e2)
    have := hSiso
    have hmapIso : IsIso ((modulePullback C S hS d).map
        (conormalMap C S hS R₀ U₀ G.source s₀ hsq_s)) := Functor.map_isIso _ _
    have : Epi ((modulePullback C S hS d).map
        (conormalMap C S hS R₀ U₀ G.source s₀ hsq_s)) := IsIso.epi_of_iso _
    exact (cancel_epi _).mp
      ((((modulePullbackCompIso C S hS d s₀).app
        (conormalModule C S hS G.objects U₀)).cancel_iso_inv_left _ _).mp hchain)
  -- Composing with the square over the target turns that into the assertion for `t ∘ δ`.
  have key : ∀ (k : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶
        (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS)) (_ : k = d ≫ t₀)
      (h1 : i ≫ (δ.1 ≫ G.target) = k ≫ i) (h2 : i ≫ (𝟙 G.objects) = k ≫ i),
      conormalMap C S hS U₀ U₀ (δ.1 ≫ G.target) k h1 =
        conormalMap C S hS U₀ U₀ (𝟙 G.objects) k h2 := by
    rintro k rfl h1 h2
    have h4 : i ≫ (identityArrow G ≫ G.target) = (d ≫ t₀) ≫ i := by
      rw [identityArrow_comp_target]; exact h2
    have e3 := conormalMap_comp C S hS δ.1 G.target U₀ R₀ U₀ d t₀ hd.symm hsq_t h1
    have e4 := conormalMap_comp C S hS (identityArrow G) G.target U₀ R₀ U₀ d t₀ hd'.symm hsq_t h4
    have ecg2 := conormalMap_congr_lower C S hS U₀ U₀ (d ≫ t₀)
      (show identityArrow G ≫ G.target = 𝟙 G.objects from identityArrow_comp_target G) h4 h2
    rw [e3, hAeq, ← e4, ecg2]
  exact key (𝟙 _) hdt.symm hsq hsqId

/-- **Stacks 0CKD, read as the identity.**  Transported across the conormal map of the identity
square — the canonical identification of `(id_{U₀})^*𝒞_{U₀/U}` with `𝒞_{U₀/U}`, an isomorphism by
`AlgebraicGeometry.Space.isIso_conormalMap_id` — the conormal map induced by `f = t ∘ δ` is the
identity: followed by the inverse of that identification it is the identity of
`(id_{U₀})^*𝒞_{U₀/U}`.  As in
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.conormalMap_sectionTarget_eq_conormalMap_id`, only
flatness of `s` is assumed. -/
@[stacks 0CKD "f = t ∘ δ acts as the identity on the conormal module, read through the \
conormal map of the identity; only flatness of s is assumed"]
theorem conormalMap_sectionTarget_comp_inv_eq_id (δ : Section G)
    (hδ : subspaceInclusion C S hS G.objects U₀ ≫ δ.1 =
      subspaceInclusion C S hS G.objects U₀ ≫ identityArrow G)
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (hs : Space.IsFlat C S hS G.source.hom)
    (hsq : subspaceInclusion C S hS G.objects U₀ ≫ (δ.1 ≫ G.target) =
      𝟙 _ ≫ subspaceInclusion C S hS G.objects U₀)
    (hsqId : subspaceInclusion C S hS G.objects U₀ ≫ 𝟙 G.objects =
      𝟙 _ ≫ subspaceInclusion C S hS G.objects U₀) :
    conormalMap C S hS U₀ U₀ (δ.1 ≫ G.target) (𝟙 _) hsq ≫
        @inv _ _ _ _ (conormalMap C S hS U₀ U₀ (𝟙 G.objects) (𝟙 _) hsqId)
          (isIso_conormalMap_id C S hS U₀ hsqId) = 𝟙 _ := by
  have := isIso_conormalMap_id C S hS U₀ hsqId
  rw [conormalMap_sectionTarget_eq_conormalMap_id G U₀ δ hδ hinv hs hsq hsqId]
  exact IsIso.hom_inv_id _

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
